import BtcPolicy.Silence
/-! **Non-normative research.** A transaction-keyed Hot accounting, modelled beside `BtcPolicy.Ledger`
so the two can be compared case by case (`F63`, the open finding). Nothing here is a rule of the
specification: no declaration carries a requirement tag, no guard parameter of `Ledger.Guards` or
`Kernel.Rules` has this accounting as a value, and no normative module imports this one. Adopting
it would be a protocol change that needs an owner decision. The comparison itself is
`docs/research/hot-accounting-comparison.md`, and the runs are `BtcPolicy.Exhibits.TxAccounting`.

**The candidate** takes the direction `F63` sketches: "Meter the exact transaction once: one row
keyed by the txid `SPN-33` already adds to the vault-authorized set", "its amount `hot_outflow`",
"its exposure the OR over the commitments that name it", "refunded when unexposed and every such
commitment has expired". `F63` leaves some choices open, and these are this model's:

- A row keeps one `Entry` per commitment with that commitment's own reservation time and signed
  expiry, and `POL-19`'s release is evaluated per entry: the charge lasts as long as the union of its
  commitments' lifetimes, and the row leaves with its last entry (`tAgeOut`). Keeping only the first
  reservation time loses a charge `POL-19`'s monotonic disjunct would hold
  (`BtcPolicy.Exhibits.TxAccounting.first_time_only_loses_charge`).
- A row remembers every commitment that ever named it (`named`), so a candidate whose entry was
  released still counts towards the row's exposure and residency.
- The capacity of 4 096 counts entries, not rows (`entryCount`). `named` is outside it: `tReserve` appends
  to `named` and `tAgeOut` never shrinks it, so a row re-quoted for ever keeps growing. No bound on it is
  modelled, and the record lists that as unresolved.
- A settlement refunds nothing, and the release point and refund point are the ones
  `Ledger.Release.acceptedAdmission` and `Ledger.Refund.onCollection` name, spelled out rather than
  read from `Ledger.current`.

The kernel is the normative one: `tsysStep` is `Ledger.sysStep`'s shape with this ledger in place of
`Ledger.Ledger`, over the same `Kernel.step`, `Ledger.admitted`, `Ledger.budgetRefusal` and
`Ledger.hotRequest`.

**What is not modelled, so not claimed.** Replay stays commitment-keyed because the kernel's Carrier
checks do. `NCH-24`'s lookup eviction, as in `BtcPolicy.Ledger`. The candidate's `POL-20` cohort is
stated over given cuts (`t_bridge`): `hamt` and `hcohort` are not derived over a candidate run, as
`Admission.fed_bridge` derives them for the current ledger. `Silence.obsOf` reads `Ledger.Sys`, so the
observation-by-observation form of `Silence.silence` is not restated: `t_coupled_walk` proves the
coupling that carries it, and equal budget verdicts and effects. -/

namespace BtcPolicy.TxAccounting
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger

/-! ## The candidate ledger -/

/-- One commitment's claim on a transaction's charge. -/
structure Entry where
  cid : Nat
  reservedAt : Mono
  expiry : Wall
  deriving DecidableEq, Repr

/-- One charge per transaction. `entries` are the commitments whose lifetime still holds the
charge; `named` is every commitment that has named it. -/
structure TRow where
  txid : Nat
  amount : Nat
  exposed : Bool
  named : List Nat
  entries : List Entry
  deriving DecidableEq, Repr

abbrev TLedger := List TRow

/-- What the candidate meters: one `amount` per row. -/
def tSum (l : TLedger) : Nat := (l.map (·.amount)).sum

def entryCount (l : TLedger) : Nat := (l.map (·.entries.length)).sum

/-- A commitment with a standing entry: the retry test. -/
def tHolds (l : TLedger) (cid : Nat) : Bool := l.any fun row => row.entries.any (·.cid == cid)

/-- A transaction with a standing charge. -/
def tHasTx (l : TLedger) (txid : Nat) : Bool := l.any (·.txid == txid)

/-- A retry adds nothing. A new commitment over a charged transaction adds no charge. Anything else
reads the sum, so a different transaction gets no credit. -/
def tAdmits (cfg : Config) (l : TLedger) (c : Cand) : Bool :=
  tHolds l c.id ||
    (decide (entryCount l < capacity) && (tHasTx l c.tx.id || decide (tSum l + c.tx.outflow ≤ cfg.cap)))

def tEntry (c : Cand) (now : Mono) : Entry := { cid := c.id, reservedAt := now, expiry := c.expiry }

def tReserve (l : TLedger) (c : Cand) (now : Mono) : TLedger :=
  if tHolds l c.id then l
  else if tHasTx l c.tx.id then
    l.map fun row =>
      if row.txid == c.tx.id then
        { row with named := row.named ++ [c.id], entries := row.entries ++ [tEntry c now] }
      else row
  else
    l ++ [{ txid := c.tx.id, amount := c.tx.outflow, exposed := false, named := [c.id],
            entries := [tEntry c now] }]

/-- The entries `POL-19`'s predicate holds at this sample. -/
def liveEntries (env : Env) (window : Secs) (row : TRow) : List Entry :=
  row.entries.filter fun x => reservationLive x.reservedAt env.mono window env.wall x.expiry

def keepLive (env : Env) (window : Secs) (row : TRow) : TRow :=
  { row with entries := liveEntries env window row }

/-- `POL-19`'s predicate, per entry and one way. A row whose last entry goes is released whatever its
exposure bit says. -/
def tAgeOut (env : Env) (window : Secs) (l : TLedger) : TLedger :=
  (l.map (keepLive env window)).filter fun row => !row.entries.isEmpty

/-- The OR over every commitment that named the row. Never cleared. -/
def tMark (n : Node) (l : TLedger) : TLedger :=
  l.map fun row =>
    if n.cands.any (fun c => row.named.contains c.id && (c.released || c.broadcast)) then
      { row with exposed := true }
    else row

/-- The whole row is refunded, or none of it: unexposed, every standing entry's signed expiry
strictly past, and no candidate that named it still resident. -/
def tRefund (env : Env) (n : Node) (l : TLedger) : TLedger :=
  l.filter fun row =>
    row.exposed || row.entries.any (fun x => Wall.atOrBefore env.wall x.expiry) ||
      n.cands.any fun c => row.named.contains c.id

/-! ## The composed step -/

structure TSys where
  world : World
  led : TLedger
  deriving DecidableEq, Repr

def tRefused (cfg : Config) (l : TLedger) : Event → Bool
  | .accept _ _ _ sp _ => sp.hot && !tAdmits cfg l sp
  | _ => false

def tChecked (env : Env) (window : Secs) (l : TLedger) (e : Event) : TLedger :=
  if hotRequest e then tAgeOut env window l else l

def tAfter (env : Env) (before after : World) : Event → TLedger → TLedger
  | e@(.accept _ _ _ sp _), l => if admitted before after e then tReserve l sp env.mono else l
  | .prune, l => tRefund env after.node l
  | _, l => l

def tsysStep (cfg : Config) (r : Rules) (env : Env) (sys : TSys) (e : Event) :
    TSys × List Effect :=
  let chk := tChecked env cfg.window sys.led e
  if tRefused cfg chk e then
    ({ world := { sys.world with node := budgetRefusal r env sys.world.node e },
       led := tMark sys.world.node sys.led }, [])
  else
    let after := (step r env sys.world e).1
    ({ world := after,
       led := tMark after.node
         (tAfter env sys.world after e (if admitted sys.world after e then chk else sys.led)) },
     (step r env sys.world e).2)

def tsysRun (cfg : Config) (r : Rules) : TSys → List (Env × Event) → TSys × List Effect
  | sys, [] => (sys, [])
  | sys, (env, e) :: rest =>
    let stepped := tsysStep cfg r env sys e
    let ran := tsysRun cfg r stepped.1 rest
    (ran.1, stepped.2 ++ ran.2)

/-! ## Local facts about each transition -/

theorem tSum_cons (row : TRow) (l : TLedger) : tSum (row :: l) = row.amount + tSum l := rfl

theorem tSum_append (a b : TLedger) : tSum (a ++ b) = tSum a + tSum b := by
  simp [tSum, List.sum_append]

theorem tSum_filter_le (l : TLedger) (p : TRow → Bool) : tSum (l.filter p) ≤ tSum l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.filter_cons]
    split
    · simpa [tSum_cons] using ih
    · rw [tSum_cons]; omega

theorem tSum_map_eq (l : TLedger) (f : TRow → TRow) (hf : ∀ r, (f r).amount = r.amount) :
    tSum (l.map f) = tSum l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [tSum_cons, ih, hf]

theorem tSum_tMark (n : Node) (l : TLedger) : tSum (tMark n l) = tSum l :=
  tSum_map_eq l _ fun r => by split <;> rfl

theorem tSum_tAgeOut_le (env : Env) (w : Secs) (l : TLedger) : tSum (tAgeOut env w l) ≤ tSum l := by
  unfold tAgeOut
  exact Nat.le_trans (tSum_filter_le _ _) (Nat.le_of_eq (tSum_map_eq l _ fun _ => rfl))

theorem tSum_tChecked_le (env : Env) (w : Secs) (l : TLedger) (e : Event) :
    tSum (tChecked env w l e) ≤ tSum l := by
  unfold tChecked
  split
  · exact tSum_tAgeOut_le env w l
  · exact Nat.le_refl _

/-- **Exact retry.** A commitment with a standing entry changes nothing: reservation time, expiry,
amount and exposure stay as they are. -/
theorem retry_changes_nothing (l : TLedger) (c : Cand) (now : Mono) (h : tHolds l c.id = true) :
    tReserve l c now = l := by
  simp [tReserve, h]

/-- **New expiry over one transaction.** A new commitment over a charged transaction adds no charge,
whatever the budget says; it adds an entry. -/
theorem requote_adds_no_charge (l : TLedger) (c : Cand) (now : Mono) (hn : tHolds l c.id = false)
    (ht : tHasTx l c.tx.id = true) : tSum (tReserve l c now) = tSum l := by
  simp only [tReserve, hn, ht, Bool.false_eq_true, if_false, if_true]
  exact tSum_map_eq l _ fun r => by split <;> rfl

theorem requote_admitted (cfg : Config) (l : TLedger) (c : Cand) (hcap : entryCount l < capacity)
    (ht : tHasTx l c.tx.id = true) : tAdmits cfg l c = true := by
  simp [tAdmits, hcap, ht]

/-- A full ledger refuses a new commitment over a charged transaction. -/
theorem requote_refused_at_capacity (cfg : Config) (l : TLedger) (c : Cand)
    (hfull : capacity ≤ entryCount l) (hn : tHolds l c.id = false) : tAdmits cfg l c = false := by
  simp [tAdmits, hn, Nat.not_lt.2 hfull]

/-- **Distinct transaction.** No netting: a different txid adds its own full amount and every row
that was there stays, unchanged. -/
theorem distinct_keeps_own_charge (l : TLedger) (c : Cand) (now : Mono) (hn : tHolds l c.id = false)
    (ht : tHasTx l c.tx.id = false) :
    tSum (tReserve l c now) = tSum l + c.tx.outflow ∧ ∀ row ∈ l, row ∈ tReserve l c now := by
  simp only [tReserve, hn, ht, Bool.false_eq_true, if_false]
  refine ⟨?_, fun row h => List.mem_append_left _ h⟩
  rw [tSum_append]; simp [tSum]

/-- And it reads the full sum: the check gives no credit for a conflict's charge. -/
theorem distinct_admitted_iff (cfg : Config) (l : TLedger) (c : Cand) (hn : tHolds l c.id = false)
    (ht : tHasTx l c.tx.id = false) (hcap : entryCount l < capacity) :
    tAdmits cfg l c = decide (tSum l + c.tx.outflow ≤ cfg.cap) := by
  simp [tAdmits, hn, ht, hcap]

/-- A re-quote touches only its own transaction's row. -/
theorem reserve_leaves_other_rows (l : TLedger) (c : Cand) (now : Mono) (row : TRow) (hr : row ∈ l)
    (hne : row.txid ≠ c.tx.id) : row ∈ tReserve l c now := by
  unfold tReserve
  split
  · exact hr
  · split
    · exact List.mem_map.2 ⟨row, hr, by simp [hne]⟩
    · exact List.mem_append_left _ hr

/-- **All commitments expire.** The exact evidence that removes a row at a prune pass: its own
never-set exposure bit, every standing entry's signed expiry strictly past on the wall sample, and
no named candidate resident. -/
theorem refund_iff (env : Env) (n : Node) (l : TLedger) (row : TRow) :
    (row ∈ l ∧ row ∉ tRefund env n l) ↔
      row ∈ l ∧ row.exposed = false ∧
        (∀ x ∈ row.entries, Wall.atOrBefore env.wall x.expiry = false) ∧
        ∀ c ∈ n.cands, row.named.contains c.id = false := by
  unfold tRefund
  simp only [List.mem_filter, not_and, Bool.not_eq_true, Bool.or_eq_false_iff,
    List.any_eq_false, Bool.not_eq_true]
  constructor
  · rintro ⟨hm, h⟩
    have h := h hm
    exact ⟨hm, h.1.1, h.1.2, h.2⟩
  · rintro ⟨hm, h1, h2, h3⟩
    exact ⟨hm, fun _ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- **One exposed twin.** The exposure of any commitment that named the row keeps the whole row out of
the refund. -/
theorem exposed_never_refunded (env : Env) (n : Node) (l : TLedger) (row : TRow) (hr : row ∈ l)
    (he : row.exposed = true) : row ∈ tRefund env n l :=
  List.mem_filter.2 ⟨hr, by simp [he]⟩

/-- A settlement moves nothing in this ledger: the evidence is `refund_iff`'s and no other. -/
theorem settlement_refunds_nothing (env : Env) (b a : World) (tx : Tx) (l : TLedger) :
    tAfter env b a (.settle tx) l = l := rfl

/-- **Aged-out exposed authority.** The release does not read the exposure bit: a row with no live
entry goes, exposed or not. -/
theorem release_ignores_exposure (env : Env) (w : Secs) (l : TLedger) (row : TRow) (hr : row ∈ l)
    (hdead : ∀ x ∈ row.entries,
      reservationLive x.reservedAt env.mono w env.wall x.expiry = false) :
    keepLive env w row ∉ tAgeOut env w l := by
  intro hin
  have hne := (List.mem_filter.1 hin).2
  have hnil : liveEntries env w row = [] :=
    List.filter_eq_nil_iff.2 fun y hy => by simp [hdead y hy]
  simp [keepLive, hnil] at hne

/-- The ledger writes nothing in the world: a step is the kernel's, or the staged refusal the budget
check asked for. -/
theorem tsysStep_world (cfg : Config) (r : Rules) (env : Env) (sys : TSys) (e : Event) :
    (tsysStep cfg r env sys e).1.world = { sys.world with node := budgetRefusal r env sys.world.node e } ∨
      (tsysStep cfg r env sys e).1.world = (step r env sys.world e).1 := by
  simp only [tsysStep]
  split
  · exact .inl rfl
  · exact .inr rfl

/-- Off a hot request the step is exactly the kernel's, effects included, so nothing this ledger holds
stands between an exposed partial and a broadcast. -/
theorem nonhot_step_is_kernel (cfg : Config) (r : Rules) (env : Env) (sys : TSys) (e : Event)
    (he : hotRequest e = false) :
    (tsysStep cfg r env sys e).1.world = (step r env sys.world e).1 ∧
      (tsysStep cfg r env sys e).2 = (step r env sys.world e).2 := by
  have hr : tRefused cfg (tChecked env cfg.window sys.led e) e = false := by
    cases e with
    | accept cid d E sp es =>
      have hhot : sp.hot = false := by simpa [hotRequest] using he
      simp [tRefused, hhot]
    | _ => rfl
  simp only [tsysStep, hr, Bool.false_eq_true, if_false, and_self]

/-- Exposed authority only grows through a composed step, whatever the ledger does. -/
theorem tsysStep_exposure (cfg : Config) (r : Rules) (env : Env) (sys : TSys) (e : Event) (x : Exp)
    (hx : x ∈ sys.world.exposure) : x ∈ (tsysStep cfg r env sys e).1.world.exposure := by
  rcases tsysStep_world cfg r env sys e with h | h <;> rw [h]
  · exact hx
  · exact exposure_monotone r env sys.world e x hx

/-! ## The invariant `POL-16` rests on still goes by induction -/

theorem tSum_reserve_le_cap (cfg : Config) (l : TLedger) (c : Cand) (now : Mono)
    (h : tAdmits cfg l c = true) (hc : tSum l ≤ cfg.cap) : tSum (tReserve l c now) ≤ cfg.cap := by
  by_cases hn : tHolds l c.id = true
  · rw [retry_changes_nothing l c now hn]; exact hc
  · simp only [Bool.not_eq_true] at hn
    by_cases ht : tHasTx l c.tx.id = true
    · rw [requote_adds_no_charge l c now hn ht]; exact hc
    · simp only [Bool.not_eq_true] at ht
      rw [(distinct_keeps_own_charge l c now hn ht).1]
      simp only [tAdmits, hn, ht, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2

/-- For every environment and event, a state at or under the cap steps to one at or under it. -/
theorem tSum_tsysStep (cfg : Config) (r : Rules) (env : Env) (sys : TSys) (e : Event)
    (h : tSum sys.led ≤ cfg.cap) : tSum (tsysStep cfg r env sys e).1.led ≤ cfg.cap := by
  have hchk := tSum_tChecked_le env cfg.window sys.led e
  simp only [tsysStep]
  split
  · rw [tSum_tMark]; exact h
  · rename_i hnr
    rw [tSum_tMark]
    have hk : tSum (if admitted sys.world (step r env sys.world e).1 e then
        tChecked env cfg.window sys.led e else sys.led) ≤ cfg.cap := by
      split
      · exact Nat.le_trans hchk h
      · exact h
    cases e with
    | accept cid d E sp es =>
      by_cases hres : admitted sys.world (step r env sys.world (.accept cid d E sp es)).1
          (.accept cid d E sp es) = true
      · simp only [tAfter, hres, if_true] at hk ⊢
        refine tSum_reserve_le_cap cfg _ sp env.mono ?_ hk
        simp only [admitted, Bool.and_eq_true] at hres
        simp only [tRefused, Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hnr
        simpa using hnr hres.1.1
      · simp only [Bool.not_eq_true] at hres
        simp only [tAfter, hres, Bool.false_eq_true, if_false] at hk ⊢
        exact hk
    | prune => exact Nat.le_trans (tSum_filter_le _ _) hk
    | settle tx | refuse cid d E pair code | receipt cid s | firePass | packageAccepted c | send c
    | tick | panic | adversaryExposes m i s c | receivePartial m i s c | clawback _ => exact hk

theorem tSum_le_cap (cfg : Config) (r : Rules) :
    ∀ (tr : List (Env × Event)) (sys : TSys), tSum sys.led ≤ cfg.cap →
      tSum (tsysRun cfg r sys tr).1.led ≤ cfg.cap := by
  intro tr
  induction tr with
  | nil => intro sys h; exact h
  | cons x rest ih =>
    intro sys h
    exact ih _ (tSum_tsysStep cfg r x.1 sys x.2 h)

/-! ## `POL-20`'s counting, by transaction -/

/-- One honest node's ledger and its own HotClock sample. -/
structure TCut where
  led : TLedger
  now : Mono
  deriving DecidableEq, Repr

/-- A node counts a transaction when some standing entry of its row was reserved inside its own
trailing interval. -/
def tCountsAt (window : Secs) (txid : Nat) (k : TCut) : Bool :=
  k.led.any fun row => row.txid == txid &&
    row.entries.any fun x => Mono.withinWindow x.reservedAt k.now window

def tCohortCount (window : Secs) (cuts : List TCut) (txid : Nat) : Nat :=
  cuts.countP (tCountsAt window txid)

/-- The candidate as a ledger the existing counting lemma reads: one row per transaction, under its
txid. -/
def asRows (l : TLedger) : Ledger :=
  l.map fun row => { cid := row.txid, amount := row.amount, reservedAt := Mono.sample 0,
                     expiry := Wall.sample 0, exposed := row.exposed }

theorem liveSum_asRows (l : TLedger) : liveSum (asRows l) = tSum l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [asRows, liveSum, tSum] at ih ⊢; exact ih

theorem holds_asRows (l : TLedger) : holds (asRows l) = tHasTx l := by
  funext id
  simp [holds, asRows, tHasTx, List.any_map, Function.comp_def]

/-- `Ledger.bridge`'s statement with the spend read as a transaction: the same bound, over distinct
txids, so a re-quote's two commitments are one cohort member. `hamt` is a real obligation here: the
row keeps the first amount, and a txid that did not bind its outflow would under-charge
(`BtcPolicy.Exhibits.TxAccounting.txid_must_bind_outflow`). -/
theorem t_bridge (cfg : Config) (q : Nat) (cohort : List Ledgers.Spend) (cuts : List TCut)
    (hnd : (cohort.map (·.1)).Nodup)
    (hamt : ∀ k ∈ cuts, ∀ s ∈ cohort, ∀ row ∈ k.led, row.txid = s.1 → row.amount = s.2)
    (hinv : ∀ k ∈ cuts, tSum k.led ≤ cfg.cap)
    (hcohort : ∀ s ∈ cohort, q ≤ tCohortCount cfg.window cuts s.1) :
    q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap := by
  have hlen : (cuts.map fun k => tHasTx k.led).length = cuts.length := List.length_map _
  have h := Ledgers.counting cohort (cuts.map fun k => tHasTx k.led) cfg.cap q
    (by
      intro l hl
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
      have hle := charge_le_liveSum cohort hnd (asRows k.led) (fun s hs row hrow hid => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hrow
        exact hamt k hk s hs y hy hid)
      rw [holds_asRows, liveSum_asRows] at hle
      exact Nat.le_trans hle (hinv k hk))
    (fun s hs => by
      refine Nat.le_trans (hcohort s hs) ?_
      unfold tCohortCount Ledgers.charging
      rw [List.countP_map]
      apply List.countP_mono_left
      intro k _ hk
      simp only [tCountsAt, List.any_eq_true, Bool.and_eq_true] at hk
      obtain ⟨row, hrow, hid, _⟩ := hk
      simp only [Function.comp_apply, tHasTx, List.any_eq_true]
      exact ⟨row, hrow, hid⟩)
  rwa [hlen] at h

/-! ## Equivalence where no transaction has two commitments

The established equivalence: over a trace in which each accepted spend's commitment id is a function
of its txid, the candidate and the current ledger take the same steps. `proj` is the
projection from candidate rows to the current ledger's rows, one per entry. -/

def resOf (row : TRow) (x : Entry) : Res :=
  { cid := x.cid, amount := row.amount, reservedAt := x.reservedAt, expiry := x.expiry,
    exposed := row.exposed }

def proj (l : TLedger) : Ledger := l.flatMap fun row => row.entries.map (resOf row)

/-- Each row holds exactly one commitment, the one `name` assigns to its txid. -/
def OneToOne (name : Nat → Nat) (l : TLedger) : Prop :=
  ∀ row ∈ l, ∃ x, row.entries = [x] ∧ row.named = [x.cid] ∧ x.cid = name row.txid

theorem OneToOne.tail {name : Nat → Nat} {a : TRow} {l : TLedger} (h : OneToOne name (a :: l)) :
    OneToOne name l := fun row hr => h row (List.mem_cons_of_mem _ hr)

theorem proj_cons_one {row : TRow} {x : Entry} (l : TLedger) (he : row.entries = [x]) :
    proj (row :: l) = resOf row x :: proj l := by
  simp [proj, he]

theorem tHolds_eq (l : TLedger) (id : Nat) : tHolds l id = holds (proj l) id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [tHolds, holds, proj, List.flatMap_cons, List.any_cons, List.any_append, List.any_map,
      Function.comp_def] at ih ⊢
    rw [ih]
    simp only [resOf]

theorem entryCount_eq (l : TLedger) : entryCount l = (proj l).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [entryCount, proj, List.flatMap_cons, List.length_append, List.length_map,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem tSum_eq {name : Nat → Nat} (l : TLedger) (h : OneToOne name l) :
    tSum l = liveSum (proj l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨x, he, -, -⟩ := h a (List.mem_cons_self ..)
    rw [proj_cons_one l he, liveSum_cons, tSum_cons, ih h.tail]
    rfl

/-- Over any ledger whose rows each hold an entry, the candidate's meter is at or below the current
one's on the same reservations. This is about the same row set: refunds can make the two ledgers
hold different rows, and then neither meter bounds the other
(`BtcPolicy.Exhibits.TxAccounting.neither_accounting_dominates`). -/
theorem tSum_le_proj (l : TLedger) (h : ∀ row ∈ l, row.entries ≠ []) :
    tSum l ≤ liveSum (proj l) := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    have ih := ih fun row hr => h row (List.mem_cons_of_mem _ hr)
    have hne := h a (List.mem_cons_self ..)
    rw [tSum_cons]
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    have : proj (a :: l) = resOf a x :: (xs.map (resOf a) ++ proj l) := by
      simp [proj, hx]
    rw [this, liveSum_cons, liveSum_append]
    show a.amount + tSum l ≤ a.amount + (_ + liveSum (proj l))
    omega

theorem tAdmits_eq {name : Nat → Nat} (cfg : Config) (l : TLedger) (c : Cand)
    (h : OneToOne name l) (hc : c.id = name c.tx.id) :
    tAdmits cfg l c = admits cfg (proj l) c := by
  have htx : tHasTx l c.tx.id = true → holds (proj l) c.id = true := by
    intro ht
    obtain ⟨row, hr, hid⟩ := List.any_eq_true.1 ht
    obtain ⟨x, he, -, hx⟩ := h row hr
    rw [← tHolds_eq]
    refine List.any_eq_true.2 ⟨row, hr, ?_⟩
    have : row.txid = c.tx.id := by simpa using hid
    simp [he, hx, this, hc]
  simp only [tAdmits, admits, ← tHolds_eq, entryCount_eq, tSum_eq l h]
  by_cases hh : tHolds l c.id = true
  · simp [hh]
  · have hno : tHasTx l c.tx.id = false := by
      cases hv : tHasTx l c.tx.id with
      | false => rfl
      | true => exact absurd ((tHolds_eq l c.id).trans (htx hv)) hh
    simp [hno]

theorem proj_ageOut (env : Env) (w : Secs) (l : TLedger) :
    proj (tAgeOut env w l) = ageOut env w (proj l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hstep : proj (tAgeOut env w (a :: l)) =
        (liveEntries env w a).map (resOf a) ++ proj (tAgeOut env w l) := by
      simp only [tAgeOut, List.map_cons, List.filter_cons]
      split
      · simp [proj, keepLive, resOf]
      · rename_i hemp
        have : liveEntries env w a = [] := by simpa [keepLive] using hemp
        simp [this]
    rw [hstep, ih]
    simp only [ageOut, proj, List.flatMap_cons, List.filter_append, liveEntries, List.filter_map,
      Function.comp_def, resOf]

theorem OneToOne_ageOut {name : Nat → Nat} (env : Env) (w : Secs) (l : TLedger)
    (h : OneToOne name l) : OneToOne name (tAgeOut env w l) := by
  intro row hr
  simp only [tAgeOut, List.mem_filter, List.mem_map] at hr
  obtain ⟨⟨a, ha, rfl⟩, hne⟩ := hr
  obtain ⟨x, he, hn, hx⟩ := h a ha
  refine ⟨x, ?_, hn, hx⟩
  simp only [keepLive, liveEntries, he, List.filter_cons, List.filter_nil] at hne ⊢
  split
  · rfl
  · rename_i hl; simp [hl] at hne

theorem OneToOne_mark {name : Nat → Nat} (n : Node) (l : TLedger) (h : OneToOne name l) :
    OneToOne name (tMark n l) := by
  intro row hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  obtain ⟨x, he, hn, hx⟩ := h a ha
  refine ⟨x, ?_⟩
  split
  · exact ⟨he, hn, hx⟩
  · exact ⟨he, hn, hx⟩

theorem contains_singleton (x id : Nat) : [x].contains id = (id == x) := by
  by_cases h : id = x <;> simp [List.contains_cons, h]

theorem proj_mark {name : Nat → Nat} (n : Node) (l : TLedger) (h : OneToOne name l) :
    proj (tMark n l) = markExposed n (proj l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨x, he, hn, -⟩ := h a (List.mem_cons_self ..)
    have hany : n.cands.any (fun c => a.named.contains c.id && (c.released || c.broadcast)) =
        n.cands.any (fun c => c.id == x.cid && (c.released || c.broadcast)) := by
      simp only [hn, contains_singleton]
    have ih := ih h.tail
    simp only [tMark, markExposed] at ih ⊢
    rw [List.map_cons, proj_cons_one l he, List.map_cons]
    by_cases hb : n.cands.any (fun c => c.id == x.cid && (c.released || c.broadcast)) = true
    · rw [hany, hb]
      simp only [if_true]
      rw [proj_cons_one _ (row := { a with exposed := true }) he, ih]
      simp only [resOf, hb, if_true]
    · simp only [Bool.not_eq_true] at hb
      rw [hany, hb]
      simp only [Bool.false_eq_true, if_false]
      rw [proj_cons_one _ he, ih]
      simp only [resOf, hb, Bool.false_eq_true, if_false]

theorem OneToOne_refund {name : Nat → Nat} (env : Env) (n : Node) (l : TLedger)
    (h : OneToOne name l) : OneToOne name (tRefund env n l) :=
  fun row hr => h row (List.mem_filter.1 hr).1

theorem proj_refund {name : Nat → Nat} (env : Env) (n : Node) (l : TLedger) (h : OneToOne name l) :
    proj (tRefund env n l) = refundAtPrune .onCollection env n (proj l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨x, he, hn, -⟩ := h a (List.mem_cons_self ..)
    have ih := ih h.tail
    simp only [tRefund, refundAtPrune] at ih ⊢
    have hkeep : (a.exposed || a.entries.any (fun y => Wall.atOrBefore env.wall y.expiry) ||
          n.cands.any fun c => a.named.contains c.id) =
        (a.exposed || Wall.atOrBefore env.wall x.expiry || n.cands.any (·.id == x.cid)) := by
      simp only [he, hn, contains_singleton, List.any_cons, List.any_nil, Bool.or_false]
    rw [List.filter_cons, proj_cons_one l he, List.filter_cons, hkeep]
    by_cases hK : (a.exposed || Wall.atOrBefore env.wall x.expiry ||
        n.cands.any (·.id == x.cid)) = true
    · have hK' : ((resOf a x).exposed || Wall.atOrBefore env.wall (resOf a x).expiry ||
          n.cands.any (·.id == (resOf a x).cid)) = true := hK
      rw [if_pos hK, if_pos hK', proj_cons_one _ he, ih]
    · have hK' : ¬ ((resOf a x).exposed || Wall.atOrBefore env.wall (resOf a x).expiry ||
          n.cands.any (·.id == (resOf a x).cid)) = true := hK
      rw [if_neg hK, if_neg hK']
      exact ih

theorem OneToOne_reserve {name : Nat → Nat} (l : TLedger) (c : Cand) (now : Mono)
    (h : OneToOne name l) (hc : c.id = name c.tx.id) : OneToOne name (tReserve l c now) := by
  unfold tReserve
  split
  · exact h
  · rename_i hh
    split
    · rename_i ht
      exfalso
      obtain ⟨row, hr, hid⟩ := List.any_eq_true.1 ht
      obtain ⟨x, he, -, hx⟩ := h row hr
      have : row.txid = c.tx.id := by simpa using hid
      exact hh (List.any_eq_true.2 ⟨row, hr, by simp [he, hx, this, hc]⟩)
    · intro row hr
      rcases List.mem_append.1 hr with hr | hr
      · exact h row hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨tEntry c now, rfl, rfl, hc⟩

theorem proj_reserve {name : Nat → Nat} (l : TLedger) (c : Cand) (now : Mono)
    (h : OneToOne name l) (hc : c.id = name c.tx.id) :
    proj (tReserve l c now) = reserve (proj l) c now := by
  unfold tReserve reserve
  rw [← tHolds_eq]
  split
  · rfl
  · rename_i hh
    split
    · rename_i ht
      exfalso
      obtain ⟨row, hr, hid⟩ := List.any_eq_true.1 ht
      obtain ⟨x, he, -, hx⟩ := h row hr
      have : row.txid = c.tx.id := by simpa using hid
      exact hh (List.any_eq_true.2 ⟨row, hr, by simp [he, hx, this, hc]⟩)
    · simp [proj, List.flatMap_append, tEntry, resOf]

/-- The current ledger's system a candidate system projects to. -/
def toSys (s : TSys) : Sys := { world := s.world, led := proj s.led }

/-- The event's accepted spend, if any, carries the commitment id `name` gives its txid. -/
def Names (name : Nat → Nat) : Event → Prop
  | .accept _ _ _ sp _ => sp.id = name sp.tx.id
  | _ => True

instance (name : Nat → Nat) (e : Event) : Decidable (Names name e) := by
  cases e <;> first | exact inferInstanceAs (Decidable (_ = _)) | exact isTrue trivial

/-- One step: under the release and refund values the candidate spells out, and with `g`'s settlement
value retaining, the candidate's step projects to the current ledger's step, with equal effects. -/
theorem proj_step {name : Nat → Nat} (g : Guards) (hs : g.settlement = .retainOnMempool)
    (hr : g.release = .acceptedAdmission) (hrf : g.refund = .onCollection)
    (cfg : Config) (r : Rules) (env : Env) (s : TSys) (e : Event) (hj : OneToOne name s.led)
    (hn : Names name e) :
    toSys (tsysStep cfg r env s e).1 = (sysStep g cfg r env (toSys s) e).1 ∧
      (tsysStep cfg r env s e).2 = (sysStep g cfg r env (toSys s) e).2 ∧
      OneToOne name (tsysStep cfg r env s e).1.led := by
  have hchk : proj (tChecked env cfg.window s.led e) = checked g.release env cfg.window (proj s.led) e := by
    simp only [tChecked, checked, hr]
    split
    · exact proj_ageOut _ _ _
    · rfl
  have hjchk : OneToOne name (tChecked env cfg.window s.led e) := by
    simp only [tChecked]
    split
    · exact OneToOne_ageOut _ _ _ hj
    · exact hj
  have href : tRefused cfg (tChecked env cfg.window s.led e) e =
      refusedByBudget cfg (checked g.release env cfg.window (proj s.led) e) e := by
    rw [← hchk]
    cases e with
    | accept cid d E sp es =>
      simp only [tRefused, refusedByBudget]
      rw [tAdmits_eq cfg _ sp hjchk hn]
    | _ => rfl
  simp only [tsysStep, sysStep, toSys, href]
  split
  · refine ⟨?_, rfl, OneToOne_mark _ _ hj⟩
    simp only [hr, kept, Bool.false_eq_true, if_false, TSys.mk.injEq, Sys.mk.injEq, true_and]
    exact proj_mark _ _ hj
  · have hkept : proj (if admitted s.world (step r env s.world e).1 e then
        tChecked env cfg.window s.led e else s.led) =
        kept g.release (checked g.release env cfg.window (proj s.led) e) (proj s.led)
          (admitted s.world (step r env s.world e).1 e) := by
      simp only [kept, hr]
      split
      · rw [← hr]; exact hchk
      · rfl
    have hjk : OneToOne name (if admitted s.world (step r env s.world e).1 e then
        tChecked env cfg.window s.led e else s.led) := by
      split
      · exact hjchk
      · exact hj
    generalize hk : (if admitted s.world (step r env s.world e).1 e then
        tChecked env cfg.window s.led e else s.led) = k at hkept hjk
    have haft : proj (tAfter env s.world (step r env s.world e).1 e k) =
        afterEvent g env s.world (step r env s.world e).1 e (proj k) ∧
        OneToOne name (tAfter env s.world (step r env s.world e).1 e k) := by
      cases e with
      | accept cid d E sp es =>
        simp only [tAfter, afterEvent]
        split
        · exact ⟨proj_reserve _ _ _ hjk hn, OneToOne_reserve _ _ _ hjk hn⟩
        · exact ⟨rfl, hjk⟩
      | prune =>
        simp only [tAfter, afterEvent, hrf]
        exact ⟨proj_refund _ _ _ hjk, OneToOne_refund _ _ _ hjk⟩
      | settle tx =>
        simp only [tAfter, afterEvent, hs]
        exact ⟨trivial, hjk⟩
      | refuse cid d E pair code | receipt cid x | firePass | packageAccepted c | send c | tick
      | panic | adversaryExposes m i x c | receivePartial m i x c | clawback _ => exact ⟨rfl, hjk⟩
    refine ⟨?_, (by first | exact trivial | rfl), OneToOne_mark _ _ haft.2⟩
    simp only [Sys.mk.injEq, true_and]
    rw [proj_mark _ _ haft.2, haft.1, hkept]

/-- **Established equivalence.** Over a trace in which no transaction has two commitments, the
candidate and the current ledger reach projected-equal states with equal effects, at every sample,
backward wall steps included, and so every verdict and every completion of the current ledger stands.
The premise is on the trace: `hn` fixes one commitment id per txid. `ADR-0014`'s distinct conflicting
transactions are inside it, a re-quote of one transaction is not. -/
theorem same_steps_without_twins {name : Nat → Nat} (g : Guards) (hs : g.settlement = .retainOnMempool)
    (hr : g.release = .acceptedAdmission) (hrf : g.refund = .onCollection)
    (cfg : Config) (r : Rules) :
    ∀ (tr : List (Env × Event)) (s : TSys), OneToOne name s.led → (∀ x ∈ tr, Names name x.2) →
      toSys (tsysRun cfg r s tr).1 = (sysRun g cfg r (toSys s) tr).1 ∧
        (tsysRun cfg r s tr).2 = (sysRun g cfg r (toSys s) tr).2 := by
  intro tr
  induction tr with
  | nil => intro s _ _; exact ⟨rfl, rfl⟩
  | cons y rest ih =>
    obtain ⟨env, e⟩ := y
    intro s hj hn
    obtain ⟨h1, h2, h3⟩ := proj_step g hs hr hrf cfg r env s e hj (hn _ (List.mem_cons_self ..))
    obtain ⟨h4, h5⟩ := ih _ h3 fun x hx => hn x (List.mem_cons_of_mem _ hx)
    refine ⟨?_, ?_⟩
    · simp only [tsysRun, sysRun]; rw [h4, h1]
    · simp only [tsysRun, sysRun]; rw [h5, h1, h2]

/-! ## Backward clocks -/

theorem tHasTx_mark (n : Node) (l : TLedger) (x : Nat) : tHasTx (tMark n l) x = tHasTx l x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [tMark, tHasTx, List.map_cons, List.any_cons] at ih ⊢
    rw [ih]
    split <;> rfl

theorem tHasTx_ageOut (env : Env) (w : Secs) (l : TLedger) (x : Nat) (h : tHasTx l x = false) :
    tHasTx (tAgeOut env w l) x = false := by
  simp only [tHasTx, List.any_eq_false, tAgeOut, List.mem_filter, List.mem_map] at h ⊢
  rintro y ⟨⟨z, hz, rfl⟩, -⟩
  exact h z hz

theorem tHasTx_refund (env : Env) (n : Node) (l : TLedger) (x : Nat) (h : tHasTx l x = false) :
    tHasTx (tRefund env n l) x = false := by
  simp only [tHasTx, List.any_eq_false, tRefund, List.mem_filter] at h ⊢
  rintro y ⟨hy, -⟩
  exact h y hy

theorem tHasTx_reserve (l : TLedger) (c : Cand) (now : Mono) (x : Nat) (h : tHasTx l x = false)
    (hne : c.tx.id ≠ x) : tHasTx (tReserve l c now) x = false := by
  unfold tReserve
  split
  · exact h
  · split
    · simp only [tHasTx, List.any_eq_false, List.mem_map] at h ⊢
      rintro y ⟨z, hz, rfl⟩
      have := h z hz
      split
      · exact this
      · exact this
    · simp only [tHasTx] at h
      simp only [tHasTx, List.any_append, h, Bool.false_or]
      simp [hne]

/-- A step that accepts no commitment over the transaction leaves a gone charge gone, whatever its wall
and HotClock samples read. -/
theorem released_stays_gone_step (cfg : Config) (r : Rules) (env : Env) (s : TSys) (e : Event)
    (x : Nat) (h : tHasTx s.led x = false)
    (he : ∀ cid d E sp es, e = .accept cid d E sp es → sp.tx.id ≠ x) :
    tHasTx (tsysStep cfg r env s e).1.led x = false := by
  have hchk : tHasTx (tChecked env cfg.window s.led e) x = false := by
    simp only [tChecked]
    split
    · exact tHasTx_ageOut _ _ _ _ h
    · exact h
  simp only [tsysStep]
  split
  · rw [tHasTx_mark]; exact h
  · rw [tHasTx_mark]
    generalize hk : (if admitted s.world (step r env s.world e).1 e then
        tChecked env cfg.window s.led e else s.led) = k
    have hkf : tHasTx k x = false := by
      rw [← hk]; split
      · exact hchk
      · exact h
    cases e with
    | accept cid d E sp es =>
      simp only [tAfter]
      split
      · exact tHasTx_reserve _ _ _ _ hkf (he _ _ _ _ _ rfl)
      · exact hkf
    | prune => exact tHasTx_refund _ _ _ _ hkf
    | settle tx | refuse cid d E pair code | receipt cid y | firePass | packageAccepted c | send c
    | tick | panic | adversaryExposes m i y c | receivePartial m i y c | clawback _ => exact hkf

/-- **Backward clocks.** A charge that is gone stays gone along every trace of any samples unless a new
acceptance over that transaction charges it again. Nothing re-tests a row that has left. -/
theorem released_stays_gone (cfg : Config) (r : Rules) (x : Nat) :
    ∀ (tr : List (Env × Event)) (s : TSys), tHasTx s.led x = false →
      (∀ y ∈ tr, ∀ cid d E sp es, y.2 = .accept cid d E sp es → sp.tx.id ≠ x) →
      tHasTx (tsysRun cfg r s tr).1.led x = false := by
  intro tr
  induction tr with
  | nil => intro s h _; exact h
  | cons y rest ih =>
    intro s h he
    exact ih _ (released_stays_gone_step cfg r y.1 s y.2 x h (he y (List.mem_cons_self ..)))
      fun z hz => he z (List.mem_cons_of_mem _ hz)

theorem tHolds_mark (n : Node) (l : TLedger) (id : Nat) : tHolds (tMark n l) id = tHolds l id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [tMark, tHolds, List.map_cons, List.any_cons] at ih ⊢
    rw [ih]
    split <;> rfl

theorem tHolds_reserve_of_holds (l : TLedger) (c : Cand) (now : Mono) (id : Nat)
    (h : tHolds l id = true) : tHolds (tReserve l c now) id = true := by
  unfold tReserve
  split
  · exact h
  · split
    · obtain ⟨row, hr, hx⟩ := List.any_eq_true.1 h
      refine List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨row, hr, rfl⟩, ?_⟩
      split
      · simp only [List.any_append, hx, Bool.true_or]
      · exact hx
    · simp only [tHolds, List.any_append] at h ⊢
      simp [h]

/-- `Ledger.released_below_ratchet` for an entry: an entry present before a step other than the prune
pass, whose commitment has no entry after it, has its signed expiry strictly below the ratchet the
step leaves. Only an accepted hot admission's own check drops it. -/
theorem entry_released_below_ratchet (cfg : Config) (r : Rules) (env : Env) (s : TSys) (e : Event)
    (he : e ≠ .prune) (row : TRow) (hrow : row ∈ s.led) (x : Entry) (hx : x ∈ row.entries)
    (hgone : tHolds (tsysStep cfg r env s e).1.led x.cid = false) :
    (tsysStep cfg r env s e).1.world.node.ratchet.atOrBefore x.expiry = false := by
  have hheld : tHolds s.led x.cid = true :=
    List.any_eq_true.2 ⟨row, hrow, List.any_eq_true.2 ⟨x, hx, by simp⟩⟩
  by_cases hb : tRefused cfg (tChecked env cfg.window s.led e) e = true
  · simp only [tsysStep, hb, if_true, tHolds_mark] at hgone
    rw [hheld] at hgone; cases hgone
  · simp only [Bool.not_eq_true] at hb
    simp only [tsysStep, hb, Bool.false_eq_true, if_false, tHolds_mark] at hgone ⊢
    by_cases hadm : admitted s.world (step r env s.world e).1 e = true
    · cases e with
      | accept cid d E sp es =>
        have hadm' := hadm
        simp only [admitted, Bool.and_eq_true, Bool.not_eq_true'] at hadm'
        obtain ⟨⟨hhot, hacc⟩, hnew⟩ := hadm'
        simp only [hadm, if_true, tAfter] at hgone
        have hchk : tChecked env cfg.window s.led (.accept cid d E sp es)
            = tAgeOut env cfg.window s.led := by simp [tChecked, hotRequest, hhot]
        rw [hchk] at hgone
        have hnot : tHolds (tAgeOut env cfg.window s.led) x.cid = false := by
          cases hv : tHolds (tAgeOut env cfg.window s.led) x.cid with
          | false => rfl
          | true =>
            rw [tHolds_reserve_of_holds _ sp env.mono _ hv] at hgone; cases hgone
        have hdead : reservationLive x.reservedAt env.mono cfg.window env.wall x.expiry = false := by
          cases hl : reservationLive x.reservedAt env.mono cfg.window env.wall x.expiry with
          | false => rfl
          | true =>
            exfalso
            have hin : tHolds (tAgeOut env cfg.window s.led) x.cid = true := by
              have hlive : x ∈ liveEntries env cfg.window row := List.mem_filter.2 ⟨hx, hl⟩
              refine List.any_eq_true.2 ⟨keepLive env cfg.window row, ?_, ?_⟩
              · refine List.mem_filter.2 ⟨List.mem_map.2 ⟨row, hrow, rfl⟩, ?_⟩
                cases hf : liveEntries env cfg.window row with
                | nil => rw [hf] at hlive; cases hlive
                | cons _ _ => simp [keepLive, hf]
              · exact List.any_eq_true.2 ⟨x, hlive, by simp⟩
            rw [hnot] at hin; cases hin
        have hwall : Wall.atOrBefore env.wall x.expiry = false := by
          simp only [reservationLive, Bool.or_eq_false_iff] at hdead
          exact hdead.2
        show (accept r env s.world.node cid d E sp es).ratchet.atOrBefore x.expiry = false
        rw [accept_ratchet_of_admitted hacc hnew hhot]
        exact Effective.not_atOrBefore_weaken (Effective.ofWall_not_atOrBefore env.hw hwall)
          (Effective.notAfter_latest_right _ _)
      | _ => simp [admitted] at hadm
    · simp only [Bool.not_eq_true] at hadm
      simp only [hadm, Bool.false_eq_true, if_false] at hgone
      exfalso
      cases e with
      | accept cid d E sp es =>
        simp only [tAfter, hadm, Bool.false_eq_true, if_false, hheld] at hgone
        cases hgone
      | prune => exact he rfl
      | settle tx | refuse cid d E pair code | receipt cid y | firePass | packageAccepted c | send c
      | tick | panic | adversaryExposes m i y c | receivePartial m i y c | clawback _ =>
        simp only [tAfter, hheld] at hgone
        cases hgone

theorem tsysStep_ratchet_never_lowered (cfg : Config) (r : Rules) (env : Env) (sys : TSys) (e : Event) :
    sys.world.node.ratchet.notAfter (tsysStep cfg r env sys e).1.world.node.ratchet = true := by
  rcases tsysStep_world cfg r env sys e with h | h <;> rw [h]
  · cases e with
    | accept cid d E sp es =>
      show sys.world.node.ratchet.notAfter (refuse r env sys.world.node cid d E _).ratchet = true
      rw [refuse_ratchet]; exact Effective.notAfter_refl _
    | _ => exact Effective.notAfter_refl _
  · exact ratchet_never_lowered r env sys.world e

theorem tsysRun_ratchet_never_lowered (cfg : Config) (r : Rules) :
    ∀ (tr : List (Env × Event)) (sys : TSys),
      sys.world.node.ratchet.notAfter (tsysRun cfg r sys tr).1.world.node.ratchet = true := by
  intro tr
  induction tr with
  | nil => intro sys; exact Effective.notAfter_refl _
  | cons x rest ih =>
    intro sys
    exact Effective.notAfter_trans (tsysStep_ratchet_never_lowered cfg r x.1 sys x.2) (ih _)

/-- `Ledger.released_never_due` for an entry: `F62`'s closure survives the re-keying. The candidate
whose entry an accepted hot admission released is never due again, at any later sample. Its premise
`hcl` is the ratchet close value, taken as a premise rather than read from `Kernel.current`. -/
theorem entry_released_never_due (cfg : Config) (r : Rules) (hcl : r.closeTime = .ratchet) (env : Env)
    (s : TSys) (e : Event) (he : e ≠ .prune) (row : TRow) (hrow : row ∈ s.led) (x : Entry)
    (hx : x ∈ row.entries) (hgone : tHolds (tsysStep cfg r env s e).1.led x.cid = false)
    (tr : List (Env × Event)) (c : Cand) (hhot : c.hot = true) (hwc : c.windowClose = none)
    (hexp : c.expiry = x.expiry) (env' : Env) :
    due r env' (tsysRun cfg r (tsysStep cfg r env s e).1 tr).1.world.node c = false := by
  have hbelow := Effective.not_atOrBefore_weaken
    (entry_released_below_ratchet cfg r env s e he row hrow x hx hgone)
    (tsysRun_ratchet_never_lowered cfg r tr _)
  refine never_due_below_ratchet hcl hhot ?_ env'
  simp [windowOpen, hwc, hexp, hbelow]

/-! ## Normal and duress worlds

`POL-21`: "a refund that happened only under duress would be the timing signal `DUR-1` forbids".
`Silence.Coupled` holds one ledger between the two runs; `TCoupled` is the same relation over this
one. -/

open BtcPolicy.Silence in
structure TCoupled (r : Rules) (a b : TSys) : Prop where
  node : pubNode r a.world.node = pubNode r b.world.node
  exposure : a.world.exposure = b.world.exposure
  led : a.led = b.led

section Coupling
open BtcPolicy.Silence
variable {r : Rules}

theorem tMark_pub {x y : Node} (h : pubNode r x = pubNode r y) (l : TLedger) :
    tMark x l = tMark y l := by
  unfold tMark
  refine congrArg (List.map · l) (funext fun row => ?_)
  rw [cands_any_pub h (fun c => row.named.contains c.id && (c.released || c.broadcast))
    (fun c => by simp [pubCand_id, pubCand_released, pubCand_broadcast])
    (fun c => by simp [pubCand_id, pubCand_released, pubCand_broadcast])]

theorem tChecked_pin (env : Env) (w : Secs) (l : TLedger) (i : Input) (tbl₀ tbl₁ : Enrolment) :
    tChecked env w l (i.event tbl₀) = tChecked env w l (i.event tbl₁) := by
  cases i <;> rfl

/-- `F63`'s bar: "a re-quote's admission verdict independent of the PIN (`POL-21`)". The verdict
reads the ledger and the spend. -/
theorem tRefused_pin (cfg : Config) (l : TLedger) (i : Input) (tbl₀ tbl₁ : Enrolment) :
    tRefused cfg l (i.event tbl₀) = tRefused cfg l (i.event tbl₁) := by
  cases i with
  | request cid pin E sp es => rfl
  | refusal cid pin E pair code => rfl
  | pinless e => rfl

theorem tAfter_pub {env : Env} {ba bb aa ab : World} (ha : pubNode r aa.node = pubNode r ab.node)
    (i : Input) (tbl₀ tbl₁ : Enrolment) (l : TLedger)
    (hadm : admitted ba aa (i.event tbl₀) = admitted bb ab (i.event tbl₁)) :
    tAfter env ba aa (i.event tbl₀) l = tAfter env bb ab (i.event tbl₁) l := by
  have hprune : tRefund env aa.node l = tRefund env ab.node l := by
    unfold tRefund
    refine congrArg (List.filter · l) (funext fun row => ?_)
    rw [cands_any_pub ha (fun c => row.named.contains c.id) (fun c => by simp [pubCand_id])
      (fun c => by simp [pubCand_id])]
  cases i with
  | request cid pin E sp es =>
    simp only [Input.event, tAfter] at hadm ⊢
    rw [hadm]
  | refusal cid pin E pair code => rfl
  | pinless e =>
    cases e with
    | accept cid d E sp es =>
      simp only [Input.event, tAfter] at hadm ⊢
      rw [hadm]
    | prune => exact hprune
    | _ => rfl

/-- One composed step of each run: the coupling, and the effects, inside the concealment horizon. -/
theorem tsysStep_coupled {cfg : Config} (ht : r.traversal = .always) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) {env : Env} {a b : TSys} (hc : TCoupled r a b)
    (hia : NodeInv r a.world.node a.world.node.ratchet) (hib : NodeInv r b.world.node b.world.node.ratchet)
    (hpa : preHorizon r env a.world.node = true) (hpb : preHorizon r env b.world.node = true)
    (i : Input) (tbl₀ tbl₁ : Enrolment) :
    TCoupled r (tsysStep cfg r env a (i.event tbl₀)).1 (tsysStep cfg r env b (i.event tbl₁)).1 ∧
      (tsysStep cfg r env a (i.event tbl₀)).2 = (tsysStep cfg r env b (i.event tbl₁)).2 := by
  obtain ⟨hnode, hexp, hled⟩ := hc
  obtain ⟨h1, h2, h3⟩ := step_pub ht hcl hdr hnode hexp hia hib hpa hpb i tbl₀ tbl₁
  simp only [tsysStep, hled, tChecked_pin env cfg.window b.led i tbl₀ tbl₁,
    tRefused_pin cfg (tChecked env cfg.window b.led (i.event tbl₁)) i tbl₀ tbl₁]
  split
  · refine ⟨⟨?_, hexp, tMark_pub hnode _⟩, rfl⟩
    cases i with
    | request cid pin E sp es => exact refuse_pub env hnode cid (tbl₀ pin) (tbl₁ pin) E _
    | refusal cid pin E pair code => exact hnode
    | pinless e =>
      cases e <;> try exact hnode
      exact refuse_pub env hnode _ _ _ _ _
  · have hadm := admitted_pub hnode h1 i tbl₀ tbl₁
    refine ⟨⟨h1, h2, ?_⟩, h3⟩
    rw [hadm, tAfter_pub h1 i tbl₀ tbl₁ _ hadm, tMark_pub h1]

theorem inv_tsysStep {cfg : Config} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) {env : Env} {sys : TSys}
    (hi : NodeInv r sys.world.node sys.world.node.ratchet) (e : Event)
    (hwf : wfEvent sys.world.node e = true)
    (hlt : sys.world.node.armed = true → env.eff.deadlineReached sys.world.node.T = false) :
    NodeInv r (tsysStep cfg r env sys e).1.world.node (tsysStep cfg r env sys e).1.world.node.ratchet := by
  simp only [tsysStep]
  split
  · cases e <;> try exact hi
    simp only [budgetRefusal, refuse_ratchet]
    exact inv_refuse hi _ _ _ _
  · exact inv_step ht hd hr hi e hwf hlt

/-- What each step of the walk can show about the Hot budget: the verdict `POL-16`'s check reaches,
the effects, and the ledger the step leaves. -/
def tView (cfg : Config) (r : Rules) (env : Env) (s : TSys) (e : Event) :
    Bool × List Effect × TLedger :=
  (tRefused cfg (tChecked env cfg.window s.led e) e, (tsysStep cfg r env s e).2,
    (tsysStep cfg r env s e).1.led)

/-- The two runs walked together while both entering states are inside the horizon, `Silence.obsPair`'s
stop rule. -/
def tPair (cfg : Config) (r : Rules) (tbl₀ tbl₁ : Enrolment) :
    TSys → TSys → List (Env × Input) → List ((Bool × List Effect × TLedger) × (Bool × List Effect × TLedger))
  | _, _, [] => []
  | a, b, (env, i) :: rest =>
    if preHorizon r env a.world.node && preHorizon r env b.world.node &&
        wfEvent a.world.node (i.event tbl₀) then
      (tView cfg r env a (i.event tbl₀), tView cfg r env b (i.event tbl₁)) ::
        tPair cfg r tbl₀ tbl₁ (tsysStep cfg r env a (i.event tbl₀)).1
          (tsysStep cfg r env b (i.event tbl₁)).1 rest
    else []

/-- **Normal and duress worlds.** Inside the concealment horizon the candidate's budget verdicts,
effects and ledger are equal in the two runs, with `Silence.silence`'s own rule and state premises.
A consequence of one ledger between them: no refund happens only under duress. Past the horizon no
coupling is claimed, under either accounting. -/
theorem t_coupled_walk {cfg : Config} (ht : r.traversal = .always) (hd : r.dynamics = .dynamic)
    (hr : r.registration = .preserve) (hcl : r.closeTime = .ratchet)
    (hdr : r.driverTime = .ratchet) (tbl₀ tbl₁ : Enrolment) :
    ∀ (tr : List (Env × Input)) (a b : TSys), TCoupled r a b →
      NodeInv r a.world.node a.world.node.ratchet → NodeInv r b.world.node b.world.node.ratchet →
      ∀ y ∈ tPair cfg r tbl₀ tbl₁ a b tr, y.1 = y.2 := by
  intro tr
  induction tr with
  | nil => intro a b _ _ _ y hy; cases hy
  | cons x rest ih =>
    obtain ⟨env, i⟩ := x
    intro a b hc hia hib y hy
    simp only [tPair] at hy
    split at hy
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨hpa, hpb⟩, hwf⟩ := hguard
      have hwfb : wfEvent b.world.node (i.event tbl₁) = true := by
        rw [← wfEvent_pub i tbl₀ tbl₁]; exact hwf
      obtain ⟨hc', heff⟩ := tsysStep_coupled (cfg := cfg) ht hcl hdr hc hia hib hpa hpb i tbl₀ tbl₁
      rcases List.mem_cons.1 hy with rfl | hy
      · simp only [tView]
        rw [hc.led, tChecked_pin env cfg.window b.led i tbl₀ tbl₁,
          tRefused_pin cfg _ i tbl₀ tbl₁, heff, hc'.led]
      · exact ih _ _ hc'
          (inv_tsysStep ht hd hr hia (i.event tbl₀) hwf
            (fun ha => (Effective.deadlineReached_latest (preHorizon_below hdr hpa ha)).2))
          (inv_tsysStep ht hd hr hib (i.event tbl₁) hwfb
            (fun ha => (Effective.deadlineReached_latest (preHorizon_below hdr hpb ha)).2)) y hy
    · cases hy

end Coupling

end BtcPolicy.TxAccounting
