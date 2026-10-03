import BtcPolicy.Kernel
import BtcPolicy.Ledgers
/-! The Hot ledger and the accounting bridge (`ADR-0023` decision 10 item 7; `F61`, `F62`):
`POL-16`'s reservation ledger as a transition system composed with `Kernel.lean`'s node, and the
bridge that discharges `Ledgers.counting`'s two hypotheses for `POL-20`'s cohort.

A row is keyed by commitment id — `POL-18` places the reservation "idempotently per commitment" —
and holds the authoritative amount, the reservation time, the signed expiry and the exposure bit.
`SPN-33` keeps all four: "the ledger retains its original reservation time, expiry and exposure
state independently of candidate residency", so a row outlives its candidate and nothing that
reads it goes back to the registry.

Reserve at acceptance under `POL-16`'s check; refund at the expiry sweep and only while unexposed
(`SPN-33`, `POL-21`); and `POL-19`'s age-out as a ONE-WAY release — the
predicate is the condition for releasing a charge, not a membership test re-run over a retained
row. `F62` is why: re-tested, a charge whose budget the node has already reclaimed becomes live
again when a backward wall step puts `wall_now` back at or below `expiry`, and `POL-20`'s "each
ledger holds at most `cap`" is then false at a reachable state (`rerun_exceeds_cap`). The composed
step is one transition, which is `POL-21`'s "one atomic step" and `SPN-29`'s "a reservation the
registration then refuses MUST be unwound in the same step": the check and the registration happen
together, and a spend the ledger refuses registers nothing.

**What is not modelled, and so is not claimed.** `SPN-33`'s conflicting-confirmation refund: the
kernel's `ChainView` holds one list of transactions "seen in the mempool or confirmed" and cannot
tell a confirmation from a mempool sighting, so no settlement refunds anything here. That is
`SPN-33`'s "Mempool-only settlement MUST NOT refund a reservation" exactly, and for the confirmed
case it over-counts, which is `POL-18`'s safe direction ("over-counting refuses a later spend,
netting could admit a coerced one"). `POL-11`'s per-transaction cap is a pure evaluation gate
(`POL-15`: "no node state") and is no transition of this ledger. Who is honest, and `DUR-8`'s
counting under `compromised < t`, are not here either: the bridge takes the honest nodes' ledgers
as given, and `POL-20`'s `n − c` is the caller's claim about the federation.

The exposure bit is per candidate, as `POL-18` words it — released "its partial" or broadcast —
while `ADR-0023` decision 9 keys the exposed authority itself by `(sighash message, input,
signer)` at world level, which is what `Kernel.exposedQuorum` counts. Two commitments over one
transaction (`CHN-24`) therefore give two rows sharing one authority, and `F63` is where that
leads. What is established here is narrower than a coverage claim: `refundAtSweep` never refunds
an exposed row (`sweep_refunds_only_unexposed_and_expired`). Exposed rows can still age out, and
no theorem here says a surviving row covers the authority of one that has — where the released
twin's row ages out first, the sweep refunds the other and the node charges nothing for a
transaction its own signature finalizes, which
`BtcPolicy.Exhibits.HotLedger.f63_twins_end_charging_nothing` runs. That reaches no state
`POL-19`'s age-out would not have reached on its own, and `POL-20` is not weakened by it: its
cohort excludes a refunded reservation, and the residual is the one it states, "Already exposed
signatures also remain valid after their reservations age out". -/

namespace BtcPolicy.Ledger

open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## The ledger -/

/-- One reservation (`POL-16`'s "reservation ledger"), keyed by commitment id. -/
structure Res where
  cid : Nat
  /-- `POL-11`'s `hot_outflow` for the spend, which is what `POL-16` meters. -/
  amount : Nat
  /-- `POL-18`: fixed at acceptance, and "a retry keeps the original reservation time". -/
  reservedAt : Mono
  /-- The candidate's signed expiry, retained past the candidate (`SPN-33`). -/
  expiry : Wall
  /-- `POL-18`: the partial "has left the node", by release or by broadcast. -/
  exposed : Bool
  deriving DecidableEq, Repr

abbrev Ledger := List Res

/-- The two sealed parameters this ledger reads (`MAN-2`, `POL-17`): `hot_max_per_window` and
`hot_window_secs`. -/
structure Config where
  cap : Nat
  window : Secs
  deriving DecidableEq, Repr

/-- `POL-16`'s "the sum of `hot_outflow` over accepted hot spends whose reservation is live":
every row IS live, because the age-out releases rather than re-tests (`F62`). -/
@[req "POL-16"]
def liveSum (l : Ledger) : Nat := (l.map (·.amount)).sum

/-- Whether a commitment is charged. This is `Ledgers.Ledger`, the counting theorem's predicate. -/
@[req "POL-20"]
def holds (l : Ledger) (cid : Nat) : Bool := l.any (·.cid == cid)

/-- `POL-16`: "The reservation ledger is bounded at 4 096 entries; a full ledger refuses with the
same code and a detail naming the capacity rather than the window." -/
@[req "POL-16"] def capacity : Nat := 4096

/-- `POL-16`'s admission check: "the sum of `hot_outflow` over accepted hot spends whose
reservation is live MUST NOT exceed `hot_max_per_window`, or the spend is refused". A retry of a
commitment already charged adds nothing and is admitted by that charge (`POL-18`); the capacity
refusal is the first conjunct of the second disjunct, and it inserts nothing. -/
@[req "POL-16"]
def admits (cfg : Config) (l : Ledger) (c : Cand) : Bool :=
  holds l c.id || (l.length < capacity && liveSum l + c.tx.outflow ≤ cfg.cap)

/-- `POL-18`: "A reservation is placed at acceptance, idempotently per commitment (a retry keeps
the original reservation time)". -/
@[req "POL-18"]
def reserve (l : Ledger) (c : Cand) (now : Mono) : Ledger :=
  if holds l c.id then l
  else l ++ [{ cid := c.id, amount := c.tx.outflow, reservedAt := now, expiry := c.expiry,
               exposed := false }]

/-- `POL-19`'s age-out, one-way: a row is dropped at the first sample where the predicate is false
and is never re-created, so the backward wall step of `F62` cannot resurrect a reclaimed charge.
An exposed charge ages like any other — `POL-20`: "Already exposed signatures also remain valid
after their reservations age out". -/
@[req "POL-19"]
def ageOut (env : Env) (window : Secs) (l : Ledger) : Ledger :=
  l.filter fun r => reservationLive r.reservedAt env.mono window env.wall r.expiry

/-- `POL-18`: "A partial that has left the node is finalizable authority in `t − 1` compromised
hands and meters exactly as a broadcast does." The bit is read off the candidate's `released` and
`broadcast` flags after each step and is never cleared, so it survives the candidate (`SPN-33`). -/
@[req "POL-18"]
def markExposed (n : Node) (l : Ledger) : Ledger :=
  l.map fun r =>
    if n.cands.any (fun c => c.id == r.cid && (c.released || c.broadcast)) then
      { r with exposed := true }
    else r

/-- `SPN-33`: "An unexposed retained charge may be refunded after its signed expiry strictly
passes or after a conflicting confirmation" — the first of those two, since the kernel's chain
view cannot tell a confirmation from a mempool sighting (see the header). `POL-21`: "the frozen
candidate's reservation is refunded at the expiry sweep that collects it, strictly after
Lockdown". The sample is the raw wall one, which is the sample `POL-19`'s expiry disjunct
reads. -/
@[req "SPN-33"]
def refundAtSweep (env : Env) (l : Ledger) : Ledger :=
  l.filter fun r => r.exposed || Wall.atOrBefore env.wall r.expiry

/-- `DEF-5`'s withdrawn rule (`F57`): a settlement refunds the reservation of every candidate it
touched — the settled id and the input-conflicting candidates `SPN-33` marks terminal — whatever
the evidence was and whether or not the partial had left. -/
def refundOnSettlement (n : Node) (l : Ledger) : Ledger :=
  l.filter fun r => !(n.cands.any fun c => c.id == r.cid && (c.settled || c.terminal))

/-! ## The guard parameter (`ADR-0023` decision 6), one `current` -/

/-- `SPN-33`: "Mempool-only settlement MUST NOT refund a reservation … Candidate terminality or
registry removal alone MUST NOT refund this charge." `refundOnAnySettlement` is `F57`'s `DEF-5`
row, where a settlement refunded the reservation on any evidence. It is a different flag from
milestone 4's pending-log projection, which `DEF-5` also got wrong. -/
inductive Settlement
  | retainOnMempool | refundOnAnySettlement
  deriving DecidableEq, Repr

def current : Settlement := .retainOnMempool

/-! ## The composed system -/

/-- The node of `Kernel.lean` and its Hot ledger, stepped together. -/
structure Sys where
  world : World
  led : Ledger
  deriving DecidableEq, Repr

/-- `POL-16`: a hot spend whose reservation would not fit "is refused `HOT_VELOCITY_EXCEEDED` /
`hot_budget_velocity` before signing", so the composed step registers nothing. -/
@[req "POL-16"]
def refusedByBudget (cfg : Config) (l : Ledger) : Event → Bool
  | .accept _ _ _ sp _ => sp.hot && !admits cfg l sp
  | _ => false

/-- The ledger's own transition for an event: `POL-18`'s reservation at an acceptance the
registration kept, `POL-21`'s refund at the expiry sweep, and under the withdrawn value `DEF-5`'s
refund at a settlement. Every other event moves nothing — `SPN-33`: "Candidate terminality or
registry removal alone MUST NOT refund this charge" — and `DUR-11`'s freeze is one of them. -/
@[req "POL-18"]
def afterEvent (g : Settlement) (env : Env) (before after : World) : Event → Ledger → Ledger
  | .accept cid _ _ sp _, l =>
    if sp.hot && after.node.carriers.any (fun k => k.cid == cid && k.accepted) &&
        !before.node.carriers.any (·.cid == cid) then reserve l sp env.mono else l
  | .prune, l => refundAtSweep env l
  | .settle _, l => match g with
    | .retainOnMempool => l
    | .refundOnAnySettlement => refundOnSettlement after.node l
  | .receivePartial _ _ _ _, l => l
  | _, l => l

/-- A budget refusal is staged (`SPN-5`), after commitments are available. -/
def budgetRefusal (r : Rules) (env : Env) (n : Node) : Event → Node
  | .accept cid d E sp es => refuse r env n cid d E (some (sp.id, es.id))
  | _ => n

/-- One composed step. The ledger ages first (`POL-19`), because that is the sum `POL-16` meters
against; a hot spend the check refuses registers nothing; then the event's own ledger transition
and the exposure bit. One step, so `SPN-29`'s "only a reservation placed by this request MUST be
unwound in the same step" has no intermediate state to be visible in, and `POL-21`'s "a
candidate's terminal removal and its release are one atomic step" holds by construction — the
atomicity is modelled, the lock is not (`Kernel`'s boundary hypotheses). -/
@[req "POL-16"]
def sysStep (g : Settlement) (cfg : Config) (r : Rules) (env : Env) (sys : Sys) (e : Event) :
    Sys × List Effect :=
  let aged := ageOut env cfg.window sys.led
  if refusedByBudget cfg aged e then
    ({ world := { sys.world with node := budgetRefusal r env sys.world.node e },
       led := markExposed sys.world.node aged }, [])
  else
    let after := (step r env sys.world e).1
    ({ world := after, led := markExposed after.node (afterEvent g env sys.world after e aged) },
     (step r env sys.world e).2)

/-- `Kernel.run`'s shape, with one difference: the step and the recursion are bound with plain
`let`s and read through `.1` and `.2` rather than destructured as a pair. A pattern match on a
pair does not reduce while its scrutinee is stuck, and the induction in `liveSum_le_cap` needs
`(sysRun … (x :: rest)).1` to reduce for an arbitrary event. -/
def sysRun (g : Settlement) (cfg : Config) (r : Rules) :
    Sys → List (Env × Event) → Sys × List Effect
  | sys, [] => (sys, [])
  | sys, (env, e) :: rest =>
    let stepped := sysStep g cfg r env sys e
    let ran := sysRun g cfg r stepped.1 rest
    (ran.1, stepped.2 ++ ran.2)

/-! ## The live sum never exceeds the cap (`POL-16`), by induction over the transitions -/

theorem liveSum_cons (r : Res) (l : Ledger) : liveSum (r :: l) = r.amount + liveSum l := rfl

theorem liveSum_append (a b : Ledger) : liveSum (a ++ b) = liveSum a + liveSum b := by
  simp [liveSum, List.map_append]

theorem liveSum_filter_le (l : Ledger) (p : Res → Bool) : liveSum (l.filter p) ≤ liveSum l := by
  induction l with
  | nil => simp [liveSum]
  | cons a as ih =>
    rw [List.filter_cons, liveSum_cons]
    split
    · rw [liveSum_cons]; omega
    · omega

theorem liveSum_map_eq (l : Ledger) (f : Res → Res) (hf : ∀ r, (f r).amount = r.amount) :
    liveSum (l.map f) = liveSum l := by
  unfold liveSum
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left fun r _ => hf r)

theorem liveSum_markExposed (n : Node) (l : Ledger) : liveSum (markExposed n l) = liveSum l :=
  liveSum_map_eq l _ fun _ => by split <;> rfl

/-- `POL-16`: "The reservation ledger is bounded at 4 096 entries; a full ledger refuses with the
same code and a detail naming the capacity rather than the window." A full ledger admits no new
commitment whatever the sums are, and a retry of one it already charges is not a new commitment. -/
@[req "POL-16"]
theorem full_ledger_refuses (cfg : Config) (l : Ledger) (c : Cand) (hfull : capacity ≤ l.length)
    (hnew : holds l c.id = false) : admits cfg l c = false := by
  simp [admits, hnew, Nat.not_lt.2 hfull]

/-- `POL-16`'s check is the invariant's inductive step: an admitted spend either is a retry, which
adds nothing, or fits under the cap. -/
@[req "POL-16"]
theorem liveSum_reserve_le_cap (cfg : Config) (l : Ledger) (c : Cand) (now : Mono)
    (h : admits cfg l c = true) (hc : liveSum l ≤ cfg.cap) :
    liveSum (reserve l c now) ≤ cfg.cap := by
  unfold reserve
  split
  · exact hc
  · rename_i hne
    simp only [admits, hne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [liveSum_append]
    simpa [liveSum] using h.2

theorem liveSum_afterEvent_le (g : Settlement) (cfg : Config) (env : Env) (before after : World)
    (e : Event) (l : Ledger) (hadm : refusedByBudget cfg l e = false) (hc : liveSum l ≤ cfg.cap) :
    liveSum (afterEvent g env before after e l) ≤ cfg.cap := by
  cases e with
  | accept cid d E sp es =>
    simp only [afterEvent]
    split
    · rename_i hres
      refine liveSum_reserve_le_cap cfg l sp env.mono ?_ hc
      simp only [refusedByBudget, Bool.and_eq_false_iff, Bool.not_eq_false'] at hadm
      simp only [Bool.and_eq_true] at hres
      rcases hadm with hnot | hyes
      · exact absurd hres.1.1 (by simp [hnot])
      · exact hyes
    · exact hc
  | prune => exact Nat.le_trans (liveSum_filter_le _ _) hc
  | settle tx =>
    simp only [afterEvent]
    split
    · exact hc
    · exact Nat.le_trans (liveSum_filter_le _ _) hc
  | refuse cid d E pair code | receipt cid s | firePass | packageAccepted c | send c | tick | panic
  | adversaryExposes m i s c | receivePartial m i s c => exact hc

/-- For every rule value, every environment and every event: a state at or under the cap steps to
a state at or under the cap. `POL-16` checks the sum at acceptance; every other transition only
releases, which is what makes the check an invariant — re-testing a retained row instead would
not (`F62`, `rerun_exceeds_cap`). -/
@[req "POL-16"]
theorem liveSum_sysStep (g : Settlement) (cfg : Config) (r : Rules) (env : Env) (sys : Sys)
    (e : Event) (h : liveSum sys.led ≤ cfg.cap) :
    liveSum (sysStep g cfg r env sys e).1.led ≤ cfg.cap := by
  have haged : liveSum (ageOut env cfg.window sys.led) ≤ cfg.cap :=
    Nat.le_trans (liveSum_filter_le _ _) h
  simp only [sysStep]
  split
  · rw [liveSum_markExposed]; exact haged
  · rename_i hadm
    rw [liveSum_markExposed]
    exact liveSum_afterEvent_le g cfg env sys.world _ e _ (by simpa using hadm) haged

/-- `POL-20`'s "each ledger holds at most `cap`", over every trace from a ledger under the cap. -/
@[req "POL-20"]
theorem liveSum_le_cap (g : Settlement) (cfg : Config) (r : Rules) :
    ∀ (tr : List (Env × Event)) (sys : Sys), liveSum sys.led ≤ cfg.cap →
      liveSum (sysRun g cfg r sys tr).1.led ≤ cfg.cap := by
  intro tr
  induction tr with
  | nil => intro sys h; exact h
  | cons x rest ih => intro sys h; exact ih _ (liveSum_sysStep g cfg r x.1 sys x.2 h)

/-! ## `POL-19`'s age-out, and what it does not release -/

/-- The no-age-out lemma. A reservation whose time lies in the trailing interval at the sweep's
sample survives the sweep: `POL-19`'s monotonic disjunct alone, both boundaries inclusive, with no
appeal to the wall disjunct and no use of `POL-17`'s `hot_window_secs ≥ max_commitment_age_secs`. -/
@[req "POL-19"]
theorem ageOut_keeps_in_window (env : Env) (window : Secs) (l : Ledger) (r : Res) (hr : r ∈ l)
    (hw : Mono.withinWindow r.reservedAt env.mono window = true) : r ∈ ageOut env window l := by
  refine List.mem_filter.2 ⟨hr, ?_⟩
  simp [reservationLive, hw]

/-- The same along a run of sweeps. Every sample is at or before the cut's, so a reservation
inside the cut's trailing interval was inside every earlier one and no sweep released it. Without
that premise the lemma is false: a charge released at one sample is live again at a later one,
which is the clock family `F60` and `F62` record. -/
@[req "POL-19"]
theorem sweeps_keep_in_window (window : Secs) (cut : Mono) (r : Res) :
    ∀ (envs : List Env) (l : Ledger), (∀ e ∈ envs, e.mono.notAfter cut = true) →
      Mono.withinWindow r.reservedAt cut window = true → r ∈ l →
      r ∈ envs.foldl (fun acc e => ageOut e window acc) l := by
  intro envs
  induction envs with
  | nil => intro l _ _ hr; exact hr
  | cons e rest ih =>
    intro l hall hcut hr
    exact ih _ (fun x hx => hall x (by simp [hx])) hcut
      (ageOut_keeps_in_window e window l r hr
        (Mono.withinWindow_of_notAfter (hall e (by simp)) hcut))

/-- `Kernel.MonotoneSamples` bounds every sample of a trace by its last: the premise the lemma
above consumes, carried on the trace rather than as a property of the clock type. -/
@[req "POL-19"]
theorem mono_le_last : ∀ (pre : List (Env × Event)) (last : Env × Event),
    MonotoneSamples (pre ++ [last]) →
    ∀ y ∈ pre ++ [last], y.1.mono.notAfter last.1.mono = true := by
  intro pre
  induction pre with
  | nil =>
    intro last _ y hy
    simp only [List.nil_append, List.mem_singleton] at hy
    subst hy
    exact Mono.notAfter_refl _
  | cons p ps ih =>
    intro last hm y hy
    have htail : MonotoneSamples (ps ++ [last]) := by
      cases ps with
      | nil => exact hm.2.2
      | cons q qs => exact hm.2.2
    have hall := ih last htail
    simp only [List.cons_append, List.mem_cons] at hy
    rcases hy with rfl | hy
    · cases ps with
      | nil => exact hm.2.1
      | cons q qs => exact Mono.notAfter_trans hm.2.1 (hall q (by simp))
    · exact hall y hy

/-- The two together, on a trace's own samples: a reservation inside the trailing interval at the
trace's LAST sample survives every AGE-OUT the trace's samples would run, given
`Kernel.MonotoneSamples` and nothing else. Age-out only: a refund is the other transition that
drops a row, and `POL-20`'s cohort excludes a refunded reservation by construction, because a
refunded row is not in the ledger the cut reads. `countsAt_of_reserved` is where this reaches the
cohort. -/
@[req "POL-19"]
theorem sweeps_keep_along_trace (window : Secs) (r : Res) (pre : List (Env × Event))
    (last : Env × Event) (hm : MonotoneSamples (pre ++ [last])) (l : Ledger)
    (hcut : Mono.withinWindow r.reservedAt last.1.mono window = true) (hr : r ∈ l) :
    r ∈ ((pre ++ [last]).map (·.1)).foldl (fun acc e => ageOut e window acc) l :=
  sweeps_keep_in_window window last.1.mono r _ l
    (fun e he => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
      exact mono_le_last pre last hm y hy)
    hcut hr

/-- `SPN-33`: "the ledger retains its original reservation time, expiry and exposure state
independently of candidate residency … Candidate terminality or registry removal alone MUST NOT
refund this charge." Under `.retainOnMempool`, the value the statement fixes, every event but the
expiry sweep keeps every charge the age-out kept —
settlement, which is `SPN-33`'s "Mempool-only settlement MUST NOT refund a reservation"; the
pruning of the candidate; the holder decision and its freeze; the fire pass; the send. The row
that comes out carries the same key, amount, time and expiry; only the exposure bit may have been
set. -/
@[req "SPN-33"]
theorem retained_outside_the_sweep (cfg : Config) (r : Rules) (env : Env) (sys : Sys) (e : Event)
    (he : e ≠ .prune) (row : Res) (hrow : row ∈ ageOut env cfg.window sys.led) :
    ∃ row' ∈ (sysStep .retainOnMempool cfg r env sys e).1.led,
      row'.cid = row.cid ∧ row'.amount = row.amount ∧ row'.reservedAt = row.reservedAt ∧
      row'.expiry = row.expiry := by
  have marked : ∀ (n : Node) (l : Ledger), row ∈ l →
      ∃ row' ∈ markExposed n l, row'.cid = row.cid ∧ row'.amount = row.amount ∧
        row'.reservedAt = row.reservedAt ∧ row'.expiry = row.expiry := by
    intro n l hl
    exact ⟨_, List.mem_map_of_mem hl, by split <;> rfl, by split <;> rfl, by split <;> rfl,
      by split <;> rfl⟩
  simp only [sysStep]
  split
  · exact marked _ _ hrow
  · refine marked _ _ ?_
    cases e with
    | prune => exact absurd rfl he
    | accept cid d E sp es =>
      simp only [afterEvent]
      split
      · unfold reserve
        split
        · exact hrow
        · exact List.mem_append_left _ hrow
      · exact hrow
    | settle tx => exact hrow
    | refuse cid d E pair code | receipt cid s | firePass | packageAccepted c | send c | tick | panic
    | adversaryExposes m i s c | receivePartial m i s c => exact hrow

/-! ## `POL-21`: the freeze is the identity on the ledger -/

/-- `POL-21`: "The duress freeze MUST NOT touch the ledger: a refund that happened only under
duress would be the timing signal `DUR-1` forbids". `DUR-11` freezes "every candidate with
`hot = true`, existing and future", so the bit is written in two places: the holder decision, and
the birth of a hot candidate on an armed node. This is the first — one write of `quorum`, `frozen`,
`armed`, `T`, `sweep_active`, the selected set and every selected window, with the Carrier's
retirement, and no field the ledger reads, so
the ledger after a holder decision is the ledger the node carried before it. The second writes
`frozen` on a candidate that has no row yet; the row `reserve` then gives it is unexposed whatever
the bit says. -/
@[req "POL-21"]
theorem holderDecision_is_identity_on_ledger (env : Env) (n : Node) (k : Carrier) (l : Ledger) :
    markExposed (holderDecision env n k) l = markExposed n l := by
  unfold markExposed holderDecision
  refine congrArg (List.map · l) (funext fun r => ?_)
  simp only [List.any_map, Function.comp_def, withWindow_id, withWindow_released,
    withWindow_broadcast]

/-- And therefore pin-uniform: one Carrier under either PIN leaves the same ledger. -/
@[req "DUR-1"]
theorem freeze_pin_uniform (env : Env) (n : Node) (k : Carrier) (l : Ledger) :
    markExposed (holderDecision env n { k with duress := true }) l =
      markExposed (holderDecision env n { k with duress := false }) l := by
  rw [holderDecision_is_identity_on_ledger, holderDecision_is_identity_on_ledger]

/-- `POL-21`: "the frozen candidate's reservation is refunded at the expiry sweep that collects
it, strictly after Lockdown". The first half is here: the sweep refunds only an unexposed charge
whose signed expiry has strictly passed (`SPN-33`), an exposed charge is never refunded and ages
under `POL-19` instead, and `retained_outside_the_sweep` shows that under `.retainOnMempool` no
other event refunds at all — so
a frozen candidate's charge does wait for the sweep.

The second half, the ordering against Lockdown, is NOT proved here and this module claims no part
of it: `T` and the Lockdown latch are `DUR-7`'s and the sweep reads neither, so the model has
nothing to order the two by. What would carry it is the two-run relation of milestone 7's fourth
ticket, where the ledger is not in `Obs` but is part of the relational invariant; the point of the
clause is that no ledger write differs between the two PINs, and the piece of that available here
is `freeze_pin_uniform` above. -/
@[req "POL-21"]
theorem sweep_refunds_only_unexposed_and_expired (env : Env) (l : Ledger) (r : Res) (hr : r ∈ l)
    (hgone : r ∉ refundAtSweep env l) :
    r.exposed = false ∧ Wall.atOrBefore env.wall r.expiry = false := by
  simp only [refundAtSweep] at hgone
  by_cases hx : r.exposed = true
  · exact absurd (List.mem_filter.2 ⟨hr, by simp [hx]⟩) hgone
  · by_cases hw : Wall.atOrBefore env.wall r.expiry = true
    · exact absurd (List.mem_filter.2 ⟨hr, by simp [hw]⟩) hgone
    · exact ⟨by simpa using hx, by simpa using hw⟩

/-! ## The bridge to `Ledgers.counting`

`Ledgers.counting` takes two hypotheses, not three: `hq` already fuses "at least `t − c` honest
acceptances" with "still charged at the cut", because the cohort below is read off the ledgers as
they stand at the cut. What the age-out lemmas add is `countsAt_of_reserved` — that a node which
reserved a spend inside its own trailing interval still counts it at the cut, so the cohort is
about the acceptance and not only about the state. -/

/-- One honest node at the cut: its ledger and its OWN HotClock sample (`POL-22`). No two samples
are ever compared, and `POL-20`'s trailing interval is computed at each node from its own
(`F61`). -/
structure NodeCut where
  led : Ledger
  now : Mono
  deriving DecidableEq, Repr

/-- `POL-20`: node `k` counts a spend when it holds a reservation for it "at a reservation time
inside that node's own interval", `[now_i − hot_window_secs, now_i]`, both boundaries inclusive. A
refunded reservation is not in the ledger, so the exclusion is PER RESERVATION and automatic;
`f61_per_spend_conclusion_false` is what the other reading costs. -/
@[req "POL-20"]
def countsAt (window : Secs) (id : Nat) (k : NodeCut) : Bool :=
  k.led.any fun r => r.cid == id && Mono.withinWindow r.reservedAt k.now window

/-- How many of the honest nodes count it. The list holds one entry per honest node — its length
is `POL-20`'s `n − c` — which is the caller's claim about the federation and not something a list
can check: a node entered twice inflates this count and the conclusion's `n − c` together. -/
@[req "POL-20"]
def cohortCount (window : Secs) (cuts : List NodeCut) (id : Nat) : Nat :=
  cuts.countP (countsAt window id)

/-- `hq`'s temporal half, and the no-age-out lemma's call site. A node that reserved a spend at a
time inside the cut's trailing interval still COUNTS it at the cut, after every sweep on the way:
`countsAt` is therefore a statement about the acceptance and not only about the state the cut
finds. The premise is `Kernel.MonotoneSamples`' consequence — every sample at or before the cut's
— and nothing else; drop it and `F62`'s wall step releases the charge at one sample and restores
it at a later one. -/
@[req "POL-20"]
theorem countsAt_of_reserved (window : Secs) (cut : Mono) (l : Ledger) (row : Res)
    (envs : List Env) (hsamples : ∀ e ∈ envs, e.mono.notAfter cut = true) (hr : row ∈ l)
    (hwin : Mono.withinWindow row.reservedAt cut window = true) :
    countsAt window row.cid
      { led := envs.foldl (fun acc e => ageOut e window acc) l, now := cut } = true := by
  refine List.any_eq_true.2 ⟨row, sweeps_keep_in_window window cut row envs l hsamples hwin hr, ?_⟩
  simp [hwin]

/-- `hq`. A node that counts a spend charges it, because the reservation it counted is a row it
holds. -/
@[req "POL-20"]
theorem cohortCount_le_charging (window : Secs) (cuts : List NodeCut) (id : Nat) :
    cohortCount window cuts id ≤ Ledgers.charging (cuts.map fun k => holds k.led) id := by
  unfold cohortCount Ledgers.charging
  rw [List.countP_map]
  apply List.countP_mono_left
  intro k _ hk
  simp only [countsAt, List.any_eq_true, Bool.and_eq_true] at hk
  obtain ⟨r, hr, hid, _⟩ := hk
  simp only [Function.comp_apply, holds, List.any_eq_true]
  exact ⟨r, hr, hid⟩

theorem sum_no_match (cid : Nat) : ∀ (cohort : List Ledgers.Spend),
    (∀ s ∈ cohort, s.1 ≠ cid) → (cohort.map fun s => if cid == s.1 then s.2 else 0).sum = 0 := by
  intro cohort
  induction cohort with
  | nil => simp
  | cons s rest ih =>
    intro h
    have hs : ¬ (cid = s.1) := fun he => h s (by simp) he.symm
    simp only [List.map_cons, List.sum_cons, ih fun x hx => h x (by simp [hx]),
      beq_eq_false_iff_ne.mpr hs, Bool.false_eq_true, ↓reduceIte]

/-- One row answers for at most one cohort spend: the cohort names each spend once, so what the
row contributes is its own amount. -/
theorem sum_match_le (r : Res) : ∀ (cohort : List Ledgers.Spend),
    (cohort.map (·.1)).Nodup → (∀ s ∈ cohort, s.1 = r.cid → s.2 = r.amount) →
    (cohort.map fun s => if r.cid == s.1 then s.2 else 0).sum ≤ r.amount := by
  intro cohort
  induction cohort with
  | nil => simp
  | cons s rest ih =>
    intro hnd hamt
    have hnd' : s.1 ∉ rest.map (·.1) ∧ (rest.map (·.1)).Nodup := by
      simpa [List.nodup_cons] using hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hs : r.cid = s.1
    · have hval : s.2 = r.amount := hamt s (by simp) hs.symm
      have hrest : ∀ x ∈ rest, x.1 ≠ r.cid := by
        intro x hx he
        exact hnd'.1 (List.mem_map.2 ⟨x, hx, by rw [he, hs]⟩)
      rw [sum_no_match r.cid rest hrest]
      simp [hs, hval]
    · simp only [beq_eq_false_iff_ne.mpr hs, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih hnd'.2 (fun x hx => hamt x (by simp [hx]))

/-- `hcap`. What a ledger charges over the cohort is at most its live sum, given the two pieces of
well-formedness `Ledgers.charge` does not assume: the cohort names each spend once, and a cohort
amount is the amount the node stored for it. -/
@[req "POL-20"]
theorem charge_le_liveSum (cohort : List Ledgers.Spend) (hnd : (cohort.map (·.1)).Nodup) :
    ∀ (l : Ledger), (∀ s ∈ cohort, ∀ r ∈ l, r.cid = s.1 → r.amount = s.2) →
      Ledgers.charge cohort (holds l) ≤ liveSum l := by
  intro l
  induction l with
  | nil => intro _; simp [Ledgers.charge, holds, liveSum, Ledgers.sum_map_zero]
  | cons r rest ih =>
    intro hamt
    have step : Ledgers.charge cohort (holds (r :: rest)) ≤
        (cohort.map fun s => if r.cid == s.1 then s.2 else 0).sum +
          Ledgers.charge cohort (holds rest) := by
      unfold Ledgers.charge
      rw [← Ledgers.sum_map_add]
      apply Ledgers.sum_map_le
      intro s _
      simp only [holds, List.any_cons]
      rcases Bool.eq_false_or_eq_true (r.cid == s.1) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (rest.any fun x => x.cid == s.1) with h2 | h2 <;>
        simp [h1, h2]
    have h1 : (cohort.map fun s => if r.cid == s.1 then s.2 else 0).sum ≤ r.amount :=
      sum_match_le r cohort hnd (fun s hs he => (hamt s hs r (by simp) he.symm).symm)
    have h2 : Ledgers.charge cohort (holds rest) ≤ liveSum rest :=
      ih fun s hs x hx => hamt s hs x (by simp [hx])
    rw [liveSum_cons]
    omega

/-- The accounting bridge. `POL-20`'s cohort at one cut, over honest ledgers each holding at most
`cap`, admits at most `((n − c) / (t − c)) × cap` of outflow — the bound cleared of its division,
`q × A ≤ (n − c) × cap`, with `q` for `t − c` and `cuts.length` for `n − c`. Both hypotheses of
`Ledgers.counting` are discharged here, from four this theorem takes instead: `hinv` is what
`liveSum_le_cap` gives for any node that ran the transitions, `hcohort` is what
`countsAt_of_reserved` gives for any node that reserved inside its own interval, and `hnd` and
`hamt` are the well-formedness `Ledgers.charge` does not assume. What no theorem can supply is
which nodes are honest. -/
@[req "POL-20"]
theorem bridge (cfg : Config) (q : Nat) (cohort : List Ledgers.Spend) (cuts : List NodeCut)
    (hnd : (cohort.map (·.1)).Nodup)
    (hamt : ∀ k ∈ cuts, ∀ s ∈ cohort, ∀ r ∈ k.led, r.cid = s.1 → r.amount = s.2)
    (hinv : ∀ k ∈ cuts, liveSum k.led ≤ cfg.cap)
    (hcohort : ∀ s ∈ cohort, q ≤ cohortCount cfg.window cuts s.1) :
    q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap := by
  have hlen : (cuts.map fun k => holds k.led).length = cuts.length := List.length_map _
  have h := Ledgers.counting cohort (cuts.map fun k => holds k.led) cfg.cap q
    (by
      intro l hl
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
      exact Nat.le_trans (charge_le_liveSum cohort hnd k.led fun s hs r hr => hamt k hk s hs r hr)
        (hinv k hk))
    (fun s hs => Nat.le_trans (hcohort s hs) (cohortCount_le_charging cfg.window cuts s.1))
  rwa [hlen] at h

/-- `POL-20` at `c = 0` for the production shape `n = 2t − 1`: `t × A ≤ (2t − 1) × cap`, the
cleared form of the coefficient `(2 − 1/t)` that `Budget.coef_c0` computes. -/
@[req "POL-20"]
theorem bridge_c0 (cfg : Config) (t : Nat) (cohort : List Ledgers.Spend) (cuts : List NodeCut)
    (hn : cuts.length + 1 = 2 * t)
    (hnd : (cohort.map (·.1)).Nodup)
    (hamt : ∀ k ∈ cuts, ∀ s ∈ cohort, ∀ r ∈ k.led, r.cid = s.1 → r.amount = s.2)
    (hinv : ∀ k ∈ cuts, liveSum k.led ≤ cfg.cap)
    (hcohort : ∀ s ∈ cohort, t ≤ cohortCount cfg.window cuts s.1) :
    t * Ledgers.outflow cohort ≤ (2 * t - 1) * cfg.cap := by
  have h := bridge cfg t cohort cuts hnd hamt hinv hcohort
  rwa [show cuts.length = 2 * t - 1 by omega] at h

/-! ## The cases the model is stated against -/

/-- A clock reading for the cases below: one raw wall sample and one HotClock sample, with no
high-water advance and an empty chain view. -/
def envOf (wall mono : Nat) : Env :=
  { wall := Wall.sample wall, hw := HighWater.sample 0, mono := Mono.sample mono,
    chain := { mtp := Mtp.sample 0, seen := [] } }

/-- A row, written out. -/
def row (cid amount reservedAt expiry : Nat) : Res :=
  { cid := cid, amount := amount, reservedAt := Mono.sample reservedAt,
    expiry := Wall.sample expiry, exposed := false }

/-- `F62`. A charge of the whole cap reserved at HotClock 0 against a window of 120 with a signed
expiry of 1120 is dead at `(mono 121, wall 1121)` — both of `POL-19`'s disjuncts false — so the
node reclaims its budget and admits a second charge of the whole cap. A wall correction to 1100,
the family `F60` records, puts `wall_now ≤ expiry` back. Re-tested over a RETAINED row the first
charge is live again beside the second and the live sum stands at twice the cap, so `POL-20`'s
"each ledger holds at most `cap`" is false at a reachable state. Released one-way the row is gone
and the sum is the cap: the invariant above is provable for one model and not for the other. -/
@[req "POL-19"]
theorem rerun_exceeds_cap :
    ageOut (envOf 1121 121) 120 [row 1 100 0 1120] = [] ∧
    liveSum (ageOut (envOf 1100 121) 120
      (ageOut (envOf 1121 121) 120 [row 1 100 0 1120] ++ [row 2 100 121 1241])) = 100 ∧
    liveSum (ageOut (envOf 1100 121) 120 [row 1 100 0 1120, row 2 100 121 1241]) = 200 := by
  decide

/-- The bridge is not vacuous, and the cohort it counts is the node-indexed one. 2-of-3 at
`c = 0`, cap 100, window 120, one spend of the whole cap, reserved at each of the three honest
nodes at a time inside THAT node's trailing interval — at HotClock 0, 900 and 99 999, against
samples 10, 1 000 and 100 000. No interval of `hot_window_secs` holds all three, so the cohort
`cohortCount` counts is not one the global reading `F61` withdrew would have. Each hypothesis is
decided, and the conclusion is `2 × 100 ≤ 3 × 100`. -/
@[req "POL-20"]
theorem bridge_nonvacuous :
    2 * Ledgers.outflow [(1, 100)] ≤
      ([{ led := [row 1 100 0 1120], now := Mono.sample 10 },
        { led := [row 1 100 900 1120], now := Mono.sample 1000 },
        { led := [row 1 100 99999 1120], now := Mono.sample 100000 }] : List NodeCut).length * 100 :=
  bridge { cap := 100, window := 120 } 2 [(1, 100)] _ (by decide) (by decide) (by decide) (by decide)

/-- Three honest nodes, three spends of 100, `q = t − c = 2`: each spend was accepted by two of
them and one of the two reservations was refunded while unexposed, so each node is left charging
one spend. Read per reservation each spend holds one charge, is under `q`, and is out of the
cohort. Read per spend all three stay in, and the counting theorem's CONCLUSION is false on that
cohort — `2 × 300 > 3 × 100` — not merely unproved. This is `F61`'s second row; its first, the
cohort that is node-indexed and not global, is `bridge_nonvacuous`. -/
@[req "POL-20"]
theorem f61_per_spend_conclusion_false :
    let cohort : List Ledgers.Spend := [(1, 100), (2, 100), (3, 100)]
    let cuts : List NodeCut :=
      [{ led := [row 1 100 0 1120], now := Mono.sample 10 },
       { led := [row 2 100 0 1120], now := Mono.sample 10 },
       { led := [row 3 100 0 1120], now := Mono.sample 10 }]
    let ledgers := cuts.map fun k => holds k.led
    (∀ l ∈ ledgers, Ledgers.charge cohort l ≤ 100) ∧
    (∀ s ∈ cohort, Ledgers.charging ledgers s.1 = 1) ∧
    (∀ s ∈ cohort, cohortCount 120 cuts s.1 = 1) ∧
    ¬ (2 * Ledgers.outflow cohort ≤ ledgers.length * 100) := by
  decide

namespace RegistrationCases
open Kernel.RegistrationCases

def cfg : Config := { cap := 1000, window := 120 }
def initial : Sys := { world := w0, led := [] }
def accepted (r : Rules) : Sys :=
  (sysStep .retainOnMempool cfg r env0 initial (.accept 10 false (Wall.sample 200) c1 e1)).1

/-- Composed ingress within the live reservation window: keep the earlier row on a shared-spend
conflict, and leave no new row on a shared-Escape conflict. The ledger places rows only after
registration succeeds, abstracting the request-local placement and unwind as one step. -/
def refusalChecks (r : Rules) : Bool :=
  let before := accepted r
  before.led == [{
    cid := 1, amount := 100, reservedAt := Mono.sample 5,
    expiry := Wall.sample 200, exposed := false }] &&
  [false, true].all fun d =>
    [(c1, e2), (c2, e1)].all fun (sp, es) =>
      let after := sysStep .retainOnMempool cfg r envBack before
        (.accept 11 d (Wall.sample 200) sp es)
      after.1.led == before.led && after.1.world.node.cands == before.world.node.cands &&
        after.1.world.node.carriers.any (fun k => k.cid == 11 && !k.accepted) && after.2 == []

end RegistrationCases

namespace RefusalCases
open Kernel.RegistrationCases

def cfg : Config := { cap := 100, window := 120 }
def initial (r : Rules) : Sys :=
  (sysStep .retainOnMempool cfg r env0 { world := w0, led := [] }
    (.accept 10 false (Wall.sample 200) c1 e1)).1

/-- Budget refusal and both directions of registration refusal, within the older reservation's
live window. The holder receipt arms only with duress and cannot open the resident pair. -/
def checks (r : Rules) : Bool :=
  [false, true].all fun d =>
    let before := initial r
    [(.accept 11 d (Wall.sample 400) c3 e3),
     (.accept 11 d (Wall.sample 200) c1 e2),
     (.accept 11 d (Wall.sample 200) c2 e1)].all fun e =>
      let cfg' := if e == .accept 11 d (Wall.sample 400) c3 e3 then cfg else { cfg with cap := 1000 }
      let s := (sysStep .retainOnMempool cfg' r envBack before e).1
      let after := (sysStep .retainOnMempool cfg' r (envAt 70 30) s (.receipt 11 1)).1
      s.led == before.led && s.world.node.cands == before.world.node.cands &&
      s.world.node.carriers.any (fun k => k.cid == 11 && !k.accepted) &&
      commits (envAt 70 30) s.world.node 11 1 && after.led == before.led &&
      after.world.node.armed == d &&
      after.world.node.cands.map (fun c => (c.id, c.quorum)) ==
        before.world.node.cands.map (fun c => (c.id, c.quorum)) &&
      after.world.node.cands.map Kernel.RefusalCases.residentFields ==
        before.world.node.cands.map Kernel.RefusalCases.residentFields

end RefusalCases

end BtcPolicy.Ledger
