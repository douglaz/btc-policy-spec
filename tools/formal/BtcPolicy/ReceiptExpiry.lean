import BtcPolicy.FedSilence
/-! Receipt-time expiry as a state transition (`NCH-24`, `SPN-41`, `POL-18`). A layer beside the existing
definitions: no definition or theorem statement changes, and no kernel event is added.

**The rule.** `NCH-24` says that on a `partial` the receiver checks, under the store lock, that "the candidate
exists, else `UNKNOWN_CANDIDATE`; it is not expired (`expiry < now`, except the delayed-slot exemption of
`SPN-41`), else evict it, refund its unexposed reservation when `POL-18` makes it refundable". The kernel's
`Kernel.receivePartial` takes no clock and states this lookup as a boundary hypothesis. Here the lookup reads the
step's own sample:

- `ReceiptExpiry.keepsAt` is `Kernel.prune`'s expiry-or-exemption keep test, one candidate at a time: the
  candidate's expiry has not passed at effective time, or a non-broadcast Escape whose fire window is open shares
  its pair (`Kernel.exemptEscape`). The comparison is strict: at `now == expiry` the candidate is unexpired
  (`Exhibits.ReceiptExpiry.equality_unexpired`). The exemption reads the installed window and no duress bit, so it
  holds for the normal PIN's inert slot as for the duress slot.
- `ReceiptExpiry.lookup` finds the first record under the commitment id: none is `unknown`, a record the keep test
  rejects is `expired`, any other is `live`. `ReceiptExpiry.answer` is `UNKNOWN_CANDIDATE` unless the lookup is
  live.
- `ReceiptExpiry.receive` evicts on `expired`: every record under that id the keep test rejects leaves the
  registry (`ReceiptExpiry.evict`), and nothing is stored. Otherwise it is `Kernel.receivePartial` itself
  (`ReceiptExpiry.receive_unexpired`). Every record the lookup evicts is one the prune pass at the same sample would
  collect (`ReceiptExpiry.evicted_pruned`). The lookup does not run `SPN-41`'s armed removal, which is the prune
  pass's own conjunct. The pending log is not touched.
- The world step appends the arriving partial to the exposure history in every case, as `Kernel.step` does for
  `receivePartial`: a refusal or an eviction removes no row (`ReceiptExpiry.wstep_exposure`), and at the federation
  level the partial inventory, the relays and the extracted set are unchanged (`ReceiptExpiry.xapply_inventories`).
  Authority read from that history is never revoked by the receipt.

**The ledger.** `ReceiptExpiry.sysRecv` is the node and its Hot ledger stepped together, as `Ledger.sysStep`
steps them. At an eviction the ledger takes `Ledger.refundAtPrune` against the node the eviction leaves: the
refund is `POL-18`'s condition, "unexposed, its signed expiry has strictly passed on the wall sample `POL-19`'s
expiry disjunct reads, and its candidate is no longer resident", whether `SPN-41`'s prune pass or `NCH-24`'s
lookup removed the candidate. A row the eviction drops was unexposed, past its expiry on the wall sample, and
its commitment is no longer resident (`ReceiptExpiry.refund_only_permitted`); an exposed row keeps its key,
amount, reservation time and expiry (`ReceiptExpiry.exposed_kept`). Refundability is read off this node's own
row for this commitment, never off world-level authority, and the accounting unit stays the commitment. Without
an eviction the step is `Ledger.sysStep` on `Kernel.Event.receivePartial` for every guard value
(`ReceiptExpiry.sysRecv_unexpired`).

**The federation.** `ReceiptExpiry.xapply` is `FedSilence.lapply` with a delivered partial taken through
`sysRecv`. On a schedule where no delivery evicts, its run is `FedSilence.lrun` (`ReceiptExpiry.xrun_lrun`), so
every result over the ledgered run and over `Federation.Execution` applies (`ReceiptExpiry.xrun_execution`).
`ReceiptExpiry.Unevicted` says that of a composed trace: at every delivery the receiving node's lookup is not
expired. The rung lifecycle run is such a trace (`Exhibits.ReceiptExpiry.lifecycle_unevicted`).

**The observer.** `ReceiptExpiry.XObs` is `FedSilence.FObs` with the channel answer to a delivered partial:
receiver, sender and `ReceiptExpiry.Answer`. Its local observation is taken on the state the receipt actually
leaves. Off an eviction its `FObs` part is `FedSilence.fobs` (`ReceiptExpiry.xfobs_unevicted`); the answer is
new, and it separates an eviction from a store (`Exhibits.ReceiptExpiry.answer_detects_expiry`).

**Duplicates.** A second copy of a stored partial leaves the registry as the first left it
(`ReceiptExpiry.receive_duplicate`, from `Kernel.addHeld_of_held`). `VariantReceipt`'s first-record rule is
unchanged and reads the same history.

**Outside.** The checks `NCH-24` lists before the lookup and after it (wallet, signer equals sender, sighash
type, rung by txid, user-signature hash, ranges, signature verification) are as `Kernel.receivePartial` and
`VariantReceipt.storable` model them; `Answer.found` means only that the lookup passed. The answer's wire bytes,
the response timing, the store lock and `NCH-8`'s sender back-off are outside. No SILENCE theorem is stated over
`XObs` here. -/

namespace BtcPolicy.ReceiptExpiry

open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence

/-! ## The lookup -/

/-- `NCH-24`'s expiry test at the lookup, "`expiry < now`, except the delayed-slot exemption of `SPN-41`": the
candidate stays if its expiry has not passed at effective time, or if an exempt Escape shares its pair. This is
`Kernel.prune`'s first keep conjunct, for one candidate. -/
@[req "NCH-24"]
def keepsAt (env : Env) (n : Node) (c : Cand) : Bool :=
  env.eff.atOrBefore c.expiry || n.cands.any fun e => e.pair == c.pair && exemptEscape env e

/-- The three outcomes of the lookup. -/
inductive Lookup
  | unknown | expired | live
  deriving DecidableEq, Repr

/-- `NCH-24`: "the candidate exists, else `UNKNOWN_CANDIDATE`; it is not expired". -/
@[req "NCH-24"]
def lookup (env : Env) (n : Node) (cid : Nat) : Lookup :=
  match n.cands.find? (·.id == cid) with
  | none => .unknown
  | some c => if keepsAt env n c then .live else .expired

/-- The lookup evicts. -/
def evicts (env : Env) (n : Node) (cid : Nat) : Bool := lookup env n cid == .expired

/-- `NCH-24`'s "else evict it": every record under the id that the keep test rejects leaves the registry. -/
@[req "NCH-24"]
def evict (env : Env) (n : Node) (cid : Nat) : Node :=
  { n with cands := n.cands.filter fun c => !(c.id == cid && !keepsAt env n c) }

/-- The channel answer the lookup decides: `UNKNOWN_CANDIDATE`, or `found` when the lookup passed and the rest of
`NCH-24`'s list applies. -/
inductive Answer
  | unknownCandidate | found
  deriving DecidableEq, Repr

/-- `NCH-24`: a missing candidate and an evicted one both answer `UNKNOWN_CANDIDATE`. -/
@[req "NCH-24"]
def answer (env : Env) (n : Node) (cid : Nat) : Answer :=
  match lookup env n cid with
  | .live => .found
  | _ => .unknownCandidate

/-- The receipt: an eviction stores nothing; otherwise `Kernel.receivePartial`. -/
@[req "NCH-24"]
def receive (env : Env) (n : Node) (m : Sighash) (i s cid : Nat) : Node :=
  if evicts env n cid then evict env n cid else receivePartial n m i s cid

theorem receive_unexpired {env : Env} {n : Node} {cid : Nat} (h : evicts env n cid = false)
    (m : Sighash) (i s : Nat) : receive env n m i s cid = receivePartial n m i s cid := by
  simp [receive, h]

theorem answer_unknown_iff (env : Env) (n : Node) (cid : Nat) :
    answer env n cid = .unknownCandidate ↔ lookup env n cid ≠ .live := by
  unfold answer
  cases lookup env n cid <;> simp

/-- An eviction answers `UNKNOWN_CANDIDATE`. -/
@[req "NCH-24"]
theorem evicts_answer {env : Env} {n : Node} {cid : Nat} (h : evicts env n cid = true) :
    answer env n cid = .unknownCandidate := by
  simp only [evicts, beq_iff_eq] at h
  simp [answer, h]

/-- The lookup evicts only past the candidate's expiry at effective time: at `now == expiry`, or before, the
first record under the id stays. -/
@[req "NCH-24"]
theorem evicts_strict {env : Env} {n : Node} {cid : Nat} (h : evicts env n cid = true) :
    ∃ c, n.cands.find? (·.id == cid) = some c ∧ env.eff.atOrBefore c.expiry = false ∧
      (n.cands.any fun e => e.pair == c.pair && exemptEscape env e) = false := by
  simp only [evicts, lookup, beq_iff_eq] at h
  split at h
  · cases h
  · rename_i c hc
    by_cases hk : keepsAt env n c = true
    · simp [hk] at h
    · simp only [keepsAt, Bool.or_eq_true, not_or, Bool.not_eq_true] at hk
      exact ⟨c, hc, hk.1, hk.2⟩

/-- `SPN-41`: "`expiry < now` is expired at lookup as well as at prune". Every record the lookup evicts is one the
prune pass at the same sample collects. -/
@[req "SPN-41"]
theorem evicted_pruned {env : Env} {n : Node} {cid : Nat} {c : Cand} (hc : c ∈ n.cands)
    (hgone : c ∉ (evict env n cid).cands) : c ∉ (prune env n).cands := by
  intro hp
  simp only [prune, List.mem_filter, Bool.and_eq_true] at hp
  apply hgone
  simp only [evict, List.mem_filter]
  refine ⟨hc, ?_⟩
  simp [keepsAt, hp.2.1]

/-- The registry the eviction leaves holds no record under the id the keep test rejects, and every other record. -/
theorem mem_evict {env : Env} {n : Node} {cid : Nat} {c : Cand} :
    c ∈ (evict env n cid).cands ↔ c ∈ n.cands ∧ (c.id ≠ cid ∨ keepsAt env n c = true) := by
  simp only [evict, List.mem_filter]
  constructor
  · rintro ⟨hc, hk⟩
    refine ⟨hc, ?_⟩
    by_cases hi : c.id = cid
    · right; simpa [hi] using hk
    · left; exact hi
  · rintro ⟨hc, hk⟩
    refine ⟨hc, ?_⟩
    rcases hk with hi | hk
    · simp [hi]
    · simp [hk]

/-- `Kernel.receivePartial`'s write to one record. -/
def stored (m : Sighash) (i s cid : Nat) (c : Cand) : Cand :=
  if c.id == cid && i == 0 && m == sighash c.tx 0 then { c with heldSigners := addHeld c.heldSigners s } else c

theorem receivePartial_stored (n : Node) (m : Sighash) (i s cid : Nat) :
    receivePartial n m i s cid = { n with cands := n.cands.map (stored m i s cid) } := rfl

theorem stored_fields (m : Sighash) (i s cid : Nat) (c : Cand) :
    (stored m i s cid c).id = c.id ∧ (stored m i s cid c).tx = c.tx ∧ (stored m i s cid c).pair = c.pair ∧
      (stored m i s cid c).expiry = c.expiry ∧ (stored m i s cid c).broadcast = c.broadcast ∧
      (stored m i s cid c).windowClose = c.windowClose ∧ (stored m i s cid c).isEscape = c.isEscape := by
  unfold stored; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stored_stored (m : Sighash) (i s cid : Nat) (c : Cand) :
    stored m i s cid (stored m i s cid c) = stored m i s cid c := by
  unfold stored
  by_cases hc : (c.id == cid && i == 0 && m == sighash c.tx 0) = true
  · simp only [hc, if_true]
    have hm : (addHeld c.heldSigners s).contains s = true := by
      unfold addHeld; split
      · assumption
      · simp
    have h2 : addHeld (addHeld c.heldSigners s) s = addHeld c.heldSigners s := if_pos hm
    simp only [h2]
  · simp only [hc, Bool.false_eq_true, if_false]

/-- The receipt's store moves no field the lookup reads, so it moves no lookup. -/
theorem lookup_stored (env : Env) (n : Node) (m : Sighash) (i s cid k : Nat) :
    lookup env (receivePartial n m i s cid) k = lookup env n k := by
  have hex : ∀ e, exemptEscape env (stored m i s cid e) = exemptEscape env e := by
    intro e
    obtain ⟨_, _, _, _, hb, hw, he⟩ := stored_fields m i s cid e
    simp only [exemptEscape, hb, hw, he]
  have hany : ∀ p : Option (Nat × Nat), ((n.cands.map (stored m i s cid)).any
      fun e => e.pair == p && exemptEscape env e) = (n.cands.any fun e => e.pair == p && exemptEscape env e) := by
    intro p
    simp only [List.any_map]
    congr 1
    funext e
    simp only [Function.comp, (stored_fields m i s cid e).2.2.1, hex]
  have hp : ((fun c : Cand => c.id == k) ∘ stored m i s cid) = fun c => c.id == k := by
    funext c
    simp only [Function.comp, (stored_fields m i s cid c).1]
  simp only [lookup, receivePartial_stored, List.find?_map, hp]
  cases n.cands.find? (·.id == k) with
  | none => rfl
  | some c =>
    simp only [Option.map_some, keepsAt, (stored_fields m i s cid c).2.2.1, (stored_fields m i s cid c).2.2.2.1,
      hany]
    rfl

/-- A second copy of a partial the lookup admits leaves the registry as the first copy left it. -/
@[req "NCH-25"]
theorem receive_duplicate (env : Env) (n : Node) (m : Sighash) (i s cid : Nat)
    (h : evicts env n cid = false) :
    receive env (receive env n m i s cid) m i s cid = receive env n m i s cid := by
  have hev : evicts env (receivePartial n m i s cid) cid = false := by
    simpa only [evicts, lookup_stored] using h
  rw [receive_unexpired h, receive_unexpired hev, receivePartial_stored, receivePartial_stored]
  simp only [List.map_map]
  congr 2
  funext c
  exact stored_stored m i s cid c

/-! ## The world and the ledger -/

/-- The world step: the node takes the receipt, and the arriving partial joins the exposure history whatever the
lookup decides, as `Kernel.step` appends it for `receivePartial`. -/
def wstep (env : Env) (w : World) (m : Sighash) (i s cid : Nat) : World :=
  { node := receive env w.node m i s cid,
    exposure := w.exposure ++ [{ msg := m, input := i, signer := s, hot := true, cid := cid }] }

/-- No receipt removes an exposure row: earlier exposed authority stays in the history. -/
@[req "NCH-24"]
theorem wstep_exposure (env : Env) (w : World) (m : Sighash) (i s cid : Nat) :
    (wstep env w m i s cid).exposure = w.exposure ++ [{ msg := m, input := i, signer := s, hot := true, cid := cid }] :=
  rfl

/-- The node and its Hot ledger, stepped together. The ledger the step starts from is `Ledger.sysStep`'s for a
`receivePartial` (`POL-19`'s release where `Ledger.checked` evaluates it, kept as `Ledger.kept` keeps it); at an
eviction, `POL-18`'s refund against the node the eviction leaves; then the exposure bit. -/
@[req "POL-18"]
def sysRecv (g : Guards) (cfg : Config) (env : Env) (sys : Sys) (m : Sighash) (i s cid : Nat) : Sys :=
  let after := wstep env sys.world m i s cid
  let base := kept g.release (checked g.release env cfg.window sys.led (.receivePartial m i s cid)) sys.led false
  { world := after,
    led := markExposed after.node
      (if evicts env sys.world.node cid then refundAtPrune g.refund env after.node base else base) }

/-- **Without an eviction the step is the old one**, for every guard value. -/
theorem sysRecv_unexpired (g : Guards) (cfg : Config) (r : Rules) (env : Env) (sys : Sys) (m : Sighash)
    (i s cid : Nat) (h : evicts env sys.world.node cid = false) :
    sysRecv g cfg env sys m i s cid = (sysStep g cfg r env sys (.receivePartial m i s cid)).1 := by
  simp only [sysRecv, wstep, receive, h, Bool.false_eq_true, if_false]
  simp [sysStep, refusedByBudget, step, afterEvent, admitted]

/-- The world the step leaves is `wstep`'s. -/
theorem sysRecv_world (g : Guards) (cfg : Config) (env : Env) (sys : Sys) (m : Sighash) (i s cid : Nat) :
    (sysRecv g cfg env sys m i s cid).world = wstep env sys.world m i s cid := rfl

/-- **Only `POL-18`'s refund.** Under `Release.acceptedAdmission` and `Refund.onCollection`: a row the receipt
drops was unexposed, its signed expiry strictly passed on the wall sample, and no record under its commitment is
resident in the node the receipt leaves; and the receipt evicted. -/
@[req "POL-18"]
theorem refund_only_permitted (g : Guards) (hr : g.release = .acceptedAdmission)
    (hf : g.refund = .onCollection) (cfg : Config) (env : Env) (sys : Sys) (m : Sighash) (i s cid : Nat)
    (row : Res) (hrow : row ∈ sys.led) (hgone : holds (sysRecv g cfg env sys m i s cid).led row.cid = false) :
    evicts env sys.world.node cid = true ∧ row.exposed = false ∧ Wall.atOrBefore env.wall row.expiry = false ∧
      (sysRecv g cfg env sys m i s cid).world.node.cands.any (·.id == row.cid) = false := by
  simp only [sysRecv, holds_markExposed, checked, hr, hotRequest, Bool.false_eq_true, if_false, kept] at hgone
  cases he : evicts env sys.world.node cid
  · simp only [he, Bool.false_eq_true, if_false] at hgone
    exact absurd (holds_of_mem hrow) (by rw [hgone]; simp)
  · simp only [he, if_true, hf] at hgone
    obtain ⟨h1, h2, h3⟩ := prune_refunds_only_unexposed_and_expired .onCollection rfl env _ sys.led row hrow
      (fun hin => absurd (holds_of_mem hin) (by rw [hgone]; simp))
    exact ⟨rfl, h1, h2, h3⟩

/-- **An exposed reservation stays.** Under `Release.acceptedAdmission`, for every refund rule: an exposed row
comes out of the receipt with its key, amount, reservation time and expiry, still exposed. -/
@[req "POL-18"]
theorem exposed_kept (g : Guards) (hr : g.release = .acceptedAdmission) (cfg : Config) (env : Env) (sys : Sys)
    (m : Sighash) (i s cid : Nat) (row : Res) (hrow : row ∈ sys.led) (hx : row.exposed = true) :
    ∃ row' ∈ (sysRecv g cfg env sys m i s cid).led, row'.cid = row.cid ∧ row'.amount = row.amount ∧
      row'.reservedAt = row.reservedAt ∧ row'.expiry = row.expiry ∧ row'.exposed = true := by
  have hin : row ∈ (if evicts env sys.world.node cid then
      refundAtPrune g.refund env (wstep env sys.world m i s cid).node sys.led else sys.led) := by
    split
    · simp only [refundAtPrune, List.mem_filter]
      exact ⟨hrow, by simp [hx]⟩
    · exact hrow
  have hfix : ∀ n : Node, (if n.cands.any (fun c => c.id == row.cid && (c.released || c.broadcast)) then
      { row with exposed := true } else row) = row := by
    intro n
    split
    · cases row
      simp_all
    · rfl
  refine ⟨row, ?_, rfl, rfl, rfl, rfl, hx⟩
  simp only [sysRecv, checked, hr, hotRequest, Bool.false_eq_true, if_false, kept, markExposed]
  exact List.mem_map.2 ⟨row, hin, hfix _⟩

/-! ## The federation -/

/-- `FedSilence.lapply`, with a delivered partial taken through `sysRecv`. -/
def xapply (g : Guards) (cfg : Config) (r : Rules) (F : LFed) : Federation.Step → LFed
  | .deliverPartial i env x =>
    let st := sysRecv g cfg env (F.sys i) x.msg x.input x.signer x.cid
    { fed := { F.fed with worlds := fun j => if j = i then st.world else F.fed.worlds j },
      leds := fun j => if j = i then st.led else F.leds j }
  | s => lapply g cfg r F s

/-- Whether a step is a delivery the receiving node's lookup evicts on. -/
def evictsAt (F : LFed) : Federation.Step → Bool
  | .deliverPartial i env x => evicts env (F.fed.worlds i).node x.cid
  | _ => false

/-- A schedule run through `xapply`. -/
def xrun (g : Guards) (cfg : Config) (r : Rules) : LFed → List Federation.Step → LFed
  | F, [] => F
  | F, s :: ss => xrun g cfg r (xapply g cfg r F s) ss

/-- Every step admitted where `xapply`'s run takes it. -/
def xlegal (g : Guards) (cfg : Config) (r : Rules) (honest : List Nat) : LFed → List Federation.Step → Bool
  | _, [] => true
  | F, s :: ss => Federation.admits honest F.fed s && xlegal g cfg r honest (xapply g cfg r F s) ss

/-- No step of the schedule is an evicting delivery, where `xapply`'s run takes it. -/
def unevicted (g : Guards) (cfg : Config) (r : Rules) : LFed → List Federation.Step → Bool
  | _, [] => true
  | F, s :: ss => !evictsAt F s && unevicted g cfg r (xapply g cfg r F s) ss

theorem xapply_unevicted (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (s : Federation.Step)
    (h : evictsAt F s = false) : xapply g cfg r F s = lapply g cfg r F s := by
  cases s with
  | deliverPartial i env x =>
    simp only [evictsAt] at h
    simp only [xapply, lapply, LFed.advance]
    rw [sysRecv_unexpired g cfg r env (F.sys i) x.msg x.input x.signer x.cid (by simpa [LFed.sys] using h)]
  | _ => rfl

/-- **Without an eviction the run is the ledgered run.** -/
theorem xrun_lrun (g : Guards) (cfg : Config) (r : Rules) (honest : List Nat) :
    ∀ (ss : List Federation.Step) (F : LFed), unevicted g cfg r F ss = true →
      xrun g cfg r F ss = lrun g cfg r F ss ∧ xlegal g cfg r honest F ss = llegal g cfg r honest F ss := by
  intro ss
  induction ss with
  | nil => intro F _; exact ⟨rfl, rfl⟩
  | cons s ss ih =>
    intro F h
    simp only [unevicted, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hx := xapply_unevicted g cfg r F s h.1
    obtain ⟨h1, h2⟩ := ih (xapply g cfg r F s) h.2
    rw [hx] at h1 h2
    refine ⟨?_, by simp only [xlegal, llegal, hx, h2]⟩
    simp only [xrun, lrun, hx]
    exact h1

/-- On a legal schedule with no evicting delivery, forgetting the ledgers leaves a `Federation.Execution`. -/
theorem xrun_execution {g : Guards} {cfg : Config} {r : Rules} {honest : List Nat}
    {t : Federation.Trace} {F : LFed} (hx : Federation.Execution r honest t F.fed) (ss : List Federation.Step)
    (hu : unevicted g cfg r F ss = true) (hl : xlegal g cfg r honest F ss = true) :
    Federation.Execution r honest (ltrace g cfg r t F ss) (xrun g cfg r F ss).fed := by
  obtain ⟨h1, h2⟩ := xrun_lrun g cfg r honest ss F hu
  rw [h1]
  exact lrun_execution hx ss (h2 ▸ hl)

/-- A delivered partial moves neither inventory nor the extracted set, evicting or not: the partial that left its
signer stays in the federation's partial inventory. -/
@[req "NCH-24"]
theorem xapply_inventories (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (i : Nat) (env : Env) (x : Exp) :
    (xapply g cfg r F (.deliverPartial i env x)).fed.parts = F.fed.parts ∧
      (xapply g cfg r F (.deliverPartial i env x)).fed.net = F.fed.net ∧
      (xapply g cfg r F (.deliverPartial i env x)).fed.extracted = F.fed.extracted :=
  ⟨rfl, rfl, rfl⟩

/-- The delivered partial joins the receiving world's exposure history, evicting or not. -/
theorem xapply_exposure (g : Guards) (cfg : Config) (r : Rules) (F : LFed) (i : Nat) (env : Env) (x : Exp) :
    ((xapply g cfg r F (.deliverPartial i env x)).fed.worlds i).exposure =
      (F.fed.worlds i).exposure ++ [{ x with hot := true }] := by
  simp [xapply, sysRecv, wstep, LFed.sys]

/-- A composed trace whose deliveries never meet an expired lookup at the node receiving them. -/
def Unevicted (t : Federation.Trace) : Bool :=
  t.all fun a => match a.2 with
    | .deliverPartial i env x => !evicts env (a.1.worlds i).node x.cid
    | _ => true

/-! ## The observer -/

/-- `FedSilence.FObs` with the channel answer to a delivered partial: receiver, sender and answer. -/
structure XObs where
  base : FObs
  answer : Option (Nat × Nat × Answer)
  deriving DecidableEq, Repr

/-- The acting node's observation, taken on the state the receipt leaves. -/
def xlocal (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (F : LFed) : Federation.Step → Option (Nat × Obs)
  | .deliverPartial i env x =>
    some (i, obsOf mk cfg r env (F.sys i) (sysRecv g cfg env (F.sys i) x.msg x.input x.signer x.cid) []
      (.receivePartial x.msg x.input x.signer x.cid))
  | s => localObs mk g cfg r F s

/-- One step's observation under the receipt-time rule. -/
def xfobs (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat) (F : LFed)
    (s : Federation.Step) : XObs :=
  { base := { node := xlocal mk g cfg r F s, sent := sent g cfg r peers F s, recv := received s,
              net := (xapply g cfg r F s).fed.net, parts := (xapply g cfg r F s).fed.parts,
              extracted := (xapply g cfg r F s).fed.extracted },
    answer := match s with
      | .deliverPartial i env x => some (i, x.signer, answer env (F.fed.worlds i).node x.cid)
      | _ => none }

/-- **Off an eviction the old observation is kept**: the `FObs` part is `FedSilence.fobs`. -/
theorem xfobs_unevicted (mk : Marker) (g : Guards) (cfg : Config) (r : Rules) (peers : List Nat) (F : LFed)
    (s : Federation.Step) (h : evictsAt F s = false) : (xfobs mk g cfg r peers F s).base = fobs mk g cfg r peers F s := by
  have hx := xapply_unevicted g cfg r F s h
  cases s with
  | deliverPartial i env x =>
    simp only [evictsAt] at h
    have hs := sysRecv_unexpired g cfg r env (F.sys i) x.msg x.input x.signer x.cid (by simpa [LFed.sys] using h)
    simp only [xfobs, fobs, hx, xlocal, localObs, Federation.actor, hs]
    rfl
  | _ => simp only [xfobs, fobs, hx, xlocal]

end BtcPolicy.ReceiptExpiry
