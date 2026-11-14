import BtcPolicy.Evaluate
import BtcPolicy.Cursor
import BtcPolicy.Coverage
import BtcPolicy.Deadline
import BtcPolicy.Classification
import BtcPolicy.Membership
import BtcPolicy.RefreshAge
import BtcPolicy.Kernel
import BtcPolicy.Federation
import BtcPolicy.Ingress
import BtcPolicy.Lifetime
import BtcPolicy.Sweep
import BtcPolicy.Settlement
import BtcPolicy.Budget
import BtcPolicy.Ledger
import BtcPolicy.Silence
import BtcPolicy.FedSilence
import BtcPolicy.Admission
import BtcPolicy.Progress
import BtcPolicy.Delivery
import BtcPolicy.Chain
import BtcPolicy.Watchtower
import BtcPolicy.VaultUnspent
import BtcPolicy.Alerts
import BtcPolicy.Package
import BtcPolicy.Trace
import BtcPolicy.TxAccounting
import BtcPolicy.Feasibility
import BtcPolicy.Recovery
import BtcPolicy.EscapeCustody
import BtcPolicy.ClawbackIngress
import BtcPolicy.ClawHandler
import BtcPolicy.PreRelease
import BtcPolicy.Coinbase
import BtcPolicy.Ladder
import BtcPolicy.Assembly
import BtcPolicy.RungRelease
import BtcPolicy.LadderRelease
import BtcPolicy.RungIngress
import BtcPolicy.RungAssembly
import BtcPolicy.VariantReceipt
import BtcPolicy.ClassAssembly
import BtcPolicy.LadderShape
import BtcPolicy.AcceptedSet
import BtcPolicy.Lifecycle
import BtcPolicy.Retained
import BtcPolicy.ReceiptExpiry
import BtcPolicy.ReleaseQuota
import BtcPolicy.Possession
import BtcPolicy.ExpirySilence
import BtcPolicy.VariantSilence
import BtcPolicy.Exhibits.Fixtures

namespace BtcPolicy.Exhibits.Registration
open Clocks Kernel Kernel.RegistrationCases

@[req "SPN-32"]
theorem fresh_pair_identity : freshChecks current = true := by decide

@[req "SPN-33"]
theorem defeated_replay_releases_nothing : (run current w0 replayFire).2 = [] := by decide

@[req "SPN-33"]
theorem historical_replay_releases :
    (run withdrawn w0 replayFire).2 = [.queuePartial (sighash tx1 0) 0 true 1] ∧
    (run withdrawn w0 replayFire).1.node.cands.any (fun c => c.id == 1 && c.terminal) = true := by
  decide

@[req "SPN-32"]
theorem resident_lifecycle_preserved : replayChecks current = true := by decide

@[req "SPN-32"]
theorem indivisible_identity_refusals : refusalChecks current = true := by decide

@[req "SPN-23"]
theorem replay_reapplies_schedule : scheduleChecks current = true := by decide

@[req "SPN-32"]
theorem reachable_ids_unique (w : World) (h : Reachable current w) :
    (w.node.cands.map Cand.id).Nodup := ids_nodup rfl h

@[req "SPN-33"]
theorem resident_terminal_id_sticky (env : Env) (w : World) (h : Reachable current w)
    (e : Event) (c : Cand) (hc : c ∈ w.node.cands) (ht : c.terminal = true) :
    ∀ c' ∈ (step current env w e).1.node.cands, c'.id = c.id → c'.terminal = true :=
  terminal_sticky current rfl env w h e c hc ht

@[req "SPN-29"]
theorem registration_refusal_reservations : Ledger.RegistrationCases.refusalChecks current = true := by
  decide

@[req "SPN-32"]
theorem registration_refusal_responses : Silence.RegistrationCases.observerChecks current = true := by
  decide

@[req "DUR-20"]
theorem replay_work_visits_once : Silence.RegistrationCases.workChecks current = true := by decide

end BtcPolicy.Exhibits.Registration

namespace BtcPolicy.Exhibits.Refusal
open Clocks Kernel Kernel.RefusalCases

@[req "DUR-5"]
theorem refused_receipt_authority_with_current (env : Env) (w : World) (hw : Reachable current w)
    (cid sender : Nat) (k : Carrier)
    (hk : w.node.carriers.find? (·.cid == cid) = some k) (ha : k.accepted = false) :
    (step current env w (.receipt cid sender)).1.node.cands.map (fun c => (c.id, c.quorum)) =
      w.node.cands.map (fun c => (c.id, c.quorum)) :=
  refused_receipt_preserves_opening current rfl env w hw cid sender k hk ha

@[req "DUR-4"]
theorem refusal_ingress_and_live_decision : ingressChecks current = true := by decide

@[req "DUR-5"]
theorem refused_decision_opens_nothing : openingChecks current = true := by decide

@[req "SPN-23"]
theorem accepted_and_replay_open : acceptedChecks current = true := by decide

@[req "SPN-29"]
theorem refused_reservations_and_holder : Ledger.RefusalCases.checks current = true := by decide

@[req "DUR-1"]
theorem refused_silence_full_prefix :
    Silence.RefusalCases.checks Silence.current current = true := by decide

set_option maxRecDepth 100000 in
@[req "ADR-0023"]
theorem refused_trace_codec_and_replay :
    Trace.decode (Trace.encode Trace.refusalTrace) = some Trace.refusalTrace ∧
    (Trace.replayKernel current Trace.w0 Trace.refusalTrace.entries).isSome = true ∧
    ((run current Trace.w0 (Trace.kernelInputs Trace.refusalTrace)).1.node.cands.map Cand.quorum) =
      [false, false] ∧
    (run current Trace.w0 (Trace.kernelInputs Trace.refusalTrace)).1.node.armed = true := by
  decide +kernel

@[req "DUR-5"]
theorem unstaged_has_no_holder_authority :
    commits RegistrationCases.envBack (residents current).node 99 1 = false ∧
    receipt current RegistrationCases.envBack (residents current).node 99 1 = (residents current).node := by
  decide

end BtcPolicy.Exhibits.Refusal

namespace BtcPolicy.Exhibits.Inheritance
open Kernel Kernel.InheritanceCases

@[req "DUR-5"]
theorem normal_copy_inherits_pair : inheritChecks current = true := by decide

@[req "DUR-10"]
theorem crossed_refusal_selects_open_escape : crossedChecks current = true := by decide

@[req "NCH-40"]
theorem retained_metadata_survives_censorship : censorChecks current.intentRetention = true := by decide

@[req "DUR-13"]
theorem duress_only_ingress : timeChecks current.ingressTime = true := by decide

@[req "NCH-34"]
theorem tombstones_have_no_holder_authority : authorityChecks current = true := by decide

/-- The refusal and isolation regressions fix the inheritance choices, whose independent flips
are checked above; they exercise the local-acceptance boundary with inherited metadata. -/
@[req "DUR-5"]
theorem inherited_refusal_opens_nothing :
    InheritanceCases.refusalChecks { current with
      inheritance := .inherit, intentRetention := .tombstones, ingressTime := .duressOnly } = true := by decide

@[req "DUR-13"]
theorem unbound_and_unrelated_metadata_stay_separate :
    isolatedChecks { current with
      inheritance := .inherit, intentRetention := .tombstones, ingressTime := .duressOnly } = true := by decide

/-! ### `DUR-13`'s seed across a backward wall step

`DUR-13` says the start is "the seed `max(ratchet, now)`, read at `DUR-7`'s time ratchet, lowered
to the `first_seen` of each record naming the same spend commitment whose own duress bit is set".
The traces are `Kernel.SeedCases`': two hot pairs, `fire_at` 1300 and 1350, both past every `T` below,
and `duress_delay_secs` 200. Each exhibit holds `T` because every hot `fire_at` lies past it. A
hot candidate whose window shut unfired and a replay of an old hot spend are `DUR-13`'s hot
domain's subject, run in `BtcPolicy.Exhibits.TwoRun`. -/

/-- A duress pair accepted at wall 1000, which moves the time ratchet there, and decided after the
wall steps back to 100. `DUR-13` says the start is "the seed `max(ratchet, now)`, read at
`DUR-7`'s time ratchet": here `max(1000, 100) = 1000`. The duress intent's own `first_seen` is
1000 too, so `T = 1000 + 200 = 1200`, below the hot cap `1300 − 5`, and not reached by `DUR-7`'s
driver at the ratchet: at the decision it compares `max(1000, 100) = 1000` with 1200. Seeded at
the effective time alone the decision would start at 100 and write 300, due at once. -/
@[req "DUR-13"]
theorem backward_step_keeps_duress_start :
    let a := SeedCases.nodeAfter current SeedCases.duressTrace
    a.armed = true ∧ a.T = Clocks.Wall.sample 1200 ∧ a.ratchet = (RegistrationCases.envAt 1000 10).eff ∧
      (a.ratchet.latest (RegistrationCases.envAt 100 20).eff).deadlineReached a.T = false := by decide

/-- The duress pair armed at 1000 and 1001, writing `T = 1200`; the wall steps back, and an
ordinary hot pair is accepted at 100, which `DUR-14`'s shrink leaves at `max(min(1200, 1350 − 5),
100) = 1200`, and decided at 110. No record naming it has its duress bit set, and `DUR-13` says "A
decision with no duress-bit record starts at the seed": here `max(1001, 110) = 1001`. It computes
`min(1001 + 200, 1300 − 5) = 1201`, both hot `fire_at` lying past it, and the armed node writes `max(min(1200, 1201), 110) = 1200`. Seeded at the effective time alone, or started at the
pair's own ingress of 100, the decision would write 310 or 300. -/
@[req "DUR-13"]
theorem backward_step_keeps_armed_T :
    (SeedCases.nodeAfter current (SeedCases.ordinaryTrace.take 2)).T = Clocks.Wall.sample 1200 ∧
    (SeedCases.nodeAfter current SeedCases.ordinaryTrace).T = Clocks.Wall.sample 1200 := by decide

end BtcPolicy.Exhibits.Inheritance

namespace BtcPolicy.Exhibits.Membership
open BtcPolicy.Membership

/-! Concrete theorem applications for descriptor membership. Derivation reads only the path's
identity and ignores the index for the definite identity, including at unscanned indices. -/

def mixedDescriptor : Descriptor := ⟨[externalPath, internalPath, definitePath]⟩

@[req "POL-4"]
theorem definite_derivation_constant (i : Nat) :
    derive definitePath i = derive definitePath 0 := rfl

@[req "POL-4"]
theorem success_characterized :
    matchesScript derive 2 mixedDescriptor [10, 2] = true ↔
      ∃ p ∈ mixedDescriptor.paths, ∃ i ∈ indices 2 p, derive p i = some [10, 2] :=
  matchesScript_iff derive 2 mixedDescriptor [10, 2]

@[req "POL-4"]
theorem inclusive_success : matchesScript derive 2 mixedDescriptor [10, 2] = true :=
  matches_at_max derive 2 mixedDescriptor externalPath (by decide) rfl [10, 2] rfl

@[req "POL-4"]
theorem zero_bound_success : matchesScript derive 0 mixedDescriptor [10, 0] = true :=
  matches_at_max derive 0 mixedDescriptor externalPath (by decide) rfl [10, 0] rfl

@[req "POL-4"]
theorem beyond_bound_refused : matchesScript derive 2 mixedDescriptor [10, 3] = false :=
  not_matches_beyond_max derive 2 mixedDescriptor externalPath (by decide) rfl [10, 3] rfl
    (by
      intro q hq i hi
      simp only [mixedDescriptor, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;>
        simp [indices, externalPath, internalPath, definitePath] at hi <;>
        simp [derive, externalPath, internalPath, definitePath] <;> omega)

@[req "POL-4"]
theorem multipath_success :
    matchesScript derive 2 ⟨[externalPath, internalPath]⟩ [10, 2] = true ∧
    matchesScript derive 2 ⟨[externalPath, internalPath]⟩ [11, 2] = true :=
  both_chains_scanned derive 2 externalPath internalPath 2 (by decide) (by decide)
    [10, 2] [11, 2] rfl rfl

@[req "POL-4"]
theorem definite_success : matchesScript derive 0 ⟨[definitePath]⟩ [12, 0] = true :=
  matches_of_derived derive 0 ⟨[definitePath]⟩ definitePath (by decide) 0 (by decide)
    [12, 0] rfl

@[req "POL-4"]
theorem definite_bound_independent :
    indices 0 definitePath = [0] ∧
    matchesScript derive 0 ⟨[definitePath]⟩ [12, 0] =
      matchesScript derive 9 ⟨[definitePath]⟩ [12, 0] :=
  definite_ignores_bound derive definitePath rfl 0 9 [12, 0]

@[req "POL-4"]
theorem failed_definite_bound_independent :
    indices 0 definitePath = [0] ∧
    matchesScript (fun _ _ => none) 0 ⟨[definitePath]⟩ [] =
      matchesScript (fun _ _ => none) 9 ⟨[definitePath]⟩ [] :=
  definite_ignores_bound (fun _ _ => none) definitePath rfl 0 9 []

@[req "POL-4"]
theorem failed_derivation_matches_nothing (s : Script) :
    matchesScript (fun _ _ => none) 2 mixedDescriptor s = false :=
  none_matches_nothing 2 mixedDescriptor s

@[req "POL-4"]
theorem failed_derivation_empty_script :
    matchesScript (fun _ _ => none) 0 mixedDescriptor [] = false :=
  none_matches_nothing 0 mixedDescriptor []

/-- Failure at zero is skipped; a later successful empty script is still a match. -/
def failsThenEmpty (_ : SinglePath) (i : Nat) : Option Script :=
  if i = 0 then none else some []

@[req "POL-4"]
theorem failed_index_skipped :
    matchesScript failsThenEmpty 0 mixedDescriptor [] = false ∧
    matchesScript failsThenEmpty 1 mixedDescriptor [] = true := by
  constructor
  · decide
  · exact matches_at_max failsThenEmpty 1 mixedDescriptor externalPath (by decide) rfl [] rfl

def differsAbove (bound : Nat) (p : SinglePath) (i : Nat) : Option Script :=
  if i ≤ bound then derive p i else none

@[req "POL-4"]
theorem locality_at_two :
    matchesScript derive 2 mixedDescriptor [10, 3] =
      matchesScript (differsAbove 2) 2 mixedDescriptor [10, 3] :=
  matchesScript_local derive (differsAbove 2) 2 mixedDescriptor [10, 3]
    (by intro p _ i hi; simp [differsAbove, hi])

@[req "POL-4"]
theorem locality_at_zero :
    matchesScript derive 0 mixedDescriptor [12, 0] =
      matchesScript (differsAbove 0) 0 mixedDescriptor [12, 0] :=
  matchesScript_local derive (differsAbove 0) 0 mixedDescriptor [12, 0]
    (by intro p _ i hi; simp [differsAbove, hi])

@[req "POL-4"]
theorem locality_derivations_differ_outside :
    derive externalPath 3 ≠ differsAbove 2 externalPath 3 ∧
    derive externalPath 1 ≠ differsAbove 0 externalPath 1 := by decide

@[req "POL-4"]
theorem classification_member_computed :
    BtcPolicy.Classification.member
      { value := 1, kind := kindOf derive 2 ⟨[definitePath]⟩ ⟨[externalPath]⟩
          [⟨[externalPath, internalPath]⟩] [10, 2] } =
      kindOf derive 2 ⟨[definitePath]⟩ ⟨[externalPath]⟩ [⟨[externalPath, internalPath]⟩] [10, 2] :=
  member_discharged derive 2 ⟨[definitePath]⟩ ⟨[externalPath]⟩
    [⟨[externalPath, internalPath]⟩] [10, 2] 1

@[req "CHN-30"]
theorem classification_priority :
    kindOf derive 2 mixedDescriptor mixedDescriptor [mixedDescriptor] [12, 0] = .vault ∧
    kindOf derive 2 ⟨[definitePath]⟩ ⟨[externalPath]⟩
      [⟨[externalPath, internalPath]⟩] [10, 2] = .escape ∧
    kindOf derive 2 ⟨[definitePath]⟩ ⟨[externalPath]⟩
      [⟨[externalPath, internalPath]⟩] [11, 2] = .hot ∧
    kindOf (fun _ _ => none) 2 mixedDescriptor mixedDescriptor [mixedDescriptor] [] = .unknown := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · exact (kindOf_order derive 2 ⟨[definitePath]⟩ ⟨[externalPath]⟩
      [⟨[externalPath, internalPath]⟩] [10, 2] (by decide)).1 (by decide)
  · exact (kindOf_order derive 2 ⟨[definitePath]⟩ ⟨[externalPath]⟩
      [⟨[externalPath, internalPath]⟩] [11, 2] (by decide)).2 (by decide) (by decide)

end BtcPolicy.Exhibits.Membership

namespace BtcPolicy.Exhibits.Provenance
open BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Kernel.ProvenanceCases

/-- The actual normal accept/receipt/fire path, with the deciding Carrier already retired. -/
@[req "DUR-8"]
theorem normal_release_after_retirement :
    Execution Kernel.current (normalHistory Kernel.current) (normalWorld Kernel.current) ∧
    (normalWorld Kernel.current).node.carriers = [] ∧
    (step Kernel.current envFire (normalWorld Kernel.current) .firePass).2 =
      [.queuePartial (sighash tx1 0) 0 true c1.id] := by
  exact ⟨normal_execution _, by decide, by decide⟩

/-- Instantiate the general theorem on the emitted effect, with its actual execution history. -/
@[req "DUR-8"]
theorem normal_release_has_provenance :
    (normalWorld Kernel.current).node.armed = false ∧
    NormalRelease Kernel.current (normalHistory Kernel.current)
      (normalWorld Kernel.current).node.id (sighash tx1 0) c1.id :=
  hot_release_provenance Kernel.current rfl (normal_execution _) envFire .firePass
    (sighash tx1 0) c1.id (by decide)

/-- Withholding the holder receipt leaves the real path closed; the extra-writer twin releases
on that same accepted prefix and violates the same message/commitment provenance property. -/
@[req "DUR-8"]
theorem holder_bypass_releases_without_provenance :
    Execution Kernel.current waitingHistory (waitingWorld Kernel.current) ∧
    (step Kernel.current envFire (waitingWorld Kernel.current) .firePass).2 = [] ∧
    (bypassFire Kernel.current envFire (waitingWorld Kernel.current)).2 =
      [.queuePartial (sighash tx1 0) 0 true c1.id] ∧
    ¬ (∀ msg cid, Effect.queuePartial msg 0 true cid ∈
      (bypassFire Kernel.current envFire (waitingWorld Kernel.current)).2 →
      (waitingWorld Kernel.current).node.armed = false ∧
        NormalRelease Kernel.current waitingHistory (waitingWorld Kernel.current).node.id msg cid) := by
  exact ⟨waiting_execution _, by decide, by decide, bypass_refutes_provenance _ (by decide)⟩

/-- Nonempty authority with duplicate rows and signers still lacks input-0 quorum, including
for another commitment over the same message. All boundary hypotheses are discharged. -/
@[req "DUR-8"]
theorem repeated_exposure_has_no_quorum :
    Reachable Kernel.current (countWorld Kernel.current) ∧
    (countWorld Kernel.current).exposure.length = 6 ∧
    compromised.eraseDups.length = 2 ∧
    exposedQuorum (countWorld Kernel.current) c1 = false ∧
    exposedQuorum (countWorld Kernel.current) c1' = false := by
  refine ⟨(count_execution _).reachable, by decide, by decide, ?_, ?_⟩
  · exact no_exposed_quorum_without_normal Kernel.current (fun _ => []) compromised _ c1
      (count_honest_exposure _) (count_no_normal _) (by decide)
  · exact no_exposed_quorum_without_normal Kernel.current (fun _ => []) compromised _ c1'
      (count_honest_exposure _) (count_no_normal _) (by decide)

end BtcPolicy.Exhibits.Provenance

namespace BtcPolicy.Exhibits.EarlierRelease
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Kernel.ProvenanceCases

/-! A 3-of-5 counterexample to replacing all-history absence with cutoff absence.
Every honest identity receives the old accepted Carrier; only 1 and 2 receive enough old
relays to open it. All four later arm. These are per-node executions, not a network semantics.
`DUR-5` says a relay "proves the peer received and processed the Carrier, not that it froze or
signed"; no receipt is treated as signature possession. -/

def oldAccept : List (Env × Event) :=
  [(envAt 10 10, .accept 10 false (Wall.sample 900) oldSpend oldEscape)]
def oldNormal : List (Env × Event) := oldAccept ++
  [(envAt 20 20, .receipt 10 3), (envAt 21 21, .receipt 10 4),
   (envAt 100 100, .firePass)]
def later (a b : Nat) : List (Env × Event) :=
  [(envAt 110 110, .accept 20 true (Wall.sample 1000) newSpend newEscape),
   (envAt 120 120, .receipt 20 a), (envAt 121 121, .receipt 20 b),
   (envAt 150 150, .firePass)]
def trace : Nat → List (Env × Event)
  | 0 => [(envAt 150 150, .adversaryExposes (sighash target 0) 0 0 newSpend.id)]
  | 1 | 2 => oldNormal ++ later 3 4
  | 3 | 4 => oldAccept ++ later 1 2
  | _ => []
def world (self : Nat) := (run current (initial self) (trace self)).1
def history (self : Nat) := recordHistory current [] (initial self) (trace self)
def inventory : World :=
  { node := node 0, exposure := (List.range 5).flatMap fun self => (world self).exposure }
def compromised : List Nat := [0]
def cut : Wall := Wall.sample 110

/-- Local histories start before staging; `DUR-5` counts this node "once it has staged the
Carrier for propagation". This proves the kernel execution boundary, not transport validity. -/
theorem legal (self : Nat) : Execution current (history self) (world self) :=
  execution_run current (trace self) (.init (node self) (by simp [node, A]))

/-- `DUR-8`: a pair "waits for the holder decision of a Carrier naming it". This is the
actual earlier normal decision, retained after its retirement and later arming. -/
@[req "DUR-8"]
theorem earlier_normal (self : Nat) (hs : self = 1 ∨ self = 2) :
    NormalRelease current (history self) self (sighash target 0) oldSpend.id := by
  refine ⟨((run current (initial self) (oldNormal.take 2)).1,
    envAt 21 21, Event.receipt 10 4), ?_, 10, 4,
    ((run current (initial self) (oldNormal.take 2)).1.node.carriers[0]?).getD
      ⟨10, false, [3], Wall.sample 900, Mono.sample 900, (envAt 10 10).eff,
        some (1, 2), true, true⟩,
    ((run current (initial self) (oldNormal.take 2)).1.node.cands[0]?).getD oldSpend, ?_⟩
  · rcases hs with rfl | rfl <;> decide +kernel
  · rcases hs with rfl | rfl <;> decide +kernel

/-- A deliberately generous necessary test for a normal opening; it reads no authority count. -/
def possibleNormal (f : World × Env × Event) : Bool :=
  !f.1.node.armed && match f.2.2 with
    | .receipt cid _ => (f.1.node.carriers.find? (·.cid == cid)).any (fun k => !k.duress)
    | _ => false

/-- `DUR-8`: "a hot partial is released only when the node is NOT armed". A normal opening
also needs an unarmed entering node and an ordinary deciding Carrier. -/
theorem opening_possible (h : NormalOpening r f self msg cid) : possibleNormal f = true := by
  obtain ⟨kcid, sender, k, c, he, hk, _, _, _, _, ha, _, _, hd, _⟩ := h
  simp [possibleNormal, he, hk, ha, hd]

/-- A satisfied cutoff-only candidate for `DUR-8`'s "never a signing quorum"; it is not a
quorum conclusion. The earlier normal decisions precede the supplied cutoff. -/
theorem no_normal_since :
    NoHonestNormalSince current history compromised (sighash target 0) cut := by
  have checked : ∀ self, (history self).all
      (fun f => !f.2.1.eff.atOrAfter cut || !possibleNormal f) = true := by
    intro self
    match self with
    | 0 | 1 | 2 | 3 | 4 => decide +kernel
    | _ + 5 => rfl
  intro self _ cid f hf ht ho
  have h := List.all_eq_true.mp (checked self) f hf
  rw [ht, opening_possible ho] at h
  contradiction

/-- `DUR-8`: a pair "waits for the holder decision of a Carrier naming it". Every relevant
honest row here has that normal-opening evidence in one of the two earlier executions. -/
@[req "DUR-8"]
theorem honest_exposure :
    HonestExposureProvenance current history compromised inventory (sighash target 0) := by
  intro x hx hm hi hs
  have rows : (inventory.exposure.filter fun x => x.msg == sighash target 0 && x.input == 0) =
      [⟨sighash target 0, 0, 0, true, newSpend.id⟩,
       ⟨sighash target 0, 0, 1, true, oldSpend.id⟩,
       ⟨sighash target 0, 0, 2, true, oldSpend.id⟩] := by decide +kernel
  have hxf : x ∈ inventory.exposure.filter (fun x => x.msg == sighash target 0 && x.input == 0) :=
    List.mem_filter.mpr ⟨hx, by simp [hm, hi]⟩
  rw [rows] at hxf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxf
  rcases hxf with rfl | rfl | rfl
  · simp [compromised] at hs
  · exact ⟨world 1, legal 1, by decide +kernel, earlier_normal 1 (Or.inl rfl)⟩
  · exact ⟨world 2, legal 2, by decide +kernel, earlier_normal 2 (Or.inr rfl)⟩

/-- `DUR-8`'s "never a signing quorum" cannot follow from the cutoff predicate alone.
A nonempty strictness witness: the cutoff predicate holds although identity 1 has an
honest earlier normal decision on this very message. The original theorem is unchanged. -/
@[req "DUR-8"]
theorem cutoff_is_strictly_weaker :
    NoHonestNormalSince current history compromised (sighash target 0) cut ∧
    ¬ NoHonestNormalDecision current history compromised (sighash target 0) := by
  refine ⟨no_normal_since, ?_⟩
  intro h
  exact h 1 (by decide) oldSpend.id (earlier_normal 1 (Or.inl rfl))

/-- `DUR-11`: "The freeze applies to every candidate with `hot = true`, existing and future,
at once". Nevertheless earlier authority persists: all four honest nodes end armed, with
frozen old and new hot candidates and no peer partials held; input-0 quorum exists under both
commitments. This is an inventory assembled from legal local histories, not a reachable
multi-node world, Bitcoin signature check or transaction-finalizability theorem. -/
@[req "DUR-8"]
theorem later_freeze_preserves_prior_quorum :
    (∀ self, Execution current (history self) (world self)) ∧
    HonestExposureProvenance current history compromised inventory (sighash target 0) ∧
    NoHonestNormalSince current history compromised (sighash target 0) cut ∧
    compromised.eraseDups.length < inventory.node.t ∧
    ([1, 2, 3, 4].all fun self =>
      (world self).node.armed &&
      (world self).node.cands.any (fun c => c.id == oldSpend.id && c.frozen) &&
      (world self).node.cands.any (fun c => c.id == newSpend.id && c.frozen) &&
      (world self).node.cands.all (fun c => c.heldSigners == [self])) = true ∧
    ((inventory.exposure.filter fun x => x.msg == sighash target 0 && x.input == 0).map
      Exp.signer).eraseDups = [0, 1, 2] ∧
    exposedQuorum inventory oldSpend = true ∧ exposedQuorum inventory newSpend = true := by
  exact ⟨legal, honest_exposure, no_normal_since, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The all-history premise of `DUR-8`'s "never a signing quorum" has an inhabited instance
with nonempty exposure;
`ProvenanceCases.countTrace` includes repeated rows and commitment ids. -/
@[req "DUR-8"]
theorem all_history_absence_implies_cutoff_on_nonempty_inventory :
    (ProvenanceCases.countWorld current).exposure.length = 6 ∧
    NoHonestNormalSince current (fun _ => []) ProvenanceCases.compromised
      (sighash RegistrationCases.tx1 0) cut := by
  exact ⟨by decide, no_normal_implies_no_normal_since (ProvenanceCases.count_no_normal _) cut⟩

/-! ### The same histories as one composed execution

A `Federation.Execution` over `Kernel.current` with honest nodes 1–4 and identity 0 outside the
honest list. Every receipt above is the delivery of a relay its sender emitted after accepting that
Carrier; every honest row is a partial its signer queued; identity 0's row is a partial signed
with its copied key. The schedule needs no change to the local histories: each honest projection is
exactly `history`. Relays of Carrier 10 from 3 and 4 reach only 1 and 2, and no other relay of it
is delivered, which is a drop the composition allows, not a guard. No partial is delivered. All
four honest nodes accept the same request under each Carrier id, so the composition's unbound
relay body is not used. -/





def linkedTrace : Federation.Trace := Federation.record current [] linkedStart linkedSteps
def linkedFinal : Federation.Fed := Federation.runFrom current linkedStart linkedSteps

theorem linked_fresh : Federation.Fresh linkedHonest linkedStart := by
  unfold Federation.Fresh
  decide

theorem linked_execution :
    Federation.Execution current linkedHonest linkedTrace linkedFinal :=
  Federation.execution_of_legal (.init _ linked_fresh) (by decide +kernel)

/-- Only honest nodes take kernel events in this schedule. -/
theorem linked_actors : linkedSteps.all (fun s => match Federation.actor s with
    | some (i, _, _) => linkedHonest.contains i
    | none => true) = true := by
  decide

/-- Each honest projection of the composed execution is that node's local `history`, unchanged;
every other identity's is empty, identity 0 acting only through its copied key. -/
theorem linked_projection (self : Nat) :
    Federation.project self linkedTrace = if self ∈ linkedHonest then history self else [] := by
  split
  · rename_i hs
    simp only [linkedHonest, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel
  · rename_i hs
    apply List.eq_nil_iff_forall_not_mem.2
    intro a ha
    obtain ⟨g, s, hm, hact⟩ := Federation.mem_project_actor ha
    rcases Federation.mem_record hm with h | h
    · cases h
    · have hc := List.all_eq_true.1 linked_actors s h
      simp only [hact, List.contains_eq_mem, decide_eq_true_eq] at hc
      exact hs hc

/-- Every relay delivered to an honest node in `linkedTrace` names an honest sender. -/
theorem linked_senders : (linkedHonest.all fun self =>
    (Federation.project self linkedTrace).all fun a => match a.2.2 with
      | .receipt _ s => linkedHonest.contains s
      | _ => true) = true := by
  decide +kernel

/-- `later_freeze_preserves_prior_quorum` on one reachable composed execution, with nothing seeded.
Each honest projection is exactly that node's `history` and ends at its `world`. Each received
relay's sender processed that Carrier (`Federation.receipt_origin`). Each partial in the inventory
was queued by its honest signer or signed with the one copied key (`Federation.part_origin`). The
partial inventory's input-0 rows are `inventory`'s rows, reordered; its other rows are the same
honest releases' partials on input 1 (`Federation.fanout`). The provenance premise is derived by
`Federation.honest_exposure_provenance`, not proved by hand, under the message binding, which holds
here. The cutoff premise holds, the all-history premise fails, the copied set is below threshold, all
four honest nodes end armed holding both hot candidates frozen and only their own partial, and both
candidates have exposed quorum. Exposed authority is not possession and not a complete
authorization: input 1, user authority, package validation and inclusion are outside, as in the
local exhibit. -/
@[req "DUR-8"]
theorem linked_preserves_prior_quorum :
    Federation.Execution current linkedHonest linkedTrace linkedFinal ∧
    (∀ self ∈ linkedHonest, Federation.project self linkedTrace = history self ∧
      linkedFinal.worlds self = world self) ∧
    (∀ self ∈ linkedHonest, ∀ a ∈ Federation.project self linkedTrace, ∀ c s,
      a.2.2 = .receipt c s → s ∈ linkedHonest ∧ Federation.Processed linkedTrace s c) ∧
    (∀ x ∈ linkedFinal.parts, x.signer ∈ linkedFinal.extracted ∨
      (x.signer ∈ linkedHonest ∧ Federation.Queued current linkedTrace x)) ∧
    linkedFinal.extracted = compromised ∧
    (linkedFinal.parts.filter (·.input == 0)).isPerm inventory.exposure = true ∧
    Federation.HotBinding linkedFinal (sighash target 0) ∧
    HonestExposureProvenance current (fun j => Federation.project j linkedTrace)
      linkedFinal.extracted (Federation.partsWorld linkedFinal 1) (sighash target 0) ∧
    NoHonestNormalSince current (fun j => Federation.project j linkedTrace) linkedFinal.extracted
      (sighash target 0) cut ∧
    ¬ NoHonestNormalDecision current (fun j => Federation.project j linkedTrace)
      linkedFinal.extracted (sighash target 0) ∧
    linkedFinal.extracted.eraseDups.length < (linkedFinal.worlds 1).node.t ∧
    (linkedHonest.all fun self =>
      (linkedFinal.worlds self).node.armed &&
      (linkedFinal.worlds self).node.cands.any (fun c => c.id == oldSpend.id && c.frozen) &&
      (linkedFinal.worlds self).node.cands.any (fun c => c.id == newSpend.id && c.frozen) &&
      (linkedFinal.worlds self).node.cands.all (fun c => c.heldSigners == [self])) = true ∧
    exposedQuorum (Federation.partsWorld linkedFinal 1) oldSpend = true ∧
    exposedQuorum (Federation.partsWorld linkedFinal 1) newSpend = true := by
  have hext : linkedFinal.extracted = compromised := by decide
  have hb : Federation.HotBinding linkedFinal (sighash target 0) := by decide +kernel
  refine ⟨linked_execution, ?_, ?_, fun x hx => Federation.part_origin linked_execution hx, hext,
    by decide +kernel, hb,
    Federation.honest_exposure_provenance rfl linked_execution hb _, ?_, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro self hs
    refine ⟨by rw [linked_projection, if_pos hs], ?_⟩
    simp only [linkedHonest, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel
  · intro self hs a ha c s he
    have hsend := List.all_eq_true.1 (List.all_eq_true.1 linked_senders self hs) a ha
    simp only [he, List.contains_eq_mem, decide_eq_true_eq] at hsend
    obtain ⟨w, env, e⟩ := a
    simp only at he
    subst he
    exact ⟨hsend, Federation.receipt_origin linked_execution ha hsend⟩
  · intro self hs cid f hf ht ho
    change f ∈ Federation.project self linkedTrace at hf
    rw [linked_projection] at hf
    split at hf
    · exact no_normal_since self (by rw [← hext]; exact hs) cid f hf ht ho
    · cases hf
  · intro h
    refine h 1 (by decide) oldSpend.id ?_
    change NormalRelease current (Federation.project 1 linkedTrace) 1 (sighash target 0) oldSpend.id
    rw [linked_projection, if_pos (by decide)]
    exact earlier_normal 1 (Or.inl rfl)



/-! ### Authority on every input (`DUR-28`)

The same schedule read on every input with `Authority.normal`. The target spends two inputs, so each
honest release puts two partials in the inventory (`Federation.fanout`). The keys are the five
identities. The user's signatures are on both inputs of the target: the requests carry them, and
ingress verifies them upstream (`CHN-12`), which `Kernel.Event.accept` does not model, so they are
supplied here as a record and not derived. -/

def keys : List Nat := List.range 5
def userSigs : List Authority.UserSig := [⟨sighash target 0, 0⟩, ⟨sighash target 1, 1⟩]

/-- Identity 0's partial on input 1, signed with its copied key. -/
def forgedRow1 : Exp := { forgedRow with msg := sighash target 1, input := 1 }
/-- Node 2's earlier normal release, on input `k`. -/
def row2 (k : Nat) : Exp :=
  { msg := sighash target k, input := k, signer := 2, hot := true, cid := oldSpend.id }

def exposedSteps : List Federation.Step := linkedSteps ++ [.forge forgedRow1]
def authorizedSteps : List Federation.Step := exposedSteps ++
  [.deliverPartial 1 (envAt 160 160) (row2 0), .deliverPartial 1 (envAt 160 160) (row2 1),
   .deliverPartial 1 (envAt 160 160) forgedRow, .deliverPartial 1 (envAt 160 160) forgedRow1]
/-- The authorized run, then node 1's prune pass long after every expiry and window. -/
def deletedSteps : List Federation.Step := authorizedSteps ++ [.process 1 (envAt 2000 2000) .prune]

def finalOf (steps : List Federation.Step) : Federation.Fed :=
  Federation.runFrom current linkedStart steps
def heldBy (steps : List Federation.Step) (i : Nat) : List Authority.Sig :=
  Federation.held i (Federation.record current [] linkedStart steps) (finalOf steps)
def exposedSigs (steps : List Federation.Step) : List Authority.Sig :=
  (finalOf steps).parts.map Authority.sig

/-- Exposure without possession. With identity 0's copied key also used on input 1, the partial
inventory holds three distinct signers on each input of the target, and with the user's signatures
that is Normal authorization (`Authority.normal`). No honest node possesses it: none was delivered a
partial, so each holds its own signatures alone. -/
@[req "DUR-28"]
theorem exposure_without_possession :
    Federation.legal current linkedHonest linkedStart exposedSteps = true ∧
    Authority.normal keys 3 target userSigs (exposedSigs exposedSteps) = true ∧
    (linkedHonest.all fun i => (heldBy exposedSteps i).all (·.signer == i) &&
      !Authority.normal keys 3 target userSigs (heldBy exposedSteps i)) = true := by
  decide +kernel

/-- Possession without complete authorization, and commitment re-quotation. In `deliveredSteps`
node 1 is delivered node 2's and identity 0's input-0 partials. Its kernel store splits them by
commitment and no candidate holds three (`linked_possession_only_where_delivered`), but by
signature identity they are three signers on one message, the old and the new commitment naming one
transaction. Input 1 has node 1's own signature alone, so the target is not authorized: a threshold
at input 0 is not authorization of a two-input transaction. -/
@[req "DUR-28"]
theorem possession_without_complete_authorization :
    Authority.signers keys target 0 (heldBy deliveredSteps 1) = [1, 2, 0] ∧
    Authority.signers keys target 1 (heldBy deliveredSteps 1) = [1] ∧
    Authority.userSigned target userSigs = true ∧
    Authority.normal keys 3 target userSigs (heldBy deliveredSteps 1) = false := by
  decide +kernel

/-- The earlier-release history as an authorization witness, and authorization without confirmation.
On one reachable composed execution, node 1 is delivered node 2's two partials from the earlier
normal release and identity 0's two forged partials. Its possession then has three distinct signers on
each input, under two commitments, and with the user's signatures that is Normal authorization of the
target, held while all four honest nodes are armed with both hot candidates frozen. Its own assembly
reads one candidate at input 0 and finds no quorum, no honest candidate ends with an assembled
package or a broadcast, and nothing in the composition includes a transaction in a chain, which is
an environmental step outside it. Node 1 is honest: the holder is the place delivery reached, and a holder outside the honest list
has no world here, so that it is the adversary is not shown. Only node 1 is delivered the partials. -/
@[req "DUR-28"]
theorem linked_authorization :
    Federation.legal current linkedHonest linkedStart authorizedSteps = true ∧
    Authority.normal keys 3 target userSigs (heldBy authorizedSteps 1) = true ∧
    Authority.signers keys target 0 (heldBy authorizedSteps 1) = [1, 2, 0] ∧
    Authority.signers keys target 1 (heldBy authorizedSteps 1) = [1, 2, 0] ∧
    (finalOf authorizedSteps).extracted = compromised ∧
    (linkedHonest.all fun self =>
      ((finalOf authorizedSteps).worlds self).node.armed &&
      ((finalOf authorizedSteps).worlds self).node.cands.any (fun c => c.id == oldSpend.id && c.frozen) &&
      ((finalOf authorizedSteps).worlds self).node.cands.any (fun c => c.id == newSpend.id && c.frozen) &&
      ((finalOf authorizedSteps).worlds self).node.cands.all
        (fun c => !c.packageOk && !c.broadcast)) = true ∧
    ((finalOf authorizedSteps).worlds 1).node.cands.all (fun c => !heldQuorum 3 c) = true ∧
    ([2, 3, 4].all fun i => !Authority.normal keys 3 target userSigs (heldBy authorizedSteps i)) = true ∧
    Authority.normal keys 3 target [⟨sighash target 0, 0⟩] (heldBy authorizedSteps 1) = false := by
  decide +kernel

/-- Retained authority after local candidate deletion. Node 1's prune pass removes every candidate
after the windows close, and its possession goes with them. The partial inventory loses nothing
(`Federation.parts_grows`), so it still holds Normal authorization of the target. -/
@[req "POL-18"]
theorem deleted_candidate_retains_authority :
    Federation.legal current linkedHonest linkedStart deletedSteps = true ∧
    ((finalOf deletedSteps).worlds 1).node.cands = [] ∧
    heldBy deletedSteps 1 = [] ∧
    Authority.normal keys 3 target userSigs (exposedSigs deletedSteps) = true := by
  decide +kernel

end BtcPolicy.Exhibits.EarlierRelease

namespace BtcPolicy.Exhibits.EveryInput
open BtcPolicy.Kernel BtcPolicy.Authority

/-! Hand-seeded records for `Authority.normal`, one per case, over a two-input transaction at
threshold 3 with keys 0–4. None is claimed reachable; the composed cases are in
`Exhibits.EarlierRelease`. -/

def X : Tx := ⟨100, [0, 1], 10⟩
def rungB : Tx := ⟨102, [0, 1], 12⟩
def keys : List Nat := List.range 5
def user (T : Tx) : List UserSig := [⟨sighash T 0, 0⟩, ⟨sighash T 1, 1⟩]
def rows (T : Tx) (k : Nat) (ss : List Nat) : List Sig :=
  ss.map fun s => { msg := sighash T k, input := k, signer := s }

/-- Inputs may be authorized by different subsets: 0, 1, 2 on input 0 and 1, 2, 3 on input 1 is
Normal authorization, though no three signers signed both inputs. -/
@[req "DUR-28"]
theorem different_subsets_authorize :
    normal keys 3 X (user X) (rows X 0 [0, 1, 2] ++ rows X 1 [1, 2, 3]) = true ∧
    ((List.range 5).filter fun s => [0, 1, 2].contains s && [1, 2, 3].contains s).length < 3 := by
  decide

/-- An absent input: three signers on input 0 and none on input 1. -/
@[req "DUR-28"]
theorem absent_input_refused : normal keys 3 X (user X) (rows X 0 [0, 1, 2]) = false := by decide

/-- The same signer twice counts once. -/
@[req "DUR-28"]
theorem repeated_signer_counted_once :
    normal keys 3 X (user X) (rows X 0 [0, 1, 1] ++ rows X 1 [0, 1, 1]) = false := by decide

/-- A foreign signer counts for nothing; the same records with that signer among the keys
authorize. -/
@[req "DUR-28"]
theorem foreign_signer_refused :
    normal keys 3 X (user X) (rows X 0 [0, 1, 9] ++ rows X 1 [0, 1, 9]) = false ∧
    normal (9 :: keys) 3 X (user X) (rows X 0 [0, 1, 9] ++ rows X 1 [0, 1, 9]) = true := by decide

/-- Signatures on two rungs do not pool: two signers on one rung and one on another authorize
neither, though the rungs spend the same inputs. -/
@[req "DUR-28"]
theorem mixed_rungs_refused :
    normal keys 3 X (user X ++ user rungB)
      (rows X 0 [0, 1] ++ rows X 1 [0, 1] ++ rows rungB 0 [2] ++ rows rungB 1 [2]) = false ∧
    normal keys 3 rungB (user X ++ user rungB)
      (rows X 0 [0, 1] ++ rows X 1 [0, 1] ++ rows rungB 0 [2] ++ rows rungB 1 [2]) = false := by decide

/-- Commitment re-quotation does not separate authority: two rows over one transaction under
commitments 1 and 5 are one signature, and rows under the two commitments pool. -/
@[req "DUR-28"]
theorem requotation_pools :
    sig ⟨sighash X 0, 0, 2, true, 1⟩ = sig ⟨sighash X 0, 0, 2, true, 5⟩ ∧
    normal keys 3 X (user X)
      ((([0, 1].map fun s => (⟨sighash X 0, 0, s, true, 1⟩ : Exp)) ++ [(⟨sighash X 0, 0, 2, true, 5⟩ : Exp)] ++
        ([0, 1].map fun s => (⟨sighash X 1, 1, s, true, 1⟩ : Exp)) ++ [(⟨sighash X 1, 1, 2, true, 5⟩ : Exp)]).map
        sig) = true := by decide

/-- Missing user authorization: a federation quorum on both inputs with the user's signature on
input 0 only. -/
@[req "CHN-12"]
theorem missing_user_signature_refused :
    quorum keys 3 X (rows X 0 [0, 1, 2] ++ rows X 1 [0, 1, 2]) = true ∧
    normal keys 3 X [⟨sighash X 0, 0⟩] (rows X 0 [0, 1, 2] ++ rows X 1 [0, 1, 2]) = false := by decide

end BtcPolicy.Exhibits.EveryInput


namespace BtcPolicy.Exhibits.Evaluate
open BtcPolicy.Evaluate

/-! Decided PSBT exhibits. The definite vault script is derived at zero; the ranged
scripts are inside the fixture bound. Request records expose the row reached by each refusal. -/


def accepted : Psbt :=
  { txInputs := [⟨[0], 0, 0⟩], txOutputs := [⟨[12, 0], 40⟩, ⟨[11, 1], 55⟩],
    inputMaps := [some ⟨[12, 0], 100⟩], outputHints := [true, false] }

def consistencyRows (p : Psbt) : List Bool :=
  [!p.txInputs.isEmpty, !p.txOutputs.isEmpty,
   p.inputMaps.length == p.txInputs.length, p.outputHints.length == p.txOutputs.length,
   !p.inputMaps.any Option.isNone]

@[req "POL-4"]
theorem fixture_membership :
    Membership.definitePath.wildcard = false ∧
    BtcPolicy.Membership.matchesScript cfg.derive cfg.max cfg.vault [12, 0] = true ∧
    (output cfg ⟨[12, 0], 40⟩).kind = .vault ∧
    (output cfg ⟨[11, 1], 55⟩).kind = .hot ∧
    (output cfg ⟨[99], 55⟩).kind = .unknown ∧
    (output cfg ⟨[98], 25⟩).kind = .unknown := by decide

@[req "POL-6"]
theorem accepting_psbt :
    Consistent accepted ∧
    request cfg accepted = ⟨false, false, .allowed, false, .ok⟩ ∧
    evaluate cfg accepted = none := by decide

@[req "POL-7"]
theorem no_inputs :
    let p := { accepted with txInputs := [], inputMaps := [] }
    consistencyRows p = [false, true, true, true, true] ∧
    evaluate cfg p = some .PSBT_INCONSISTENT := by decide

@[req "POL-7"]
theorem no_outputs :
    let p := { accepted with txOutputs := [], outputHints := [] }
    consistencyRows p = [true, false, true, true, true] ∧
    evaluate cfg p = some .PSBT_INCONSISTENT := by decide

@[req "POL-7"]
theorem wrong_input_map_count :
    let p := { accepted with inputMaps := [] }
    consistencyRows p = [true, true, false, true, true] ∧
    evaluate cfg p = some .PSBT_INCONSISTENT := by decide

@[req "POL-7"]
theorem wrong_output_map_count :
    let p := { accepted with outputHints := [true] }
    consistencyRows p = [true, true, true, false, true] ∧
    evaluate cfg p = some .PSBT_INCONSISTENT := by decide

@[req "POL-7"]
theorem absent_witness_utxo :
    let p := { accepted with inputMaps := [none] }
    consistencyRows p = [true, true, true, true, false] ∧
    evaluate cfg p = some .PSBT_INCONSISTENT := by decide

@[req "POL-9"]
theorem foreign_input :
    let p := { accepted with inputMaps := [some ⟨[99], 100⟩] }
    Consistent p ∧
    request cfg p = ⟨false, true, .allowed, false, .ok⟩ ∧
    evaluate cfg p = some .UNKNOWN_INPUT := by decide

def stranger : Psbt := { accepted with txOutputs := [⟨[12, 0], 40⟩, ⟨[99], 55⟩] }

@[req "POL-10"]
theorem stranger_refused :
    Consistent stranger ∧
    request cfg stranger = ⟨false, false, .notAllowed, false, .ok⟩ ∧
    evaluate cfg stranger = some .DEST_NOT_ALLOWED := by decide

/-- This otherwise admissible stranger would be admitted if its hint counted as recognition.
The verdict is computed directly, never obtained from another theorem. -/
@[req "POL-10"]
theorem hinted_stranger_refused :
    let p := { stranger with outputHints := [true, true] }
    Consistent p ∧
    request cfg p = ⟨false, false, .changeNotDerivable, false, .ok⟩ ∧
    evaluate cfg p = some .CHANGE_NOT_DERIVABLE := by decide

def strangers (hs : List Bool) : Psbt :=
  { accepted with
    txOutputs := [⟨[98], 25⟩, ⟨[99], 30⟩],
    inputMaps := [some ⟨[12, 0], 60⟩], outputHints := hs }

@[req "POL-10"]
theorem first_stranger_unhinted :
    Consistent (strangers [false, true]) ∧
    request cfg (strangers [false, true]) = ⟨false, false, .notAllowed, false, .ok⟩ ∧
    evaluate cfg (strangers [false, true]) = some .DEST_NOT_ALLOWED := by decide

@[req "POL-10"]
theorem first_stranger_hinted :
    Consistent (strangers [true, false]) ∧
    request cfg (strangers [true, false]) = ⟨false, false, .changeNotDerivable, false, .ok⟩ ∧
    evaluate cfg (strangers [true, false]) = some .CHANGE_NOT_DERIVABLE := by decide

@[req "POL-11"]
theorem hot_budget_refused :
    let p := { accepted with txOutputs := [⟨[12, 0], 30⟩, ⟨[11, 1], 65⟩] }
    Consistent p ∧
    request cfg p = ⟨false, false, .allowed, true, .ok⟩ ∧
    evaluate cfg p = some .HOT_BUDGET_EXCEEDED := by decide

@[req "POL-12"]
theorem inconsistent_fee_totals :
    let p := { accepted with txOutputs := [⟨[12, 0], 50⟩, ⟨[11, 1], 55⟩] }
    Consistent p ∧
    request cfg p = ⟨false, false, .allowed, false, .inconsistent⟩ ∧
    evaluate cfg p = some .PSBT_INCONSISTENT := by decide

@[req "POL-12"]
theorem excessive_fee :
    let p := { accepted with txOutputs := [⟨[12, 0], 40⟩, ⟨[11, 1], 49⟩] }
    Consistent p ∧ totalOut p ≤ totalIn p ∧
    request cfg p = ⟨false, false, .allowed, false, .overCap⟩ ∧
    evaluate cfg p = some .FEE_EXCEEDS_CAP := by decide

@[req "POL-10"]
def mixedHintFaults : Psbt :=
  { accepted with
    txOutputs := [⟨[12, 0], 40⟩, ⟨[98], 25⟩, ⟨[99], 30⟩],
    outputHints := [true, true, false] }

@[req "API-25"]
theorem mixed_hint_fault_list :
    Consistent mixedHintFaults ∧ Owned cfg mixedHintFaults ∧
    faults cfg mixedHintFaults =
      [⟨.output, 1, .CHANGE_NOT_DERIVABLE⟩, ⟨.output, 2, .DEST_NOT_ALLOWED⟩] ∧
    evaluate cfg mixedHintFaults = some .CHANGE_NOT_DERIVABLE := by decide

@[req "POL-10"]
theorem mixed_hints_reach_destinations :
    faults cfg mixedHintFaults = destinationFaults cfg mixedHintFaults :=
  destinationFaults_selected cfg mixedHintFaults (by decide) (by decide)

@[req "POL-9"]
def foreignPair : Psbt :=
  { accepted with
    txInputs := [⟨[0], 0, 0⟩, ⟨[1], 0, 0⟩, ⟨[2], 0, 0⟩],
    inputMaps := [some ⟨[12, 0], 40⟩, some ⟨[98], 30⟩, some ⟨[99], 30⟩] }

@[req "API-25"]
theorem foreign_pair_fault_list :
    Consistent foreignPair ∧
    faults cfg foreignPair = [⟨.input, 1, .UNKNOWN_INPUT⟩, ⟨.input, 2, .UNKNOWN_INPUT⟩] ∧
    evaluate cfg foreignPair = some .UNKNOWN_INPUT := by decide

@[req "POL-9"]
theorem foreign_pair_reaches_ownership :
    faults cfg foreignPair = ownershipFaults cfg foreignPair ∧ ownershipFaults cfg foreignPair ≠ [] :=
  ownershipFaults_selected cfg foreignPair (by decide) (by decide)

@[req "POL-7"]
def missingSecond : Psbt :=
  { accepted with
    txInputs := [⟨[0], 0, 0⟩, ⟨[1], 0, 0⟩],
    inputMaps := [some ⟨[12, 0], 100⟩, none] }

@[req "API-25"]
theorem missing_second_fault_list :
    structural missingSecond = false ∧
    consistencyRows missingSecond = [true, true, true, true, false] ∧
    faults cfg missingSecond = [⟨.input, 1, .PSBT_INCONSISTENT⟩] ∧
    evaluate cfg missingSecond = some .PSBT_INCONSISTENT := by decide

@[req "POL-7"]
theorem missing_second_reaches_metadata :
    faults cfg missingSecond = missingFaults missingSecond ∧ missingFaults missingSecond ≠ [] :=
  missingFaults_selected cfg missingSecond (by decide) (by decide)

@[req "API-25"]
def manyFaults (n : Nat) : Psbt :=
  { accepted with
    txOutputs := List.replicate n ⟨[99], 1⟩,
    outputHints := List.replicate n false }

@[req "API-25"]
theorem above_cap_fault_list :
    Consistent (manyFaults 33) ∧ Owned cfg (manyFaults 33) ∧
    faults cfg (manyFaults 33) = (List.range 33).map (fun i => ⟨.output, i, .DEST_NOT_ALLOWED⟩) ∧
    transmitted cfg (manyFaults 33) = (List.range 32).map (fun i => ⟨.output, i, .DEST_NOT_ALLOWED⟩) ∧
    truncated cfg (manyFaults 33) = true ∧
    evaluate cfg (manyFaults 33) = some .DEST_NOT_ALLOWED := by decide

@[req "API-25"]
theorem exact_cap_fault_list :
    (faults cfg (manyFaults 32)).length = 32 ∧
    transmitted cfg (manyFaults 32) = faults cfg (manyFaults 32) ∧
    truncated cfg (manyFaults 32) = false := by decide

@[req "API-25"]
theorem accepting_fault_lists_empty :
    missingFaults accepted = [] ∧ ownershipFaults cfg accepted = [] ∧
    destinationFaults cfg accepted = [] ∧ faults cfg accepted = [] ∧
    transmitted cfg accepted = [] ∧ truncated cfg accepted = false := by decide

/-- Every structural row suppresses item defects, including missing metadata and strangers. -/
@[req "API-25"]
theorem structural_fault_lists_empty :
    faults cfg { mixedHintFaults with txInputs := [], inputMaps := [none] } = [] ∧
    faults cfg { missingSecond with txOutputs := [], outputHints := [] } = [] ∧
    faults cfg { mixedHintFaults with inputMaps := [none, none] } = [] ∧
    faults cfg { missingSecond with outputHints := [] } = [] := by decide

@[req "API-25"]
theorem earlier_items_suppress_later_faults :
    let p := { mixedHintFaults with inputMaps := [none] }
    destinationFaults cfg p ≠ [] ∧ faults cfg p = [⟨.input, 0, .PSBT_INCONSISTENT⟩] ∧
    let q := { mixedHintFaults with inputMaps := [some ⟨[99], 100⟩] }
    destinationFaults cfg q ≠ [] ∧ faults cfg q = [⟨.input, 0, .UNKNOWN_INPUT⟩] := by decide

@[req "API-25"]
theorem ineligible_fault_lists_empty :
    let hot := { accepted with
    txOutputs := [⟨[12, 0], 30⟩, ⟨[11, 1], 65⟩] }
    let overspend := { accepted with
    txOutputs := [⟨[12, 0], 50⟩, ⟨[11, 1], 55⟩] }
    let fee := { accepted with
    txOutputs := [⟨[12, 0], 40⟩, ⟨[11, 1], 49⟩] }
    evaluate cfg hot = some .HOT_BUDGET_EXCEEDED ∧ faults cfg hot = [] ∧
    evaluate cfg overspend = some .PSBT_INCONSISTENT ∧ faults cfg overspend = [] ∧
    evaluate cfg fee = some .FEE_EXCEEDS_CAP ∧ faults cfg fee = [] := by decide

end BtcPolicy.Exhibits.Evaluate

namespace BtcPolicy.Exhibits.Composition
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases
  BtcPolicy.Kernel.ProvenanceCases
open BtcPolicy.Federation BtcPolicy.Federation.Cases

/-! The composed execution over `Kernel.current`. Every run below is an actual
`Federation.Execution`: its guards are decided and each node moves by `Kernel.step`. These are not
hand-seeded. `Federation` owns the alphabet and what it leaves out. -/

/-- The chronological kernel events of one projected node, as `Kernel.run` takes them. -/
def eventsOf (i : Nat) (t : Trace) : List (Env × Event) :=
  (project i t).reverse.map (·.2)

def composedOrdinary :
    BtcPolicy.Federation.Execution Kernel.current honest (ordinaryTrace Kernel.current)
      (ordinaryFinal Kernel.current) :=
  execution_of_legal (.init fed0 fed0_fresh) (by decide)

/-- The ordinary run: three nodes accept, relay and receive; nodes 1 and 2 decide and release; node
3 is reached by a relay only after that, and decides without having released. Each projection is
exactly the local run named here and replays through `Kernel.run` to the node's world. Threshold 2
is reached only over the federation's inventory, and exposed authority here is not possession: no
partial is delivered in this run, so each node holds its own signature alone. -/
@[req "DUR-5"]
theorem ordinary_run :
    (∀ i ∈ honest, Kernel.Execution Kernel.current (project i (ordinaryTrace Kernel.current))
      ((ordinaryFinal Kernel.current).worlds i)) ∧
    eventsOf 1 (ordinaryTrace Kernel.current) =
      [(env0, .accept 10 false (Wall.sample 200) c1 RegistrationCases.e1), (env0, .receipt 10 2),
       (envFire, .firePass)] ∧
    eventsOf 3 (ordinaryTrace Kernel.current) =
      [(env0, .accept 10 false (Wall.sample 200) c1 RegistrationCases.e1),
       (envFire, .receipt 10 1)] ∧
    (∀ i ∈ honest, (Kernel.run Kernel.current (start i)
      (eventsOf i (ordinaryTrace Kernel.current))).1 = (ordinaryFinal Kernel.current).worlds i) ∧
    (exposure honest (ordinaryFinal Kernel.current)).map Exp.signer = [1, 2] ∧
    exposedQuorum (inventoryWorld honest (ordinaryFinal Kernel.current) 1) c1 = true ∧
    exposedQuorum ((ordinaryFinal Kernel.current).worlds 1) c1 = false ∧
    (∀ i ∈ honest, ((ordinaryFinal Kernel.current).worlds i).node.cands.all
      (fun c => c.heldSigners == [i] && !heldQuorum 2 c)) ∧
    ((ordinaryFinal Kernel.current).worlds 3).node.cands.any
      (fun c => c.id == c1.id && c.quorum && !c.released) := by
  refine ⟨fun i hi => project_execution composedOrdinary hi, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- `Kernel.hot_release_provenance` with its execution premise supplied by the federation: node 1's
fire pass in the ordinary run has its normal opening in node 1's projected history, whose receipt
came from node 2's relay. -/
@[req "DUR-8"]
theorem ordinary_release_has_provenance :
    ((runFrom Kernel.current fed0 toDecisions).worlds 1).node.armed = false ∧
    NormalRelease Kernel.current (project 1 (record Kernel.current [] fed0 toDecisions)) 1
      (sighash tx1 0) c1.id :=
  BtcPolicy.Federation.hot_release_provenance rfl
    (execution_of_legal (.init fed0 fed0_fresh) (by decide)) (by decide) envFire .firePass
    (sighash tx1 0) c1.id (by decide)

/-- `SPN-9`: "a peer that receives this node's relay still counts it under `DUR-5`". Node 2 refuses
at gate 10 and relays, so it has no Carrier, no candidate, no history in the kernel and no exposure;
node 1 still counts it and its holder decision opens the spend. The relay proved processing and
nothing else. -/
@[req "SPN-9"]
theorem unstaged_relay_is_counted :
    legal Kernel.current honest fed0 unstagedRelay = true ∧
    ((runFrom Kernel.current fed0 unstagedRelay).worlds 1).node.cands.any
      (fun c => c.id == c1.id && c.quorum) = true ∧
    ((runFrom Kernel.current fed0 unstagedRelay).worlds 2).node.carriers = [] ∧
    ((runFrom Kernel.current fed0 unstagedRelay).worlds 2).node.cands = [] ∧
    ((runFrom Kernel.current fed0 unstagedRelay).worlds 2).exposure = [] ∧
    project 2 (record Kernel.current [] fed0 unstagedRelay) = [] := by
  decide

/-- Authentication proves identity and not honesty. A relay cannot name an honest sender from
outside, but one naming a sender outside the honest list, who processed nothing the trace shows, is
counted and opens the spend. `Exhibits.Composition.stolen_key_partial_is_held` is the same for a
partial. -/
@[req "DUR-5"]
theorem authenticated_is_not_honest :
    legal Kernel.current honest fed0 injected = true ∧
    admits honest fed0 (.inject ⟨1, 10⟩) = false ∧
    ((runFrom Kernel.current fed0 injected).worlds 1).node.cands.any
      (fun c => c.id == c1.id && c.quorum) = true := by
  decide

/-- What the composition refuses and the kernel takes. `Kernel.Execution` holds of a history whose
holder receipt names node 1 with nothing behind it. In a federation with node 1 honest that history
has node 1's processing in its trace, whatever the schedule; on an empty inventory neither a
delivery nor an honest relay of a Carrier nobody consumed is admitted. -/
@[req "NCH-28"]
theorem forged_relay_refused :
    Kernel.Execution Kernel.current (normalHistory Kernel.current) (normalWorld Kernel.current) ∧
    admits honest fed0 (.deliver 1 env0 ⟨2, 10⟩) = false ∧
    admits honest fed0 (.emit 2 10) = false ∧
    ∀ t f, BtcPolicy.Federation.Execution Kernel.current [0, 1] t f →
      project 0 t = normalHistory Kernel.current → Processed t 1 10 := by
  refine ⟨normal_execution _, by decide, by decide, ?_⟩
  intro t f hx hp
  have hm : ∃ w, (w, env0, Event.receipt 10 1) ∈ project 0 t := by
    rw [hp]
    exact ⟨_, List.mem_cons_self⟩
  obtain ⟨_, hm⟩ := hm
  exact receipt_origin hx hm (by decide)

/-! ### Partials, extracted keys and derived provenance -/

/-- Ordinary successful authorization, with selective delivery and a duplicate partial. After the
ordinary run node 2's partial reaches node 1 alone, twice: node 1 holds a quorum, assembles and
broadcasts, while node 2 holds only its own signature and node 3 only its own. The second copy
changes nothing node 1 holds and no count over its world. -/
@[req "DUR-28"]
theorem authorized_run :
    legal Kernel.current honest fed0 authorized = true ∧
    ((runFrom Kernel.current fed0 authorized).worlds 1).node.cands.any
      (fun c => c.id == c1.id && c.heldSigners == [1, 2] && heldQuorum 2 c) = true ∧
    ((runFrom Kernel.current fed0 authorized).worlds 2).node.cands.all
      (fun c => c.heldSigners == [2]) = true ∧
    ((runFrom Kernel.current fed0 authorized).worlds 3).node.cands.all
      (fun c => c.heldSigners == [3]) = true ∧
    (Kernel.step Kernel.current envFire
      ((runFrom Kernel.current fed0 (authorized.take 14)).worlds 1) (.send c1.id)).2 =
        [.broadcast tx1.id] ∧
    authorized.drop 14 = [.process 1 envFire (.send c1.id)] ∧
    ((runFrom Kernel.current fed0 (ordinary ++ [.deliverPartial 1 envFire (part 2)])).worlds 1).node =
      ((runFrom Kernel.current fed0 (ordinary ++ [.deliverPartial 1 envFire (part 2),
        .deliverPartial 1 envFire (part 2)])).worlds 1).node ∧
    exposedQuorum ((runFrom Kernel.current fed0 (ordinary ++ [.deliverPartial 1 envFire (part 2)])).worlds 1) c1 =
      exposedQuorum ((runFrom Kernel.current fed0 (ordinary ++ [.deliverPartial 1 envFire (part 2),
        .deliverPartial 1 envFire (part 2)])).worlds 1) c1 := by
  decide

def authorizedTrace : Trace := record Kernel.current [] fed0 authorized
def authorizedFinal : Fed := runFrom Kernel.current fed0 authorized

/-- The derived premise on a run with honest target rows: the partial inventory holds input-0 rows for
the target message under honest signers 1 and 2, nobody's key is extracted, and
`Kernel.HonestExposureProvenance` holds of it, by `Federation.honest_exposure_provenance` and not by
hand. Each row's normal opening is in its signer's projection. -/
@[req "DUR-8"]
theorem authorized_provenance :
    ((authorizedFinal.parts.filter fun x => x.msg == sighash tx1 0 && x.input == 0).map
      Exp.signer) = [1, 2] ∧
    authorizedFinal.extracted = [] ∧
    HonestExposureProvenance Kernel.current (fun j => project j authorizedTrace)
      authorizedFinal.extracted (partsWorld authorizedFinal 1) (sighash tx1 0) :=
  ⟨by decide, by decide,
    honest_exposure_provenance rfl (execution_of_legal (.init fed0 fed0_fresh) (by decide))
      (by decide) _⟩

/-- Delayed delivery beyond Carrier expiry: node 2's relay reaches node 1 at a wall sample past the
Carrier's `E`, and node 1 counts nothing and opens nothing (`DUR-6`). -/
@[req "DUR-6"]
theorem late_relay_counts_nothing :
    legal Kernel.current honest fed0 lateRelay = true ∧
    ((runFrom Kernel.current fed0 lateRelay).worlds 1).node.carriers.all
      (fun k => k.relaySenders == []) = true ∧
    ((runFrom Kernel.current fed0 lateRelay).worlds 1).node.cands.all (fun c => !c.quorum) = true := by
  decide

/-- Duplicate relays: at threshold 3, node 2's relay reaches node 1 twice and is one holder; the
Carrier opens only when node 3's relay arrives. -/
@[req "DUR-6"]
theorem replayed_relay_is_one_holder :
    legal Kernel.current honest fed3 replayedThenThird = true ∧
    ((runFrom Kernel.current fed3 replayed).worlds 1).node.carriers.map (·.relaySenders) = [[2]] ∧
    ((runFrom Kernel.current fed3 replayed).worlds 1).node.cands.all (fun c => !c.quorum) = true ∧
    ((runFrom Kernel.current fed3 replayedThenThird).worlds 1).node.cands.any
      (fun c => c.id == c1.id && c.quorum) = true := by
  decide

/-- A legal schedule in which one node arms while a usable quorum stays unfrozen: node 3 accepts
under duress and arms; nodes 1 and 2 decide normally and release; node 1 holds both partials over an
unfrozen candidate. Nothing in a relay carries node 3's duress to its peers. -/
@[req "DUR-11"]
theorem arm_beside_unfrozen_quorum :
    legal Kernel.current honest fed0 armedBeside = true ∧
    ((runFrom Kernel.current fed0 armedBeside).worlds 3).node.armed = true ∧
    ((runFrom Kernel.current fed0 armedBeside).worlds 1).node.armed = false ∧
    ((runFrom Kernel.current fed0 armedBeside).worlds 2).node.armed = false ∧
    ((runFrom Kernel.current fed0 armedBeside).worlds 1).node.cands.any
      (fun c => c.id == c1.id && !c.frozen && heldQuorum 2 c) = true ∧
    exposedQuorum (partsWorld (runFrom Kernel.current fed0 armedBeside) 1) c1 = true := by
  decide

def stolenPartialTrace : Trace := record Kernel.current [] fed0 stolenPartial
def stolenPartialFinal : Fed := runFrom Kernel.current fed0 stolenPartial

/-- A malicious authenticated partial. Honest node 3's key is copied; a partial signed with it
reaches node 1, which holds it beside its own, though node 3 never released. Authentication proved
the signer and not the signer's node. A partial under node 2's name, whose key nobody holds, is
still refused, and the derived provenance holds: signer 3 is in the extracted set. -/
@[req "NCH-24"]
theorem stolen_key_partial_is_held :
    legal Kernel.current honest fed0 stolenPartial = true ∧
    (stolenPartialFinal.worlds 1).node.cands.any
      (fun c => c.id == c1.id && c.heldSigners == [1, 3]) = true ∧
    (stolenPartialFinal.worlds 3).node.cands.all (fun c => !c.released) = true ∧
    admits honest stolenPartialFinal (.forge (part 2)) = false ∧
    HonestExposureProvenance Kernel.current (fun j => project j stolenPartialTrace)
      stolenPartialFinal.extracted (stolenPartialFinal.worlds 1) (sighash tx1 0) :=
  ⟨by decide, by decide, by decide, by decide,
    node_exposure_provenance rfl (execution_of_legal (.init fed0 fed0_fresh) (by decide))
      (by decide) (by decide)⟩

def fab (s : Nat) : Event := .adversaryExposes (sighash tx1 0) 0 s c1.id
def fabricatedWorld : World :=
  (Kernel.step Kernel.current env0 (Kernel.step Kernel.current env0 (start 1) (fab 1)).1 (fab 2)).1

/-- `Kernel.no_exposed_quorum_without_normal` without `honestExposure` alone. The unconstrained
kernel writes rows under signers 1 and 2 with nothing behind them; with no compromised signer, no
history and so no normal decision, and `0 < t`, the world reaches exposed quorum. The composed
execution refuses each way of writing such a row while nodes 1 and 2 are honest and unextracted: the
kernel event is outside the alphabet, a forged partial needs an extracted key, and a delivery needs
the partial in the inventory. -/
@[req "DUR-8"]
theorem fabricated_honest_row_refused :
    Kernel.Execution Kernel.current
      [((Kernel.step Kernel.current env0 (start 1) (fab 1)).1, env0, fab 2), (start 1, env0, fab 1)]
      fabricatedWorld ∧
    NoHonestNormalDecision Kernel.current (fun _ => []) [] (sighash tx1 0) ∧
    ([] : List Nat).eraseDups.length < fabricatedWorld.node.t ∧
    exposedQuorum fabricatedWorld c1 = true ∧
    ¬ HonestExposureProvenance Kernel.current (fun _ => []) [] fabricatedWorld (sighash tx1 0) ∧
    admits honest fed0 (.process 1 env0 (fab 2)) = false ∧
    admits honest fed0 (.forge (part 2)) = false ∧
    admits honest fed0 (.deliverPartial 1 env0 (part 2)) = false := by
  have hn : NoHonestNormalDecision Kernel.current (fun _ => []) [] (sighash tx1 0) := by
    intro _ _ _ hp
    obtain ⟨_, h, _⟩ := hp
    cases h
  have hq : exposedQuorum fabricatedWorld c1 = true := by decide
  refine ⟨.next env0 (fab 2) (.next env0 (fab 1) (.init _ (by decide))), hn, by decide, hq, ?_,
    by decide, by decide, by decide⟩
  intro hp
  have := no_exposed_quorum_without_normal Kernel.current _ _ _ c1 hp hn (by decide)
  rw [hq] at this
  cases this

def stolenQuorumTrace : Trace := record Kernel.current [] fed0 stolenQuorum
def stolenQuorumFinal : Fed := runFrom Kernel.current fed0 stolenQuorum

/-- `Federation.no_exposed_quorum`, and the kernel theorem under it, without `bound` alone. The keys
of honest node 3, which then takes no further step, and of signer 9 are copied, and each signs a
partial. The provenance premise is derived, the message binding holds, no relay was delivered so
no honest node decided, and the cumulative extracted set reaches `t`: the inventory holds an exposed
quorum. -/
@[req "DUR-8"]
theorem extracted_set_reaches_threshold :
    legal Kernel.current honest fed0 stolenQuorum = true ∧
    3 ∈ honest ∧ stolenQuorumFinal.extracted = [3, 9] ∧
    HotBinding stolenQuorumFinal (sighash tx1 0) ∧
    HonestExposureProvenance Kernel.current (fun j => project j stolenQuorumTrace)
      stolenQuorumFinal.extracted
      (partsWorld stolenQuorumFinal 1) (sighash tx1 0) ∧
    NoHonestNormalDecision Kernel.current (fun j => project j stolenQuorumTrace)
      stolenQuorumFinal.extracted (sighash tx1 0) ∧
    stolenQuorumFinal.extracted.eraseDups.length = (stolenQuorumFinal.worlds 1).node.t ∧
    exposedQuorum (partsWorld stolenQuorumFinal 1) c1 = true := by
  have hb : HotBinding stolenQuorumFinal (sighash tx1 0) := by decide
  refine ⟨by decide, by decide, by decide, hb,
    honest_exposure_provenance rfl (execution_of_legal (.init fed0 fed0_fresh) (by decide)) hb _,
    ?_, by decide, by decide⟩
  apply no_normal_without_receipt
  intro g s hm i env c snd
  rcases mem_record hm with h | h
  · cases h
  · simp only [stolenQuorum, acceptAt, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> subst h <;> simp [actor]

end BtcPolicy.Exhibits.Composition

namespace BtcPolicy.Exhibits.Cohort
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases

/-! ### A Hold-protected blocking cohort

Research task `bps-uaer.5`. Keys 0–4, threshold 3, `hold_secs` 100 at every node, honest nodes 1–4,
identity 0 outside the honest list. The target is input 0 of transaction 100. Each `envAt` gives a
node's own wall and HotClock samples; no sample is compared across nodes.

All four honest nodes accept the target pair under ordinary Carrier 10 at HotClock 10. Relays open
it at node 1 and at node 3. Node 1's fire pass at HotClock 120 releases its target partial, the Hold
having matured. Node 3's pass at HotClock 60 is inside the fire window but before the Hold matures,
and releases nothing. Nodes 2–4 then accept duress Carrier 20, naming a new commitment over the same
transaction, at HotClock 62, and arm on relays at 64 and 65. Armed passes at 170, after every Hold
has matured, release no target partial. A third commitment over the same transaction, accepted
under ordinary Carrier 30 after arming, is born frozen; node 3's holder decision for it opens it,
and its pass at 290, after its Hold matured, releases nothing. No settlement is observed. Identity 0's copied key signs a
target row. The cohort is 2, 3, 4, each read at HotClock 70 of its own. -/

def node (self : Nat) : Node := { A with id := self, t := 3, holdSecs := 100 }
def initial (self : Nat) : World := { node := node self, exposure := [] }
def start : Federation.Fed := { worlds := initial, net := [] }
def honest : List Nat := [1, 2, 3, 4]
def keys : List Nat := [0, 1, 2, 3, 4]
def cohort : List Nat := [2, 3, 4]
def clock (_ : Nat) : Mono := Mono.sample 70
def target : Tx := ⟨100, [0, 1], 10⟩
def escape : Tx := ⟨101, [0, 1], 0⟩
def oldSpend := cand 1 target true (some 100) 900
def oldEscape := cand 2 escape false none 900
def newSpend := cand 5 target true (some 300) 1000
def newEscape := cand 6 escape false none 1000
def laterSpend := cand 7 target true (some 130) 1100
def laterEscape := cand 8 escape false none 1100
def msg : Sighash := sighash target 0

/-- A target row signed with a copied key. -/
def row (s cid : Nat) : Exp := { msg := msg, input := 0, signer := s, hot := true, cid := cid }

def acceptOld (i : Nat) : Federation.Step :=
  .process i (envAt 10 10) (.accept 10 false (Wall.sample 900) oldSpend oldEscape)
def acceptDuress (i : Nat) : Federation.Step :=
  .process i (envAt 105 62) (.accept 20 true (Wall.sample 1000) newSpend newEscape)
def acceptLater (i : Nat) : Federation.Step :=
  .process i (envAt 125 180) (.accept 30 false (Wall.sample 1100) laterSpend laterEscape)

/-- Carrier 10 opens the target at node 1 and node 3; node 1 releases, node 3's Hold blocks. -/
def opening : List Federation.Step :=
  [acceptOld 1, acceptOld 2, acceptOld 3, acceptOld 4,
   .emit 1 10, .emit 2 10, .emit 3 10, .emit 4 10,
   .deliver 1 (envAt 20 20) ⟨3, 10⟩, .deliver 1 (envAt 21 21) ⟨4, 10⟩,
   .deliver 3 (envAt 20 20) ⟨1, 10⟩, .deliver 3 (envAt 21 21) ⟨2, 10⟩,
   .process 1 (envAt 100 120) .firePass, .process 3 (envAt 100 60) .firePass]

/-- Duress Carrier 20 arms node `i` on relays from `a` and `b`. -/
def armAt (i a b : Nat) : List Federation.Step :=
  [.deliver i (envAt 106 64) ⟨a, 20⟩, .deliver i (envAt 107 65) ⟨b, 20⟩]

def duress : List Federation.Step :=
  [acceptDuress 2, acceptDuress 3, acceptDuress 4, .emit 2 20, .emit 3 20, .emit 4 20]

/-- Armed passes, then a later ordinary commitment over the same transaction at node 3. -/
def afterArm : List Federation.Step :=
  [.process 2 (envAt 120 170) .firePass, .process 3 (envAt 120 170) .firePass,
   .process 4 (envAt 120 170) .firePass,
   acceptLater 2, acceptLater 3, acceptLater 4, .emit 2 30, .emit 4 30,
   .deliver 3 (envAt 126 181) ⟨2, 30⟩, .deliver 3 (envAt 127 182) ⟨4, 30⟩,
   .process 3 (envAt 135 290) .firePass]

def steps : List Federation.Step :=
  opening ++ duress ++ armAt 2 3 4 ++ armAt 3 2 4 ++ armAt 4 2 3 ++ afterArm ++
    [.extract 0, .forge (row 0 newSpend.id)]

def trace (r : Rules) (ss : List Federation.Step) : Federation.Trace :=
  Federation.record r [] start ss
def final (r : Rules) (ss : List Federation.Step) : Federation.Fed := Federation.runFrom r start ss

/-- The distinct signers of target input-0 rows in the partial inventory. -/
def signers (f : Federation.Fed) : List Nat :=
  ((f.parts.filter fun x => x.msg == msg && x.input == 0).map Exp.signer).eraseDups

theorem fresh : Federation.Fresh honest start := by
  unfold Federation.Fresh
  decide

theorem record_append (r : Rules) (t : Federation.Trace) (f : Federation.Fed)
    (a b : List Federation.Step) :
    Federation.record r t f (a ++ b) =
      Federation.record r (Federation.record r t f a) (Federation.runFrom r f a) b := by
  induction a generalizing t f with
  | nil => rfl
  | cons s a ih => exact ih _ _

theorem project_record {r : Rules} {i : Nat} {t : Federation.Trace} {f : Federation.Fed}
    {ss : List Federation.Step} {a : World × Env × Event} (h : a ∈ Federation.project i t) :
    a ∈ Federation.project i (Federation.record r t f ss) := by
  induction ss generalizing t f with
  | nil => exact h
  | cons s ss ih => exact ih (Federation.mem_project_cons _ h)

/-- Node 3's normal decision on Carrier 10 opened the target before it armed, derived from its
projected execution by `Kernel.openProvenance_execution`, and stays in its history. -/
theorem member_normal_decision :
    NormalRelease current (Federation.project 3 (trace current steps)) 3 msg oldSpend.id := by
  have hx : Federation.Execution current honest (trace current opening) (final current opening) :=
    Federation.execution_of_legal (.init _ fresh) (by decide +kernel)
  have h3 : 3 ∈ honest := by decide
  have hop := openProvenance_execution current rfl (Federation.project_execution hx h3)
  have hid := Federation.node_id hx h3
  have hc : ∃ c ∈ ((final current opening).worlds 3).node.cands,
      c.quorum = true ∧ c.hot = true ∧ c.id = oldSpend.id ∧ c.tx = target := by decide +kernel
  obtain ⟨c, hc, hq, hh, hcid, htx⟩ := hc
  have hp := hop (by decide +kernel) c hc hq hh
  rw [hid, hcid, htx] at hp
  obtain ⟨g, hg, ho⟩ := hp
  refine ⟨g, ?_, ho⟩
  unfold trace steps
  simp only [List.append_assoc]
  rw [record_append]
  exact project_record hg

theorem holdProtected_of_all {h : History} {m : Mono}
    (hc : h.all (Federation.holdFrame msg m) = true) : Federation.HoldProtected msg m h :=
  List.all_eq_true.1 hc

/-- `DUR-8`'s "never a signing quorum" for the target, from the cohort and with no premise on
normal decisions: node 1 released, cohort member 3 holds an earlier normal decision, identity 0's
key is copied, and the target rows reach two signers against threshold 3. Every cohort member ends
armed with its target candidates, the later one included, open and frozen at node 3. -/
@[req "DUR-8"]
theorem cohort_blocks_quorum :
    Federation.Execution current honest (trace current steps) (final current steps) ∧
    (∀ i ∈ cohort, i ∈ honest ∧ i ∉ (final current steps).extracted ∧
      Federation.HoldProtected msg (clock i) (Federation.project i (trace current steps))) ∧
    ¬ NoHonestNormalDecision current (fun j => Federation.project j (trace current steps))
      (final current steps).extracted msg ∧
    (final current steps).extracted = [0] ∧ signers (final current steps) = [1, 0] ∧
    (cohort.all fun i => ((final current steps).worlds i).node.armed) = true ∧
    ((final current steps).worlds 3).node.cands.all
      (fun c => c.tx != target || (c.quorum && c.frozen && !c.released)) = true ∧
    exposedQuorum (Federation.partsWorld (final current steps) 1) oldSpend = false := by
  have hx : Federation.Execution current honest (trace current steps) (final current steps) :=
    Federation.execution_of_legal (.init _ fresh) (by decide +kernel)
  have hc : ∀ i ∈ cohort, i ∈ honest ∧ i ∉ (final current steps).extracted ∧
      Federation.HoldProtected msg (clock i) (Federation.project i (trace current steps)) := by
    intro i hi
    simp only [cohort, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact ⟨by decide, by decide +kernel, holdProtected_of_all (by decide +kernel)⟩
  have hext : (final current steps).extracted = [0] := by decide +kernel
  refine ⟨hx, hc, fun h => h 3 (by rw [hext]; decide) _ member_normal_decision, hext,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact Federation.cohort_no_exposed_quorum rfl hx _ oldSpend (by decide +kernel) cohort clock hc
    keys (fun j hj => by
      rw [hext] at hj
      simp only [honest, keys, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
      omega)
    (by decide +kernel)

/-! Each sibling drops one condition of `Federation.cohort_no_exposed_quorum` and reaches quorum. -/

/-- Node 2 is also opened by Carrier 10 and its pass at HotClock 120, before it arms, finds the
older commitment's Hold matured: it releases. Its newer commitment over the same transaction,
accepted at 62, is within the Hold of its arming, which does not help: no instant of node 2's clock
protects its history (`Federation.not_holdProtected_of_breach`). -/
def maturedSteps : List Federation.Step :=
  opening ++ [.deliver 2 (envAt 20 20) ⟨3, 10⟩, .deliver 2 (envAt 21 21) ⟨4, 10⟩,
    .process 2 (envAt 100 120) .firePass] ++ duress ++ armAt 2 3 4 ++ armAt 3 2 4 ++
    armAt 4 2 3 ++ afterArm ++ [.extract 0, .forge (row 0 newSpend.id)]

@[req "SPN-38"]
theorem matured_hold_releases :
    Federation.legal current honest start maturedSteps = true ∧
    Federation.holdBreach msg (Federation.project 2 (trace current maturedSteps)) = true ∧
    (∀ m, ¬ Federation.HoldProtected msg m (Federation.project 2 (trace current maturedSteps))) ∧
    2 ∈ signers (final current maturedSteps) ∧
    exposedQuorum (Federation.partsWorld (final current maturedSteps) 1) oldSpend = true := by
  have hb : Federation.holdBreach msg (Federation.project 2 (trace current maturedSteps)) = true := by
    decide +kernel
  exact ⟨by decide +kernel, hb, Federation.not_holdProtected_of_breach hb, by decide +kernel,
    by decide +kernel⟩

/-- Selective delivery: Carrier 10 opens node 4 and duress Carrier 20's relays never reach it, so it
releases at HotClock 170 unarmed. Nodes 2 and 3 still arm and are Hold-protected, a cohort of two,
one short of `n − t + 1`; the count premise fails. -/
def undeliveredSteps : List Federation.Step :=
  opening ++ [.deliver 4 (envAt 20 20) ⟨1, 10⟩, .deliver 4 (envAt 21 21) ⟨2, 10⟩] ++ duress ++
    armAt 2 3 4 ++ armAt 3 2 4 ++ afterArm ++ [.extract 0, .forge (row 0 newSpend.id)]

@[req "DUR-5"]
theorem undelivered_cohort_releases :
    Federation.legal current honest start undeliveredSteps = true ∧
    ((final current undeliveredSteps).worlds 4).node.armed = false ∧
    (∀ m, ¬ Federation.HoldProtected msg m (Federation.project 4 (trace current undeliveredSteps))) ∧
    (∀ i ∈ [2, 3], Federation.HoldProtected msg (clock i)
      (Federation.project i (trace current undeliveredSteps))) ∧
    ¬ keys.eraseDups.length < [2, 3].eraseDups.length + 3 ∧
    4 ∈ signers (final current undeliveredSteps) ∧
    exposedQuorum (Federation.partsWorld (final current undeliveredSteps) 1) oldSpend = true := by
  refine ⟨by decide +kernel, by decide +kernel,
    Federation.not_holdProtected_of_breach (by decide +kernel), ?_, by decide, by decide +kernel,
    by decide +kernel⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact holdProtected_of_all (by decide +kernel)

/-- A cohort member's key is copied after it armed, while the coin is spendable: the copied key
signs the target, and every other condition still holds. -/
def extractedSteps : List Federation.Step := steps ++ [.extract 3, .forge (row 3 oldSpend.id)]

@[req "POL-18"]
theorem extracted_member_signs :
    Federation.legal current honest start extractedSteps = true ∧
    3 ∈ (final current extractedSteps).extracted ∧
    (∀ i ∈ cohort, Federation.HoldProtected msg (clock i)
      (Federation.project i (trace current extractedSteps))) ∧
    3 ∈ signers (final current extractedSteps) ∧
    exposedQuorum (Federation.partsWorld (final current extractedSteps) 1) oldSpend = true := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  intro i hi
  simp only [cohort, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact holdProtected_of_all (by decide +kernel)

/-- `SPN-38`'s HotClock check withdrawn (`Kernel.HoldCheck.windowOnly`): the same schedule, node 3's
pass at HotClock 60 releases on its fire window alone. The cohort's histories are unchanged. -/
def unchecked : Rules := { current with holdCheck := .windowOnly }

@[req "SPN-38"]
theorem hold_unchecked_releases :
    Federation.legal unchecked honest start steps = true ∧
    (∀ i ∈ cohort, Federation.HoldProtected msg (clock i)
      (Federation.project i (trace unchecked steps))) ∧
    signers (final unchecked steps) = [1, 3, 0] ∧
    exposedQuorum (Federation.partsWorld (final unchecked steps) 1) oldSpend = true := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  intro i hi
  simp only [cohort, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact holdProtected_of_all (by decide +kernel)

/-- The earlier-release counterexample is outside the cohort theorem: with `hold_secs` 0, each
honest node's unarmed acceptance of the target has a matured Hold at its own sample, so no instant
protects any honest history of the linked execution. -/
@[req "SPN-38"]
theorem earlier_release_unprotected :
    ∀ i ∈ EarlierRelease.linkedHonest, ∀ m, ¬ Federation.HoldProtected (sighash EarlierRelease.target 0) m
      (Federation.project i EarlierRelease.linkedTrace) := by
  intro i hi
  simp only [EarlierRelease.linkedHonest, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> exact Federation.not_holdProtected_of_breach (by decide +kernel)

end BtcPolicy.Exhibits.Cohort
