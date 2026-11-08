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
/-! Historical defects as executable exhibits (`ADR-0023` decision 6): every theorem over the
`current` value of a guard parameter lives here, so flipping `current` in the module that owns
it goes red HERE and nowhere else, which is what the CI controls assert; beside each, the same
trace under the withdrawn value. Two are not parameters and cannot be flipped: `F58`, whose
refuted theorem has no parameter, and `F65`, whose withdrawn reading was a lost field rather
than a rule value, so its trap is the quorum its exhibit computes. Each defect looked correct,
was built or nearly built, and broke; it is retained here so the trap cannot be re-laid
without a red build. -/

namespace BtcPolicy.Exhibits
open BtcPolicy.Cursor BtcPolicy.Coverage BtcPolicy.Deadline BtcPolicy.Classification
  BtcPolicy.RefreshAge

/-! ## `F51`: the release cursor's cap anchored on the cursor -/

/-- Every published boundary row reproduces under the anchor as it stands. -/
@[req "SPN-38"]
theorem rows_reproduce :
    ∀ r ∈ rows, quotaRungCap current r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 = r.2.2.2.2.2 := by
  decide

/-- On every row, the batch fits the budget and a released cap is at or above `F`. -/
@[req "SPN-38"]
theorem rows_fit_and_progress : ∀ r ∈ rows, rowOk current r = true := by decide

/-- The cap formula `SPN-38` carries is the one rendered from the anchor as it stands. -/
@[req "SPN-38"]
theorem cap_formula_current :
    capFormula = "quota_rung_cap = min(last_rung_index, F + affordable_rungs − 1)" := by decide

/-- `F51`'s candidate releases `[1, 1]` under the anchor as it stands — and, in `Cursor.lean`,
nothing under the withdrawn one (`f51_refused_on_cursor`), forever (`stuck_forever`). -/
@[req "SPN-38"]
theorem f51_current_admits :
    (pass current 3 1 f51Candidate).1 = some (1, 1) := by decide

/-- `F51`'s `DUR-30` row: a median split does not stop the sweep. Two honest nodes, `a = 1`,
latches 2 and 3 from two medians, quota 3, one input, three passes: under the anchor as it stands
both release `[1, 2]` and `DUR-28` finalizes rung 2 from either latch — the lower latch, as
`DUR-30` now says: "so a rung that enough nodes reached still completes"
(`split_finalizes_lower_latch`, for every such pair). Under the withdrawn anchor nothing is
released and nothing finalizes (`split_on_cursor_finalizes_nothing`). -/
@[req "DUR-28"]
theorem dur30_split_finalizes_lower_latch :
    let lower := releases Cursor.current 3 1 3 { floor := 0, latch := 2, a := 1, last := 3 }
    let upper := releases Cursor.current 3 1 3 { floor := 0, latch := 3, a := 1, last := 3 }
    lower = [(1, 1), (2, 2)] ∧ upper = [(1, 1), (2, 2), (3, 3)] ∧
      finalized 2 [lower, upper] 3 = some 2 ∧ finalized 2 [lower, upper] 2 = some 2 := by
  decide

/-! ## `F54`: the coverage denominator that shrank -/

/-- `F54`'s trace at the default coverage: a 100-satoshi vault in two coins. Escape A sweeps the
95 and is resident, so its input has left the read; Escape B is composed over the 5 left
behind. -/
def eA : Coverage.Escape := { id := 1, inputs := [(1, 95)], outputs := [11], delivered := 95 }
def eB : Coverage.Escape := { id := 2, inputs := [(2, 5)], outputs := [12], delivered := 5 }
def f54Pass : Coverage.Pass :=
  { read := [(2, 5)], selected := [eA, eB], residentRungs := [], unconfirmedExternal := [] }

/-- As the rule stands, A's input is counted though the chain shows it spent, so the
denominator is still the whole vault and B does not cover. -/
@[req "DUR-22"]
theorem f54_refused_with_current :
    covers eB.delivered (denominator Coverage.current .countedWhenSpent f54Pass eB) 95 = false := by
  decide

/-- Under the withdrawn rule only the Escape under evaluation is restored, the denominator is
the 5 that remain, and B covers: two input-disjoint Escapes both admissible and both
confirmable, at every coverage (`restoreOne_admits_the_remainder`). -/
@[req "DUR-22"]
theorem f54_admitted_with_restoreOne :
    covers eB.delivered (denominator .restoreOne .countedWhenSpent f54Pass eB) 95 = true := by
  decide

/-! ## `F59`: the unconfirmed external deposit, counted or excluded -/

/-- Coins `A` and `B` are the vault; `D` is an external deposit, unconfirmed on the first pass
and confirmed on the second. `E1` spends `A`; `E2` spends `B` and `D`. They are input-disjoint,
and the coverage is the floor, 51. -/
def e1 : Coverage.Escape := { id := 1, inputs := [(1, 60)], outputs := [11], delivered := 60 }
def e2 : Coverage.Escape :=
  { id := 2, inputs := [(2, 40), (3, 100)], outputs := [12], delivered := 140 }

/-- Pass one: `D` is an unconfirmed external deposit, so it is not in the vault-unspent read. -/
def passOne : Coverage.Pass :=
  { read := [(1, 60), (2, 40)], selected := [e1, e2], residentRungs := [], unconfirmedExternal := [3] }
/-- Pass two: `D` has confirmed, and `E1` is resident so its input has left the read. `E1`'s
coin is absent for a different reason than `D` was, and the two must not be confused (`F54`
against `F59`). -/
def passTwo : Coverage.Pass :=
  { read := [(2, 40), (3, 100)], selected := [e1, e2], residentRungs := [], unconfirmedExternal := [] }

/-- As the rule stands `D` is counted from the first pass, because a selected Escape spends it.
The denominator is 200 on both passes, `E1` does not cover, and only `E2` fires. -/
@[req "DUR-22"]
theorem f59_external_refused_with_current :
    covers e1.delivered (denominator .restoreAll Coverage.currentExternal passOne e1) 51 = false ∧
    covers e2.delivered (denominator .restoreAll Coverage.currentExternal passTwo e2) 51 = true := by
  decide

/-- Under the withdrawn reading `D` is dropped from the count while it is unconfirmed and
counted once it confirms — and only for that reason, since `E1`'s spent coin stays counted
either way. The denominator is 100 on the first pass and 200 on the second, and both
input-disjoint Escapes cover. -/
@[req "DUR-22"]
theorem f59_external_admits_both_with_withdrawn :
    covers e1.delivered (denominator .restoreAll .alwaysExcluded passOne e1) 51 = true ∧
    covers e2.delivered (denominator .restoreAll .alwaysExcluded passTwo e2) 51 = true := by
  decide

/-- The floor holds on both passes under the rule as it stands, which is what refuses the pair. -/
@[req "DUR-22"]
theorem f59_floor_holds :
    Coverage.selectedInputs passOne ≤ denominator .restoreAll .countedWhenSpent passOne e1 ∧
    Coverage.selectedInputs passTwo ≤ denominator .restoreAll .countedWhenSpent passTwo e2 := by
  decide

/-! ## `F59`'s residuals: reachable, recorded, and not repaired -/

/-- A pass at a node that has selected only `E1`, and one that has selected only `E2`. -/
def passOnlyE1 : Coverage.Pass :=
  { read := [(1, 60), (2, 40)], selected := [e1], residentRungs := [], unconfirmedExternal := [3] }
def passOnlyE2 : Coverage.Pass :=
  { read := [(2, 40), (3, 100)], selected := [e2], residentRungs := [], unconfirmedExternal := [] }

/-- **Late selection.** `E2` is selected only after this node released on `E1`, so its inputs
were not in the denominator `E1` was measured against. Both cover, input-disjoint. Structural:
no rule puts a coin in a denominator before the coin exists. -/
@[req "DUR-22"]
theorem late_selection_admits_both :
    covers e1.delivered (denominator .restoreAll .countedWhenSpent passOnlyE1 e1) 51 = true ∧
    covers e2.delivered (denominator .restoreAll .countedWhenSpent passTwo e2) 51 = true := by
  decide

/-- **Cross-node.** One honest node selected only `E1` and another only `E2`; each measures
against its own set, each covers, and two quorums form. The guarantee is per node over the
Escapes it had selected at its first release, which is why `DUR-28`'s "at most one can confirm" is
scoped that way. -/
@[req "DUR-22"]
theorem cross_node_admits_both :
    covers e1.delivered (denominator .restoreAll .countedWhenSpent passOnlyE1 e1) 51 = true ∧
    covers e2.delivered (denominator .restoreAll .countedWhenSpent passOnlyE2 e2) 51 = true := by
  decide

/-- **The phantom prevout.** `SPN-25` tolerates an absent prevout at ingress, so a selected
Escape can name one with an inflated value. Counting it raises the denominator for everyone and
refuses a real Escape; the phantom itself can never confirm (`WTC-24`). Denial inside
`SEC-21`, and the price of counting an input whatever the read says of it. -/
def ePhantom : Coverage.Escape :=
  { id := 9, inputs := [(9, 1000)], outputs := [19], delivered := 0 }
def passPhantom : Coverage.Pass :=
  { read := [(1, 60), (2, 40)], selected := [e1, ePhantom], residentRungs := [],
    unconfirmedExternal := [] }

@[req "DUR-22"]
theorem phantom_denies_a_real_escape :
    covers e1.delivered (denominator .restoreAll .countedWhenSpent passPhantom e1) 51 = false := by
  decide

/-! ## `F59`: a counted input outranks an exclusion, and the shape that subtracted -/

/-- `CHN-30` permits vault change, so one selected Escape can spend another's change output.
`eOut` pays its whole coin to outpoint 50; `eSpend` spends that outpoint. Coin 50 is therefore
both an excluded output and a counted input, and the read no longer shows it. Outpoint 60 is a
resident rung's output, excluded; outpoint 70 is an ordinary vault coin, kept. -/
def eOut : Coverage.Escape := { id := 1, inputs := [(1, 100)], outputs := [50], delivered := 100 }
def eSpend : Coverage.Escape := { id := 2, inputs := [(50, 100)], outputs := [51], delivered := 100 }
def changePass : Coverage.Pass :=
  { read := [(60, 7), (70, 13)], selected := [eOut, eSpend], residentRungs := [60],
    unconfirmedExternal := [] }

/-- The counted input takes precedence: coin 50 is in the denominator at its `witness_utxo`
value even though an exclusion names it, the resident rung's output is dropped, the ordinary
coin is kept, and the floor holds. -/
@[req "DUR-22"]
theorem counted_input_outranks_exclusion :
    denominator .restoreAll .countedWhenSpent changePass eSpend = 213 ∧
    Coverage.selectedInputs changePass = 200 ∧
    Coverage.selectedInputs changePass
      ≤ denominator .restoreAll .countedWhenSpent changePass eSpend := by
  decide

/-- The shape this module carried before `F59` — the read, plus the restorations, minus the
exclusions, as numbers — subtracts coin 50 and the rung it never added to the read, and lands
below the floor on the same pass. That is why the denominator is built as a filter over the
read with the counted inputs added, and never as arithmetic. -/
@[req "DUR-22"]
theorem subtracting_breaks_floor_on_that_pass :
    Coverage.subtractShape (Coverage.sumValues changePass.read)
        (Coverage.selectedInputs changePass) 107 < Coverage.selectedInputs changePass := by
  decide

/-! ## `F58`: the deadline theorem that did not hold -/

/-- The conformance item for `DUR-14` asked for `T' ≤ T` (`F58`); `Deadline.not_never_grows` refutes it and `late_acceptance_exhibit`
is the input. Restated here so the exhibit file lists every recorded defect. -/
@[req "DUR-14"]
theorem f58_exhibit : shrink 10 100 1 11 = 11 ∧ ¬ (shrink 10 100 1 11 ≤ 10) := by decide

/-! ## `F57`: the claw-back burn that repeated -/

/-- `F57`'s trace on a 1000-satoshi coin: 1 to the escape wallet, 100 burned, 899 back to the vault.
Under the no-change rule as it stands it is refused. -/
@[req "CHN-35"]
theorem f57_refused_with_current : burnAdmitted current 1000 1 = false := by decide

/-- Under the withdrawn rule it is admitted, and so is the claw-back over its 899-satoshi change,
which burns 89 more (`permitted_burns_again`, for every coin that can pay the dust). -/
@[req "CHN-35"]
theorem f57_admitted_with_permitted :
    burnAdmitted .permitted 1000 1 = true ∧ change 1000 1 = 899 ∧
      burnAdmitted .permitted 899 1 = true := by
  decide

/-! ## `DEF-15`: the mixed arm of classification -/

/-- Every output of the mixed spend is allowlisted, so it passes evaluation, and classification
refuses it. Faulting the mixed arm to escape-class is red here. -/
@[req "CHN-30"]
theorem def15_mixed_allowlisted_but_unclassified :
    allowlisted mixedSpend = true ∧ classify mixedSpend = none := by decide

/-- For every transaction: an escape output beside a hot output has no class, whatever else it
carries. -/
@[req "CHN-30"]
theorem escape_and_hot_unclassified (outs : List Output) (e h : Output) (he : e ∈ outs)
    (hek : member e = .escape) (hh : h ∈ outs) (hhk : member h = .hot) : classify outs = none := by
  have mem : ∀ o ∈ outs, member o ≠ .vault →
      outputClass o ∈ (outs.filter (!inVault ·)).map outputClass := fun o ho hv =>
    List.mem_map.2 ⟨o, List.mem_filter.2 ⟨ho, by simpa [inVault] using hv⟩, rfl⟩
  have hE := mem e he (by simp [hek])
  have hH := mem h hh (by simp [hhk])
  rw [show outputClass e = some .escape by simp [outputClass, hek]] at hE
  rw [show outputClass h = some .hot by simp [outputClass, inAllowlist, hhk]] at hH
  unfold classify
  generalize (outs.filter (!inVault ·)).map outputClass = dest at hE hH
  have hne : dest.isEmpty = false := by cases dest <;> simp_all
  simp [hne, hE, hH]

/-! ## `POL-11`: non-hot classification and outflow -/

/-- `POL-11`: "refresh and escape sweeps have zero outflow by construction". This follows
from the returned class for arbitrary outputs and values, including vault change, with no
allowlist premise. Descriptor membership remains `Classification.member`'s boundary. -/
@[req "POL-11"]
theorem non_hot_class_zero_outflow (outs : List Output)
    (h : classify outs = some .escape ∨ classify outs = some .refresh) :
    hotOutflow outs = 0 := by
  have hall : ((outs.filter (!inVault ·)).map outputClass).all (· == some .escape) = true := by
    unfold classify at h
    dsimp only at h
    split at h
    · rename_i he
      simp only [List.isEmpty_iff] at he
      simp [he]
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · assumption
          · simp at h
  have hempty : counted outs = [] := by
    unfold counted
    rw [List.filter_eq_nil_iff.mpr ?_]
    · rfl
    intro o ho
    by_cases hv : inVault o = true
    · simp [hv]
    · have hc := List.all_eq_true.mp hall (outputClass o)
        (List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho, by simpa using hv⟩, rfl⟩)
      cases o with
      | mk value kind => cases kind <;> simp_all [outputClass, inVault, inAllowlist, member]
  simp [hotOutflow, hempty]

/-- Nonempty, positive-valued escape outputs with vault change and refresh outputs inhabit
both class premises of `non_hot_class_zero_outflow`. -/
@[req "POL-11"]
theorem non_hot_positive_outputs :
    classify [⟨90, .escape⟩, ⟨9, .vault⟩] = some .escape ∧
    hotOutflow [⟨90, .escape⟩, ⟨9, .vault⟩] = 0 ∧
    classify [⟨99, .vault⟩] = some .refresh ∧ hotOutflow [⟨99, .vault⟩] = 0 := by decide

/-! ## `F52`: the refresh interval read from a node's own log -/

/-- `F52`'s alternation under the rule as it stands: the first link is admitted — `X` is thirty
days old — and the second is refused on EVERY honest node, because `Y` is two days old on the
chain they all read. Under the withdrawn rule the node the second link is presented to admits it,
and every later link likewise (`perNodeLog_admits_every_link`): seven confirmed refreshes in
fifteen days against a thirty-day interval. -/
@[req "SPN-46"]
theorem f52_refused_with_current :
    (∀ l ∈ links.take 1, ∀ node ∈ [0, 1], verdict RefreshAge.current node l = true) ∧
    (∀ l ∈ (links.drop 1).take 1, ∀ node ∈ [0, 1], verdict RefreshAge.current node l = false) := by
  decide

/-- `WTC-25`'s bump path under the rule as it stands: an unconfirmed refresh leaves no trace on
the chain, so its higher-fee replacement over the same coin is admitted. Under the withdrawn rule
the node's log holds the coin and refuses it for the rest of the interval
(`perNodeLog_refuses_replacement`). This is the ingress half of the bump path; the fire-time
half, the replacement's prevouts admitted by the walk over the resident, is
`PackageAncestry.twin_admitted_with_current` over `Package.current`. -/
@[req "WTC-25"]
theorem wtc25_replacement_admitted_with_current : bumpVerdict RefreshAge.current = true := by
  decide

end BtcPolicy.Exhibits

namespace BtcPolicy.Exhibits.ReleaseKernel
open BtcPolicy.Clocks BtcPolicy.Kernel

/-! ## The release and Carrier kernel: `DEF-1`, `DEF-4`, `F57` row 8, `DUR-29`'s race, and
decision 9's exposure case, each over `current` and beside it the same trace under the
withdrawn value written out in full (so a flip of `current` reaches only the `current` twin). -/

abbrev A := Kernel.RegistrationCases.A
abbrev w0 := Kernel.RegistrationCases.w0
abbrev tx1 := Kernel.RegistrationCases.tx1
abbrev txE := Kernel.RegistrationCases.txE
abbrev tx3 := Kernel.RegistrationCases.tx3
abbrev claw := Kernel.RegistrationCases.claw
abbrev cand := Kernel.RegistrationCases.cand
abbrev c1 := Kernel.RegistrationCases.c1
abbrev e1 := Kernel.RegistrationCases.e1
abbrev c3 := Kernel.RegistrationCases.c3
abbrev e3 := Kernel.RegistrationCases.e3
abbrev c1' := Kernel.RegistrationCases.c1'
abbrev e1' := Kernel.RegistrationCases.e1'
abbrev envAt (wall mono : Nat) (seen : List Tx := []) : Env :=
  Kernel.RegistrationCases.envAt wall mono seen
abbrev env0 := Kernel.RegistrationCases.env0
abbrev envFire := Kernel.RegistrationCases.envFire
abbrev envClaw := Kernel.RegistrationCases.envClaw
abbrev envLate := Kernel.RegistrationCases.envLate
abbrev envExcursion := Kernel.RegistrationCases.envExcursion
abbrev envBack := Kernel.RegistrationCases.envBack

def withdrawnRetire : Rules :=
  { retire := .byWall, reauth := .beforeSend, poison := .asserted, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic }
def withdrawnReauth : Rules :=
  { retire := .byMono, reauth := .beforeAssembly, poison := .asserted, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic }
def withdrawnPoison : Rules :=
  { retire := .byMono, reauth := .beforeSend, poison := .byLockOrder, defeat := .terminalFlag,
    traversal := .always, dynamics := .dynamic }
def withdrawnDefeat : Rules :=
  { retire := .byMono, reauth := .beforeSend, poison := .asserted, defeat := .mempoolResidency,
    traversal := .always, dynamics := .dynamic }
/-- `DUR-20`'s traversal made conditional on the shrink (`F54`'s row), and `DUR-14`'s `T` made
static, each beside every other value as it stands. -/
def withdrawnTraversal : Rules :=
  { retire := .byMono, reauth := .beforeSend, poison := .asserted, defeat := .terminalFlag,
    traversal := .onlyWhenMoved, dynamics := .dynamic }
def withdrawnDynamics : Rules :=
  { retire := .byMono, reauth := .beforeSend, poison := .asserted, defeat := .terminalFlag,
    traversal := .always, dynamics := .static }

def isBroadcast : Effect → Bool
  | .broadcast _ => true
  | _ => false

/-! ### `DEF-1`: the Carrier survives a forward wall excursion -/

/-- Accepted at wall 50 with `E = 200`, so `D = 155`; the prune driver runs at the excursion; a
receipt arrives once the wall is back. -/
def def1Trace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (envExcursion, .tick), (envBack, .receipt 10 1) ]

/-- As it stands, `NCH-40` (3) reads the HotClock: the intent is still there and the receipt
commits it. -/
@[req "NCH-35"]
theorem def1_refused_with_current :
    (run current w0 (def1Trace.take 2)).1.node.carriers.any (fun k => k.cid == 10 && k.D == Mono.sample 155) = true ∧
    (run current w0 def1Trace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = true := by
  decide

/-- Under the withdrawn value the excursion deletes the node's own intent, and the receipt
finds nothing: the node is left unarmed beside whoever holds the partial. -/
@[req "NCH-35"]
theorem def1_admitted_with_withdrawn :
    (run withdrawnRetire w0 (def1Trace.take 2)).1.node.carriers = [] ∧
    (run withdrawnRetire w0 def1Trace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = false := by
  decide

/-! ### `F65`: one peer relaying twice is one holder

At a threshold `A3.t` two distinct relays are needed and the duplicate has somewhere to go
wrong; on `A` the first relay already reaches `t`. -/

/-- `A` with a higher threshold. A `Node` carries no `n`, so the shape here is `t` alone. -/
def A3 : Node := { A with t := 3 }
def w3 : World := { node := A3, exposure := [] }

def oneRelayTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1) ]
/-- Peer 1 relays the same Carrier twice. -/
def dupRelayTrace : List (Env × Event) := oneRelayTrace ++ [(env0, .receipt 10 1)]
/-- Peers 1 and 2 relay it once each: the same two receipts, differing only in who sent the
second. -/
def twoRelaysTrace : List (Env × Event) := oneRelayTrace ++ [(env0, .receipt 10 2)]
/-- A relay carrying this node's OWN id after peer 1's. `DUR-5` counts each distinct PEER and
`A3.id` is already the `+ 1`, so it must add nothing. -/
def selfRelayTrace : List (Env × Event) := oneRelayTrace ++ [(env0, .receipt 10 0)]

/-- The count `F65` found in this model: a number bumped once per receipt, with no sender to
deduplicate against. Not a `Rules` value — the withdrawn reading here was a lost field, so
there is nothing to flip and no `withdrawn` prefix is claimed. It is arithmetic over the trace
and runs no kernel term: it counts every `receipt` in the list, whatever its commitment id and
whether or not `DUR-6`'s `D` and `E` guards would have admitted it, so it agrees with the
field this model used to carry only on traces like the ones below, where every relay names one
live Carrier. It is written out so the comparison is visible; the conjunct that goes red if
the count comes back is the quorum. -/
def f65RelayCount (tr : List (Env × Event)) : Nat :=
  1 + (tr.filter fun x => match x.2 with | .receipt _ _ => true | _ => false).length

def relaySendersOf (w : World) (cid : Nat) : List Nat :=
  ((w.node.carriers.find? (·.cid == cid)).map Carrier.relaySenders).getD []

/-- `DUR-5` counts "each distinct peer whose authenticated relay of the same Carrier this node
receives" and `DUR-6` says "a sender already counted … MUST be an idempotent no-op". Peer 1
relaying
twice is one holder by `holderCount`, so the pair's release gate stays shut — that second
conjunct is what goes red if the count comes back. Beside it the withdrawn count reaches `t` on
the same trace, which is `DUR-8`'s gate opened a relay early, under either PIN. Two distinct
peers do reach it, so what the holder set refuses is the duplicate and not the relay; a relay
carrying this node's own id is refused the same way (`self_relay_is_not_a_second_holder`). -/
@[req "DUR-6"]
theorem duplicate_relay_is_one_holder :
    holderCount (relaySendersOf (run current w3 dupRelayTrace).1 10) = 2 ∧
    (run current w3 dupRelayTrace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = false ∧
    A3.t ≤ f65RelayCount dupRelayTrace ∧
    (run current w3 twoRelaysTrace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = true := by
  decide

/-- `DUR-5`'s "each distinct peer": a relay carrying this node's own `sender_node_id` is the
node it already counts, so it is the same no-op as a duplicate. Without the check `holderCount`
would count this node twice and reach `t` a relay early, exactly as the duplicate did. -/
@[req "DUR-5"]
theorem self_relay_is_not_a_second_holder :
    holderCount (relaySendersOf (run current w3 selfRelayTrace).1 10) = 2 ∧
    (run current w3 selfRelayTrace).1.node.cands.any (fun c => c.id == 1 && c.quorum) = false := by
  decide

/-- And the repeat is a no-op on the whole world, not only on the count: `DUR-6`'s "idempotent
no-op" read literally, at a state where the Carrier already holds that sender. -/
@[req "DUR-6"]
theorem duplicate_relay_changes_nothing :
    step current env0 (run current w3 oneRelayTrace).1 (.receipt 10 1)
      = ((run current w3 oneRelayTrace).1, []) := by
  decide

/-! ### Authenticated partial receipt: possession and exposed authority stay distinct -/

/-- Acceptance supplies this node's own withheld partial through `born`; the Carrier's holder
set is then complete. No partial has left this node yet. -/
def partialStart : World := (run current w0 oneRelayTrace).1

def partialOnce : World :=
  (step current env0 partialStart (.receivePartial (sighash tx1 0) 0 1 1)).1

def heldOf (w : World) (cid : Nat) : List Nat :=
  ((w.node.cands.find? (·.id == cid)).map Cand.heldSigners).getD []

/-- The accepted candidate holds self, then admits peer 1. The distinct held count rises and
reaches quorum, while self's withheld partial is still absent from exposed authority. -/
@[req "NCH-24"]
theorem receivePartial_admits_peer :
    heldOf partialStart 1 = [A.id] ∧
    heldOf partialOnce 1 = [A.id, 1] ∧
    (heldOf partialOnce 1).eraseDups.length = (heldOf partialStart 1).eraseDups.length + 1 ∧
    partialOnce.node.cands.any (fun c => c.id == 1 && heldQuorum A.t c) = true ∧
    exposedQuorum partialOnce c1 = false ∧
    partialOnce.node.cands.any (·.released) = false ∧
    (step current env0 partialStart (.receivePartial (sighash tx1 0) 0 1 1)).2 = [] := by
  decide

/-- `NCH-25`: "A duplicate is an idempotent `ACCEPTED` and never displaces the first."
The exact held list stays put; the world legitimately appends another exposed-authority row. -/
@[req "NCH-25"]
theorem duplicate_partial_preserves_held :
    let again := (step current env0 partialOnce (.receivePartial (sighash tx1 0) 0 1 1)).1
    heldOf again 1 = heldOf partialOnce 1 ∧
    again.node.cands.map Cand.heldSigners = partialOnce.node.cands.map Cand.heldSigners ∧
    again.exposure = partialOnce.exposure ++
      [{ msg := sighash tx1 0, input := 0, signer := 1, hot := true, cid := 1 }] := by
  decide

/-- The honest node releases and another signer exposes, without delivering. The candidate
still holds only self, despite world-level quorum. -/
def partialExposedOnly : World :=
  (run current partialStart [(envFire, .firePass),
    (envFire, .adversaryExposes (sighash tx1 0) 0 1 1)]).1

@[req "POL-18"]
theorem exposure_without_receivePartial_is_not_held :
    exposedQuorum partialExposedOnly c1 = true ∧
    heldOf partialExposedOnly 1 = [A.id] ∧
    partialExposedOnly.node.cands.any (fun c => c.id == 1 && heldQuorum A.t c) = false := by
  decide

/-- The candidate has been pruned. Arrival still records exposed authority, and creates no
candidate or possession. -/
@[req "NCH-24"]
theorem receivePartial_after_prune_still_exposes :
    let pruned := (step current envLate partialStart .prune).1
    let received := (step current envLate pruned (.receivePartial (sighash tx1 0) 0 1 1)).1
    pruned.node.cands = [] ∧ received.node = pruned.node ∧
    received.exposure = pruned.exposure ++
      [{ msg := sighash tx1 0, input := 0, signer := 1, hot := true, cid := 1 }] := by
  decide

/-- A resident id with the wrong sighash cannot gain possession, and cannot suppress the
independent exposed-authority append either. -/
@[req "NCH-24"]
theorem mismatched_receivePartial_still_exposes :
    let received := (step current env0 partialStart (.receivePartial (sighash tx3 0) 0 1 1)).1
    heldOf partialStart 1 = [A.id] ∧ received.node = partialStart.node ∧
    received.exposure = partialStart.exposure ++
      [{ msg := sighash tx3 0, input := 0, signer := 1, hot := true, cid := 1 }] := by
  decide

/-- The package test reads possession. This node has released and the world holds `t` exposed
signers on `tx1`, but the peer's partial was exposed and never delivered, so `packageAccepted`
leaves the package unassembled: exposed authority this node never received is not something it
can finalize from. -/
@[req "SPN-39"]
theorem exposed_not_held_cannot_assemble :
    let assembled := (step current envFire partialExposedOnly (.packageAccepted 1)).1
    exposedQuorum partialExposedOnly c1 = true ∧
    partialExposedOnly.node.cands.any (fun c => c.id == 1 && c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = false := by
  decide

/-- The same release with the peer's partial delivered: the store holds it, and the package can
be assembled (`received_can_assemble`). -/
def partialReceived : World :=
  (run current partialStart [(envFire, .firePass),
    (envFire, .receivePartial (sighash tx1 0) 0 1 1)]).1

/-- And a node that received can assemble: released, `t` held, and the package test passes. -/
@[req "SPN-39"]
theorem received_can_assemble :
    let assembled := (step current envFire partialReceived (.packageAccepted 1)).1
    heldOf partialReceived 1 = [A.id, 1] ∧
    partialReceived.node.cands.any (fun c => c.id == 1 && c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = true := by
  decide

/-- A partial on input 7 — an input this kernel does not model — is exposed authority and not
possession: the step appends its row, the store keeps the held set `[A.id]`, and after this node
releases the package test still refuses. The trap that goes red if the store guard stops reading
the input: without it the held set reaches `t` on a row `exposedQuorum` never counts, and
`Kernel.released_held_exposed` is false. -/
@[req "NCH-24"]
theorem input7_receipt_is_exposed_not_held :
    let received := (step current env0 partialStart (.receivePartial (sighash tx1 0) 7 1 1)).1
    let assembled := (run current received [(envFire, .firePass),
      (envFire, .packageAccepted 1)]).1
    received.exposure = partialStart.exposure ++
      [{ msg := sighash tx1 0, input := 7, signer := 1, hot := true, cid := 1 }] ∧
    heldOf received 1 = [A.id] ∧
    received.node.cands.any (fun c => c.id == 1 && heldQuorum A.t c) = false ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = false := by
  decide

/-- The `released` conjunct is live: the peer's partial is held and the candidate is due, but
this node has run no fire pass, so it has released nothing and assembles nothing. -/
@[req "SPN-39"]
theorem held_without_release_cannot_assemble :
    let assembled := (step current envFire partialOnce (.packageAccepted 1)).1
    partialOnce.node.cands.any
      (fun c => c.id == 1 && due current envFire partialOnce.node c && heldQuorum A.t c && !c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = false := by
  decide

/-! ### `DUR-29`'s race under both values, over one `step` -/

/-- `SPN-39`: "the linearization point between arming and sending". The current rule
discharges the general theorem's re-authorization premise, independently of any chosen trace. -/
@[req "SPN-39"]
theorem no_hot_broadcast_while_armed_with_current (env : Env) (w : World)
    (hw : Reachable current w) (ha : w.node.armed = true) (cid : Nat) :
    ∀ eff ∈ (step current env w (.send cid)).2,
      ∃ c ∈ w.node.cands, c.id = cid ∧ c.hot = false ∧ eff = .broadcast c.tx.id :=
  no_hot_broadcast_while_armed current rfl env w hw ha cid

/-- Acceptance, the duress holder decision, release, peer possession and package acceptance
of the selected Escape, through the existing kernel transitions. -/
def armedEscapePrefix : List (Env × Event) :=
  [(env0, .accept 10 true (Wall.sample 200) c1 e1), (env0, .receipt 10 1),
   (envFire, .firePass), (envFire, .receivePartial (sighash txE 0) 0 1 2),
   (envFire, .packageAccepted 2)]

/-- The armed-send premises are inhabited and permit a non-hot broadcast. -/
@[req "DUR-11"]
theorem armed_escape_can_broadcast :
    let w := (run current w0 armedEscapePrefix).1
    Reachable current w ∧ w.node.armed = true ∧
      (step current envFire w (.send 2)).2 = [.broadcast txE.id] := by
  refine ⟨(ProvenanceCases.execution_run current armedEscapePrefix
    (.init A (by decide))).reachable, ?_, ?_⟩ <;> decide

/-- The arm — the second Carrier's holder decision — injected after package acceptance and before
the send: `DUR-11`'s "refused at the broadcast authorization even after mempool acceptance
passed". -/
def raceTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1),
    (env0, .receipt 10 1),                                 -- holder decision: pair opened
    (envFire, .firePass),                                  -- A's partial queued: exposed
    (envFire, .receivePartial (sighash tx1 0) 0 2 1),      -- peer 2's partial delivered, held
    (envFire, .packageAccepted 1),                         -- assembled and mempool-tested
    (envFire, .accept 20 true (Wall.sample 300) c3 e3),
    (envFire, .receipt 20 1),                              -- ARM: every hot candidate frozen
    (envFire, .send 1) ]

/-- As it stands: nothing is broadcast, and the node is armed. -/
@[req "DUR-29"]
theorem race_refused_with_current :
    ((run current w0 raceTrace).2.filter isBroadcast) = [] ∧
    (run current w0 raceTrace).1.node.armed = true := by decide

/-- Under the withdrawn value — the check before assembly instead of before the send — the same
trace broadcasts the coerced spend. -/
@[req "DUR-29"]
theorem race_admitted_with_withdrawn :
    (run withdrawnReauth w0 raceTrace).2.filter isBroadcast = [.broadcast 100] := by decide

/-- The partial itself left at the fire pass: exposure is at "queued for transport", not at the
send, so the refused broadcast revokes nothing. -/
@[req "POL-18"]
theorem race_partial_already_exposed :
    (run current w0 raceTrace).1.exposure.any (fun e => e.signer == 0 && e.msg == sighash tx1 0) = true := by
  decide

/-! ### Decision 9: exposure at world level -/

/-- Two SpendRequests over one transaction with different expiries. `c1`'s partial is released,
`c1` is pruned at its expiry, `c1'` over the same `tx1` is accepted; one compromised signer adds
its partial. -/
def twoRequestsTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1),
    (env0, .receipt 10 1),
    (envFire, .firePass),                                   -- A releases under commitment 1
    (envLate, .prune),                                      -- c1 expired: gone from the registry
    (envLate, .accept 30 false (Wall.sample 250) c1' e1'),  -- commitment 5, same tx1
    (envLate, .adversaryExposes (sighash tx1 0) 0 2 5) ]

def wTwo : World := (run current w0 twoRequestsTrace).1

/-- The count a commitment-keyed history would give `c1'`. -/
def finalizableByCommitment (w : World) (c : Cand) : Bool :=
  w.node.t ≤ ((w.exposure.filter fun (e : Exp) => e.cid == c.id && e.input == 0).map
    Exp.signer).eraseDups.length

/-- The count a node-local history pruned with the candidate would give: this node's own
RELEASED partials, read from resident candidates only. Decision 9's retained WRONG model, and
named for what it reads rather than for finalizability — `Cand.heldSigners` is the real
node-local possession, and release is not possession. -/
def releasedResidentQuorum (w : World) (c : Cand) : Bool :=
  let own := if w.node.cands.any (fun d => d.id == c.id && d.released) then 1 else 0
  let others := ((w.exposure.filter fun (e : Exp) => e.msg == sighash c.tx 0 && e.signer != w.node.id).map
    Exp.signer).eraseDups.length
  w.node.t ≤ own + others

/-- `c1` is gone, `c1'` was never released by this node, and yet the world holds `t` partials on
`c1'`'s sighash: `c1'` is finalizable. The two wrong models each report it safe. -/
@[req "POL-18"]
theorem exposure_key_exhibit :
    wTwo.node.cands.any (fun c => c.id == 1) = false ∧
    wTwo.node.cands.any (fun c => c.id == 5 && c.released) = false ∧
    exposedQuorum wTwo c1' = true ∧
    finalizableByCommitment wTwo c1' = false ∧
    releasedResidentQuorum wTwo c1' = false := by decide

/-- The safety statement the wrong models would let one prove — "if this node released nothing
resident over the transaction, the transaction is not finalizable" — is false at world level. -/
@[req "POL-18"]
theorem no_resident_release_does_not_mean_safe :
    ¬ (∀ w : World, ∀ c : Cand,
        (∀ d ∈ w.node.cands, d.tx = c.tx → d.released = false) → exposedQuorum w c = false) := by
  intro h
  have := h wTwo c1' (by decide)
  simp [exposure_key_exhibit.2.2.1] at this

/-! ### `DEF-4`: poison the lock, drive a fire pass -/

def poisonTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1), (envFire, .panic), (envFire, .firePass) ]

@[req "DUR-9"]
theorem def4_refused_with_current :
    (run current w0 poisonTrace).2 = [] ∧ (run current w0 poisonTrace).1.node.lockedDown = true := by decide

/-- With the gate resting on lock order alone, the same pass releases the partial. -/
@[req "DUR-9"]
theorem def4_admitted_with_withdrawn :
    (run withdrawnPoison w0 poisonTrace).2 = [.queuePartial (sighash tx1 0) 0 true 1] := by decide

/-! ### `F57` row 8: a defeated hot spend at its fire time after the claw-back is evicted -/

/-- The claw-back is seen at wall 120, past `c1`'s fire time of 100; then it is evicted (the chain
view no longer shows it) and a fire pass runs. -/
def f57Trace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1),
    (envClaw, .settle claw), (envFire, .firePass) ]

/-- As it stands: the defeated spend is resident, terminal, and releases nothing. -/
@[req "SPN-33"]
theorem f57row8_refused_with_current :
    (run current w0 f57Trace).2 = [] ∧
    (run current w0 f57Trace).1.node.cands.any (fun c => c.id == 1 && c.terminal) = true := by decide

/-- Under the withdrawn reading the evicted claw-back un-defeats it and the spend fires. -/
@[req "SPN-33"]
theorem f57row8_admitted_with_withdrawn :
    (run withdrawnDefeat w0 f57Trace).2 = [.queuePartial (sighash tx1 0) 0 true 1] := by decide

/-- `DEF-5` on the same trace: the claw-back's settlement clears the defeated spend from the
pending log, which `/pending` reads, and the candidate stays resident; `SPN-33` says
"removal from the pending log is not removal from the registry". -/
@[req "SPN-30"]
theorem def5_defeated_off_pending :
    pending current envFire (run current w0 f57Trace).1.node = [] ∧
    (run current w0 f57Trace).1.node.cands.any (fun c => c.id == 1) = true := by decide

/-! ### A normal release completes -/

def normalTrace : List (Env × Event) :=
  [ (env0, .accept 10 false (Wall.sample 200) c1 e1), (env0, .receipt 10 1), (envFire, .firePass),
    (envFire, .receivePartial (sighash tx1 0) 0 1 1), (envFire, .packageAccepted 1),
    (envFire, .send 1) ]

@[req "SPN-39"]
theorem normal_release_completes :
    (run current w0 normalTrace).2 = [.queuePartial (sighash tx1 0) 0 true 1, .broadcast 100] ∧
    (run current w0 normalTrace).1.node.cands.any (fun c => c.id == 1 && c.broadcast) = true := by
  decide

/-! ### Bounded enumeration, from the package-accepted state

An exhibit over a stated bound, with no completeness claim: 2-of-3, one hot pair and one duress
pair accepted, the hot partial released, the peer's partial received and the package accepted
(`wReady`), every word of up to three events over the ten-event alphabet, one environment (the
claw-back visible) per step. From acceptance the race is six events away and a three-deep
enumeration is a silent success under the flip; from `wReady` it is two.

It is not evidence for `packageAccepted`'s quorum conjunct. `safeStep` checks nothing possession
can affect — no hot `queuePartial` and no `broadcast` on an armed node, every hot candidate of an
armed node frozen — so it proves the same with the package test reading possession or exposure.
The exhibits of the receipt section are the evidence for that conjunct. -/

def wReady : World :=
  (run current w0 [(env0, .accept 10 false (Wall.sample 200) c1 e1),
    (env0, .accept 20 true (Wall.sample 300) c3 e3), (env0, .receipt 10 1), (envFire, .firePass),
    (envFire, .receivePartial (sighash tx1 0) 0 2 1), (envFire, .packageAccepted 1)]).1

def alphabet : List Event :=
  [ .receipt 10 1, .receipt 20 1, .firePass, .packageAccepted 1, .send 1, .settle claw, .prune,
    .tick, .panic, .receivePartial (sighash tx1 0) 0 2 1 ]

def traces : Nat → List (List Event)
  | 0 => [[]]
  | k + 1 => (traces k).flatMap fun t => alphabet.map fun e => t ++ [e]

/-- What every step must satisfy: on an armed node no hot partial is queued and nothing is
broadcast (`DUR-8`, `DUR-11`), and afterwards every hot candidate of an armed node is frozen. -/
def safeStep (r : Rules) (env : Env) (w : World) (e : Event) : Bool :=
  let (w', effs) := step r env w e
  (!w.node.armed || effs.all fun eff => match eff with
    | .queuePartial _ _ hot _ => !hot
    | .broadcast _ => false) &&
  (!w'.node.armed || w'.node.cands.all fun c => !c.hot || c.frozen)

def safeRun (r : Rules) (w : World) : List Event → Bool
  | [] => true
  | e :: es => safeStep r envClaw w e && safeRun r (step r envClaw w e).1 es

theorem traces_count : (traces 3).length = 1000 := by decide +kernel

set_option maxRecDepth 100000 in
@[req "DUR-8"]
theorem bounded_from_ready : (traces 3).all (safeRun current wReady) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The enumeration is not vacuous: under the withdrawn value it finds the race, the shortest
offending word is `[receipt 20 1, send 1]` — arm, then send — and no one-event word offends. -/
@[req "DUR-29"]
theorem bounded_from_ready_withdrawn_finds_race :
    (traces 3).all (safeRun withdrawnReauth wReady) = false ∧
    safeRun withdrawnReauth wReady [.receipt 20 1, .send 1] = false ∧
    (traces 1).all (safeRun withdrawnReauth wReady) = true := by decide +kernel

end BtcPolicy.Exhibits.ReleaseKernel

namespace BtcPolicy.Exhibits.HotLedger
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt)

/-! ## The Hot ledger: `ADR-0014`'s trace made reachable, and `DEF-5`'s settlement refund

`ADR-0014`'s configuration, read from `Budget.params` rather than restated: 2-of-3 with no
compromised node, `hot_window_secs = max_commitment_age_secs = 120`, `hold_secs = 20`,
`combine_slack_secs = 100`. The cap is `V`, so one maximal spend fills a window.

`Budget.lean` holds the same timeline as data — "the timeline as data … not a lifecycle exhibit
showing each row reachable" — and names what it does not carry. The run below carries four of
those five: `DUR-8` withholding the first release until the holder decision, that decision
admitted at 100, the release of the first charge at the second acceptance's own admission check at
121 (`POL-19`), and the completion at 141 as a fresh exposure. The fifth — that pruning has not
collected the first candidate — is vacuous here, because the run prunes nothing. -/

def V : Nat := 100
def cfg : Config := { cap := V, window := Budget.params.window }

def A : Node :=
  { id := 0, t := Budget.params.t, armed := false, poisoned := false, lockedDown := false,
    carriers := [], cands := [], T := Wall.sample 0, sweepActive := false, selected := [],
    duressDelay := 200, epsilon := 5, combineSlack := Budget.params.slack,
    holdSecs := Budget.params.hold }

def sys0 : Sys := { world := { node := A, exposure := [] }, led := [] }

/-- The first hot spend and its Escape, the second pair, and, for `DEF-5`, a third pair over
disjoint inputs with a claw-back that conflicts with the first. -/
def hot1 : Tx := { id := 200, inputs := [0], outflow := V }
def esc1 : Tx := { id := 201, inputs := [0, 1], outflow := 0 }
def hot2 : Tx := { id := 202, inputs := [2], outflow := V }
def esc2 : Tx := { id := 203, inputs := [2, 3], outflow := 0 }
def hot3 : Tx := { id := 204, inputs := [4], outflow := V }
def esc3 : Tx := { id := 205, inputs := [4, 5], outflow := 0 }
def clawBack : Tx := { id := 206, inputs := [0], outflow := 0 }

/-- `SPN-30`: "A hot-class spend's fire time is `ingress_now + hold_secs`." -/
def fireOf (accepted : Nat) : Nat := accepted + Budget.params.hold
/-- `SPN-10`'s ceiling on a signed expiry, which `ADR-0014` takes at equality. -/
def expiryOf (accepted : Nat) : Nat := accepted + Budget.params.window

/-- The instant the claw-back reaches the mempool, which is the instant it settles, and the
instant `DEF-5`'s second spend arrives. -/
def clawSeen : Nat := 40

def s1 : Cand := cand 1 hot1 true (some (fireOf Budget.timeline.firstAccept))
  (expiryOf Budget.timeline.firstAccept)
def e1 : Cand := cand 2 esc1 false none (expiryOf Budget.timeline.firstAccept)
def s2 : Cand := cand 5 hot2 true (some (fireOf Budget.timeline.secondAccept))
  (expiryOf Budget.timeline.secondAccept)
def e2 : Cand := cand 6 esc2 false none (expiryOf Budget.timeline.secondAccept)
def s3 : Cand := cand 7 hot3 true (some (fireOf clawSeen)) (expiryOf clawSeen)
def e3 : Cand := cand 8 esc3 false none (expiryOf clawSeen)

/-- The chain view each step reads: empty, or holding the claw-back from the instant it arrives.
A claw-back visible before it was broadcast would be a different trace, and under `F57` row 8's
withdrawn reading of defeat it would be one where the first spend was never due. -/
def plain (n : Nat) : Env := envAt n n
def withClaw (n : Nat) : Env := envAt n n (if clawSeen ≤ n then [clawBack] else [])

/-- The run, with each effect stamped with the instant that emitted it. `Wall` has no accessor —
the clock types are opaque outside `Clocks.lean` — and a completion TIME is what `ADR-0014`
counts, so the instant is carried beside the event and the environment is built from it. Wall and
HotClock read the same number here: one node, no excursion, `NCH-41`'s lag not exercised. -/
def timedRun (mk : Nat → Env) (g : Guards) :
    List (Nat × Event) → Sys → Sys × List (Nat × Effect)
  | [], sys => (sys, [])
  | (n, e) :: rest, sys =>
    let stepped := sysStep g cfg Kernel.current (mk n) sys e
    let ran := timedRun mk g rest stepped.1
    (ran.1, (stepped.2.map fun eff => (n, eff)) ++ ran.2)

def steps (mk : Nat → Env) (tr : List (Nat × Event)) : List (Env × Event) :=
  tr.map fun x => (mk x.1, x.2)

/-- Stamping the effects changes no state: the run is `Ledger.sysRun`'s. -/
theorem timedRun_is_sysRun (mk : Nat → Env) (g : Guards) :
    ∀ (tr : List (Nat × Event)) (sys : Sys),
      (timedRun mk g tr sys).1 = (sysRun g cfg Kernel.current sys (steps mk tr)).1 := by
  intro tr
  induction tr with
  | nil => intro sys; rfl
  | cons x rest ih =>
    intro sys
    obtain ⟨n, e⟩ := x
    exact ih _

/-- The outflow a broadcast carried, read from the transactions themselves. -/
def amountOf (txid : Nat) : Nat :=
  ([hot1, esc1, hot2, esc2, hot3, esc3, clawBack].find? (·.id == txid)).elim 0 (·.outflow)

/-- The completions of a run: the instant of every `Effect.broadcast` and the outflow it carried.
`SPN-38`'s queued partial is an exposure, not a completion. -/
def completions (mk : Nat → Env) (g : Guards) (tr : List (Nat × Event)) : List (Nat × Nat) :=
  (timedRun mk g tr sys0).2.filterMap fun x =>
    match x.2 with
    | .broadcast txid => some (x.1, amountOf txid)
    | .queuePartial _ _ _ _ => none

def completedInWindow (start window : Nat) (cs : List (Nat × Nat)) : Nat :=
  ((cs.filter fun c => start ≤ c.1 && c.1 < start + window).map (·.2)).sum

/-! ### `ADR-0014`'s delayed-holder trace -/

/-- The trace, at `Budget.timeline`'s instants. The holder decision arrives at 100, which is why
the first release and its completion are there and not at the Hold; the second acceptance is at
121, the first instant at which both of `POL-19`'s disjuncts are false for the first reservation
(`Budget.reservation_boundary`), so the second acceptance's own check releases it; its `fire_at`
is 141.

`ADR-0014`'s federation is "2-of-3 … with no compromised node", and the partial that completes
each spend beside this node's is a HONEST peer's, delivered: `receivePartial` stores it in the
candidate's held set (`NCH-24`) and records it as exposed authority in the same step, and
`packageAccepted` assembles from the two held partials, this node's own and the peer's. The trace
has no compromised signer. -/
def adr0014 : List (Nat × Event) :=
  [ (Budget.timeline.firstAccept,
      .accept 10 false (Wall.sample (expiryOf Budget.timeline.firstAccept)) s1 e1),
    (Budget.timeline.firstHold, .firePass),
    (Budget.timeline.firstComplete, .receipt 10 1),
    (Budget.timeline.firstComplete, .firePass),
    (Budget.timeline.firstComplete, .receivePartial (sighash hot1 0) 0 2 1),
    (Budget.timeline.firstComplete, .packageAccepted 1),
    (Budget.timeline.firstComplete, .send 1),
    (Budget.timeline.secondAccept,
      .accept 20 false (Wall.sample (expiryOf Budget.timeline.secondAccept)) s2 e2),
    (Budget.timeline.secondComplete, .receipt 20 1),
    (Budget.timeline.secondComplete, .firePass),
    (Budget.timeline.secondComplete, .receivePartial (sighash hot2 0) 0 2 5),
    (Budget.timeline.secondComplete, .packageAccepted 5),
    (Budget.timeline.secondComplete, .send 5) ]

/-- Both spends are admitted and both complete, at the instants `Budget.timeline` records. The
fire pass at the Hold releases nothing and exposes nothing: `DUR-8` withholds the release until
the holder decision, which is what puts the first completion at 100 rather than at 20. -/
@[req "POL-20"]
theorem adr0014_completions :
    (timedRun plain current (adr0014.take 2) sys0).1.world.exposure = [] ∧
    completions plain current adr0014 =
      [(Budget.timeline.firstComplete, V), (Budget.timeline.secondComplete, V)] := by decide

/-- The refutation, existential over that reachable trace: SOME window of length
`hot_window_secs` completes more than `(n / t) × cap`, cleared of its division.
`Budget.exceeds_withdrawn_bound` computes the coefficient; what is new here is that the trace is
run rather than tabulated. -/
@[req "POL-20"]
theorem adr0014_refutes_completion_bound :
    ∃ start, Budget.params.n * V <
      Budget.params.t * completedInWindow start Budget.params.window
        (completions plain current adr0014) :=
  ⟨Budget.intervalStart, by decide⟩

/-- And it hits exactly `2V`, which is `t × cap` at `t = 2`. So the trace refutes the `n / t`
reading and NOT `cap ≤ tolerable per-window loss ÷ t`, which `POL-20` withdraws for its own
reason: "No replacement rolling completion-loss formula is specified." -/
@[req "POL-20"]
theorem adr0014_hits_exactly_t_cap :
    completedInWindow Budget.intervalStart Budget.params.window
        (completions plain current adr0014) = Budget.statedTotalV * V ∧
      Budget.statedTotalV * V = Budget.params.t * V := by decide

/-- The admission bound stands on the same run, which is `POL-20`'s point — "an acceptance-time
admission bound, not a rolling completion-loss bound". Both spends were registered, so both passed
`POL-16` at their own acceptance, and the ledger is under the cap at the end by the invariant
rather than by inspection. -/
@[req "POL-16"]
theorem adr0014_admission_holds :
    (timedRun plain current adr0014 sys0).1.world.node.cands.any (·.id == 1) = true ∧
    (timedRun plain current adr0014 sys0).1.world.node.cands.any (·.id == 5) = true ∧
    liveSum (timedRun plain current adr0014 sys0).1.led ≤ cfg.cap := by
  refine ⟨by decide, by decide, ?_⟩
  rw [timedRun_is_sysRun]
  exact liveSum_le_cap current cfg Kernel.current _ sys0 (by decide)

/-! ### `DEF-5`: the settlement that refunded the reservation -/

/-- `DEF-5`'s settlement refund (`F57`), every other ledger value as it stands. An explicit record,
so a flip of `current` cannot reach it. -/
def withdrawnSettlement : Guards :=
  { settlement := .refundOnAnySettlement, release := .acceptedAdmission, refund := .onCollection }

/-- The claw-back is seen in the mempool and `SPN-33` marks the first spend terminal; its partial
is already out. A second hot spend of the whole cap arrives inside the same window. -/
def def5 : List (Nat × Event) :=
  [ (0, .accept 10 false (Wall.sample (expiryOf 0)) s1 e1),
    (30, .receipt 10 1),
    (30, .firePass),
    (30, .adversaryExposes (sighash hot1 0) 0 2 1),
    (clawSeen, .settle clawBack),
    (clawSeen, .accept 30 false (Wall.sample (expiryOf clawSeen)) s3 e3) ]

/-- As the rule stands: the mempool settlement refunds nothing, the charge is still the first
spend's, and the second spend is refused before signing — nothing of it is registered. The first
spend's authority is out and finalizable all the while, which is why the charge must stay. -/
@[req "SPN-33"]
theorem def5_refused_with_current :
    (timedRun withClaw current def5 sys0).1.led.map (·.cid) = [1] ∧
    (timedRun withClaw current def5 sys0).1.world.node.cands.any (·.id == 7) = false ∧
    exposedQuorum (timedRun withClaw current def5 sys0).1.world s1 = true := by decide

/-- Under the withdrawn value the settlement refunds the reservation of every candidate it
touched — here through the terminal mark `SPN-33` sets on the input-conflicting spend. The first
charge is gone, its exposed authority is not, and the same second spend is now admitted: a second
maximal hot spend accepted inside the window in which the first's partial is out and finalizable,
against a cap of one, with the ledger showing a single charge. `POL-20`'s counting theorem cannot
see this — the refunded reservation leaves its own cohort — which is why the defect is an exhibit
and not a theorem. -/
@[req "SPN-33"]
theorem def5_admitted_with_withdrawn :
    (timedRun withClaw withdrawnSettlement def5 sys0).1.led.map (·.cid) = [7] ∧
    (timedRun withClaw withdrawnSettlement def5 sys0).1.world.node.cands.any (·.id == 7) = true ∧
    exposedQuorum (timedRun withClaw withdrawnSettlement def5 sys0).1.world s1 = true := by decide

/-! ### `F63`: two commitments over one transaction, and the end of both their charges

The history `F63` records, run over the landed ledger's own transitions. The finding owns the
argument; nothing is re-argued here. -/

/-- The twin's acceptance. `CHN-27`: "A changed transaction or expiry gets a fresh commitment and
evaluation", so one re-quoted expiry over the SAME transaction is a second commitment taking its
own charge (`POL-18`, "idempotently per commitment"). No clause fixes WHEN the re-quote arrives;
this sample is the exhibit's own choice, inside the first charge's window and far enough in that
its own window outlives it. -/
def twinAccept : Nat := 60

/-- The twin itself: same transaction, later signed expiry, its own id. -/
def s1Twin : Cand := cand 9 hot1 true (some (fireOf twinAccept)) (expiryOf twinAccept)

/-- The node at the moment the first twin's partial is out and the second's is not. -/
def twinNode : Node := { A with cands := [{ s1 with released := true }, s1Twin] }
/-- The same moment with one commitment only. -/
def soloNode : Node := { A with cands := [{ s1 with released := true }] }

/-- Both charges, `hot_outflow` each, EACH reserved at its own acceptance (`POL-18`: "at
acceptance"), which is what puts the twin's row inside a trailing window the first's has left. -/
def twinLed : Ledger :=
  [row 1 V Budget.timeline.firstAccept (expiryOf Budget.timeline.firstAccept),
   row 9 V twinAccept (expiryOf twinAccept)]
/-- The same history with a single commitment. -/
def soloLed : Ledger :=
  [row 1 V Budget.timeline.firstAccept (expiryOf Budget.timeline.firstAccept)]

/-- The sample at which the first charge is dead on both of `POL-19`'s disjuncts, which
`Budget.reservation_boundary` owns. -/
def deadAt : Env := envOf Budget.timeline.secondAccept Budget.timeline.secondAccept
/-- The prune pass, one sample past the twin's signed expiry and no further: its HotClock is
still inside the twin's trailing window, so no release at that sample could take it. -/
def pruneAt : Env := envOf (expiryOf twinAccept + 1) Budget.timeline.secondAccept

/-- The node that prune pass leaves: both twins are past their signed expiries and neither belongs to
an exempt Escape's pair, so `SPN-41`'s pruning collects both. -/
def prunedNode : Node := prune pruneAt twinNode

/-- Two commitments over one transaction are metered twice — `2V` against a cap of `V` — and the
two charges then leave by different doors. `markExposed` sets the released twin's bit; at
`deadAt`, a hot admission's check, both of `POL-19`'s disjuncts are dead for that row and it is
released, while the twin survives on its own later reservation; at `pruneAt` a release STILL could
not take the twin, and it is the prune pass that collects it, its wall sample past the twin's
expiry, which refunds it (`POL-18`: "a reservation is refundable exactly when it is unexposed, its
signed expiry has strictly passed on the wall sample `POL-19`'s expiry disjunct reads, and its
candidate is no longer resident"). The fifth conjunct is what makes the prune pass load-bearing rather
than decorative: a release at the prune pass's own sample leaves the charge standing. The sixth and
seventh are the collection: against the node before the prune pass, where the twin is resident, nothing
is refunded; the prune pass leaves no candidate; against the node it leaves, the twin's charge is
refunded.

The single-commitment history reaches the same empty ledger without the prune pass at all, which is
`F63`'s point that the refund reaches no state the release would not have reached alone. -/
@[req "POL-18"]
theorem f63_twins_end_charging_nothing :
    liveSum (markExposed twinNode twinLed) = 2 * V ∧
    (markExposed twinNode twinLed).map (·.exposed) = [true, false] ∧
    liveSum (ageOut deadAt cfg.window (markExposed twinNode twinLed)) = V ∧
    (ageOut deadAt cfg.window (markExposed twinNode twinLed)).map (·.cid) = [9] ∧
    liveSum (ageOut pruneAt cfg.window
      (ageOut deadAt cfg.window (markExposed twinNode twinLed))) = V ∧
    liveSum (refundAtPrune Ledger.current.refund pruneAt twinNode
      (ageOut deadAt cfg.window (markExposed twinNode twinLed))) = V ∧
    prunedNode.cands = [] ∧
    liveSum (refundAtPrune Ledger.current.refund pruneAt prunedNode
      (ageOut deadAt cfg.window (markExposed twinNode twinLed))) = 0 ∧
    liveSum (ageOut deadAt cfg.window (markExposed soloNode soloLed)) = 0 := by
  decide

/-- The exposure the emptied ledger no longer prices: 2-of-3 with two distinct signers on the
transaction's input 0. `POL-20` states the residual — "Already exposed signatures also remain
valid after their reservations age out" — and `exposedQuorum` keys on `(sighash, input, signer)`,
so it does not read a commitment id and no charge was ever what held this. -/
def twinExposure : World :=
  { node := A,
    exposure := [{ msg := sighash hot1 0, input := 0, signer := 0, cid := 1, hot := true },
                 { msg := sighash hot1 0, input := 0, signer := 1, cid := 1, hot := true }] }

@[req "POL-20"]
theorem f63_exposure_outlives_the_charges : exposedQuorum twinExposure s1 = true := by decide

/-! ### `F62`: the release is one way, at an accepted hot admission, and the refund waits for
collection

The traces below run over `s1`, a spend of the whole cap accepted at wall and HotClock 0, with
`fire_at` 20 and its signed expiry at 120, opened by its holder decision. In each, a sample past both of
`POL-19`'s disjuncts for its charge is followed by a backward wall step to 50 while the HotClock
keeps moving, so `POL-19`'s wall disjunct holds the charge again. Wall and HotClock are sampled
apart, so these runs are `Ledger.sysRun`'s own. Each says which way it is closed: the second spend
of the whole cap is refused, or no candidate releases a partial while its commitment has no row. -/

/-- The release at every composed step, the requirement as it stood before 2026-10-09. An explicit
record, so a flip of `current` cannot reach it. -/
def withdrawnRelease : Guards :=
  { settlement := .retainOnMempool, release := .everyStep, refund := .onCollection }
/-- The refund at the prune pass after expiry whether or not the candidate is resident, the requirement
as it stood before 2026-10-09. -/
def withdrawnRefund : Guards :=
  { settlement := .retainOnMempool, release := .acceptedAdmission, refund := .atExpiry }

def runAt (g : Guards) (tr : List (Env × Event)) : Sys × List Effect :=
  sysRun g cfg Kernel.current sys0 tr

/-- The second spend of the whole cap, requested after the backward step. -/
def late : Cand := cand 5 hot2 true (some 70) 170
def lateEsc : Cand := cand 6 esc2 false none 170

/-- `s1` accepted, and opened by its holder decision at 10. -/
def opened : List (Env × Event) :=
  [ (envAt 0 0, .accept 10 false (Wall.sample (expiryOf 0)) s1 e1),
    (envAt 10 10, .receipt 10 1) ]

/-- After the step back to wall 50: the second spend, then a fire pass, at which `s1`'s window is
open on the effective sample and the time ratchet alike. -/
def afterBack : List (Env × Event) :=
  [ (envAt 50 122, .accept 20 false (Wall.sample 170) late lateEsc),
    (envAt 50 122, .firePass) ]

/-- `s1`'s partial, queued for transport. -/
def s1Partial : Effect := .queuePartial (sighash hot1 0) 0 true 1

/-- **The uncharged fire**: a tick at wall and HotClock 121, then the step back. -/
def unchargedFire : List (Env × Event) := opened ++ [(envAt 121 121, .tick)] ++ afterBack

/-- Closed as the release point stands, by the refusal: the tick releases nothing, the second
spend's check finds `s1`'s charge live again on the wall, and the spend is refused before signing;
`s1`'s release that follows is charged. -/
@[req "POL-19"]
theorem uncharged_fire_closed_with_current :
    (runAt Ledger.current unchargedFire).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current unchargedFire).1.world.node.cands.any (·.id == 5) = false ∧
    (runAt Ledger.current unchargedFire).2 = [s1Partial] := by decide

/-- Red under the release at every step: the tick released the charge, the second spend of the
whole cap is admitted against the emptied ledger, and `s1` releases its partial with no row. -/
@[req "POL-19"]
theorem uncharged_fire_with_withdrawn :
    (runAt withdrawnRelease unchargedFire).1.led.map (·.cid) = [5] ∧
    (runAt withdrawnRelease unchargedFire).1.world.node.cands.any (·.id == 5) = true ∧
    (runAt withdrawnRelease unchargedFire).2 = [s1Partial] := by decide

/-- A request on `s1`'s retired nonce: its check passes the budget once `s1`'s charge is released,
and the kernel refuses it (`NCH-40`'s tombstone). -/
def replayed : Cand := cand 7 hot3 true (some 141) 241
def replayedEsc : Cand := cand 8 esc3 false none 241

/-- **The refused admission**: that request at wall and HotClock 121, then the step back. -/
def refusedAdmission : List (Env × Event) :=
  opened ++ [(envAt 121 121, .accept 10 false (Wall.sample 241) replayed replayedEsc)] ++ afterBack

/-- A hot spend over the whole cap: its check releases `s1`'s charge, and the budget still refuses
it (`POL-16`). -/
def overCap : Cand := cand 7 { id := 207, inputs := [6], outflow := V + 1 } true (some 141) 241
def overCapEsc : Cand := cand 8 { id := 208, inputs := [6, 7], outflow := 0 } false none 241

/-- **The budget-refused admission**: that request at wall and HotClock 121, then the step back. -/
def budgetRefusedAdmission : List (Env × Event) :=
  opened ++ [(envAt 121 121, .accept 30 false (Wall.sample 241) overCap overCapEsc)] ++ afterBack

/-- Closed as the release point stands, by the refusal, whichever refuses: the kernel's tombstone
or the budget. The refused request persists nothing (`SPN-14`: "A refused request MUST mutate
nothing"), so the second spend is refused as in the uncharged-fire trace. -/
@[req "POL-19"]
theorem refused_admission_closed_with_current :
    (runAt Ledger.current refusedAdmission).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current refusedAdmission).1.world.node.cands.any (fun c => c.id == 5 || c.id == 7)
      = false ∧
    (runAt Ledger.current refusedAdmission).2 = [s1Partial] ∧
    (runAt Ledger.current budgetRefusedAdmission).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current budgetRefusedAdmission).1.world.node.cands.any
      (fun c => c.id == 5 || c.id == 7) = false ∧
    (runAt Ledger.current budgetRefusedAdmission).2 = [s1Partial] := by decide

/-- **The refund exemption**: `s1`'s holder decision lands late, at 110, and installs its Escape's
window `[110, 210]` past `s1`'s expiry under the normal PIN (`DUR-20`); the prune pass at wall and
HotClock 121 finds `s1` expired and keeps it as the exempt Escape's pair (`SPN-41`); then the step
back. -/
def refundExemption : List (Env × Event) :=
  [ (envAt 0 0, .accept 10 false (Wall.sample (expiryOf 0)) s1 e1),
    (envAt 110 110, .receipt 10 1),
    (envAt 121 121, .prune) ] ++ afterBack

/-- Closed as the refund point stands, by the refusal: the prune pass kept the pair, so it refunded
nothing, and the spend is not refunded while it is resident (`POL-18`: "never while the candidate
is resident"). -/
@[req "POL-18"]
theorem refund_exemption_closed_with_current :
    (runAt Ledger.current (refundExemption.take 3)).1.world.node.cands.map (·.id) = [1, 2] ∧
    (runAt Ledger.current refundExemption).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current refundExemption).1.world.node.cands.any (·.id == 5) = false ∧
    (runAt Ledger.current refundExemption).2 = [s1Partial] := by decide

/-- Red under the refund at expiry: the prune pass refunded the resident spend's charge, the second
spend of the whole cap is admitted, and `s1` releases its partial with no row. -/
@[req "POL-18"]
theorem refund_exemption_with_withdrawn :
    (runAt withdrawnRefund refundExemption).1.led.map (·.cid) = [5] ∧
    (runAt withdrawnRefund refundExemption).1.world.node.cands.any (·.id == 5) = true ∧
    (runAt withdrawnRefund refundExemption).2 = [s1Partial] := by decide

/-- A second spend of the whole cap accepted at wall and HotClock 121, where its check releases
`s1`'s charge. -/
def next : Cand := cand 5 hot2 true (some 141) 241
def nextEsc : Cand := cand 6 esc2 false none 241
def releaseStep : Event := .accept 20 false (Wall.sample 241) next nextEsc

def openedSys : Sys := (runAt Ledger.current opened).1
/-- The state the release leaves. -/
def released : Sys := (sysStep Ledger.current cfg Kernel.current (envAt 121 121) openedSys releaseStep).1

/-- **The release at an accepted admission**, then the step back and a fire pass. -/
def releasedAtAdmission : List (Env × Event) :=
  opened ++ [(envAt 121 121, releaseStep), (envAt 50 122, .firePass)]

/-- Closed as the release point stands, with no candidate releasing uncharged: the acceptance that
released `s1`'s charge advanced the time ratchet to 121, `s1` is still resident, and after the step
back its window's close, 120, is below the ratchet, so the fire pass releases nothing. -/
@[req "POL-19"]
theorem release_at_admission_shuts_window :
    (runAt Ledger.current releasedAtAdmission).1.led.map (·.cid) = [5] ∧
    (runAt Ledger.current releasedAtAdmission).1.world.node.cands.any (·.id == 1) = true ∧
    (runAt Ledger.current releasedAtAdmission).2 = [] := by decide

/-- And at every sample from then on, for `s1` as it is resident in the state the release leaves
and through any later trace: the acceptance left the ratchet at 121, past `s1`'s expiry, no later
step lowers it (`Ledger.sysRun_ratchet_never_lowered`), and a hot window read at the ratchet is
closed (`Kernel.never_due_below_ratchet`). `Ledger.released_never_due` is the same argument over
every release. The proof takes the close's value and no other guard's. -/
@[req "POL-19"]
theorem release_at_admission_never_due (tr : List (Env × Event)) (env' : Env) (c : Cand)
    (hc : c ∈ released.world.node.cands) (hid : c.id = 1) :
    due Kernel.current env' (sysRun Ledger.current cfg Kernel.current released tr).1.world.node c
      = false := by
  have hshape : ∀ x ∈ released.world.node.cands, x.id = 1 →
      x.hot = true ∧ x.windowClose = none ∧ x.expiry = Wall.sample 120 := by decide
  obtain ⟨hhot, hwc, hexp⟩ := hshape c hc hid
  have hpast : released.world.node.ratchet.atOrBefore (Wall.sample 120) = false := by decide
  have hbelow := Effective.not_atOrBefore_weaken hpast
    (sysRun_ratchet_never_lowered Ledger.current cfg Kernel.current tr released)
  refine never_due_below_ratchet rfl hhot ?_ env'
  simp [windowOpen, hwc, hexp, hbelow]

/-! ### `POL-20`: one node's count at the end of its composed run -/

/-- The composed per-node count with the ledger guards as they stand; all run premises remain. -/
@[req "POL-20"]
theorem countsAt_of_sysRun_with_current (cfg : Config) (r : Rules) (sys : Sys)
    (pre : List (Env × Event)) (last : Env × Event)
    (hm : MonotoneHotClock (pre ++ [last]))
    (a b : List (Env × Event)) (envR : Env) (cid : Nat) (d : Bool) (E : Wall) (sp es : Cand)
    (hsplit : pre ++ [last] = a ++ (envR, .accept cid d E sp es) :: b)
    (ha : admitted (sysRun Ledger.current cfg r sys a).1.world
      (sysStep Ledger.current cfg r envR (sysRun Ledger.current cfg r sys a).1 (.accept cid d E sp es)).1.world
      (.accept cid d E sp es) = true)
    (hfresh : holds (checked Ledger.current.release envR cfg.window (sysRun Ledger.current cfg r sys a).1.led
      (.accept cid d E sp es)) sp.id = false)
    (hwin : Mono.withinWindow envR.mono last.1.mono cfg.window = true)
    (hprune : pruneKeeps Ledger.current cfg r sp.id envR.mono sys (pre ++ [last]) = true) :
    countsAt cfg.window sp.id
      { led := (sysRun Ledger.current cfg r sys (pre ++ [last])).1.led, now := last.1.mono } = true := by
  exact countsAt_of_sysRun Ledger.current rfl rfl cfg r sys pre last hm a b envR cid d E sp es
    hsplit ha hfresh hwin hprune

/-- Two hot spends fit together under this cap. -/
def cohortCfg : Config := { cfg with cap := 2 * V }
def cohortNext : Cand := cand 5 hot2 true (some 30) 130
def cohortNextEsc : Cand := cand 6 esc2 false none 130

def cohortPre : List (Env × Event) :=
  [(envAt 0 0, .accept 10 false (Wall.sample 120) s1 e1)]
def cohortLast : Env × Event :=
  (envAt 10 10, .accept 20 false (Wall.sample 130) cohortNext cohortNextEsc)

/-- The first reservation is still counted after a later accepted hot admission's release check.
Both reservation samples lie inside the final sample's trailing interval. -/
@[req "POL-20"]
theorem composed_reservation_counted_with_current :
    countsAt cohortCfg.window s1.id
      { led := (sysRun Ledger.current cohortCfg Kernel.current sys0 (cohortPre ++ [cohortLast])).1.led,
        now := cohortLast.1.mono } = true ∧
    holds (sysRun Ledger.current cohortCfg Kernel.current sys0 (cohortPre ++ [cohortLast])).1.led
      cohortNext.id = true := by
  decide

/-! ### `POL-20`: a counted row keeps its own reservation time

`composed_reservation_counted_with_current` checks 10 seconds after the first reservation, with
nothing in between. The run below adds a peer's relay that runs the holder decision, a fire pass
that exposes the row, a replay of the same pair under a fresh Carrier, and a wall excursion past
the row's signed expiry and back, with a prune pass at its peak that collects the pair while the
row stays. Its last check runs at exactly the reservation time plus the
window, with the wall past that expiry: only the monotonic disjunct, at its inclusive boundary,
keeps the row (`POL-19`: "a reservation is released when both disjuncts are false"). -/

/-- The first hot spend, fire time 30 and signed expiry 130, and its Escape, accepted at wall and
HotClock 10. -/
def keptSp : Cand := cand 1 hot1 true (some 30) 130
def keptEsc : Cand := cand 2 esc1 false none 130
def keptEnvR : Env := envAt 10 10
def keptAccept : Event := .accept 10 false (Wall.sample 130) keptSp keptEsc

/-- The relay that runs the holder decision at 20, the fire pass at 30, the same pair replayed
under Carrier 20 at 40, the prune pass that collects the pair at wall 500 and HotClock 60, and the
wall back at 50 with HotClock 70. -/
def keptMid : List (Env × Event) :=
  [ (envAt 20 20, .receipt 10 1),
    (envAt 30 30, .firePass),
    (envAt 40 40, .accept 20 false (Wall.sample 150) keptSp keptEsc),
    (envAt 500 60, .prune),
    (envAt 50 70, .tick) ]
def keptPre : List (Env × Event) := (keptEnvR, keptAccept) :: keptMid

/-- The second spend accepted at wall 131 and HotClock 130 = 10 + 120. -/
def keptLast : Env × Event := (envAt 131 130, .accept 30 false (Wall.sample 241) next nextEsc)
def keptRun : Sys :=
  (sysRun Ledger.current cohortCfg Kernel.current sys0 (keptPre ++ [keptLast])).1

/-- At the last check the first row has its commitment, its original reservation time, its signed
expiry and its exposure bit set, and it is counted (`POL-18`: "a retry keeps the original
reservation time"; `SPN-33`: "the ledger retains its original reservation time, expiry and
exposure state independently of candidate residency"). -/
@[req "POL-20"]
theorem composed_row_time_kept_with_current :
    keptRun.led.map (fun r => (r.cid, r.reservedAt, r.expiry, r.exposed)) =
      [(1, Mono.sample 10, Wall.sample 130, true), (5, Mono.sample 130, Wall.sample 241, false)] ∧
    countsAt cohortCfg.window keptSp.id { led := keptRun.led, now := keptLast.1.mono } = true := by
  decide

/-- `countsAt_of_sysRun_with_current` applies to this run: its premises hold across the exposure, the
replay, the prune pass and the wall excursion. -/
@[req "POL-20"]
theorem composed_row_counted_by_theorem_with_current :
    countsAt cohortCfg.window keptSp.id { led := keptRun.led, now := keptLast.1.mono } = true :=
  countsAt_of_sysRun_with_current cohortCfg Kernel.current sys0 keptPre keptLast
    (by simp only [keptPre, keptMid, keptLast, List.cons_append, List.nil_append,
      MonotoneHotClock]; decide)
    [] (keptMid ++ [keptLast]) keptEnvR 10 false (Wall.sample 130) keptSp keptEsc rfl
    (by decide) (by decide) (by decide) (by decide)

/-! ### `POL-21`: a frozen candidate's refund, at the prune pass that collects it

Through the composed step, not a ledger function called on a node pruned by hand. -/

/-- `s1` accepted at 0 under duress, so its holder decision at 10 arms the node and freezes it
(`DUR-11`); then the prune pass at wall and HotClock 121, past `s1`'s signed expiry of 120 and
its Escape's window. -/
def frozenPrune : List (Env × Event) :=
  [ (envAt 0 0, .accept 10 true (Wall.sample (expiryOf 0)) s1 e1),
    (envAt 10 10, .receipt 10 1),
    (envAt 121 121, .prune) ]

/-- `POL-21`: "the frozen candidate's reservation is refunded at `SPN-41`'s prune pass that
collects it". The freeze leaves the charge standing; the prune pass at 121 collects `s1` and its Escape, and the
same composed step refunds the charge. A refund that waited for a later prune pass would leave it. -/
@[req "POL-21"]
theorem frozen_charge_refunded_at_collecting_prune :
    (runAt Ledger.current (frozenPrune.take 2)).1.world.node.cands.any
      (fun c => c.id == 1 && c.frozen) = true ∧
    (runAt Ledger.current (frozenPrune.take 2)).1.led.map (·.cid) = [1] ∧
    (runAt Ledger.current frozenPrune).1.world.node.cands = [] ∧
    (runAt Ledger.current frozenPrune).1.led = [] := by decide

end BtcPolicy.Exhibits.HotLedger

namespace BtcPolicy.Exhibits.TwoRun
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt withdrawnTraversal withdrawnDynamics)

/-! ## SILENCE as a two-run relation: `DEF-12`'s marker, `F54`'s conditional traversal, `DUR-14`'s
static `T`, and the horizon itself

One request body under two enrolment tables (`Silence.Enrolment`): the same bytes, the same
delivery, the same chain view and the same samples, and only the class the table gives the
presented PIN differs. The workflow attributes each guard-parameter flip to the declarations it
refutes; the full-prefix exhibits also check coverage of the observation walk. -/

/-- 2-of-3, `duress_delay_secs` 200, `epsilon_secs` 5, `combine_slack_secs` 40, `hold_secs` 0.
Each spend here is handed its `fire_at` directly, and the HotClock check of `SPN-38` is
`BtcPolicy.Exhibits.HotClockHold`'s subject. `OPS-13` says "`hold_secs` has no positive lower
bound", and 0 leaves the check satisfied by every acceptance. -/
def A : Node :=
  { id := 0, t := 2, armed := false, poisoned := false, lockedDown := false, carriers := [],
    cands := [], T := Wall.sample 0, sweepActive := false, selected := [], duressDelay := 200,
    epsilon := 5, combineSlack := 40, holdSecs := 0 }

def sys0 : Sys := { world := { node := A, exposure := [] }, led := [] }
def cfg : Config := { cap := 1000, window := 120 }

/-- The two enrolments: PIN 1 is the duress PIN under the first table and an ordinary PIN under
the second. The request bytes are the same in both worlds; the table is the secret. -/
def tblD : Enrolment := fun p => p == 1
def tblN : Enrolment := fun _ => false

def hot1 : Tx := { id := 100, inputs := [0], outflow := 10 }
def esc1 : Tx := { id := 101, inputs := [0, 1], outflow := 0 }
def hot2 : Tx := { id := 102, inputs := [2], outflow := 10 }
def esc2 : Tx := { id := 103, inputs := [2, 3], outflow := 0 }

def s1 : Cand := cand 1 hot1 true (some 300) 400
def e1 : Cand := cand 2 esc1 false none 400
/-- A hot spend whose `fire_at` is 100, well before the `T` the arm wrote. -/
def s2 : Cand := cand 5 hot2 true (some 100) 400
def e2 : Cand := cand 6 esc2 false none 400

/-- Ingress at 50 under the PIN the first table makes a duress PIN, and the relay that reaches
`t` at 60: the holder decision writes `T = max(min(50 + 200, 300 − 5), 60) = 250` in the first
world, whose start is the duress intent's own `first_seen`, and `max(min(60 + 200, 300 − 5), 60) =
260` in the other, where no record's duress bit is set and the start is the seed `max(ratchet,
now) = 60` (`DUR-13`). It arms only the first world. -/
def armTrace : List (Env × Input) :=
  [ (envAt 50 50, .request 10 1 (Wall.sample 400) s1 e1),
    (envAt 60 60, .pinless (.receipt 10 1)) ]

/-- And a second hot spend accepted at 70, after the arm. -/
def hotTrace : List (Env × Input) :=
  armTrace ++ [ (envAt 70 70, .request 20 0 (Wall.sample 400) s2 e2) ]

def runOf (r : Rules) (tbl : Enrolment) (tr : List (Env × Input)) : Sys :=
  (sysRun Ledger.current cfg r sys0 (tr.map fun x => (x.1, x.2.event tbl))).1

def pairs (g : Silence.Marker) (r : Rules) (tr : List (Env × Input)) : List (Obs × Obs) :=
  obsPair g Ledger.current cfg r tblD tblN sys0 sys0 tr

/-! ### The relation over the values as they stand -/

/-- `BtcPolicy.Silence.silence` instantiated at the guard parameters as they stand: `DEF-12`'s
marker keyed on `DUR-5`'s pin-uniform condition, `DUR-20`'s unconditional traversal and `DUR-14`'s
dynamic `T`, with `SPN-32`'s preserving registration, and `DUR-7`'s time ratchet read by the hot
close and by the driver at `max(ratchet, effective)`. Every guard-parameter hypothesis is
discharged here; the workflow holds each flip to its measured failures. No premise is taken on
the trace's samples: they may step backward anywhere. -/
@[req "DUR-1"]
theorem silence_with_current {gs : Guards} (tbl₀ tbl₁ : Enrolment)
    (tr : List (Env × Input)) (a b : Sys) (hc : Coupled Kernel.current a b)
    (hia : NodeInv Kernel.current a.world.node a.world.node.ratchet)
    (hib : NodeInv Kernel.current b.world.node b.world.node.ratchet) :
    ∀ y ∈ obsPair Silence.current gs cfg Kernel.current tbl₀ tbl₁ a b tr, y.1 = y.2 :=
  silence rfl rfl rfl rfl rfl rfl tbl₀ tbl₁ tr a b hc hia hib

/-- The invariant the relation takes, at the state both runs start from: no candidate, no Carrier,
unarmed, with duplicate-free resident ids and `DUR-10`'s two flags agreeing. The other
clauses are vacuous on the empty candidate list. -/
theorem nodeInv_A (now : Effective) : NodeInv Kernel.current A now := nodeInv_initial A now rfl rfl rfl rfl

/-! ### Why `NodeInv` carries `unarmed` (`SPN-41`'s exemption)

`SPN-41`'s exemption keeps an expired Escape and its pair while the Escape's window
`[T, T + combine_slack_secs]` has not closed, and each run's window closes at its own `T`, which
the projection erases. Two coupled states satisfying every other clause of `NodeInv`, unarmed but
with `T` away from `Node.unarmedT`, fall out of step at a prune pass, and a request on the same ids is
then accepted in one run and refused in the other. The `unarmed` clause is what excludes them;
every reachable state satisfies it (`inv_sysStep`) and so does the state every exhibit starts
from (`nodeInv_A`). -/

def tSpend : Cand := { cand 1 hot1 false none 120 with pair := some (1, 2) }
def tEsc (T : Nat) : Cand :=
  { cand 2 esc1 false (some T) 120 with pair := some (1, 2), windowClose := some (Wall.sample (T + 40)) }
/-- An unarmed node holding the pair, its Escape selected with the window its own `T` wrote. -/
def tNode (T : Nat) : Node := { A with selected := [(2, false)], T := Wall.sample T, cands := [tSpend, tEsc T] }
def tSys (T : Nat) : Sys := { world := { node := tNode T, exposure := [] }, led := [] }

/-- A prune pass at wall 150, where the window closes at 140 in one run and 240 in the other, then a
request over another transaction on the same ids. -/
def tTrace : List (Env × Input) :=
  [ (envAt 150 150, .pinless .prune),
    (envAt 150 150, .request 11 0 (Wall.sample 300) (cand 1 hot2 true (some 170) 300)
      (cand 2 esc2 false none 300)) ]

/-- The two states are coupled and satisfy every clause of `NodeInv` but `unarmed`, which fails
in both; the walk emits an unequal pair at the second step, `accepted` where the prune pass collected
the pair and `PSBT_INCONSISTENT` where it kept it. -/
@[req "SPN-41"]
theorem silence_needs_unarmed :
    pubNode Kernel.current (tSys 100).world.node = pubNode Kernel.current (tSys 200).world.node ∧
    (tSys 100).world.exposure = (tSys 200).world.exposure ∧ (tSys 100).led = (tSys 200).led ∧
    (∀ T ∈ [100, 200],
      (tNode T).sweepActive = (tNode T).armed ∧ (tNode T).armed = false ∧
      (tNode T).cands.all (fun c => !c.frozen && !c.quorum && !c.hot) = true ∧
      (tNode T).cands.all (fun c => inSel (selIds (tNode T)) c.id ||
        c.windowClose == none) = true ∧
      (tNode T).cands.all (fun c => !inSel (selIds (tNode T)) c.id ||
        c.windowClose == some ((tNode T).T.plus (tNode T).combineSlack)) = true ∧
      ((tNode T).cands.map Cand.id).Nodup ∧
      (tNode T).T ≠ (tNode T).unarmedT) ∧
    (obsPair Silence.current Ledger.current cfg Kernel.current tblN tblN (tSys 100) (tSys 200)
      tTrace).map (fun y => (y.1.resp, y.2.resp)) =
      [(.silent, .silent),
       (.accepted 1 (envAt 150 150).eff (some (Wall.sample 170)), .refused .PSBT_INCONSISTENT)] := by
  decide

/-- And the relation applied: every hypothesis discharged at a concrete pair of runs, so the
theorem is known to say something about the traces the exhibits below compute. -/
@[req "DUR-1"]
theorem silence_on_armTrace :
    ∀ y ∈ pairs Silence.current Kernel.current armTrace, y.1 = y.2 :=
  silence_with_current tblD tblN armTrace sys0 sys0 (coupled_refl _) (nodeInv_A _) (nodeInv_A _)

/-! ### Resubmissions after selection

`SPN-23` says an accepted repeat "re-applies its schedule, records its own intent (`DUR-4`),
and re-stages". These traces exercise that ingress and its later holder decision through
`Ledger.sysStep` and `obsPair`, including selection before a pair has any resident candidate. -/

/-- The original repeat: fresh nonce, ordinary PIN in both enrolments, then a fire pass. -/
def resubTrace : List (Env × Input) :=
  armTrace ++ [(envAt 70 70, .request 11 0 (Wall.sample 400) s1 e1),
               (envAt 80 80, .pinless .firePass)]

/-- Same-PIN and cross-PIN repeats, each including the repeated Carrier's holder decision. -/
def repeatTrace (samePin : Bool) : List (Env × Input) :=
  armTrace ++ [(envAt 70 70, .request 11 (if samePin then 1 else 0) (Wall.sample 400) s1 e1),
               (envAt 80 80, .pinless .firePass),
               (envAt 90 90, .pinless (.receipt 11 1)),
               (envAt 100 100, .pinless .firePass)]

/-- A bound refusal selects an absent pair, then a fresh nonce accepts it. The non-hot variant
also exercises registration without a hot traversal: it is selected but closed until receipt. -/
def refusedRepeatTrace (samePin hot : Bool) : List (Env × Input) :=
  let sp := { s1 with hot := hot }
  [(envAt 50 50, .refusal 10 1 (Wall.sample 400) (some (s1.id, e1.id))),
   (envAt 60 60, .pinless (.receipt 10 1)),
   (envAt 70 70, .request 11 (if samePin then 1 else 0) (Wall.sample 400) sp e1),
   (envAt 80 80, .pinless .firePass),
   (envAt 90 90, .pinless (.receipt 11 1)),
   (envAt 100 100, .pinless .firePass)]

/-- Fill the Hot ledger, refuse a different pair, and accept the pair selected by the refused
Carrier once its check can release the filling charge. No alternate evaluator or initial ledger is
supplied. The filling spend meets `SPN-30`'s "`expiry ≥ fire_at + combine_slack_secs`, equality passing" at `10 + 40 =
50`, and its expiry is below the holder decision at 60, so `DUR-13`'s scan leaves it out. -/
def budgetRepeatTrace : List (Env × Input) :=
  [(envAt 1 1, .request 20 0 (Wall.sample 50)
      (cand 5 { id := 102, inputs := [2], outflow := 995 } true (some 10) 50)
      (cand 6 esc2 false none 50)),
   (envAt 50 50, .request 10 1 (Wall.sample 400) s1 e1),
   (envAt 60 60, .pinless (.receipt 10 1)),
   (envAt 130 130, .request 11 0 (Wall.sample 400) s1 e1),
   (envAt 140 140, .pinless (.receipt 11 1)),
   (envAt 150 150, .pinless .firePass)]

/-- Check each entering state by replaying its proper prefix through the composed transition.
This checks the horizon only; observation coverage is asserted independently below. -/
def allPreHorizon (r : Rules) (tbl : Enrolment) (tr : List (Env × Input)) : Bool :=
  tr.zipIdx.all fun ((env, _), j) => preHorizon r env (runOf r tbl (tr.take j)).world.node

def fullSilent (g : Marker) (r : Rules) (tr : List (Env × Input)) : Prop :=
  (pairs g r tr).length = tr.length ∧
  allPreHorizon r tblD tr = true ∧ allPreHorizon r tblN tr = true ∧
  (pairs g r tr).all (fun y => y.1 == y.2) = true

instance (g : Marker) (r : Rules) (tr : List (Env × Input)) : Decidable (fullSilent g r tr) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- General equality, with the initial invariant and coupling premises discharged. -/
@[req "DUR-1"]
theorem silence_on_resubTrace :
    ∀ y ∈ pairs Silence.current Kernel.current resubTrace, y.1 = y.2 :=
  silence_with_current tblD tblN resubTrace sys0 sys0 (coupled_refl _) (nodeInv_A _) (nodeInv_A _)

@[req "DUR-1"]
theorem silence_on_repeatTrace (samePin : Bool) :
    ∀ y ∈ pairs Silence.current Kernel.current (repeatTrace samePin), y.1 = y.2 :=
  silence_with_current tblD tblN (repeatTrace samePin) sys0 sys0 (coupled_refl _)
    (nodeInv_A _) (nodeInv_A _)

@[req "DUR-1"]
theorem silence_on_refusedRepeatTrace (samePin hot : Bool) :
    ∀ y ∈ pairs Silence.current Kernel.current (refusedRepeatTrace samePin hot), y.1 = y.2 :=
  silence_with_current tblD tblN (refusedRepeatTrace samePin hot) sys0 sys0 (coupled_refl _)
    (nodeInv_A _) (nodeInv_A _)

@[req "DUR-1"]
theorem silence_on_budgetRepeatTrace :
    ∀ y ∈ pairs Silence.current Kernel.current budgetRepeatTrace, y.1 = y.2 :=
  silence_with_current tblD tblN budgetRepeatTrace sys0 sys0 (coupled_refl _)
    (nodeInv_A _) (nodeInv_A _)

/-- Full lengths, both entering-state horizons, and equality of every computed observation.
The general theorems above and these computations refer to the same `obsPair` lists. -/
@[req "DUR-1"]
theorem resubmissions_full_prefix :
    fullSilent Silence.current Kernel.current resubTrace ∧
    (∀ samePin : Bool, fullSilent Silence.current Kernel.current (repeatTrace samePin)) ∧
    (∀ samePin hot : Bool,
      fullSilent Silence.current Kernel.current (refusedRepeatTrace samePin hot)) ∧
    fullSilent Silence.current Kernel.current budgetRepeatTrace := by
  decide +kernel

/-- A repeat actually accepts and re-stages, preserving the already-open residents verbatim.
Its own holder decision then retires the new Carrier. `SPN-32`: "an already resident compatible
pair is left exactly as is". -/
@[req "SPN-23"]
theorem repeat_keeps_residents :
    ∀ samePin : Bool, ∀ tbl ∈ [tblD, tblN],
    let tr := repeatTrace samePin
    let before := runOf Kernel.current tbl (tr.take 2)
    let after := runOf Kernel.current tbl (tr.take 3)
    let decided := runOf Kernel.current tbl (tr.take 5)
    after.world.node.cands = before.world.node.cands ∧
    after.world.node.carriers.any (fun k => k.cid == 11 && k.accepted && k.mayOpen) = true ∧
    decided.world.node.carriers.any (·.cid == 11) = false ∧
    decided.world.node.tombstones.any (·.cid == 11) = true := by
  intro samePin
  simp only [List.mem_cons, forall_eq_or_imp]
  cases samePin <;> decide +kernel

/-- The two enrolments really differ after the refused holder decision. It selected the absent
Escape and opened nothing; acceptance creates closed residents and the later receipt opens them.
`DUR-5`: "A refused Carrier MUST NOT open any candidate". -/
@[req "DUR-5"]
theorem refused_repeat_selects_before_residency :
    ∀ samePin hot : Bool,
    let tr := refusedRepeatTrace samePin hot
    let before := runOf Kernel.current tblD (tr.take 2)
    let normal := runOf Kernel.current tblN (tr.take 2)
    before.world.node.cands = [] ∧ normal.world.node.cands = [] ∧
    before.world.node.selected = [(e1.id, true)] ∧
    normal.world.node.selected = [(e1.id, false)] ∧
    before.world.node.armed = true ∧ normal.world.node.armed = false ∧
    (∀ tbl ∈ [tblD, tblN],
      (runOf Kernel.current tbl (tr.take 1)).world.node.carriers.any
        (fun k => k.cid == 10 && !k.accepted && !k.mayOpen) = true ∧
      (runOf Kernel.current tbl (tr.take 3)).world.node.cands.map (fun c => (c.id, c.quorum))
        = [(s1.id, false), (e1.id, false)] ∧
      (runOf Kernel.current tbl (tr.take 5)).world.node.cands.map (fun c => (c.id, c.quorum))
        = [(s1.id, true), (e1.id, true)]) := by
  intro samePin hot
  simp only [List.mem_cons, forall_eq_or_imp]
  cases samePin <;> cases hot <;> decide +kernel

/-- The composed refusal really takes the budget path, places no reservation for the absent
pair, and stages a closed Carrier. Later, the request's own admission check releases the earlier
charge (`POL-19`), which permits acceptance and its own holder decision. -/
@[req "POL-16"]
theorem budget_refusal_then_acceptance :
    (∀ tbl ∈ [tblD, tblN],
      let refused := runOf Kernel.current tbl (budgetRepeatTrace.take 2)
      let selected := runOf Kernel.current tbl (budgetRepeatTrace.take 3)
      let accepted := runOf Kernel.current tbl (budgetRepeatTrace.take 4)
      let opened := runOf Kernel.current tbl (budgetRepeatTrace.take 5)
      respond Kernel.current cfg (envAt 50 50)
        (runOf Kernel.current tbl (budgetRepeatTrace.take 1))
        (.accept 10 (tbl 1) (Wall.sample 400) s1 e1) = .refused .HOT_VELOCITY_EXCEEDED ∧
      refused.world.node.carriers.any (fun k => k.cid == 10 && !k.accepted && !k.mayOpen) = true ∧
      refused.led.map (·.cid) = [5] ∧
      selected.world.node.cands.map (fun c => (c.id, c.quorum)) = [(5, false), (6, false)] ∧
      selected.world.node.selected.map (·.1) = [e1.id] ∧
      accepted.led.map (·.cid) = [s1.id] ∧
      accepted.world.node.cands.map (fun c => (c.id, c.quorum)) =
        [(1, false), (2, false), (5, false), (6, false)] ∧
      opened.world.node.cands.map (fun c => (c.id, c.quorum)) =
        [(1, true), (2, true), (5, false), (6, false)]) := by
  simp only [List.mem_cons, forall_eq_or_imp]
  decide +kernel

/-! ### The relation is not vacuous, and the arming receipt is inside it -/

/-- Both steps of the arming trace are inside the horizon — the node enters the receipt unarmed —
and every observation of both is equal: the response, `/pending`, `locked_down`, `DEF-12`'s
marker, the effects and the work trace. The second step is the holder decision itself, which is
where the marker twin lives. -/
@[req "DUR-1"]
theorem arm_is_silent_with_current :
    (pairs Silence.current Kernel.current armTrace).length = 2 ∧
    (pairs Silence.current Kernel.current armTrace).all (fun y => y.1 == y.2) = true ∧
    ((pairs Silence.current Kernel.current armTrace).map fun y => y.1.marker) = [false, true] := by
  decide

/-- Under the withdrawn value the marker fires on the arm bit, so the holder confirmation is
present in one world and absent in the other — `DEF-12`'s "duress oracle hanging off an ordinary
log", on the one step both worlds still share. -/
@[req "DEF-12"]
theorem marker_leaks_with_armBit :
    (pairs .armBit Kernel.current armTrace).any (fun y => y.1 != y.2) = true ∧
    ((pairs .armBit Kernel.current armTrace).map fun y => y.1.marker) = [false, true] ∧
    ((pairs .armBit Kernel.current armTrace).map fun y => y.2.marker) = [false, false] := by
  decide

/-! ### `F54`'s `DUR-20` row: the traversal that runs only when `T` moved -/

/-- As the clause stands, every hot acceptance visits every selected entry, so the work trace of
the second acceptance is the same in both worlds. -/
@[req "DUR-20"]
theorem traversal_uniform_with_current :
    (pairs Silence.current Kernel.current hotTrace).length = 3 ∧
    (pairs Silence.current Kernel.current hotTrace).all (fun y => y.1.ops == y.2.ops) = true ∧
    ((pairs Silence.current Kernel.current hotTrace).map fun y => y.1.ops.length) = [2, 3, 4] := by
  decide

/-- Under the withdrawn value the traversal runs only when `T` actually moved, and `DUR-14`
shrinks `T` only on an armed node: at the second acceptance the armed world visits the whole
registry and the other visits nothing, which is "work a normal-PIN twin does not do". The world
that skips reaches the same node it reaches under the rule as it stands — its `T` did not move, so
the windows the traversal would have written are the ones already there — and the last conjunct
is that state equality, so what the twin changes is the trace and nothing else. (The first
acceptance moves no `T` in either world, so under the withdrawn value neither traverses, which is
why the leak appears only after the arm.) -/
@[req "DUR-20"]
theorem traversal_leaks_with_onlyWhenMoved :
    (pairs Silence.current withdrawnTraversal hotTrace).any (fun y => y.1.ops != y.2.ops) = true ∧
    ((pairs Silence.current withdrawnTraversal hotTrace).map fun y => y.1.ops) =
      [[], [.select 2, .visit 1, .visit 2], [.visit 5, .visit 6, .visit 1, .visit 2]] ∧
    ((pairs Silence.current withdrawnTraversal hotTrace).map fun y => y.2.ops) =
      [[], [.select 2, .visit 1, .visit 2], []] ∧
    (runOf withdrawnTraversal tblN hotTrace).world.node
      = (runOf Kernel.current tblN hotTrace).world.node := by
  decide

/-! ### `DUR-14`'s dynamic `T` -/

/-- `ADR-0012`'s verification round of 2026-07-15 records "One true silence break → FIXED: dynamic
T". As the clause stands, the hot spend accepted at 70 pulls `T` to `100 − 5`, and the bound the
whole relation rests on — `T` at or before that spend's fire time less `epsilon_secs` — holds at
the state the acceptance leaves. -/
@[req "DUR-14"]
theorem dynamic_bound_holds_with_current :
    (runOf Kernel.current tblD hotTrace).world.node.T = Wall.sample 95 ∧
    Wall.belowFire (runOf Kernel.current tblD hotTrace).world.node.T (Wall.sample 100) 5
      (envAt 70 70).eff = true := by
  decide

/-- Under the withdrawn value `T` stays at the deadline the arm wrote, and the bound is false at
that reachable state: the armed world holds a hot candidate whose fire time, 100, is 150 seconds
before the deadline it is concealing. What the model does NOT show is the release — `SPN-38`
requires a quorum, and the only thing that opens one is that candidate's own holder decision, which
writes a `T` no later than the one `DUR-13` computes from its scan over exactly these candidates.
So this is the invariant failing, not a trace of the partial leaving. -/
@[req "DUR-14"]
theorem static_bound_fails_with_withdrawn :
    (runOf withdrawnDynamics tblD hotTrace).world.node.T = Wall.sample 250 ∧
    Wall.belowFire (runOf withdrawnDynamics tblD hotTrace).world.node.T (Wall.sample 100) 5
      (envAt 70 70).eff = false := by
  decide

/-! ### `DUR-10`'s insertion, and the horizon itself -/

def beforeReceipt (tbl : Enrolment) : Node := (runOf Kernel.current tbl (armTrace.take 1)).world.node

/-- Not a flip: a holder decision that inserted the Escape only under duress. `DUR-10` requires
the insertion "under either PIN, in identical work"; the leaky variant's visit trace differs at
the arming receipt, which is the step both worlds otherwise share. -/
@[req "DUR-10"]
theorem duress_only_insertion_leaks :
    workDuressOnly (envAt 60 60) (beforeReceipt tblD) (.receipt 10 1)
      = [Op.select 2, Op.visit 1, Op.visit 2] ∧
    workDuressOnly (envAt 60 60) (beforeReceipt tblN) (.receipt 10 1) = [Op.visit 1, Op.visit 2] ∧
    (workDuressOnly (envAt 60 60) (beforeReceipt tblD) (.receipt 10 1)
      != workDuressOnly (envAt 60 60) (beforeReceipt tblN) (.receipt 10 1)) = true ∧
    (((pairs Silence.current Kernel.current armTrace).drop 1).map fun y => y.1.ops)
      = [[.select 2, .visit 1, .visit 2]] ∧
    (((pairs Silence.current Kernel.current armTrace).drop 1).map fun y => y.2.ops)
      = [[.select 2, .visit 1, .visit 2]] := by
  decide

/-- The horizon is where it is because that is where the two worlds part: at `T` the armed
world's selected Escape opens its window (`DUR-20`) with `sweep_active` and its own bit set
(`DUR-10`), and queues a partial the other world does not. The walk stops before that step, which
is what "sticky" means here; the step is computed beside it to show the boundary is real and not
an artifact of the guard. -/
@[req "DUR-7"]
theorem horizon_is_where_the_runs_part :
    (pairs Silence.current Kernel.current
      (armTrace ++ [(envAt 250 250, .pinless .firePass)])).length = 2 ∧
    (sysStep Ledger.current cfg Kernel.current (envAt 250 250)
      (runOf Kernel.current tblD armTrace) .firePass).2
        = [Effect.queuePartial (sighash esc1 0) 0 false 2] ∧
    (sysStep Ledger.current cfg Kernel.current (envAt 250 250)
      (runOf Kernel.current tblN armTrace) .firePass).2 = [] := by
  decide

/-! ### `F64`: a later holder decision on an armed node, and `DUR-13`'s clamp

Every holder decision writes `T` under both PINs (`DUR-5`). On a node armed before it, `DUR-13`
writes `max(min(T, T_computed), now)`, selected on the arm bit as it stood before the decision;
on any other node it writes the computed value. The traces below run the rule over `current`, and
the growth `F64` records under the withdrawn value, `never`, in an explicit record. -/

def sp3 : Cand := cand 7 { id := 300, inputs := [4], outflow := 0 } false none 900
def es3 : Cand := cand 8 { id := 301, inputs := [4, 5], outflow := 0 } false none 900
def sp6 : Cand := cand 11 { id := 304, inputs := [8], outflow := 0 } false none 900
def es6 : Cand := cand 12 { id := 305, inputs := [8, 9], outflow := 0 } false none 900
def sp5 : Cand := cand 13 { id := 306, inputs := [10], outflow := 0 } false none 900
def es5 : Cand := cand 14 { id := 307, inputs := [10, 11], outflow := 0 } false none 900

/-- Every value as it stands but `DUR-13`'s clamp, which is `never`: a holder decision writes the
computed value whatever the node's arm bit. -/
def withdrawnClampOn : Rules := { Kernel.current with clampOn := .never }

/-- `armTrace`, then a second pair, of the same class under both tables when `pin` is 0, requested
at `request` and committed by its holder decision at `receipt`. -/
def secondPairTrace (pin request receipt : Nat) : List (Env × Input) :=
  armTrace ++ [ (envAt request request, .request 30 pin (Wall.sample 900) sp3 es3),
                (envAt receipt receipt, .pinless (.receipt 30 1)) ]

/-- A selected candidate's window, as `(fire_at, close)`. -/
def windowOf (n : Node) (id : Nat) : Option (Option Wall × Option Wall) :=
  (n.cands.find? (·.id == id)).map fun c => (c.fireAt, c.windowClose)

/-- An ordinary commit inside the concealment horizon leaves `T` where the arm put it. The second
pair is requested at 100 and committed at 110, while the hot spend of `armTrace` is pending, so
no record naming the second pair has its duress bit set, so `DUR-13` starts at the seed
`max(ratchet, now) = 110` and computes `max(min(110 + 200, 300 − 5), 110) = 295`. The world whose table made the first
PIN ordinary is unarmed and writes 295; the armed world writes `max(min(250, 295), 110) = 250`.
Every step's entering state is inside the horizon in both worlds. The decision selects the second
pair's Escape beside the first, and both carry the one window `[250, 290]` (`DUR-20`). -/
@[req "DUR-13"]
theorem later_commit_keeps_T :
    let tr := secondPairTrace 0 100 110
    allPreHorizon Kernel.current tblD tr = true ∧
    allPreHorizon Kernel.current tblN tr = true ∧
    (runOf Kernel.current tblD tr).world.node.T = Wall.sample 250 ∧
    (runOf Kernel.current tblD tr).world.node.armed = true ∧
    (runOf Kernel.current tblN tr).world.node.T = Wall.sample 295 ∧
    (runOf Kernel.current tblN tr).world.node.armed = false ∧
    (runOf Kernel.current tblD tr).world.node.selected = [(2, true), (8, false)] ∧
    windowOf (runOf Kernel.current tblD tr).world.node 2
      = some (some (Wall.sample 250), some (Wall.sample 290)) ∧
    windowOf (runOf Kernel.current tblD tr).world.node 8
      = some (some (Wall.sample 250), some (Wall.sample 290)) := by
  decide

/-- A later arm cannot grow `T` either: the same trace with the second pair requested under PIN 1,
the duress PIN of the first table, so its holder decision arms the first world a second time. That
world writes 250 again and selects both Escapes under their duress bits at the one window
`[250, 290]`; the other world, unarmed, writes the computed 295. -/
@[req "DUR-13"]
theorem later_arm_keeps_T :
    let tr := secondPairTrace 1 100 110
    allPreHorizon Kernel.current tblD tr = true ∧
    allPreHorizon Kernel.current tblN tr = true ∧
    (runOf Kernel.current tblD tr).world.node.T = Wall.sample 250 ∧
    (runOf Kernel.current tblN tr).world.node.T = Wall.sample 295 ∧
    (runOf Kernel.current tblD tr).world.node.selected = [(2, true), (8, true)] ∧
    windowOf (runOf Kernel.current tblD tr).world.node 2
      = some (some (Wall.sample 250), some (Wall.sample 290)) ∧
    windowOf (runOf Kernel.current tblD tr).world.node 8
      = some (some (Wall.sample 250), some (Wall.sample 290)) := by
  decide

/-- A trace with no hot spend in `DUR-13`'s hot domain, so nothing caps its ceiling: a pair that is not hot
armed by PIN 1 at 50 and 60, writing `T = max(50 + 200, 60) = 250`; then two ordinary pairs, at 240
and 245 and at 430 and 435, each computing its seed `max(ratchet, now)`, its decision's own sample,
plus 200. -/
def chainTrace : List (Env × Input) :=
  [ (envAt 50 50, .request 30 1 (Wall.sample 900) sp3 es3),
    (envAt 60 60, .pinless (.receipt 30 1)),
    (envAt 240 240, .request 31 0 (Wall.sample 900) sp6 es6),
    (envAt 245 245, .pinless (.receipt 31 1)),
    (envAt 430 430, .request 32 0 (Wall.sample 900) sp5 es5),
    (envAt 435 435, .pinless (.receipt 32 1)) ]

/-- The uncapped case as the rule stands: the ordinary commit at 245 computes 445, which the
unarmed world writes and the armed world does not, keeping 250, with every entering state inside
the horizon. The armed world's `T` has passed by the next ordinary request, at 430. -/
@[req "DUR-13"]
theorem chained_commit_keeps_T :
    let tr := chainTrace.take 4
    allPreHorizon Kernel.current tblD tr = true ∧
    allPreHorizon Kernel.current tblN tr = true ∧
    (runOf Kernel.current tblD tr).world.node.T = Wall.sample 250 ∧
    (runOf Kernel.current tblD tr).world.node.armed = true ∧
    (runOf Kernel.current tblN tr).world.node.T = Wall.sample 445 ∧
    (runOf Kernel.current tblN tr).world.node.armed = false := by
  decide

/-- `F64`'s growth, under the withdrawn value (`withdrawnClampOn`): each ordinary commit on the
armed node writes its computed value, so `T` walks from 250 to 445 to 635, and every step's
entering state is inside the horizon in both worlds. The coercer's requests extend the hostage window with no pending
hot spend to cap it, and never learn the PIN class. -/
@[req "DUR-13"]
theorem f64_commits_grow_T_with_withdrawn :
    allPreHorizon withdrawnClampOn tblD chainTrace = true ∧
    allPreHorizon withdrawnClampOn tblN chainTrace = true ∧
    (runOf withdrawnClampOn tblD (chainTrace.take 2)).world.node.T = Wall.sample 250 ∧
    (runOf withdrawnClampOn tblD (chainTrace.take 2)).world.node.armed = true ∧
    (runOf withdrawnClampOn tblD (chainTrace.take 4)).world.node.T = Wall.sample 445 ∧
    (runOf withdrawnClampOn tblD chainTrace).world.node.T = Wall.sample 635 ∧
    (runOf withdrawnClampOn tblD chainTrace).world.node.armed = true := by
  decide

/-- An ordinary pair committed at 50 and 60 on an unarmed node, writing `T = max(min(60 + 200, 300 −
5), 60) = 260` from the seed; then a duress
pair that is not hot requested at 600 and committed at 610, after the first spend's expiry, so
`DUR-13`'s scan finds no candidate in its hot domain. -/
def ordinaryFirstTrace : List (Env × Input) :=
  [ (envAt 50 50, .request 10 0 (Wall.sample 400) s1 e1),
    (envAt 60 60, .pinless (.receipt 10 1)),
    (envAt 600 600, .request 30 1 (Wall.sample 900) sp3 es3),
    (envAt 610 610, .pinless (.receipt 30 1)) ]

/-- The first arm after ordinary traffic writes the computed value, `max(600 + 200, 610) = 800`,
and not its minimum with the stale 260 the ordinary commit left: the selector reads the arm bit
as it stood before the decision, which was clear. A selector on the bit the decision writes would
give `max(min(260, 800), 610) = 610`. The world whose table made the PIN ordinary starts the same
decision at the seed, 610, and writes 810. -/
@[req "DUR-13"]
theorem first_arm_writes_computed :
    (runOf Kernel.current tblD (ordinaryFirstTrace.take 2)).world.node.T = Wall.sample 260 ∧
    (runOf Kernel.current tblD (ordinaryFirstTrace.take 2)).world.node.armed = false ∧
    (runOf Kernel.current tblD ordinaryFirstTrace).world.node.T = Wall.sample 800 ∧
    (runOf Kernel.current tblD ordinaryFirstTrace).world.node.armed = true ∧
    (runOf Kernel.current tblN ordinaryFirstTrace).world.node.T = Wall.sample 810 ∧
    (runOf Kernel.current tblN ordinaryFirstTrace).world.node.armed = false := by
  decide

/-- A holder decision that lands after `T`, past the concealment horizon, writes its own sample:
the clamp's `max(…, now)`. An ordinary commit at 305, with the first spend's window `[300, 340]`
still open and so in the hot domain, computes
`max(min(305 + 200, 300 − 5), 305) = 305` from the seed, and the armed world writes `max(min(250, 305), 305) =
305` and re-windows both selected Escapes at `[305, 345]`; a plain `min` would leave 250 and a
window `[250, 290]` already closed. With no candidate in the hot domain, a commit at 610 computes 810,
writes 610 and re-windows both at `[610, 650]`. -/
@[req "DUR-13"]
theorem late_decision_writes_now :
    (envAt 300 300).eff.deadlineReached (runOf Kernel.current tblD armTrace).world.node.T = true ∧
    (runOf Kernel.current tblD (secondPairTrace 0 300 305)).world.node.T = Wall.sample 305 ∧
    windowOf (runOf Kernel.current tblD (secondPairTrace 0 300 305)).world.node 2
      = some (some (Wall.sample 305), some (Wall.sample 345)) ∧
    windowOf (runOf Kernel.current tblD (secondPairTrace 0 300 305)).world.node 8
      = some (some (Wall.sample 305), some (Wall.sample 345)) ∧
    (runOf Kernel.current tblD (secondPairTrace 0 600 610)).world.node.T = Wall.sample 610 ∧
    (runOf Kernel.current tblD (secondPairTrace 0 600 610)).world.node.armed = true ∧
    windowOf (runOf Kernel.current tblD (secondPairTrace 0 600 610)).world.node 2
      = some (some (Wall.sample 610), some (Wall.sample 650)) ∧
    windowOf (runOf Kernel.current tblD (secondPairTrace 0 600 610)).world.node 8
      = some (some (Wall.sample 610), some (Wall.sample 650)) := by
  decide

/-! ### `F60`: a backward effective sample after the arm, and the time ratchet

`F60` records a wall clock stepping backward after a holder decision. Of the effective sample's
high-water, `SPN-13` says it "is advanced, on an accept only", so the effective sample steps back
below the `T` that decision wrote, or back into a hot window the node has already passed. `silence` takes no premise on the samples.
What closes both routes is `DUR-7`'s time ratchet, read by the deadline driver and by a hot
window's close (`SPN-38`). Each route runs below on the effective sample alone
(`withdrawnReadTime`), under the readers as they stand, and with one reader at a time, which is
why each reader is a guard parameter of its own. -/

/-- The hot close and the driver on the effective sample alone, beside every other value as it stands. -/
def withdrawnReadTime : Rules := { Kernel.current with closeTime := .effective, driverTime := .effective }
/-- The hot close at the time ratchet and the driver on the effective sample alone. -/
def withdrawnDriverTime : Rules := { Kernel.current with driverTime := .effective }
/-- The driver at the time ratchet and the hot close on the effective sample alone. -/
def withdrawnCloseTime : Rules := { Kernel.current with closeTime := .effective }

/-- `F60`'s hot candidate: its `fire_at` is 90, so `DUR-13`'s ceiling is `90 − 5`. -/
def s60 : Cand := cand 1 hot1 true (some 90) 400

/-- `F60`'s trace, the clamp route. Ingress at 40 with `duress_delay_secs` 200, the holder
decision at 100 writing `T = max(85, 100) = 100` under both tables (`DUR-13`), the cap `90 − 5` below
the ceiling from either start, the duress intent's 40 or the seed 100,
and then a wall stepped back to 95 with no accept between, so nothing holds the effective sample
up, and a fire pass in the gap. -/
def backTrace : List (Env × Input) :=
  [ (envAt 40 40, .request 10 1 (Wall.sample 400) s60 e1),
    (envAt 100 100, .pinless (.receipt 10 1)),
    (envAt 95 101, .pinless .firePass) ]

/-- The backward step, named on its own: the third environment's effective sample is strictly
before the second's, while its HotClock is not. `NCH-41`'s Mono is process-lifetime and does not
step back; `F60` moves the wall alone. -/
theorem f60_sample_steps_backward :
    (envAt 100 100).eff.notAfter (envAt 95 101).eff = false ∧
    (envAt 100 100).mono.notAfter (envAt 95 101).mono = true := by decide

/-- The deadline the arm wrote, at the value `F60` records. -/
@[req "DUR-13"]
theorem f60_T_is_the_arm_sample :
    (runOf Kernel.current tblD backTrace).world.node.T = Wall.sample 100 := by decide

/-- The clamp route on the effective sample alone (`withdrawnReadTime`), which is `F60` as
recorded. All three steps are inside the horizon — 95 is strictly below the `T` of 100, so `preHorizon` admits
the fire pass in both worlds — and the third pair is unequal: the world whose table made the PIN
ordinary queues a hot partial, and the armed world's `DUR-11` freeze holds it. A PIN-dependent
observable strictly before `T`, which `DUR-1` forbids: "Every observable a node emits MUST be
identical between a normal-PIN and a duress-PIN request". -/
@[req "DUR-1"]
theorem f60_backward_step_leaks :
    (pairs Silence.current withdrawnReadTime backTrace).length = 3 ∧
    ((pairs Silence.current withdrawnReadTime backTrace).map fun y => y.1 == y.2)
      = [true, true, false] ∧
    ((pairs Silence.current withdrawnReadTime backTrace).map fun y => y.1.effects)
      = [[], [], []] ∧
    ((pairs Silence.current withdrawnReadTime backTrace).map fun y => y.2.effects)
      = [[], [], [Effect.queuePartial (sighash hot1 0) 0 true 1]] := by
  decide

/-- The clamp route under the readers as they stand: the holder decision at 100 advanced the time
ratchet to 100 under both tables, so `DUR-7`'s driver at `max(100, 95)` has reached `T = 100` and
the walk ends before the pass at 95. Two pairs, both equal. -/
@[req "DUR-7"]
theorem f60_clamp_silent_with_current :
    (runOf Kernel.current tblD (backTrace.take 2)).world.node.ratchet = (envAt 100 100).eff ∧
    (runOf Kernel.current tblN (backTrace.take 2)).world.node.ratchet = (envAt 100 100).eff ∧
    preHorizon Kernel.current (envAt 95 101)
      (runOf Kernel.current tblD (backTrace.take 2)).world.node = false ∧
    (pairs Silence.current Kernel.current backTrace).length = 2 ∧
    (pairs Silence.current Kernel.current backTrace).all (fun y => y.1 == y.2) = true := by
  decide

/-- The expiry route's hot pair: a `fire_at` of 80 and an expiry of 120, which meets
`SPN-30`'s "`expiry ≥ fire_at + combine_slack_secs`, equality passing" at this node's 40. -/
def sLapsing : Cand := cand 1 hot1 true (some 80) 120
def eLapsing : Cand := cand 2 esc1 false none 120

/-- The second route, through the scan of `DUR-13`, whose hot domain is `DUR-13`'s "candidate is
hot, not broadcast, fire window not closed at max(ratchet, now)": a candidate whose expiry has
passed at the decision is outside it. The hot pair is requested at 40 under PIN 0, ordinary in both
tables, and opened by its own holder decision at 70. A pair that is not hot is requested at 72
under PIN 1 and committed at 130, after the hot candidate's expiry, so the scan drops the hot
candidate and `T = max(72 + 200, 130) = 272` in the first world, arming it, and `max(130 + 200,
130) = 330` in the other, from the seed. The wall then
steps back to 85, and a fire pass runs there, 187 seconds before `T`. -/
def expiryTrace : List (Env × Input) :=
  [ (envAt 40 40, .request 10 0 (Wall.sample 120) sLapsing eLapsing),
    (envAt 70 70, .pinless (.receipt 10 1)),
    (envAt 72 72, .request 20 1 (Wall.sample 900) sp3 es3),
    (envAt 130 130, .pinless (.receipt 20 1)),
    (envAt 85 131, .pinless .firePass) ]

/-- The expiry route on the effective sample alone: 85 is inside the hot window `[80, 120]` and
below `T`, so the ordinary world queues the hot partial and the armed world's freeze holds it. -/
@[req "DUR-1"]
theorem f60_expiry_route_leaks :
    (runOf withdrawnReadTime tblD (expiryTrace.take 4)).world.node.T = Wall.sample 272 ∧
    (runOf withdrawnReadTime tblD (expiryTrace.take 4)).world.node.armed = true ∧
    (pairs Silence.current withdrawnReadTime expiryTrace).length = 5 ∧
    ((pairs Silence.current withdrawnReadTime expiryTrace).map fun y => y.1 == y.2)
      = [true, true, true, true, false] ∧
    ((pairs Silence.current withdrawnReadTime expiryTrace).map fun y => y.1.effects)
      = [[], [], [], [], []] ∧
    ((pairs Silence.current withdrawnReadTime expiryTrace).map fun y => y.2.effects)
      = [[], [], [], [], [Effect.queuePartial (sighash hot1 0) 0 true 1]] := by
  decide

/-- The expiry route under the readers as they stand: the arm at 130 advanced the ratchet to 130,
so the close reads `max(130, 85)`, past the expiry of 120, and the window is shut in both worlds,
while the driver at 130 is still below `T`. Every step is inside the horizon, and every pair is
equal. -/
@[req "SPN-38"]
theorem f60_expiry_route_silent_with_current :
    (runOf Kernel.current tblD (expiryTrace.take 4)).world.node.ratchet = (envAt 130 130).eff ∧
    fullSilent Silence.current Kernel.current expiryTrace := by
  decide +kernel

/-- The send's shape of the same route. The hot pair is released by a fire pass at 85, before the
arm; a peer's partial brings the held set to `t`; the package is assembled and tested at 87. The
arm at 130 finds the candidate expired and still resident, and the send re-authorizes it on a wall
stepped back to 90. -/
def sendTrace : List (Env × Input) :=
  [ (envAt 40 40, .request 10 0 (Wall.sample 120) sLapsing eLapsing),
    (envAt 70 70, .pinless (.receipt 10 1)),
    (envAt 72 72, .request 20 1 (Wall.sample 900) sp3 es3),
    (envAt 85 85, .pinless .firePass),
    (envAt 86 86, .pinless (.receivePartial (sighash hot1 0) 0 1 1)),
    (envAt 87 87, .pinless (.packageAccepted 1)),
    (envAt 130 130, .pinless (.receipt 20 1)),
    (envAt 90 131, .pinless (.send 1)) ]

/-- The send route on the effective sample alone: the ordinary world broadcasts at 90, inside the
window and below `T`, and the armed world's freeze refuses the same send. -/
@[req "DUR-1"]
theorem f60_send_route_leaks :
    (runOf withdrawnReadTime tblN (sendTrace.take 6)).world.node.cands.any
      (fun c => c.id == 1 && c.packageOk) = true ∧
    (pairs Silence.current withdrawnReadTime sendTrace).length = 8 ∧
    ((pairs Silence.current withdrawnReadTime sendTrace).map fun y => y.1 == y.2)
      = [true, true, true, true, true, true, true, false] ∧
    ((pairs Silence.current withdrawnReadTime sendTrace).drop 7).map (fun y => (y.1.effects, y.2.effects))
      = [([], [Effect.broadcast hot1.id])] := by
  decide +kernel

/-- The send route under the readers as they stand: the re-authorization reads the same `due` as
the fire pass, so its close is at `max(130, 90)`, past the expiry, and neither world broadcasts. -/
@[req "SPN-39"]
theorem f60_send_route_silent_with_current :
    (runOf Kernel.current tblN (sendTrace.take 6)).world.node.cands.any
      (fun c => c.id == 1 && c.packageOk) = true ∧
    fullSilent Silence.current Kernel.current sendTrace := by
  decide +kernel

/-- Neither reader is enough alone. With the hot close at the ratchet and the driver on the
effective sample, the clamp route leaks: the driver at 95 is below `T = 100`, and the close at
`max(100, 95)` is inside the window `[90, 130]`. -/
@[req "DUR-7"]
theorem f60_ratcheted_close_alone_leaks :
    ((pairs Silence.current withdrawnDriverTime backTrace).map fun y => y.1 == y.2) = [true, true, false] := by
  decide

/-- And with the driver at the ratchet and the hot close on the effective sample, the expiry and
send routes leak: the driver at 130 is below `T = 272`, and the close at 85 or 90 is inside the
window `[80, 120]`. -/
@[req "SPN-38"]
theorem f60_ratcheted_driver_alone_leaks :
    ((pairs Silence.current withdrawnCloseTime expiryTrace).map fun y => y.1 == y.2)
      = [true, true, true, true, false] ∧
    ((pairs Silence.current withdrawnCloseTime sendTrace).map fun y => y.1 == y.2)
      = [true, true, true, true, true, true, true, false] := by
  decide +kernel

/-! ### What moves the time ratchet (`DUR-7`) -/

/-- A hot spend over the budget once `s1` is charged: `POL-16` refuses it before signing. -/
def overBudget : Cand := cand 5 { id := 102, inputs := [2], outflow := 995 } true (some 400) 500

/-- A hot acceptance at 50 under PIN 1, and its holder decision at 60, which arms the first world;
then, at later samples, a prune, a fire pass and a tick, a repeat of the spend with a different
expiry that registration refuses, and a hot spend the Hot ledger refuses. The prune runs at 290,
the last second of `e1`'s window on the armed run, `[250, 290]`, so `BtcPolicy.Kernel.prune`'s removal conjunct leaves the pair resident on
the armed run too and the repeat meets it. Both refusals stage a
Carrier (`DUR-4`); a relay at 350 reaches `t` on the first, the registration's, and runs a refused
Carrier's holder decision; and at 360 an accepted spend that is not hot. -/
def ratchetTrace : List (Env × Input) :=
  [ (envAt 50 50, .request 10 1 (Wall.sample 400) s1 e1),
    (envAt 60 60, .pinless (.receipt 10 1)),
    (envAt 290 70, .pinless .prune),
    (envAt 300 80, .pinless .firePass),
    (envAt 310 90, .pinless .tick),
    (envAt 330 100, .request 11 0 (Wall.sample 400) { s1 with expiry := Wall.sample 410 } e1),
    (envAt 340 110, .request 12 0 (Wall.sample 500) overBudget e2),
    (envAt 350 120, .pinless (.receipt 11 1)),
    (envAt 360 130, .request 13 0 (Wall.sample 900) sp6 es6) ]

/-- `DUR-7`: "The **time ratchet** is the greatest effective time this node has read at a holder
decision (`DUR-5`), a refused Carrier's included, or at a hot acceptance". Under both tables it
advances at the hot acceptance (50), at the holder decision (60) and at the refused Carrier's
holder decision (350), and nothing else moves it: not a prune, a fire pass or a tick at later
samples, nor a registration refusal or a budget refusal of a hot request, which the composed step
routes around `Kernel.accept`, nor the accepted spend at 360 that is not hot. The refused
Carrier's decision writes `T` by `DUR-13`, which names "an ordinary, a duress or a refused
Carrier's" decision: `max(min(250, 350), 350) = 350` on the armed node, and on the other the
computed value from the seed, `max(350 + 200, 350) = 550`, since `s1`'s window `[300, 340]` is
closed at 350 and `s1` is outside the hot domain. -/
@[req "DUR-7"]
theorem ratchet_moves_only_at_its_events :
    ∀ tbl ∈ [tblD, tblN],
      ((List.range 9).map fun k =>
          (runOf Kernel.current tbl (ratchetTrace.take (k + 1))).world.node.ratchet)
        = [50, 60, 60, 60, 60, 60, 60, 350, 350].map (fun x => (envAt x x).eff) ∧
      respond Kernel.current cfg (envAt 330 100) (runOf Kernel.current tbl (ratchetTrace.take 5))
        ((ratchetTrace.getD 5 (envAt 0 0, .pinless .tick)).2.event tbl)
        = .refused .PSBT_INCONSISTENT ∧
      respond Kernel.current cfg (envAt 340 110) (runOf Kernel.current tbl (ratchetTrace.take 6))
        ((ratchetTrace.getD 6 (envAt 0 0, .pinless .tick)).2.event tbl)
        = .refused .HOT_VELOCITY_EXCEEDED ∧
      (runOf Kernel.current tbl (ratchetTrace.take 7)).world.node.carriers.any
        (fun k => k.cid == 11 && !k.accepted) = true ∧
      (runOf Kernel.current tbl ratchetTrace).world.node.carriers.any
        (fun k => k.cid == 13 && k.accepted) = true ∧
      (runOf Kernel.current tbl (ratchetTrace.take 8)).world.node.T
        = Wall.sample (if tbl 1 then 350 else 550) := by
  simp only [List.mem_cons, forall_eq_or_imp]
  decide +kernel

/-! ### What reads effective time below the ratchet (`SPN-38`, `DUR-13`)

Of the time ratchet and its deadline driver, `DUR-7` says "Its readers are exactly three: this
driver's comparison, the close of a hot candidate's fire window (`SPN-38`) and the seed of a holder
decision's start (`DUR-13`)" and "No other comparison reads the ratchet". Each trace below puts the
ratchet above the effective sample at one of those other comparisons, so a reading at the ratchet
differs; `clamp_reads_effective_below_ratchet`'s decision reads the seed at the ratchet, and the
close of the hot candidate in its domain there too, which is `SPN-38`'s close, and its clamp at
effective time. -/

/-- A spend that is not hot, with its own fire window: `fire_at` 240 and expiry 300. -/
def nh : Cand := cand 15 { id := 110, inputs := [12], outflow := 0 } false (some 240) 300
def nhEsc : Cand := cand 16 { id := 111, inputs := [12, 13], outflow := 0 } false none 300
/-- A hot spend accepted at 400, far from due, which advances the ratchet there. -/
def sLate : Cand := cand 17 { id := 112, inputs := [14], outflow := 10 } true (some 800) 900
def eLate : Cand := cand 18 { id := 113, inputs := [14, 15], outflow := 0 } false none 900

/-- Under a PIN both tables make ordinary: `nh`'s pair accepted at 40 and opened at 45, `s1`'s
accepted at 50 and opened at 60, which writes `T = max(min(60 + 200, 300 − 5), 60) = 260` from the
seed and both selected Escapes' windows at `[260, 300]` (`DUR-20`); then `sLate` accepted at 400, which
advances the ratchet to 400 and, the node not being armed, leaves `T` where it was. -/
def closeTrace : List (Env × Input) :=
  [ (envAt 40 40, .request 30 0 (Wall.sample 900) nh nhEsc),
    (envAt 45 45, .pinless (.receipt 30 1)),
    (envAt 50 50, .request 10 0 (Wall.sample 400) s1 e1),
    (envAt 60 60, .pinless (.receipt 10 1)),
    (envAt 400 70, .request 40 0 (Wall.sample 900) sLate eLate) ]

/-- `SPN-38`: "every other candidate's fire window, opening and close, is read at effective time".
With the ratchet at 400 and `T` at 260, a wall stepped back to 265 finds `s1`'s Escape inside its
window `[T, T + combine_slack_secs]` and `nh` inside `[240, 300]`, and both are due; read at the
ratchet, both windows would be shut. -/
@[req "SPN-38"]
theorem other_windows_close_on_effective_time :
    ∀ tbl ∈ [tblD, tblN],
      (runOf Kernel.current tbl closeTrace).world.node.ratchet = (envAt 400 400).eff ∧
      (runOf Kernel.current tbl closeTrace).world.node.T = Wall.sample 260 ∧
      windowOf (runOf Kernel.current tbl closeTrace).world.node e1.id
        = some (some (Wall.sample 260), some (Wall.sample 300)) ∧
      (runOf Kernel.current tbl closeTrace).world.node.cands.any
        (fun c => c.id == e1.id && due Kernel.current (envAt 265 80)
          (runOf Kernel.current tbl closeTrace).world.node c) = true ∧
      (runOf Kernel.current tbl closeTrace).world.node.cands.any
        (fun c => c.id == nh.id && due Kernel.current (envAt 265 80)
          (runOf Kernel.current tbl closeTrace).world.node c) = true := by
  simp only [List.mem_cons, forall_eq_or_imp]
  decide +kernel

/-- A pair that is not hot, accepted at 140 and opened at 150. -/
def sx : Cand := cand 19 { id := 114, inputs := [16], outflow := 0 } false none 900
def ex : Cand := cand 20 { id := 115, inputs := [16, 17], outflow := 0 } false none 900
/-- A hot spend whose `fire_at` is 120. -/
def sH : Cand := cand 21 { id := 116, inputs := [18], outflow := 10 } true (some 120) 900
def eH : Cand := cand 22 { id := 117, inputs := [18, 19], outflow := 0 } false none 900

/-- The holder decision at 150 advances the ratchet to 150; the wall steps back, and `sH` is
accepted at 100 and opened by its own holder decision at 100. `hold_secs` is 0 on this node
(`A`), so the HotClock check passes at every sample and only the wall opening decides. -/
def openTrace : List (Env × Input) :=
  [ (envAt 140 140, .request 50 0 (Wall.sample 900) sx ex),
    (envAt 150 150, .pinless (.receipt 50 1)),
    (envAt 100 160, .request 60 0 (Wall.sample 900) sH eH),
    (envAt 100 161, .pinless (.receipt 60 1)) ]

/-- `SPN-38`: "For a hot candidate, its fire window's opening, `fire_at ≤ now`, is read at
effective time". The ratchet is at 150 when `sH`, accepted at 100 with `fire_at` 120, is opened;
at 101 it is not due, and at 120 it is. Read at the ratchet, its opening would have passed when it
was accepted, and its Hold would be shortened to nothing. -/
@[req "SPN-38"]
theorem hot_opening_on_effective_time :
    ∀ tbl ∈ [tblD, tblN],
      (runOf Kernel.current tbl openTrace).world.node.ratchet = (envAt 150 150).eff ∧
      (runOf Kernel.current tbl openTrace).world.node.cands.any
        (fun c => c.id == sH.id && c.quorum &&
          !due Kernel.current (envAt 101 162) (runOf Kernel.current tbl openTrace).world.node c &&
          due Kernel.current (envAt 120 163) (runOf Kernel.current tbl openTrace).world.node c)
        = true := by
  simp only [List.mem_cons, forall_eq_or_imp]
  decide +kernel

/-- Three hot pairs: `sP` and `sS` with `fire_at` 800, and `sQ` with `fire_at` 260, whose window
is `[260, 300]`. -/
def sP : Cand := cand 55 { id := 354, inputs := [54], outflow := 10 } true (some 800) 900
def eP : Cand := cand 56 { id := 355, inputs := [54, 55], outflow := 0 } false none 900
def sQ : Cand := cand 57 { id := 356, inputs := [56], outflow := 10 } true (some 260) 900
def eQ : Cand := cand 58 { id := 357, inputs := [56, 57], outflow := 0 } false none 900
def sS : Cand := cand 59 { id := 358, inputs := [58], outflow := 10 } true (some 800) 900
def eS : Cand := cand 60 { id := 359, inputs := [58, 59], outflow := 0 } false none 900

/-- `sP` requested at 50 under PIN 1 and committed at 60, which arms the first world with `T =
max(min(50 + 200, 800 − 5), 60) = 250`; `sQ` accepted at 270 under PIN 0, which advances the
ratchet to 270 and, `sQ`'s window not closed at 270, writes `max(min(250, 260 − 5), 270) = 270` on
the armed node (`DUR-14`); then the wall steps back, and `sS` is accepted at 200 and committed at
205, with `sQ` still in the hot domain. -/
def clampTrace : List (Env × Input) :=
  [ (envAt 50 50, .request 10 1 (Wall.sample 900) sP eP),
    (envAt 60 60, .pinless (.receipt 10 1)),
    (envAt 270 70, .request 30 0 (Wall.sample 900) sQ eQ),
    (envAt 200 80, .request 31 0 (Wall.sample 900) sS eS),
    (envAt 205 90, .pinless (.receipt 31 1)) ]

/-- `DUR-13`'s clamp at a holder decision while the ratchet is above effective time: the decision
at 205 starts at the seed, the ratchet's 270, and `sQ`, its window `[260, 300]` not closed at
`max(270, 205)`, pulls the computed value below the ratchet: `max(min(270 + 200, 260 − 5), 205) =
255`. The armed world writes `max(min(270, 255), 205) = 255`, its own effective sample in the
clamp's `now`, and the world whose table made the first PIN ordinary the computed value, the same
255. The ratchet stays at 270; a clamp that read it would write 270 on the armed node. -/
@[req "DUR-13"]
theorem clamp_reads_effective_below_ratchet :
    (runOf Kernel.current tblD (clampTrace.take 3)).world.node.T = Wall.sample 270 ∧
    (runOf Kernel.current tblD clampTrace).world.node.armed = true ∧
    (runOf Kernel.current tblD clampTrace).world.node.ratchet = (envAt 270 270).eff ∧
    (runOf Kernel.current tblD clampTrace).world.node.T = Wall.sample 255 ∧
    (runOf Kernel.current tblN clampTrace).world.node.T = Wall.sample 255 := by
  decide +kernel

/-! ### `SPN-30`'s cap on a hot window -/

/-- `s2`, a hot spend whose `fire_at` is 100 and whose expiry is 400, requested at 40 under a
PIN both tables make ordinary and opened by its own holder decision at 41. Its `SPN-30` close is
`min(400, 100 + 40) = 140`, well before the expiry. -/
def capTrace : List (Env × Input) :=
  [ (envAt 40 40, .request 50 0 (Wall.sample 400) s2 e2),
    (envAt 41 41, .pinless (.receipt 50 1)) ]

/-- `SPN-30`: "Its fire window is `[fire_at, min(expiry, fire_at + combine_slack_secs)]`", and the
cap decides it. At 140 the opened spend is due. At 141 it is past its opening at 100 and before
its expiry of 400, and the ratchet, at 41, is below both samples, so only the cap at `100 + 40`
finds it not due. -/
@[req "SPN-30"]
theorem hot_window_closes_at_cap :
    let n := (runOf Kernel.current tblN capTrace).world.node
    n.ratchet = (envAt 41 41).eff ∧
    s2.fireAt = some (Wall.sample 100) ∧
    (envAt 141 141).eff.atOrAfter (Wall.sample 100) = true ∧
    (envAt 141 141).eff.atOrBefore s2.expiry = true ∧
    n.cands.any (fun c => c.id == s2.id && c.quorum &&
      due Kernel.current (envAt 140 140) n c) = true ∧
    n.cands.any (fun c => c.id == s2.id && due Kernel.current (envAt 141 141) n c) = false := by
  decide +kernel

/-! ### `SPN-30`'s never-fires residual -/

/-- A hot spend with a Hold of 50 accepted at 100: `fire_at` 150 and an expiry of 1200, so its
`SPN-30` close is `min(1200, 150 + 40) = 190`, the cap and not the expiry. -/
def sNever : Cand := cand 5 hot2 true (some 150) 1200
def eNever : Cand := cand 6 esc2 false none 1200

/-- A forward excursion that contained a holder decision: a pair that is not hot is requested at
50 and committed at a wall reading of 1000, which advances the ratchet to 1000 under both tables.
The wall then steps back to 100, where `sNever` is accepted and, at 101, opened by its own holder
decision. -/
def neverTrace : List (Env × Input) :=
  [ (envAt 50 50, .request 30 0 (Wall.sample 2000) sp3 es3),
    (envAt 1000 60, .pinless (.receipt 30 1)),
    (envAt 100 70, .request 40 0 (Wall.sample 300) sNever eNever),
    (envAt 101 71, .pinless (.receipt 40 1)) ]

/-- The never-fires residual as a trace (`SPN-30`): the spend is accepted, charged — its
reservation is in the ledger right after the acceptance — listed by `/pending`, and opened, but
its close of 190 is below the ratchet of 1000, which is at or before its expiry of 1200: the band
is `SPN-30`'s cap. The raw reading would have released it at 160. -/
@[req "SPN-30"]
theorem never_fires_with_current :
    respond Kernel.current cfg (envAt 100 70) (runOf Kernel.current tblN (neverTrace.take 2))
      (.accept 40 false (Wall.sample 300) sNever eNever)
      = .accepted 5 (envAt 100 70).eff sNever.fireAt ∧
    (runOf Kernel.current tblN (neverTrace.take 3)).led.any (·.cid == sNever.id) = true ∧
    pending Kernel.current (envAt 100 70) (runOf Kernel.current tblN (neverTrace.take 3)).world.node
      = [sNever.id] ∧
    (runOf Kernel.current tblN neverTrace).world.node.ratchet = (envAt 1000 60).eff ∧
    (envAt 1000 60).eff.atOrBefore sNever.expiry = true ∧
    (runOf Kernel.current tblN neverTrace).world.node.cands.any
      (fun c => c.id == sNever.id && c.quorum) = true ∧
    (runOf withdrawnReadTime tblN neverTrace).world.node.cands.any
      (fun c => c.id == sNever.id &&
        due withdrawnReadTime (envAt 160 80) (runOf withdrawnReadTime tblN neverTrace).world.node c) = true := by
  decide +kernel

/-- And it is due at no sample whatever: its window is shut at the ratchet, so
`Kernel.never_due_below_ratchet` refuses it for every environment, and no later state lowers the
ratchet (`Kernel.ratchet_never_lowered`). -/
@[req "SPN-30"]
theorem never_fires_never_due (env : Env) :
    ∀ c ∈ (runOf Kernel.current tblN neverTrace).world.node.cands, c.id = sNever.id →
      due Kernel.current env (runOf Kernel.current tblN neverTrace).world.node c = false := by
  have h : (runOf Kernel.current tblN neverTrace).world.node.cands.all (fun c =>
      c.id != sNever.id || (c.hot && !windowOpen (runOf Kernel.current tblN neverTrace).world.node.ratchet
        (runOf Kernel.current tblN neverTrace).world.node.combineSlack c)) = true := by
    decide +kernel
  intro c hc hid
  have hc' := List.all_eq_true.1 h c hc
  simp only [hid, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hc'
  exact never_due_below_ratchet rfl hc'.1 hc'.2 env

/-! ### `F68`'s ordinary-record route: a late ordinary decision on an armed node

`DUR-13` says the start is "the seed `max(ratchet, now)`, read at `DUR-7`'s time ratchet,
lowered to the `first_seen` of each record naming the same spend commitment whose own duress bit
is set". An ordinary record therefore cannot start the countdown before a duress PIN was
presented. Every SpendRequest's spend below is hot, since `CHN-32` says "A SpendRequest whose spend
is any class other than hot MUST be refused", and every hot `fire_at` lies past the `T` the arm
writes, at the arm, at each acceptance and at each holder decision. `F68`'s two other routes, a hot
candidate whose window shut unfired and a replay of an old hot spend, are closed by `DUR-13`'s hot
domain, and the section on it below runs both. -/

/-- A pair that is not hot, so `DUR-13`'s scan finds no hot candidate when it is decided. -/
def s68 : Cand := cand 9 { id := 302, inputs := [6], outflow := 0 } false none 900
def e68 : Cand := cand 10 { id := 303, inputs := [6, 7], outflow := 0 } false none 900

/-- The old ordinary pair and a duress pair, each hot with `fire_at` 800 and an expiry of 900. -/
def sOld : Cand := cand 41 { id := 340, inputs := [40], outflow := 10 } true (some 800) 900
def eOld : Cand := cand 42 { id := 341, inputs := [40, 41], outflow := 0 } false none 900
def sArm : Cand := cand 43 { id := 342, inputs := [42], outflow := 10 } true (some 800) 900
def eArm : Cand := cand 44 { id := 343, inputs := [42, 43], outflow := 0 } false none 900

/-- `F68`'s resubmission. The old pair is requested at 10 under PIN 0, ordinary in both tables,
and committed at 20; its nonce tombstone keeps `first_seen` 10 (`NCH-40`). The duress pair is
requested at 500 under PIN 1 and committed at 510, writing `T = max(min(500 + 200, 800 − 5), 510)
= 700` and arming the first world. At 520 the old pair is resubmitted under a fresh nonce and the
same PIN 1, the one the victim gave, whose class the coercer does not know; it is decided at 530,
and a fire pass follows at 531. With `refused` the resubmission is a refused Carrier bound to the
old pair instead. -/
def resubmitTrace (refused : Bool) : List (Env × Input) :=
  [ (envAt 10 10, .request 40 0 (Wall.sample 900) sOld eOld),
    (envAt 20 20, .pinless (.receipt 40 1)),
    (envAt 500 500, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt 510 510, .pinless (.receipt 41 1)),
    (envAt 520 520, if refused then .refusal 42 1 (Wall.sample 900) (some (sOld.id, eOld.id))
                    else .request 42 1 (Wall.sample 900) sOld eOld),
    (envAt 530 530, .pinless (.receipt 42 1)),
    (envAt 531 531, .pinless .firePass) ]

/-- `F68`'s resubmission on the kernel as it stands. The old pair's tombstone still holds
`first_seen` 10 when the resubmission arrives, but its duress bit is clear, and `DUR-13` says "a
record's own duress bit masks only its contribution": the decision at 530 starts at the resubmission's own 520 in the armed world, computes
`min(520 + 200, 800 − 5) = 720`, and writes `max(min(700, 720), 530) = 700`, where the arm put it.
Both runs are inside the concealment horizon on every step of the trace. Started at the old
`first_seen`, the same decision would compute 210 and write `now`, 530, due at once in one world
and not in the other. -/
@[req "DUR-13"]
theorem f68_resubmission_keeps_T :
    ∀ refused : Bool,
    let tr := resubmitTrace refused
    (runOf Kernel.current tblD (tr.take 5)).world.node.tombstones.any
      (fun k => k.cid == 40 && k.firstSeen == (envAt 10 10).eff) = true ∧
    (runOf Kernel.current tblD (tr.take 5)).world.node.carriers.any
      (fun k => k.cid == 42 && k.accepted == !refused) = true ∧
    (runOf Kernel.current tblD (tr.take 4)).world.node.T = Wall.sample 700 ∧
    (runOf Kernel.current tblD (tr.take 4)).world.node.armed = true ∧
    (runOf Kernel.current tblD (tr.take 6)).world.node.T = Wall.sample 700 ∧
    allPreHorizon Kernel.current tblD tr = true ∧
    allPreHorizon Kernel.current tblN tr = true := by
  decide +kernel

/-- A late ordinary decision. A request under PIN 2, a wrong PIN under both tables, is refused
`BAD_PIN` at 5. `SPN-5` says of gate 12 "arm hook records intent (`DUR-4`) — never fails", and it
runs before gate 14's refusal, which stages it; and no spend commitment is computed yet, so the intent
is unbound. The duress pair is requested at 500 and committed at 510, writing `T = 700` and arming
the first world. The wrong-PIN intent's holder decision lands at 530, 525 seconds after its
ingress, and a fire pass follows at 531. -/
def wrongPinTrace : List (Env × Input) :=
  [ (envAt 5 5, .refusal 50 2 (Wall.sample 900) none),
    (envAt 500 500, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt 510 510, .pinless (.receipt 41 1)),
    (envAt 530 530, .pinless (.receipt 50 1)),
    (envAt 531 531, .pinless .firePass) ]

/-- The late ordinary decision on the kernel as it stands. `DUR-13`: "An unbound intent reads only
its own record: the seed, lowered to its own `first_seen` if its own duress bit is set." The wrong-PIN
intent's bit is clear, so its decision at 530 starts at the seed `max(510, 530) = 530`, computes
`min(530 + 200, 800 − 5) = 730`, and the armed world writes `max(min(700, 730), 530) = 700`. Both
runs are inside the concealment horizon on every step. Started at its own `first_seen`, 5, the
decision would compute 205 and write `now`, 530. -/
@[req "DUR-13"]
theorem late_ordinary_decision_keeps_T :
    (runOf Kernel.current tblD (wrongPinTrace.take 3)).world.node.T = Wall.sample 700 ∧
    (runOf Kernel.current tblD (wrongPinTrace.take 3)).world.node.armed = true ∧
    (runOf Kernel.current tblD (wrongPinTrace.take 4)).world.node.T = Wall.sample 700 ∧
    allPreHorizon Kernel.current tblD wrongPinTrace = true ∧
    allPreHorizon Kernel.current tblN wrongPinTrace = true := by
  decide +kernel

/-! ### `DUR-13`'s and `DUR-14`'s hot domain: only hot spends still in play cap `T`

`DUR-13`'s `earliest_hot` ranges over its hot domain, `DUR-13`'s "candidate is hot, not broadcast,
fire window not closed at max(ratchet, now)", and `DUR-14` says "`T ← max(min(T, its fire_at −
epsilon_secs), now)` when the candidate the acceptance leaves registered is in `DUR-13`'s hot
domain, and `T` is retained when it is not". Every
SpendRequest's spend below is hot, since `CHN-32` says "A SpendRequest whose spend is any class
other than hot MUST be refused". Two guards carry the section: `Kernel.HotDomain`, which
candidates are in the domain, and `Kernel.AcceptRead`, which candidate `DUR-14`'s update reads.
The first exhibit goes red under the withdrawn read, `AcceptRead.request`, and the three after it
under the withdrawn domain, `HotDomain.unexpired`; the four after them hold under every value of
both guards, so a rule that drops every hot candidate fails them. The floor of `SEC-37` closes the
section. -/

/-- An old hot pair: `fire_at` 480, its window `[480, 520]`. -/
def sB : Cand := cand 45 { id := 344, inputs := [44], outflow := 10 } true (some 480) 900
def eB : Cand := cand 46 { id := 345, inputs := [44, 45], outflow := 0 } false none 900

/-- `sB`'s pair requested at 400 under PIN 0, ordinary in both tables, and committed at 410; at 480
a fire pass releases its partial, a peer's partial completes the held set, and this node assembles
and broadcasts it. The duress pair is requested at 490 under PIN 1 and committed at 500, arming the
first world; `sB`, broadcast, is outside the hot domain at the arm. At 505 the old pair is replayed
under a fresh nonce and PIN 1, while its window is still open at effective time and at the ratchet;
then a fire pass at 506. -/
def replayTrace : List (Env × Input) :=
  [ (envAt 400 400, .request 60 0 (Wall.sample 900) sB eB),
    (envAt 410 410, .pinless (.receipt 60 1)),
    (envAt 480 480, .pinless .firePass),
    (envAt 480 480, .pinless (.receivePartial (sighash sB.tx 0) 0 1 sB.id)),
    (envAt 480 480, .pinless (.packageAccepted sB.id)),
    (envAt 480 480, .pinless (.send sB.id)),
    (envAt 490 490, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt 500 500, .pinless (.receipt 41 1)),
    (envAt 505 505, .request 61 1 (Wall.sample 900) sB eB),
    (envAt 506 506, .pinless .firePass) ]

/-- The replay after the arm holds `T`, through the resident. The arm writes `T = max(min(490 +
200, 800 − 5), 500) = 690`. The replay is a repeat, and `DUR-14` says "a repeat reads the
resident's `fire_at` and whether the resident is in the domain, never the request's": the resident
is broadcast, so `T` stays at 690. The request's own candidate is not broadcast and its window
`[480, 520]` is open at 505, so a read of the request would write `max(min(690, 480 − 5), 505) =
505`, as the withdrawn read, `Kernel.AcceptRead.request`, does. Both runs are inside the concealment horizon on every step. -/
@[req "DUR-14"]
theorem replay_keeps_T_through_resident :
    (runOf Kernel.current tblD (replayTrace.take 6)).world.node.cands.any
      (fun c => c.id == sB.id && c.broadcast) = true ∧
    (runOf Kernel.current tblD (replayTrace.take 8)).world.node.T = Wall.sample 690 ∧
    (runOf Kernel.current tblD (replayTrace.take 9)).world.node.T = Wall.sample 690 ∧
    allPreHorizon Kernel.current tblD replayTrace = true ∧
    allPreHorizon Kernel.current tblN replayTrace = true := by
  decide +kernel

/-- An old hot pair whose window `[100, 140]` shuts unfired. -/
def sU : Cand := cand 47 { id := 346, inputs := [46], outflow := 10 } true (some 100) 900
def eU : Cand := cand 48 { id := 347, inputs := [46, 47], outflow := 0 } false none 900

/-- `sU`'s pair requested at 10 under PIN 0 and committed at 20, and no fire pass while its window
is open; the duress pair requested at 500 and committed at 510; a fire pass at 511. -/
def unfiredTrace : List (Env × Input) :=
  [ (envAt 10 10, .request 62 0 (Wall.sample 900) sU eU),
    (envAt 20 20, .pinless (.receipt 62 1)),
    (envAt 500 500, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt 510 510, .pinless (.receipt 41 1)),
    (envAt 511 511, .pinless .firePass) ]

/-- The first arm with a hot spend whose window shut unfired. `sU`'s window `[100, 140]` is closed
at 510, so it is outside the hot domain, and the arm writes `T = min(500 + 200, 800 − 5) = 700`.
The withdrawn scan, which reads `sU`'s expiry of 900 and not its window, writes `max(100 − 5, 510)
= 510`, `now`. Both runs are inside the concealment horizon on every step. -/
@[req "DUR-13"]
theorem shut_unfired_spend_keeps_first_arm :
    (runOf Kernel.current tblD (unfiredTrace.take 4)).world.node.T = Wall.sample 700 ∧
    allPreHorizon Kernel.current tblD unfiredTrace = true ∧
    allPreHorizon Kernel.current tblN unfiredTrace = true := by
  decide +kernel

/-- A hot pair with `fire_at` 800. -/
def sK : Cand := cand 49 { id := 348, inputs := [48], outflow := 10 } true (some 800) 900
def eK : Cand := cand 50 { id := 349, inputs := [48, 49], outflow := 0 } false none 900

/-- `sU`'s pair requested at 10 and committed at 20; `sK` accepted at 150, which advances the time
ratchet to 150, past `sU`'s close at 140; then the wall steps back to 120, inside `sU`'s old
window, where the duress pair is requested, and its holder decision lands at 125; a fire pass at
126. -/
def revivedTrace : List (Env × Input) :=
  [ (envAt 10 10, .request 62 0 (Wall.sample 900) sU eU),
    (envAt 20 20, .pinless (.receipt 62 1)),
    (envAt 150 150, .request 63 0 (Wall.sample 900) sK eK),
    (envAt 120 160, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt 125 165, .pinless (.receipt 41 1)),
    (envAt 126 166, .pinless .firePass) ]

/-- A backward step past the ratchet does not bring a shut window back. `DUR-13` says "a backward
wall step does not bring a shut window back, since the close reads at or above the ratchet": at
the decision the close reads `max(150, 125)`, past `sU`'s 140, and the arm writes `T = max(min(120
+ 200, 800 − 5), 125) = 320` from the duress intent's own `first_seen`. Read at effective time,
125 is inside `[100, 140]` and the arm would write `max(100 − 5, 125) = 125`, which the withdrawn
domain also writes. Both runs are inside the concealment horizon on every step. -/
@[req "DUR-13"]
theorem backward_step_keeps_window_shut :
    (runOf Kernel.current tblD (revivedTrace.take 3)).world.node.ratchet = (envAt 150 150).eff ∧
    (runOf Kernel.current tblD (revivedTrace.take 5)).world.node.T = Wall.sample 320 ∧
    allPreHorizon Kernel.current tblD revivedTrace = true ∧
    allPreHorizon Kernel.current tblN revivedTrace = true := by
  decide +kernel

/-- `sU`'s pair requested at 10 and committed at 20, then the duress pair requested at 50 and its
holder decision at `d`. -/
def edgeTrace (d : Nat) : List (Env × Input) :=
  [ (envAt 10 10, .request 62 0 (Wall.sample 900) sU eU),
    (envAt 20 20, .pinless (.receipt 62 1)),
    (envAt 50 50, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt d d, .pinless (.receipt 41 1)) ]

/-- One second past the close. The arm at 141 reads `sU`'s window `[100, 140]` closed and writes
`T = min(50 + 200, 800 − 5) = 250`; the withdrawn domain writes `max(100 − 5, 141) = 141`. -/
@[req "DUR-13"]
theorem arm_past_close_not_capped :
    (runOf Kernel.current tblD (edgeTrace 141)).world.node.T = Wall.sample 250 := by
  decide +kernel

/-- At the close. The arm at 140, the last second of `sU`'s window `[100, 140]`, reads it as not
closed, and `sU` caps the arm: `T = max(min(250, 100 − 5), 140) = 140`, `now`, under every value of
both guards. -/
@[req "DUR-13"]
theorem arm_at_close_is_capped :
    (runOf Kernel.current tblD (edgeTrace 140)).world.node.T = Wall.sample 140 := by
  decide +kernel

/-- Before `fire_at`. `DUR-13` says "a candidate before its `fire_at` has not closed": the arm at
60, forty seconds before `sU`'s `fire_at` of 100, is capped by it, `T = max(min(250, 100 − 5), 60) =
95`, under every value of both guards. -/
@[req "DUR-13"]
theorem arm_before_fire_at_is_capped :
    (runOf Kernel.current tblD (edgeTrace 60)).world.node.T = Wall.sample 95 := by
  decide +kernel

/-- A hot pair with `fire_at` 600, its window `[600, 640]`. -/
def sL : Cand := cand 51 { id := 350, inputs := [50], outflow := 10 } true (some 600) 900
def eL : Cand := cand 52 { id := 351, inputs := [50, 51], outflow := 0 } false none 900

/-- `sL`'s pair requested at 400 under PIN 0 and committed at 410; the duress pair requested at
500 and committed at 510; `sL`'s pair replayed at 520 under PIN 1 and decided at 530. -/
def liveReplayTrace : List (Env × Input) :=
  [ (envAt 400 400, .request 64 0 (Wall.sample 900) sL eL),
    (envAt 410 410, .pinless (.receipt 64 1)),
    (envAt 500 500, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt 510 510, .pinless (.receipt 41 1)),
    (envAt 520 520, .request 65 1 (Wall.sample 900) sL eL),
    (envAt 530 530, .pinless (.receipt 65 1)) ]

/-- A replay of a spend still in the hot domain caps `T` at its `fire_at − epsilon_secs`: `sL`,
before its `fire_at`, caps the arm at `min(500 + 200, 600 − 5) = 595`, and the replay, whose
resident is in the domain, and its holder decision leave `T` at 595, under every value of both
guards. -/
@[req "DUR-14"]
theorem live_replay_caps_T :
    (runOf Kernel.current tblD (liveReplayTrace.take 4)).world.node.T = Wall.sample 595 ∧
    (runOf Kernel.current tblD (liveReplayTrace.take 5)).world.node.T = Wall.sample 595 ∧
    (runOf Kernel.current tblD liveReplayTrace).world.node.T = Wall.sample 595 := by
  decide +kernel

/-- A hot pair with `fire_at` 480, its window `[480, 520]`, and a claw-back over its input. -/
def sW : Cand := cand 53 { id := 352, inputs := [52], outflow := 10 } true (some 480) 900
def eW : Cand := cand 54 { id := 353, inputs := [52, 53], outflow := 0 } false none 900
def clawW : Tx := { id := 399, inputs := [52], outflow := 0 }

/-- `sW`'s pair requested at 400 under PIN 0 and committed at 410; at 490, inside its window,
`sW`'s own transaction is seen, broadcast by another node, or with `claw` the claw-back is; the
duress pair requested at 500 and committed at 510. -/
def settledTrace (claw : Bool) : List (Env × Input) :=
  [ (envAt 400 400, .request 66 0 (Wall.sample 900) sW eW),
    (envAt 410 410, .pinless (.receipt 66 1)),
    (envAt 490 490 [if claw then clawW else sW.tx], .pinless (.settle (if claw then clawW else sW.tx))),
    (envAt 500 500, .request 41 1 (Wall.sample 900) sArm eArm),
    (envAt 510 510, .pinless (.receipt 41 1)) ]

/-- A settled hot spend whose window is still open caps the arm. `SEC-37` says "whether or not it
can still fire": `sW`, settled (`SPN-33`) or made terminal by the claw-back at 490, its window
`[480, 520]` open at 510, stays in the hot domain, and the arm writes `T = max(min(500 + 200,
480 − 5), 510) = 510`, `now`, under every value of both guards. -/
@[req "SEC-37"]
theorem settled_spend_in_window_caps_arm :
    ∀ claw : Bool,
    (runOf Kernel.current tblD ((settledTrace claw).take 3)).world.node.cands.any
      (fun c => c.id == sW.id && (c.settled || c.terminal)) = true ∧
    (runOf Kernel.current tblD (settledTrace claw)).world.node.T = Wall.sample 510 := by
  decide +kernel

/-- Node `A` with `hold_secs` `h`, so that `SPN-30`'s "A hot-class spend's fire time is
`ingress_now + hold_secs`" and `SPN-38`'s HotClock check agree on every hot spend below. -/
def holdSys (h : Nat) : Sys := { world := { node := { A with holdSecs := h }, exposure := [] }, led := [] }

def runHold (h : Nat) (r : Rules) (tbl : Enrolment) (tr : List (Env × Input)) : Sys :=
  (sysRun Ledger.current cfg r (holdSys h) (tr.map fun x => (x.1, x.2.event tbl))).1

def holdPreHorizon (h : Nat) (r : Rules) (tbl : Enrolment) (tr : List (Env × Input)) : Bool :=
  tr.zipIdx.all fun ((env, _), j) => preHorizon r env (runHold h r tbl (tr.take j)).world.node

/-- Four hot pairs, each with `fire_at` its ingress plus `h`: one requested at 10, one at 30, the
duress pair at 500 and a later one at 540. -/
def fU (h : Nat) : Cand := cand 61 { id := 360, inputs := [60], outflow := 10 } true (some (10 + h)) 900
def gU : Cand := cand 62 { id := 361, inputs := [60, 61], outflow := 0 } false none 900
/-- An ordinary acceptance of `fU 300` at effective time 10, then an accepted repeat at 30
under a fresh nonce. Under `Registration.preserve`, while the pair is resident, request records
carrying fire times 310, 330 and none answer with the recorded instants 10 and 310. -/
@[req "SPN-34"]
def acceptanceTimesTrace (f : Option Wall) : List (Env × Input) :=
  [(envAt 10 10, .request 71 0 (Wall.sample 900) (fU 300) gU),
   (envAt 30 30, .request 72 0 (Wall.sample 900) { fU 300 with fireAt := f } gU)]

@[req "SPN-34"]
theorem accepted_repeat_keeps_instants :
    [some (Wall.sample 310), some (Wall.sample 330), none].all (fun f =>
      let os := obsPair Silence.current Ledger.current cfg Kernel.current tblN tblN
        (holdSys 300) (holdSys 300) (acceptanceTimesTrace f)
      os.length == 2 && os.map (·.1.resp) ==
        [.accepted 61 (envAt 10 10).eff (some (Wall.sample 310)),
         .accepted 61 (envAt 10 10).eff (some (Wall.sample 310))]) = true := by
  decide +kernel

def fB (h : Nat) : Cand := cand 63 { id := 362, inputs := [62], outflow := 10 } true (some (30 + h)) 900
def gB : Cand := cand 64 { id := 363, inputs := [62, 63], outflow := 0 } false none 900
def fD (h : Nat) : Cand := cand 65 { id := 364, inputs := [64], outflow := 10 } true (some (500 + h)) 900
def gD : Cand := cand 66 { id := 365, inputs := [64, 65], outflow := 0 } false none 900
def fC (h : Nat) : Cand := cand 67 { id := 366, inputs := [66], outflow := 10 } true (some (540 + h)) 900
def gC : Cand := cand 68 { id := 367, inputs := [66, 67], outflow := 0 } false none 900

/-- Every ordinary route in one trace. A wrong-PIN request at 5, refused and staged unbound; `fU`'s
pair at 10, committed at 20, its partial released at `fB`'s fire pass, which falls inside `fU`'s
window `[10 + h, 50 + h]`, and never broadcast, its window closed before the arm; `fB`'s pair at
30, committed at 40, fired and broadcast by this node at `30 + h`. Then `F`: the duress pair at
500, committed at 510. Then `fB`'s pair replayed at 520 under PIN 1, `fU`'s resubmitted at 525
under PIN 1 and decided at 530, the wrong-PIN Carrier's holder decision at 535, `fC`'s pair at 540,
and a fire pass at 541. -/
def floorTrace (h : Nat) : List (Env × Input) :=
  [ (envAt 5 5, .refusal 70 2 (Wall.sample 900) none),
    (envAt 10 10, .request 71 0 (Wall.sample 900) (fU h) gU),
    (envAt 20 20, .pinless (.receipt 71 1)),
    (envAt 30 30, .request 72 0 (Wall.sample 900) (fB h) gB),
    (envAt 40 40, .pinless (.receipt 72 1)),
    (envAt (30 + h) (30 + h), .pinless .firePass),
    (envAt (30 + h) (30 + h), .pinless (.receivePartial (sighash (fB h).tx 0) 0 1 (fB h).id)),
    (envAt (30 + h) (30 + h), .pinless (.packageAccepted (fB h).id)),
    (envAt (30 + h) (30 + h), .pinless (.send (fB h).id)),
    (envAt 500 500, .request 73 1 (Wall.sample 900) (fD h) gD),
    (envAt 510 510, .pinless (.receipt 73 1)),
    (envAt 520 520, .request 74 1 (Wall.sample 900) (fB h) gB),
    (envAt 525 525, .request 75 1 (Wall.sample 900) (fU h) gU),
    (envAt 530 530, .pinless (.receipt 75 1)),
    (envAt 535 535, .pinless (.receipt 70 1)),
    (envAt 540 540, .request 76 0 (Wall.sample 900) (fC h) gC),
    (envAt 541 541, .pinless .firePass) ]

/-- The floor, `SEC-37`'s "once armed, `T` stays at or above `F + min(duress_delay_secs, hold_secs −
epsilon_secs)`". With `F = 500`, `duress_delay_secs` 200 and `epsilon_secs` 5: at `hold_secs` 300
the delay is the smaller arm, the floor is 700, and the arm writes `min(500 + 200, 800 − 5) = 700`;
at `hold_secs` 100 the Hold is, the floor is `500 + 100 − 5 = 595`, and through the duress pair's
own hot spend the arm writes `max(min(700, 600 − 5), 510) = 595`. In both, the replay of the
broadcast spend, `fU`, released and never broadcast with its window closed, its resubmission, the late
wrong-PIN decision and the later hot spend leave `T` there to the end, both runs inside the
concealment horizon. The withdrawn domain, which reads `fU`'s expiry of 900 and not its window,
writes `max(min(700, 10 + h − 5, 500 + h − 5), 510) = 510` at the arm, through `fU`. The withdrawn
read, which reads the replay's own `fire_at`, `30 + h`, and not the broadcast resident, writes
`max(min(T, 30 + h − 5), 520) = 520` at the replay. -/
@[req "SEC-37"]
theorem floor_holds_on_ordinary_routes :
    ∀ h ∈ [100, 300],
      ((List.range 7).map fun k => (runHold h Kernel.current tblD ((floorTrace h).take (k + 11))).world.node.T)
        = List.replicate 7 (Wall.sample (500 + min 200 (h - 5))) ∧
      holdPreHorizon h Kernel.current tblD (floorTrace h) = true ∧
      holdPreHorizon h Kernel.current tblN (floorTrace h) = true := by
  simp only [List.mem_cons, forall_eq_or_imp]
  decide +kernel

/-- `floorTrace 300`'s first eleven steps, which arm the first run at 510 with `T = 700`, then a
request at 520 under PIN 1 refused at gate 24 with `HOT_VELOCITY_EXCEEDED` whose computed pair is
`(80, 61)`: its Escape id is `fU`'s, the hot spend released at `fB`'s fire pass and never
broadcast, whose window `[310, 350]` had closed at the arm. Its holder decision at 525, then two
unbound refusals at 530 and 540 and their holder decisions at 535 and 545. -/
def crossedFloorTrace : List (Env × Input) :=
  (floorTrace 300).take 11 ++
  [ (envAt 520 520, .refusal 90 1 (Wall.sample 900) (some (80, (fU 300).id)) .HOT_VELOCITY_EXCEEDED),
    (envAt 525 525, .pinless (.receipt 90 1)),
    (envAt 530 530, .refusal 91 2 (Wall.sample 900) none),
    (envAt 535 535, .pinless (.receipt 91 1)),
    (envAt 540 540, .refusal 92 2 (Wall.sample 900) none),
    (envAt 545 545, .pinless (.receipt 92 1)) ]

/-- The floor on a crossed refusal, `SEC-37`'s "once armed, `T` stays at or above `F +
min(duress_delay_secs, hold_secs − epsilon_secs)`", at `hold_secs` 300, where the floor is 700. The
decision at 525 inserts `fU`'s id, and the entry acts only on a candidate registered in the
Escape role (`Kernel.entryActs`), which `fU` is not: `fU` keeps its window and stays outside the
hot domain, and `T` reads 700 after every step from the arm to the end, both runs inside the
concealment horizon. Under the withdrawn `Kernel.EntryTarget.idAlone` the decision at 525 writes
`fU`'s window `[700, 740]`, which puts it back in the hot domain, and the two later decisions walk
`T` down to 695 and then 690. -/
@[req "SEC-37"]
theorem floor_holds_on_crossed_refusal :
    ((List.range 7).map fun k =>
        (runHold 300 Kernel.current tblD (crossedFloorTrace.take (k + 11))).world.node.T)
      = List.replicate 7 (Wall.sample 700) ∧
    holdPreHorizon 300 Kernel.current tblD crossedFloorTrace = true ∧
    holdPreHorizon 300 Kernel.current tblN crossedFloorTrace = true := by
  decide +kernel

/-- The same eleven steps under the table that makes every PIN ordinary, so nothing arms, then a
request at 520 under PIN 0 refused at gate 24 with `HOT_VELOCITY_EXCEEDED` whose computed pair is
`(80, 65)`: its Escape id is `fD`'s, the hot spend of the pair requested at 500, `fire_at` 800.
Its holder decision at 525, and a fire pass at 800. -/
def crossedPaymentTrace : List (Env × Input) :=
  (floorTrace 300).take 11 ++
  [ (envAt 520 520, .refusal 99 0 (Wall.sample 900) (some (80, (fD 300).id)) .HOT_VELOCITY_EXCEEDED),
    (envAt 525 525, .pinless (.receipt 99 1)),
    (envAt 800 800, .pinless .firePass) ]

/-- A crossed refusal stops no payment: the decision at 525 inserts `fD`'s id with a clear bit,
the entry acts on no candidate in the spend role, and the fire pass at 800, `fD`'s `fire_at`,
releases `fD`. Under the withdrawn `Kernel.EntryTarget.idAlone` that decision writes `fD`'s window
`[725, 765]` and gates its release on the clear entry, and `fD` is not released at 800. -/
@[req "DUR-10"]
theorem crossed_refusal_spend_releases_at_fire :
    (runHold 300 Kernel.current tblN crossedPaymentTrace).world.node.cands.any
      (fun c => c.id == (fD 300).id && c.released) = true := by
  decide +kernel

/-- A pair whose Escape is selected while resident, both expiring at 400, and a later hot pair
whose spend carries that Escape's id, `fire_at` 760. -/
def sPruned : Cand := cand 60 { id := 350, inputs := [50], outflow := 10 } true (some 310) 400
def ePruned : Cand := cand 61 { id := 351, inputs := [50, 51], outflow := 0 } false none 400
/-- The kernel's collection route: a Carrier expiring at 900 accepts members expiring at
400, a prune pass at 450 collects them, and the same pair is accepted at 460 under nonce 72
with the spend record's fire time changed to 350, passing gate 27 (`SPN-30`) at expiry 400
with slack 40. Under `Registration.preserve` the pair is born afresh. Its fire time precedes its
new first-seen instant; the Carrier's expiry outlives the members', unlike the text's one request expiry;
this trace claims nothing about a node following the text. -/
@[req "SPN-34"]
def acceptanceTimesAfterPrune : List (Env × Input) :=
  [(envAt 10 10, .request 71 0 (Wall.sample 900) sPruned ePruned),
   (envAt 450 450, .pinless .prune),
   (envAt 460 460, .request 72 0 (Wall.sample 900)
     { sPruned with fireAt := some (Wall.sample 350) } ePruned)]

@[req "SPN-34"]
theorem collected_pair_records_new_instants :
    (runHold 300 Kernel.current tblN (acceptanceTimesAfterPrune.take 2)).world.node.cands = [] ∧
    (obsPair Silence.current Ledger.current cfg Kernel.current tblN tblN (holdSys 300)
      (holdSys 300) acceptanceTimesAfterPrune).map (·.1.resp) =
      [.accepted 60 (envAt 10 10).eff (some (Wall.sample 310)), .silent,
       .accepted 60 (envAt 460 460).eff (some (Wall.sample 350))] := by
  decide +kernel

def sReused : Cand := cand 61 { id := 368, inputs := [68], outflow := 10 } true (some 760) 900
def eReused : Cand := cand 62 { id := 369, inputs := [68, 69], outflow := 0 } false none 900

/-- The first pair requested at 10 and committed at 20, which selects Escape 61; a prune pass at
450, past the pair's expiry 400 and its Escape's closed window, which removes it; the second pair
requested at 460 and committed at 470; the duress pair requested at 500 and committed at 510,
which arms the first run with `T = 700`; an unbound refusal at 520 and its holder decision at 525;
a fire pass at 760, the reused spend's `fire_at`. -/
def reusedIdTrace : List (Env × Input) :=
  [ (envAt 10 10, .request 71 0 (Wall.sample 900) sPruned ePruned),
    (envAt 20 20, .pinless (.receipt 71 1)),
    (envAt 450 450, .pinless .prune),
    (envAt 460 460, .request 77 0 (Wall.sample 900) sReused eReused),
    (envAt 470 470, .pinless (.receipt 77 1)),
    (envAt 500 500, .request 73 1 (Wall.sample 900) (fD 300) gD),
    (envAt 510 510, .pinless (.receipt 73 1)),
    (envAt 520 520, .refusal 91 2 (Wall.sample 900) none),
    (envAt 525 525, .pinless (.receipt 91 1)),
    (envAt 760 760, .pinless .firePass) ]

/-- A pruned selected Escape's id comes back as a hot spend's: the set still holds 61, and the
spend registered under it is in the spend role, so no entry acts on it. `T` reads 700 after the
arm, after the refusal and after its decision, both runs inside the concealment horizon through
those nine steps, and under the ordinary table the fire pass at 760 releases the spend. Under the
withdrawn `Kernel.EntryTarget.idAlone` `T` reads 510, 510 and 525 there, and the spend is not
released. This route is the kernel's: its ids are abstract, so nothing stops one from naming two
transactions. In the text one id is one transaction, since `CHN-24` says "Two distinct transactions
MUST never share a commitment", and that transaction has one class: `CHN-30` says "The escape test
MUST run before the hot test for each output", and an Escape passes `SPN-27`'s "prefixed
`escape:`, then require escape-class", so an Escape's id never names a hot spend. -/
@[req "DUR-13"]
theorem reused_id_spend_keeps_floor_and_releases :
    ((List.range 3).map fun k =>
        (runHold 300 Kernel.current tblD (reusedIdTrace.take (k + 7))).world.node.T)
      = List.replicate 3 (Wall.sample 700) ∧
    holdPreHorizon 300 Kernel.current tblD (reusedIdTrace.take 9) = true ∧
    holdPreHorizon 300 Kernel.current tblN (reusedIdTrace.take 9) = true ∧
    (runHold 300 Kernel.current tblN reusedIdTrace).world.node.cands.any
      (fun c => c.id == sReused.id && c.released) = true := by
  decide +kernel

/-- A hot spend under the pruned selected Escape's id, 61, with `fire_at` 400 and expiry 900, its
request record carrying the given `pair` field. -/
def sClosed (pair : Option (Nat × Nat)) : Cand :=
  { cand 61 { id := 368, inputs := [68], outflow := 10 } true (some 400) 900 with pair := pair }

/-- `reusedIdTrace`'s first three steps, which select Escape 61 and prune its pair at 450; the
duress pair requested at 500 and committed at 510, which arms the first run with `T = 700`; then
at 520, under PIN 0, `sClosed pair` beside `eReused`: a hot spend under id 61 whose window
`[400, 440]` is closed at 520. -/
def requestPairTrace (pair : Option (Nat × Nat)) : List (Env × Input) :=
  reusedIdTrace.take 3 ++
  [ (envAt 500 500, .request 73 1 (Wall.sample 900) (fD 300) gD),
    (envAt 510 510, .pinless (.receipt 73 1)),
    (envAt 520 520, .request 77 0 (Wall.sample 900) (sClosed pair) eReused) ]

/-- The acceptance at 520 on `requestPairTrace`, with the request record's `pair` left at `none`
and with it set to `some (0, 61)`, which names the record itself the Escape of a pair. Under
either, the spend is registered in the spend role under id 61, which the selected set still holds:
no entry acts on it, its window is closed at `max(ratchet, now) = 520`, so it is outside the hot
domain and `DUR-14`'s update retains `T`, which reads 700 after the arm and after the acceptance,
and the two records leave the same registry. With the update reading the request's own `pair`
field, the second record is read in the Escape role under a selected id, inside the domain whatever
its window: the acceptance writes `max(min(700, 400 − 5), 520) = 520`, below `SEC-37`'s floor of 700
on this trace, and the two registries differ. This route is the kernel's. The text gives a request
no pair or sibling field for the event's incoming `pair` to stand for: `SPN-32` says each resident
has "the request's other id recorded as its sibling". `SPN-30` says "A hot-class spend's fire time
is `ingress_now + hold_secs`", which at `hold_secs` 300 gives a spend ingressed at 520 a `fire_at`
of 820 and not this trace's 400. The id reuse is `reused_id_spend_keeps_floor_and_releases`'s,
argued there. -/
@[req "DUR-14"]
theorem request_pair_keeps_T_and_registry :
    (∀ p ∈ [none, some (0, 61)],
      ((List.range 2).map fun k =>
          (runHold 300 Kernel.current tblD ((requestPairTrace p).take (k + 5))).world.node.T)
        = List.replicate 2 (Wall.sample 700)) ∧
    (runHold 300 Kernel.current tblD (requestPairTrace none)).world.node.cands
      = (runHold 300 Kernel.current tblD (requestPairTrace (some (0, 61)))).world.node.cands := by
  simp only [List.mem_cons, forall_eq_or_imp]
  decide +kernel

/-- A hot spend ingressed at 460 with Hold 300, beside Escape 60 whose request record carries `f`. -/
def sEscapeReuse : Cand := cand 59 { id := 370, inputs := [70], outflow := 10 } true (some 760) 900
def eEscapeReuse (f : Option Wall) : Cand :=
  { cand 60 { id := 371, inputs := [70, 71], outflow := 0 } false none 900 with fireAt := f }

/-- The id-reuse trace `request_escape_fireAt_keeps_effects_and_registry` runs, with Escape 60's
request record carrying `f`. -/
def requestEscapeFireTrace (f : Option Wall) : List (Env × Input) :=
  [ (envAt 10 10, .request 71 0 (Wall.sample 900) sPruned ePruned),
    (envAt 450 450, .pinless .prune),
    (envAt 460 460, .request 77 0 (Wall.sample 900) sEscapeReuse (eEscapeReuse f)),
    (envAt 470 470, .pinless (.receipt 71 1)),
    (envAt 480 480, .pinless .firePass) ]

/-- `requestEscapeFireTrace` requests pair `(60, 61)` at 10, runs a prune pass at 450, and requests
pair `(59, 60)` at 460, followed by Carrier 71's receipt from peer 1 at 470 and a fire pass at 480.
Escape 60's request record gives
`fireAt` `none` in one run and `some 0` in the other. Both records leave the same registry after
each prefix and the same effects, none, through the fire pass at 480, and after the request at
460 candidate 60 holds no fire time under the second record. Every request presents PIN 0,
ordinary under both tables, so the two tables give one event list here.
With the old registration the second record queued a partial for candidate 60,
`Effect.queuePartial (371, 0) 0 false 60`, and an exposed-authority row, on an unarmed node.
This route is the kernel's: `SPN-37` says "The Escape member of a pair is registered with **no**
fire window"; the id-reuse argument is `reused_id_spend_keeps_floor_and_releases`'s, here with
an old hot spend's id returning as an Escape's. -/
@[req "SPN-37"]
theorem request_escape_fireAt_keeps_effects_and_registry :
    ∀ tbl ∈ [tblN, tblD],
    (sysRun Ledger.current cfg Kernel.current (holdSys 300)
      ((requestEscapeFireTrace none).map fun x => (x.1, x.2.event tbl))).2 = [] ∧
    (sysRun Ledger.current cfg Kernel.current (holdSys 300)
      ((requestEscapeFireTrace (some (Wall.sample 0))).map fun x => (x.1, x.2.event tbl))).2 = [] ∧
    (∀ j ∈ List.range 6,
      (runHold 300 Kernel.current tbl ((requestEscapeFireTrace none).take j)).world.node.cands =
        (runHold 300 Kernel.current tbl
          ((requestEscapeFireTrace (some (Wall.sample 0))).take j)).world.node.cands) ∧
    ((runHold 300 Kernel.current tbl ((requestEscapeFireTrace (some (Wall.sample 0))).take 3)
      ).world.node.cands.find? (·.id == 60)).map (·.fireAt) = some none := by
  decide +kernel

/-! ### The removal at `T + combine_slack_secs` (`SPN-41`), on an armed node only -/

/-- A hot spend accepted at 100 and handed `fire_at` 400, 300 seconds later, with an expiry of
1200. Node `A`'s `hold_secs` is 0, so the 300 seconds are the delay to `fire_at` and no Hold. -/
def sLive : Cand := cand 21 hot1 true (some 400) 1200
def eLive : Cand := cand 22 esc1 false none 1200

/-- `sLive` requested at 100 under a PIN both tables make ordinary and committed at 101. Its own
holder decision starts at the seed `max(ratchet, now) = 101`, writes `T = max(min(101 + 200, 400 −
5), 101) = 301` and installs `eLive`'s window `[301, 341]`. A prune pass at 342, past that close
and before both `fire_at` and the expiry, then a fire pass at 400. -/
def liveTrace : List (Env × Input) :=
  [ (envAt 100 100, .request 70 0 (Wall.sample 1200) sLive eLive),
    (envAt 101 101, .pinless (.receipt 70 1)),
    (envAt 342 342, .pinless .prune),
    (envAt 400 400, .pinless .firePass) ]

/-- The removal on an unarmed node would kill an ordinary spend: its pair's Escape is selected,
under a clear bit, with a window that closes at 341, fifty-nine seconds before the spend's own
`fire_at`. On the unarmed node the prune pass at 342 keeps the pair, and the fire pass at 400 queues
the spend's partial: its close, `min(1200, 400 + 40) = 440`, is above the ratchet of 101, and `A`'s
`hold_secs` of 0 leaves the HotClock check satisfied. -/
@[req "SPN-41"]
theorem unarmed_spend_fires_past_close :
    (runOf Kernel.current tblN (liveTrace.take 2)).world.node.armed = false ∧
    (runOf Kernel.current tblN (liveTrace.take 2)).world.node.selected = [(eLive.id, false)] ∧
    windowOf (runOf Kernel.current tblN (liveTrace.take 2)).world.node eLive.id
      = some (some (Wall.sample 301), some (Wall.sample 341)) ∧
    (runOf Kernel.current tblN (liveTrace.take 3)).world.node.cands.map (·.id)
      = [sLive.id, eLive.id] ∧
    (sysRun Ledger.current cfg Kernel.current sys0
        (liveTrace.map fun x => (x.1, x.2.event tblN))).2
      = [.queuePartial (sighash hot1 0) 0 true sLive.id] := by
  decide +kernel

/-- `later_commit_keeps_T`'s trace on the armed run: `s1`'s pair selected under its duress bit and
the ordinary pair `(sp3, es3)` committed after the arm under a clear one, both windows `[250, 290]`.
Then prune passes at 290, at 291 and at 401. -/
def removalTrace : List (Env × Input) :=
  secondPairTrace 0 100 110 ++
  [ (envAt 290 120, .pinless .prune), (envAt 291 130, .pinless .prune),
    (envAt 401 140, .pinless .prune) ]

/-- On the armed node, the prune pass at 290, the last second of the window, removes nothing. The
one at 291 removes both selected Escapes and their spends, `s1` with an expiry of 400 and `sp3`
with one of 900, including the pair whose entry's duress bit is clear: the removal is keyed on the
node's `active` bit, not on the entry's. The pending log keeps `s1`'s entry: `/pending` lists it at
400, its expiry, and not at 401, by the read-time filter, and the prune pass at 401 drops it from
the log. -/
@[req "SPN-41"]
theorem armed_removal_keeps_pending :
    (runOf Kernel.current tblD (removalTrace.take 4)).world.node.armed = true ∧
    (runOf Kernel.current tblD (removalTrace.take 4)).world.node.selected
      = [(2, true), (8, false)] ∧
    (runOf Kernel.current tblD (removalTrace.take 5)).world.node.cands.map (·.id) = [7, 8, 1, 2] ∧
    (runOf Kernel.current tblD (removalTrace.take 6)).world.node.cands = [] ∧
    pending Kernel.current (envAt 400 140) (runOf Kernel.current tblD (removalTrace.take 6)).world.node
      = [s1.id] ∧
    pending Kernel.current (envAt 401 140) (runOf Kernel.current tblD (removalTrace.take 6)).world.node
      = [] ∧
    (runOf Kernel.current tblD removalTrace).world.node.pendingLog.entries = [] := by
  decide +kernel

/-- Every value as it stands but what `/pending` reads, which is `projection`: the registry's hot,
unsettled, not terminal, not broadcast candidates. Each value's trace over every rule is in
`Kernel.PendingCases`. -/
def withdrawnPendingSource : Rules := { Kernel.current with pendingSource := .projection }

/-- Under the withdrawn value the same removal takes `s1` off `/pending` with its candidate: listed
at 290, gone at 291, more than a hundred seconds before its expiry of 400, by a removal that runs on
the armed node alone. `SPN-42` says "Before expiry, an id is removed only on a public network
settlement event (`SPN-33`), never by a PIN-dependent path". -/
@[req "SPN-42"]
theorem removal_drops_pending_with_withdrawn :
    pending withdrawnPendingSource (envAt 290 120)
        (runOf withdrawnPendingSource tblD (removalTrace.take 5)).world.node = [s1.id] ∧
    (runOf withdrawnPendingSource tblD (removalTrace.take 6)).world.node.cands = [] ∧
    pending withdrawnPendingSource (envAt 291 130)
        (runOf withdrawnPendingSource tblD (removalTrace.take 6)).world.node = [] := by
  decide +kernel

/-- `removalTrace` to the removal at 291, then `e1`'s transaction seen at 300, which is `s1`'s
sibling and spends its input: the settlement clears `s1`'s entry, whose candidate the registry no
longer holds, a hundred seconds before its expiry (`SPN-33`, `DUR-33`). Then a replay of the pair
at 310 under a fresh Carrier, which registers it again. -/
def settleTrace : List (Env × Input) :=
  removalTrace.take 6 ++
  [ (envAt 300 135 [esc1], .pinless (.settle esc1)),
    (envAt 310 136, .request 40 0 (Wall.sample 400) s1 e1) ]

/-- After the removal, the settlement removes the entry from `/pending` before its expiry, and the
replay that registers the pair again does not list it again, under `API-21`'s "this node has
accepted and not yet seen settle". -/
@[req "SPN-33"]
theorem settlement_clears_removed_pending :
    (runOf Kernel.current tblD (settleTrace.take 6)).world.node.cands = [] ∧
    pending Kernel.current (envAt 300 135) (runOf Kernel.current tblD (settleTrace.take 6)).world.node
      = [s1.id] ∧
    pending Kernel.current (envAt 300 135) (runOf Kernel.current tblD (settleTrace.take 7)).world.node
      = [] ∧
    (runOf Kernel.current tblD settleTrace).world.node.cands.any (·.id == s1.id) = true ∧
    pending Kernel.current (envAt 310 136) (runOf Kernel.current tblD settleTrace).world.node
      = [] := by
  decide +kernel

/-- A hot spend whose `fire_at` is 362: its window `[362, 402]` has not closed at 400. -/
def sNear : Cand := cand 69 { id := 368, inputs := [68], outflow := 10 } true (some 362) 900
def eNear : Cand := cand 70 { id := 369, inputs := [68, 69], outflow := 0 } false none 900

/-- `s68`'s pair requested at 300 under PIN 1 and committed at 400, which arms the first
world with `T = max(300 + 200, 400) = 500` and advances the ratchet to 400. Then the wall steps
back: `sNear`, its window `[362, 402]` not closed at `max(400, 100)` and so in `DUR-13`'s hot
domain, is accepted at 100, whose acceptance writes `T = max(min(500, 362 − 5), 100) = 357`
(`DUR-14`) and leaves the ratchet at 400. Then a prune pass at 380. -/
def backstepTrace : List (Env × Input) :=
  [ (envAt 300 30, .request 41 1 (Wall.sample 900) s68 e68),
    (envAt 400 40, .pinless (.receipt 41 1)),
    (envAt 100 50, .request 60 0 (Wall.sample 900) sNear eNear),
    (envAt 380 60, .pinless .prune) ]

/-- `SPN-41`: "The close is read at effective time and never at the time ratchet". On the armed
node the ratchet, at 400, is past the close at `357 + 40 = 397`, while the prune pass at 380 is
inside the window `[357, 397]`: the pass keeps `e68`, the selected Escape, and `s68`, its pair.
Read at the ratchet, the removal would delete both while the window is still open on effective
time. -/
@[req "SPN-41"]
theorem removal_closes_on_effective_time :
    let n := (runOf Kernel.current tblD (backstepTrace.take 3)).world.node
    n.armed = true ∧
    n.T = Wall.sample 357 ∧
    n.ratchet = (envAt 400 40).eff ∧
    n.ratchet.atOrBefore (n.T.plus n.combineSlack) = false ∧
    (envAt 380 60).eff.atOrAfter n.T = true ∧
    (envAt 380 60).eff.atOrBefore (n.T.plus n.combineSlack) = true ∧
    (runOf Kernel.current tblD backstepTrace).world.node.cands.any (·.id == e68.id) = true ∧
    (runOf Kernel.current tblD backstepTrace).world.node.cands.any (·.id == s68.id) = true := by
  decide +kernel

/-! ### Gate 27 on a re-signed request (`SPN-30`, `bps-xrv`) -/

/-- The first pair's spend re-signed: the same commitments, transactions, class and expiry, and
the incoming fire time 370, against the expiry 400 with `combine_slack_secs`
40. The resident's recorded fire time, 300, passes; its own does not. -/
def s1Resigned : Cand := { s1 with fireAt := some (Wall.sample 370) }

/-- `armTrace`, then the re-signed request at 70 under nonce 30 and the PIN the first table makes
a duress PIN: the first world is armed with `T = 250`, both inside the horizon. -/
def resignTrace : List (Env × Input) :=
  armTrace ++ [(envAt 70 70, .request 30 1 (Wall.sample 400) s1Resigned e1)]

/-- Gate 27 reads the resident's recorded fire time in both worlds, and the re-signed request is
answered with the first acceptance's instants in both (`SPN-34`). Under the withdrawn
`Kernel.ExpiryRead.request` both worlds refuse it `EXPIRY_TOO_SHORT`. -/
@[req "SPN-30"]
theorem resigned_reads_resident_fire :
    (pairs Silence.current Kernel.current resignTrace).map (fun y => (y.1.resp, y.2.resp)) =
      [(.accepted 1 (envAt 50 50).eff (some (Wall.sample 300)),
        .accepted 1 (envAt 50 50).eff (some (Wall.sample 300))),
       (.ack, .ack),
       (.accepted 1 (envAt 50 50).eff (some (Wall.sample 300)),
        .accepted 1 (envAt 50 50).eff (some (Wall.sample 300)))] := by
  decide +kernel

/-- `armTrace`, then a prune pass at 295, past the first world's `T + combine_slack_secs = 290`:
`SPN-41`'s removal takes the selected pair there and not in the other world. -/
def resignRemovalTrace : List (Env × Input) := armTrace ++ [(envAt 295 295, .pinless .prune)]

/-- Past the horizon, before any Lockdown (the kernel has none at `T`): a re-signed request at 300
whose own fire time fails gate 27 is refused in the armed world, which no longer holds the pair,
and accepted with the first instants in the other. One whose own fire time, 350, passes is answered
with different instants in the two worlds, born afresh in one and retained in the other. -/
@[req "SPN-30"]
theorem resigned_after_removal :
    preHorizon Kernel.current (envAt 295 295) (runOf Kernel.current tblD armTrace).world.node = false ∧
    respond Kernel.current cfg (envAt 300 300) (runOf Kernel.current tblD resignRemovalTrace)
      (.accept 30 true (Wall.sample 400) s1Resigned e1) = .refused .EXPIRY_TOO_SHORT ∧
    respond Kernel.current cfg (envAt 300 300) (runOf Kernel.current tblN resignRemovalTrace)
      (.accept 30 false (Wall.sample 400) s1Resigned e1) =
      .accepted 1 (envAt 50 50).eff (some (Wall.sample 300)) ∧
    respond Kernel.current cfg (envAt 300 300) (runOf Kernel.current tblD resignRemovalTrace)
      (.accept 30 true (Wall.sample 400) { s1 with fireAt := some (Wall.sample 350) } e1) =
      .accepted 1 (envAt 300 300).eff (some (Wall.sample 350)) ∧
    respond Kernel.current cfg (envAt 300 300)
      (runOf Kernel.current tblN resignRemovalTrace)
      (.accept 30 false (Wall.sample 400) { s1 with fireAt := some (Wall.sample 350) } e1) =
      .accepted 1 (envAt 50 50).eff (some (Wall.sample 300)) := by
  decide +kernel

/-- `resignRemovalTrace` with the HotClock moving 5 s across the wall's jump to 295, so that the
wall can then fall back to 70. -/
def fallbackRemovalTrace : List (Env × Input) := armTrace ++ [(envAt 295 65, .pinless .prune)]

/-- `SPN-41`'s difference after the removal falls outside the sticky concealment horizon. The
prune at effective 295 enters the first world armed and past its `T = 250`, so the two-run walk
ends there, having emitted only the steps of `armTrace`, and the removal takes the selected pair in
that world only. The prune moves no ratchet (`DUR-7`), so after the wall falls back to 70
`preHorizon` reads true on both worlds' entering states, again in the first; with no Lockdown
landed (the kernel has none at `T`), a re-signed request whose own fire time fails gate 27 is
refused in the first world and accepted with the first acceptance's instants in the other, at a
step the walk never reaches. -/
@[req "SPN-41"]
theorem removal_difference_outside_sticky_horizon :
    let d := (runOf Kernel.current tblD fallbackRemovalTrace).world.node
    let n := (runOf Kernel.current tblN fallbackRemovalTrace).world.node
    preHorizon Kernel.current (envAt 295 65) (runOf Kernel.current tblD armTrace).world.node = false ∧
    d.cands = [] ∧ d.ratchet = (envAt 60 60).eff ∧ d.lockedDown = false ∧
    preHorizon Kernel.current (envAt 70 70) d = true ∧
    preHorizon Kernel.current (envAt 70 70) n = true ∧
    respond Kernel.current cfg (envAt 70 70) (runOf Kernel.current tblD fallbackRemovalTrace)
      (.accept 30 true (Wall.sample 400) s1Resigned e1) = .refused .EXPIRY_TOO_SHORT ∧
    respond Kernel.current cfg (envAt 70 70) (runOf Kernel.current tblN fallbackRemovalTrace)
      (.accept 30 false (Wall.sample 400) s1Resigned e1) =
      .accepted 1 (envAt 50 50).eff (some (Wall.sample 300)) ∧
    (pairs Silence.current Kernel.current (fallbackRemovalTrace ++
      [(envAt 70 70, .request 30 1 (Wall.sample 400) s1Resigned e1)])).length = armTrace.length := by
  decide +kernel

/-- Gate 27 reads the pair resident after `armTrace` in the ordinary world; registration reads the
registry after a prune pass at 450, past the expiry 400 and the Escape's window, which collected
both members. The re-signed request whose own fire time fails is refused `EXPIRY_TOO_SHORT` at
registration (`SPN-30`), and one whose own fire time passes is admitted, as a request reaching
gate 27 after the prune would be. -/
@[req "SPN-30"]
theorem lost_pair_retest_refuses :
    (runOf Kernel.current tblN (armTrace ++ [(envAt 450 450, .pinless .prune)])).world.node.cands = [] ∧
    ingressRefusal Kernel.current (runOf Kernel.current tblN armTrace).world.node
      (runOf Kernel.current tblN armTrace).world.node s1Resigned e1 = none ∧
    ingressRefusal Kernel.current (runOf Kernel.current tblN armTrace).world.node
      (runOf Kernel.current tblN (armTrace ++ [(envAt 450 450, .pinless .prune)])).world.node
      s1Resigned e1 = some .EXPIRY_TOO_SHORT ∧
    ingressRefusal Kernel.current (runOf Kernel.current tblN armTrace).world.node
      (runOf Kernel.current tblN (armTrace ++ [(envAt 450 450, .pinless .prune)])).world.node
      { s1 with fireAt := some (Wall.sample 350) } e1 = none := by
  decide +kernel

/-- With no resident pair or an incompatible one, gate 27 reads the request's own fire time.
A failing fire time precedes the identity refusal; a passing one admits a birth or reaches that
identity refusal. The kernel's ids are abstract, so the incompatible transaction under an old id
is an identity-check input, not a commitment-collision claim. -/
@[req "SPN-30"]
theorem unretained_pair_uses_request_fire :
    respond Kernel.current cfg (envAt 70 70) sys0
      (.accept 30 false (Wall.sample 400) s1Resigned e1) = .refused .EXPIRY_TOO_SHORT ∧
    respond Kernel.current cfg (envAt 70 70) sys0
      (.accept 30 false (Wall.sample 400) { s1Resigned with fireAt := some (Wall.sample 350) } e1) =
      .accepted 1 (envAt 70 70).eff (some (Wall.sample 350)) ∧
    respond Kernel.current cfg (envAt 70 70) (runOf Kernel.current tblN armTrace)
      (.accept 30 false (Wall.sample 400) s1Resigned { e1 with tx := esc2 }) =
      .refused .EXPIRY_TOO_SHORT ∧
    respond Kernel.current cfg (envAt 70 70) (runOf Kernel.current tblN armTrace)
      (.accept 30 false (Wall.sample 400) { s1Resigned with fireAt := some (Wall.sample 350) }
        { e1 with tx := esc2 }) = .refused .PSBT_INCONSISTENT := by
  decide +kernel

/-- Registration's registry holds only the Escape from the pair gate 27 found resident and
compatible. The kernel does not model `NCH-24`'s lookup eviction that can collect only one member. -/
def oneMemberRegistry : Node :=
  let n := (runOf Kernel.current tblN armTrace).world.node
  { n with cands := n.cands.filter (·.id == e1.id) }

/-- A failing own fire time is refused at the re-test before the missing member's identity
refusal (`SPN-30`, `SPN-32`), although the resident pair's recorded fire time passed gate 27. -/
@[req "SPN-30"]
theorem one_member_retest_before_identity :
    expiryAdmits Kernel.current (runOf Kernel.current tblN armTrace).world.node s1Resigned e1 = true ∧
    oneMemberRegistry.cands.map Cand.id = [e1.id] ∧
    ingressRefusal Kernel.current (runOf Kernel.current tblN armTrace).world.node
      oneMemberRegistry s1Resigned e1 = some .EXPIRY_TOO_SHORT := by
  decide +kernel

/-- The same registries and request with only its own fire time changed to pass: the re-test
passes and the one-member registration is refused for identity (`SPN-32`). -/
@[req "SPN-32"]
theorem one_member_passing_fire_identity :
    expiryAdmits Kernel.current (runOf Kernel.current tblN armTrace).world.node
      { s1Resigned with fireAt := some (Wall.sample 350) } e1 = true ∧
    oneMemberRegistry.cands.map Cand.id = [e1.id] ∧
    ingressRefusal Kernel.current (runOf Kernel.current tblN armTrace).world.node
      oneMemberRegistry { s1Resigned with fireAt := some (Wall.sample 350) } e1 =
      some .PSBT_INCONSISTENT := by
  decide +kernel

end BtcPolicy.Exhibits.TwoRun

namespace BtcPolicy.Exhibits.HotClockHold
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt tx1 txE)

/-! ## `SPN-38`'s HotClock check of a hot spend's Hold

A forward wall step opens a hot spend's fire window, whose opening is read at effective time, and
the spend still waits until its HotClock age reaches `hold_secs`. The cost is stated at `NCH-41`:
`SPN-38` reads the close "at `max(ratchet, effective)`", so a step longer than
`combine_slack_secs` before the Hold matures on the HotClock closes the window first, and a wall
corrected back into the window after it matures opens it again. `withdrawnHoldCheck` is the value
under which a forward step makes the spend due at once; each value's trace over every rule is in
`Kernel.HoldCases`. -/

/-- A hot spend due on its fire window alone, with no HotClock check of its Hold: the reading
withdrawn on 2026-10-09. -/
def withdrawnHoldCheck : Rules := { current with holdCheck := .windowOnly }

/-- 2-of-3, `hold_secs` 20 and `combine_slack_secs` 60: `Kernel.HoldCases`' node. -/
def A : Node := Kernel.HoldCases.holdA
def w0 : World := { node := A, exposure := [] }

/-- A hot spend whose fire time is 20 and its Escape, so the spend's window is `[20, 80]`. -/
def sp : Cand := cand 1 tx1 true (some 20) 300
def es : Cand := cand 2 txE false none 300

/-- Accepted at wall 0 and HotClock 0, and opened by peer 1's relay at the same samples. -/
def opened : List (Env × Event) :=
  [ (envAt 0 0, .accept 10 false (Wall.sample 300) sp es), (envAt 0 0, .receipt 10 1) ]

def openedAt (r : Rules) : World := (run r w0 opened).1

/-- The candidate `id` is resident and due. -/
def dueAt (r : Rules) (w : World) (env : Env) (id : Nat := sp.id) : Bool :=
  w.node.cands.any fun c => c.id == id && due r env w.node c

def hotPartial : List Effect := [.queuePartial (sighash tx1 0) 0 true 1]

/-- A forward wall step of 50 by HotClock 6: the wall reads 56, so the opened spend's window is
open on the wall, and it is not due. At HotClock 19 it is still not due; at HotClock 20, its age
equal to `hold_secs`, it is due, and the fire pass there releases its partial. -/
@[req "SPN-38"]
theorem forward_step_waits_for_hold :
    (openedAt current).node.cands.any (fun c => c.id == sp.id && c.quorum &&
      c.acceptedAt == Mono.sample 0 && (envAt 56 6).eff.atOrAfter (Wall.sample 20) &&
      windowOpen (closeSample current (envAt 56 6) (openedAt current).node c)
        (openedAt current).node.combineSlack c) = true ∧
    dueAt current (openedAt current) (envAt 56 6) = false ∧
    (step current (envAt 56 6) (openedAt current) .firePass).2 = [] ∧
    dueAt current (openedAt current) (envAt 69 19) = false ∧
    dueAt current (openedAt current) (envAt 70 20) = true ∧
    (step current (envAt 70 20) (openedAt current) .firePass).2 = hotPartial := by
  decide +kernel

/-- A step of 70 by HotClock 6, longer than `combine_slack_secs`: the wall reads 76, inside
`[20, 80]`, so the spend fires at once under `withdrawnHoldCheck`, and under `current` it does
not, then or at its HotClock maturity, wall 90. The same samples are a suspend's: a correct wall
reading 76 while a HotClock that lagged by 70 seconds reads 6 (`NCH-41`: "A suspend makes it lag
real time"), so this one trace is both readings. The spend stays listed in `/pending` through its
expiry at 300 and leaves it after. -/
@[req "SPN-38"]
theorem beyond_slack_fires_with_withdrawn_only :
    (step withdrawnHoldCheck (envAt 76 6) (openedAt withdrawnHoldCheck) .firePass).2
      = hotPartial ∧
    (step current (envAt 76 6) (openedAt current) .firePass).2 = [] ∧
    (step current (envAt 90 20) (openedAt current) .firePass).2 = [] ∧
    pending current (envAt 300 224) (openedAt current).node = [sp.id] ∧
    pending current (envAt 301 225) (openedAt current).node = [] := by
  decide +kernel

/-- And under `current` that spend is due at no sample before its HotClock age reaches
`hold_secs` (`Kernel.not_due_before_hold`), nor at the sample where that age is reached, wall 90,
nor at any sample
whose effective time is not before that, because its close at 80 has passed there
(`Kernel.not_due_after_close`, through `Kernel.windowOpen_weaken`). The order is effective time: a
wall that later stepped back into `[20, 80]` with the HotClock past 20 is a different trace,
`corrected_wall_reopens_window`. -/
@[req "SPN-38"]
theorem beyond_slack_never_due :
    (∀ env : Env, ∀ c ∈ (openedAt current).node.cands, c.id = sp.id →
      c.acceptedAt.aged env.mono (openedAt current).node.holdSecs = false →
      due current env (openedAt current).node c = false) ∧
    (∀ env : Env, (envAt 90 20).eff.notAfter env.eff = true →
      ∀ c ∈ (openedAt current).node.cands, c.id = sp.id →
      due current env (openedAt current).node c = false) := by
  have h : (openedAt current).node.cands.all (fun c => c.id != sp.id ||
      (c.hot && !windowOpen (envAt 90 20).eff (openedAt current).node.combineSlack c)) = true := by
    decide +kernel
  have hc : ∀ c ∈ (openedAt current).node.cands, c.id = sp.id →
      c.hot = true ∧
        windowOpen (envAt 90 20).eff (openedAt current).node.combineSlack c = false := by
    intro c hm hid
    have := List.all_eq_true.1 h c hm
    simpa [hid] using this
  exact ⟨fun _ c hm hid ha => not_due_before_hold rfl (hc c hm hid).1 ha,
    fun _ hab c hm hid => not_due_after_close (hc c hm hid).2 hab⟩

/-- The same pair accepted at wall 0 and HotClock 10, and opened by peer 1's relay there. The
spend's fire time 20 is its acceptance wall reading plus `hold_secs` (`SPN-30`: "A hot-class
spend's fire time is `ingress_now + hold_secs`"), so its window on the wall is `[20, 80]`, and
`born` stamps it at HotClock 10, so its Hold matures at HotClock 30. -/
def late : List (Env × Event) :=
  [ (envAt 0 10, .accept 10 false (Wall.sample 300) sp es), (envAt 0 10, .receipt 10 1) ]

def lateAt (r : Rules) : World := (run r w0 late).1

/-- The instant `born` writes decides the verdict: the spend accepted at HotClock 10 carries that
instant, is not due at wall 29 and HotClock 29, and is due at wall 30 and HotClock 30, where the
fire pass releases its partial. Both walls are inside `[20, 80]` and the ratchet is the
acceptance's 0, so the window is open at both, and only the HotClock age decides: 19 at the first,
equal to `hold_secs` at the second. -/
@[req "SPN-38"]
theorem hold_counts_from_acceptance :
    (lateAt current).node.cands.any (fun c => c.id == sp.id && c.quorum &&
      c.acceptedAt == Mono.sample 10) = true ∧
    dueAt current (lateAt current) (envAt 29 29) = false ∧
    dueAt current (lateAt current) (envAt 30 30) = true ∧
    (step current (envAt 30 30) (lateAt current) .firePass).2 = hotPartial := by
  decide +kernel

/-- A replay of that pair under a fresh Carrier at wall 5 and HotClock 15 leaves the resident spend
as it is, its instant included (`POL-18`: "a retry keeps the original reservation time"): it is
not due at wall 29 and HotClock 29 and is due at wall 30 and HotClock 30, the original maturity,
and not only from HotClock 35. The replay moves the ratchet to its 5, below both samples, so the
close is read at their effective time; both walls are inside `[20, 80]`, the window is open at
both, and the instant alone decides them. -/
@[req "SPN-38"]
theorem replay_keeps_reservation_time :
    (run current (lateAt current)
      [(envAt 5 15, .accept 11 false (Wall.sample 300) sp es)]).1.node.carriers.map Carrier.cid
      = [11] ∧
    (run current (lateAt current)
      [(envAt 5 15, .accept 11 false (Wall.sample 300) sp es)]).1.node.cands.any
      (fun c => c.id == sp.id && c.acceptedAt == Mono.sample 10) = true ∧
    dueAt current (run current (lateAt current)
      [(envAt 5 15, .accept 11 false (Wall.sample 300) sp es)]).1 (envAt 29 29) = false ∧
    dueAt current (run current (lateAt current)
      [(envAt 5 15, .accept 11 false (Wall.sample 300) sp es)]).1 (envAt 30 30) = true := by
  decide +kernel

/-- The step of 70 by HotClock 6 corrected back: fire passes at wall 76 and HotClock 6, and at
wall 90 and HotClock 20, release nothing, and a fire pass at wall 70 and HotClock 21 releases the
hot partial. A fire pass does not advance the time ratchet (`DUR-7`: "Nothing else moves it — not
a fire pass"), so the close is read at effective time again, the ratchet being the acceptance's 0,
and effective time 70, the high-water sample being 0, is inside `[20, 80]` with the Hold matured
on the HotClock. -/
@[req "SPN-38"]
theorem corrected_wall_reopens_window :
    (run current (openedAt current) [(envAt 76 6, .firePass)]).2 = [] ∧
    (run current (openedAt current) [(envAt 76 6, .firePass), (envAt 90 20, .firePass)]).2 = [] ∧
    (run current (openedAt current)
      [(envAt 76 6, .firePass), (envAt 90 20, .firePass), (envAt 70 21, .firePass)]).2
      = hotPartial := by
  decide +kernel

/-- The same pair accepted under a duress Carrier at wall 0 and HotClock 0, and armed by peer 1's
relay there: the holder decision writes `T = 15`, freezes the spend and installs the Escape's
window `[15, 75]`. -/
def armedTrace : List (Env × Event) :=
  [ (envAt 0 0, .accept 10 true (Wall.sample 300) sp es), (envAt 0 0, .receipt 10 1) ]

def armedAt (r : Rules) : World := (run r w0 armedTrace).1

/-- The HotClock check gates hot candidates only. The candidate is the Escape of that hot pair,
born with the spend at HotClock 0 and selected by the duress holder decision: at wall 15 and
HotClock 15, inside its window and before its spend's Hold would mature at HotClock 20, it is due,
and the fire pass there releases its partial. -/
@[req "SPN-38"]
theorem armed_escape_not_gated :
    (armedAt current).node.armed = true ∧
    (armedAt current).node.cands.any (fun c => c.id == es.id && !c.hot &&
      c.acceptedAt == Mono.sample 0) = true ∧
    dueAt current (armedAt current) (envAt 15 15) es.id = true ∧
    (step current (envAt 15 15) (armedAt current) .firePass).2
      = [.queuePartial (sighash txE 0) 0 false 2] := by
  decide +kernel

end BtcPolicy.Exhibits.HotClockHold

namespace BtcPolicy.Exhibits.OperatorDelivery
open BtcPolicy.Delivery

/-! ## The Operator's delivery loop and its watch: `DEF-8` and `F56`

`Delivery.lean` owns two guard parameters in one `current` record. Every theorem over `current` is
here; beside each twin's `current` half, the same trace under the withdrawn value is in
`Delivery.lean`. A universal theorem's proof opens by naming its goal after the theorem, so the
red a flip leaves names the theorem it refutes. -/

/-- Under `current` every outcome after connect advances the knowledge and `NotSent` leaves it, for
every knowledge and every outcome — `400`, `413`, a mismatched `accepted` and every failure
included. `OPR-49`: the state advances "on EVERY attempt that is not `NotSent`". -/
@[req "OPR-49"]
theorem post_connect_advances_with_current (k : Knowledge) (o : Outcome) :
    advance Delivery.current k o = .possiblyDelivered ↔
      k = .possiblyDelivered ∨ o ≠ .notSent := by
  refine ?post_connect_advances_with_current
  rw [advance_possibly_iff]
  cases o <;> simp [readAsNotSent, Delivery.current]

/-! ### `DEF-8`: reissue after a failure past connect -/

/-- `OPR-51` under `current`, for every expected id and every list of outcomes: reissue is
authorized iff every endpoint was `NotSent` — "If EVERY endpoint was `NotSent`". From
`reissue_iff`, which is proved by induction on the list. -/
@[req "OPR-51"]
theorem reissue_iff_every_notSent_with_current (e : Nat) (os : List Outcome) :
    reissue (run Delivery.current e os) = true ↔ ∀ o ∈ os, o = .notSent := by
  refine ?reissue_iff_every_notSent_with_current
  rw [reissue_iff]
  refine forall_congr' fun o => imp_congr_right fun _ => ?_
  cases o <;> simp [readAsNotSent, Delivery.current]

/-- `DEF-8`: "a single endpoint's `NotSent` authorizes nothing". Under `current`, a list holding
one outcome that is not `NotSent` never authorizes reissue, whatever its other members are. -/
@[req "OPR-51"]
theorem one_attempt_sent_refuses_with_current (e : Nat) (os : List Outcome) (o : Outcome)
    (ho : o ∈ os) (hs : o ≠ .notSent) : reissue (run Delivery.current e os) = false := by
  refine ?one_attempt_sent_refuses_with_current
  cases h : reissue (run Delivery.current e os)
  · rfl
  · have := (reissue_iff Delivery.current e os).1 h o ho
    cases o <;> simp_all [readAsNotSent, Delivery.current]

/-- `DEF-8`'s twin under `current`: three endpoints, each failing after connect, leave the run
"possibly delivered, exact bytes", and reissue is refused. Under the withdrawn value the run ends
"definitely not sent" and reissue is authorized (`def8_admitted_with_withdrawn`). -/
@[req "OPR-51"]
theorem def8_refused_with_current :
    run Delivery.current expectedId def8Failures = ⟨.possiblyDelivered, false⟩ ∧
    reissue (run Delivery.current expectedId def8Failures) = false := by
  decide

/-- `DEF-8`'s second shape under `current`: the second endpoint's `400` is possible delivery, so
reissue is refused — and under the withdrawn value too (`def8_status_refused_with_withdrawn`), so
this half stays green when the parameter flips. -/
@[req "OPR-51"]
theorem def8_status_refused_with_current :
    run Delivery.current expectedId def8Status = ⟨.possiblyDelivered, false⟩ ∧
    reissue (run Delivery.current expectedId def8Status) = false := by
  decide

/-! ### `F56`: the output the watch polls -/

/-- `OPR-51`'s table under `current`: output 1 for `spend`, output 0 for `clawback` and for
`refresh`. -/
@[req "OPR-51"]
theorem watch_target_with_current :
    watchTarget Delivery.current .spend = 1 ∧ watchTarget Delivery.current .clawback = 0 ∧
      watchTarget Delivery.current .refresh = 0 := by
  decide

/-- `F56`'s twin under `current`: the watched output exists for the one-output claw-back and the
one-in-one-out refresh, and for the two-output `spend`. Under the withdrawn value it exists for
the `spend` alone (`f56_target_missing_with_withdrawn`), so the contrast is the kinds without an
output 1. -/
@[req "OPR-51"]
theorem f56_target_exists_with_current :
    targetExists Delivery.current .clawback clawbackOutputs = true ∧
    targetExists Delivery.current .refresh refreshOutputs = true ∧
    targetExists Delivery.current .spend spendOutputs = true := by
  decide

end BtcPolicy.Exhibits.OperatorDelivery

namespace BtcPolicy.Exhibits.WatchtowerCursor
open BtcPolicy.Chain BtcPolicy.Watchtower

/-! ## The watchtower cursor, the scan proof and the tip test: `DEF-6` and `ADR-0024`

`Watchtower.lean` owns two guard parameters, the cursor's shape and `WTC-14`'s tip test. Every
theorem over `current` is here; each parameter's trace under each value is beside it in
`Watchtower.lean`. A universal theorem's proof opens by naming its goal after the theorem, so the
red a flip leaves names the theorem it refutes. -/

/-- In-window detection under `current`, over every view and every cursor with a newest anchor:
reconciliation is the identity iff that one read finds the anchor active. `WTC-13`: "one hash
read at the newest anchor detects any in-window reorg". -/
@[req "WTC-13"]
theorem reconcile_identity_iff_with_current (v : View) (c : Cursor) (a : Anchor)
    (older : List Anchor) (h : c.anchors = a :: older) :
    reconcile Watchtower.current v c = c ↔ a.active v = true := by
  refine ?reconcile_identity_iff_with_current
  simp only [Watchtower.current, reconcile_identity_iff v c a older h]

/-- Deeper than the window under `current`, over every view and every cursor: no anchor active,
reconciliation is genesis. `WTC-13`: "it clears and re-scans from genesis rather than wedging or
silently advancing". -/
@[req "WTC-13"]
theorem reconcile_none_active_with_current (v : View) (c : Cursor)
    (h : ∀ x ∈ c.anchors, x.active v = false) : reconcile Watchtower.current v c = genesis := by
  refine ?reconcile_none_active_with_current
  simp only [Watchtower.current, reconcile_none_active v c h]

/-! ### `WTC-12`'s three checks are each necessary

One cursor for the four scans: anchors at heights 3 to 5 on chain `A`, hashes `100 + h`, next
height 6, expected parent `105`. Fork `B` has hashes `200 + h`. In each of the three, the other
two checks pass, the failing check fails, and accepting the scan would bind a result to an
abandoned fork; the pass leaves the cursor as it was. -/

@[req "WTC-12"]
def scanCursor : Cursor := { anchors := [⟨5, 105⟩, ⟨4, 104⟩, ⟨3, 103⟩], next := 6 }

/-- (a) "closing a fork below the range that rebuilt taller": the chain abandoned `A` at heights
4 and 5 for `B`, which grew to height 7; the scan of heights 6 to 7 reads `B`'s blocks, which
link among themselves and end on the active hash, but the first links to `205`, not `105`. -/
@[req "WTC-12"]
def scanA : Scan :=
  { blocks := blocksOf [206, 207] 6 205, spends := [],
    after := chainOf [100, 101, 102, 103, 204, 205, 206, 207] }

@[req "WTC-12"]
theorem first_check_necessary_with_current :
    laterLinks scanA.blocks = true ∧ lastActive scanA = true ∧
      firstLinks scanCursor scanA = false ∧ bindsAbandoned scanCursor scanA = true ∧
      pass Watchtower.current Watchtower.currentTipTest scanCursor ⟨7, 207⟩ (.scanned scanA) =
        scanCursor := by
  decide

/-- (b) "breaking a mixed-fork straddle": height 6 was read on `A` and links to the expected
parent; the chain then switched to `B`, and heights 7 and 8 were read there, the last active —
but `B`'s block at 7 links to `206`, not to the `106` scanned before it. -/
@[req "WTC-12"]
def scanB : Scan :=
  { blocks := ⟨6, 106, 105⟩ :: blocksOf [207, 208] 7 206, spends := [],
    after := chainOf [100, 101, 102, 103, 104, 105, 206, 207, 208] }

@[req "WTC-12"]
theorem later_check_necessary_with_current :
    firstLinks scanCursor scanB = true ∧ lastActive scanB = true ∧
      laterLinks scanB.blocks = false ∧ bindsAbandoned scanCursor scanB = true ∧
      pass Watchtower.current Watchtower.currentTipTest scanCursor ⟨8, 208⟩ (.scanned scanB) =
        scanCursor := by
  decide

/-- (c) "closing a scan that ran entirely on an abandoned fork, including one that returned to
the captured tip": the tip captured before the scan is `(7, 107)` on `A`; the loop read heights 6
and 7 on `B`, every block linking to its predecessor and the first to `105`; the chain then
returned to `A`, so the tip read after the loop is `(7, 107)` again and `WTC-14`'s tip-changed
outcome does not fire — yet the hash at height 7 is `107`, not the `207` scanned. -/
@[req "WTC-12"]
def scanC : Scan :=
  { blocks := blocksOf [206, 207] 6 105, spends := [],
    after := chainOf [100, 101, 102, 103, 104, 105, 106, 107] }

@[req "WTC-12"]
theorem last_check_necessary_with_current :
    firstLinks scanCursor scanC = true ∧ laterLinks scanC.blocks = true ∧
      scanC.after.tip = ⟨7, 107⟩ ∧ lastActive scanC = false ∧
      bindsAbandoned scanCursor scanC = true ∧
      pass Watchtower.current Watchtower.currentTipTest scanCursor ⟨7, 107⟩ (.scanned scanC) =
        scanCursor := by
  decide

/-- The positive exhibit: heights 6 and 7 read on `A`, all three checks hold, and the pass
advances — the next height to 8 and, under `current`, the newest anchor to `(7, 107)`. -/
@[req "WTC-12"]
def scanOk : Scan :=
  { blocks := blocksOf [106, 107] 6 105, spends := [],
    after := chainOf [100, 101, 102, 103, 104, 105, 106, 107] }

@[req "WTC-14"]
theorem proven_scan_advances_with_current :
    proven scanCursor scanOk = true ∧
      (pass Watchtower.current Watchtower.currentTipTest scanCursor ⟨7, 107⟩
          (.scanned scanOk)).next = 8 ∧
      (pass Watchtower.current Watchtower.currentTipTest scanCursor ⟨7, 107⟩
          (.scanned scanOk)).anchors.head? = some ⟨7, 107⟩ := by
  decide

/-! ### `WTC-14`'s tip test: the block that arrives on top -/

/-- Under `current`, over every captured tip and every view read after the loop: a captured tip
still active at its own height is not a change. `WTC-14`: "a block arriving on top during the scan
is not such a change, and is the next pass's range" — the view's own tip is not read, so whatever
arrived on top the test is false. -/
@[req "WTC-14"]
theorem block_on_top_not_a_change_with_current (tip : Anchor) (after : View)
    (ha : after.activeAt tip.height = some tip.hash) :
    tipChanged Watchtower.currentTipTest tip after = false := by
  refine ?block_on_top_not_a_change_with_current
  simp only [Watchtower.currentTipTest, tipChanged_capturedHeight_false tip after ha]

/-- The trace under `current`: the pass captured `A`'s tip `(5, 105)`, height 6 arrived while the
loop ran, and the pass is KEPT — the candidate advances the cursor to next height 6. Under the
withdrawn reading the same pass discards it (`def14_discarded_with_chainTip`), and on mainnet that
is every pass of a `WTC-13` genesis re-scan. -/
@[req "WTC-14"]
theorem block_on_top_kept_with_current :
    tipChanged Watchtower.currentTipTest def14Tip def14Scan.after = false ∧
      (pass Watchtower.current Watchtower.currentTipTest def14Cursor def14Tip
          (.scanned def14Scan)).next = 6 := by
  decide

/-! ### `DEF-6`: the spend that re-lands below the cursor -/

/-- `DEF-6`'s twin under `current`: the first pass binds its one spend; after it the cursor
stands at 6; reconciled against the reorged chain it rewinds to the highest still-active anchor,
`(2, 102)`, and stands at 3 — at or below the height the spend re-lands at, so the re-scan
reaches it. Under the withdrawn shape it stands at 6 and the spend is never scanned again
(`def6_missed_with_withdrawn`). -/
@[req "WTC-13"]
theorem def6_rescanned_with_current :
    (result Watchtower.current genesis def6Scan).map (·.2) = some [1] ∧
      (def6Cursor Watchtower.current).next = 6 ∧
      (reconcile Watchtower.current (chainOf def6ChainB) (def6Cursor Watchtower.current)).next = 3 ∧
      3 ≤ def6Relanded := by
  decide

end BtcPolicy.Exhibits.WatchtowerCursor

namespace BtcPolicy.Exhibits.VaultUnspentCache
open BtcPolicy.Chain BtcPolicy.VaultUnspent
open BtcPolicy.Watchtower (Scan chainOf blocksOf)

/-! ## The vault-unspent cache, the wallet import and the delta walk: `DEF-21` and `ADR-0024`

`VaultUnspent.lean` owns seven guard parameters: the import bracket, the marker anchor, the latch
scope, and the four `VaultUnspent.Rules` carries — the delta commit, the walk range, the retry
trigger and the chain tie. Every theorem over `current` is here; each parameter's trace under its
withdrawn value is beside it in `VaultUnspent.lean`. A universal theorem's proof opens by naming
its goal after the theorem, so the red a flip leaves names the theorem it refutes. -/

/-- Under `current`, over every settled block, pair of bracket views and birthday: a settled block
that moved at either point `WTC-7` brackets refuses the import. `WTC-7`: "if it moved, the import
is refused rather than importing a birthday from another branch". -/
@[req "WTC-7"]
theorem import_refused_when_moved_with_current (S : Anchor) (atDescriptors atMarker : View)
    (b : Height)
    (h : anchorStillActive atDescriptors S = false ∨ anchorStillActive atMarker S = false) :
    importBirthday VaultUnspent.current S atDescriptors atMarker b = none := by
  refine ?import_refused_when_moved_with_current
  simp only [VaultUnspent.current, import_refused_when_moved S atDescriptors atMarker b h]

/-- And under `current` a settled block active at both points imports the birthday: the bracket
refuses nothing a stable chain offers. Both values import here, so a flip leaves this one green and
the control does not count it. -/
@[req "WTC-7"]
theorem import_accepted_when_active_with_current (S : Anchor) (atDescriptors atMarker : View)
    (b : Height) (hd : anchorStillActive atDescriptors S = true)
    (hm : anchorStillActive atMarker S = true) :
    importBirthday VaultUnspent.current S atDescriptors atMarker b = some b := by
  refine ?import_accepted_when_active_with_current
  simp [VaultUnspent.current, importBirthday, hd, hm]

/-- Under `current`, over every ledger, scan view, pair of bracket views and walk: the marker the
import leaves is the settled import's. `WTC-8`: "the anchor height and hash of the import's settled
block, and the import's birthday (`WTC-7`)". -/
@[req "WTC-8"]
theorem import_is_settled_with_current (L : Ledger) (scanView atDescriptors atMarker : View)
    (s : Scan) :
    importMarker VaultUnspent.currentMarkerAnchor VaultUnspent.current L scanView atDescriptors
        atMarker s =
      settledImport VaultUnspent.current L scanView atDescriptors atMarker s := by
  refine ?import_is_settled_with_current
  simp only [VaultUnspent.currentMarkerAnchor, importMarker]

/-- `WTC-7`: "so the import covers every output a reorg that leaves S active can make live".
A current import's actual marker birthday has the universal coverage property, under the chain
and ledger hypotheses of `settledBirthday_watches_everything`. The import supplies the proven
walk and scan-view activity through `settledImport_watches_everything`. This is a formal-model
property, not runtime conformance. The proof uses `import_is_settled_with_current`, so a marker
anchor flip fails at that owning verdict instead of adding a second failure here. -/
@[req "WTC-7"]
theorem imported_birthday_watches_everything_with_current (L : Ledger)
    (scanView v' atDescriptors atMarker : View) (s : Scan) (m : Marker)
    (hi : importMarker VaultUnspent.currentMarkerAnchor VaultUnspent.current L scanView
      atDescriptors atMarker s = some m)
    (hblocks : ∀ b ∈ s.blocks, scanView.activeAt b.height = some b.hash)
    (hlaterActive : m.anchor.active v' = true)
    (hagree : ∀ h, h ≤ m.anchor.height → v'.activeAt h = scanView.activeAt h)
    (hlaterTip : m.anchor.height ≤ v'.tip.height)
    (hcreators : ∀ d, d ≤ scanView.tip.height → ∀ c, c ≤ scanView.tip.height →
      ∀ p ∈ spentAt L scanView d, p.2 ∈ confirmedAt L scanView c → p.1 = c) :
    unwatched L v' m.birthday = [] := by
  rw [import_is_settled_with_current] at hi
  exact settledImport_watches_everything VaultUnspent.current L scanView v' atDescriptors
    atMarker s m hi hblocks hlaterActive hagree hlaterTip hcreators

/-- Under `current`, over every ledger, scan view, bracket views, walk and wallet: a rebuild whose
bracket does not hold the settled block at either point yields no wallet, so the latch stays set.
`WTC-9`: "keep the wallet out of use until a cold scan and re-import have rebuilt it". -/
@[req "WTC-9"]
theorem rebuild_refused_when_moved_with_current (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (w : Wallet) (S : Anchor)
    (hS : settledBlock scanView scanView.tip = some S)
    (h : anchorStillActive atDescriptors S = false ∨ anchorStillActive atMarker S = false) :
    rebuild VaultUnspent.currentMarkerAnchor VaultUnspent.current L scanView atDescriptors atMarker
      s w = none := by
  refine ?rebuild_refused_when_moved_with_current
  simp only [VaultUnspent.current, VaultUnspent.currentMarkerAnchor,
    rebuild_refused_when_moved L scanView atDescriptors atMarker s w S hS h]

/-! ### `DEF-21`: the birthday proven on the abandoned fork

The reorg to `B` is deeper than the settled depth, so it unseats `S = (2, 102)`. -/

/-- `DEF-21`'s twin under `current`: the import re-proves `S` on `B`, finds it inactive at both
bracket points, and refuses; a fresh cold scan and walk on `B` find `S = (2, 202)` and birthday 0,
because `X`, created at height 0, is live there, and a wallet imported with it leaves nothing
unwatched. Under the withdrawn bracket the import goes through with birthday 1 and `X` is never
watched (`def21_unwatched_with_unbracketed`). -/
@[req "WTC-7"]
theorem def21_refused_with_current :
    importMarker VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
        (chainOf vaultChainA) (chainOf vaultChainB) (chainOf vaultChainB) vaultWalkA = none ∧
      importMarker VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
        (chainOf vaultChainB) (chainOf vaultChainB) (chainOf vaultChainB) vaultWalkB =
          some ⟨⟨2, 202⟩, 0⟩ ∧
      unwatched vaultLedger (chainOf vaultChainB) 0 = [] := by
  decide

/-- The state the reorg to `B` leaves: the wallet the import on `A` built, the latch set, no cold
scan published since it set, no repair attempt in progress, and no cache. -/
@[req "WTC-9"]
def def21Latched : State :=
  { wallet := { privateKeysDisabled := true, birthday := def21Birthday,
                markers := [⟨vaultSettledA, def21Birthday⟩],
                holdsEveryVaultDescriptor := true },
    latched := true, scanned := false, repairScan := none, cache := none }

/-- The state after the refresh on `B` that finds the latch set, no scan published since and no
attempt in progress: the cold scan on `B` is the cache, and an attempt that started from that scan
is in progress (`def21_rebuilt_with_current`). -/
@[req "WTC-9"]
def def21Attempting : State :=
  { def21Latched with scanned := true,
                      repairScan := some (coldScan vaultLedger (chainOf vaultChainB)),
                      cache := some (coldScan vaultLedger (chainOf vaultChainB)) }

/-- The scan of no block, read on `B`: what the refreshes of this trace are offered as a walk. -/
@[req "WTC-9"]
def def21NoWalk : Scan := { blocks := [], spends := [], after := chainOf vaultChainB }

/-- `B` one block on: the view on which the cache the cold scan left is one block behind. -/
@[req "WTC-9"]
def def21GrownB : View := chainOf (vaultChainB ++ [213])

/-- A walk of that one block that fails its proof: the block's `previousblockhash` is not the
cached anchor's hash, so `WTC-12`'s first check refuses it under every walk range. -/
@[req "WTC-9"]
def def21UnlinkedWalk : Scan :=
  { blocks := blocksOf [213] 13 999, spends := [], after := def21GrownB }

/-- The positive exhibit, `WTC-9`'s whole sequence on `B`. The refresh that finds the latch set, no
cold scan published since and no attempt in progress replaces the cache with the cold scan on `B`
and starts an attempt from it; the re-import of that scan clears the latch and ends the attempt,
leaves the import's marker newest — `B`'s settled block `(2, 202)` with birthday 0 — lowers the
descriptors' birthday to 0, and leaves the cache the cold scan published where it was. The wallet's
earlier marker carried birthday 1, so this repair starts *below* what the wallet covered and
re-imports the descriptors rather than only a marker (`WTC-7`). -/
@[req "WTC-9"]
theorem def21_rebuilt_with_current :
    refresh VaultUnspent.currentRules vaultLedger def21Latched (chainOf vaultChainB)
        (chainOf vaultChainB) (chainOf vaultChainB) def21NoWalk = def21Attempting ∧
    (let st' := repair VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
      (chainOf vaultChainB) (chainOf vaultChainB) (chainOf vaultChainB) vaultWalkB def21Attempting
    st'.latched = false ∧ st'.attempting = false ∧
      st'.wallet.markers.head? = some ⟨⟨2, 202⟩, 0⟩ ∧
      st'.wallet.birthday = 0 ∧ st'.wallet.holdsEveryVaultDescriptor = true ∧
      st'.cache = some (coldScan vaultLedger (chainOf vaultChainB))) := by
  decide

/-- The attempt that ends without rebuilding, both ways `WTC-9` names, from the same state, and
what follows. A failure before the re-import ends the attempt and leaves the latch set, the wallet
and the cache as they were. A re-import offered the scan read on `A` — a scan the import would
accept on its own, `settled_covers_resurrection_with_current` — is not of the cold scan this
attempt started from, on `B`, so it rebuilds nothing and ends the attempt the same way. `WTC-9`:
"one that ends without rebuilding the wallet leaves any latch set". From that state the next
refresh on `B` walks no block from the cache, which is at the tip, and leaves the state as it found
it: no scan, and no new attempt. The attempt after that starts where the cache needs a cold scan
anyway — here a block later, offered a walk that fails its proof — and from that scan.
`WTC-9`: "the next attempt starts only from a cold scan `WTC-6` itself reaches with none in
progress, and starts no scan of its own". -/
@[req "WTC-9"]
theorem def21_failed_attempt_not_retried :
    let failed := endAsFailure def21Attempting
    failed.latched = true ∧ failed.attempting = false ∧
      failed.wallet = def21Attempting.wallet ∧ failed.cache = def21Attempting.cache ∧
      repair VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
        (chainOf vaultChainA) (chainOf vaultChainA) (chainOf vaultChainA) vaultWalkA
        def21Attempting = failed ∧
      refresh VaultUnspent.currentRules vaultLedger failed (chainOf vaultChainB)
        (chainOf vaultChainB) (chainOf vaultChainB) def21NoWalk = failed ∧
      (refresh VaultUnspent.currentRules vaultLedger failed def21GrownB def21GrownB def21GrownB
        def21UnlinkedWalk).repairScan = some (coldScan vaultLedger def21GrownB) := by
  decide

/-- (i) Under `current`, over every ledger, state, view and scan: a refresh that finds the latch
set, no cold scan published since it set and no attempt in progress serves the cold scan, whatever
the cache holds and whatever the walk offered, and starts an attempt from it. `WTC-9`: "From the
latch setting until a cold scan has replaced the cache, every refresh with no attempt in progress
starts a repair attempt from a cold scan, whatever cache it holds". The retry trigger of 2026-10-01
cold-scans here too, so a flip to it leaves this one green; the flip to the reading before it does
not. -/
@[req "WTC-9"]
theorem latched_unscanned_serves_cold_with_current (L : Ledger) (st : State)
    (v after walk : View) (s : Scan) (hl : st.latched = true) (hs : st.scanned = false)
    (hn : st.repairScan = none) :
    serve VaultUnspent.currentRules L st v after walk s = (.coldScan, coldScan L v) ∧
      (refresh VaultUnspent.currentRules L st v after walk s).repairScan =
        some (coldScan L v) := by
  refine ?latched_unscanned_serves_cold_with_current
  simp [VaultUnspent.currentRules, VaultUnspent.currentRetryTrigger, refresh, serve, walletServed,
    deltaFrom, deltaBase, State.attempting, hl, hs, hn]

/-- (ii) Under `current`, over every ledger, view, scan and state in which a cold scan has replaced
the cache since the latch set: after a repair, whatever its re-import yielded, and after a failure
before the re-import, the delta base is the cache the attempt left, so the next refresh cold-scans
only where `WTC-6`'s own order falls through to the cold scan. `WTC-9`: "the next attempt starts
only from a cold scan `WTC-6` itself reaches with none in progress, and starts no scan of its
own". The reading the amendment of 2026-10-01 withdrew walks from the cache here too, so a flip to
it leaves this one green; the flip to the retry trigger of 2026-10-01 does not. -/
@[req "WTC-9"]
theorem failed_attempt_starts_no_scan_with_current (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) (hs : st.scanned = true) :
    deltaBase VaultUnspent.currentRetryTrigger
        (repair VaultUnspent.currentMarkerAnchor VaultUnspent.current L scanView atDescriptors
          atMarker s st) = st.cache ∧
      deltaBase VaultUnspent.currentRetryTrigger (endAsFailure st) = st.cache := by
  refine ?failed_attempt_starts_no_scan_with_current
  simp [VaultUnspent.currentRetryTrigger, deltaBase, repair_keeps_scanned, repair_keeps_cache,
    endAsFailure, hs]

/-! ### The marker anchor: the output a shallow reorg resurrects

The reorg to `C` is no deeper than the settled depth, so it leaves `S = (2, 102)` active, and with
it the one completion marker this wallet holds. -/

/-- `ADR-0024`'s twin under `current`: the import on `A` anchors its marker at `S = (2, 102)` and
carries birthday 1 — the creating height of `Z`, which the walk of `(S, A]` found spent at height 7.
After the reorg to `C` that marker is still active, so the wallet stays usable and nothing latches,
and `Z`, live again on `C`, is watched: nothing is unwatched. Under the withdrawn value the marker
anchors at the scan anchor, which `C` unseats, so the wallet is out of use until a repair has
rebuilt it — one cold scan and re-import for a reorg that left `S` standing
(`markerAnchor_repairs_with_scanTip`). -/
@[req "WTC-7"]
theorem settled_covers_resurrection_with_current :
    importMarker VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
        (chainOf vaultChainA) (chainOf vaultChainA) (chainOf vaultChainA) vaultWalkA =
      some ⟨vaultSettledA, def21Birthday⟩ ∧
      anchorStillActive (chainOf vaultChainC) vaultSettledA = true ∧
      usable (chainOf vaultChainC) settledWallet = true ∧
      observe VaultUnspent.currentLatchScope (chainOf vaultChainC) settledWallet false = false ∧
      unwatched vaultLedger (chainOf vaultChainC) def21Birthday = [] := by
  have htrace :
      importMarker VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
          (chainOf vaultChainA) (chainOf vaultChainA) (chainOf vaultChainA) vaultWalkA =
        some ⟨vaultSettledA, def21Birthday⟩ ∧
        anchorStillActive (chainOf vaultChainC) vaultSettledA = true ∧
        usable (chainOf vaultChainC) settledWallet = true ∧
        observe VaultUnspent.currentLatchScope (chainOf vaultChainC) settledWallet false = false :=
    by decide
  refine ⟨htrace.1, htrace.2.1, htrace.2.2.1, htrace.2.2.2, ?_⟩
  apply imported_birthday_watches_everything_with_current vaultLedger (chainOf vaultChainA)
    (chainOf vaultChainC) (chainOf vaultChainA) (chainOf vaultChainA) vaultWalkA
    ⟨vaultSettledA, def21Birthday⟩ htrace.1
  · decide
  · exact htrace.2.1
  · intro h hh
    have hp : ∀ k ∈ List.range 3,
        (chainOf vaultChainC).activeAt k = (chainOf vaultChainA).activeAt k := by decide
    exact hp h (List.mem_range.mpr (by change h ≤ 2 at hh; simp only [Height] at *; omega))
  · decide
  · intro d hd c hc p hp hpc
    have hledger : ∀ d ∈ List.range 13, ∀ c ∈ List.range 13,
        ∀ p ∈ spentAt vaultLedger (chainOf vaultChainA) d,
        p.2 ∈ confirmedAt vaultLedger (chainOf vaultChainA) c → p.1 = c := by decide
    exact hledger d (List.mem_range.mpr (by change d ≤ 12 at hd; simp only [Height] at *; omega))
      c (List.mem_range.mpr (by change c ≤ 12 at hc; simp only [Height] at *; omega)) p hp hpc

/-! ### `WTC-6`'s delta walk, committed and read

Walks from the one cache `VaultUnspent.deltaState` holds under the latch, a cold scan published
since it set and a repair attempt in progress, which is the state `WTC-9` advances by delta walks;
the latch keeps the wallet out of play, so its value is immaterial. Served for
`VaultUnspent.deltaView`, heights 0 to 2 with tip `(2, 102)`, and for `VaultUnspent.deltaLongView`,
heights 0 to 34 with tip `(34, 134)`; no block arrives during these refreshes, so the three views
of each are one. -/

/-- The view after one more block: heights 0 to 3, tip `(3, 103)`. -/
@[req "WTC-6"] def deltaGrownView : View := chainOf [100, 101, 102, 103]

/-- A latched walk advances the one cache, and the fire-time read uses it. A scan of the two blocks
above the cache's anchor, each linking to the one before it and the last still active after the
loop, covers its range and is served as the delta walk; the refresh makes it the cache, anchored at
the tip `(2, 102)` with the output block 1 creates, with the latch still set and the same attempt
still in progress; `WTC-5`'s fire-time read takes that cache; and the next refresh, a block later,
walks from it — from `(2, 102)`, not from `(0, 100)` — to the new tip. `WTC-6`: "any later delta
walk starts from that cache". Every value of every guard commits these walks, so no flip turns
this red. -/
@[req "WTC-6"]
theorem latched_walk_advances_the_cache :
    let st' := refresh VaultUnspent.currentRules vaultLedger deltaState deltaView deltaView
      deltaView deltaTipWalk
    let next : Scan := { blocks := blocksOf [103] 3 102, spends := [], after := deltaGrownView }
    (serve VaultUnspent.currentRules vaultLedger deltaState deltaView deltaView deltaView
        deltaTipWalk).1 = .deltaWalk ∧
      st'.latched = true ∧ st'.repairScan = deltaState.repairScan ∧
      st'.cache = some { outputs := [(4, 60)], anchor := ⟨2, 102⟩ } ∧
      st'.cache.bind (fireTimeRead deltaView) = some [(4, 60)] ∧
      serve VaultUnspent.currentRules vaultLedger st' deltaGrownView deltaGrownView deltaGrownView
        next = (.deltaWalk, { outputs := [(4, 60)], anchor := ⟨3, 103⟩ }) := by
  decide

/-- Under `current`, over every ledger, state, view, scan and pair of caches: a walk that completes
— succeeds from a still-active base, covers its whole range, and ends on a block active on the
view captured when it started — is committed, wherever that range ends. `WTC-6`: "A walk that
completes becomes the cache even where it ends below the tip". Either chain tie commits such a walk,
so a flip of the chain tie leaves this one green; `walk_committed_on_any_branch_with_current` is
the one without the last hypothesis. -/
@[req "WTC-6"]
theorem delta_commits_completed_walk_with_current (L : Ledger) (st : State) (v : View) (s : Scan)
    (c c' : Cache) (hb : deltaBase VaultUnspent.currentRetryTrigger st = some c)
    (ha : c.anchor.active v = true) (hw : deltaWalk L c s = some c')
    (hc : coversRange c v s = true) (ht : c'.anchor.active v = true) :
    deltaFrom VaultUnspent.currentRules L st v s = some c' := by
  refine ?delta_commits_completed_walk_with_current
  simp only [VaultUnspent.currentRules, VaultUnspent.currentDeltaCommit,
    delta_commits_completed_walk VaultUnspent.currentWalkRange VaultUnspent.currentRetryTrigger
      VaultUnspent.currentChainTie L st v s c c' hb ha hw hc ht]

/-- The walk that completes below the tip. On the long view the cache is 34 blocks behind, so the
walk that covers its whole range is the `deltaWindow` blocks at heights 1 to 32 and ends at
`(32, 132)`. Under `current` it is committed — the delta walk is the source and the refresh makes it
the cache — while the fire-time read refuses it, `WTC-6`: "a cache whose anchor is not the current
tip is refused at fire time (`WTC-5`)". The next refresh walks the two blocks left from that cache
to the tip, and the fire-time read takes what it leaves. Under the withdrawn delta commit the first
walk is thrown away and the cold scan runs (`delta_below_tip_falls_through_with_tipOnly`). -/
@[req "WTC-6"]
theorem delta_walk_below_tip_committed :
    let st' := refresh VaultUnspent.currentRules vaultLedger deltaState deltaLongView
      deltaLongView deltaLongView deltaWindowWalk
    let next : Scan := { blocks := blocksOf [133, 134] 33 132, spends := [], after := deltaLongView }
    (serve VaultUnspent.currentRules vaultLedger deltaState deltaLongView deltaLongView
        deltaLongView deltaWindowWalk).1 = .deltaWalk ∧
      st'.cache.map (·.anchor) = some ⟨32, 132⟩ ∧
      st'.cache.bind (fireTimeRead deltaLongView) = none ∧
      (serve VaultUnspent.currentRules vaultLedger st' deltaLongView deltaLongView deltaLongView
        next).1 = .deltaWalk ∧
      fireTimeRead deltaLongView
        (serve VaultUnspent.currentRules vaultLedger st' deltaLongView deltaLongView deltaLongView
          next).2 = some [(4, 60), (2, 40)] := by
  decide

/-- Under `current`, over every ledger, state, view and scan: a walk that covers less than its
range from the cache is discarded, however well it proves. `WTC-6`: "A walk that covers less is
discarded whole". -/
@[req "WTC-6"]
theorem uncovered_walk_discarded_with_current (L : Ledger) (st : State) (w : View) (s : Scan)
    (hc : ∀ c, st.cache = some c → coversRange c w s = false) :
    deltaFrom VaultUnspent.currentRules L st w s = none := by
  refine ?uncovered_walk_discarded_with_current
  simp only [VaultUnspent.currentRules, VaultUnspent.currentWalkRange,
    delta_refuses_uncovered_walk VaultUnspent.currentDeltaCommit VaultUnspent.currentRetryTrigger
      VaultUnspent.currentChainTie L st w s hc]

/-- The walk that covers less than its range: a scan of block 1 alone stops at `(1, 101)`, one
short of the tip it had to reach. It passes every `WTC-12` proof and is discarded all the same, and
the refresh falls through to the cold scan, anchored at the tip. `WTC-6`: "A walk that covers less
is discarded whole". Under the withdrawn walk range it is committed
(`short_and_empty_walk_committed_with_asRead`); both values of the delta commit discard it. -/
@[req "WTC-6"]
theorem delta_walk_short_falls_through :
    deltaWalk vaultLedger { outputs := [], anchor := ⟨0, 100⟩ } deltaShortWalk =
        some { outputs := [(4, 60)], anchor := ⟨1, 101⟩ } ∧
      serve VaultUnspent.currentRules vaultLedger deltaState deltaView deltaView deltaView
        deltaShortWalk = (.coldScan, coldScan vaultLedger deltaView) ∧
      (coldScan vaultLedger deltaView).anchor = ⟨2, 102⟩ := by
  decide

/-- The empty walk, two short of the tip, is not committed: no block fails no proof, and the range
is what refuses it, so the refresh cold-scans rather than serve the cache as it was. A walk of no
block is complete only where the cache's anchor already is the tip
(`VaultUnspent.coversRange_empty`). Under the withdrawn walk range it is committed
(`short_and_empty_walk_committed_with_asRead`); both values of the delta commit discard it. -/
@[req "WTC-6"]
theorem delta_walk_empty_below_tip_falls_through :
    deltaWalk vaultLedger { outputs := [], anchor := ⟨0, 100⟩ } deltaEmptyWalk =
        some { outputs := [], anchor := ⟨0, 100⟩ } ∧
      serve VaultUnspent.currentRules vaultLedger deltaState deltaView deltaView deltaView
        deltaEmptyWalk = (.coldScan, coldScan vaultLedger deltaView) ∧
      (coldScan vaultLedger deltaView).anchor = ⟨2, 102⟩ := by
  decide

/-- Under `current`, over every ledger, state, view, scan and pair of caches: a walk that succeeds
from a still-active base and covers its whole range is committed, whichever branch its last block
is on. `WTC-12`: "after the loop the hash at the last height still equals the last scanned hash" —
`deltaWalk` has made that check against the view read after the loop, and the view captured when
the walk starts is asked for the base and the range only. -/
@[req "WTC-6"]
theorem walk_committed_on_any_branch_with_current (L : Ledger) (st : State) (w : View) (s : Scan)
    (c c' : Cache) (hb : deltaBase VaultUnspent.currentRetryTrigger st = some c)
    (ha : c.anchor.active w = true) (hw : deltaWalk L c s = some c')
    (hc : coversRange c w s = true) :
    deltaFrom VaultUnspent.currentRules L st w s = some c' := by
  refine ?walk_committed_on_any_branch_with_current
  simp only [VaultUnspent.currentRules, VaultUnspent.currentDeltaCommit,
    VaultUnspent.currentChainTie,
    delta_commits_walk_on_any_branch VaultUnspent.currentWalkRange
      VaultUnspent.currentRetryTrigger L st w s c c' hb ha hw hc]

/-- The walk read on the branch the chain moved to. The short view is captured when the walk
starts; the chain then moves to `VaultUnspent.deltaForkView`, and `VaultUnspent.deltaForkWalk`
reads that branch: it links from the cache's anchor, covers heights 1 to 2, the whole range the
short view set, and its last block `(2, 202)` is active on the view read after its loop, though it
is not the block the short view has at height 2. It is committed. The fire-time read on the chain
as it now is takes the cache it leaves, and the read on the chain that was left refuses it —
`WTC-5`: "MUST refuse if the cache's anchor is not the current tip". Under the withdrawn chain tie
the walk is discarded for a cold scan (`off_branch_walk_refused_with_tied`). -/
@[req "WTC-6"]
theorem off_branch_walk_committed :
    deltaWalk vaultLedger { outputs := [], anchor := ⟨0, 100⟩ } deltaForkWalk =
        some { outputs := [], anchor := ⟨2, 202⟩ } ∧
      coversRange { outputs := [], anchor := ⟨0, 100⟩ } deltaView deltaForkWalk = true ∧
      Anchor.active deltaView ⟨2, 202⟩ = false ∧
      serve VaultUnspent.currentRules vaultLedger deltaState deltaView deltaView deltaView
        deltaForkWalk = (.deltaWalk, { outputs := [], anchor := ⟨2, 202⟩ }) ∧
      fireTimeRead deltaForkView { outputs := [], anchor := ⟨2, 202⟩ } = some [] ∧
      fireTimeRead deltaView { outputs := [], anchor := ⟨2, 202⟩ } = none := by
  decide

/-- The refresh that finds the latch set, no cold scan published since it set and no attempt in
progress cold-scans, whatever the cache holds: the same cache and the same walk
`latched_walk_advances_the_cache` commits are passed over for the cold scan, which replaces the
cache and starts an attempt from itself. `WTC-9`: "From the latch setting until a cold scan has
replaced the cache, every refresh with no attempt in progress starts a repair attempt from a cold
scan, whatever cache it holds". Under the retry trigger the amendment of 2026-10-01 had withdrawn
the walk is served and no attempt starts (`latched_unscanned_walks_with_noFirstScan`). -/
@[req "WTC-9"]
theorem latched_unscanned_cold_scans :
    let st' := refresh VaultUnspent.currentRules vaultLedger deltaUnscannedState deltaView
      deltaView deltaView deltaTipWalk
    serve VaultUnspent.currentRules vaultLedger deltaUnscannedState deltaView deltaView deltaView
        deltaTipWalk = (.coldScan, coldScan vaultLedger deltaView) ∧
      st'.latched = true ∧ st'.scanned = true ∧
      st'.repairScan = some (coldScan vaultLedger deltaView) ∧
      st'.cache = some (coldScan vaultLedger deltaView) := by
  decide

/-- (iv) The liveness consequence, exhibited. With the latch set, a cold scan published since and the
attempt failed, the refresh serves the walk from the cache and starts no attempt; the refresh a
block later walks on from the cache that one left and starts none either. `WTC-9`: "A failed build
or repair is therefore not retried while delta walks succeed". The retry comes with the next cold
scan the cache itself needs: offered a walk whose block does not link to the cached anchor, which
fails `WTC-12`'s first check, the refresh falls through to the cold scan and starts an attempt from
it.
Under the retry trigger of 2026-10-01 the first refresh cold-scans of its own
(`failed_attempt_rescans_with_everyRefresh`). -/
@[req "WTC-9"]
theorem failed_attempt_not_retried_while_walks_succeed :
    let st' := refresh VaultUnspent.currentRules vaultLedger deltaFailedState deltaView deltaView
      deltaView deltaTipWalk
    let next : Scan := { blocks := blocksOf [103] 3 102, spends := [], after := deltaGrownView }
    let unlinked : Scan :=
      { blocks := blocksOf [103] 3 999, spends := [], after := deltaGrownView }
    serve VaultUnspent.currentRules vaultLedger deltaFailedState deltaView deltaView deltaView
        deltaTipWalk = (.deltaWalk, { outputs := [(4, 60)], anchor := ⟨2, 102⟩ }) ∧
      st'.latched = true ∧ st'.attempting = false ∧
      (refresh VaultUnspent.currentRules vaultLedger st' deltaGrownView deltaGrownView
        deltaGrownView next).attempting = false ∧
      (refresh VaultUnspent.currentRules vaultLedger st' deltaGrownView deltaGrownView
        deltaGrownView next).cache = some { outputs := [(4, 60)], anchor := ⟨3, 103⟩ } ∧
      (refresh VaultUnspent.currentRules vaultLedger st' deltaGrownView deltaGrownView
        deltaGrownView unlinked).repairScan = some (coldScan vaultLedger deltaGrownView) := by
  decide

/-! ### The walk's own tip: the block that lands during the wallet read

`WTC-6`: "the lesser of the tip captured when the walk starts and 32 blocks above that anchor".
The tip the walk measures its range by is captured when the walk starts, not when the refresh
does. -/

/-- A node in its steady state: the latch clear, a wallet usable on the short view, and the cache
at that view's tip `(2, 102)`. -/
@[req "WTC-6"]
def steadyState : State :=
  { wallet := deltaState.wallet, latched := false, scanned := false, repairScan := none,
    cache := some { outputs := [(4, 60)], anchor := ⟨2, 102⟩ } }

/-- A block arrives during the wallet read. The refresh captured the short view, tip `(2, 102)`,
before the listing; when the reconciliation ends the tip is `(3, 103)`, so the read's bracket
discards it, though the wallet is usable and the same read with no block arriving is served. The
delta walk then starts and captures its own tip, `(3, 103)`: the one block above the cache's anchor
is its whole range, it is committed, and the fire-time read on the new tip takes the cache it
leaves. No cold scan runs. Measured against the tip the refresh captured first the same walk would
overrun its range, which is why the walk reads its own view. Every value of every guard commits
this walk, so no flip turns this red. -/
@[req "WTC-6"]
theorem block_during_wallet_read_is_walked :
    let s : Scan := { blocks := blocksOf [103] 3 102, spends := [], after := deltaGrownView }
    let st' := refresh VaultUnspent.currentRules vaultLedger steadyState deltaView deltaGrownView
      deltaGrownView s
    usable deltaView steadyState.wallet = true ∧
      walletServed steadyState deltaView deltaView = true ∧
      walletServed steadyState deltaView deltaGrownView = false ∧
      coversRange { outputs := [(4, 60)], anchor := ⟨2, 102⟩ } deltaView s = false ∧
      coversRange { outputs := [(4, 60)], anchor := ⟨2, 102⟩ } deltaGrownView s = true ∧
      serve VaultUnspent.currentRules vaultLedger steadyState deltaView deltaGrownView
        deltaGrownView s = (.deltaWalk, { outputs := [(4, 60)], anchor := ⟨3, 103⟩ }) ∧
      st'.attempting = false ∧
      st'.cache.bind (fireTimeRead deltaGrownView) = some [(4, 60)] := by
  decide
/-! ### `WTC-9`'s latch scope: the wallet that holds no marker -/

/-- (iii) Under `current`, over every view, wallet holding no marker and latch: observing leaves
the latch as it was. `WTC-9`: "A wallet holding no completion marker is not latched, `WTC-8`
already keeping it out of use". -/
@[req "WTC-9"]
theorem unbuilt_wallet_never_latches_with_current (v : View) (w : Wallet) (l : Bool)
    (h : w.markers = []) : observe VaultUnspent.currentLatchScope v w l = l := by
  refine ?unbuilt_wallet_never_latches_with_current
  simp only [VaultUnspent.currentLatchScope, unbuilt_wallet_never_latches v w l h]

/-- The node whose first wallet build has failed (`VaultUnspent.unbuiltState`). Observing the short
view latches nothing and leaves the state as it was, and the wallet is not usable — `WTC-8` is what
keeps it out of use. A refresh offered the walk of no block from the cache, which is already at the
tip, serves that walk and starts nothing: the state it leaves is the state it found, so the failed
build is not retried while walks succeed and costs no scan of its own. The same node with no cache
yet is where the build starts: `WTC-6`'s order reaches the cold scan, and the refresh starts the
first build from it, with the latch still clear. `WTC-9`: "its first build, and any retry after a
failed one, starts the same way, from a cold scan `WTC-6` reaches with no attempt in progress".
Under the withdrawn latch scope the observation latches the wallet and the refresh cold-scans
(`unbuilt_wallet_latches_with_vacuous`). -/
@[req "WTC-9"]
theorem unbuilt_wallet_not_latched :
    unbuiltState.observe VaultUnspent.currentLatchScope deltaView = unbuiltState ∧
      usable deltaView unbuiltWallet = false ∧
      serve VaultUnspent.currentRules vaultLedger unbuiltState deltaView deltaView deltaView
        deltaEmptyWalk = (.deltaWalk, coldScan vaultLedger deltaView) ∧
      refresh VaultUnspent.currentRules vaultLedger unbuiltState deltaView deltaView deltaView
        deltaEmptyWalk = unbuiltState ∧
      (let st' := refresh VaultUnspent.currentRules vaultLedger { unbuiltState with cache := none }
        deltaView deltaView deltaView deltaEmptyWalk
      st'.latched = false ∧ st'.repairScan = some (coldScan vaultLedger deltaView) ∧
        st'.cache = some (coldScan vaultLedger deltaView)) := by
  decide
/-- The joint attempt invariant is preserved by every refresh under the current rules. -/
@[req "WTC-9"]
theorem attemptInvariant_refresh_with_current (L : Ledger) (st : State)
    (v after walk : View) (s : Scan) (hi : attemptInvariant st = true) :
    attemptInvariant (refresh VaultUnspent.currentRules L st v after walk s) = true :=
  attemptInvariant_refresh VaultUnspent.currentRules L st v after walk s hi

/-- A re-import ends the attempt under the current import rules, establishing the pair. -/
@[req "WTC-9"]
theorem attemptInvariant_repair_with_current (L : Ledger)
    (scanView atDescriptors atMarker : View) (s : Scan) (st : State) :
    attemptInvariant (repair VaultUnspent.currentMarkerAnchor VaultUnspent.current L
      scanView atDescriptors atMarker s st) = true :=
  attemptInvariant_repair VaultUnspent.currentMarkerAnchor VaultUnspent.current L
    scanView atDescriptors atMarker s st

/-- Observation preserves both halves under the current scope, including a running first build.
The `.vacuous` flip refutes this universal at this declaration. -/
@[req "WTC-9"]
theorem attemptInvariant_observe_with_current (v : View) (st : State)
    (hi : attemptInvariant st = true) :
    attemptInvariant (st.observe VaultUnspent.currentLatchScope v) = true := by
  refine ?attemptInvariant_observe_with_current
  simp only [VaultUnspent.currentLatchScope, attemptInvariant_observe v st hi]

/-- A first build actually started by a refresh of the marker-free wallet with no cache.
`WTC-9`: "its first build, and any retry after a failed one, starts the same way, from a cold
scan `WTC-6` reaches with no attempt in progress". -/
@[req "WTC-9"]
def firstBuildRunning : State :=
  refresh VaultUnspent.currentRules vaultLedger { unbuiltState with cache := none }
    deltaView deltaView deltaView deltaEmptyWalk

/-- A successful marker-free first build shows the marker and attempt premises shared by
`first_build_is_of_the_attempts_scan` and `first_build_reads_the_attempts_settled_block` are
satisfiable, not their provenance conclusions. The refresh is offered the empty walk; the import
gets the independent proven walk above genesis. No pair of distinct views is exhibited: under the
second theorem's ancestry premise, views with a shared tip agree below it
(`Chain.Ancestry.below_shared_tip`), and `View`'s documented `none` past the tip leaves nothing
above it. -/
@[req "WTC-9"]
theorem first_build_provenance_with_current :
    let st := { unbuiltState with cache := none }
    let done := repair VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
      deltaView deltaView deltaView deltaTipWalk firstBuildRunning
    st.wallet.markers = [] ∧ st.attempting = false ∧ done.wallet.markers ≠ [] := by
  decide

/-- The no-attempt base and refresh preservation establish the joint invariant of an actual
running first build. Observation preservation then covers that build with its latch clear;
both ways of ending it establish the pair as well. -/
@[req "WTC-9"]
theorem first_build_attemptInvariant_with_current :
    firstBuildRunning.attempting = true ∧ firstBuildRunning.latched = false ∧
      attemptInvariant firstBuildRunning = true ∧
      (firstBuildRunning.observe VaultUnspent.currentLatchScope deltaView).attempting = true ∧
      attemptInvariant (firstBuildRunning.observe VaultUnspent.currentLatchScope deltaView) = true ∧
      attemptInvariant (endAsFailure firstBuildRunning) = true ∧
      attemptInvariant (repair VaultUnspent.currentMarkerAnchor VaultUnspent.current vaultLedger
        deltaView deltaView deltaView deltaTipWalk firstBuildRunning) = true := by
  have hi : attemptInvariant firstBuildRunning = true :=
    attemptInvariant_refresh_with_current vaultLedger _ deltaView deltaView deltaView
      deltaEmptyWalk (attemptInvariant_of_no_attempt _ rfl)
  refine ⟨by decide, by decide, hi, by decide, ?_, ?_, ?_⟩
  · exact attemptInvariant_observe_with_current deltaView firstBuildRunning hi
  · exact attemptInvariant_endAsFailure firstBuildRunning
  · exact attemptInvariant_repair_with_current vaultLedger deltaView deltaView deltaView
      deltaTipWalk firstBuildRunning

/-- The latched case uses invariant evidence from the base through refresh and observation,
then the no-scan corollary without a separately assumed `scanned` field. The re-import offered
here has another scan and fails, as `def21_failed_attempt_not_retried` exhibits. `WTC-9`:
"the next attempt starts only from a cold scan `WTC-6` itself reaches with none in progress,
and starts no scan of its own". -/
@[req "WTC-9"]
theorem latched_attempt_no_scan_from_invariant :
    let st := (refresh VaultUnspent.currentRules vaultLedger def21Latched
      (chainOf vaultChainB) (chainOf vaultChainB) (chainOf vaultChainB) def21NoWalk).observe
        VaultUnspent.currentLatchScope (chainOf vaultChainB)
    deltaBase .neededScan (repair VaultUnspent.currentMarkerAnchor VaultUnspent.current
      vaultLedger (chainOf vaultChainA) (chainOf vaultChainA) (chainOf vaultChainA)
      vaultWalkA st) = st.cache ∧
      deltaBase .neededScan (endAsFailure st) = st.cache := by
  dsimp only
  apply invariant_failed_attempt_starts_no_scan
  · apply attemptInvariant_observe_with_current
    apply attemptInvariant_refresh_with_current
    exact attemptInvariant_of_no_attempt _ rfl
  · decide
  · decide

end BtcPolicy.Exhibits.VaultUnspentCache

namespace BtcPolicy.Exhibits.WatchtowerAlerts
open BtcPolicy.Alerts

/-! ## Watchtower recognition: `WTC-18`'s two twins under `current`

`Alerts.lean` owns recognition as a guard parameter. Every theorem over `current` is here; the
two refutations under the refuted readings, `.coSigned` and `.evaluated`, are beside the
parameter in `Alerts.lean`. A universal theorem's proof opens by naming its goal after the
theorem and then case-splits on the guard: every value the proposition holds under closes from
`Alerts.lean`'s value-indexed lemma, and the one value that refutes it closes from the guard's
literal alone, so a flip leaves red exactly the theorems it refutes and the red names the
theorem. The case label the controls grep, `<theorem>.<value>.refl`, is built by
`generalize hc : Alerts.current = g` followed by `cases g`, which labels the branch with the value,
and by `cases hc` on the guard equation in the refuting branch, which appends `.refl`. -/

/-- Under `current`, over every record and txid: a txid the record accepted is recognised.
`WTC-18`: "Recognition is by **validation and acceptance**, never by co-signing and never by
evaluation". -/
@[req "WTC-18"]
theorem accepted_recognised_with_current (r : Record) (txid : Nat) (h : txid ∈ r.accepted) :
    recognised Alerts.current r txid = true := by
  refine ?accepted_recognised_with_current
  generalize hc : Alerts.current = g
  cases g with
  | validated => exact accepted_recognised .validated (by decide) r txid h
  | coSigned => cases hc
  | evaluated => exact accepted_recognised .evaluated (by decide) r txid h

/-- Under `current`, over every well-formed record and txid: a txid the record refused is not
recognised. `WTC-18`: "a spend a node REFUSED was evaluated". -/
@[req "WTC-18"]
theorem refused_not_recognised_with_current (r : Record) (txid : Nat) (hw : r.wf)
    (h : txid ∈ r.refused) : recognised Alerts.current r txid = false := by
  refine ?refused_not_recognised_with_current
  generalize hc : Alerts.current = g
  cases g with
  | validated => exact refused_not_recognised .validated (by decide) r txid hw h
  | coSigned => exact refused_not_recognised .coSigned (by decide) r txid hw h
  | evaluated => cases hc

/-- Under `current`, over every list of records and every Normal-branch spend: a spend every
record accepted alerts on none. `WTC-18`: "A legitimate spend is accepted by all `n` and alerts
nowhere". -/
@[req "WTC-18"]
theorem accepted_everywhere_silent_with_current (records : List Record) (s : Spend)
    (hr : isRecovery s.witness = false) (h : ∀ r ∈ records, s.txid ∈ r.accepted) :
    alerting Alerts.current records s = 0 := by
  refine ?accepted_everywhere_silent_with_current
  generalize hc : Alerts.current = g
  cases g with
  | validated => exact accepted_everywhere_silent .validated (by decide) records s hr h
  | coSigned => cases hc
  | evaluated => exact accepted_everywhere_silent .evaluated (by decide) records s hr h

/-- Under `current`, over every list of well-formed records and every spend: a spend every
record refused alerts on all. `WTC-18`: "a theft the honest nodes refuse is in nobody's set and
alerts everywhere". -/
@[req "WTC-18"]
theorem refused_everywhere_alerts_with_current (records : List Record) (s : Spend)
    (h : ∀ r ∈ records, r.wf ∧ s.txid ∈ r.refused) :
    alerting Alerts.current records s = records.length := by
  refine ?refused_everywhere_alerts_with_current
  generalize hc : Alerts.current = g
  cases g with
  | validated => exact refused_everywhere_alerts .validated (by decide) records s h
  | coSigned => exact refused_everywhere_alerts .coSigned (by decide) records s h
  | evaluated => cases hc

/-! ### The federation's twins under `current` -/

/-- The legitimate spend, accepted by all five and signed by three, alerts nowhere under
`current`. `WTC-18`: "A legitimate spend is accepted by all `n` and alerts nowhere". Under
`.coSigned` it false-alarms on two (`legit_false_alarms_with_coSigned`). -/
@[req "WTC-18"]
theorem legit_silent_with_current : alerting Alerts.current federation legitSpend = 0 := by
  decide

/-- The theft fanned to every honest node, refused by all five and in nobody's accepted set,
alerts `UNRECOGNIZED_SPEND` on all five under `current`. `WTC-18`: "a theft the honest nodes
refuse is in nobody's set and alerts everywhere". Under `.evaluated` it alerts nowhere
(`theft_suppressed_with_evaluated`). -/
@[req "WTC-18"]
theorem theft_alerts_everywhere_with_current :
    countVerdict .unrecognizedSpend Alerts.current federation theftSpend = 5 ∧
      alerting Alerts.current federation theftSpend = federation.length := by
  decide

/-- The precedence under `current`: a Recovery-branch spend whose txid is in every accepted set
alerts `RECOVERY_PATH_SPEND` on every node. `WTC-17`: "a witness whose branch selector is the
empty push (`CHN-9`) is a `RECOVERY_PATH_SPEND`, even if the txid is in the authorized set".
Its short-witness variant reads as non-recovery (`WTC-19`) and alerts as unrecognised on every
node when unauthorized, and not at all when authorized. -/
@[req "WTC-17"]
theorem recovery_never_swallowed_with_current :
    (∀ r ∈ federation, recoverySpend.txid ∈ r.accepted) ∧
      countVerdict .recoveryPathSpend Alerts.current federation recoverySpend = 5 ∧
      isRecovery shortUnauthorized.witness = false ∧
      countVerdict .unrecognizedSpend Alerts.current federation shortUnauthorized = 5 ∧
      alerting Alerts.current federation shortAuthorized = 0 := by
  decide

end BtcPolicy.Exhibits.WatchtowerAlerts

namespace BtcPolicy.Exhibits.PackageAncestry
open BtcPolicy.Package
open BtcPolicy.VaultUnspent (Snapshot)
open BtcPolicy.Coverage (Outpoint)

/-! ## Package ancestry and replacement: `F54`'s row under `current`

`Package.lean` owns the replacement's ancestry read as a guard parameter. Every theorem over
`current` is here; the twin under the withdrawn value, `.plainRead`, is beside the parameter in
`Package.lean`. A universal theorem's proof opens by naming its goal after the theorem, so the red
a flip leaves names the theorem it refutes. -/

/-- Under `current`, over every creator, snapshot, membership read, authorized set and candidate:
a replacement over a resident `r` in the membership read and in the authorized set, with exactly
`r`'s ordered inputs, whose every unconfirmed ancestor is authorized and within the limit, is
admitted with those ancestors, whatever the read shows. `WTC-24`: "the resident's own inputs are
read as unspent for the replacement". -/
@[req "WTC-25"]
theorem replacement_admitted_with_current (creator : Creator) (snap : Snapshot)
    (mem : MempoolRead) (authorized : List Nat) (c : Candidate) (r : Nat) (ins : List Outpoint)
    (hm : mem.lookup r = some ins) (hr : r ∈ authorized) (hc : c.inputs = ins)
    (hanc : ∀ t ∈ ancestors creator mem c.inputs, t ∈ authorized)
    (hlim : (ancestors creator mem c.inputs).length ≤ ancestorLimit) :
    validate Package.current creator snap mem authorized c (some r) =
      .admitted (ancestors creator mem c.inputs) := by
  refine ?replacement_admitted_with_current
  simp only [Package.current,
    replacement_admitted creator snap mem authorized c r ins hm hr hc hanc hlim]

/-- The twin under `current`: `R'` over `[X, Y]`, the read showing neither, is admitted with no
unconfirmed ancestor — `X` and `Y` are confirmed and their creator is not resident. Under
`.plainRead` it is refused "unknown or spent" (`twin_refused_with_plainRead`). This is also the
positive ordered-outpoints exhibit, `[X, Y]` over `[X, Y]`, through the whole validation. -/
@[req "WTC-25"]
theorem twin_admitted_with_current :
    validate Package.current twinCreator twinSnapshot twinMembership twinAuthorized twinReplacement
      (some twinResident) = .admitted [] := by
  decide

/-- A snapshot whose read shows the two confirmed coins `X` and `Y`. -/
@[req "WTC-24"]
def confirmedSnapshot : Snapshot := { tip := ⟨5, 105⟩, sequence := 7, read := [(1, 50), (2, 50)] }

/-- A candidate over two confirmed vault coins with no resident is admitted under `current`, with
no ancestor: nothing above holds vacuously. -/
@[req "WTC-24"]
theorem confirmed_coins_admitted_with_current :
    validate Package.current twinCreator confirmedSnapshot [] [] twinReplacement none =
      .admitted [] := by
  decide

/-- The membership read of one authorized parent `P1 = 21` over a confirmed coin. -/
@[req "WTC-24"] def parentMembership : MempoolRead := [(21, [50])]

/-- A candidate spending one output of an authorized resident parent is admitted under `current`
with that parent as its one ancestor. `WTC-24`: "an unconfirmed parent MUST be resident in the
mempool AND in the vault-authorized set". -/
@[req "WTC-24"]
theorem resident_parent_admitted_with_current :
    validate Package.current diamondCreator diamondSnapshot parentMembership [21]
      { txid := 24, inputs := [31] } none = .admitted [21] := by
  decide

end BtcPolicy.Exhibits.PackageAncestry

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

def externalPath : SinglePath := ⟨10, true⟩
def internalPath : SinglePath := ⟨11, true⟩
def definitePath : SinglePath := ⟨12, false⟩
def mixedDescriptor : Descriptor := ⟨[externalPath, internalPath, definitePath]⟩
def derive (p : SinglePath) (i : Nat) : Option Script :=
  some [p.id, if p.id = 12 then 0 else i]

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

def node (self : Nat) : Node := { A with id := self, t := 3 }
def initial (self : Nat) : World := { node := node self, exposure := [] }
def target : Tx := ⟨100, [0, 1], 10⟩
def escape : Tx := ⟨101, [0, 1], 0⟩
def oldSpend := cand 1 target true (some 100) 900
def oldEscape := cand 2 escape false none 900
def newSpend := cand 5 target true (some 300) 1000
def newEscape := cand 6 escape false none 1000
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

def linkedHonest : List Nat := [1, 2, 3, 4]
def linkedStart : Federation.Fed := { worlds := initial, net := [] }

/-- Identity 0's row in `inventory`, here a partial signed with its copied key. -/
def forgedRow : Exp :=
  { msg := sighash target 0, input := 0, signer := 0, hot := true, cid := newSpend.id }

def acceptOld (i : Nat) : Federation.Step :=
  .process i (envAt 10 10) (.accept 10 false (Wall.sample 900) oldSpend oldEscape)
def acceptNew (i : Nat) : Federation.Step :=
  .process i (envAt 110 110) (.accept 20 true (Wall.sample 1000) newSpend newEscape)

def linkedSteps : List Federation.Step :=
  [acceptOld 1, acceptOld 2, acceptOld 3, acceptOld 4, .emit 3 10, .emit 4 10,
   .deliver 1 (envAt 20 20) ⟨3, 10⟩, .deliver 1 (envAt 21 21) ⟨4, 10⟩,
   .deliver 2 (envAt 20 20) ⟨3, 10⟩, .deliver 2 (envAt 21 21) ⟨4, 10⟩,
   .process 1 (envAt 100 100) .firePass, .process 2 (envAt 100 100) .firePass,
   acceptNew 1, acceptNew 2, acceptNew 3, acceptNew 4,
   .emit 1 20, .emit 2 20, .emit 3 20, .emit 4 20,
   .deliver 1 (envAt 120 120) ⟨3, 20⟩, .deliver 1 (envAt 121 121) ⟨4, 20⟩,
   .deliver 2 (envAt 120 120) ⟨3, 20⟩, .deliver 2 (envAt 121 121) ⟨4, 20⟩,
   .deliver 3 (envAt 120 120) ⟨1, 20⟩, .deliver 3 (envAt 121 121) ⟨2, 20⟩,
   .deliver 4 (envAt 120 120) ⟨1, 20⟩, .deliver 4 (envAt 121 121) ⟨2, 20⟩,
   .process 1 (envAt 150 150) .firePass, .process 2 (envAt 150 150) .firePass,
   .process 3 (envAt 150 150) .firePass, .process 4 (envAt 150 150) .firePass,
   .extract 0, .forge forgedRow]

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

def deliveredSteps : List Federation.Step :=
  linkedSteps ++ [.deliverPartial 1 (envAt 160 160)
      { msg := sighash target 0, input := 0, signer := 2, hot := true, cid := oldSpend.id },
    .deliverPartial 1 (envAt 160 160) forgedRow]

/-- Possession only where a partial is delivered. `linkedSteps` delivers none. Extended by the
deliveries of node 2's and identity 0's target rows to node 1, node 1's old candidate holds 1 and 2
and its new one 1 and 0: the rows sit under two commitments, and neither candidate holds three.
Nodes 2–4 still hold only their own partial, and the inventory's exposed quorum is what it was. A
holder of rows under both commitments is outside `Cand.heldSigners`, which is per candidate. -/
@[req "DUR-28"]
theorem linked_possession_only_where_delivered :
    linkedSteps.all (fun s => match s with | .deliverPartial .. => false | _ => true) = true ∧
    Federation.legal current linkedHonest linkedStart deliveredSteps = true ∧
    ((Federation.runFrom current linkedStart deliveredSteps).worlds 1).node.cands.any
      (fun c => c.id == oldSpend.id && c.frozen && c.heldSigners == [1, 2]) = true ∧
    ((Federation.runFrom current linkedStart deliveredSteps).worlds 1).node.cands.any
      (fun c => c.id == newSpend.id && c.frozen && c.heldSigners == [1, 0]) = true ∧
    ((Federation.runFrom current linkedStart deliveredSteps).worlds 1).node.cands.all
      (fun c => !heldQuorum 3 c) = true ∧
    ([2, 3, 4].all fun self =>
      ((Federation.runFrom current linkedStart deliveredSteps).worlds self).node.cands.all
        (fun c => c.heldSigners == [self])) = true ∧
    exposedQuorum (Federation.partsWorld (Federation.runFrom current linkedStart deliveredSteps) 1)
      oldSpend = true := by
  decide +kernel

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

def cfg : Cfg :=
  { derive := Membership.derive, max := 2, vault := ⟨[Membership.definitePath]⟩,
    escape := ⟨[Membership.externalPath]⟩,
    allow := [⟨[Membership.externalPath, Membership.internalPath]⟩], hotMaxPerTx := 60 }

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

namespace BtcPolicy.Exhibits.Ingress
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ingress
open BtcPolicy.Kernel.RegistrationCases (A env0 envFire envAt)
open BtcPolicy.Federation (Step Fed Trace HotBinding legal runFrom record execution_of_legal)
open BtcPolicy.Federation.Cases (fed0 fed0_fresh honest)

/-! ### Checked ingress

Research task `bps-uaer.7`. The policy configuration is `Exhibits.Evaluate.cfg` (vault script
`[12, 0]`, Escape scripts `[10, i]`, allowlist scripts `[11, i]`, `hot_max_per_tx` 60). The
identities are `Ingress.code`, which is injective (`Ingress.code_injective`). The spend sends 55 to
an allowlist script with 40 of vault change; the Escape sends 98 back to an Escape script; both
spend one 32-byte outpoint holding 100. Every candidate below is computed by `Ingress.check`, never
written by hand. -/

def txidA : Encode.Bytes := List.replicate 31 0 ++ [1]

def ctx0 : Ctx :=
  { cfg := BtcPolicy.Exhibits.Evaluate.cfg, walletId := List.replicate 32 7,
    policyVersion := 1, txId := code, commitId := code, outpoint := code }

def spendPsbt : BtcPolicy.Evaluate.Psbt :=
  { txInputs := [⟨txidA, 0, 0⟩], txOutputs := [⟨[12, 0], 40⟩, ⟨[11, 1], 55⟩],
    inputMaps := [some ⟨[12, 0], 100⟩], outputHints := [true, false] }

def escPsbt : BtcPolicy.Evaluate.Psbt :=
  { txInputs := [⟨txidA, 0, escapeSequence⟩], txOutputs := [⟨[10, 0], 98⟩],
    inputMaps := [some ⟨[12, 0], 100⟩], outputHints := [false] }

def req0 : Request :=
  { spend := ⟨spendPsbt, 2, 0, none⟩, escape := ⟨escPsbt, 2, 0, none⟩,
    expiry := 200, fireAt := some (Wall.sample 100) }

def sp0 : Cand := cand ctx0 req0 req0.spend true req0.fireAt
def es0 : Cand := cand ctx0 req0 req0.escape false none

/-- An accepted request: the pair `Kernel.accept` receives, the spend's outflow and class read from
its outputs, the Escape's zero outflow. The cap and the allowlist come out of
`Evaluate.acceptance_exact` through `Ingress.accepted_spend`. -/
@[req "SPN-5"]
theorem checked_pair :
    check ctx0 true req0 = .accepted sp0 es0 ∧ sp0.hot = true ∧ es0.hot = false ∧
    sp0.tx.outflow = 55 ∧ es0.tx.outflow = 0 ∧ sp0.tx.inputs = es0.tx.inputs ∧ sp0.tx.id ≠ es0.tx.id :=
  ⟨by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel, rfl, by decide +kernel⟩

@[req "POL-11"]
theorem checked_within_cap : sp0.tx.outflow ≤ ctx0.cfg.hotMaxPerTx :=
  (accepted_spend checked_pair.1).2.2.1

/-- `POL-11` at any checked acceptance: the Escape carries no Hot outflow. It rests on
`Exhibits.non_hot_class_zero_outflow`, so it reads the current classification. -/
@[req "POL-11"]
theorem escape_zero_outflow {ctx : Ctx} {fits : Bool} {q : Request} {sp es : Cand}
    (h : check ctx fits q = .accepted sp es) : es.tx.outflow = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := accepted_validates h
  exact BtcPolicy.Exhibits.non_hot_class_zero_outflow _ (.inl (accepted_escape h).1)

/-- Two copies of the request. One differs in its output hints alone and yields the same verdict.
The other reports a different `witness_utxo` value: the fee `CHN-24` binds moves, so the commitment
id moves, while the transaction, its sighash and its amount stay. Two nodes taking the two copies
reserve the same amount (`POL-18`). -/
def hintCopy : Request :=
  { req0 with spend := { req0.spend with psbt := { spendPsbt with outputHints := [false, false] } } }
def valueCopy : Request :=
  { req0 with spend := { req0.spend with psbt := { spendPsbt with inputMaps := [some ⟨[12, 0], 101⟩] } } }

def lcfg : Ledger.Config := { cap := 100, window := 600 }
def sysAt (i : Nat) : Ledger.Sys := { world := { node := { A with id := i }, exposure := [] }, led := [] }
def reserveAt (i : Nat) (env : Env) (q : Request) : List (Nat × Nat) :=
  (Ledger.sysStep Ledger.current lcfg current env (sysAt i)
    (.accept 10 false (Wall.sample 200) (cand ctx0 q q.spend true q.fireAt)
      (cand ctx0 q q.escape false none))).1.led.map fun r => (r.cid, r.amount)

@[req "POL-18"]
theorem copies_reserve_alike :
    check ctx0 true hintCopy = check ctx0 true req0 ∧
    check ctx0 true valueCopy = .accepted (cand ctx0 valueCopy valueCopy.spend true valueCopy.fireAt)
      (cand ctx0 valueCopy valueCopy.escape false none) ∧
    (cand ctx0 valueCopy valueCopy.spend true valueCopy.fireAt).id ≠ sp0.id ∧
    (cand ctx0 valueCopy valueCopy.spend true valueCopy.fireAt).tx = sp0.tx ∧
    reserveAt 1 env0 req0 = [(sp0.id, 55)] ∧
    reserveAt 2 (envAt 70 30) hintCopy = [(sp0.id, 55)] ∧
    reserveAt 3 (envAt 60 20) valueCopy =
      [((cand ctx0 valueCopy valueCopy.spend true valueCopy.fireAt).id, 55)] := by
  decide +kernel

/-! #### Refusals stay in the input domain -/

/-- Malformed data. A 31-byte txid is outside the decoded domain; a spend with no inputs decodes
and is refused by `POL-7`; a member whose upstream signature verdict failed is refused with it. -/
@[req "POL-7"]
theorem malformed_refused :
    check ctx0 true { req0 with spend := { req0.spend with psbt :=
      { spendPsbt with txInputs := [⟨List.replicate 31 0, 0, 0⟩] } } } = .malformed ∧
    check ctx0 true { req0 with spend := { req0.spend with psbt :=
      { spendPsbt with txInputs := [], inputMaps := [] } } } = .refused .PSBT_INCONSISTENT ∧
    check ctx0 true { req0 with spend := { req0.spend with upstream := some .USER_SIG_INVALID } } =
      .refused .USER_SIG_INVALID := by
  decide +kernel

def stranger (hs : List Bool) : Request :=
  { req0 with spend := { req0.spend with psbt :=
      { spendPsbt with txOutputs := [⟨[12, 0], 40⟩, ⟨[99], 55⟩], outputHints := hs } } }

/-- A misleading derivation hint. An output no descriptor derives is refused whatever its hint says:
the hint changes the refusal's spelling and never admits it (`Ingress.hints_never_pass`). -/
@[req "POL-10"]
theorem hint_admits_nothing :
    check ctx0 true (stranger [true, true]) = .refused .CHANGE_NOT_DERIVABLE ∧
    check ctx0 true (stranger [false, false]) = .refused .DEST_NOT_ALLOWED := by
  decide +kernel

def rung (amount sequence : Nat) : Member :=
  ⟨{ escPsbt with txInputs := [⟨txidA, 0, sequence⟩], txOutputs := [⟨[10, 0], amount⟩] }, 2, 0, none⟩

/-- The ladder. One good rung is accepted; a malformed final rung — here `CHN-15`'s sequence missing
— refuses the whole request, so nothing is signed; a fourth rung is refused at gate 18. -/
@[req "SPN-27"]
theorem final_rung_refuses_group :
    (check ctx0 true { req0 with rungs := [rung 97 escapeSequence] }).event 10 false (Wall.sample 200) =
      some (.accept 10 false (Wall.sample 200) sp0
        (cand ctx0 { req0 with rungs := [rung 97 escapeSequence] } req0.escape false none)) ∧
    check ctx0 true { req0 with rungs := [rung 97 escapeSequence, rung 96 0] } =
      .refused .PSBT_INCONSISTENT ∧
    (check ctx0 true { req0 with rungs := [rung 97 escapeSequence, rung 96 0] }).event 10 false
      (Wall.sample 200) = none ∧
    check ctx0 true { req0 with rungs := List.replicate 4 (rung 97 escapeSequence) } =
      .refused .PSBT_INCONSISTENT := by
  decide +kernel

/-- `CHN-30`'s count rule. The vault change split into two outputs on a one-input spend passes
`POL-6`'s evaluation and is refused at gate 23. -/
@[req "CHN-30"]
theorem vault_count_refused :
    let p := { spendPsbt with txOutputs := [⟨[12, 0], 20⟩, ⟨[12, 0], 20⟩, ⟨[11, 1], 55⟩],
                              outputHints := [true, true, false] }
    BtcPolicy.Evaluate.evaluate ctx0.cfg p = none ∧
    check ctx0 true { req0 with spend := { req0.spend with psbt := p } } =
      .refused .PSBT_INCONSISTENT := by
  decide +kernel

def tight : Ledger.Config := { cap := 50, window := 600 }
def badEscape : Request := { req0 with escape := rung 98 0 }

/-- Gate 24 before gate 25. With the ledger's verdict on the spend as `fits`, a request whose Escape
fails gate 25 is still refused at gate 24 first, staged, when the reservation would not fit; when it
fits, the Escape's refusal stages nothing. -/
@[req "SPN-5"]
theorem velocity_precedes_escape :
    Ledger.admits tight [] sp0 = false ∧ Ledger.admits lcfg [] sp0 = true ∧
    check ctx0 (Ledger.admits tight [] sp0) badEscape =
      .staged .HOT_VELOCITY_EXCEEDED ((cand ctx0 badEscape badEscape.spend true badEscape.fireAt).id,
        (cand ctx0 badEscape badEscape.escape false none).id) ∧
    check ctx0 (Ledger.admits lcfg [] sp0) badEscape = .refused .PSBT_INCONSISTENT := by
  decide +kernel

/-- A swapped pair. The Escape offered as the spend is escape-class and refused at gate 23
(`CHN-32`); no checked acceptance hands `Kernel.accept` a non-hot spend (`Ingress.accepted_roles`). -/
@[req "CHN-32"]
theorem swapped_pair_refused :
    check ctx0 true { req0 with spend := req0.escape, escape := req0.spend } =
      .refused .PSBT_INCONSISTENT ∧
    ∀ q, check ctx0 true q ≠ .accepted es0 sp0 := by
  refine ⟨by decide +kernel, fun q h => ?_⟩
  have := (accepted_roles h).1
  simp [es0, cand] at this

def overCap : Request :=
  { req0 with spend := { req0.spend with psbt :=
      { spendPsbt with txOutputs := [⟨[12, 0], 30⟩, ⟨[11, 1], 65⟩] } } }

def stagedEvent : Event :=
  ((check ctx0 true overCap).event 11 true (Wall.sample 200)).getD .tick

/-- Refused but staged under duress. A spend over `POL-11`'s per-transaction cap is gate 22's
`HOT_BUDGET_EXCEEDED`, which `SPN-5` stages: a refusal Carrier under duress. At a node already
holding the checked pair, a peer's relay brings that Carrier to the threshold: the node arms and
freezes the resident hot spend, and nothing opens. The accepted Carrier's relay alone opens the
pair. The refused request shares the resident Escape's commitment, so under the withdrawn refusal
rule, `allStaged`, the same relay opens that Escape. -/
@[req "DUR-5"]
theorem staged_duress_opens_nothing :
    check ctx0 true overCap = .staged .HOT_BUDGET_EXCEEDED
      ((cand ctx0 overCap overCap.spend true overCap.fireAt).id,
       (cand ctx0 overCap overCap.escape false none).id) ∧
    (let w := (Kernel.run current { node := { A with id := 1 }, exposure := [] }
        [(env0, .accept 10 false (Wall.sample 200) sp0 es0), (env0, stagedEvent),
         (env0, .receipt 11 2)]).1
     w.node.armed = true ∧ w.node.cands.all (fun c => !c.quorum) = true ∧
       w.node.cands.any (fun c => c.id == sp0.id && c.frozen) = true) ∧
    ((Kernel.run current { node := { A with id := 1 }, exposure := [] }
        [(env0, .accept 10 false (Wall.sample 200) sp0 es0), (env0, .receipt 10 2)]).1.node.cands.any
      (fun c => c.id == sp0.id && c.quorum)) = true := by
  decide +kernel

/-! #### The message binding over a federation -/

def acc (c : Ctx) (i : Nat) (d : Bool) : Step :=
  .process i env0 (.accept 10 d (Wall.sample 200) (cand c req0 req0.spend true req0.fireAt)
    (cand c req0 req0.escape false none))

/-- Three honest nodes take the checked pair, node 3 under duress. Relays open it at nodes 1 and 2,
which release the spend, and arm node 3, whose fire pass releases the Escape. -/
def run (c : Ctx) : List Step :=
  [acc c 1 false, acc c 2 false, acc c 3 true, .emit 1 10, .emit 2 10, .emit 3 10,
   .deliver 1 env0 ⟨2, 10⟩, .deliver 2 env0 ⟨1, 10⟩, .deliver 3 env0 ⟨1, 10⟩,
   .process 1 envFire .firePass, .process 2 envFire .firePass, .process 3 (envAt 120 70) .firePass]

def trace : Trace := record current [] fed0 (run ctx0)
def final : Fed := runFrom current fed0 (run ctx0)

theorem run_legal : legal current honest fed0 (run ctx0) = true := by decide +kernel

/-- The binding derived, on a run with honest rows of both classes: the two spend rows are on the
target message, the Escape's row is on another, and `Federation.HotBinding` holds of the target by
`Ingress.hot_binding`, not by hand. -/
@[req "DUR-8"]
theorem checked_binding :
    (final.parts.map fun x => (x.signer, x.hot, x.input, x.msg == sighash sp0.tx 0)) =
      [(1, true, 0, true), (2, true, 0, true), (3, false, 0, false)] ∧
    HotBinding final (sighash sp0.tx 0) :=
  ⟨by decide +kernel,
    hot_binding (execution_of_legal (.init fed0 fed0_fresh) run_legal)
      (checkedTrace_of ctx0 trace [req0] (by decide +kernel)) code_injective
      (frame_wf (accepted_validates checked_pair.1).1) (accepted_spend checked_pair.1).1⟩

/-- The collision premise is needed. With one identity for every transaction, the same checked run
puts the Escape's honest, non-hot row on the spend's message, and the binding fails: checking alone
does not separate the two members' messages. -/
def ctxCollide : Ctx := { ctx0 with txId := fun _ => 7 }

@[req "DUR-8"]
theorem collision_breaks_binding :
    legal current honest fed0 (run ctxCollide) = true ∧
    CheckedTrace ctxCollide (record current [] fed0 (run ctxCollide)) ∧
    ¬ HotBinding (runFrom current fed0 (run ctxCollide))
      (sighash (cand ctxCollide req0 req0.spend true req0.fireAt).tx 0) :=
  ⟨by decide +kernel, checkedTrace_of _ _ [req0] (by decide +kernel), by decide +kernel⟩

end BtcPolicy.Exhibits.Ingress

namespace BtcPolicy.Exhibits.Lifetime
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Lifetime
open BtcPolicy.Kernel.RegistrationCases (A env0 envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 spendPsbt escPsbt rung)

/-! ### Ingress lifetime seams

Research task `bps-uaer.8`. One node, `Kernel.current`, the checked request `Exhibits.Ingress.req0`
and its context. Every candidate is computed by `Ingress.check` inside `Lifetime.hold`. The refresh
`rf` spends the Escape's input. -/

def conf (g : Subordination) : Lifetime.Cfg :=
  { g := g, lg := Ledger.current, cfg := { cap := 100, window := 600 }, r := Kernel.current,
    ctx := ctx0 }

def st0 : St := { sys := { world := { node := { A with id := 1 }, exposure := [] }, led := [] } }

def rf : Tx := { id := 900, inputs := es0.tx.inputs, outflow := 0 }

/-- `DEF-7`'s race: the spend claims its marker and enters its preflight, a refresh arrives, then
the spend's registration hold runs. -/
def race : List Op := [.claim 1, .refresh env0 rf true, .hold 1 env0 10 false (Wall.sample 200) req0]

/-- With the marker, the refresh is subordinated during the preflight; the pair registers and the
pending log lists the spend. -/
@[req "SPN-31"]
theorem preflight_race_subordinated :
    let s := run (conf Lifetime.current) st0 race
    s.refreshes = [] ∧ s.inFlight = [] ∧ s.sys.world.node.cands.any (·.id == es0.id) = true ∧
      pending Kernel.current env0 s.sys.world.node = [sp0.id] := by
  decide +kernel

/-- `DEF-7`: with subordination reading the pending log alone, the same race registers the refresh
during the preflight, and the registered refresh spends the resident Escape's input. -/
@[req "DEF-7"]
theorem preflight_race_without_marker :
    let s := run (conf .pendingOnly) st0 race
    s.refreshes = [rf] ∧
      s.sys.world.node.cands.any (fun c => c.id == es0.id && conflicts rf c) = true ∧
      pending Kernel.current env0 s.sys.world.node = [sp0.id] := by
  decide +kernel

/-- A panic unwind releases the marker: the refresh the claim held off registers after it. -/
@[req "SPN-31"]
theorem panic_exit_releases :
    (run (conf Lifetime.current) st0 [.claim 1, .exit 1 .panic]).inFlight = [] ∧
    (run (conf Lifetime.current) st0 [.claim 1, .refresh env0 rf true]).refreshes = [] ∧
    (run (conf Lifetime.current) st0 [.claim 1, .exit 1 .panic, .refresh env0 rf true]).refreshes =
      [rf] := by
  decide +kernel

/-- The failing history for "released on every exit": a marker no exit releases holds every later
refresh off, whatever runs after it (`Lifetime.no_refresh_after_claim`), here a refresh long after a
prune pass with nothing pending. -/
@[req "SPN-31"]
theorem stuck_marker_subordinates (ops : List Op) (h : ∀ o ∈ ops, o.ends 1 = false) :
    (run (conf Lifetime.current) st0 (.claim 1 :: ops)).refreshes = [] ∧
    pending Kernel.current (envAt 100000 100000)
      (run (conf Lifetime.current) st0 [.claim 1, .kernel (envAt 100000 100000) .prune]).sys.world.node =
      [] ∧
    (run (conf Lifetime.current) st0 [.claim 1, .kernel (envAt 100000 100000) .prune,
      .refresh (envAt 100000 100000) rf true]).refreshes = [] :=
  ⟨no_refresh_after_claim _ rfl 1 st0 ops h, by decide +kernel, by decide +kernel⟩

/-- The abstract atomicity is needed: a marker released before the registration hold writes the
pending log — a deliberately reordered history, since a handler that exits does not register —
lets the refresh in, and it spends the Escape's input. -/
@[req "SPN-31"]
theorem release_before_hold_admits_refresh :
    let s := run (conf Lifetime.current) st0
      [.claim 1, .exit 1 .refused, .refresh env0 rf true, .hold 1 env0 10 false (Wall.sample 200) req0]
    s.refreshes = [rf] ∧
      s.sys.world.node.cands.any (fun c => c.id == es0.id && conflicts rf c) = true := by
  decide +kernel

def held (g : Subordination) : St :=
  run (conf g) st0 [.claim 1, .hold 1 env0 10 false (Wall.sample 200) req0]

/-- The handoff: the hold that releases the marker leaves the pending log listing the spend, so
under either reading a refresh is subordinated through the spend's expiry, 200, and registers one
second after it. -/
@[req "SPN-30"]
theorem marker_hands_off :
    (held Lifetime.current).inFlight = [] ∧
    ([Subordination.pendingAndMarker, .pendingOnly].all fun g =>
      (refreshHold (conf g) (held g) (envAt 200 100) rf true).refreshes == [] &&
      (refreshHold (conf g) (held g) (envAt 201 140) rf true).refreshes == [rf]) = true ∧
    subordinated .pendingOnly Kernel.current (envAt 200 100) (held .pendingOnly) = true :=
  ⟨by decide +kernel, by decide +kernel,
    (hold_logs_spend (conf .pendingOnly) rfl (step (conf .pendingOnly) st0 (.claim 1)) 1 env0 10
      false (Wall.sample 200) req0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (envAt 200 100) (by decide +kernel)).2 .pendingOnly⟩

/-! #### A refused registration -/

def txidB : Encode.Bytes := List.replicate 31 0 ++ [2]

/-- An earlier request on another coin: 40 to the allowlist, expiry 100. -/
def spendY : BtcPolicy.Evaluate.Psbt :=
  { spendPsbt with txInputs := [⟨txidB, 0, 0⟩], txOutputs := [⟨[12, 0], 55⟩, ⟨[11, 1], 40⟩] }

def escY : BtcPolicy.Evaluate.Psbt :=
  { escPsbt with txInputs := [⟨txidB, 0, Ingress.escapeSequence⟩] }

def reqY : Ingress.Request :=
  { req0 with spend := { req0.spend with psbt := spendY }, escape := { req0.escape with psbt := escY },
              expiry := 100, fireAt := some (Wall.sample 50) }

/-- A retry of `req0`'s spend commitment with a different Escape. -/
def retry : Ingress.Request := { req0 with escape := rung 97 Ingress.escapeSequence }

/-- A new spend commitment offered with `req0`'s resident Escape. -/
def reqW : Ingress.Request :=
  { req0 with spend := { req0.spend with psbt :=
      { spendPsbt with txOutputs := [⟨[12, 0], 50⟩, ⟨[11, 1], 45⟩] } } }

/-- Cap 100 and a window of 50, so a check at HotClock 150 and wall 150 releases `reqY`'s row and
keeps `req0`'s. -/
def narrow (lg : Ledger.Guards) : Lifetime.Cfg :=
  { g := Lifetime.current, lg := lg, cfg := { cap := 100, window := 50 }, r := Kernel.current,
    ctx := ctx0 }

def envR : Env := envAt 150 150

def accepted2 (lg : Ledger.Guards) : St :=
  run (narrow lg) st0
    [.hold 1 env0 10 false (Wall.sample 100) reqY, .hold 2 (envAt 60 20) 11 false (Wall.sample 200) req0]

/-- `SPN-29`, `POL-18`, `POL-19` on the checked path. Two acceptances charge 40 and 55. The retry of
`req0`'s commitment passes its checks and gate 24, whose release drops `reqY`'s row; registration
refuses it, staging an unaccepted Carrier, and every row stays as it was: the earlier acceptance of
the same commitment keeps its row and the released row stays charged. A new commitment offered with
the resident Escape is refused at registration too and leaves no row of its own. -/
@[req "SPN-29"]
theorem registration_refusals_keep_charges :
    let c := narrow Ledger.current
    let s := accepted2 Ledger.current
    (s.sys.led.map fun r => (r.amount, r.reservedAt, r.expiry)) =
      [(40, Mono.sample 5, Wall.sample 100), (55, Mono.sample 20, Wall.sample 200)] ∧
    (spendOf ctx0 retry).id = sp0.id ∧
    verdict c envR s.sys.led 12 false (Wall.sample 200) retry =
      .accepted (spendOf ctx0 retry) (escapeOf ctx0 retry) ∧
    (Ledger.ageOut envR 50 s.sys.led).map (·.amount) = [55] ∧
    rows (step c s (.hold 3 envR 12 false (Wall.sample 200) retry)).sys.led = rows s.sys.led ∧
    (step c s (.hold 3 envR 12 false (Wall.sample 200) retry)).sys.world.node.carriers.any
      (fun k => k.cid == 12 && !k.accepted) = true ∧
    verdict c envR s.sys.led 13 false (Wall.sample 200) reqW =
      .accepted (spendOf ctx0 reqW) (escapeOf ctx0 reqW) ∧
    Ledger.holds (step c s (.hold 4 envR 13 false (Wall.sample 200) reqW)).sys.led
      (spendOf ctx0 reqW).id = false ∧
    rows (step c s (.hold 4 envR 13 false (Wall.sample 200) reqW)).sys.led = rows s.sys.led := by
  decide +kernel

/-- `POL-19`'s withdrawn release point, `Ledger.Release.everyStep`: the same refused retry keeps
its check's release, and `reqY`'s charge is gone. -/
@[req "POL-19"]
theorem release_kept_at_refused_registration :
    let lg := { Ledger.current with release := .everyStep }
    ((step (narrow lg) (accepted2 lg) (.hold 3 envR 12 false (Wall.sample 200) retry)).sys.led.map
      (·.amount)) = [55] := by
  decide +kernel

/-- A deliberately broken unwind, not a withdrawn rule: on a refused registration it removes the
row of the request's commitment whoever placed it. -/
def unwindByCommitment (sp : Cand) (l : Ledger.Ledger) : Ledger.Ledger := l.filter (·.cid != sp.id)

/-- `SPN-29`'s "only a reservation placed by this request": unwound by commitment, the refused
retry takes the earlier acceptance's charge with it, and `req0`'s hot spend stays resident with no
row. -/
@[req "SPN-29"]
theorem unwind_by_commitment_drops_earlier_charge :
    let after := step (narrow Ledger.current) (accepted2 Ledger.current)
      (.hold 3 envR 12 false (Wall.sample 200) retry)
    let broken := unwindByCommitment (spendOf ctx0 retry) after.sys.led
    Ledger.liveSum after.sys.led = 95 ∧ Ledger.holds after.sys.led sp0.id = true ∧
    Ledger.liveSum broken = 40 ∧ Ledger.holds broken sp0.id = false ∧
    after.sys.world.node.cands.any (fun c => c.id == sp0.id && c.hot && !c.settled) = true := by
  decide +kernel

end BtcPolicy.Exhibits.Lifetime

namespace BtcPolicy.Exhibits.Sweep
open BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Sweep BtcPolicy.Sweep.Cases
open BtcPolicy.Federation.Cases (honest)

/-! ### The composed sweep

Research task `bps-uaer.9`. Every run below is an actual `Sweep.Execution` over `Kernel.current`
with the three guard values as they stand: its guards are decided, each node moves by
`Kernel.step`, and each node's reads come from an instant of one backend world. `Sweep.Cases` holds
the schedules; the book and the creator map are model parameters, hand-chosen. -/

def cfgNow : Cfg := Cases.cfg Coverage.current Coverage.currentExternal Package.current

/-- The prefix a schedule leaves, as a trace and a state. -/
def runOf (b : Backend) (ss : List Step) : BtcPolicy.Sweep.Trace × State :=
  record Kernel.current [] (start b) ss

/-- One reachable successful sweep. Nodes 1 and 2 arm under duress and release the Escape; node
2's partial on each input reaches node 1; node 1 reads the vault, passes coverage, ancestry and
possession on every input at that read, assembles, and its send, re-authorized at its own state,
submits the Escape's transaction. -/
@[req "DUR-29"]
theorem successful_sweep :
    let p := runOf vault sweep
    Execution cfgNow Kernel.current honest (record Kernel.current p.1 p.2 [sendAt 1 RegistrationCases.e1.id]).1
        (record Kernel.current p.1 p.2 [sendAt 1 RegistrationCases.e1.id]).2 ∧
      admits cfgNow honest p.2 p.1 (sendAt 1 RegistrationCases.e1.id) = true ∧
      submits Kernel.current p.2 (sendAt 1 RegistrationCases.e1.id) = [txE.id] := by
  refine ⟨?_, by decide, by decide⟩
  have h := execution_of_legal (cfg := cfgNow) (r := Kernel.current) (honest := honest)
    (.init (start vault) ⟨Federation.Cases.fed0_fresh, rfl, fun _ => rfl⟩)
    (ss := sweep ++ [sendAt 1 RegistrationCases.e1.id]) (by decide)
  simpa [runOf, record] using h

/-- **Armed, and no eligible Escape.** The vault holds a third confirmed output no Escape spends, so
the Escape covers too little of the protected value. Both nodes are armed, the hot spend is frozen
at both and node 1 has released the Escape; ancestry and possession pass at node 1's read, coverage
does not, and its assembly is not admitted. The federation underneath is the one the successful
sweep runs on: arming and freezing read no backend. -/
@[req "DUR-19"]
theorem armed_without_eligible_escape :
    let p := runOf vaultLarge (delivered ++ [.observe 1 vaultLarge])
    let n := (p.2.fed.worlds 1).node
    legal cfgNow Kernel.current honest [] (start vaultLarge) (delivered ++ [.observe 1 vaultLarge]) = true ∧
      n.armed = true ∧ ((p.2.fed.worlds 2).node).armed = true ∧
      n.cands.any (fun c => c.id == c1.id && c.frozen) = true ∧
      n.cands.any (fun c => c.id == RegistrationCases.e1.id && c.released) = true ∧
      covered cfgNow (authorizedAt p.2 p.1 1) n vaultLarge RegistrationCases.e1 = false ∧
      ancestryOk cfgNow (authorizedAt p.2 p.1 1) vaultLarge RegistrationCases.e1 = true ∧
      possessed cfgNow n.t (Federation.held 1 (fedTrace p.1) p.2.fed) RegistrationCases.e1 = true ∧
      admits cfgNow honest p.2 p.1 (assemble 1 RegistrationCases.e1.id) = false ∧
      p.2.fed.worlds 1 = (runOf vault (delivered ++ [.observe 1 vault])).2.fed.worlds 1 := by
  decide

/-- **A valid Escape, insufficient possession.** Only node 2's partial on input 0 reaches node 1.
The kernel's package test, which reads input 0 for every input, passes, and the federation admits
the step; coverage and ancestry pass at node 1's read; possession on input 1 does not, and the
assembly is not admitted. -/
@[req "DUR-28"]
theorem insufficient_possession :
    let p := runOf vault inputZeroOnly
    let n := (p.2.fed.worlds 1).node
    legal cfgNow Kernel.current honest [] (start vault) inputZeroOnly = true ∧
      Federation.admits honest p.2.fed (.process 1 envFire (.packageAccepted RegistrationCases.e1.id)) = true ∧
      (Kernel.packageAccepted Kernel.current envFire (p.2.fed.worlds 1) RegistrationCases.e1.id).cands.any
        (fun c => c.id == RegistrationCases.e1.id && c.packageOk) = true ∧
      covered cfgNow (authorizedAt p.2 p.1 1) n vault RegistrationCases.e1 = true ∧
      ancestryOk cfgNow (authorizedAt p.2 p.1 1) vault RegistrationCases.e1 = true ∧
      possessed cfgNow n.t (Federation.held 1 (fedTrace p.1) p.2.fed) RegistrationCases.e1 = false ∧
      admits cfgNow honest p.2 p.1 (assemble 1 RegistrationCases.e1.id) = false := by
  decide

/-- **One inadmissible rung beside an admissible one.** `Kernel.packageAccepted` assembles one rung
per candidate, so the two rungs here are two selected Escapes over the same ordered outpoints,
measured on one pass against one denominator: `e2` delivers 40 of 100 and `e1` 90. Both are
possessed and both pass ancestry; `e2` fails coverage and its assembly is not admitted, `e1`'s is,
and `e1` is submitted. -/
@[req "DUR-24"]
theorem inadmissible_beside_admissible :
    let p := runOf vault twoEscapes
    let n := (p.2.fed.worlds 1).node
    let A := authorizedAt p.2 p.1 1
    let R := Federation.held 1 (fedTrace p.1) p.2.fed
    legal cfgNow Kernel.current honest [] (start vault) twoEscapes = true ∧
      (selectedEscapes n).map (·.id) = [RegistrationCases.e2.id, RegistrationCases.e1.id] ∧
      covered cfgNow A n vault RegistrationCases.e2 = false ∧ ancestryOk cfgNow A vault RegistrationCases.e2 = true ∧
      possessed cfgNow n.t R RegistrationCases.e2 = true ∧ admits cfgNow honest p.2 p.1 (assemble 1 RegistrationCases.e2.id) = false ∧
      covered cfgNow A n vault RegistrationCases.e1 = true ∧
      legal cfgNow Kernel.current honest p.1 p.2 [assemble 1 RegistrationCases.e1.id, sendAt 1 RegistrationCases.e1.id] = true ∧
      submits Kernel.current (record Kernel.current p.1 p.2 [assemble 1 RegistrationCases.e1.id]).2 (sendAt 1 RegistrationCases.e1.id) =
        [txE.id] := by
  decide

/-- **Ancestry moves before assembly.** After node 1's read an external transaction becomes resident
over the Escape's second input, and node 1 reads again before assembling. At that read coverage and
possession pass, `WTC-24` refuses the input as unknown or spent, and the assembly is not admitted. -/
@[req "WTC-24"]
theorem ancestry_moves_before_assembly :
    let p := runOf vault movedBeforeAssembly
    let n := (p.2.fed.worlds 1).node
    let A := authorizedAt p.2 p.1 1
    legal cfgNow Kernel.current honest [] (start vault) movedBeforeAssembly = true ∧
      covered cfgNow A n vaultConflict RegistrationCases.e1 = true ∧
      possessed cfgNow n.t (Federation.held 1 (fedTrace p.1) p.2.fed) RegistrationCases.e1 = true ∧
      Package.validate Package.current creator (snapshot A vaultConflict) vaultConflict.mempool A
        (candidateOf RegistrationCases.e1.tx) none = .refused (.unknownOrSpent 1) ∧
      admits cfgNow honest p.2 p.1 (assemble 1 RegistrationCases.e1.id) = false := by
  decide

/-- **Ancestry moves before send.** The same move after node 1's assembly: node 1 reads the new
instant, at which `WTC-24` would refuse, and its send still submits, because the send re-reads the
local authorization (`DUR-29`) and no backend fact. What the backend makes of the submission is not
modelled here. -/
@[req "DUR-29"]
theorem ancestry_moves_before_send :
    let p := runOf vault movedBeforeSend
    let A := authorizedAt p.2 p.1 1
    legal cfgNow Kernel.current honest [] (start vault) (movedBeforeSend ++ [sendAt 1 RegistrationCases.e1.id]) = true ∧
      p.2.obs 1 = some vaultConflict ∧ ancestryOk cfgNow A vaultConflict RegistrationCases.e1 = false ∧
      submits Kernel.current p.2 (sendAt 1 RegistrationCases.e1.id) = [txE.id] := by
  decide

/-- **Two nodes with different selected sets.** Nodes 1 and 2 select only `f1`, nodes 3 and 4 only
`f2`; the two are input-disjoint. Node 1 reads an instant at which `f2`'s second input is an
unconfirmed external deposit; node 3 reads a later one at which it has confirmed and `f1` is
resident. Each Escape passes its node's check and both are submitted, `F59`'s cross-node residual on
one composed run. The floor `Sweep.single_sweep_needs_common_floor` needs fails at node 1: the
Escapes selected on its pass have 60 in inputs, below the two deliveries. -/
@[req "DUR-22"]
theorem different_selected_sets :
    let p := runOf before split
    let p₁ := runOf before (split.take 20)
    let p₃ := runOf before (split.take 24)
    legal cfgNow Kernel.current honest4 [] (start before) (split ++ [sendAt 3 f2.id]) = true ∧
      check cfgNow p₁.2 p₁.1 1 f1 = true ∧ check cfgNow p₃.2 p₃.1 3 f2 = true ∧
      submits Kernel.current (runOf before (split.take 21)).2 (sendAt 1 f1.id) = [txF1.id] ∧
      submits Kernel.current p.2 (sendAt 3 f2.id) = [txF2.id] ∧
      Coverage.selectedInputs (readsAt cfgNow p₁.2 p₁.1 1 before) = 60 ∧
      book.delivered txF1.id + book.delivered txF2.id = 200 := by
  decide

/-- **No stale authorization is permission to send.** After the successful assembly the send runs
once the Escape's window has closed: the package test is standing, the send's own re-authorization
refuses, and nothing is submitted. -/
@[req "DUR-29"]
theorem stale_assembly_not_sent :
    let p := runOf vault sweep
    (p.2.fed.worlds 1).node.cands.any (fun c => c.id == RegistrationCases.e1.id && c.packageOk) = true ∧
      admits cfgNow honest p.2 p.1 (sendAt 1 RegistrationCases.e1.id envLate) = true ∧
      submits Kernel.current p.2 (sendAt 1 RegistrationCases.e1.id envLate) = [] := by
  decide

/-- Under the withdrawn value — the check before assembly instead of before the send — the same send
submits the Escape after its window closed. -/
@[req "DUR-29"]
theorem stale_assembly_sent_with_withdrawn :
    let r : Rules := { Kernel.current with reauth := .beforeAssembly }
    submits r (record r [] (start vault) sweep).2 (sendAt 1 RegistrationCases.e1.id envLate) = [txE.id] := by
  decide

end BtcPolicy.Exhibits.Sweep

namespace BtcPolicy.Exhibits.Settlement
open BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Settlement BtcPolicy.Settlement.Cases
open BtcPolicy.Federation.Cases (honest)
open BtcPolicy.Sweep (Backend State record ancestryOk covered authorizedAt check)
open BtcPolicy.Sweep.Cases (vault start delivered sweep assemble sendAt)

/-! ### Chain observation in the sweep

Research task `bps-uaer.10`. Every run below is a `Settlement.Execution`: a `Sweep.Execution` whose
kernel steps read their chain view off the acting node's latest observation, over the three guard
values as they stand. The instants are hand-chosen in `Settlement.Cases`; the runs are not. The
withdrawn runs take an explicit rule record, so a flip of `Kernel.current` cannot reach them. -/

def cfgNow : Sweep.Cfg := Sweep.Cases.cfg Coverage.current Coverage.currentExternal Package.current

/-- The prefix a schedule leaves under these rules, from the vault with nothing observed. -/
def runOf (r : Rules) (ss : List Sweep.Step) : Sweep.Trace × State := record r [] (start vault) ss

/-- The reservation `Ledger.reserve` writes for the hot spend at its acceptance, at the sample node 1
accepted at. The ledger is not part of the composed state, so this row is seeded. -/
def row : Ledger.Ledger := Ledger.reserve [] c1 env0.mono
def lcfg : Ledger.Config := { cap := 1000, window := 120 }

/-- The successful sweep of `Exhibits.Sweep.successful_sweep` reads no chain view, so it is a run of
the tied execution too. -/
@[req "DUR-29"]
theorem successful_sweep_observed :
    legal cfgNow Kernel.current honest [] (start vault) (sweep ++ [sendAt 1 RegistrationCases.e1.id]) =
      true := by
  decide

/-- **A mempool sighting, later evicted.** The claw-back over the hot spend's input becomes resident
and node 1 reads it there, unconfirmed. Its settlement marks the hot spend terminal and takes it off
`/pending`; a fire pass at that view releases nothing. Then the claw-back is evicted and node 1 reads
the vault without it: a fire pass past the spend's fire time still releases nothing, and no partial
has left any node. The ledger's composed step at that settlement, on node 1's world, keeps the
reservation. -/
@[req "SPN-33"]
theorem mempool_sighting_evicted :
    let q := runOf Kernel.current (mempoolThenEvicted.take 6)
    let q' := runOf Kernel.current (mempoolThenEvicted.take 7)
    let p := runOf Kernel.current (mempoolThenEvicted ++ [fireAt 1 envFire])
    legal cfgNow Kernel.current honest [] (start vault) (mempoolThenEvicted ++ [fireAt 1 envFire]) = true ∧
      q.2.obs 1 = some clawResident ∧ resident clawResident claw = true ∧
      confirmedAt clawResident claw = false ∧
      pending Kernel.current envClaw (q.2.fed.worlds 1).node ≠ [] ∧
      (q'.2.fed.worlds 1).node.cands.any (fun c => c.id == c1.id && c.terminal) = true ∧
      pending Kernel.current envClaw (q'.2.fed.worlds 1).node = [] ∧
      shows evicted claw = false ∧ p.2.obs 1 = some evicted ∧
      (p.2.fed.worlds 1).node.cands.any (fun c => c.id == c1.id && c.terminal) = true ∧
      p.2.fed.parts = [] ∧
      (Ledger.sysStep Ledger.current lcfg Kernel.current envClaw ⟨q.2.fed.worlds 1, row⟩
        (.settle claw)).1 = ⟨q'.2.fed.worlds 1, row⟩ := by
  decide

/-- Under `F57` row 8's withdrawn reading, defeat read off the claw-back's residency, the same
schedule runs: the fire pass at the resident view releases nothing, and after the eviction the
defeated spend's partial leaves node 1. -/
@[req "SPN-33"]
theorem mempool_sighting_evicted_with_withdrawn :
    let r := Exhibits.ReleaseKernel.withdrawnDefeat
    legal cfgNow r honest [] (start vault) (mempoolThenEvicted ++ [fireAt 1 envFire]) = true ∧
      (runOf r mempoolThenEvicted).2.fed.parts = [] ∧
      (runOf r (mempoolThenEvicted ++ [fireAt 1 envFire])).2.fed.parts ≠ [] := by
  decide

/-- Under `DEF-5`'s withdrawn value, the ledger's composed step at the same mempool-only settlement
refunds the reservation, while the hot spend is still resident at node 1. -/
@[req "SPN-33"]
theorem mempool_settlement_refunds_with_withdrawn :
    let q := runOf Kernel.current (mempoolThenEvicted.take 6)
    let s := (Ledger.sysStep Exhibits.HotLedger.withdrawnSettlement lcfg Kernel.current envClaw
      ⟨q.2.fed.worlds 1, row⟩ (.settle claw)).1
    row ≠ [] ∧ s.led = [] ∧ s.world.node.cands.any (·.id == c1.id) = true := by
  decide

/-- **A reorganization after apparent settlement.** The claw-back confirms and node 1 reads it
confirmed and settles it: the hot spend is terminal. A reorganization replaces the block with one
that holds nothing, node 1 reads the new tip, and a fire pass past the spend's fire time releases
nothing: the hot spend is still terminal and no partial has left any node. -/
@[req "SPN-33"]
theorem reorg_after_settlement :
    let q := runOf Kernel.current (minedThenReorged.take 6)
    let p := runOf Kernel.current (minedThenReorged ++ [fireAt 1 envFire])
    legal cfgNow Kernel.current honest [] (start vault) (minedThenReorged ++ [fireAt 1 envFire]) = true ∧
      q.2.obs 1 = some clawMined ∧ confirmedAt clawMined claw = true ∧
      resident clawMined claw = false ∧
      p.2.truth = reorged ∧ shows reorged claw = false ∧ reorged.tip.height = clawMined.tip.height ∧
      reorged.tip ≠ clawMined.tip ∧
      (p.2.fed.worlds 1).node.cands.any (fun c => c.id == c1.id && c.terminal) = true ∧
      p.2.fed.parts = [] := by
  decide

/-- Under the withdrawn reading the reorganization un-defeats the spend, and its partial leaves
node 1. -/
@[req "SPN-33"]
theorem reorg_after_settlement_with_withdrawn :
    let r := Exhibits.ReleaseKernel.withdrawnDefeat
    legal cfgNow r honest [] (start vault) (minedThenReorged ++ [fireAt 1 envFire]) = true ∧
      (runOf r (minedThenReorged ++ [fireAt 1 envFire])).2.fed.parts ≠ [] := by
  decide

/-- **Exposure outlives a reorganization.** Node 1 releases its hot spend, the spend confirms and
node 1 settles it; a reorganization drops the block and node 1 reads the new tip. The released
partial is still in the federation's inventory and in node 1's exposure rows, the spend stays settled,
and a later fire pass releases nothing more. `Settlement.exposure_persists` is the general result. -/
@[req "POL-18"]
theorem reorg_keeps_exposure :
    let q := runOf Kernel.current (releasedThenReorged.take 5)
    let p := runOf Kernel.current (releasedThenReorged ++ [fireAt 1 envAfter])
    legal cfgNow Kernel.current honest [] (start vault) (releasedThenReorged ++ [fireAt 1 envAfter]) = true ∧
      q.2.fed.parts ≠ [] ∧ p.2.fed.parts = q.2.fed.parts ∧
      (p.2.fed.worlds 1).exposure = (q.2.fed.worlds 1).exposure ∧
      p.2.truth = reorged ∧ shows reorged tx1 = false ∧
      (p.2.fed.worlds 1).node.cands.any (fun c => c.id == c1.id && c.settled) = true := by
  decide

/-- **A conflicting confirmed spend.** After the duress release and delivery, an external
transaction spending the Escape's first input confirms and node 1 reads it; the instant's confirmed
outputs, hand-chosen, no longer hold that input. At that read `WTC-24`
refuses the Escape and its assembly is not admitted; node 1's settlement of the spend marks its
frozen hot spend terminal. Node 2 has observed nothing: its hot spend stays as it was, and it may not
take the same settlement. -/
@[req "SPN-33"]
theorem conflicting_confirmed_spend :
    let p := runOf Kernel.current externalConfirmed
    let p' := runOf Kernel.current (externalConfirmed ++ [settleAt 1 envExternal spendExternal])
    legal cfgNow Kernel.current honest [] (start vault)
        (externalConfirmed ++ [settleAt 1 envExternal spendExternal]) = true ∧
      confirmedAt externalMined spendExternal = true ∧
      ancestryOk cfgNow (authorizedAt p.2 p.1 1) externalMined RegistrationCases.e1 = false ∧
      admits cfgNow honest p.2 p.1 (assemble 1 RegistrationCases.e1.id) = false ∧
      admits cfgNow honest p.2 p.1 (settleAt 2 envExternal spendExternal) = false ∧
      (p'.2.fed.worlds 1).node.cands.any (fun c => c.id == c1.id && c.terminal) = true ∧
      (p'.2.fed.worlds 2).node.cands.any (fun c => c.id == c1.id && c.terminal) = false := by
  decide

/-- **A late confirmed deposit.** After the duress release and delivery, node 1 reads an instant at
which an external deposit is resident: it is an unconfirmed external output, and the Escape passes
the check. The deposit confirms and node 1 reads again: the deposit is in the snapshot, coverage
fails and the assembly is not admitted. Assembled at the earlier read instead, the Escape is still
sent after the confirmation, leaving the deposit outside the sweep. -/
@[req "DUR-22"]
theorem late_confirmed_deposit :
    let p₁ := runOf Kernel.current depositSeen
    let p₂ := runOf Kernel.current depositConfirmed
    let late := [assemble 1 RegistrationCases.e1.id, .chain depositMined, .observe 1 depositMined]
    legal cfgNow Kernel.current honest [] (start vault) depositConfirmed = true ∧
      Sweep.unconfirmedExternal (authorizedAt p₁.2 p₁.1 1) depositResident = [3] ∧
      check cfgNow p₁.2 p₁.1 1 RegistrationCases.e1 = true ∧
      (Sweep.snapshot (authorizedAt p₂.2 p₂.1 1) depositMined).read.any (·.1 == 3) = true ∧
      covered cfgNow (authorizedAt p₂.2 p₂.1 1) (p₂.2.fed.worlds 1).node depositMined
        RegistrationCases.e1 = false ∧
      admits cfgNow honest p₂.2 p₂.1 (assemble 1 RegistrationCases.e1.id) = false ∧
      legal cfgNow Kernel.current honest p₁.1 p₁.2 (late ++ [sendAt 1 RegistrationCases.e1.id]) = true ∧
      Sweep.submits Kernel.current (record Kernel.current p₁.1 p₁.2 late).2
        (sendAt 1 RegistrationCases.e1.id) = [txE.id] := by
  decide

end BtcPolicy.Exhibits.Settlement

namespace BtcPolicy.Exhibits.FedSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.Exhibits.TwoRun (sLapsing eLapsing sp3 es3 cfg tblD tblN withdrawnReadTime
  withdrawnCloseTime withdrawnDriverTime s60 hot1 esc1)
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt withdrawnTraversal)

/-! ## SILENCE over a composed federation, one fixed schedule

Two honest nodes, 1 and 2, each `Kernel.RegistrationCases.A` at its own id (threshold 2,
`duress_delay_secs` 200, `epsilon_secs` 5, `combine_slack_secs` 40, `hold_secs` 0) with an empty
Hot ledger, under the two enrolment tables of `Exhibits.TwoRun` at both nodes. Every run below is a
legal ledgered run, and forgetting its ledgers leaves a `Federation.Execution`
(`FedSilence.lrun_execution`). These are not hand-seeded. -/

def honest : List Nat := [1, 2]
/-- The manifest's node list: node 3 is a peer with no world here, whose messages are addressed and
never delivered. -/
def peers : List Nat := [1, 2, 3]
def F0 : LFed := { fed := Federation.Cases.fed0, leds := fun _ => [] }

theorem F0_fresh : Federation.Fresh honest F0.fed := by
  unfold Federation.Fresh
  decide

theorem F0_sweep : ∀ i ∈ honest, (F0.fed.worlds i).node.sweepActive = false := by decide

/-- PIN 1 is the duress PIN at both nodes in the first family and an ordinary PIN in the second. -/
def tblsD : Nat → Enrolment := fun _ => tblD
def tblsN : Nat → Enrolment := fun _ => tblN

/-- A hot spend whose `fire_at` of 200 is below the `T` of 272 the duress arm writes. -/
def sH : Cand := cand 21 { id := 116, inputs := [18], outflow := 10 } true (some 200) 900
def eH : Cand := cand 22 { id := 117, inputs := [18, 19], outflow := 0 } false none 900
/-- Node 2's partial over `sLapsing`, as its fire pass queues it. -/
def part2 : Exp := { msg := sighash hot1 0, input := 0, signer := 2, hot := true, cid := 1 }

/-- `Exhibits.TwoRun.sendTrace` and `Exhibits.TwoRun.hotTrace`'s second acceptance, run by two
nodes that relay to each other. A hot pair under PIN 0, ordinary in both families, is accepted at
both nodes at 40; each relays and each relay reaches the other node at 70, which opens the pair. A
pair that is not hot is requested at both nodes under PIN 1 at 72 and relayed. Both nodes' fire
passes at 85 queue a hot partial; node 2's reaches node 1 at 86, which then holds two partials and
assembles at 87. The PIN-1 relays reach the other node at 130, after the hot candidate's expiry,
so each holder decision writes `T = max(72 + 200, 130) = 272` and arms both nodes in the first
family and neither in the second. Node 1's send runs on a wall stepped back to 90, and node 1
accepts another hot spend at 140. The last step is node 1's fire pass at 200, past the `T` of 195
that acceptance left in the first family. -/
def lastStep : PStep := .input 1 (envAt 200 200) (.pinless .firePass)

def sched : List PStep :=
  [.input 1 (envAt 40 40) (.request 10 0 (Wall.sample 120) sLapsing eLapsing),
   .input 2 (envAt 40 40) (.request 10 0 (Wall.sample 120) sLapsing eLapsing),
   .net (.emit 1 10), .net (.emit 2 10),
   .net (.deliver 1 (envAt 70 70) ⟨2, 10⟩), .net (.deliver 2 (envAt 70 70) ⟨1, 10⟩),
   .input 1 (envAt 72 72) (.request 20 1 (Wall.sample 900) sp3 es3),
   .input 2 (envAt 72 72) (.request 20 1 (Wall.sample 900) sp3 es3),
   .net (.emit 1 20), .net (.emit 2 20),
   .input 1 (envAt 85 85) (.pinless .firePass),
   .input 2 (envAt 85 85) (.pinless .firePass),
   .net (.deliverPartial 1 (envAt 86 86) part2),
   .input 1 (envAt 87 87) (.pinless (.packageAccepted 1)),
   .net (.deliver 1 (envAt 130 130) ⟨2, 20⟩), .net (.deliver 2 (envAt 130 130) ⟨1, 20⟩),
   .input 1 (envAt 90 131) (.pinless (.send 1)),
   .input 1 (envAt 140 140) (.request 30 0 (Wall.sample 900) sH eH),
   lastStep]

/-- `Exhibits.TwoRun.backTrace` run by two nodes: both accept a hot pair under PIN 1 at 40, relay,
and decide at 100, which writes `T = 100` at both; node 1's fire pass then runs on a wall stepped
back to 95. -/
def clampSched : List PStep :=
  [.input 1 (envAt 40 40) (.request 10 1 (Wall.sample 400) s60 (cand 2 esc1 false none 400)),
   .input 2 (envAt 40 40) (.request 10 1 (Wall.sample 400) s60 (cand 2 esc1 false none 400)),
   .net (.emit 1 10), .net (.emit 2 10),
   .net (.deliver 1 (envAt 100 100) ⟨2, 10⟩), .net (.deliver 2 (envAt 100 100) ⟨1, 10⟩),
   .input 1 (envAt 95 101) (.pinless .firePass)]

def pairs (mk : Marker) (r : Rules) (sc : List PStep) : List (FObs × FObs) :=
  walk mk Ledger.current cfg r honest peers tblsD tblsN F0 F0 sc

/-- The ledgered run of the schedule's first `k` steps under one family. -/
def runOf (r : Rules) (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  lrun Ledger.current cfg r F0 ((sched.take k).map (·.step tbls))

/-! ### The relation over the values as they stand -/

/-- `FedSilence.fed_silence` at the guard parameters as they stand, every rule and marker premise
discharged. -/
@[req "DUR-1"]
theorem fed_silence_with_current {gs : Guards} {c : Config} (hon ps : List Nat)
    (tbls₀ tbls₁ : Nat → Enrolment) (sc : List PStep) (A B : LFed)
    (hc : FCoupled Kernel.current hon A B) (hia : FInv Kernel.current hon A)
    (hib : FInv Kernel.current hon B) :
    ∀ y ∈ walk Silence.current gs c Kernel.current hon ps tbls₀ tbls₁ A B sc, y.1 = y.2 :=
  BtcPolicy.FedSilence.fed_silence rfl rfl rfl rfl rfl rfl hon ps tbls₀ tbls₁ sc A B hc hia hib

/-- Both runs of the schedule are federation executions: each is legal, and forgetting its Hot
ledgers leaves a `Federation.Execution` from the fresh state. -/
@[req "DUR-5"]
theorem fed_runs_are_executions :
    Federation.Execution Kernel.current honest
        (ltrace Ledger.current cfg Kernel.current [] F0 (sched.map (·.step tblsD)))
        (lrun Ledger.current cfg Kernel.current F0 (sched.map (·.step tblsD))).fed ∧
      Federation.Execution Kernel.current honest
        (ltrace Ledger.current cfg Kernel.current [] F0 (sched.map (·.step tblsN)))
        (lrun Ledger.current cfg Kernel.current F0 (sched.map (·.step tblsN))).fed :=
  ⟨lrun_execution (.init _ F0_fresh) _ (by decide +kernel),
    lrun_execution (.init _ F0_fresh) _ (by decide +kernel)⟩

/-- **The relation on a run with inter-node traffic.** `FedSilence.fed_silence_fresh` at the values
as they stand gives equality at every step of the walk. The walk covers 18 of the 19 steps: two
nodes' acceptances, four relays emitted and delivered, two fire passes whose partials enter the
inventory, one partial delivered, an assembly, two holder decisions that arm both nodes in the
first family and neither in the second, a send on a stepped-back wall and a hot acceptance after the
arm. The acting node of each step and its confirmation marker are listed, and the inventories the
walk ends with hold both partials and all four relays. -/
@[req "DUR-1"]
theorem fed_run_silent :
    (∀ y ∈ pairs Silence.current Kernel.current sched, y.1 = y.2) ∧
    sched.length = 19 ∧ (pairs Silence.current Kernel.current sched).length = 18 ∧
    ((pairs Silence.current Kernel.current sched).map fun y => y.1.node.map (·.1)) =
      [some 1, some 2, none, none, some 1, some 2, some 1, some 2, none, none, some 1, some 2,
       some 1, some 1, some 1, some 2, some 1, some 1] ∧
    ((pairs Silence.current Kernel.current sched).map fun y => y.1.node.map (·.2.marker)) =
      [some false, some false, none, none, some true, some true, some false, some false, none,
       none, some false, some false, some false, some false, some true, some true, some false,
       some false] ∧
    ((pairs Silence.current Kernel.current sched).getLast?.map fun y =>
      (y.1.parts.map Exp.signer, y.1.net.length)) = some ([1, 2], 4) ∧
    ((runOf Kernel.current tblsD 16).fed.worlds 1).node.armed = true ∧
    ((runOf Kernel.current tblsD 16).fed.worlds 2).node.armed = true ∧
    ((runOf Kernel.current tblsN 16).fed.worlds 1).node.armed = false ∧
    ((runOf Kernel.current tblsN 16).fed.worlds 2).node.armed = false :=
  ⟨fed_silence_fresh rfl rfl rfl rfl rfl rfl honest peers tblsD tblsN F0 F0_fresh F0_sweep sched,
    by decide +kernel⟩

/-- The walk stops where the runs part. At node 1's fire pass at 200, the first family's node 1 is
armed with `T = 195` reached, and the second's is not armed. Computed beside the walk, the step
queues the selected Escape's partial in the first family, one row per input entering the partial
inventory, and nothing in the second. -/
@[req "DUR-7"]
theorem fed_horizon_is_where_the_runs_part :
    sched.drop 18 = [lastStep] ∧
    ((runOf Kernel.current tblsD 18).fed.worlds 1).node.T = Wall.sample 195 ∧
    inside Kernel.current (runOf Kernel.current tblsD 18) (lastStep.step tblsD) = false ∧
    inside Kernel.current (runOf Kernel.current tblsN 18) (lastStep.step tblsN) = true ∧
    ((fobs Silence.current Ledger.current cfg Kernel.current peers (runOf Kernel.current tblsD 18)
      (lastStep.step tblsD)).parts.drop 2).map (fun x => (x.input, x.hot, x.cid)) =
      [(0, false, 8), (1, false, 8)] ∧
    (fobs Silence.current Ledger.current cfg Kernel.current peers (runOf Kernel.current tblsN 18)
      (lastStep.step tblsN)).parts.drop 2 = [] := by
  decide +kernel

/-! ### The leaks the relation rejects, on the same federation runs -/

/-- `DEF-12`'s marker keyed on the arm bit: the two holder decisions at 130 confirm in one family
and not the other, at node 1 and at node 2. -/
@[req "DEF-12"]
theorem fed_marker_leaks_with_armBit :
    ((pairs .armBit Kernel.current sched).map fun y => y.1 == y.2) =
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, false,
       false, true, true] ∧
    (((pairs .armBit Kernel.current sched).drop 14).take 2).map
      (fun y => (y.1.node.map fun o => (o.1, o.2.marker), y.2.node.map fun o => (o.1, o.2.marker))) =
      [(some (1, true), some (1, false)), (some (2, true), some (2, false))] := by
  decide +kernel

/-- `F54`'s traversal that runs only when `T` moved: node 1's hot acceptance at 140 shrinks `T` in
the armed family, which visits the whole registry, and the other visits nothing. -/
@[req "DUR-20"]
theorem fed_traversal_leaks_with_onlyWhenMoved :
    ((pairs Silence.current withdrawnTraversal sched).map fun y => y.1 == y.2) =
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
       true, true, false] ∧
    ((pairs Silence.current withdrawnTraversal sched).drop 17).map
      (fun y => (y.1.node.map (·.2.ops), y.2.node.map (·.2.ops))) =
      [(some [.visit 21, .visit 22, .visit 7, .visit 8, .visit 1, .visit 2], some [])] := by
  decide +kernel

/-- A hot window's close on the effective sample, alone or with the driver: node 1's send on the
wall stepped back to 90 broadcasts in the second family, inside the window and below `T`, and the
armed family's freeze refuses it. -/
@[req "SPN-38"]
theorem fed_close_on_effective_leaks :
    ((pairs Silence.current withdrawnCloseTime sched).map fun y => y.1 == y.2) =
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
       true, false, true] ∧
    ((pairs Silence.current withdrawnReadTime sched).map fun y => y.1 == y.2) =
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
       true, false, true] ∧
    (((pairs Silence.current withdrawnCloseTime sched).drop 16).take 1).map
      (fun y => (y.1.node.map (·.2.effects), y.2.node.map (·.2.effects))) =
      [(some [], some [.broadcast hot1.id])] := by
  decide +kernel

/-- The driver on the effective sample alone: node 1's fire pass on the wall stepped back to 95 is
inside the horizon of `T = 100`, and the second family's partial enters the federation's partial
inventory while the first family's freeze holds it. As the readers stand the walk ends before that
step, every pair equal. -/
@[req "DUR-7"]
theorem fed_driver_on_effective_leaks :
    (pairs Silence.current Kernel.current clampSched).length = 6 ∧
    (pairs Silence.current Kernel.current clampSched).all (fun y => y.1 == y.2) = true ∧
    ((pairs Silence.current withdrawnDriverTime clampSched).map fun y => y.1 == y.2) =
      [true, true, true, true, true, true, false] ∧
    ((pairs Silence.current withdrawnDriverTime clampSched).drop 6).map
      (fun y => (y.1.parts.length, y.2.parts.map Exp.signer)) = [(0, [1])] := by
  decide +kernel

/-- Not a flip: a holder decision that inserted the Escape only under duress. At node 1's holder
decision on the relay from node 2 at 130, the leaky variant's work differs between the families,
while the work the walk observes is the same in both. -/
@[req "DUR-10"]
theorem fed_duress_only_insertion_leaks :
    workDuressOnly (envAt 130 130) ((runOf Kernel.current tblsD 14).fed.worlds 1).node (.receipt 20 2)
      = [.select 8, .visit 7, .visit 8, .visit 1, .visit 2] ∧
    workDuressOnly (envAt 130 130) ((runOf Kernel.current tblsN 14).fed.worlds 1).node (.receipt 20 2)
      = [.visit 7, .visit 8, .visit 1, .visit 2] ∧
    (((pairs Silence.current Kernel.current sched).drop 14).take 1).map
      (fun y => (y.1.node.map (·.2.ops), y.2.node.map (·.2.ops))) =
      [(some [.select 8, .visit 7, .visit 8, .visit 1, .visit 2],
        some [.select 8, .visit 7, .visit 8, .visit 1, .visit 2])] := by
  decide +kernel

/-! ### An adaptive observer -/

/-- The partial a history's latest observation holds that node 2 signed, if any. -/
def signedBy2 (h : List FObs) : Option Exp :=
  (h.getLast?.map FObs.parts).bind (·.find? (·.signer == 2))

/-- An observer that runs `sched` but picks its 12th and 13th steps from what it has seen. After
each of those observations it looks in the partial inventory for a partial node 2 signed: if there
is one it delivers that partial, as it reads it, to node 1 at 86, and if there is none it runs node
2's fire pass at 85. The partial delivered is not written into the observer. -/
def follow : Observer where
  next h :=
    if h.length = 11 ∨ h.length = 12 then
      match signedBy2 h with
      | some x => some (.net (.deliverPartial 1 (envAt 86 86) x))
      | none => some (.input 2 (envAt 85 85) (.pinless .firePass))
    else sched[h.length]?

def apairs (c : Scheduler) (k : Nat) : List (FObs × FObs) :=
  awalk Silence.current Ledger.current cfg Kernel.current honest peers tblsD tblsN c k F0 F0 [] []

/-- **The relation against an adaptive observer, on a run with inter-node traffic.**
`FedSilence.fed_silence_adaptive_fresh` at the values as they stand. The observer branches on an
earlier observation: after node 1's fire pass the inventory holds no partial node 2 signed, and it
runs node 2's fire pass; after that one the inventory holds `part2`, and it delivers it. Each run's
observer selects `sched`, and the adaptive walk is the walk of `fed_run_silent`, 18 steps with
relays and partials delivered, stopping at the horizon. -/
@[req "DUR-1"]
theorem adaptive_run_silent :
    (∀ y ∈ apairs follow.sched 19, y.1 = y.2) ∧
    signedBy2 (((pairs Silence.current Kernel.current sched).take 11).map Prod.fst) = none ∧
    signedBy2 (((pairs Silence.current Kernel.current sched).take 12).map Prod.fst) = some part2 ∧
    play Silence.current Ledger.current cfg Kernel.current peers tblsD follow 19 F0 [] = sched ∧
    play Silence.current Ledger.current cfg Kernel.current peers tblsN follow 19 F0 [] = sched ∧
    apairs follow.sched 19 = pairs Silence.current Kernel.current sched ∧
    (apairs follow.sched 19).length = 18 :=
  ⟨(fed_silence_adaptive_fresh rfl rfl rfl rfl rfl rfl honest peers tblsD tblsN F0 F0_fresh F0_sweep
      follow 19).2, by decide +kernel⟩

/-- A scheduler that reads node 1's arm bit, which no observation carries. For its 17th step it
runs a tick at node 1 if node 1 is armed and at node 2 if not; otherwise it is `follow`. -/
def peek : Scheduler := fun F h =>
  if h.length = 16 then
    some (.input (if (F.fed.worlds 1).node.armed then 1 else 2) (envAt 131 131) (.pinless .tick))
  else follow.next h

/-- **The hidden-state reader distinguishes the families.** Its walk is equal for 16 steps, both
families' histories the same, and its 17th step, admitted in both runs, wakes node 1 in the armed
family and node 2 in the other. It is not an observer: at that one history it picks two different
steps. -/
@[req "DUR-1"]
theorem hidden_state_reader_leaks :
    ((apairs peek 17).map fun y => y.1 == y.2) =
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
       true, false] ∧
    ((apairs peek 17).drop 16).map (fun y => (y.1.node.map (·.1), y.2.node.map (·.1))) =
      [(some 1, some 2)] ∧
    Federation.admits honest (runOf Kernel.current tblsN 16).fed
      (.process 2 (envAt 131 131) .tick) = true ∧
    (apairs peek 16).map Prod.fst = (apairs peek 16).map Prod.snd ∧
    ¬ ∃ σ : Observer, σ.sched = peek := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨σ, hσ⟩
  have h0 := congrFun (congrFun hσ (runOf Kernel.current tblsD 16)) ((apairs peek 16).map Prod.fst)
  have h1 := congrFun (congrFun hσ (runOf Kernel.current tblsN 16)) ((apairs peek 16).map Prod.fst)
  simp only [Observer.sched] at h0 h1
  have hne : peek (runOf Kernel.current tblsD 16) ((apairs peek 16).map Prod.fst) ≠
      peek (runOf Kernel.current tblsN 16) ((apairs peek 16).map Prod.fst) := by
    decide +kernel
  exact hne (h0.symm.trans h1)

/-! ### Per-destination messages

`FedSilence.FObs` carries the messages each step addresses, one per destination, and the message a
delivery hands to its node. `peers` lists node 3, which runs nothing here: the messages a holder of
node 3's channel would be sent are part of what the relation compares. -/

/-- **The relation, per destination, on the run with inter-node traffic.** The walk of
`fed_run_silent` addresses each relay and each partial to both other peers, node 3 included, and
delivers five messages; `fed_run_silent` gives each step's equal in the two families. Listed by
sender and destination. -/
@[req "DUR-1"]
theorem fed_frames_per_destination :
    ((pairs Silence.current Kernel.current sched).map fun y =>
      (y.1.sent.map fun f => (f.src, f.dst), y.1.recv.map fun f => (f.src, f.dst))) =
      [([], none), ([], none), ([(1, 2), (1, 3)], none), ([(2, 1), (2, 3)], none), ([], some (2, 1)),
       ([], some (1, 2)), ([], none), ([], none), ([(1, 2), (1, 3)], none), ([(2, 1), (2, 3)], none),
       ([(1, 2), (1, 3)], none), ([(2, 1), (2, 3)], none), ([], some (2, 1)), ([], none),
       ([], some (2, 1)), ([], some (1, 2)), ([], none), ([], none)] := by
  decide +kernel

/-- Not a rule the protocol has had: a relay route that reads the Carrier's duress bit, sending a
Carrier this node recorded under duress to no peer. -/
def routeByDuress (F : LFed) (i cid : Nat) : List Frame :=
  if (F.fed.worlds i).node.carriers.any (fun k => k.cid == cid && k.duress) then []
  else addressed peers i [.request cid]

/-- **A PIN-dependent destination is a difference the relation sees.** At the ninth step node 1
relays the Carrier requested under PIN 1. The route that reads the duress bit addresses it to
nobody in the first family and to nodes 2 and 3 in the second, while the step's addressed messages,
which the walk compares, are the same two in both. -/
@[req "DUR-1"]
theorem fed_duress_route_leaks :
    sched[8]? = some (.net (.emit 1 20)) ∧
    routeByDuress (runOf Kernel.current tblsD 8) 1 20 = [] ∧
    routeByDuress (runOf Kernel.current tblsN 8) 1 20 = [⟨1, 2, .request 20⟩, ⟨1, 3, .request 20⟩] ∧
    (((pairs Silence.current Kernel.current sched).drop 8).take 1).map (fun y => (y.1.sent, y.2.sent)) =
      [([⟨1, 2, .request 20⟩, ⟨1, 3, .request 20⟩], [⟨1, 2, .request 20⟩, ⟨1, 3, .request 20⟩])] := by
  decide +kernel

/-- The input of a partial's body. -/
def inputOf : Body → Option Nat
  | .part x => some x.input
  | .request _ => none

/-- Past the horizon, per destination: node 1's fire pass at 200 addresses the selected Escape's
partial on each of its two inputs to nodes 2 and 3 in the first family, and nothing in the second. -/
@[req "DUR-7"]
theorem fed_horizon_frames :
    (fobs Silence.current Ledger.current cfg Kernel.current peers (runOf Kernel.current tblsD 18)
      (lastStep.step tblsD)).sent.map (fun f => (f.src, f.dst, inputOf f.body)) =
      [(1, 2, some 0), (1, 2, some 1), (1, 3, some 0), (1, 3, some 1)] ∧
    (fobs Silence.current Ledger.current cfg Kernel.current peers (runOf Kernel.current tblsN 18)
      (lastStep.step tblsN)).sent = [] := by
  decide +kernel

/-! ### A refund that happened only under duress -/

/-- A hot spend that fires at 800, past every instant below, and a hot spend of 995 against the cap
of 1000. -/
def hX : Cand := cand 23 { id := 118, inputs := [20], outflow := 10 } true (some 800) 900
def eX : Cand := cand 24 { id := 119, inputs := [20, 21], outflow := 0 } false none 900
def sBig : Cand := cand 25 { id := 120, inputs := [22], outflow := 995 } true (some 800) 900
def eBig : Cand := cand 26 { id := 121, inputs := [22, 23], outflow := 0 } false none 900

def bigStep : PStep := .input 1 (envAt 140 140) (.request 30 0 (Wall.sample 900) sBig eBig)

/-- Node 1 accepts `hX` under PIN 0 at 40, reserving 10. Both nodes accept a pair that is not hot
under PIN 1 at 72, node 2 relays it, and node 1's holder decision on that relay at 130 arms node 1
in the first family and freezes `hX` there. At 140 node 1 is asked for `sBig`. -/
def refundSched : List PStep :=
  [.input 1 (envAt 40 40) (.request 10 0 (Wall.sample 900) hX eX),
   .input 1 (envAt 72 72) (.request 20 1 (Wall.sample 900) sp3 es3),
   .input 2 (envAt 72 72) (.request 20 1 (Wall.sample 900) sp3 es3),
   .net (.emit 2 20),
   .net (.deliver 1 (envAt 130 130) ⟨2, 20⟩),
   bigStep]

def runR (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  lrun Ledger.current cfg Kernel.current F0 ((refundSched.take k).map (·.step tbls))

/-- Not a rule the protocol has had: node `i`'s unexposed charges of frozen candidates refunded. -/
def refundFrozen (F : LFed) (i : Nat) : LFed :=
  { F with leds := fun j => if j = i then (F.leds j).filter (fun row => row.exposed ||
      !(F.fed.worlds j).node.cands.any (fun c => c.id == row.cid && c.frozen)) else F.leds j }

/-- The commitment an acceptance names. -/
def acceptedCid : Resp → Option Nat
  | .accepted c _ _ => some c
  | _ => none

/-- **A refund that happened only under duress is a difference the relation sees.** `POL-21`: "a
refund that happened only under duress would be the timing signal `DUR-1` forbids". As the rules
stand, the walk is equal at all six steps: the arm leaves node 1's ledger as it is in the other
family, holding `hX`'s charge, and `sBig` is refused `HOT_VELOCITY_EXCEEDED` in both. With the freeze
refunding `hX`'s charge, node 1 accepts `sBig` in the first family and refuses it in the second. -/
@[req "POL-21"]
theorem fed_duress_refund_leaks :
    (walk Silence.current Ledger.current cfg Kernel.current honest peers tblsD tblsN F0 F0
      refundSched).length = 6 ∧
    ((runR tblsD 5).fed.worlds 1).node.armed = true ∧
    ((runR tblsN 5).fed.worlds 1).node.armed = false ∧
    (runR tblsD 5).leds 1 = (runR tblsN 5).leds 1 ∧
    ((runR tblsD 5).leds 1).map (·.cid) = [23] ∧
    ((walk Silence.current Ledger.current cfg Kernel.current honest peers tblsD tblsN F0 F0
      refundSched).drop 5).map (fun y => (y.1.node.map (·.2.resp), y.2.node.map (·.2.resp))) =
      [(some (.refused .HOT_VELOCITY_EXCEEDED), some (.refused .HOT_VELOCITY_EXCEEDED))] ∧
    ((fobs Silence.current Ledger.current cfg Kernel.current peers (refundFrozen (runR tblsD 5) 1)
      (bigStep.step tblsD)).node.map (·.2.resp)).bind acceptedCid = some sBig.id ∧
    (fobs Silence.current Ledger.current cfg Kernel.current peers (refundFrozen (runR tblsN 5) 1)
      (bigStep.step tblsN)).node.map (·.2.resp) = some (.refused .HOT_VELOCITY_EXCEEDED) := by
  decide +kernel

/-- `FedSilence.fed_silence_fresh` on the same schedule: every step's observation is equal. -/
@[req "DUR-1"]
theorem fed_refund_run_silent :
    ∀ y ∈ walk Silence.current Ledger.current cfg Kernel.current honest peers tblsD tblsN F0 F0
      refundSched, y.1 = y.2 :=
  fed_silence_fresh rfl rfl rfl rfl rfl rfl honest peers tblsD tblsN F0 F0_fresh F0_sweep refundSched

/-! ### Equal frames, unequal bytes -/

/-- Node 1's relay to node 3, in an envelope with `WIR-29`'s wallet id and manifest hash, a one-byte
payload, the timestamp 140 and a given nonce. -/
def relayBytes (nonce : Encode.Bytes) : Encode.Bytes :=
  Envelope.preimage ((⟨1, 3, .request 20⟩ : Frame).envelope (List.replicate 32 0x22)
    (List.replicate 32 0x33) [0x41] nonce 140)

/-- **Shape equality is not byte equality.** One frame in two envelopes whose nonces differ, as two
fresh random draws may: the preimages differ, and both are as long as
`FedSilence.frame_preimage_length` says. -/
@[req "NCH-11"]
theorem equal_frames_unequal_bytes :
    relayBytes (List.replicate 16 0x44) ≠ relayBytes (List.replicate 16 0x45) ∧
    (relayBytes (List.replicate 16 0x44)).length = 116 ∧
    (relayBytes (List.replicate 16 0x45)).length = 116 := by
  decide +kernel

end BtcPolicy.Exhibits.FedSilence

namespace BtcPolicy.Exhibits.Admission
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.FedSilence BtcPolicy.Admission
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 spendPsbt sp0 es0 acc lcfg checked_pair)
open BtcPolicy.Federation (Step)
open BtcPolicy.Federation.Cases (honest)

/-! ## `POL-20`'s admission bound over a ledgered federation run

Research task `bps-uaer.14`. Three honest nodes, 1 to 3, each `Kernel.RegistrationCases.A` at its own
id (threshold 2) with an empty Hot ledger, cap 100 and window 600 (`Exhibits.Ingress.lcfg`). Every
acceptance is the checked pair of `Exhibits.Ingress.req0` (`Exhibits.Ingress.checked_pair`): a hot
spend of outflow 55 and its Escape. The cuts are each node's ledger at the end of the schedule at
its own HotClock sample. These runs are not hand-seeded, except where a docstring says so. -/

def F0 : LFed := { fed := Federation.Cases.fed0, leds := fun _ => [] }

/-- The three nodes accept the pair at HotClock 5; relays reach nodes 1 and 2, which decide
normally and release their partials at 60. -/
def run : List Step :=
  [acc ctx0 1 false, acc ctx0 2 false, acc ctx0 3 false, .emit 1 10, .emit 2 10,
   .deliver 1 env0 ⟨2, 10⟩, .deliver 2 env0 ⟨1, 10⟩,
   .process 1 envFire .firePass, .process 2 envFire .firePass]

def final : LFed := lrun Ledger.current lcfg current F0 run
def now : Nat → Mono := fun _ => Mono.sample 60
def cohort : List Ledgers.Spend := [(sp0.id, 55)]

theorem run_legal : llegal Ledger.current lcfg current honest F0 run = true := by decide +kernel

/-- Forgetting the ledgers leaves a federation execution (`FedSilence.lrun_execution`). -/
theorem run_execution :
    Federation.Execution current honest (ltrace Ledger.current lcfg current [] F0 run) final.fed :=
  lrun_execution (.init _ Federation.Cases.fed0_fresh) run run_legal

theorem run_checked : Ingress.CheckedTrace ctx0 (ltrace Ledger.current lcfg current [] F0 run) :=
  Ingress.checkedTrace_of ctx0 _ [req0] (by decide +kernel)

theorem cohort_checked : ∀ s ∈ cohort, ∃ fits q sp es, Ingress.check ctx0 fits q = .accepted sp es ∧
    sp.id = s.1 ∧ sp.tx.outflow = s.2 := by
  intro s hs
  simp only [cohort, List.mem_singleton] at hs
  subst hs
  exact ⟨true, req0, sp0, es0, checked_pair.1, rfl, checked_pair.2.2.2.1⟩

theorem run_clock : ∀ i ∈ honest, ∀ x ∈ nodeTrace i run, x.1.mono.notAfter (now i) = true := by
  decide +kernel

/-- Each node's acceptance is a fresh reservation at HotClock 5, inside the interval ending at 60,
and no prune pass follows it. -/
theorem all_counted : ∀ i ∈ honest, Counted Ledger.current lcfg current F0 run i sp0.id (now i) := by
  intro i hi
  simp only [honest, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨[], run.drop 1, env0, 10, false, Wall.sample 200, sp0, es0, rfl, rfl,
      ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  · exact ⟨run.take 1, run.drop 2, env0, 10, false, Wall.sample 200, sp0, es0, rfl, rfl,
      ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  · exact ⟨run.take 2, run.drop 3, env0, 10, false, Wall.sample 200, sp0, es0, rfl, rfl,
      ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- **The bound, with its three run premises derived.** `Admission.fed_bridge` on this run, `q = 2`
(`t − c` at `c = 0`): `hinv`, `hamt` and `hcohort` come from the run, not from a hand-seeded cut. -/
@[req "POL-20"]
theorem admission_bound_derived : 2 * Ledgers.outflow cohort ≤ honest.length * lcfg.cap :=
  fed_bridge (g := Ledger.current) (cfg := lcfg) (r := current) (F := F0) (ss := run) (t := [])
    (honest := honest) (ctx := ctx0) rfl rfl (fun _ _ => rfl) run_checked Ingress.code_injective 2 cohort (by decide +kernel)
    cohort_checked now run_clock
    (fun s hs => by
      simp only [cohort, List.mem_singleton] at hs
      subst hs
      exact ⟨honest, by decide +kernel, by decide +kernel, fun i hi => ⟨hi, all_counted i hi⟩⟩)

/-- What the cuts hold. All three count the spend; each charges its 55; the partials nodes 1 and 2
released set their rows' exposure bits, and node 3's row, unreleased, is charged alike. Exposure
is a different record from the charge. -/
@[req "POL-20"]
theorem run_cuts :
    cohortCount lcfg.window (cuts final honest now) sp0.id = 3 ∧
    (honest.map fun i => ((final.leds i).map fun row => (row.cid == sp0.id, row.amount, row.exposed))) =
      [[(true, 55, true)], [(true, 55, true)], [(true, 55, false)]] := by
  decide +kernel

/-! ### Failing siblings: the premises each derivation takes -/

/-- `hamt` needs the collision-free commitment id. Here node 2's request spends 50 to the allowlist
with 45 of change, and its commitment is mapped onto the id of `req0`'s spend; both acceptances are
checked, and the cohort amount is a checked spend's outflow, yet node 2 charges 50 under the id
whose cohort amount is 55. -/
def reqB : BtcPolicy.Ingress.Request :=
  { req0 with spend := { req0.spend with psbt :=
      { spendPsbt with txOutputs := [⟨[12, 0], 45⟩, ⟨[11, 1], 50⟩] } } }

def ctxC : BtcPolicy.Ingress.Ctx :=
  { ctx0 with commitId := fun b =>
      if b = Encode.encode (Ingress.commitment ctx0 reqB reqB.spend) then sp0.id else Ingress.code b }

def accB (i : Nat) (q : BtcPolicy.Ingress.Request) : Step :=
  .process i env0 (.accept 10 false (Wall.sample 200) (Ingress.cand ctxC q q.spend true q.fireAt)
    (Ingress.cand ctxC q q.escape false none))

def runC : List Step := [accB 1 req0, accB 2 reqB]

@[req "CHN-24"]
theorem collision_splits_amount :
    Ingress.CheckedTrace ctxC (ltrace Ledger.current lcfg current [] F0 runC) ∧
    Ingress.check ctxC true req0 = .accepted (Ingress.cand ctxC req0 req0.spend true req0.fireAt)
      (Ingress.cand ctxC req0 req0.escape false none) ∧
    (Ingress.cand ctxC req0 req0.spend true req0.fireAt).id = sp0.id ∧
    (Ingress.cand ctxC req0 req0.spend true req0.fireAt).tx.outflow = 55 ∧
    ¬ (∀ k ∈ cuts (lrun Ledger.current lcfg current F0 runC) honest now, ∀ s ∈ cohort,
        ∀ row ∈ k.led, row.cid = s.1 → row.amount = s.2) :=
  ⟨Ingress.checkedTrace_of ctxC _ [req0, reqB] (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `hinv` and `hamt` need the empty start ledger. Hand-seeded: node 2 starts holding a row under
`sp0`'s id, of 150, with no acceptance behind it. The same run then leaves node 2 over the cap,
and charging 150 under the cohort's id. -/
def seeded : LFed :=
  { F0 with leds := fun i => if i = 2 then
      [{ cid := sp0.id, amount := 150, reservedAt := Mono.sample 0, expiry := Wall.sample 200,
         exposed := false }] else [] }

@[req "POL-20"]
theorem seeded_ledger_breaks_premises :
    Ingress.CheckedTrace ctx0 (ltrace Ledger.current lcfg current [] seeded run) ∧
    liveSum ((lrun Ledger.current lcfg current seeded run).leds 2) = 150 ∧
    ¬ (∀ k ∈ cuts (lrun Ledger.current lcfg current seeded run) honest now, ∀ s ∈ cohort,
        ∀ row ∈ k.led, row.cid = s.1 → row.amount = s.2) :=
  ⟨Ingress.checkedTrace_of ctx0 _ [req0] (by decide +kernel), by decide +kernel, by decide +kernel⟩

/-- A refunded reservation is not counted (`Ledger.pruneKeeps`). Node 1 accepts at HotClock 5; a
prune pass at wall and HotClock 300, past the pair's signed expiry of 200, collects the unreleased
pair and refunds the unexposed row. The acceptance is fresh and inside the interval ending at 300. -/
def runRefund : List Step := [acc ctx0 1 false, .process 1 (envAt 300 300) .prune]

@[req "POL-18"]
theorem refunded_not_counted :
    Reserves Ledger.current lcfg current F0 [] 1 env0 10 false (Wall.sample 200) sp0 es0 ∧
    Mono.withinWindow env0.mono (Mono.sample 300) lcfg.window = true ∧
    pruneKeeps Ledger.current lcfg current sp0.id env0.mono
      (sysStep Ledger.current lcfg current env0 (F0.sys 1)
        (.accept 10 false (Wall.sample 200) sp0 es0)).1 (nodeTrace 1 (runRefund.drop 1)) = false ∧
    countsAt lcfg.window sp0.id
      { led := (lrun Ledger.current lcfg current F0 runRefund).leds 1, now := Mono.sample 300 } = false :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A retry is admitted at its own HotClock sample but places no reservation (`POL-18`: "a retry
keeps the original reservation time"), so freshness is needed. Node 1 accepts at HotClock 5, then
the same pair under Carrier 20 at wall 150 and HotClock 650. The first row is live on its wall
disjunct and stays; the retry is inside the interval ending at 650, the reservation is not. -/
def runRetry : List Step :=
  [acc ctx0 1 false, .process 1 (envAt 150 650) (.accept 20 false (Wall.sample 200) sp0 es0)]

@[req "POL-18"]
theorem retry_not_fresh :
    admitted ((lrun Ledger.current lcfg current F0 [acc ctx0 1 false]).sys 1).world
      (sysStep Ledger.current lcfg current (envAt 150 650)
        ((lrun Ledger.current lcfg current F0 [acc ctx0 1 false]).sys 1)
        (.accept 20 false (Wall.sample 200) sp0 es0)).1.world
      (.accept 20 false (Wall.sample 200) sp0 es0) = true ∧
    holds (checked Ledger.current.release (envAt 150 650) lcfg.window
      ((lrun Ledger.current lcfg current F0 [acc ctx0 1 false]).sys 1).led
      (.accept 20 false (Wall.sample 200) sp0 es0)) sp0.id = true ∧
    Mono.withinWindow (Mono.sample 650) (Mono.sample 650) lcfg.window = true ∧
    countsAt lcfg.window sp0.id
      { led := (lrun Ledger.current lcfg current F0 runRetry).leds 1, now := Mono.sample 650 } = false := by
  decide +kernel

/-- `hclock` is needed. Node 1 accepts at HotClock 5; a second checked request, with signed expiry
1000, is admitted at wall 300 and HotClock 700, and its check releases the first row, dead on both
disjuncts. The cut then reads HotClock 10, behind 700. The spend is `Counted` at that sample, and
not counted there. -/
def reqLate : BtcPolicy.Ingress.Request := { req0 with expiry := 1000 }
def runBack : List Step :=
  [acc ctx0 1 false, .process 1 (envAt 300 700) (.accept 20 false (Wall.sample 1000)
    (Ingress.cand ctx0 reqLate reqLate.spend true reqLate.fireAt)
    (Ingress.cand ctx0 reqLate reqLate.escape false none))]

@[req "POL-22"]
theorem backward_clock_uncounts :
    Counted Ledger.current lcfg current F0 runBack 1 sp0.id (Mono.sample 10) ∧
    countsAt lcfg.window sp0.id
      { led := (lrun Ledger.current lcfg current F0 runBack).leds 1, now := Mono.sample 10 } = false ∧
    ¬ (∀ x ∈ nodeTrace 1 runBack, x.1.mono.notAfter (Mono.sample 10) = true) ∧
    Ingress.CheckedTrace ctx0 (ltrace Ledger.current lcfg current [] F0 runBack) :=
  ⟨⟨[], runBack.drop 1, env0, 10, false, Wall.sample 200, sp0, es0, rfl, rfl,
      ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩,
    by decide +kernel, by decide +kernel,
    Ingress.checkedTrace_of ctx0 _ [req0, reqLate] (by decide +kernel)⟩

end BtcPolicy.Exhibits.Admission

/-! ## The transaction-keyed comparison (`F63`; non-normative research)

The runs behind `docs/research/hot-accounting-comparison.md`. Each trace goes through
`Ledger.sysRun` under `Ledger.current` and through `TxAccounting.tsysRun`, over `Kernel.current` both
times, with no hand-seeded ledger. The candidate is no guard value and nothing here decides anything. -/

namespace BtcPolicy.Exhibits.TxAccounting
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.TxAccounting BtcPolicy.Silence
open BtcPolicy.Exhibits.HotLedger
open Kernel.RegistrationCases (cand envAt)

/-- A budget with room for two whole spends, so a re-quote is registered under both accountings. -/
def cfg2 : Config := { cap := 2 * V, window := 120 }
def t0 : TSys := { world := sys0.world, led := [] }

def runC (c : Config) (tr : List (Env × Event)) : Sys := (sysRun Ledger.current c Kernel.current sys0 tr).1
def runT (c : Config) (tr : List (Env × Event)) : TSys := (tsysRun c Kernel.current t0 tr).1

def hasCand (n : Node) (id : Nat) : Bool := n.cands.any (·.id == id)
/-- The commitments with a standing entry, row by row. -/
def entryIds (s : TSys) : List (List Nat) := s.led.map fun row => row.entries.map (·.cid)

def twinE : Cand := cand 10 esc1 false none (expiryOf twinAccept)
def acc1 : Env × Event := (envAt 0 0, .accept 10 false (Wall.sample (expiryOf 0)) s1 HotLedger.e1)
def accTwin : Env × Event := (envAt 60 60, .accept 20 false (Wall.sample (expiryOf 60)) s1Twin twinE)
/-- A hot spend and its Escape for an acceptance at wall sample `at'`: `SPN-30`'s fire time and `SPN-10`'s
ceiling on the signed expiry, at equality, read from that sample. -/
def spendAt (id : Nat) (tx : Tx) (at' : Nat) : Cand := cand id tx true (some (fireOf at')) (expiryOf at')
def escAt (id : Nat) (tx : Tx) (at' : Nat) : Cand := cand id tx false none (expiryOf at')
/-- A distinct hot spend at the sample `at'`, and a second one. -/
def acc5 (w m at' : Nat) : Env × Event :=
  (envAt w m, .accept 30 false (Wall.sample (expiryOf at')) (spendAt 5 hot2 at') (escAt 6 esc2 at'))
def acc7 (w m at' : Nat) : Env × Event :=
  (envAt w m, .accept 40 false (Wall.sample (expiryOf at')) (spendAt 7 hot3 at') (escAt 8 esc3 at'))
/-- `s1` accepted, opened at 10, and its partial queued at 30. -/
def opened1 : List (Env × Event) := [acc1, (envAt 10 10, .receipt 10 1), (envAt 30 30, .firePass)]

/-! ### Exact retry -/

/-- A retry under a new Carrier, and one under the same Carrier, change neither ledger: one charge at
the original reservation time, under both accountings. -/
theorem exact_retry_preserved :
    let fresh : Env × Event := (envAt 30 30, .accept 11 false (Wall.sample (expiryOf 0)) s1 HotLedger.e1)
    let same : Env × Event := (envAt 30 30, .accept 10 false (Wall.sample (expiryOf 0)) s1 HotLedger.e1)
    (runC cfg [acc1, fresh]).led = (runC cfg [acc1]).led ∧
    (runC cfg [acc1, same]).led = (runC cfg [acc1]).led ∧
    (runT cfg [acc1, fresh]).led = (runT cfg [acc1]).led ∧
    (runT cfg [acc1, same]).led = (runT cfg [acc1]).led ∧
    (runC cfg [acc1]).led.map (·.reservedAt) = [Mono.sample 0] ∧
    (runT cfg [acc1]).led.map (fun row => row.entries.map (·.reservedAt)) = [[Mono.sample 0]] ∧
    liveSum (runC cfg [acc1]).led = V ∧ tSum (runT cfg [acc1]).led = V := by decide

/-! ### New expiry over one transaction -/

/-- A maximal spend re-quoted while its first charge stands: the current ledger refuses and registers
nothing, the availability cost `ADR-0014` names for a re-quote of one transaction; the
candidate registers it under the one charge. -/
theorem requote_of_maximal_spend :
    hasCand (runC cfg [acc1, accTwin]).world.node 9 = false ∧
    liveSum (runC cfg [acc1, accTwin]).led = V ∧
    hasCand (runT cfg [acc1, accTwin]).world.node 9 = true ∧
    entryIds (runT cfg [acc1, accTwin]) = [[1, 9]] ∧
    tSum (runT cfg [acc1, accTwin]).led = V := by decide

/-- With room for both, the current ledger charges `2V` for one transaction and the candidate `V`, and
what the difference buys is the next distinct spend: refused under the current ledger, admitted under
the candidate. -/
theorem requote_frees_budget :
    let next : Env × Event := acc5 70 70 70
    liveSum (runC cfg2 [acc1, accTwin]).led = 2 * V ∧
    tSum (runT cfg2 [acc1, accTwin]).led = V ∧
    hasCand (runC cfg2 [acc1, accTwin, next]).world.node 5 = false ∧
    hasCand (runT cfg2 [acc1, accTwin, next]).world.node 5 = true ∧
    tSum (runT cfg2 [acc1, accTwin, next]).led = 2 * V := by decide

/-- The price: the charge now lasts as long as the union of its commitments' lifetimes. Two re-quotes
keep one `V` charged at 200, where the current ledger, having refused them, has released it by then,
and a distinct spend is admitted there only under the current ledger. -/
theorem requote_holds_the_charge_longer :
    let third : Cand := cand 13 hot1 true (some 140) 240
    let thirdE : Cand := cand 14 esc1 false none 240
    let z : Cand := cand 5 hot2 true (some 220) 320
    let zE : Cand := cand 6 esc2 false none 320
    let tr : List (Env × Event) :=
      [acc1, accTwin, (envAt 120 120, .accept 21 false (Wall.sample 240) third thirdE),
        (envAt 200 200, .accept 30 false (Wall.sample 320) z zE)]
    hasCand (runC cfg tr).world.node 5 = true ∧ (runC cfg tr).led.map (·.cid) = [5] ∧
    hasCand (runT cfg tr).world.node 5 = false ∧ entryIds (runT cfg tr) = [[1, 9, 13]] := by decide

/-- A simplification this comparison rejects: keeping only the first reservation time. At HotClock 121
with the wall stepped forward past the twin's expiry, both `POL-19` disjuncts are false at the first
time and the monotonic one holds at the twin's own, so the simplified row would release a charge
`POL-19`'s window still holds. -/
theorem first_time_only_loses_charge :
    reservationLive (Mono.sample 0) (Mono.sample 121) 120 (Wall.sample 181) (Wall.sample 180) = false ∧
    reservationLive (Mono.sample 60) (Mono.sample 121) 120 (Wall.sample 181) (Wall.sample 180) = true := by
  decide

/-! ### Distinct RBF transaction -/

/-- A fee-bump over the same input with a different txid: its own full charge, no netting with the
conflict. The same verdict and the same sum under both accountings, at either budget. -/
theorem rbf_keeps_its_own_charge :
    let bump : Tx := { id := 210, inputs := [0], outflow := V }
    let sb : Cand := cand 11 bump true (some 80) 180
    let eb : Cand := cand 12 esc1 false none 180
    let acc : Env × Event := (envAt 60 60, .accept 20 false (Wall.sample 180) sb eb)
    hasCand (runC cfg [acc1, acc]).world.node 11 = false ∧
    hasCand (runT cfg [acc1, acc]).world.node 11 = false ∧
    liveSum (runC cfg2 [acc1, acc]).led = 2 * V ∧
    tSum (runT cfg2 [acc1, acc]).led = 2 * V ∧
    (runT cfg2 [acc1, acc]).led.map (·.txid) = [200, 210] := by decide

/-! ### One exposed twin -/

/-- `f63_twins_end_charging_nothing`'s history, run through both composed steps with no fixture: `s1`'s
partial leaves at 30, a twin is registered at 60, a hot admission at 121 releases `s1`'s reservation,
and a prune pass past the twin's expiry collects both. -/
def exposedTwin : List (Env × Event) :=
  opened1 ++ [accTwin, acc5 121 121 121]
def pruneTwin : Env × Event := (envAt 181 121, .prune)
def nextSpend : Env × Event := acc7 181 122 181

/-- The current ledger refunds the unexposed twin and charges nothing for the transaction whose
partial is out. The candidate's row carries the exposure the OR gives it and the same prune pass keeps
it. The two meters now differ in the other direction: `V` against `2V`, and the next distinct spend is
admitted only under the current ledger. -/
theorem exposed_twin_blocks_the_refund :
    (runC cfg2 (exposedTwin ++ [pruneTwin])).led.map (·.cid) = [5] ∧
    (runT cfg2 (exposedTwin ++ [pruneTwin])).led.map (fun row => (row.txid, row.exposed)) =
      [(200, true), (202, false)] ∧
    (runT cfg2 (exposedTwin ++ [pruneTwin])).world.node.cands.any (·.tx.id == 200) = false ∧
    hasCand (runC cfg2 (exposedTwin ++ [pruneTwin, nextSpend])).world.node 7 = true ∧
    hasCand (runT cfg2 (exposedTwin ++ [pruneTwin, nextSpend])).world.node 7 = false := by decide

/-- **Neither accounting dominates.** One history each way, over the same transitions: the candidate
admits what the current ledger refuses, and the current ledger admits what the candidate refuses. -/
theorem neither_accounting_dominates :
    (hasCand (runT cfg [acc1, accTwin]).world.node 9 = true ∧
      hasCand (runC cfg [acc1, accTwin]).world.node 9 = false) ∧
    (hasCand (runC cfg2 (exposedTwin ++ [pruneTwin, nextSpend])).world.node 7 = true ∧
      hasCand (runT cfg2 (exposedTwin ++ [pruneTwin, nextSpend])).world.node 7 = false) := by decide

/-! ### All commitments expire -/

/-- Both twins unexposed. The prune pass at 121 collects the first and the current ledger refunds its
row: `2V` becomes `V`. The candidate charged `V` all along and holds it. The prune pass past the twin's
expiry empties both. -/
theorem unexposed_twins_refund :
    let p1 : Env × Event := (envAt 121 121, .prune)
    let p2 : Env × Event := (envAt 181 122, .prune)
    liveSum (runC cfg2 [acc1, accTwin]).led = 2 * V ∧
    (runC cfg2 [acc1, accTwin, p1]).led.map (·.cid) = [9] ∧
    entryIds (runT cfg2 [acc1, accTwin, p1]) = [[1, 9]] ∧
    (runC cfg2 [acc1, accTwin, p1, p2]).led = [] ∧
    (runT cfg2 [acc1, accTwin, p1, p2]).led = [] := by decide

/-! ### Aged-out exposed authority -/

/-- Quorum on `s1`'s transaction is out by 30, from this node's partial and a peer's. At 121 a charge for
it still stands under both, the twin's, and only the candidate's says the transaction is exposed. By 182
each has gone by the release, not by a refund, and two other spends of `V` are charged. The authority
outlives the charge under both, and a settlement of the transaction moves neither ledger. -/
theorem aged_out_authority_outlives_both :
    let tr := opened1 ++ [(envAt 30 30, .receivePartial (sighash hot1 0) 0 2 1), accTwin, acc5 121 121 121]
    let later : Env × Event := acc7 182 182 182
    (runT cfg2 tr).led.map (fun row => (row.txid, row.exposed)) = [(200, true), (202, false)] ∧
    (runC cfg2 tr).led.map (fun x => (x.cid, x.exposed)) = [(9, false), (5, false)] ∧
    (runC cfg2 (tr ++ [later])).led.map (·.cid) = [5, 7] ∧
    (runT cfg2 (tr ++ [later])).led.map (·.txid) = [202, 204] ∧
    exposedQuorum (runC cfg2 (tr ++ [later])).world s1 = true ∧
    exposedQuorum (runT cfg2 (tr ++ [later])).world s1 = true ∧
    (runC cfg2 (tr ++ [later, (envAt 182 182, .settle hot1)])).led = (runC cfg2 (tr ++ [later])).led ∧
    (runT cfg2 (tr ++ [later, (envAt 182 182, .settle hot1)])).led = (runT cfg2 (tr ++ [later])).led := by
  decide

/-- What the candidate's OR does not reach: once a row has gone, a new commitment over the same
transaction starts an unexposed row, though the quorum is still out, as the current ledger's new row
does. The prune pass past its expiry refunds it under both, along with the other unexposed spend. -/
theorem requote_after_release_forgets_exposure :
    let tr := opened1 ++ [(envAt 30 30, .receivePartial (sighash hot1 0) 0 2 1), acc5 121 121 121]
    let again : Cand := cand 9 hot1 true (some 142) 242
    let againE : Cand := cand 10 esc1 false none 242
    let acc : Env × Event := (envAt 122 122, .accept 20 false (Wall.sample 242) again againE)
    exposedQuorum (runT cfg2 (tr ++ [acc])).world s1 = true ∧
    (runT cfg2 (tr ++ [acc])).led.map (fun row => (row.txid, row.exposed)) =
      [(202, false), (200, false)] ∧
    (runC cfg2 (tr ++ [acc])).led.map (fun x => (x.cid, x.exposed)) = [(5, false), (9, false)] ∧
    (runT cfg2 (tr ++ [acc, (envAt 243 122, .prune)])).led = [] ∧
    (runC cfg2 (tr ++ [acc, (envAt 243 122, .prune)])).led = [] := by decide

/-! ### Backward clocks -/

/-- `F62`'s uncharged fire under the candidate: a tick releases nothing, the second spend of the whole
cap is refused after the step back, and the partial that follows is charged. -/
theorem uncharged_fire_closed_under_candidate :
    (runT cfg unchargedFire).led.map (·.txid) = [200] ∧
    hasCand (runT cfg unchargedFire).world.node 5 = false ∧
    (tsysRun cfg Kernel.current t0 unchargedFire).2 = [s1Partial] := by decide

/-- A released entry stays out while its row stands, and a released row stays gone, across a wall step
back to 50. Re-testing would hold both: the wall disjunct is true again for `s1`'s expiry and the
twin's. -/
theorem released_stays_out_under_backward_wall :
    let dropEntry : Env × Event := acc5 125 125 125
    let dropRow : Env × Event := acc7 182 182 182
    let back : Env × Event := (envAt 50 183, .tick)
    let back2 : Env × Event := (envAt 50 126, .tick)
    entryIds (runT cfg2 [acc1, accTwin, dropEntry, back2]) = [[9], [5]] ∧
    Wall.atOrBefore (Wall.sample 50) (Wall.sample (expiryOf 0)) = true ∧
    (runT cfg2 [acc1, accTwin, dropEntry, dropRow, back]).led.map (·.txid) = [202, 204] ∧
    Wall.atOrBefore (Wall.sample 50) (Wall.sample (expiryOf 60)) = true := by decide

/-! ### Normal and duress worlds -/

def nor : Enrolment := fun _ => false
def dur : Enrolment := fun p => p == 1

/-- PIN 1 is the duress PIN in one enrolment. Unopened, so inside the horizon throughout: a re-quote
and both prune passes, the second of which refunds the row. -/
def walkRefund : List (Env × Input) :=
  [ (envAt 0 0, .request 10 1 (Wall.sample 120) s1 HotLedger.e1),
    (envAt 60 60, .request 20 0 (Wall.sample 180) s1Twin twinE),
    (envAt 121 121, .pinless .prune),
    (envAt 181 122, .pinless .prune) ]

/-- Opened, so armed in one run from 10, with `s1`'s fire time at 20: a re-quote, a budget refusal and a
prune pass before the horizon. -/
def walkArmed : List (Env × Input) :=
  [ (envAt 0 0, .request 10 1 (Wall.sample 120) s1 HotLedger.e1),
    (envAt 5 5, .request 20 0 (Wall.sample (expiryOf 5)) (spendAt 9 hot1 5) (escAt 10 esc1 5)),
    (envAt 10 10, .pinless (.receipt 10 1)),
    (envAt 12 12, .request 30 0 (Wall.sample (expiryOf 12)) (spendAt 5 hot2 12) (escAt 6 esc2 12)),
    (envAt 13 13, .pinless .prune) ]

/-- `t_coupled_walk` applies at the initial state under `Kernel.current`. -/
theorem coupled_premises (c : Config) (tr : List (Env × Input)) :
    ∀ y ∈ tPair c Kernel.current nor dur t0 t0 tr, y.1 = y.2 :=
  t_coupled_walk (by decide) (by decide) (by decide) (by decide) (by decide) nor dur tr t0 t0
    ⟨rfl, rfl, rfl⟩
    (nodeInv_initial _ _ rfl rfl rfl rfl) (nodeInv_initial _ _ rfl rfl rfl rfl)

/-- Both walks stay inside the horizon to their last step, with what they are there to show: the
re-quote's entry, the refund, and a budget refusal with the node armed in one run. -/
theorem coupled_walks_inhabited :
    (tPair cfg2 Kernel.current nor dur t0 t0 walkRefund).map
        (fun y => y.1.2.2.map fun row => (row.txid, row.entries.length)) =
      [[(200, 1)], [(200, 2)], [(200, 2)], []] ∧
    (tPair cfg Kernel.current nor dur t0 t0 walkArmed).map (·.1.1) =
      [false, false, false, true, false] ∧
    (runT cfg ((walkArmed.take 3).map fun x => (x.1, x.2.event dur))).world.node.armed = true := by
  decide

/-- Past the horizon both accountings separate the two runs, on one commitment and alike: the partial
left in the normal run and not in the other, so a prune pass past the expiry and the armed removal
refunds only under duress. No coupling is claimed there. On this schedule, with a re-quote and an
admission before it, the current ledger's two runs hold the same rows and the candidate's do not. -/
theorem past_horizon_split :
    let single (p : Nat) : List (Env × Input) :=
      [ (envAt 0 0, .request 10 p (Wall.sample 120) s1 HotLedger.e1), (envAt 10 10, .pinless (.receipt 10 1)),
        (envAt 30 30, .pinless .firePass), (envAt 222 122, .pinless .prune) ]
    let twins : List (Env × Input) :=
      [ (envAt 0 0, .request 10 1 (Wall.sample 120) s1 HotLedger.e1), (envAt 10 10, .pinless (.receipt 10 1)),
        (envAt 30 30, .pinless .firePass), (envAt 60 60, .request 20 0 (Wall.sample 180) s1Twin twinE),
        (envAt 121 121, .request 30 0 (Wall.sample (expiryOf 121)) (spendAt 5 hot2 121) (escAt 6 esc2 121)),
        (envAt 222 122, .pinless .prune) ]
    let ev (tbl : Enrolment) (tr : List (Env × Input)) : List (Env × Event) :=
      tr.map fun x => (x.1, x.2.event tbl)
    (runC cfg (ev nor (single 1))).led.length = 1 ∧ (runC cfg (ev dur (single 1))).led.length = 0 ∧
    (runT cfg (ev nor (single 1))).led.length = 1 ∧ (runT cfg (ev dur (single 1))).led.length = 0 ∧
    (runC cfg2 (ev nor twins)).led.map (·.cid) = (runC cfg2 (ev dur twins)).led.map (·.cid) ∧
    (runT cfg2 (ev nor twins)).led.map (·.txid) = [200, 202] ∧
    (runT cfg2 (ev dur twins)).led.map (·.txid) = [202] := by decide

/-! ### Equivalence, and what it needs -/

/-- One commitment per transaction, `ADR-0014`'s conflicting replacements included: `adr0014` runs the
same under the candidate, effect for effect, by `same_steps_without_twins`. -/
theorem adr0014_same_under_candidate :
    (tsysRun cfg Kernel.current t0 (steps plain adr0014)).2 =
      (sysRun Ledger.current cfg Kernel.current sys0 (steps plain adr0014)).2 := by
  have h := same_steps_without_twins (name := fun tx => if tx = 200 then 1 else 5) Ledger.current rfl rfl rfl
    cfg Kernel.current (steps plain adr0014) t0 (fun _ hr => by cases hr) (by decide)
  exact h.2

/-- The premise is needed. At a cap of `V` the current ledger refuses the twin and the candidate registers
it, so the states differ. With room for both, the rows project and the meters differ. -/
theorem twins_break_the_projection :
    toSys (runT cfg2 [acc1, accTwin]) = runC cfg2 [acc1, accTwin] ∧
    liveSum (toSys (runT cfg2 [acc1, accTwin])).led ≠ tSum (runT cfg2 [acc1, accTwin]).led ∧
    toSys (runT cfg [acc1, accTwin]) ≠ runC cfg [acc1, accTwin] := by decide

/-! ### Preservation obligations -/

/-- The row keeps the first amount: over a txid that did not bind the outflow, a larger spend under
the same id is admitted free. So the candidate owes `Ingress.tx_of_fields`'s binding plus a collision-free
txid, where the current ledger owes `Ingress.one_amount_per_commitment`'s over the commitment id. -/
theorem txid_must_bind_outflow :
    let huge : Cand := cand 11 { hot1 with outflow := 10 * V } true (some 20) 120
    tAdmits cfg (runT cfg [acc1]).led huge = true ∧
    tSum (tReserve (runT cfg [acc1]).led huge (Mono.sample 5)) = V := by decide

/-- `t_bridge` over a reachable candidate ledger: a re-quoted transaction is one cohort member. -/
theorem bridge_nonvacuous :
    1 * Ledgers.outflow [(200, V)] ≤
      [({ led := (runT cfg [acc1, accTwin]).led, now := Mono.sample 60 } : TCut)].length * cfg.cap :=
  t_bridge cfg 1 [(200, V)] _ (by decide) (by decide)
    (by
      intro k hk
      rw [List.mem_singleton.1 hk]
      exact tSum_le_cap cfg Kernel.current [acc1, accTwin] t0 (by decide))
    (by decide)

end BtcPolicy.Exhibits.TxAccounting

namespace BtcPolicy.Exhibits.Progress
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Progress
open BtcPolicy.Exhibits.TwoRun (A s1 s2 esc1)
open Kernel.RegistrationCases (envAt)

/-! ### Progress profiles, the deadline driver and the unbounded histories

Research task `bps-uaer.16`. One node, 2-of-3, `duress_delay_secs` 200, `epsilon_secs` 5,
`combine_slack_secs` 40, under `Kernel.current`. A duress request at wall 50 and a relay at 60 arm it
with `T = 250`; the Escape's fire window is `[250, 290]`. Every step below is a `Progress.pStep`. -/

/-- The two Escapes, by their full names: inside this namespace a bare `e1` is the coverage Escape. -/
def es1 : Cand := Exhibits.TwoRun.e1
def es2 : Cand := Exhibits.TwoRun.e2

def conf : Lifetime.Cfg := Exhibits.Lifetime.conf Lifetime.current

/-- The node before anything, with a `max_commitment_age_secs` of 1000 in the log. -/
def s0 : PSt := { st := { sys := { world := { node := A, exposure := [] }, led := [] } }, log := { maxAge := 1000 } }

/-- The chain view the envelope grants carry. -/
def view : ChainView := (envAt 0 0).chain

def duressRequest : Grant := .op (.kernel (envAt 50 50) (.accept 10 true (Wall.sample 400) s1 es1))
def relayAt (raw nonce : Nat) : Grant := .envelope raw raw view 10 1 nonce raw

/-- Every goal in order, with service at each slot: the request, the relay, a driver attempt below
`T` and one at it, the fire pass, a peer's partial, the package test, the send, and a settle pass
whose view shows the Escape. The driver is served at every slot after that. -/
def good : Nat → Grant
  | 0 => duressRequest
  | 1 => relayAt 60 1
  | 2 => .driver 240 240
  | 3 => .driver 250 250
  | 4 => .op (.kernel (envAt 251 251) .firePass)
  | 5 => .op (.kernel (envAt 252 252) (.receivePartial (sighash esc1 0) 0 1 es1.id))
  | 6 => .op (.kernel (envAt 253 253) (.packageAccepted es1.id))
  | 7 => .op (.kernel (envAt 254 254) (.send es1.id))
  | 8 => .op (.kernel (envAt 255 255 [esc1]) (.settle esc1))
  | _ + 9 => .driver 300 300

def goodAt (t : Nat) : PSt := pRun conf s0 good t

/-- The five goals' bits: received, armed, latched, submitted, settled. -/
def subm (s : PSt) : Bool := s.node.cands.any fun c => c.id == es1.id && c.broadcast
def settl (s : PSt) : Bool := s.node.cands.any fun c => c.id == es1.id && c.settled
def bits (s : PSt) : List Bool :=
  [!s.guard.seen.isEmpty, s.node.armed, s.node.lockedDown, subm s, settl s]

/-- **The positive run, and the goals stand apart.** One composed history reaches each goal in turn:
an armed node not yet latched, a latched node with nothing submitted, a submitted Escape not settled.
The Escape is submitted after the latch, because `DUR-7` says "Lockdown blocks NEW signing and MUST
NOT block the in-flight Escape combine". The deciding relay is both received and arming here;
`f3_outlasts_expiry` has one received and not arming. -/
@[req "DUR-7"]
theorem goals_are_separate :
    (List.range 10).map (fun t => bits (goodAt t)) =
      [[false, false, false, false, false],
       [false, false, false, false, false],
       [true, true, false, false, false],
       [true, true, false, false, false],
       [true, true, true, false, false],
       [true, true, true, false, false],
       [true, true, true, false, false],
       [true, true, true, false, false],
       [true, true, true, true, false],
       [true, true, true, true, true]] := by
  decide +kernel

theorem good_service : (Profile.bounded 5).Holds fun u => isDriver (good u) := by
  intro t
  by_cases h : 9 ≤ t
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
    exact ⟨n + 9, Nat.le_refl _, by omega, rfl⟩
  · have ht : t < 9 := by omega
    match t, ht with
    | 0, _ => exact ⟨2, by omega, by omega, rfl⟩
    | 1, _ => exact ⟨2, by omega, by omega, rfl⟩
    | 2, _ => exact ⟨2, by omega, by omega, rfl⟩
    | 3, _ => exact ⟨3, by omega, by omega, rfl⟩
    | 4, _ => exact ⟨9, by omega, by omega, rfl⟩
    | 5, _ => exact ⟨9, by omega, by omega, rfl⟩
    | 6, _ => exact ⟨9, by omega, by omega, rfl⟩
    | 7, _ => exact ⟨9, by omega, by omega, rfl⟩
    | 8, _ => exact ⟨9, by omega, by omega, rfl⟩

/-- `Progress.latch_within`'s premises met: driver service within five slots, and the comparison true
at the one driver sample in the window from slot 3. Its conclusion is the run's: the latch by slot
9, and in fact at slot 4. -/
@[req "DUR-7"]
theorem bounded_service_latches : (goodAt 9).node.lockedDown = true := by
  refine latch_within (t0 := 3) (B := 5) good_service fun u hu hle => ?_
  match u, hu, hle with
  | 3, _, _ => decide +kernel
  | 4, _, _ => rfl
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, _ => rfl

/-- An envelope at every slot, each with its own nonce, stamped at its own sample. -/
def relays : Nat → Grant := fun u => relayAt (60 + u) (u + 1)

/-- The state after the request. -/
def accepted : PSt := pStep conf s0 duressRequest

/-- `Progress.received_within` and `Progress.armed_within` are inhabited: at `bounded 0` delivery,
over the run from the accepted request, the first slot's relay fits and decides. -/
@[req "DUR-5"]
theorem received_and_armed_inhabited :
    (∃ u, 0 ≤ u ∧ u ≤ 0 + 0 ∧ Received (pRun conf accepted relays (u + 1)) 1) ∧
      Armed (pRun conf accepted relays (0 + 0 + 1)) := by
  constructor
  · refine received_within (fun t => ⟨t, by omega, by omega, by simp [relays, relayAt, carries]⟩) ?_
    intro u _ hle
    have hu : u = 0 := by omega
    subst hu
    decide +kernel
  · refine armed_within (cid := 10) (t0 := 0) (B := 0)
      (fun t => ⟨t, by omega, by omega, by simp [relays, relayAt, relaysFor]⟩) ?_
    intro u _ hle
    have hu : u = 0 := by omega
    subst hu
    decide +kernel

/-- The state with the package accepted, and a send at every slot. -/
def packaged : PSt := goodAt 7
def sends (raw : Nat) : Nat → Grant := fun _ => .op (.kernel (envAt raw raw) (.send es1.id))

/-- `Progress.submitted_within` is inhabited inside the Escape's window. -/
@[req "DUR-29"]
theorem submitted_inhabited :
    ∃ u, 0 ≤ u ∧ u ≤ 0 + 0 ∧ Submitted (pRun conf packaged (sends 254) (u + 1)) es1.id := by
  refine submitted_within (fun t => ⟨t, by omega, by omega, by simp [sends, sendsFor]⟩) ?_
  intro u _ hle
  have hu : u = 0 := by omega
  subst hu
  decide +kernel

/-- The usable window closed. `combine_slack_secs` closes the Escape's window at 290, a send served
then and again later finds it closed: the service profile is met and the goal is not. -/
@[req "DUR-29"]
theorem send_after_window_closes :
    subm (pRun conf packaged (sends 300) 1) = false ∧
      subm (pRun conf packaged (sends 300) 2) = false ∧
      subm (pRun conf packaged (sends 254) 1) = true := by
  decide +kernel

/-- `Progress.settled_within` is inhabited: a view showing the Escape, and the candidate resident. -/
@[req "SPN-33"]
theorem settled_inhabited :
    ∃ u, 0 ≤ u ∧ u ≤ 0 + 0 ∧
      Settled (pRun conf (goodAt 8) (fun _ => .op (.kernel (envAt 255 255 [esc1]) (.settle esc1))) (u + 1)) esc1 := by
  refine settled_within (fun t => ⟨t, by omega, by omega, by simp [settlesFor]⟩) ?_
  intro u _ hle
  have hu : u = 0 := by omega
  subst hu
  decide +kernel

/-- Submission is not inclusion. The Escape was sent, and a settle pass over a view that does not
show it settles nothing: the node has no transition that puts a transaction in a block.
`Exhibits.Settlement.reorg_after_settlement` shows a settlement leaving the chain afterwards. -/
@[req "SPN-33"]
theorem submitted_is_not_included :
    bits (pStep conf (goodAt 8) (.op (.kernel (envAt 255 255) (.settle esc1)))) =
      [true, true, true, true, false] := by
  decide +kernel

/-! #### The driver apart from the store prune tick -/

/-- `NCH-40`'s store prune tick and `DUR-7`'s driver on the same node at the same sample. On the armed
node past `T`, the tick leaves the latch open and the driver sets it. On the accepted request past
its `D`, the tick retires the Carrier and the driver does not. -/
@[req "NCH-40"]
theorem prune_tick_is_not_the_driver :
    let armed := (goodAt 2).node
    let resident := accepted.node
    (tick Kernel.current (envAt 260 260) armed).lockedDown = false ∧
      (driverStep Kernel.current (envAt 260 260) armed).lockedDown = true ∧
      (tick Kernel.current (envAt 401 401) resident).carriers = [] ∧
      (driverStep Kernel.current (envAt 401 401) resident).carriers.length = 1 := by
  decide +kernel

/-! #### `F13` -/

/-- The history: the node armed, then a stream of refused requests holding the lock, each one with
the wall one second later, starting past `T`. -/
def armedAt : PSt := goodAt 2
def wallAfter (u : Nat) : Env := envAt (251 + u) (251 + u)
def stream : Nat → Grant := mint wallAfter (fun u => 1000 + u) (Wall.sample 400)
def f13Sched : Nat → Grant := fun u =>
  match u with
  | 0 => duressRequest
  | 1 => relayAt 60 1
  | n + 2 => stream n

theorem f13Sched_prefix : pRun conf s0 f13Sched 2 = armedAt := by decide +kernel

/-- **`F13` as an unbounded history under the existing model.** At every slot of an unending run, the
node is armed and past `T`, the driver's comparison holds at that slot's sample, the driver is never
granted the lock, and the latch stays open. The lock is unfair and `DUR-15` says "a post-wrench
coordinator holding the auth key can mint validly signed requests indefinitely". -/
@[req "DUR-15"]
theorem f13_starved_run (u : Nat) :
    let s := pRun conf armedAt stream u
    isDriver (stream u) = false ∧ s.node.armed = true ∧ s.node.lockedDown = false ∧
      driverDue conf.r (driverEnv s.log (251 + u) (251 + u)) s.node = true := by
  obtain ⟨hd, ha, hl, hT, _⟩ := f13_starved conf armedAt wallAfter (fun u => 1000 + u) (Wall.sample 400)
    (by decide +kernel) (by decide +kernel) u
  refine ⟨hd u, ha, hl, driverDue_of_wall rfl ha (τ := 250) (hT.trans (by decide +kernel)) (by omega)⟩

/-- The consequence stays bounded in that same history: from the world the first slot started from,
at every slot, a fire pass queues no hot partial. No premise on the schedule. -/
@[req "DUR-15"]
theorem f13_delayed_frozen (u : Nat) (env : Env) :
    ∀ eff ∈ (step conf.r env (pRun conf s0 f13Sched (2 + u)).st.sys.world .firePass).2,
      ∀ m i cid, eff ≠ .queuePartial m i true cid := by
  refine delayed_node_frozen conf s0 f13Sched (.init A ⟨rfl, rfl, rfl⟩) (2 + u) env ?_
  have hs : (fun v => f13Sched (2 + v)) = stream := by
    funext v
    rw [Nat.add_comm]
    rfl
  rw [pRun_shift, f13Sched_prefix, hs]
  exact (f13_starved conf armedAt wallAfter (fun u => 1000 + u) (Wall.sample 400)
    (by decide +kernel) (by decide +kernel) u).2.1

/-- **`F13` under eventual service, for any postponement.** A driver served from slot `L` on is
eventual and bounded by `L`, and has not latched at `L`, whatever `L`. -/
@[req "DUR-15"]
theorem f13_postponed_run (L : Nat) :
    (pRun conf armedAt (fun u => if u < L then stream u else .driver 300 300) L).node.lockedDown = false :=
  (f13_postponed conf armedAt wallAfter (fun u => 1000 + u) (Wall.sample 400) (by decide +kernel)
    (by decide +kernel) L 300 300).2.2

/-- The other premise of `latch_within`. The driver is served every other slot and samples 249, below
`T`. Between its slots a store prune tick samples 260, past `T`, so the wall steps back each time. At
that later sample the comparison holds, at every slot, and the ratchet never reads it: service is
bounded, and the node never latches. -/
@[req "DUR-7"]
theorem alternating_samples_never_latch (u : Nat) :
    let sched : Nat → Grant := fun v =>
      if v % 2 = 0 then .driver 249 249 else .op (.kernel (envAt 260 260) .tick)
    (Profile.bounded 1).Holds (fun v => isDriver (sched v)) ∧
      driverDue conf.r (driverEnv (pRun conf armedAt sched u).log 260 260) (pRun conf armedAt sched u).node = true ∧
      (pRun conf armedAt sched u).node.lockedDown = false := by
  intro sched
  have hb : (Profile.bounded 1).Holds (fun v => isDriver (sched v)) := fun t => by
    by_cases h : t % 2 = 0
    · exact ⟨t, by omega, by omega, by simp [sched, h, isDriver]⟩
    · exact ⟨t + 1, by omega, by omega, by
        have h' : (t + 1) % 2 = 0 := by omega
        simp [sched, h', isDriver]⟩
  have hbelow : driverDue conf.r (driverEnv armedAt.log 249 249) armedAt.node = false := by decide +kernel
  have hpast : driverDue conf.r (driverEnv armedAt.log 260 260) armedAt.node = true := by decide +kernel
  have hinv : ∀ v, (pRun conf armedAt sched v).node.armed = armedAt.node.armed ∧
      (pRun conf armedAt sched v).node.ratchet = armedAt.node.ratchet ∧
      (pRun conf armedAt sched v).node.T = armedAt.node.T ∧
      (pRun conf armedAt sched v).node.lockedDown = false ∧
      (pRun conf armedAt sched v).log = armedAt.log := by
    intro v
    induction v with
    | zero => exact ⟨rfl, rfl, rfl, by decide +kernel, rfl⟩
    | succ v ih =>
      obtain ⟨ha, hr, hT, hl, hlog⟩ := ih
      show (pStep conf (pRun conf armedAt sched v) (sched v)).node.armed = _ ∧
        (pStep conf (pRun conf armedAt sched v) (sched v)).node.ratchet = _ ∧
        (pStep conf (pRun conf armedAt sched v) (sched v)).node.T = _ ∧
        (pStep conf (pRun conf armedAt sched v) (sched v)).node.lockedDown = false ∧
        (pStep conf (pRun conf armedAt sched v) (sched v)).log = _
      by_cases h : v % 2 = 0
      · have hg : sched v = .driver 249 249 := by simp [sched, h]
        rw [hg]
        have hd : driverDue conf.r (driverEnv (pRun conf armedAt sched v).log 249 249)
            (pRun conf armedAt sched v).st.sys.world.node = false := by
          rw [hlog]
          exact (driverDue_congr ha hr hT).trans hbelow
        simp only [pStep, PSt.node, driverStep, hd, Bool.false_eq_true, if_false]
        exact ⟨ha, hr, hT, hl, hlog⟩
      · have hg : sched v = .op (.kernel (envAt 260 260) .tick) := by simp [sched, h]
        rw [hg]
        have hw : (pStep conf (pRun conf armedAt sched v) (.op (.kernel (envAt 260 260) .tick))).node =
            tick conf.r (envAt 260 260) (pRun conf armedAt sched v).node := by
          show ((Ledger.sysStep conf.lg conf.cfg conf.r (envAt 260 260) (pRun conf armedAt sched v).st.sys
            .tick).1.world).node = _
          rw [(FedSilence.sysStep_kernel _ _ _ _ _ _).1]
          rfl
        rw [hw]
        exact ⟨ha, hr, hT, hl, hlog⟩
  obtain ⟨ha, hr, hT, hl, hlog⟩ := hinv u
  refine ⟨hb, ?_, hl⟩
  rw [hlog]
  exact (driverDue_congr ha hr hT).trans hpast

/-- A later hot acceptance on the armed node, at wall 260. -/
def readS : PSt := pStep conf armedAt (.op (.kernel (envAt 260 260) (.accept 20 false (Wall.sample 400) s2 es2)))

/-- The ratchet's reading. A hot acceptance at wall 260 advances the ratchet past `T`, after which a
wall back at 249 still reaches it, so `Progress.latch_within_of_read` needs no premise on the driver's
samples. Without the reading the same driver sample does not reach `T`
(`alternating_samples_never_latch`). -/
@[req "DUR-7"]
theorem read_past_survives_backward_wall :
    ReadPast readS.node ∧ (pRun conf readS (fun _ => .driver 249 249) (0 + 0 + 1)).node.lockedDown = true := by
  have hr : ReadPast readS.node := by decide +kernel
  exact ⟨hr, latch_within_of_read (c := conf) (s0 := readS) (t0 := 0) (B := 0) rfl rfl
    (fun t => ⟨t, by omega, by omega, rfl⟩) hr⟩

/-! #### `F3` -/

/-- **`F3` as an unbounded history under the existing model.** For every `L`, the excursion to
`L + 301`, then an honest relay at every slot of the next `L` seconds: delivery at `bounded 0`, and the
accepted duress request never arms. Delivery was never the problem. -/
@[req "NCH-38"]
theorem f3_no_arming_run (L u : Nat) (hu : u ≤ L + 1) :
    (pRun conf accepted (honestStream (L + 301) (fun v => v) view 10 1) u).node.armed = false := by
  have h := ((f3_blackhole conf accepted (fun v => v) view 10 1 L (L + 301) (by
    show L + 300 < L + 301
    omega)).2 u hu).1
  simp only [PSt.node, h]
  decide +kernel

/-- `NCH-38`: "A stale sender recovers only when elapsed real time brings its timestamps back inside
the 300-second window before `E` and `D`". An excursion to 650 latches the guard: the relay at 349 is
stale, the relay at 350 is taken, and the node arms below `E = 400`. -/
@[req "NCH-38"]
theorem f3_recovers_before_expiry :
    let g := (pStep conf accepted (.envelope 650 60 view 10 1 1 60))
    (pStep conf g (relayAt 349 2)).node.armed = false ∧
      (pStep conf g (relayAt 350 3)).node.armed = true := by
  decide +kernel

/-- And an excursion to 1000 outlasts the Carrier: the guard takes the relay at 700, and the Carrier's
`E` has passed, so nothing arms. The window was never open for this request. -/
@[req "NCH-38"]
theorem f3_outlasts_expiry :
    let g := (pStep conf accepted (.envelope 1000 60 view 10 1 1 60))
    (pStep conf g (relayAt 699 2)).guard.seen.isEmpty = true ∧
      (pStep conf g (relayAt 700 3)).guard.seen.isEmpty = false ∧
      (pStep conf g (relayAt 700 3)).node.armed = false := by
  decide +kernel

/-! #### `F4` -/

/-- The request's own log entry with its `D`, then a Refresh with a later expiry, wall-only. -/
def logged : List Grant := [.logAccept 50 50 1 400 true, .logAccept 50 50 2 500 false]
/-- An accept at a wall that has jumped to 1000: the HotClock has moved five seconds, so the
Carrier's entry stays live and only the Refresh is pruned. -/
def excursion : Grant := .logAccept 1000 55 3 1100 false

def playAll (s : PSt) : List Grant → PSt
  | [] => s
  | g :: gs => playAll (pStep conf s g) gs

def afterExcursion : PSt := playAll accepted (logged ++ [excursion])

/-- **`F4` over the log.** `SPN-12`'s sentence, run: the high-water latches at the Refresh's 500, above
the Carrier's `E = 400`, the Carrier's entry stays live, and the Refresh's entry is gone. -/
@[req "SPN-12"]
theorem f4_latches_past_live_carrier :
    afterExcursion.log.hw = 500 ∧
      afterExcursion.log.entries.map (·.nonce) = [3, 1] ∧
      afterExcursion.node.carriers.map (·.E) = [Wall.sample 400] := by
  decide +kernel

/-- **`F4` as an unbounded history under the existing model.** After the latch the clock is corrected
and the relays come at every slot, each sample whatever it is: the kernel's world does not move and
the accepted duress request never arms, for as many slots as the schedule runs. -/
@[req "NCH-36"]
theorem f4_no_arming_run (raw mono : Nat → Nat) (u : Nat) :
    (pRun conf afterExcursion (relayStream raw mono view 10 1) u).node.armed = false := by
  obtain ⟨_, h⟩ := f4_no_arming conf afterExcursion raw mono view 10 1 400 _ rfl rfl (by decide +kernel)
  simp only [PSt.node, (h u).1]
  decide +kernel

/-- The failing sibling. With the same steps and no excursion, the same relay at the same corrected
sample arms the node: the latch is what refused it. -/
@[req "NCH-36"]
theorem f4_sibling_without_excursion :
    (pStep conf (playAll accepted logged) (relayAt 60 1)).node.armed = true ∧
      (pStep conf afterExcursion (relayAt 60 1)).node.armed = false := by
  decide +kernel

/-- `F4`'s unbounded form at the log, run: an age bound of 1000 and excursions to 5000 and 6000 leave
the high-water at 6000. Every expiry is refused at every raw sample up to 5000, and one sample later
the window opens again (`window_open_below_latch`). -/
@[req "SPN-12"]
theorem f4_log_outage_run :
    let l : NonceLog := (({ maxAge := 1000 } : NonceLog).accept 5000 50 0 6000 false).accept 6000 50 1 7000 false
    l.hw = 6000 ∧ l.windowOk 5000 6000 = false ∧ l.windowOk 5000 6001 = false ∧ l.windowOk 5001 6001 = true := by
  decide +kernel

end BtcPolicy.Exhibits.Progress

namespace BtcPolicy.Exhibits.Feasibility
open BtcPolicy.Feasibility
open BtcPolicy.Coverage (Coin Outpoint)

/-! ### Fast-exit feasibility

Research task `bps-uaer.17`, over `F1`, `F2` and `F48`. Every state below is a `Sweep.Backend` instant
with hand-chosen values; `Coverage.current`, `Coverage.currentExternal` and `Package.current` are the
guards. `Limits` here is 2-of-3 with one `P2WSH` output, the primary and the Escape on the wire. Its
wire figures are assumptions of these exhibits, and `escape_feerate_floor` is 1 unless a state says
otherwise. -/

/-- The assumed sizes: a one-output Escape, a primary and an Escape, 400 bytes per input per PSBT. -/
def lim : Limits :=
  { t := 2, n := 3, outBytes := 44, psbts := 2, shell := 1024, perInput := 400, envelope := 2048,
    msg := 1048576 }

def book (value : Outpoint → Nat) : Sweep.Book :=
  { value, outputs := fun _ => [], delivered := fun _ => 0 }

/-- Each coin its own funding transaction unless a state says otherwise, none of them resident. -/
def funding (o : Outpoint) : Nat := 10000 + o

def cfgOf (value : Outpoint → Nat) (creator : Package.Creator := funding) : Sweep.Cfg :=
  { pct := Coverage.floorPct, keys := [1, 2, 3, 4], book := book value, creator,
    denominator := Coverage.current, external := Coverage.currentExternal, ancestry := Package.current }

def instant (confirmed : List Coin) (mempool : Package.MempoolRead := [])
    (pending : List (Nat × Coin) := []) : Sweep.Backend :=
  { tip := ⟨5, 105⟩, sequence := 1, confirmed, mempool, pending }

/-- A small parent. -/
def plain : Parent := ⟨250, 0⟩
/-- A parent near the consensus limit, nearly all witness (`F1`'s "consensus-valid very large
parent"). -/
def huge : Parent := ⟨1000, 3980000⟩
/-- A parent over twice the body cap, inside the domain. -/
def over2 : Parent := ⟨1000, 2100000⟩

def refusal : Except Refusal Request → Option Refusal
  | .error e => some e
  | .ok _ => none

theorem ok_of_toOption {x : Except Refusal Request} {q : Request} (h : x.toOption = some q) :
    x = .ok q := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok a =>
    simp only [Except.toOption, Option.some.injEq] at h
    rw [h]

def mk (confirmed : List Coin) (value : Outpoint → Nat) (parentOf : Nat → Option Parent)
    (floor : Nat := 1) (creator : Package.Creator := funding) : Vault :=
  { cfg := cfgOf value creator, A := [], b := instant confirmed, parentOf, floor }

/-! #### A feasible state -/

def smallCoins : List Coin := [(1, 60000), (2, 30000), (3, 10000)]
def smallVault : Vault :=
  mk smallCoins (fun o => if o == 1 then 60000 else if o == 2 then 30000 else 10000)
    fun _ => some plain

/-- **A feasible state with its constructed request.** The composer spends every coin and what it
builds validates, reached both by the check and by `compose_bounded`'s premises. -/
@[req "OPR-33"]
theorem feasible_constructed :
    (composeEvery lim 9 smallVault).toOption = some (everyRequest lim 9 smallVault) ∧
      (everyRequest lim 9 smallVault).inputs = [1, 2, 3] ∧
      smallVault.bounded lim .ignore (everyRequest lim 9 smallVault) = true ∧
      smallVault.bounded lim .verify (everyRequest lim 9 smallVault) = true ∧
      smallVault.bounded lim .refuse (everyRequest lim 9 smallVault) = false := by
  decide +kernel

/-- `compose_bounded`'s premises hold at that state, so the theorem has an inhabitant. -/
@[req "OPR-33"]
theorem compose_bounded_inhabited :
    smallVault.bounded lim .ignore (everyRequest lim 9 smallVault) = true :=
  compose_bounded .ignore (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    (ok_of_toOption (x := composeEvery lim 9 smallVault) (q := everyRequest lim 9 smallVault)
      (by decide +kernel))

/-- `feasible_iff_best` at that state with its count bound discharged: 620 inputs is `OPR-35`'s
figure at this shape. One coin reaches the share, two fewer than the composer spends. -/
@[req "DUR-24"]
theorem closed_form_small :
    (∃ q, q.carried = false ∧ smallVault.bounded lim .ignore q = true) :=
  (feasible_iff_best smallVault lim .ignore false (fun _ => true) 620 rfl rfl (by decide)
    (by decide) (by decide) (by decide)
    (countOnly_of_slack smallVault lim .ignore 620 250 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
      (by decide +kernel) (by decide))).2 ⟨1, by decide, by decide +kernel⟩

/-- The count bound itself: at this shape 620 inputs fit `OPR-35`'s vsize bound and 621 do not, and
at 8-of-15 the same bound stops at 268. -/
@[req "OPR-35"]
theorem vsize_capacity :
    vsizeOf lim 620 ≤ vsizeCap ∧ vsizeCap < vsizeOf lim 621 ∧
      vsizeOf { lim with t := 8, n := 15 } 268 ≤ vsizeCap ∧
      vsizeCap < vsizeOf { lim with t := 8, n := 15 } 269 := by
  decide +kernel

/-- A full ladder on the wire lowers the count under these sizes: with five PSBTs at 400 bytes the
body cap binds before the vsize bound does. -/
@[req "API-4"]
theorem ladder_lowers_capacity :
    let full : Limits := { lim with psbts := 5 }
    (smallVault.wire full (List.range 524) false ≤ bodyCap) = false ∧
      (smallVault.wire lim (List.range 620) false ≤ bodyCap) = true := by
  decide +kernel

/-! #### `F1`: consolidation and fragments -/

/-- One large coin and 621 dust coins an outsider sent. -/
def dustCoins : List Coin := (0, 1000000000) :: (List.range 621).map fun i => (i + 1, 546)
def dustVault : Vault := mk dustCoins (fun o => if o == 0 then 1000000000 else 546) fun _ => some plain

/-- **The composer's refusal is not infeasibility.** Dust alone stops `OPR-33`'s composer, which has
"no coin selection and no omission"; one input covers the vault, and the dust stays in its
denominator. -/
@[req "OPR-33"]
theorem dust_stops_composer_only :
    refusal (composeEvery lim 9 dustVault) = some .vsizeOver ∧
      dustVault.bounded lim .ignore (requestOver dustVault lim 9 [0]) = true ∧
      dustVault.denominator (requestOver dustVault lim 9 [0]) = dustVault.total ∧
      dustVault.total = 1000000000 + 621 * 546 := by
  decide +kernel

/-- `n` coins of 100 000. -/
def even (n : Nat) : List Coin := (List.range n).map fun i => (i, 100000)
def evenVault (n : Nat) : Vault := mk (even n) (fun _ => 100000) fun _ => some plain

theorem evenVault_read (n : Nat) : (evenVault n).read = even n := by
  simp [Vault.read, Vault.snap, Sweep.snapshot, Sweep.additions, evenVault, mk, instant,
    Sweep.spentInMempool]

/-- **`F1`, fragmentation: no bounded request exists.** Every coin equal, and more of them than `620`
inputs can reach at `MAN-9`'s floor: `fragmented_infeasible` over every request, not a search. The
state is admissible: canonical, values agreeing, every parent small. -/
@[req "DUR-24"]
theorem fragments_infeasible (rule : ParentRule) (q : Request) :
    (evenVault 1216).bounded lim rule q = false := by
  have hv : ∀ c ∈ (evenVault 1216).read, (evenVault 1216).cfg.book.value c.1 = c.2 := by
    intro c hc
    rw [evenVault_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rfl
  have hle : ∀ c ∈ (evenVault 1216).read, c.2 ≤ 100000 := by
    intro c hc
    rw [evenVault_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    exact Nat.le_refl _
  exact Vault.fragmented_infeasible rfl rfl (by decide +kernel) hv hle
    (fun q h => Vault.inputs_le_of_vsize (N := 620) (by decide +kernel) h) (by decide +kernel) q

/-- Below that count the same vault has a request, by `feasible_iff_best` at 620 inputs with the fee
at the floor paid: 620 of 1 213 coins cover. The two figures bracket the threshold at this floor. -/
@[req "DUR-24"]
theorem fragments_feasible_below :
    ∃ q, q.carried = false ∧ (evenVault 1213).bounded lim .ignore q = true := by
  have hrd := evenVault_read 1213
  have hs : ascending ((evenVault 1213).read.map (·.1)) = true := by rw [hrd]; decide +kernel
  have hv : ∀ c ∈ (evenVault 1213).read, (evenVault 1213).cfg.book.value c.1 = c.2 := by
    intro c hc
    rw [hrd] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rfl
  have hsum : Coverage.sumValues (even 620) = 62000000 := by decide +kernel
  have hsub : (even 620).Sublist (even 1213) := by
    have : even 620 = (even 1213).take 620 := by decide +kernel
    rw [this]
    exact List.take_sublist _ _
  have hbest : 62000000 ≤ best 620 ((evenVault 1213).read.filter fun _ => true) := by
    have hft : (even 1213).filter (fun _ => true) = even 1213 := List.filter_eq_self.2 fun _ _ => rfl
    rw [hrd, hft]
    exact hsum ▸ best_ge _ _ 620 hsub (by decide +kernel)
  refine (feasible_iff_best (evenVault 1213) lim .ignore false (fun _ => true) 620 rfl rfl hs hv
    (by rw [Vault.total, hrd]; decide +kernel) (by decide)
    (countOnly_of_slack _ lim .ignore 620 250 (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun _ _ => rfl) (fun _ _ => Nat.le_of_eq rfl)
      (by decide +kernel) (fun _ _ => rfl))).2 ⟨620, by decide, ?_⟩
  have hf : (evenVault 1213).floor * vsizeOf lim 620 = vsizeOf lim 620 := Nat.one_mul _
  have hvs : vsizeOf lim 620 ≤ 99900 := by decide +kernel
  have ht : (evenVault 1213).total * (evenVault 1213).cfg.pct = 6186300000 := by
    rw [Vault.total, hrd]
    decide +kernel
  rw [ht, hf]
  omega

/-! #### `F1`: a large parent -/

/-- Sixteen outputs of one parent near the consensus limit, equal in value. -/
def toxicCoins : List Coin := (List.range 16).map fun i => (i, 100000)
def toxicVault : Vault :=
  mk toxicCoins (fun _ => 100000) (fun _ => some huge) (creator := fun _ => 7)

theorem toxic_read : toxicVault.read = toxicCoins := by decide

/-- The parents are inside the assumed domain, and the large one's non-witness bytes hold its sixteen
`P2WSH` outputs at 43 bytes each. -/
@[req "OPR-35"]
theorem huge_in_domain : huge.inDomain = true ∧ over2.inDomain = true ∧ 16 * 43 ≤ huge.base := by decide

/-- **`F1`, large parent: no bounded request exists.** Nine inputs from this parent project past
`OPR-35`'s 64 MiB, eight carry half the value, and `MAN-9`'s floor needs more than half. -/
@[req "OPR-35"]
theorem toxic_infeasible (rule : ParentRule) (q : Request) :
    toxicVault.bounded lim rule q = false := by
  have hv : ∀ c ∈ toxicVault.read, toxicVault.cfg.book.value c.1 = c.2 := by
    intro c hc
    rw [toxic_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rfl
  have hle : ∀ c ∈ toxicVault.read, c.2 ≤ 100000 := by
    intro c hc
    rw [toxic_read] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    exact Nat.le_refl _
  have hm : ∀ c ∈ toxicVault.read, 3981000 ≤ toxicVault.parentBytes c.1 := fun _ _ =>
    Nat.le_of_eq (show 3981000 = _ from rfl)
  exact Vault.fragmented_infeasible rfl rfl (by decide) hv hle
    (fun q h => Vault.inputs_le_of_retained (N := 8) (m := 3981000) hm (by decide +kernel) h)
    (by decide +kernel) q

/-- That refutation is the composer's and the signer's bound, not the node's. A node reading no
parent takes a request of nine of these coins; `OPR-35` refuses to retain them, and the composer
stops at the same bound. -/
@[req "OPR-35"]
theorem toxic_node_would_take :
    toxicVault.nodeOk lim .ignore (requestOver toxicVault lim 9 (List.range 9)) = true ∧
      toxicVault.boundOk lim (List.range 9) = false ∧
      toxicVault.boundOk lim (List.range 8) = true ∧
      refusal (composeEvery lim 9 toxicVault) = some .retainedOver := by
  decide +kernel

/-- One such parent paying the vault once breaks nothing with the wire stripped: inside the domain
eight inputs always fit (`Vault.eight_inputs_always_retained`), so `F1`'s large parent needs
multiplicity or a wire that carries it. -/
@[req "OPR-35"]
theorem one_large_parent_composes :
    let v := mk [(0, 100000)] (fun _ => 100000) (fun _ => some huge)
    (composeEvery lim 9 v).toOption = some (everyRequest lim 9 v) := by
  decide +kernel

/-! #### `F2`: vault-authorized unconfirmed value -/

/-- A prior vault spend, 500, is resident over coin 1 and pays 90 000 back to the vault as coin 5;
coin 0 holds the rest. -/
def priorCreator : Package.Creator := fun o => if o == 5 then 500 else funding o
def priorVault : Vault :=
  { cfg := cfgOf (fun o => if o == 0 then 10000 else if o == 1 then 95000 else 90000) priorCreator,
    A := [500], b := instant [(0, 10000), (1, 95000)] [(500, [1])] [(500, (5, 90000))],
    parentOf := fun _ => some plain, floor := 1 }

/-- **`F2`, the gap: a request exists that the composer cannot build.** The node takes a request
over the unconfirmed change, `WTC-24` admitting its one authorized ancestor. `OPR-34` refuses the
whole inventory for coin 1 ("A coin mempool-spent by a prior vault spend is the common case"). -/
@[req "OPR-39"]
theorem prior_spend_composer_refuses :
    priorVault.read = [(0, 10000), (5, 90000)] ∧
      priorVault.bounded lim .ignore (requestOver priorVault lim 9 [0, 5]) = true ∧
      refusal (composeEvery lim 9 priorVault) = some (.mempoolSpent 1) := by
  decide +kernel

/-- And composing over the remainder would not help, the reason `OPR-34` gives: "Composing over the
remainder yields an under-covered Escape." No request over confirmed coins alone covers this state. -/
@[req "OPR-34"]
theorem confirmed_only_undercovers (q : Request) (h : ∀ o ∈ q.inputs, o = 0) :
    priorVault.nodeOk lim .ignore q = false := by
  refine Vault.not_nodeOk_of_usable (usable := fun c => c.1 == 0) rfl rfl (by decide) (by decide)
    (by decide +kernel) ?_
  intro c hc
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc
  simp [h o ho]

/-- A chain of `k` residents, each spending the last one's change; only the tail's is unspent. -/
def chainMempool (k : Nat) : Package.MempoolRead :=
  (List.range k).map fun i => (i + 1, [if i == 0 then 1000 else i])
def chainPending (k : Nat) : List (Nat × Coin) :=
  (List.range k).map fun i => (i + 1, (i + 1, 90000))
def chainCreator (k : Nat) : Package.Creator := fun o => if 1 ≤ o && o ≤ k then o else funding o
def chainVault (k : Nat) : Vault :=
  { cfg := cfgOf (fun o => if o == 0 then 10000 else if o == 1000 then 90000 else 90000) (chainCreator k),
    A := (List.range k).map (· + 1),
    b := instant [(0, 10000), (1000, 90000)] (chainMempool k) (chainPending k),
    parentOf := fun _ => some plain, floor := 1 }

/-- **`F2`, the deep chain: no bounded request exists.** The value sits on the tail of 25 residents,
all vault-authorized. The tail itself has 24 ancestors, which `WTC-24` calls "one below Bitcoin
Core's default ancestor limit", so a default mempool can hold it; a candidate spending it has 25.
No selection goes around it (`deep_coin_excluded`), coin 0 alone does not cover, and nothing leaves
the denominator. Here the node's own rule refuses, under every `F48` reading. -/
@[req "WTC-24"]
theorem deep_chain_infeasible (rule : ParentRule) (q : Request) :
    (chainVault 25).nodeOk lim rule q = false := by
  have hrd : (chainVault 25).read = [(0, 10000), (25, 90000)] := by decide +kernel
  by_cases hin : 25 ∈ q.inputs
  · have : (chainVault 25).ancestryOk q.inputs = false :=
      deep_coin_excluded hin (by decide +kernel)
    simp [Vault.nodeOk, this]
  · refine Vault.not_nodeOk_of_usable (usable := fun c => c.1 != 25) rfl rfl
      (by decide +kernel) (by rw [hrd]; decide +kernel) (by decide +kernel) ?_
    intro c hc
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc
    have : o ≠ 25 := fun he => hin (he ▸ ho)
    simpa using this

/-- One link shorter the same state has a request over the tail: 24 ancestors pass. -/
@[req "WTC-24"]
theorem shallow_chain_feasible :
    (chainVault 24).read = [(0, 10000), (24, 90000)] ∧
      (chainVault 24).bounded lim .ignore (requestOver (chainVault 24) lim 9 [0, 24]) = true := by
  decide +kernel

/-! #### `F48`: inputs without full previous transactions -/

/-- Coin 0 holds most of the value and its parent is more than a body cap's worth. -/
def largeVault : Vault :=
  mk [(0, 90000), (1, 10000)] (fun o => if o == 0 then 90000 else 10000)
    fun t => if t == funding 0 then some over2 else some plain

/-- **`F48` moves the verdict.** At one state, under `ignore` and `verify` a stripped request is
bounded. Under `refuse` a request must carry its parents, the parent then exceeds `API-4`'s body cap,
and the other coin does not cover: no request. `F48` says the rule "matters for `F1`'s size bounds";
this is that, and it answers nothing. -/
@[req "API-4"]
theorem f48_moves_the_verdict (q : Request) :
    largeVault.bounded lim .ignore (requestOver largeVault lim 9 [0, 1]) = true ∧
      largeVault.bounded lim .verify (requestOver largeVault lim 9 [0, 1]) = true ∧
      largeVault.nodeOk lim .refuse q = false := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  cases hc : q.carried with
  | false => simp [Vault.nodeOk, Vault.wireOk, hc]
  | true =>
    by_cases hin : 0 ∈ q.inputs
    · have : largeVault.wireOk lim .refuse q.inputs true = false :=
        Vault.carried_parent_over_body hin (by decide +kernel)
      simp [Vault.nodeOk, hc, this]
    · refine Vault.not_nodeOk_of_usable (usable := fun c => c.1 != 0) rfl rfl (by decide)
        (by decide) (by decide +kernel) ?_
      intro c hc'
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc'
      have : o ≠ 0 := fun he => hin (he ▸ ho)
      simpa using this

/-- Coin 0's full previous transaction cannot be obtained. -/
def missingVault : Vault :=
  mk [(0, 90000), (1, 10000)] (fun o => if o == 0 then 90000 else 10000)
    fun t => if t == funding 0 then none else some plain

/-- **`F48`, no full previous transaction: no bounded request exists.** `CHN-22` makes the coin
unsignable and the composer refuses. The other coin does not cover, and the coin stays in the
denominator. A node that reads no parent would take a request over it, had one been signed: signing
needs the parent the wire strips, which is where the finding and `CHN-22` meet. -/
@[req "CHN-22"]
theorem missing_parent_infeasible (rule : ParentRule) (q : Request) :
    missingVault.bounded lim rule q = false ∧
      missingVault.nodeOk lim .ignore (requestOver missingVault lim 9 [0, 1]) = true ∧
      refusal (composeEvery lim 9 missingVault) = some (.noParent 0) := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  refine Vault.unreachable_infeasible (usable := fun c => c.1 != 0) rfl rfl (by decide) (by decide)
    (fun q hq c hc => ?_) (by decide +kernel) q
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hc
  have hall : (q.inputs.all fun o => (missingVault.parent o).isSome) = true := by
    simp only [Vault.bounded, Vault.boundOk, Bool.and_eq_true] at hq
    exact hq.2.1.2
  have hsome := List.all_eq_true.1 hall o ho
  have : o ≠ 0 := by
    rintro rfl
    exact absurd hsome (by decide)
  simpa using this

/-- Every state the refutations and comparisons above name is admissible. -/
@[req "MAN-9"]
theorem states_admissible :
    smallVault.admissible = true ∧ dustVault.admissible = true ∧ (evenVault 1216).admissible = true ∧
      (evenVault 1213).admissible = true ∧ toxicVault.admissible = true ∧ priorVault.admissible = true ∧
      (chainVault 25).admissible = true ∧ (chainVault 24).admissible = true ∧
      largeVault.admissible = true ∧ missingVault.admissible = true := by
  decide +kernel

/-! #### The denominator is not the repair -/

def halves : Vault := mk [(0, 50000), (1, 50000)] (fun _ => 50000) fun _ => some plain

/-- **Omitting a coin from the denominator is what `MAN-9`'s floor forbids.** Each coin alone covers
a denominator that omits the other, so two input-disjoint Escapes both pass. Against `DUR-22`'s value
neither does. An omitted coin stays counted, and that is why infeasibility above is not repaired by
narrowing what is protected. -/
@[req "DUR-22"]
theorem omitting_admits_two :
    let d := fun o => (halves.escape (requestOver halves lim 9 [o])).delivered
    Coverage.covers (d 0) 50000 Coverage.floorPct = true ∧
      Coverage.covers (d 1) 50000 Coverage.floorPct = true ∧ d 0 + d 1 ≤ 100000 ∧
      halves.denominator (requestOver halves lim 9 [0]) = 100000 ∧
      halves.denominator (requestOver halves lim 9 [1]) = 100000 ∧
      halves.coverOk (requestOver halves lim 9 [0]) = false ∧
      halves.coverOk (requestOver halves lim 9 [1]) = false := by
  decide +kernel

/-! #### Bounded-selection ideas, compared -/

/-- Dust before the large coin: prefix selection misses it, largest-first finds it. -/
def lateCoin : Vault :=
  mk [(0, 546), (1, 546), (2, 546), (999, 1000000000)]
    (fun o => if o == 999 then 1000000000 else 546) fun _ => some plain

/-- The largest coin has no parent: largest-first picks it and stops, and a request exists. -/
def largeNoParent : Vault :=
  mk [(0, 50000), (1, 30000), (2, 30000)] (fun o => if o == 0 then 50000 else 30000)
    fun t => if t == funding 0 then none else some plain

/-- **No idea here dominates, and none repairs an infeasible state.** Spending every coin fails where
prefix selection works (`dustVault`); prefix fails where largest-first works (`lateCoin`); largest-first
fails where a third selection works (`largeNoParent`), which `F1`'s "distinguish an unsupported toxic
fragment from insufficient funds" also asks. On `fragments_infeasible` and `toxic_infeasible` every
selection fails, being a request. Nothing here selects a mechanism. -/
@[req "OPR-33"]
theorem selection_ideas_compared :
    refusal (composeEvery lim 9 dustVault) = some .vsizeOver ∧
      dustVault.bounded lim .ignore (byPrefix dustVault lim 9 2) = true ∧
      lateCoin.bounded lim .ignore (byPrefix lateCoin lim 9 2) = false ∧
      lateCoin.bounded lim .ignore (byLargest lateCoin lim 9 2) = true ∧
      largeNoParent.bounded lim .ignore (byLargest largeNoParent lim 9 2) = false ∧
      largeNoParent.bounded lim .ignore (requestOver largeNoParent lim 9 [1, 2]) = true := by
  decide +kernel

/-! #### On the composed sweep -/

section Run
open BtcPolicy.Sweep BtcPolicy.Sweep.Cases
open BtcPolicy.Federation.Cases (honest)

/-- The sweep fixture's book with coin 9 given its value, and its guards as they stand. -/
def runBook : Book :=
  { Cases.book with value := fun o => if o == 9 then 1000 else Cases.book.value o }
def runCfg : Cfg :=
  { Cases.cfg Coverage.current Coverage.currentExternal Package.current with book := runBook }

/-- **The request the composed sweep assembles validates.** `Exhibits.Sweep.successful_sweep`'s Escape
over `Sweep.Cases.vault`, read as a request: same inputs, its fee the difference it pays, no feerate
floor since the fixture's values are too small to carry one. -/
@[req "DUR-24"]
theorem swept_request_validates :
    let v : Vault := { cfg := Exhibits.Sweep.cfgNow, A := [], b := vault, parentOf := fun _ => some plain,
                       floor := 0 }
    let q : Request := { txid := Kernel.RegistrationCases.txE.id, inputs := Kernel.RegistrationCases.txE.inputs, fee := 10 }
    v.bounded lim .ignore q = true ∧ (v.escape q).delivered = Cases.book.delivered Kernel.RegistrationCases.txE.id := by
  decide +kernel

/-- **Armed, fast exit unavailable, and nothing submitted.** At an instant where one Escape cannot
reach its share (`vaultLarge`, its third coin in no input), both nodes arm, the hot spend is frozen
and the partials are delivered. That registered Escape's assembly is refused and the send submits
nothing. Another request over all three coins would pass at this read: this run is one Escape's
failure, not a state with no request. `F1`: "Funds remain under vault and Recovery authority; what is lost is the
fast exit." -/
@[req "DUR-24"]
theorem armed_no_fast_exit :
    let ss := delivered ++ [.observe 1 vaultLarge]
    let p := record Kernel.current [] (start vaultLarge) ss
    let n := (p.2.fed.worlds 1).node
    legal runCfg Kernel.current honest [] (start vaultLarge) ss = true ∧
      n.armed = true ∧ ((p.2.fed.worlds 2).node).armed = true ∧
      n.cands.any (fun c => c.id == Kernel.RegistrationCases.c1.id && c.frozen) = true ∧
      covered runCfg (authorizedAt p.2 p.1 1) n vaultLarge Kernel.RegistrationCases.e1 = false ∧
      admits runCfg honest p.2 p.1 (assemble 1 Kernel.RegistrationCases.e1.id) = false ∧
      submits Kernel.current p.2 (sendAt 1 Kernel.RegistrationCases.e1.id) = [] := by
  decide

/-- The same verdict from the theorem, at that node's own selected set: the delivery is within what
the Escape's own inputs hold, and the read holds a thousand more. -/
@[req "DUR-24"]
theorem armed_verdict_from_bound :
    let ss := delivered ++ [.observe 1 vaultLarge]
    let p := record Kernel.current [] (start vaultLarge) ss
    covered runCfg (authorizedAt p.2 p.1 1) (p.2.fed.worlds 1).node vaultLarge
      Kernel.RegistrationCases.e1 = false :=
  covered_false_of_value_bound _ _ _ _ _ 100 rfl rfl (by decide) (by decide) (by decide) (by decide)

end Run

end BtcPolicy.Exhibits.Feasibility

namespace BtcPolicy.Exhibits.Recovery
open BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Recovery
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Sweep.Cases (vault honest4 start delivered armed)
open BtcPolicy.Settlement (confirmedAt)

/-! ### Recovery authority and the five classes

Research task `bps-uaer.18`. Every run below is a `Recovery.Execution` over `Kernel.current`, the
guard values as they stand and `Sweep.Cases`' federation: four honest nodes, keys 1 to 4, threshold 2,
outpoints 0 and 1 created by transaction 7. The lock is the default vault's. The instants are
hand-chosen; the runs are not. Custody is written in, never derived: that is the whole of what these
exhibits say about keys. -/

def lock : Nat := Timelock.defaultNSequence
def secs : Nat := 15552000

/-- Outpoint 50 is the refresh's output, outpoint 51 the next refresh's; 3 is the sweep fixture's
external deposit, and the rest come from funding transaction 7. -/
def creator : Package.Creator := fun o =>
  if o == 50 then 600 else if o == 51 then 601 else if o == 3 then 300 else 7

def rcfg : Cfg :=
  { sweep := { Sweep.Cases.cfg Coverage.current Coverage.currentExternal Package.current with creator := creator },
    t := 2, recKeys := [11, 12, 13], sealedLock := lock }

theorem lock_secs : lockSecs lock = secs := by decide

/-- Funding transaction 7 confirmed at height 3, whose parent's MTP is 1000. Height 9's MTP is a thousand
seconds on: both coins are young. -/
def young : Backend :=
  { vault with tip := ⟨9, 109⟩, heights := [(7, 3)], mtps := [(2, 1000), (3, 1100), (9, 2000)] }
/-- The same chain later, with the tip's MTP one second short of the lock. -/
def almost : Backend := { young with sequence := 2, mtps := [(2, 1000), (3, 1100), (9, 1000 + secs - 1)], tip := ⟨9, 209⟩ }
/-- The tip's MTP exactly at the lock. -/
def ripe : Backend := { young with sequence := 3, mtps := [(2, 1000), (3, 1100), (9, 1000 + secs)], tip := ⟨9, 309⟩ }
/-- `ripe` with a large third coin no Escape spends. -/
def ripeLarge : Backend := { ripe with confirmed := [(0, 40), (1, 60), (9, 1000)] }

/-- The Operator's Recovery spend of outpoint 0. -/
def rtx : Tx := { id := 900, inputs := [0], outflow := 0 }
def rspend : Spend := { tx := rtx, sequences := [lock], witness := Alerts.recoveryWitness }

/-- It confirms in block 10, whose parent is `ripe`'s tip. -/
def minedR : Backend :=
  { ripe with
    tip := ⟨10, 410⟩, sequence := 4, confirmed := [(1, 60)], mined := [(900, [0])],
    heights := [(900, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 600)] }
/-- A chain that shows it confirmed in a block whose parent's lock has not passed. -/
def earlyR : Backend :=
  { young with
    tip := ⟨10, 510⟩, sequence := 4, confirmed := [(1, 60)], mined := [(900, [0])],
    heights := [(900, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 2000), (10, 2600)] }
/-- A reorganization to a chain with no spend, on which funding transaction 7 confirmed at height 8. -/
def reorgYoung : Backend :=
  { ripe with
    tip := ⟨9, 609⟩, sequence := 5, heights := [(7, 8)],
    mtps := [(7, 1000 + secs - 5), (8, 1000 + secs - 2), (9, 1000 + secs)] }
/-- A reorganization that keeps the funding block and drops every spend. -/
def reorgBack : Backend := { ripe with tip := ⟨10, 710⟩, sequence := 5, mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 700)] }
/-- A reorganization on which an external transaction spent outpoint 0. -/
def reorgSpent : Backend :=
  { ripe with
    tip := ⟨10, 810⟩, sequence := 5, confirmed := [(1, 60)], mined := [(777, [0])],
    heights := [(777, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 800)] }

def full : Holder := { keys := [11, 12, 13], descriptor := true, network := true }
def nobody : Holder := { keys := [], descriptor := false, network := false }

/-- The start: a fresh federation at instant `b`; the Operator holds all, the attacker nothing. -/
def st0 (b : Backend) : St := { sw := start b, op := full, att := nobody }

theorem st0_fresh (b : Backend) : Fresh honest4 (st0 b) := by
  have h : Federation.Fresh honest4 Federation.Cases.fed0 := by
    unfold Federation.Fresh
    decide
  exact ⟨⟨h, rfl, fun _ => rfl⟩, rfl, rfl, rfl, rfl⟩

abbrev base (ss : List Sweep.Step) : List BtcPolicy.Recovery.Step := ss.map .base

def runOf (b : Backend) (xs : List BtcPolicy.Recovery.Step) : Trace × St := record Kernel.current [] (st0 b) xs
def isLegal (b : Backend) (xs : List BtcPolicy.Recovery.Step) : Bool := legal rcfg Kernel.current honest4 [] (st0 b) xs
def failsOf (b : Backend) (xs : List BtcPolicy.Recovery.Step) (sc : Scenario) : List Failure :=
  failures rcfg (runOf b xs).2 (runOf b xs).1 honest4 sc
def canPublish (b : Backend) (xs : List BtcPolicy.Recovery.Step) (who : Party) (sp : Spend) : Bool :=
  admits rcfg Kernel.current honest4 (runOf b xs).2 (runOf b xs).1 (.publish who sp)

theorem execution_of (b : Backend) (xs : List BtcPolicy.Recovery.Step) (h : isLegal b xs = true) :
    Execution rcfg Kernel.current honest4 (runOf b xs).1 (runOf b xs).2 :=
  execution_of_legal (.init _ (st0_fresh b)) h

/-- The Normal-path question throughout: the hot spend over outpoint 0, user-signed. -/
def sc0 : Scenario :=
  { coin := 0, target := tx1, userSigs := [{ msg := sighash tx1 0, input := 0 }], hot := true }

/-- Nodes 1 and 2 armed, the Escape released and possessed at node 1, which reads this instant; nodes 3
and 4 took nothing, so a hot spend still has two open signers. -/
def swept (b : Backend) : List BtcPolicy.Recovery.Step := base (delivered ++ [.observe 1 b])

/-! #### One scenario per class, standing alone -/

/-- **Recovery not yet mature.** The Normal path has its signers, node 1 can assemble the Escape, the
Operator holds everything and nothing is out: all that fails is this coin's age. -/
@[req "CHN-4"]
theorem only_not_mature : isLegal young (swept young) = true ∧
    failsOf young (swept young) sc0 = [.notMature] := by
  decide

/-- **Missing custody capability.** The same run on the mature chain, the Operator two keys short. -/
@[req "OPS-33"]
theorem only_missing_custody :
    isLegal ripe (swept ripe ++ [.lose 11, .lose 12]) = true ∧
      failsOf ripe (swept ripe ++ [.lose 11, .lose 12]) sc0 = [.missingCustody] := by
  decide

/-- **Waiting for inclusion.** The same run with the Recovery spend published and not confirmed. -/
@[req "SEC-54"]
theorem only_awaiting :
    isLegal ripe (swept ripe ++ [.publish .operator rspend]) = true ∧
      failsOf ripe (swept ripe ++ [.publish .operator rspend]) sc0 = [.awaitingInclusion] := by
  decide

/-- **Unavailable fast exit.** The vault holds a coin the Escape leaves out, so it covers too little of
the read (`Exhibits.Sweep.armed_without_eligible_escape`). -/
@[req "DUR-24"]
theorem only_fast_unavailable :
    isLegal ripeLarge (swept ripeLarge) = true ∧
      failsOf ripeLarge (swept ripeLarge) sc0 = [.fastUnavailable] := by
  decide

/-- **Blocked Normal authority.** Nodes 1 and 2 are armed and nodes 3 and 4 dead: no signer remains for
the hot spend, while the Escape and Recovery both stand. -/
@[req "DUR-11"]
theorem only_normal_blocked :
    isLegal ripe (swept ripe ++ [.die 3, .die 4]) = true ∧
      failsOf ripe (swept ripe ++ [.die 3, .die 4]) sc0 = [.normalBlocked] := by
  decide

/-- The same class from a lost user key instead: nodes 3 and 4 are open and would be the quorum, and no
user signature exists. `SEC-54`: "Loss of `U` prevents fresh user signatures". -/
@[req "SEC-54"]
theorem normal_blocked_by_user_key :
    failsOf ripe (swept ripe) { sc0 with userSigs := [] } = [.normalBlocked] ∧
      normalOpen rcfg (runOf ripe (swept ripe)).2 honest4 sc0 = true := by
  decide

/-- **Not interchangeable.** Each class has a reachable scenario standing in it alone, so each pair of
classes is told apart by a reachable scenario. -/
@[req "SEC-54"]
theorem classes_stand_alone (f : Failure) :
    ∃ T st, Execution rcfg Kernel.current honest4 T st ∧ failures rcfg st T honest4 sc0 = [f] := by
  cases f with
  | normalBlocked => exact ⟨_, _, execution_of _ _ only_normal_blocked.1, only_normal_blocked.2⟩
  | fastUnavailable => exact ⟨_, _, execution_of _ _ only_fast_unavailable.1, only_fast_unavailable.2⟩
  | notMature => exact ⟨_, _, execution_of _ _ only_not_mature.1, only_not_mature.2⟩
  | missingCustody => exact ⟨_, _, execution_of _ _ only_missing_custody.1, only_missing_custody.2⟩
  | awaitingInclusion => exact ⟨_, _, execution_of _ _ only_awaiting.1, only_awaiting.2⟩

/-! #### Eligible, possible, included -/

/-- **A mature coin with custody held.** The Operator publishes at the lock, equality passing; it waits;
the chain confirms it in the next block; the coin stands in no class. `Recovery.included_origin` applies to
this run. -/
@[req "OPS-26"]
theorem mature_with_custody_included :
    let xs := [BtcPolicy.Recovery.Step.publish .operator rspend, .base (.chain minedR)]
    isLegal ripe xs = true ∧ eligible rcfg ripe rspend = true ∧
      confirmedAt (runOf ripe xs).2.sw.truth rtx = true ∧
      failsOf ripe [.publish .operator rspend] sc0 = [.fastUnavailable, .awaitingInclusion] ∧
      failsOf ripe xs sc0 = [] := by
  decide

/-- The theorem's premises on that run: it has an inhabitant. -/
@[req "OPS-26"]
theorem included_origin_inhabited :
    let xs := [BtcPolicy.Recovery.Step.publish .operator rspend, .base (.chain minedR)]
    includedOk rcfg (runOf ripe xs).2.sw.truth rspend = true ∧
      ∃ st₀, (st₀, BtcPolicy.Recovery.Step.publish .operator rspend) ∈ (runOf ripe xs).1 ∧
        eligible rcfg st₀.sw.truth rspend = true ∧ capable rcfg (st₀.holder .operator) = true := by
  intro xs
  exact included_origin (p := (.operator, rspend)) (execution_of ripe xs (by decide)) (by decide) (by decide)

/-- **Not yet mature, with everything else held.** One second short, the chain refuses every party; at
the lock it takes the Operator's. The same spend with the sequence that disables relative locks, or the
Normal branch's witness, is refused at the lock. -/
@[req "CHN-10"]
theorem before_maturity_refused :
    canPublish young [] .operator rspend = false ∧ canPublish almost [] .operator rspend = false ∧
      canPublish ripe [] .operator rspend = true ∧
      canPublish ripe [] .operator { rspend with sequences := [0xffffffff] } = false ∧
      canPublish ripe [] .operator { rspend with witness := Alerts.normalWitness } = false := by
  decide

/-- **Custody short, with the coin mature.** One key lost leaves two and Recovery stands. Two lost, or the
descriptor backup lost with all three keys held, and it does not. Two copies of one key count once. -/
@[req "OPS-23"]
theorem missing_custody_refused :
    canPublish ripe [.lose 11] .operator rspend = true ∧
      canPublish ripe [.lose 11, .lose 12] .operator rspend = false ∧
      canPublish ripe [.loseBackup] .operator rspend = false ∧
      capable rcfg { full with keys := [11, 11] } = false ∧
      capable rcfg { full with keys := [11, 99] } = false ∧
      capable rcfg { full with network := false } = false := by
  decide

/-- **`SEC-54` row 14's maturity half.** An attacker with two copied keys and the public backup can spend
no coin before its lock has passed, and can spend it, against an Operator holding everything, at the lock; the
chain then shows the attacker's spend. That this is theft, and who holds which key, is outside. -/
@[req "SEC-54"]
theorem two_keys_gate_on_maturity :
    let ks : List BtcPolicy.Recovery.Step := [.copy 11, .copy 12, .learnBackup]
    canPublish young ks .attacker rspend = false ∧ canPublish ripe ks .attacker rspend = true ∧
      canPublish ripe [.copy 11, .learnBackup] .attacker rspend = false ∧
      isLegal ripe (ks ++ [.publish .attacker rspend, .base (.chain minedR)]) = true ∧
      confirmedAt (runOf ripe (ks ++ [.publish .attacker rspend, .base (.chain minedR)])).2.sw.truth rtx = true := by
  decide

/-- A chain cannot show a published spend where its lock did not allow it: the move to that instant is
not admitted, and the move to the instant where it did allow is. -/
@[req "CHN-10"]
theorem early_inclusion_refused :
    admits rcfg Kernel.current honest4 (runOf ripe [.publish .operator rspend]).2
        (runOf ripe [.publish .operator rspend]).1 (.base (.chain earlyR)) = false ∧
      admits rcfg Kernel.current honest4 (runOf ripe [.publish .operator rspend]).2
        (runOf ripe [.publish .operator rspend]).1 (.base (.chain minedR)) = true := by
  decide

/-- A chain over slots: the coin mature at slots 0 and 1, the spend confirmed from slot 2 on, its input
spent there. -/
def chainAt (u : Nat) : Backend := if u < 2 then ripe else minedR

theorem chainAt_serves : Serves rcfg chainAt (fun u => u % 2 == 1) rspend := by
  intro u _ he
  have hu : u + 1 ≥ 2 := by
    by_cases h : u < 2
    · have : u % 2 = 1 := by simpa using ‹(fun u => u % 2 == 1) u = true›
      omega
    · omega
  simp only [chainAt, if_neg (Nat.not_lt.2 hu)]
  decide

theorem chainAt_enabled (u : Nat) :
    (eligible rcfg (chainAt u) rspend || confirmedAt (chainAt u) rspend.tx) = true := by
  unfold chainAt
  split <;> decide

/-- `Recovery.included_within` and `Recovery.included_eventually` have an inhabitant, on a chain where the
spend's input is spent once it confirms: service every other slot, so `bounded 1`, and confirmation by slot 2. -/
@[req "OPS-26"]
theorem inclusion_inhabited :
    (∃ u, 0 ≤ u ∧ u ≤ 0 + 1 + 1 ∧ confirmedAt (chainAt u) rspend.tx = true) ∧
      ∃ u, 0 ≤ u ∧ confirmedAt (chainAt u) rspend.tx = true := by
  have hb : (Progress.Profile.bounded 1).Holds (fun u => u % 2 == 1) := by
    intro t
    by_cases h : t % 2 = 1
    · exact ⟨t, Nat.le_refl _, by omega, by simp [h]⟩
    · exact ⟨t + 1, by omega, by omega, by simp; omega⟩
  exact ⟨included_within hb chainAt_serves fun u _ _ => chainAt_enabled u,
    included_eventually (Progress.bounded_eventual hb) chainAt_serves fun u _ => chainAt_enabled u⟩

/-! #### A coin's history is the chain's -/

/-- **Lockdown does not restart maturity.** On the young chain nodes 1 and 2 arm, and the deadline driver
latches both past `T`: the coin's age is what it was and the Operator's spend is refused. The chain alone
moves it to the lock, where the spend stands, exactly as on the run with no duress and no latch at all. -/
@[req "CHN-4"]
theorem lockdown_does_not_restart :
    let lat : List BtcPolicy.Recovery.Step :=
      swept young ++ [.latch 1 (envAt 1000 1000), .latch 2 (envAt 1000 1000)]
    let lat' := lat ++ [.base (.chain ripe)]
    isLegal young lat' = true ∧
      (runOf young lat).2.latched = [2, 1] ∧
      (lockAge (clock (runOf young lat).2.sw.truth) 7 = lockAge (clock young) 7) ∧
      canPublish young lat .operator rspend = false ∧
      canPublish young lat' .operator rspend = true ∧
      canPublish ripe [] .operator rspend = true ∧
      lockAge (clock (runOf young lat').2.sw.truth) 7 = lockAge (clock (runOf ripe []).2.sw.truth) 7 := by
  decide

/-- A latched node registers nothing new, and an unarmed node's driver has nothing to latch. -/
@[req "DUR-7"]
theorem latched_takes_no_accept :
    let lat : List BtcPolicy.Recovery.Step := swept young ++ [.latch 1 (envAt 1000 1000)]
    admits rcfg Kernel.current honest4 (runOf young lat).2 (runOf young lat).1
        (.base (Sweep.Cases.duressAt 1 30 RegistrationCases.c3 RegistrationCases.e3)) = false ∧
      admits rcfg Kernel.current honest4 (runOf young lat).2 (runOf young lat).1
        (.latch 3 (envAt 1000 1000)) = false := by
  decide

/-- The refresh: outpoint 0 into outpoint 50. -/
def rf : Tx := { id := 600, inputs := [0], outflow := 0 }
def afterRefresh : Backend := confirmRefresh ripe rf [(50, 39)] 10 910 (1000 + secs + 600)
/-- The successor's chain a month on, and at its own lock. -/
def month : Backend :=
  { afterRefresh with
    tip := ⟨11, 911⟩, sequence := afterRefresh.sequence + 1,
    mtps := (11, 1000 + secs + 600 + 2592000) :: afterRefresh.mtps }
def succRipe : Backend :=
  { afterRefresh with
    tip := ⟨12, 912⟩, sequence := afterRefresh.sequence + 2,
    mtps := (12, 1000 + secs + secs) :: afterRefresh.mtps }
/-- A Recovery spend of the successor. -/
def rspend50 : Spend := { rspend with tx := { rtx with id := 901, inputs := [50] } }

/-- **A confirmed refresh's outputs start their own count.** The parent is mature; the refresh spends it,
so nothing can reach the parent any more. The successor reads its own block's parent: young at once and a
month on, mature only at its own lock. `SPN-46`'s own age, which reads the confirming block, admits the
parent's refresh at thirty days, and admits the successor's a month on, before its lock: so a holder who
keeps refreshing keeps a coin young, the part of `SEC-54` row 14 that says "only refresh keeps a coin
young". -/
@[req "CHN-4"]
theorem refresh_starts_own_count :
    matured rcfg ripe 0 = true ∧ matured rcfg afterRefresh 0 = false ∧
      matured rcfg afterRefresh 50 = false ∧ matured rcfg month 50 = false ∧
      matured rcfg succRipe 50 = true ∧
      RefreshAge.admit .chainMtp 2592000 (clock ripe) [] 0 7 = true ∧
      RefreshAge.admit .chainMtp 2592000 (clock month) [] 0 600 = true ∧
      isLegal ripe [.base (.chain afterRefresh), .base (.chain month)] = true ∧
      canPublish ripe [.base (.chain afterRefresh), .base (.chain month)] .operator rspend50 = false ∧
      canPublish ripe [.base (.chain afterRefresh), .base (.chain succRipe)] .operator rspend50 = true := by
  decide

/-- `Recovery.successor_own_history` on that refresh: it has an inhabitant. -/
@[req "CHN-4"]
theorem successor_own_history_inhabited :
    lockAge (clock afterRefresh) 600 = some 600 ∧ ¬ lockSecs rcfg.sealedLock ≤ 600 ∧
      matured rcfg afterRefresh 50 = false :=
  ⟨(successor_own_history rcfg ripe rf [(50, 39)] 10 910 (1000 + secs + 600) (by decide) (o := 50)
      (by decide) (by decide)).1.trans (by decide), by decide, by decide⟩

/-- **A reorganization can make a mature coin young.** The funding transaction re-confirms at height 8,
and the spend the chain allowed a moment ago is refused, with the same keys. -/
@[req "CHN-4"]
theorem reorg_makes_coin_young :
    isLegal ripe [.base (.chain reorgYoung)] = true ∧ matured rcfg ripe 0 = true ∧
      matured rcfg reorgYoung 0 = false ∧
      canPublish ripe [] .operator rspend = true ∧
      canPublish ripe [.base (.chain reorgYoung)] .operator rspend = false ∧
      failsOf ripe (base [.chain reorgYoung]) { sc0 with userSigs := sc0.userSigs } =
        [.fastUnavailable, .notMature] := by
  decide

/-- **A reorganization can undo an inclusion.** The spend confirmed; a reorganization drops it: the coin is
unspent again, and the spend is waiting again, with no step of any party's. -/
@[req "SEC-54"]
theorem reorg_undoes_inclusion :
    let xs : List BtcPolicy.Recovery.Step :=
      [.publish .operator rspend, .base (.chain minedR)]
    let ys := xs ++ [.base (.chain reorgBack)]
    isLegal ripe ys = true ∧ failsOf ripe xs sc0 = [] ∧
      confirmedAt reorgBack rtx = false ∧ matured rcfg reorgBack 0 = true ∧
      (failsOf ripe ys sc0).contains .awaitingInclusion = true := by
  decide

/-- **A reorganization can spend the coin.** On the other chain an external transaction spent it, and a
Recovery spend of it is refused. The coin has moved and stands in no class. -/
@[req "CHN-4"]
theorem reorg_spends_coin :
    isLegal ripe [.base (.chain reorgSpent)] = true ∧
      canPublish ripe [.base (.chain reorgSpent)] .operator rspend = false ∧
      failsOf ripe (base [.chain reorgSpent]) sc0 = [] := by
  decide

/-! #### Death, loss and what stays -/

/-- **`SEC-54` rows L3, L7 and L8 at one mature coin.** Every node is dead: the Normal path and the fast exit
are gone and Recovery stands. Then the Operator also loses two keys, or the descriptor backup, and nothing
remains: three classes at once, each for its own reason. -/
@[req "SEC-54"]
theorem dead_federation :
    let allDead : List BtcPolicy.Recovery.Step := [.die 1, .die 2, .die 3, .die 4]
    isLegal ripe allDead = true ∧ failsOf ripe allDead sc0 = [.normalBlocked, .fastUnavailable] ∧
      canPublish ripe allDead .operator rspend = true ∧
      failsOf ripe (allDead ++ [.lose 11, .lose 12]) sc0 =
        [.normalBlocked, .fastUnavailable, .missingCustody] ∧
      canPublish ripe (allDead ++ [.lose 11, .lose 12]) .operator rspend = false ∧
      failsOf ripe (allDead ++ [.loseBackup]) sc0 = [.normalBlocked, .fastUnavailable, .missingCustody] ∧
      canPublish ripe (allDead ++ [.loseBackup]) .operator rspend = false := by
  decide

/-- **Death stops a later copy, not an earlier one.** A dead node's key cannot be extracted; one copied
before it died stays copied, and its copy can still sign. -/
@[req "DUR-18"]
theorem copy_before_death_stays :
    let xs : List BtcPolicy.Recovery.Step := [.die 1]
    let ys : List BtcPolicy.Recovery.Step := [.base (.fed (.extract 1)), .die 1]
    admits rcfg Kernel.current honest4 (runOf ripe xs).2 (runOf ripe xs).1 (.base (.fed (.extract 1))) = false ∧
      isLegal ripe ys = true ∧ (runOf ripe ys).2.sw.fed.extracted.contains 1 = true ∧
      admits rcfg Kernel.current honest4 (runOf ripe ys).2 (runOf ripe ys).1
        (.base (.fed (.forge (Sweep.Cases.part RegistrationCases.c1 1 0)))) = true := by
  decide

/-- **What left a node stays out.** The Escape is sent, the sender dies: the submission still stands, and
another node's Escape need not. An external transaction confirming over the Escape's second input conflicts
it, on this instant's chain, while outpoint 0 is unspent. -/
def conflictX : Backend :=
  { ripe with
    tip := ⟨10, 1010⟩, sequence := 6, confirmed := [(0, 40)], mined := [(777, [1])],
    heights := [(777, 10), (7, 3)], mtps := [(2, 1000), (3, 1100), (9, 1000 + secs), (10, 1000 + secs + 800)] }

@[req "SEC-54"]
theorem submission_outlives_sender :
    let sentS := swept ripe ++ base [Sweep.Cases.assemble 1 RegistrationCases.e1.id, Sweep.Cases.sendAt 1 RegistrationCases.e1.id]
    isLegal ripe (sentS ++ [.die 1, .die 2, .base (.chain conflictX)]) = true ∧
      failsOf ripe sentS sc0 = [.awaitingInclusion] ∧
      failsOf ripe (sentS ++ [.die 1, .die 2]) sc0 = [.awaitingInclusion] ∧
      failsOf ripe (sentS ++ [.die 1, .die 2, .base (.chain conflictX)]) sc0 = [.fastUnavailable] := by
  decide

/-- **A dead node's history stays.** Node 1 releases and dies. It takes no later step, and its partial stays
in the inventory; it is counted as a record although the node can sign nothing more. -/
@[req "DUR-18"]
theorem death_keeps_record :
    let xs := base armed ++ [.die 1]
    isLegal ripe xs = true ∧
      admits rcfg Kernel.current honest4 (runOf ripe xs).2 (runOf ripe xs).1
        (.base (.fed (.process 1 envFire .firePass))) = false ∧
      (runOf ripe xs).2.sw.fed.parts.contains (Sweep.Cases.part RegistrationCases.e1 1 0) = true ∧
      openSigner (runOf ripe xs).2 honest4 RegistrationCases.e1.tx false 1 = false := by
  decide

end BtcPolicy.Exhibits.Recovery

namespace BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (A env0 envFire envAt)
open BtcPolicy.Ingress (check checkedTrace_of hot_binding code code_injective frame_wf accepted_validates accepted_spend)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 txidA checked_pair lcfg)
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Recovery
open BtcPolicy.Settlement (confirmedAt)

/-! ### One reachable composed history, end to end

Research task `bps-uaer.18`. One request, `Exhibits.Ingress.req0`, whose candidates are computed by
`Ingress.check`, through one composed model: three honest nodes under `Kernel.current` with `hold_secs`
100 and threshold 2, keys 1 to 3, reading one backend world. `coerced` runs from checked ingress through
each node's holder decision, the Escape's partials and their delivery, the assembly's coverage, ancestry and
possession, and the send, to a confirmation the chain alone makes. Beside it, over the same model and the
same request: `ordinary`, the path with no duress; `thirdSigns`, `tooLate` and `keysCopied`, where the protection has its limits or fails; the same schedule at
an instant the Escape does not cover, and `coercedSteps` stopped short of the chain, where safety holds and
progress does not.
The ledger is beside the run as it is in `BtcPolicy.Settlement`; `Exhibits.LedgerSilence` carries the Hot
ledgers on these runs and states SILENCE on `coerced`. -/

/-- The request's one outpoint. -/
def coin : Nat := code (txidA ++ Encode.be 4 0)

theorem coin_is_input : sp0.tx.inputs = [coin] ∧ es0.tx.inputs = [coin] := by decide +kernel

def book : Sweep.Book :=
  { value := fun o => if o == coin then 100 else if o == 9 then 1000 else 0,
    outputs := fun tx => [tx + 1000],
    delivered := fun tx => if tx == es0.tx.id then 98 else 0 }

def rcfg : Cfg :=
  { sweep :=
      { pct := Coverage.floorPct, keys := [1, 2, 3], book := book, creator := fun _ => 7,
        denominator := Coverage.current, external := Coverage.currentExternal,
        ancestry := Package.current },
    t := 2, recKeys := [11, 12, 13], sealedLock := Timelock.defaultNSequence }

def honest : List Nat := [1, 2, 3]
def worlds (self : Nat) : World := { node := { A with id := self, holdSecs := 100 }, exposure := [] }
def fed0 : Federation.Fed := { worlds := worlds, net := [] }

/-- The coin confirmed at height 3 and young at height 5. -/
def v : Backend :=
  { tip := ⟨5, 105⟩, sequence := 1, confirmed := [(coin, 100)], mempool := [], pending := [],
    heights := [(7, 3)], mtps := [(2, 1000), (5, 2000)] }
/-- The same vault with a large coin the Escape leaves out. -/
def vLarge : Backend := { v with confirmed := [(coin, 100), (9, 1000)] }
/-- The Escape confirmed. -/
def vSwept : Backend :=
  { v with
    tip := ⟨6, 106⟩, sequence := 2, confirmed := [], mined := [(es0.tx.id, es0.tx.inputs)],
    heights := [(es0.tx.id, 6), (7, 3)], mtps := [(2, 1000), (5, 2000), (6, 2600)] }
/-- The hot spend confirmed. -/
def vSpent : Backend :=
  { v with
    tip := ⟨6, 206⟩, sequence := 2, confirmed := [], mined := [(sp0.tx.id, sp0.tx.inputs)],
    heights := [(sp0.tx.id, 6), (7, 3)], mtps := [(2, 1000), (5, 2000), (6, 2600)] }
/-- The uncovered vault at the coin's lock. -/
def vLargeRipe : Backend :=
  { vLarge with tip := ⟨9, 109⟩, sequence := 2, mtps := [(2, 1000), (5, 2000), (9, 1000 + 15552000)] }

def custody : Holder := { keys := [11, 12, 13], descriptor := true, network := true }
def st0 (b : Backend) : St :=
  { sw := { fed := fed0, truth := b }, op := custody, att := { keys := [], descriptor := false, network := false } }

theorem st0_fresh (b : Backend) : Fresh honest (st0 b) := by
  have h : Federation.Fresh honest fed0 := by
    unfold Federation.Fresh
    decide
  exact ⟨⟨h, rfl, fun _ => rfl⟩, rfl, rfl, rfl, rfl⟩

def acc (i cid : Nat) (duress : Bool) (env : Env := env0) : Sweep.Step :=
  .fed (.process i env (.accept cid duress (Wall.sample 200) sp0 es0))
def fire (i : Nat) (env : Env) : Sweep.Step := .fed (.process i env .firePass)
def assemble (i cid : Nat) (env : Env) : Sweep.Step := .fed (.process i env (.packageAccepted cid))
def send (i cid : Nat) (env : Env) : Sweep.Step := .fed (.process i env (.send cid))
/-- Signer `s`'s partial on input 0 of a candidate. -/
def part (c : Cand) (s : Nat) : Exp :=
  { msg := sighash c.tx 0, input := 0, signer := s, hot := c.hot, cid := c.id }

/-- Nodes 1 and 2 take the checked request under duress, each relays, each counts `t` holders and arms
at its holder decision, and each fire pass releases the Escape and not the hot spend. -/
def toRelease : List Sweep.Step :=
  [acc 1 10 true, acc 2 10 true, .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩), fire 1 envFire, fire 2 envFire]

/-- Then node 2's partial reaches node 1, which reads the vault. -/
def toRead (b : Backend) : List Sweep.Step :=
  toRelease ++ [.fed (.deliverPartial 1 envFire (part es0 2)), .observe 1 b]

/-- Then node 1 assembles and sends. -/
def coercedSteps : List Sweep.Step :=
  toRead v ++ [assemble 1 es0.id envFire, send 1 es0.id envFire]

/-- Then the chain alone confirms it. -/
def coerced : List Sweep.Step := coercedSteps ++ [.chain vSwept]

abbrev base (ss : List Sweep.Step) : List BtcPolicy.Recovery.Step := ss.map .base
def runOf (b : Backend) (ss : List BtcPolicy.Recovery.Step) : Trace × St := record Kernel.current [] (st0 b) ss
def isLegal (b : Backend) (ss : List BtcPolicy.Recovery.Step) : Bool :=
  legal rcfg Kernel.current honest [] (st0 b) ss

theorem execution_of (b : Backend) (xs : List BtcPolicy.Recovery.Step) (h : isLegal b xs = true) :
    Execution rcfg Kernel.current honest (runOf b xs).1 (runOf b xs).2 :=
  execution_of_legal (.init _ (st0_fresh b)) h

def sc : Scenario :=
  { coin := coin, target := sp0.tx, userSigs := [{ msg := sighash sp0.tx 0, input := 0 }], hot := true }

/-- The composed federation trace of a schedule. -/
def fedOf (b : Backend) (xs : List BtcPolicy.Recovery.Step) : Federation.Trace :=
  Sweep.fedTrace (sweepTrace (runOf b xs).1)

theorem federation_of (b : Backend) (xs : List BtcPolicy.Recovery.Step) (h : isLegal b xs = true) :
    Federation.Execution Kernel.current honest (fedOf b xs) (runOf b xs).2.sw.fed :=
  Sweep.fed_execution (Settlement.to_sweep (to_settlement (execution_of b xs h)))

/-- **The history.** Checked ingress: every acceptance in the run is the event `Ingress.check` produced
for the request, and gate 24's verdict holds on the empty Hot ledger, whose row is the check's own amount.
Local decision: nodes 1 and 2 are armed with the hot spend frozen, and the Escape released. Distributed
authority: at node 1's read, coverage, ancestry and `t` distinct signers on every input of the Escape.
Permitted submission: the assembly is admitted and the send, re-authorized at its own state, submits the
Escape's transaction. Then the chain, and only the chain, shows it confirmed. -/
@[req "DUR-29"]
theorem coerced_history :
    let p := runOf v (base (toRead v))
    let n := (p.2.sw.fed.worlds 1).node
    let R := Federation.held 1 (Sweep.fedTrace (sweepTrace p.1)) p.2.sw.fed
    let q := runOf v (base coercedSteps)
    check ctx0 true req0 = .accepted sp0 es0 ∧
      Ledger.admits lcfg [] sp0 = true ∧
      isLegal v (base coerced) = true ∧
      n.armed = true ∧ ((p.2.sw.fed.worlds 2).node).armed = true ∧
      n.cands.any (fun c => c.id == sp0.id && c.frozen) = true ∧
      n.cands.any (fun c => c.id == es0.id && c.released) = true ∧
      Sweep.covered rcfg.sweep (Sweep.authorizedAt p.2.sw (sweepTrace p.1) 1) n v es0 = true ∧
      Sweep.ancestryOk rcfg.sweep (Sweep.authorizedAt p.2.sw (sweepTrace p.1) 1) v es0 = true ∧
      Authority.quorum rcfg.sweep.keys n.t es0.tx R = true ∧
      Sweep.admits rcfg.sweep honest p.2.sw (sweepTrace p.1) (assemble 1 es0.id envFire) = true ∧
      Sweep.submits Kernel.current (runOf v (base (toRead v ++ [assemble 1 es0.id envFire]))).2.sw
        (send 1 es0.id envFire) = [es0.tx.id] ∧
      confirmedAt q.2.sw.truth es0.tx = false ∧
      confirmedAt (runOf v (base coerced)).2.sw.truth es0.tx = true := by
  decide +kernel

/-- Every acceptance of that run is checked, and the hot spend's message is bound. -/
theorem coerced_checked :
    Ingress.CheckedTrace ctx0 (fedOf v (base coerced)) ∧
      Federation.HotBinding (runOf v (base coerced)).2.sw.fed (sighash sp0.tx 0) := by
  have hc : Ingress.CheckedTrace ctx0 (fedOf v (base coerced)) :=
    checkedTrace_of ctx0 _ [req0] (by decide +kernel)
  exact ⟨hc, hot_binding (federation_of v (base coerced) (by decide +kernel)) hc code_injective
    (frame_wf (accepted_validates checked_pair.1).1) (accepted_spend checked_pair.1).1⟩

/-- Past the Hold on each node's own HotClock. -/
def envHeld : Env := envAt 120 110

/-- `Federation.cohort_no_exposed_quorum` on a composed run of this request: with nodes 1 and 2
Hold-protected on their own histories, unextracted, and every key one of the three, the hot spend has no
exposed quorum against a threshold of 2. Each premise is decided on the run it is applied to. -/
theorem withholds_on (xs : List BtcPolicy.Recovery.Step) (qcs : List Ingress.ClawbackRequest)
    (hl : isLegal v xs = true)
    (hc : (Ingress.acceptPairs (fedOf v xs)).all
      (fun p => [req0].any fun q => check ctx0 true q == .accepted p.1 p.2) = true)
    (hcl : (Ingress.clawCands (fedOf v xs)).all
      (fun c => qcs.any fun q => Ingress.checkClawback ctx0 Classification.current q == some c) = true)
    (hp : ∀ i ∈ [1, 2], i ∈ honest ∧ i ∉ (runOf v xs).2.sw.fed.extracted ∧
      (Federation.project i (fedOf v xs)).all
        (Federation.holdFrame (sighash sp0.tx 0) (Mono.sample 10)) = true)
    (he : (runOf v xs).2.sw.fed.extracted = []) :
    exposedQuorum { node := (worlds 1).node, exposure := (runOf v xs).2.sw.fed.parts } sp0 = false := by
  have hexec := federation_of v xs hl
  have hchk := Ingress.checkedTrace_of_claws ctx0 _ [req0] qcs hc hcl
  refine Federation.cohort_no_exposed_quorum (r := Kernel.current) rfl hexec (worlds 1).node sp0
    (hot_binding hexec hchk code_injective (frame_wf (accepted_validates checked_pair.1).1)
      (accepted_spend checked_pair.1).1)
    [1, 2] (fun _ => Mono.sample 10) ?_ [1, 2, 3] ?_ (by decide)
  · intro i hi
    obtain ⟨h1, h2, h3⟩ := hp i hi
    exact ⟨h1, h2, List.all_eq_true.1 h3⟩
  · intro j hj
    rcases hj with hj | hj
    · exact hj
    · rw [he] at hj
      cases hj

/-- **What duress prevents, on the history.** No exposed quorum for the hot spend at the end of
`coerced`, from the theorem and not from reading the rows. -/
@[req "DUR-8"]
theorem duress_withholds :
    exposedQuorum { node := (worlds 1).node, exposure := (runOf v (base coerced)).2.sw.fed.parts } sp0 =
      false :=
  withholds_on _ [] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Node 3, which saw no duress, takes the same pair as an ordinary request after the Escape has
confirmed, is opened by relays from 1 and 2, and at its own matured Hold releases. -/
def thirdSigns : List Sweep.Step :=
  coerced ++ [acc 3 10 false, .fed (.deliver 3 env0 ⟨1, 10⟩), .fed (.deliver 3 env0 ⟨2, 10⟩),
    fire 3 envHeld]

/-- **What duress does not stop, and why it is enough.** A node outside the cohort still signs: the
inventory holds its hot row. That is one signer against a threshold of 2, by the same theorem. -/
@[req "DUR-8"]
theorem third_signs_alone :
    let p := runOf v (base thirdSigns)
    isLegal v (base thirdSigns) = true ∧
      ((p.2.sw.fed.parts.filter (·.hot)).map Exp.signer).eraseDups = [3] ∧
      exposedQuorum { node := (worlds 1).node, exposure := p.2.sw.fed.parts } sp0 = false :=
  ⟨by decide +kernel, by decide +kernel,
    withholds_on _ [] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)⟩

/-! #### The ordinary path -/

/-- With no duress, on the same request: both nodes take it, the Hold matures on each node's own clock,
each fires, node 2's partial reaches node 1, and node 1 assembles and sends the hot spend. -/
def ordinarySteps : List Sweep.Step :=
  [acc 1 10 false, acc 2 10 false, .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩), fire 1 envHeld, fire 2 envHeld,
   .fed (.deliverPartial 1 envHeld (part sp0 2)), .observe 1 v, assemble 1 sp0.id envHeld]
def ordinaryAll : List Sweep.Step := ordinarySteps ++ [send 1 sp0.id envHeld, .chain vSpent]

/-- **The same request, no duress.** The same chain of transitions reaches the hot spend's submission,
user-signed with `t` signers on every input, and the Escape is never released. -/
@[req "DUR-28"]
theorem ordinary_history :
    let p := runOf v (base ordinarySteps)
    isLegal v (base ordinaryAll) = true ∧
      (p.2.sw.fed.worlds 1).node.armed = false ∧
      Authority.normal rcfg.sweep.keys 2 sp0.tx sc.userSigs (inventory p.2) = true ∧
      Sweep.submits Kernel.current p.2.sw (send 1 sp0.id envHeld) = [sp0.tx.id] ∧
      p.2.sw.fed.parts.all (fun x => x.cid != es0.id) = true ∧
      confirmedAt (runOf v (base ordinaryAll)).2.sw.truth sp0.tx = true := by
  decide +kernel

/-! #### Where the protection fails -/

/-- A second request over the same two transactions: a new commitment under a new expiry. -/
def req1 : Ingress.Request := { req0 with expiry := 300 }
def sp1 : Cand := Ingress.cand ctx0 req1 req1.spend true req1.fireAt
def es1 : Cand := Ingress.cand ctx0 req1 req1.escape false none

/-- Both nodes release the hot spend, its Hold matured, before any duress; then the coercion arrives, on a
new commitment, at both. -/
def tooLate : List Sweep.Step :=
  ordinarySteps.take 8 ++
    [.fed (.process 1 envHeld (.accept 20 true (Wall.sample 300) sp1 es1)),
     .fed (.process 2 envHeld (.accept 20 true (Wall.sample 300) sp1 es1)),
     .fed (.emit 1 20), .fed (.emit 2 20),
     .fed (.deliver 1 envHeld ⟨2, 20⟩), .fed (.deliver 2 envHeld ⟨1, 20⟩)]

/-- **Duress too late.** Both nodes end armed, as in the history above, and it prevents nothing: the
partials left before it, so the inventory holds the hot spend's quorum. The theorem's premise fails, and
the history shows where: node 1's opening at HotClock 110 is past any instant by which it could have
armed. -/
@[req "DUR-8"]
theorem duress_too_late :
    let p := runOf v (base tooLate)
    isLegal v (base tooLate) = true ∧
      check ctx0 true req1 = .accepted sp1 es1 ∧ sp1.tx = sp0.tx ∧ sp1.id ≠ sp0.id ∧
      (p.2.sw.fed.worlds 1).node.armed = true ∧ (p.2.sw.fed.worlds 2).node.armed = true ∧
      exposedQuorum { node := (worlds 1).node, exposure := p.2.sw.fed.parts } sp0 = true ∧
      Authority.quorum rcfg.sweep.keys 2 sp0.tx (inventory p.2) = true ∧
      Federation.holdBreach (sighash sp0.tx 0) (Federation.project 1 (fedOf v (base tooLate))) = true := by
  decide +kernel

/-- Two copied keys sign the hot spend at the armed nodes' side. -/
def keysCopied : List Sweep.Step :=
  toRelease ++ [.fed (.extract 1), .fed (.extract 2), .fed (.forge (part sp0 1)), .fed (.forge (part sp0 2))]

/-- **Copied keys.** The same armed nodes hold no hot row of their own, and two keys copied from them
give the quorum the cohort theorem excluded, whose premise asks each member unextracted. -/
@[req "DUR-8"]
theorem copied_keys_defeat :
    let p := runOf v (base keysCopied)
    isLegal v (base keysCopied) = true ∧
      (p.2.sw.fed.worlds 1).node.armed = true ∧ (p.2.sw.fed.worlds 2).node.armed = true ∧
      (p.2.sw.fed.worlds 1).exposure.all (fun x => !x.hot) = true ∧
      exposedQuorum { node := (worlds 1).node, exposure := p.2.sw.fed.parts } sp0 = true ∧
      p.2.sw.fed.extracted.contains 1 = true := by
  decide +kernel

/-! #### Where safety holds and progress does not -/

/-- **Safe, and nothing moves.** The same request at an instant its Escape does not cover: both nodes arm,
the hot spend is frozen, and the theorem's account holds as before. The assembly is not admitted and the send
submits nothing. The coin stands in three classes at once on the young chain, and at its lock
in two, with Recovery open. -/
@[req "DUR-19"]
theorem safe_without_progress :
    let p := runOf vLarge (base (toRead vLarge))
    isLegal vLarge (base (toRead vLarge)) = true ∧
      (p.2.sw.fed.worlds 1).node.armed = true ∧
      (p.2.sw.fed.worlds 1).node.cands.any (fun c => c.id == sp0.id && c.frozen) = true ∧
      Sweep.admits rcfg.sweep honest p.2.sw (sweepTrace p.1) (assemble 1 es0.id envFire) = false ∧
      Sweep.submits Kernel.current p.2.sw (send 1 es0.id envFire) = [] ∧
      exposedQuorum { node := (worlds 1).node, exposure := p.2.sw.fed.parts } sp0 = false ∧
      failures rcfg p.2 p.1 honest sc = [.normalBlocked, .fastUnavailable, .notMature] := by
  decide +kernel

/-- The same run with the chain moved to the coin's lock. Of this hot target, this registered Escape and
Recovery, Recovery is the one that stands. Another Normal-path transaction over the coin is another
scenario (`other_target_other_scenario`). -/
@[req "OPS-26"]
theorem at_the_lock :
    let xs := base (toRead vLarge ++ [.chain vLargeRipe])
    let p := runOf vLarge xs
    let rsp : Spend :=
      { tx := { id := 900, inputs := [coin], outflow := 0 },
        sequences := [Timelock.defaultNSequence], witness := Alerts.recoveryWitness }
    isLegal vLarge xs = true ∧
      failures rcfg p.2 p.1 honest sc = [.normalBlocked, .fastUnavailable] ∧
      admits rcfg Kernel.current honest p.2 p.1 (.publish .operator rsp) = true := by
  decide +kernel

/-- A non-hot Normal-path target over the coin, as a claw-back or a refresh would be. -/
def clawTx : Tx := { id := 500, inputs := [coin], outflow := 0 }

/-- **Another target is another scenario.** At the nodes the coercion armed, the hot spend's Normal path is
blocked and a non-hot target's reads open: `DUR-36` has "An armed node MUST sign a claw-back exactly as an idle
node does". This is the class's reading and not a signed claw-back: `Exhibits.Clawback.armed_signs_alike` runs one. Latched,
with node 3 dead, the same target reads blocked. -/
@[req "DUR-36"]
theorem other_target_other_scenario :
    let cl : Scenario :=
      { coin := coin, target := clawTx, userSigs := [{ msg := sighash clawTx 0, input := 0 }], hot := false }
    let ys := base toRelease ++
      [BtcPolicy.Recovery.Step.latch 1 (envAt 1000 1000), .latch 2 (envAt 1000 1000), .die 3]
    normalOpen rcfg (runOf v (base toRelease)).2 honest cl = true ∧
      normalOpen rcfg (runOf v (base toRelease ++ [.die 3])).2 honest cl = true ∧
      normalOpen rcfg (runOf v (base toRelease ++ [.die 3])).2 honest sc = false ∧
      isLegal v ys = true ∧ normalOpen rcfg (runOf v ys).2 honest cl = false := by
  decide +kernel

/-- **Sent, and the chain never takes it.** `coercedSteps` with no chain move: the Escape is out, the coin
stands in the waiting class, and the model holds no step that confirms it but the environment's
(`Recovery.no_inclusion_without_service`). -/
@[req "SEC-54"]
theorem sent_not_included :
    let p := runOf v (base coercedSteps)
    isLegal v (base coercedSteps) = true ∧ confirmedAt p.2.sw.truth es0.tx = false ∧
      failures rcfg p.2 p.1 honest sc = [.normalBlocked, .notMature, .awaitingInclusion] := by
  decide +kernel

end BtcPolicy.Exhibits.EndToEnd

namespace BtcPolicy.Exhibits.Clawback
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envAt envFire)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 escPsbt)
open BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Recovery

/-! ### A claw-back run through the composed model

Research task `bps-hmxr.1`. The model of `BtcPolicy.Exhibits.EndToEnd`, with a claw-back taken by
`Kernel.Event.clawback`: one ClawbackRequest over the request's one coin, paying the escape descriptor 97
where the Escape pays 98, checked by `Ingress.checkClawback` under `CHN-35`'s rule as it stands. Every
step is replayed through the actual transitions; the candidate is computed, never written by hand. -/

def clReq : Ingress.ClawbackRequest :=
  { member := ⟨{ escPsbt with txOutputs := [⟨[10, 0], 97⟩] }, 2, 0, none⟩, expiry := 2000 }

/-- The candidate the checks hand the kernel. -/
def cl0 : Cand := (Ingress.checkClawback ctx0 Classification.current clReq).getD es0

/-- `SPN-50`'s checks pass, and the claw-back is a transaction of its own over the Escape's coin, under a
commitment of its own, escape-class and not hot. -/
@[req "SPN-50"]
theorem checked_clawback :
    Ingress.checkClawback ctx0 Classification.current clReq = some cl0 ∧ cl0.hot = false ∧
      cl0.tx.inputs = es0.tx.inputs ∧ cl0.tx.id ≠ es0.tx.id ∧ cl0.id ≠ es0.id ∧
      Ingress.classOf ctx0 clReq.member = some .escape := by
  decide +kernel

def envCl : Env := envAt 70 20
def clIn (i : Nat) (env : Env := envCl) : Sweep.Step := .fed (.process i env (.clawback cl0))

/-- The claw-back's own steps: nodes 1 and 2 take it, each fire pass releases it, node 2's partial reaches
node 1, which assembles and sends. -/
def clSteps : List Sweep.Step :=
  [clIn 1, clIn 2, fire 1 envCl, fire 2 envCl, .fed (.deliverPartial 1 envCl (part cl0 2)),
    assemble 1 cl0.id envCl, send 1 cl0.id envCl]

/-- Nodes 1 and 2 take the checked request under duress, relay, and arm at their holder decisions:
`toRelease` before its fire passes. -/
def armedOnly : List Sweep.Step := toRelease.take 6

/-- After nodes 1 and 2 armed, and before their `T`. -/
def armedRun : List Sweep.Step := armedOnly ++ clSteps
/-- From the start, with no request and nothing armed. -/
def idleRun : List Sweep.Step := clSteps

/-- The claw-back's rows in the partial inventory. -/
def clRows (st : St) : List Exp := st.sw.fed.parts.filter (·.cid == cl0.id)

/-- **`DUR-36`, run.** "An armed node MUST sign a claw-back exactly as an idle node does": nodes 1 and 2,
armed at their holder decisions with the hot spend frozen and `T` at 95, take the claw-back at 70, during
`[arm, T]`; both release its partial, and node 1 assembles and submits its transaction. The same steps on
idle nodes leave the same claw-back rows and submit the same transaction. -/
@[req "DUR-36"]
theorem armed_signs_alike :
    let p := runOf v (base armedRun)
    let q := runOf v (base idleRun)
    isLegal v (base armedRun) = true ∧ isLegal v (base idleRun) = true ∧
      (p.2.sw.fed.worlds 1).node.armed = true ∧ (p.2.sw.fed.worlds 2).node.armed = true ∧
      (p.2.sw.fed.worlds 1).node.T = Wall.sample 95 ∧ (p.2.sw.fed.worlds 2).node.T = Wall.sample 95 ∧
      (p.2.sw.fed.worlds 1).node.cands.any (fun c => c.id == sp0.id && c.frozen) = true ∧
      (q.2.sw.fed.worlds 1).node.armed = false ∧ (q.2.sw.fed.worlds 2).node.armed = false ∧
      clRows p.2 = [part cl0 1, part cl0 2] ∧ clRows q.2 = clRows p.2 ∧
      Sweep.submits Kernel.current (runOf v (base armedRun.dropLast)).2.sw (send 1 cl0.id envCl) =
        [cl0.tx.id] ∧
      Sweep.submits Kernel.current (runOf v (base idleRun.dropLast)).2.sw (send 1 cl0.id envCl) =
        [cl0.tx.id] := by
  decide +kernel

/-- Every acceptance and every claw-back of the armed run is checked, and duress still withholds the hot
spend there: `Federation.cohort_no_exposed_quorum` through `EndToEnd.withholds_on`, with the claw-back's
request among the checked ones. -/
@[req "DUR-8"]
theorem withholds_beside_clawback :
    Ingress.CheckedTrace ctx0 (fedOf v (base armedRun)) ∧
      exposedQuorum { node := (worlds 1).node, exposure := (runOf v (base armedRun)).2.sw.fed.parts } sp0 =
        false :=
  ⟨Ingress.checkedTrace_of_claws ctx0 _ [req0] [clReq] (by decide +kernel) (by decide +kernel),
    withholds_on _ [clReq] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)⟩

/-- The claw-back read as a Normal-path target over the coin. -/
def clSc : Scenario :=
  { coin := coin, target := cl0.tx, userSigs := [{ msg := sighash cl0.tx 0, input := 0 }], hot := false }

def envLatch : Env := envAt 1000 1000
def envLater : Env := envAt 1010 1010

/-- Nodes 1 and 2 latch Lockdown at their deadline. -/
def latched : List BtcPolicy.Recovery.Step :=
  base toRelease ++ [BtcPolicy.Recovery.Step.latch 1 envLatch, .latch 2 envLatch]

/-- **`DUR-7`, run.** "After Lockdown a claw-back is refused with every other request" (`DUR-36`). A latched
node takes no claw-back step, before or after one is offered; node 3, not latched, takes it and releases
alone, one signer of the two needed, so the Normal path over this target is blocked. Before the latch the
same target reads open. The kernel's own refusal is `Kernel.clawback_refused_locked`. -/
@[req "DUR-7"]
theorem latched_refuses_clawback :
    let xs := latched ++ base [clIn 3 envLater, fire 3 envLater]
    let p := runOf v xs
    normalOpen rcfg (runOf v (base toRelease)).2 honest clSc = true ∧
      isLegal v xs = true ∧
      admits rcfg Kernel.current honest p.2 p.1 (.base (clIn 1 envLater)) = false ∧
      admits rcfg Kernel.current honest p.2 p.1 (.base (clIn 2 envLater)) = false ∧
      clRows p.2 = [part cl0 3] ∧
      normalOpen rcfg p.2 honest clSc = false := by
  decide +kernel

/-! #### What a resident or confirmed claw-back does to the Escape -/

/-- The claw-back resident in the mempool. -/
def vRes : Sweep.Backend := { v with sequence := 2, mempool := [(cl0.tx.id, cl0.tx.inputs)] }
/-- The claw-back confirmed at height 6, the coin spent. -/
def vMined : Sweep.Backend :=
  { v with
    tip := ⟨6, 106⟩, sequence := 2, confirmed := [], mined := [(cl0.tx.id, cl0.tx.inputs)],
    heights := [(cl0.tx.id, 6), (7, 3)], mtps := [(2, 1000), (5, 2000), (6, 2600)] }

/-- Before `T`: node 1's next sample, at 90. -/
def envPre : Env := envAt 90 30

/-- The armed run, with the claw-back submitted at 70; the chain moves through `bs` while node 1 reads each
instant; node 1 takes a fire pass at 90, before `T`, which releases nothing new; then, at 120, past `T`, both
fire passes release the Escape and node 2's partial reaches node 1. -/
def escapeAfter (bs : List Sweep.Backend) : List Sweep.Step :=
  armedRun ++ bs.flatMap (fun b => [.chain b, .observe 1 b]) ++
    [fire 1 envPre, fire 1 envFire, fire 2 envFire, .fed (.deliverPartial 1 envFire (part es0 2))]

/-- The Escape's guard at node 1, at the end of a schedule: coverage, ancestry, and whether its assembly is
admitted. -/
def escapeGuard (xs : List Sweep.Step) : Bool × Bool × Bool :=
  let p := runOf v (base xs)
  let A := Sweep.authorizedAt p.2.sw (sweepTrace p.1) 1
  let b := (p.2.sw.obs 1).getD v
  (Sweep.covered rcfg.sweep A (p.2.sw.fed.worlds 1).node b es0, Sweep.ancestryOk rcfg.sweep A b es0,
    Sweep.admits rcfg.sweep honest p.2.sw (sweepTrace p.1) (assemble 1 es0.id envFire))

/-- **`DUR-36`'s defeat, run.** "If it is still mempool-resident or confirmed when the Escape is evaluated,
the Escape releases nothing, failing no later than `DUR-21`'s ancestry step (`WTC-24`) and never at
coverage": the claw-back taken and submitted before `T`, at node 1's read of it resident, or confirmed, the
Escape released past `T` covers and fails ancestry, and its assembly is refused. "Accepting or signing the
claw-back alone settles nothing": with the claw-back signed and submitted and node 1 reading the vault
without it, the assembly is admitted. "One evicted before `T` leaves the Escape admissible": resident, then
gone, both in the schedule before node 1's step at 90, before `T` at 95, and node 1's samples increase along
it; the assembly at 120 is admitted. A chain move carries no clock of its own, so this is the sense of
"before `T`" the model has. The guard sits
at assembly, as in `Sweep`: `DUR-21`'s check before release is not modelled in `Sweep` (it is in
`Exhibits.PreRelease.clawback_residency_pair`), so the Escape's partials are
released in every case. -/
@[req "DUR-36"]
theorem resident_clawback_defeats_escape :
    isLegal v (base (escapeAfter [vRes, vMined])) = true ∧ isLegal v (base (escapeAfter [vRes, v])) = true ∧
      escapeGuard (escapeAfter [vRes]) = (true, false, false) ∧
      escapeGuard (escapeAfter [vMined]) = (true, false, false) ∧
      escapeGuard (escapeAfter [v]) = (true, true, true) ∧
      escapeGuard (escapeAfter [vRes, v]) = (true, true, true) := by
  decide +kernel

end BtcPolicy.Exhibits.Clawback

namespace BtcPolicy.Exhibits.LedgerSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.Admission (lfaithful lrun_faithful checked_on_ledger fed_bridge Counted nodeTrace)
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 lcfg checked_pair)
open BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Exhibits.TwoRun (tblD tblN)
open BtcPolicy.Recovery

/-! ### The Hot ledger and SILENCE on the end-to-end run

Research task `bps-hmxr.2`. The model of `BtcPolicy.Exhibits.EndToEnd` with each honest node's Hot
ledger carried: the run's federation steps (`Recovery.fedSteps`) taken through `FedSilence.lapply`
from `EndToEnd.fed0` with empty ledgers, cap 100 and window 600 (`Exhibits.Ingress.lcfg`). While gate 24
admits every acceptance (`Admission.lfaithful`, decided on the run), forgetting the ledgers leaves the
run's federation state and federation trace (`Admission.lrun_faithful`, `Recovery.fed_record`). The
composed state with its ledgers is `LSt`: the run's whole composed state, backend, observations,
custody, latches and submissions included, beside the replay's ledgers, and its federation part is the
replay's (`lstate_fed`). No ledger reads or moves a step that is not a federation step. A theorem of
`EndToEnd` about `runOf` is about that state's first part, and one about the federation trace is about
the replay's. `POL-20`'s bound is `Admission.fed_bridge` on the replay, and gate 24's verdict at each
acceptance is the one its own ledger gives (`Admission.checked_on_ledger`). SILENCE is
`FedSilence.fed_silence_adaptive_fresh` from the run's start: the coerced run against the same
schedule under the normal PIN. The run's backend and chain steps are not federation steps and are
not walked; on `coerced` they come after the horizon. -/

/-- The run's start, every honest ledger empty. -/
def L0 : LFed := { fed := fed0, leds := fun _ => [] }

/-- A composed schedule with the ledgers carried: its federation steps through `FedSilence.lapply`. -/
def ledgered (c : Config) (xs : List BtcPolicy.Recovery.Step) : LFed :=
  lrun Ledger.current c Kernel.current L0 (fedSteps xs)

/-- Gate 24 admits every acceptance of the schedule, over the ledgers it builds. -/
def faithful (c : Config) (xs : List BtcPolicy.Recovery.Step) : Bool :=
  lfaithful Ledger.current c Kernel.current L0 (fedSteps xs)

/-- **The ledgered run is the run.** For every composed schedule from `EndToEnd.st0` and every ledger
configuration: when gate 24 admits each acceptance over the ledgers the schedule builds, forgetting
the ledgers leaves the run's federation state and its federation trace. -/
theorem ledgered_is_run (c : Config) (b : Sweep.Backend) (xs : List BtcPolicy.Recovery.Step)
    (h : faithful c xs = true) :
    (ledgered c xs).fed = (runOf b xs).2.sw.fed ∧
      ltrace Ledger.current c Kernel.current [] L0 (fedSteps xs) = fedOf b xs := by
  obtain ⟨h1, h2⟩ := lrun_faithful Ledger.current c Kernel.current (fedSteps xs) [] L0 h
  obtain ⟨h3, h4⟩ := fed_record Kernel.current xs [] (st0 b)
  exact ⟨h1.trans h4.symm, h2.trans h3.symm⟩

/-- A composed state with each honest node's Hot ledger beside it. -/
structure LSt where
  st : St
  leds : Nat → Ledger

/-- A composed schedule's state with its ledgers: the run's composed state, and the ledgers its
federation steps build. -/
def lstate (c : Config) (b : Sweep.Backend) (xs : List BtcPolicy.Recovery.Step) : LSt :=
  { st := (runOf b xs).2, leds := (ledgered c xs).leds }

/-- **The ledgers in the composed state.** When gate 24 admits each acceptance, the federation part of
the composed state and its ledgers are exactly the ledgered replay. -/
theorem lstate_fed (c : Config) (b : Sweep.Backend) (xs : List BtcPolicy.Recovery.Step)
    (h : faithful c xs = true) :
    ({ fed := (lstate c b xs).st.sw.fed, leds := (lstate c b xs).leds } : LFed) = ledgered c xs := by
  have h1 := (ledgered_is_run c b xs h).1
  show ({ fed := (runOf b xs).2.sw.fed, leds := (ledgered c xs).leds } : LFed) = ledgered c xs
  rw [← h1]

theorem coerced_faithful : faithful lcfg (base coerced) = true := by decide +kernel

theorem coerced_trace : ltrace Ledger.current lcfg Kernel.current [] L0 (fedSteps (base coerced)) =
    fedOf v (base coerced) :=
  (ledgered_is_run lcfg v _ coerced_faithful).2

theorem coerced_checked_led :
    Ingress.CheckedTrace ctx0 (ltrace Ledger.current lcfg Kernel.current [] L0 (fedSteps (base coerced))) := by
  rw [coerced_trace]; exact coerced_checked.1

/-- **The ledgered history.** `coerced` with the honest nodes' Hot ledgers in its composed state: gate 24
admits both acceptances over the ledgers the run has built, the composed state's federation part and
ledgers are the ledgered replay (`lstate_fed`), so the federation state `duress_withholds` reads is the
replay's, and at the end nodes 1 and 2 each hold one
row, `req0`'s spend at its outflow of 55, unexposed, and node 3, which accepted nothing, none. Each
acceptance is `Ingress.check`'s with `fits` read from that node's ledger at that step. -/
@[req "POL-16"]
theorem coerced_ledgered :
    faithful lcfg (base coerced) = true ∧
      ({ fed := (lstate lcfg v (base coerced)).st.sw.fed, leds := (lstate lcfg v (base coerced)).leds } : LFed) =
        ledgered lcfg (base coerced) ∧
      (honest.map fun i => ((lstate lcfg v (base coerced)).leds i).map fun row =>
        (row.cid == sp0.id, row.amount, row.exposed)) = [[(true, 55, false)], [(true, 55, false)], []] ∧
      ∀ a b i env cid d E sp es, fedSteps (base coerced) = a ++ .process i env (.accept cid d E sp es) :: b →
        ∃ q, Ingress.check ctx0 (Ledger.admits lcfg (checked Ledger.current.release env lcfg.window
          ((lrun Ledger.current lcfg Kernel.current L0 a).leds i) (.accept cid d E sp es)) sp) q =
            .accepted sp es :=
  ⟨coerced_faithful, lstate_fed lcfg v _ coerced_faithful, by decide +kernel,
    fun _ _ _ _ _ _ _ _ _ h => checked_on_ledger coerced_checked_led coerced_faithful h⟩

/-- Each node's HotClock samples on the run are at or before 60. -/
def now : Nat → Mono := fun _ => Mono.sample 60
def cohort : List Ledgers.Spend := [(sp0.id, 55)]

theorem coerced_counted : ∀ i ∈ [1, 2],
    Counted Ledger.current lcfg Kernel.current L0 (fedSteps (base coerced)) i sp0.id (now i) := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨[], (fedSteps (base coerced)).drop 1, env0, 10, true, Wall.sample 200, sp0, es0,
      by decide +kernel, rfl, ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  · exact ⟨(fedSteps (base coerced)).take 1, (fedSteps (base coerced)).drop 2, env0, 10, true,
      Wall.sample 200, sp0, es0, by decide +kernel, rfl, ⟨by decide +kernel, by decide +kernel⟩,
      by decide +kernel, by decide +kernel⟩

/-- **`POL-20`'s bound on the end-to-end run.** `Admission.fed_bridge` at the honest nodes' cuts of the
ledgered `coerced`, `q = 2`: the two duress acceptances are counted at nodes 1 and 2, each at its own
ledger, and `hinv`, `hamt` and `hcohort` come from the run. -/
@[req "POL-20"]
theorem coerced_admission_bound : 2 * Ledgers.outflow cohort ≤ honest.length * lcfg.cap :=
  fed_bridge (g := Ledger.current) (cfg := lcfg) (r := Kernel.current) (F := L0)
    (ss := fedSteps (base coerced)) (t := []) (honest := honest) (ctx := ctx0) rfl rfl
    (fun _ _ => rfl) coerced_checked_led Ingress.code_injective 2 cohort (by decide +kernel)
    (fun s hs => by
      simp only [cohort, List.mem_singleton] at hs
      subst hs
      exact ⟨true, req0, sp0, es0, checked_pair.1, rfl, checked_pair.2.2.2.1⟩)
    now (by decide +kernel)
    (fun s hs => by
      simp only [cohort, List.mem_singleton] at hs
      subst hs
      exact ⟨[1, 2], by decide, by decide, fun i hi =>
        ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> decide,
          coerced_counted i hi⟩⟩)

/-! #### SILENCE on the run -/

/-- PIN 1 is the duress PIN at every node in the first family and an ordinary PIN in the second. -/
def tblsD : Nat → Enrolment := fun _ => tblD
def tblsN : Nat → Enrolment := fun _ => tblN

/-- Node `i` presents `req0` with PIN 1. -/
def request (i : Nat) : PStep := .input i env0 (.request 10 1 (Wall.sample 200) sp0 es0)

/-- `coerced`'s federation steps as the environment presents them: the requests carry the PIN, every
other step is the same in both families. -/
def sched : List PStep :=
  [request 1, request 2, .net (.emit 1 10), .net (.emit 2 10), .net (.deliver 1 env0 ⟨2, 10⟩),
   .net (.deliver 2 env0 ⟨1, 10⟩), .input 1 envFire (.pinless .firePass),
   .input 2 envFire (.pinless .firePass), .net (.deliverPartial 1 envFire (part es0 2)),
   .input 1 envFire (.pinless (.packageAccepted es0.id)), .input 1 envFire (.pinless (.send es0.id))]

/-- An observer that has seen `k` observations runs the `k`-th step of `sched`. -/
def replay : Observer where
  next h := sched[h.length]?

def apairs (c : Scheduler) (k : Nat) : List (FObs × FObs) :=
  awalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN c k L0 L0 [] []

/-- The ledgered run of the schedule's first `k` steps under one family. -/
def runK (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  lrun Ledger.current lcfg Kernel.current L0 ((sched.take k).map (·.step tbls))

theorem L0_fresh : Federation.Fresh honest L0.fed := (st0_fresh v).1.1

theorem L0_sweep : ∀ i ∈ honest, (L0.fed.worlds i).node.sweepActive = false := by decide

/-- **SILENCE from the end-to-end run's start.** `FedSilence.fed_silence_adaptive_fresh` at the values as
they stand, from `EndToEnd.fed0` with empty ledgers and the manifest's three nodes as peers: against
every observer, the two families emit equal observations at every step of the adaptive walk, which is
the fixed walk over the schedule the observer selects. -/
@[req "DUR-1"]
theorem silent_from_start (σ : Observer) (n : Nat) :
    awalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN σ.sched n L0 L0 [] [] =
        walk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN L0 L0
          (play Silence.current Ledger.current lcfg Kernel.current honest tblsD σ n L0 []) ∧
      ∀ y ∈ awalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN σ.sched n
        L0 L0 [] [], y.1 = y.2 :=
  fed_silence_adaptive_fresh rfl rfl rfl rfl rfl rfl honest honest tblsD tblsN L0 L0_fresh L0_sweep σ n

/-- **SILENCE on the coerced run.** The observer `replay` selects `sched` in both families; under the
duress family it is `coerced`'s federation schedule, and the ledgered run is `coerced` with its ledgers.
The walk is equal at every step it covers: six of the eleven, both requests, both relays emitted and
delivered, the two holder decisions that arm nodes 1 and 2 at `T = 95` in the first family and neither
in the second. It stops at node 1's first fire pass, past the duress family's `T`; the partials, the
read, the assembly, the send and the chain all lie beyond it. -/
@[req "DUR-1"]
theorem coerced_silent :
    (∀ y ∈ apairs replay.sched 11, y.1 = y.2) ∧
      sched.map (·.step tblsD) = fedSteps (base coerced) ∧
      play Silence.current Ledger.current lcfg Kernel.current honest tblsD replay 11 L0 [] = sched ∧
      (apairs replay.sched 11).length = 6 ∧
      ((runK tblsD 6).fed.worlds 1).node.armed = true ∧ ((runK tblsD 6).fed.worlds 2).node.armed = true ∧
      ((runK tblsD 6).fed.worlds 1).node.T = Wall.sample 95 ∧
      ((runK tblsN 6).fed.worlds 1).node.armed = false ∧ ((runK tblsN 6).fed.worlds 2).node.armed = false :=
  ⟨(silent_from_start replay 11).2, by decide +kernel⟩

/-! #### Where the relation stops, and what it needs -/

/-- Node 1's first fire pass. -/
def fire1 : PStep := .input 1 envFire (.pinless .firePass)

/-- **The horizon is where the runs part.** At node 1's fire pass the duress family's node 1 is armed with
`T` reached and outside its horizon, and the normal family's is inside. Computed beside the walk, the
step queues node 1's Escape partial in the first family and nothing in the second. -/
@[req "DUR-7"]
theorem coerced_parts_at_fire :
    sched.drop 6 = fire1 :: sched.drop 7 ∧
      inside Kernel.current (runK tblsD 6) (fire1.step tblsD) = false ∧
      inside Kernel.current (runK tblsN 6) (fire1.step tblsN) = true ∧
      (fobs Silence.current Ledger.current lcfg Kernel.current honest (runK tblsD 6) (fire1.step tblsD)).parts =
        [part es0 1] ∧
      (fobs Silence.current Ledger.current lcfg Kernel.current honest (runK tblsN 6) (fire1.step tblsN)).parts =
        [] := by
  decide +kernel

/-- A scheduler that reads node 1's arm bit, which no observation carries: after the six steps it runs a
tick at node 1 if node 1 is armed and at node 2 if not. -/
def peek : Scheduler := fun F h =>
  if h.length = 6 then
    some (.input (if (F.fed.worlds 1).node.armed then 1 else 2) env0 (.pinless .tick))
  else replay.next h

/-- **The observer premise.** The hidden-state reader distinguishes the families on the coerced run's
prefix, inside the horizon: equal for six steps, then node 1 acts in the duress family and node 2 in the
normal one. It is not an `FedSilence.Observer`. -/
@[req "DUR-1"]
theorem arm_reader_leaks :
    ((apairs peek 7).map fun y => y.1 == y.2) = [true, true, true, true, true, true, false] ∧
      ((apairs peek 7).drop 6).map (fun y => (y.1.node.map (·.1), y.2.node.map (·.1))) =
        [(some 1, some 2)] ∧
      ¬ ∃ σ : Observer, σ.sched = peek := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨σ, hσ⟩
  have h0 := congrFun (congrFun hσ (runK tblsD 6)) ((apairs peek 6).map Prod.fst)
  have h1 := congrFun (congrFun hσ (runK tblsN 6)) ((apairs peek 6).map Prod.fst)
  simp only [Observer.sched] at h0 h1
  have hne : peek (runK tblsD 6) ((apairs peek 6).map Prod.fst) ≠
      peek (runK tblsN 6) ((apairs peek 6).map Prod.fst) := by
    decide +kernel
  exact hne (h0.symm.trans h1)

/-- `Exhibits.Clawback.armedRun`'s federation steps: the six steps that arm nodes 1 and 2, then the
claw-back at both. -/
def clSched : List PStep :=
  sched.take 6 ++ [.input 1 Clawback.envCl (.pinless (.clawback Clawback.cl0)),
    .input 2 Clawback.envCl (.pinless (.clawback Clawback.cl0))]

/-- Node 1 after it takes the claw-back from the start, idle. -/
def idleClaw : Node :=
  ((lapply Ledger.current lcfg Kernel.current L0 (.process 1 Clawback.envCl (.clawback Clawback.cl0))).fed.worlds 1).node

/-- **The claw-back was outside the earlier walk.** Against the walk as it stood before claw-back
ingress was admitted (`FedSilence.walkPre`, `Silence.wfEventPre`), the claw-back run covers the same
six steps and stops at the claw-back's ingress at 70, although node 1 is inside its horizon there
(`T` at 95). The reason it was refused: `Silence.NodeInv.noWindow` then asked every candidate no
selected entry acts on to carry no window close, and the claw-back is born with one
(`Kernel.clawbackBorn`), here at 110 on an idle node. The restated clause admits that unpaired, not
hot singleton, and the expanded walk goes through the same ingress
(`Exhibits.ClawSilence.clawback_inside_walk`). -/
@[req "DUR-36"]
theorem clawback_outside_walk :
    (walkPre Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN L0 L0 clSched).length = 6 ∧
      preHorizon Kernel.current Clawback.envCl ((runK tblsD 6).fed.worlds 1).node = true ∧
      insidePre Kernel.current (runK tblsD 6) ((.process 1 Clawback.envCl (.clawback Clawback.cl0) : Federation.Step)) = false ∧
      faithful lcfg (base Clawback.armedRun) = true ∧
      idleClaw.cands.map (fun c => (selEsc Kernel.current (selIds idleClaw) c, c.windowClose)) =
        [(false, some (Wall.sample 110))] := by
  decide +kernel

/-- **What the ledger adds.** `EndToEnd.tooLate` takes a second request over the same transaction under a
new commitment at nodes 1 and 2 while the first reservation of 55 stands. Under `F63`'s settled reading
each commitment is booked in full, so at cap 100 gate 24 refuses it: the schedule is not faithful, and the
ledgered run stages that request instead of registering it. `duress_too_late`'s outcome survives: both
nodes still end armed, and the inventory still holds the hot spend's quorum. At a cap of 110 the
history is the ledgered run as written. -/
@[req "POL-16"]
theorem too_late_needs_budget :
    faithful lcfg (base tooLate) = false ∧
      ((runOf v (base tooLate)).2.sw.fed.worlds 1).node.cands.any (·.id == sp1.id) = true ∧
      ((ledgered lcfg (base tooLate)).fed.worlds 1).node.cands.any (·.id == sp1.id) = false ∧
      ((ledgered lcfg (base tooLate)).fed.worlds 1).node.armed = true ∧
      ((ledgered lcfg (base tooLate)).fed.worlds 2).node.armed = true ∧
      exposedQuorum { node := (worlds 1).node, exposure := (ledgered lcfg (base tooLate)).fed.parts } sp0 = true ∧
      faithful { lcfg with cap := 110 } (base tooLate) = true := by
  decide +kernel

/-- The other histories of `EndToEnd` are faithful at cap 100: the ordinary path, the third signer, the copied
keys and the uncovered vault each keep every acceptance, so each is its own ledgered run. -/
theorem others_faithful :
    faithful lcfg (base ordinaryAll) = true ∧ faithful lcfg (base thirdSigns) = true ∧
      faithful lcfg (base keysCopied) = true ∧ faithful lcfg (base (toRead vLarge)) = true := by
  decide +kernel

end BtcPolicy.Exhibits.LedgerSilence

namespace BtcPolicy.Exhibits.ClawSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 lcfg)
open BtcPolicy.Exhibits.EndToEnd (honest part)
open BtcPolicy.Exhibits.LedgerSilence (L0 L0_fresh L0_sweep sched tblsD tblsN silent_from_start)
open BtcPolicy.Exhibits.Clawback (cl0 envCl)

/-! ### SILENCE through claw-back ingress

Research task `bps-9oab.2`, first part. The end-to-end run of `Exhibits.LedgerSilence`: nodes 1 and 2
take `req0` with PIN 1, which arms them at their holder decisions with `T` at 95 in the duress family
and leaves them unarmed in the normal family; both families start from `LedgerSilence.L0` and emit
equal observations over those six steps. Then the claw-back of `Exhibits.Clawback`, checked by
`Ingress.checkClawback`, is taken by `Kernel.Event.clawback`, its post-check registration, at nodes 1
and 2 at 70, before `T`, and runs on to its submission. Every step is the actual ledgered composed
transition; the observer is a `FedSilence.Observer`. The handler's retained-replay log
(`ClawbackIngress.lookup`) and the relay of the claw-back request are not in this run. -/

/-- A backward sample at node 1, below the claw-back's ingress sample, and a later one. -/
def envBack : Env := envAt 60 22
def envD : Env := envAt 80 30

/-- The six arming steps, then: the claw-back at nodes 1 and 2 at 70; node 1's fire pass at the
backward sample 60, then at 70, where the singleton's window opens; node 2's fire pass at 70; node
2's partial delivered to node 1 later, at 80; node 1's package check and its send at 80. -/
def clSteps : List PStep :=
  [.input 1 envCl (.pinless (.clawback cl0)), .input 2 envCl (.pinless (.clawback cl0)),
   .input 1 envBack (.pinless .firePass), .input 1 envCl (.pinless .firePass),
   .input 2 envCl (.pinless .firePass), .net (.deliverPartial 1 envD (part cl0 2)),
   .input 1 envD (.pinless (.packageAccepted cl0.id)), .input 1 envD (.pinless (.send cl0.id))]

def clSched : List PStep := sched.take 6 ++ clSteps

/-- An observer that has seen `k` observations runs the `k`-th step of `clSched`. -/
def replay : Observer where
  next h := clSched[h.length]?

def apairs (n : Nat) : List (FObs × FObs) :=
  awalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN replay.sched n
    L0 L0 [] []

/-- The ledgered run of `clSched`'s first `k` steps under one family. -/
def runK (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  lrun Ledger.current lcfg Kernel.current L0 ((clSched.take k).map (·.step tbls))

/-- The response a step's acting node gives, if one acts. -/
def resp (y : FObs) : Option Resp := y.node.map (·.2.resp)

/-- The claw-back rows in the partial inventory a step leaves. -/
def clRows (y : FObs) : List Exp := y.parts.filter (·.cid == cl0.id)

/-- **A claw-back inside the walk.** From one start, the adaptive walk covers all fourteen steps:
the six that arm nodes 1 and 2 at `T = 95` in the duress family and leave them unarmed in the
normal one, and the claw-back's eight, all before `T`. The two families emit equal observations at
every step (`Exhibits.LedgerSilence.silent_from_start`). Each node answers the claw-back `Accepted`
under its commitment id with `first_seen` and `fire_at` both at 70, `SPN-51`'s
"`remaining_secs = 0`". Node 1's fire pass at the backward sample 60 releases nothing, the window
being `[70, 110]`; at 70 nodes 1 and 2 each release one partial, node 2's reaches node 1 later, and
node 1 submits the claw-back's transaction, in both families. -/
@[req "DUR-36"]
theorem clawback_inside_walk :
    (∀ y ∈ apairs 14, y.1 = y.2) ∧
      play Silence.current Ledger.current lcfg Kernel.current honest tblsD replay 14 L0 [] = clSched ∧
      (apairs 14).length = 14 ∧
      ((runK tblsD 6).fed.worlds 1).node.armed = true ∧ ((runK tblsD 6).fed.worlds 2).node.armed = true ∧
      ((runK tblsD 6).fed.worlds 1).node.T = Wall.sample 95 ∧
      ((runK tblsN 6).fed.worlds 1).node.armed = false ∧ ((runK tblsN 6).fed.worlds 2).node.armed = false ∧
      (((apairs 14).drop 6).take 2).map (fun y => (resp y.1, resp y.2)) =
        [(some (.accepted cl0.id (Effective.ofWall (Wall.sample 70) (HighWater.sample 0))
            (some (Wall.sample 70))),
          some (.accepted cl0.id (Effective.ofWall (Wall.sample 70) (HighWater.sample 0))
            (some (Wall.sample 70)))),
         (some (.accepted cl0.id (Effective.ofWall (Wall.sample 70) (HighWater.sample 0))
            (some (Wall.sample 70))),
          some (.accepted cl0.id (Effective.ofWall (Wall.sample 70) (HighWater.sample 0))
            (some (Wall.sample 70))))] ∧
      ((apairs 14).drop 8).map (fun y => (clRows y.1).length) = [0, 1, 2, 2, 2, 2] ∧
      ((apairs 14).getLast?.map fun y => y.1.node.map (·.2.effects)) =
        some (some [.broadcast cl0.tx.id]) :=
  ⟨(silent_from_start replay 14).2, by decide +kernel⟩

/-- A claw-back byte-identical to the resident pair's Escape, `Exhibits.Collision.checked_identity`'s
candidate, offered at node 1 at 70 after the six arming steps. -/
def collSched : List PStep := sched.take 6 ++ [.input 1 envCl (.pinless (.clawback es0))]

def collPairs : List (FObs × FObs) :=
  walk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN L0 L0 collSched

def collRun (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  lrun Ledger.current lcfg Kernel.current L0 ((collSched.take k).map (·.step tbls))

/-- **The collision refusal, in both families.** Node 1 holds `req0`'s pair, armed in the duress family
and not in the normal one. The claw-back whose commitment id is that pair's Escape's is answered
`PSBT_INCONSISTENT` / `candidate_identity` in both, inside the walk and with equal observations, and
node 1's registry is the one it held before: the resident pair is kept. -/
@[req "SPN-51"]
theorem collision_both_families :
    (∀ y ∈ collPairs, y.1 = y.2) ∧ collPairs.length = 7 ∧
      (collPairs.drop 6).map (fun y => (resp y.1, resp y.2)) =
        [(some (.refusal .PSBT_INCONSISTENT "candidate_identity"),
          some (.refusal .PSBT_INCONSISTENT "candidate_identity"))] ∧
      ((collRun tblsD 7).fed.worlds 1).node = ((collRun tblsD 6).fed.worlds 1).node ∧
      ((collRun tblsN 7).fed.worlds 1).node = ((collRun tblsN 6).fed.worlds 1).node ∧
      ((collRun tblsD 6).fed.worlds 1).node.armed = true ∧
      ((collRun tblsD 6).fed.worlds 1).node.cands.any (·.id == es0.id) = true :=
  ⟨fed_silence_fresh rfl rfl rfl rfl rfl rfl honest honest tblsD tblsN L0 L0_fresh L0_sweep collSched,
    by decide +kernel⟩

/-- The same claw-back offered at node 1 at 120, past the duress family's `T`. -/
def lateSched : List PStep := sched.take 6 ++ [.input 1 envFire (.pinless (.clawback cl0))]

def lateRun (tbls : Nat → Enrolment) : LFed :=
  lrun Ledger.current lcfg Kernel.current L0 ((sched.take 6).map (·.step tbls))

/-- **A genuine horizon crossing.** At 120 the duress family's node 1 is armed with `T = 95` reached,
outside its horizon, and the normal family's is inside: the walk covers the six arming steps and
stops at the claw-back. The stop is the horizon's, not the claw-back's: the shape boundary admits it
(`Silence.wfEvent_clawback_escapeRole`). -/
@[req "DUR-7"]
theorem late_clawback_stops :
    (walk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN L0 L0 lateSched).length = 6 ∧
      inside Kernel.current (lateRun tblsD) (.process 1 envFire (.clawback cl0)) = false ∧
      inside Kernel.current (lateRun tblsN) (.process 1 envFire (.clawback cl0)) = true ∧
      wfEvent Kernel.current ((lateRun tblsD).fed.worlds 1).node (.clawback cl0) = true := by
  decide +kernel

end BtcPolicy.Exhibits.ClawSilence

namespace BtcPolicy.Exhibits.EscapeCustody
open BtcPolicy.Kernel BtcPolicy.Clocks
open BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Exhibits.Ingress (es0)
open BtcPolicy.EscapeCustody

/-! ### The same submitted destinations, different escape authority
`bps-hmxr.3`: the checked Escape of `EndToEnd.coerced` and the checked claw-back of
`Clawback.armedRun`, each followed by its explicit chain inclusion. The custody prefix alone changes;
the composed run is projected back exactly. A 2-of-3 supplied escape wallet is assumed to be the
checked destination. This is abstract authority at inclusion, not a signing or hardware experiment. -/

def wallet : Wallet := { keys := [21, 22, 23], k := 2 }
def initial : Custody :=
  { keys := fun p => if p == 0 then [21, 22, 23] else [], lost := fun _ => [] }
def start : St := { base := st0 v, custody := initial }
def lift (xs : List BtcPolicy.Recovery.Step) : List Step := xs.map .base
/-- One coercer obtains two distinct usable keys. The Operator then loses those keys and backups. -/
def stolen : List Step := [.copy 1 21, .copy 1 22, .lose 0 21, .lose 0 22]
/-- Nobody else holds a key; the Operator loses two of three, backups included. -/
def lost : List Step := [.lose 0 21, .lose 0 22]

def run (xs : List Step) : Trace × St := record Kernel.current [] start xs
def lawful (xs : List Step) : Bool := legal rcfg Kernel.current honest [] start xs

theorem execution (xs : List Step) (h : lawful xs = true) :
    Execution rcfg Kernel.current honest (run xs).1 (run xs).2 :=
  execution_of_legal (.init _ (st0_fresh v)) h

/-- The chain's inclusion remains an explicit step, for both routes. -/
def sweepRoute : List BtcPolicy.Recovery.Step := base coerced
def clawRoute : List BtcPolicy.Recovery.Step := base (Clawback.armedRun ++ [.chain Clawback.vMined])

/-- Initial authority is the Operator's alone. The universal quantifier covers every other holder. -/
theorem initial_denial : Reads wallet initial .denial := by
  refine ⟨by decide +kernel, ?_⟩
  intro p hp
  simp [capable, heldKeys, wallet, initial, hp]

/-- A coercer retains authority after the Operator's loss: losing E is not global Loss. -/
theorem stolen_theft : Reads wallet (run stolen).2.custody .theft ∧
    capable wallet (run stolen).2.custody 0 = false ∧
    ¬ Reads wallet (run stolen).2.custody .loss := by
  have h : capable wallet (run stolen).2.custody 1 = true := by decide +kernel
  exact ⟨⟨1, by decide, h⟩, by decide +kernel, retained_not_loss _ _ _ h⟩

/-- Nobody retains E. This is not inferred merely from the Operator's loss. -/
theorem lost_loss : Reads wallet (run lost).2.custody .loss := by
  intro p
  by_cases hp : p = 0
  · subst p; decide +kernel
  · simp [run, lost, start, record, apply, capable, heldKeys, initial, hp, wallet]

/-- Copying one key twice is still one key, and a permanently lost key cannot be copied back. -/
@[req "SEC-54"]
theorem duplicates_and_permanent_loss :
    (0 < wallet.k ∧ wallet.k ≤ wallet.keys.eraseDups.length) ∧
      capable wallet (run [.copy 1 21, .copy 1 21]).2.custody 1 = false ∧
      admits rcfg Kernel.current honest (run lost).2 (run lost).1 (.copy 0 21) = false ∧
      capable wallet (run (lost ++ [.copy 0 21])).2.custody 0 = false := by
  decide +kernel

/-- Environment prefixes project away, leaving exactly the old trace and state for either route.
Every custody variant is a reachable execution; node steps keep the same custody reading through
inclusion. No additional node, ledger, chain or signature step is introduced. -/
theorem routes_project (pre : List Step) (hp : pre = [] ∨ pre = stolen ∨ pre = lost)
    (route : List BtcPolicy.Recovery.Step) (hr : route = sweepRoute ∨ route = clawRoute) :
    lawful (pre ++ lift route) = true ∧
      baseTrace (run (pre ++ lift route)).1 = (runOf v route).1 ∧
      (run (pre ++ lift route)).2.base = (runOf v route).2 ∧
      (run (pre ++ lift route)).2.custody = (run pre).2.custody := by
  rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl <;>
    exact ⟨by decide +kernel, rfl, rfl, rfl⟩

/-- Operator-only authority: the swept or clawed-back destination reads Denial, given the unwanted
delay. The model does not derive the Operator's wishes or a latency bound. -/
@[req "SEC-54"]
theorem operator_destinations :
    Delivered wallet (run (lift sweepRoute)).2 es0.tx .denial ∧
      Delivered wallet (run (lift clawRoute)).2 Clawback.cl0.tx .denial := by
  constructor <;> refine ⟨?_, by decide +kernel, initial_denial⟩
  · exact ⟨true, by decide +kernel⟩
  · exact ⟨false, by decide +kernel⟩

/-- Coercer authority: the same confirmed destinations read Theft. -/
@[req "SEC-54"]
theorem coercer_destinations :
    Delivered wallet (run (stolen ++ lift sweepRoute)).2 es0.tx .theft ∧
      Delivered wallet (run (stolen ++ lift clawRoute)).2 Clawback.cl0.tx .theft := by
  constructor <;> refine ⟨?_, by decide +kernel, stolen_theft.1⟩
  · exact ⟨true, by decide +kernel⟩
  · exact ⟨false, by decide +kernel⟩

/-- No holder retains authority: the same confirmed destinations read Loss. This quantifies over
all holder identities; it assumes initial custody and permanent loss are accurately supplied. -/
@[req "SEC-54"]
theorem lost_destinations :
    Delivered wallet (run (lost ++ lift sweepRoute)).2 es0.tx .loss ∧
      Delivered wallet (run (lost ++ lift clawRoute)).2 Clawback.cl0.tx .loss := by
  constructor <;> refine ⟨?_, by decide +kernel, lost_loss⟩
  · exact ⟨true, by decide +kernel⟩
  · exact ⟨false, by decide +kernel⟩

/-- Submission alone is not arrival: the same sweep stopped before the chain's move. -/
theorem sent_is_not_arrival :
    lawful (lift (base coercedSteps)) = true ∧
      (true, es0.tx) ∈ (run (lift (base coercedSteps))).2.base.sent ∧
      Settlement.confirmedAt (run (lift (base coercedSteps))).2.base.sw.truth es0.tx = false := by
  decide +kernel

end BtcPolicy.Exhibits.EscapeCustody

namespace BtcPolicy.Exhibits.Collision
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Exhibits.Ingress (ctx0 req0 es0)
open BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Recovery

/-- Same complete decoded member and expiry, not merely equal sequence and lock time. -/
def request : Ingress.ClawbackRequest := ⟨req0.escape, req0.expiry⟩

@[req "SPN-51"]
theorem checked_identity :
    Ingress.checkClawback ctx0 Classification.current request = some es0 ∧
      Ingress.clawCommitment ctx0 request = Ingress.commitment ctx0 req0 req0.escape := by
  decide +kernel

/-- Pair residency is reached through the existing composed transitions, under either PIN. -/
def idlePrefix : List Sweep.Step := [acc 1 10 false]
def idle : Node := ((runOf v (base idlePrefix)).2.sw.fed.worlds 1).node
def armed : Node := ((runOf v (base Clawback.armedOnly)).2.sw.fed.worlds 1).node

@[req "SPN-51"]
theorem pair_collision :
    isLegal v (base idlePrefix) = true ∧ isLegal v (base Clawback.armedOnly) = true ∧
      idle.armed = false ∧ armed.armed = true ∧
      BtcPolicy.ClawbackIngress.register Clawback.envCl idle es0 =
        (idle, some ⟨.PSBT_INCONSISTENT, "candidate_identity"⟩) ∧
      BtcPolicy.ClawbackIngress.register Clawback.envCl armed es0 =
        (armed, some ⟨.PSBT_INCONSISTENT, "candidate_identity"⟩) := by
  decide +kernel

/-- A different checked singleton still succeeds; the existing armed/idle run carries its release. -/
@[req "SPN-51"]
theorem fresh_singleton :
    (BtcPolicy.ClawbackIngress.register Clawback.envCl idle Clawback.cl0).2 = none ∧
      (BtcPolicy.ClawbackIngress.register Clawback.envCl idle Clawback.cl0).1.cands.any
        (fun c => c.id == Clawback.cl0.id && c.pair.isNone && c.quorum) = true ∧
      BtcPolicy.ClawbackIngress.register Clawback.envCl { idle with lockedDown := true } es0 =
        ({ idle with lockedDown := true }, some ⟨.FRAUD_SUSPECTED, "lockdown"⟩) := by
  decide +kernel

/-- Symbolic supplied byte strings exercise exact-byte matching; they are not serialized PSBTs. -/
def key : BtcPolicy.ClawbackIngress.Key := ⟨.clawback, 7, [1, 2]⟩
def metadata : BtcPolicy.ClawbackIngress.Key := { key with psbt := [1, 3] }
def pairKey : BtcPolicy.ClawbackIngress.Key := { key with role := .spend }
def log : List BtcPolicy.ClawbackIngress.Entry := [⟨key, [42]⟩]

@[req "SPN-50"]
theorem retry_keys :
    BtcPolicy.ClawbackIngress.lookup log key = some [42] ∧
      BtcPolicy.ClawbackIngress.lookup [⟨pairKey, [42]⟩] key = none ∧
      BtcPolicy.ClawbackIngress.lookup log metadata = none ∧
      BtcPolicy.ClawbackIngress.lookup log { key with id := 8 } = none := by
  decide

@[req "SPN-50"]
theorem retry_retains_first :
    BtcPolicy.ClawbackIngress.retain log key [99] = log ∧
      BtcPolicy.ClawbackIngress.retain log metadata [99] = log ++ [⟨metadata, [42]⟩] ∧
      BtcPolicy.ClawbackIngress.lookup (BtcPolicy.ClawbackIngress.retain log metadata [99]) key = some [42] ∧
      BtcPolicy.ClawbackIngress.lookup (BtcPolicy.ClawbackIngress.retain log metadata [99]) metadata = some [42] := by
  decide

/-- Even a progressed/terminal resident is not reborn by a retained response. -/
@[req "SPN-50"]
theorem replay_keeps_lifecycle (n : Node) :
    (BtcPolicy.ClawbackIngress.replay n [42]).1 = n ∧
      (BtcPolicy.ClawbackIngress.replay n [42]).2 = [42] := by
  exact BtcPolicy.ClawbackIngress.replay_preserves n [42]

end BtcPolicy.Exhibits.Collision

namespace BtcPolicy.Exhibits.ClawHandler
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.ClawHandler (HFed HStep HObserver Request hwalk hawalk hplay happly caseOf hit
  hfed_silence_fresh hfed_silence_adaptive_fresh replay_unchanged)
open BtcPolicy.Kernel.RegistrationCases (envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 es0 lcfg)
open BtcPolicy.Exhibits.EndToEnd (honest part)
open BtcPolicy.Exhibits.LedgerSilence (L0 L0_fresh L0_sweep sched tblsD tblsN)
open BtcPolicy.Exhibits.Clawback (cl0 envCl clReq)
open BtcPolicy.Exhibits.ClawSilence (envBack envD)

/-! ### The claw-back handler's acceptance log inside the walk

Research task `bps-9oab.2`, second part. The run of `Exhibits.ClawSilence` with the claw-back taken
through the handler (`BtcPolicy.ClawHandler`): after the six steps of `Exhibits.LedgerSilence` that
arm nodes 1 and 2 at `T = 95` in the duress family and leave them unarmed in the normal family, each
ClawbackRequest at a node is looked up in that node's acceptance log before fresh evaluation. Every
step is the actual handler transition over the ledgered composed step; the observer is a
`ClawHandler.HObserver`. PSBT bytes are supplied values; no serializer, nonce generator or signer is
modelled, and the relay and re-relay of a request are not in the run. -/

/-- The handler's start: `LedgerSilence.L0`, every acceptance log empty. -/
def H0 : HFed := { L := L0, logs := fun _ => [] }

/-- Two supplied decoded PSBT byte strings under one commitment. -/
def pA : Encode.Bytes := [1, 1]
def pB : Encode.Bytes := [1, 2]

/-- The checked claw-back of `Exhibits.Clawback` as a ClawbackRequest. -/
def q0 : Request := { nonce := 1, psbt := pA, cand := cl0 }

/-- `SPN-51`'s answer to the claw-back registered at 70: `remaining_secs = 0`. -/
def acc0 : Resp := .accepted cl0.id (Effective.ofWall (Wall.sample 70) (HighWater.sample 0))
  (some (Wall.sample 70))

/-- The handler steps after the six arming steps: the request at nodes 1 and 2 at 70; at node 1 its
exact retry with another nonce, then the same commitment with other PSBT bytes; node 1's fire pass at
the backward sample 60, then node 1's and node 2's at 70; at 80 another exact retry at node 1 after its
release; node 2's partial delivered to node 1 at 80, and again; node 1's package check and its send at
80. Node 2's partial is addressed to node 3 and never delivered there. -/
def hsteps : List HStep :=
  [.claw 1 envCl q0, .claw 2 envCl q0, .claw 1 envCl { q0 with nonce := 2 },
   .claw 1 envCl { q0 with nonce := 3, psbt := pB },
   .step (.input 1 envBack (.pinless .firePass)), .step (.input 1 envCl (.pinless .firePass)),
   .step (.input 2 envCl (.pinless .firePass)), .claw 1 envD { q0 with nonce := 4 },
   .step (.net (.deliverPartial 1 envD (part cl0 2))), .step (.net (.deliverPartial 1 envD (part cl0 2))),
   .step (.input 1 envD (.pinless (.packageAccepted cl0.id))), .step (.input 1 envD (.pinless (.send cl0.id)))]

def hsched : List HStep := (sched.take 6).map .step ++ hsteps

/-- An observer that has seen `k` observations runs the `k`-th step of `hsched`. -/
def hreplay : HObserver where
  next h := hsched[h.length]?

def hapairs (n : Nat) : List (FObs × FObs) :=
  hawalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN hreplay.sched n
    H0 H0 [] []

/-- The handler run of a schedule's first `k` steps under one family. -/
def hrun (tbls : Nat → Enrolment) : Nat → HFed → List HStep → HFed
  | 0, F, _ => F
  | _, F, [] => F
  | k + 1, F, s :: ss => hrun tbls k (happly Ledger.current lcfg Kernel.current tbls F s) ss

def resp (y : FObs) : Option Resp := y.node.map (·.2.resp)

/-- **The handler inside the walk.** From one start, the adaptive walk covers all eighteen steps, and
the two families emit equal observations at every one (`ClawHandler.hfed_silence_adaptive_fresh`).
Nodes 1 and 2 answer the fresh request `Accepted` with `first_seen` and `fire_at` at 70. Node 1's
exact retry with another nonce is a replay in both families and answers that `Accepted`; the request
with other PSBT bytes under the same commitment misses the lookup and is evaluated afresh, which
over the resident singleton changes nothing and answers the same `Accepted`; the log then holds both
keys, each beside the first `Accepted`. The fire pass at the backward sample 60 queues nothing; at 70
each node queues one partial; the retry at 80, after release, is again a replay. Node 2's partial
reaches node 1 at 80 twice and node 3 never; node 1 submits the claw-back's transaction. In both
families. -/
@[req "SPN-50"]
theorem handler_inside_walk :
    (∀ y ∈ hapairs 18, y.1 = y.2) ∧
      hplay Silence.current Ledger.current lcfg Kernel.current honest tblsD hreplay 18 H0 [] = hsched ∧
      (hapairs 18).length = 18 ∧
      ((hrun tblsD 6 H0 hsched).L.fed.worlds 1).node.armed = true ∧
      ((hrun tblsD 6 H0 hsched).L.fed.worlds 1).node.T = Wall.sample 95 ∧
      ((hrun tblsN 6 H0 hsched).L.fed.worlds 1).node.armed = false ∧
      ((hapairs 18).drop 6).map (fun y => (resp y.1, resp y.2)) =
        [(some acc0, some acc0), (some acc0, some acc0), (some acc0, some acc0), (some acc0, some acc0),
         (some .silent, some .silent), (some .silent, some .silent), (some .silent, some .silent),
         (some acc0, some acc0), (some .silent, some .silent), (some .silent, some .silent),
         (some .silent, some .silent), (some .silent, some .silent)] ∧
      caseOf (hrun tblsD 8 H0 hsched) 1 { q0 with nonce := 2 } = .replay acc0 ∧
      caseOf (hrun tblsN 8 H0 hsched) 1 { q0 with nonce := 2 } = .replay acc0 ∧
      caseOf (hrun tblsD 9 H0 hsched) 1 { q0 with nonce := 3, psbt := pB } = .fresh ∧
      caseOf (hrun tblsN 9 H0 hsched) 1 { q0 with nonce := 3, psbt := pB } = .fresh ∧
      ((hrun tblsD 10 H0 hsched).L.fed.worlds 1).node = ((hrun tblsD 9 H0 hsched).L.fed.worlds 1).node ∧
      (hrun tblsD 18 H0 hsched).logs 1 =
        [⟨q0.key, acc0⟩, ⟨({ q0 with psbt := pB } : Request).key, acc0⟩] ∧
      (hrun tblsN 18 H0 hsched).logs 1 = (hrun tblsD 18 H0 hsched).logs 1 ∧
      caseOf (hrun tblsD 13 H0 hsched) 1 { q0 with nonce := 4 } = .replay acc0 ∧
      ((hapairs 18).drop 10).map (fun y => ((y.1.parts.filter (·.cid == cl0.id)).length, y.1.recv)) =
        [(0, none), (1, none), (2, none), (2, none), (2, some ⟨2, 1, .part (part cl0 2)⟩),
         (2, some ⟨2, 1, .part (part cl0 2)⟩), (2, none), (2, none)] ∧
      ((hapairs 18).getLast?.map fun y => y.1.node.map (·.2.effects)) =
        some (some [.broadcast cl0.tx.id]) :=
  ⟨(hfed_silence_adaptive_fresh rfl rfl rfl rfl rfl rfl honest honest tblsD tblsN H0 L0_fresh L0_sweep
      hreplay 18).2, by decide +kernel⟩

/-- **The retry changes nothing.** Node 1's exact retry with another nonce leaves the whole handler
state as it was, in each family, by `ClawHandler.replay_unchanged` on the hit the log gives. -/
@[req "SPN-50"]
theorem retry_changes_nothing (tbls : Nat → Enrolment) (htbls : tbls = tblsD ∨ tbls = tblsN) :
    happly Ledger.current lcfg Kernel.current tbls (hrun tbls 8 H0 hsched) (.claw 1 envCl { q0 with nonce := 2 }) =
      hrun tbls 8 H0 hsched := by
  have h : hit (hrun tbls 8 H0 hsched) 1 { q0 with nonce := 2 } = some acc0 := by
    rcases htbls with rfl | rfl <;> decide +kernel
  exact (replay_unchanged Silence.current Ledger.current lcfg Kernel.current honest tbls (fun _ => [])
    _ 1 envCl _ acc0 h).1

/-- The claw-back with expiry 90, below `T = 95`, checked as `Exhibits.Clawback`'s is. -/
def cl1 : Cand := (Ingress.checkClawback ctx0 Classification.current { clReq with expiry := 90 }).getD es0

def qS : Request := { nonce := 1, psbt := pA, cand := cl1 }

/-- `Accepted` for `cl1` at a sample. -/
def acc1 (s : Nat) : Resp := .accepted cl1.id (Effective.ofWall (Wall.sample s) (HighWater.sample 0))
  (some (Wall.sample s))

/-- The pruning run: node 1 takes `qS` at 70; its prune pass at 92, past the expiry and before `T`;
at a backward sample 80, before the expiry, the exact retry with another nonce, then the same
commitment with other PSBT bytes. -/
def psteps : List HStep :=
  [.claw 1 envCl qS, .step (.input 1 (envAt 92 40) (.pinless .prune)),
   .claw 1 (envAt 80 45) { qS with nonce := 2 }, .claw 1 (envAt 80 45) { qS with nonce := 3, psbt := pB }]

def psched : List HStep := (sched.take 6).map .step ++ psteps

def ppairs : List (FObs × FObs) :=
  hwalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN H0 H0 psched

/-- **A replay after pruning.** `Ingress.checkClawback` admits the claw-back with expiry 90. Accepted at
70, its candidate is pruned at 92, inside the horizon of both families. The exact retry at the
backward sample 80, before the commitment's expiry at that sample, is a replay in both families
because the model's log still holds its key: log expiry is not modelled, and `SPN-24` says "Log
entries expire with their commitment", so a real log may have dropped the key at the prune's sample.
Given the key retained, it answers the stored `Accepted` at 70, and the registry still lacks the candidate, which
is neither recreated nor re-timed. The request with other PSBT bytes then misses the lookup and is
evaluated afresh under the current rule: `Kernel.clawback` registers the singleton anew, born at 80,
and answers `Accepted` at 80, while the log keeps, beside its new key, the commitment's first
`Accepted` at 70 (`ClawbackIngress.retain`). The two families emit equal observations at every step
(`ClawHandler.hfed_silence_fresh`). -/
@[req "SPN-50"]
theorem replay_after_prune :
    (∀ y ∈ ppairs, y.1 = y.2) ∧
      (Ingress.checkClawback ctx0 Classification.current { clReq with expiry := 90 }).isSome = true ∧
      cl1.expiry = Wall.sample 90 ∧ ppairs.length = 10 ∧
      ((hrun tblsD 6 H0 psched).L.fed.worlds 1).node.armed = true ∧
      (ppairs.drop 6).map (fun y => (resp y.1, resp y.2)) =
        [(some (acc1 70), some (acc1 70)), (some .silent, some .silent),
         (some (acc1 70), some (acc1 70)), (some (acc1 80), some (acc1 80))] ∧
      ((hrun tblsD 7 H0 psched).L.fed.worlds 1).node.cands.any (·.id == cl1.id) = true ∧
      ((hrun tblsD 8 H0 psched).L.fed.worlds 1).node.cands.any (·.id == cl1.id) = false ∧
      caseOf (hrun tblsD 8 H0 psched) 1 { qS with nonce := 2 } = .replay (acc1 70) ∧
      caseOf (hrun tblsN 8 H0 psched) 1 { qS with nonce := 2 } = .replay (acc1 70) ∧
      ((hrun tblsD 9 H0 psched).L.fed.worlds 1).node.cands.any (·.id == cl1.id) = false ∧
      ((hrun tblsN 9 H0 psched).L.fed.worlds 1).node.cands.any (·.id == cl1.id) = false ∧
      ((hrun tblsD 10 H0 psched).L.fed.worlds 1).node.cands.any (·.id == cl1.id) = true ∧
      (hrun tblsD 10 H0 psched).logs 1 =
        [⟨qS.key, acc1 70⟩, ⟨({ qS with psbt := pB } : Request).key, acc1 70⟩] ∧
      (hrun tblsN 10 H0 psched).logs 1 = (hrun tblsD 10 H0 psched).logs 1 :=
  ⟨hfed_silence_fresh rfl rfl rfl rfl rfl rfl honest honest tblsD tblsN H0 L0_fresh L0_sweep psched,
    by decide +kernel⟩

end BtcPolicy.Exhibits.ClawHandler

namespace BtcPolicy.Exhibits.PreRelease
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 spendPsbt escPsbt)
open BtcPolicy.Exhibits.EndToEnd (coin fed0 honest acc part assemble send)
open BtcPolicy.Exhibits.Clawback (cl0 clIn envCl)
open BtcPolicy.PreRelease (verdict failing fill)

/-! ### `DUR-21`'s check before release, run

Research task `bps-9oab.3`. The model of `BtcPolicy.Exhibits.EndToEnd`: three honest nodes under
`Kernel.current`, threshold 2, keys 1 to 3, the request `Exhibits.Ingress.req0` whose candidates
`Ingress.check` computes. Every run below is a `PreRelease.Execution`: a `Sweep.Execution` whose fire passes
carry the verdict `PreRelease.failing` computes at their own state and history, written into each fire pass
by `PreRelease.fill` and then checked by `PreRelease.legal`, never assumed. The book is a model parameter in
sats: the coin holds 510 000, and the Escape pays 499 800, all of it to the escape descriptor, so 98 of
every 100 as its checked PSBT does; its fee is 10 200. The legacy length of every transaction is 100 bytes,
so the Escape's maximum finalized vsize at threshold 2 of 3 keys is 221, and the floor is 1 unless a run
says otherwise. -/

/-- A second checked request over the same coin, whose Escape pays 99 of 100: fee 5 100 in the book. -/
def req1 : Ingress.Request :=
  { req0 with
    spend := ⟨{ spendPsbt with txOutputs := [⟨[12, 0], 41⟩, ⟨[11, 1], 54⟩] }, 2, 0, none⟩,
    escape := ⟨{ escPsbt with txOutputs := [⟨[10, 0], 99⟩] }, 2, 0, none⟩ }
def sp1 : Cand := Ingress.cand ctx0 req1 req1.spend true req1.fireAt
def es1 : Cand := Ingress.cand ctx0 req1 req1.escape false none

def book : Book :=
  { value := fun o => if o == coin then 510000 else if o == es0.tx.id + 1000 then 499800
      else if o == es1.tx.id + 1000 then 504900 else 0,
    outputs := fun tx => [tx + 1000],
    delivered := fun tx => if tx == es0.tx.id then 499800 else if tx == es1.tx.id then 504900 else 0 }

def scfg : Sweep.Cfg :=
  { pct := Coverage.floorPct, keys := [1, 2, 3], book := book, creator := fun _ => 7,
    denominator := Coverage.current, external := Coverage.currentExternal, ancestry := Package.current }

/-- The refined configuration at a feerate floor. -/
def pcfg (floor : Nat) : PreRelease.Cfg := { sweep := scfg, legacyLen := fun _ => 100, floor := floor }

/-- The vault: the coin, confirmed, nothing resident. -/
def vault : Backend :=
  { tip := ⟨5, 105⟩, sequence := 1, confirmed := [(coin, 510000)], mempool := [], pending := [] }
/-- A later instant with a second confirmed coin of value `x`, which no Escape spends. -/
def withCoin (x : Nat) : Backend := { vault with sequence := 2, confirmed := [(coin, 510000), (9, x)] }
/-- A later instant with an outside transaction resident over the coin. -/
def vConflict : Backend := { vault with sequence := 2, mempool := [(777, [coin])] }
/-- A later instant the coin is absent from. -/
def vMissing : Backend := { vault with sequence := 2, confirmed := [] }
/-- The claw-back resident. -/
def vRes : Backend := { vault with sequence := 2, mempool := [(cl0.tx.id, cl0.tx.inputs)] }
/-- The claw-back confirmed, the coin spent. -/
def vMined : Backend :=
  { vault with tip := ⟨6, 106⟩, sequence := 2, confirmed := [], mined := [(cl0.tx.id, cl0.tx.inputs)] }

def start (b : Backend) : State := { fed := fed0, truth := b }
def fire (i : Nat) (env : Env := envFire) : Step := .fed (.process i env .firePass)
def envLater : Env := envAt 125 65

/-- Nodes 1 and 2 take the checked request under duress, relay, and arm at their holder decisions. -/
def arm : List Step :=
  [acc 1 10 true, acc 2 10 true, .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩)]

/-- A schedule with its fire passes' verdicts filled in, its run, and whether the refined run admits it. -/
def sched (c : PreRelease.Cfg) (b : Backend) (ss : List Step) : List Step :=
  fill c Kernel.current [] (start b) ss
def run (c : PreRelease.Cfg) (b : Backend) (ss : List Step) : Trace × State :=
  record Kernel.current [] (start b) (sched c b ss)
def ok (c : PreRelease.Cfg) (b : Backend) (ss : List Step) : Bool :=
  PreRelease.legal c Kernel.current honest [] (start b) (sched c b ss)
/-- Node `i`'s verdict on `x` at the end of a schedule. -/
def verdictAt (c : PreRelease.Cfg) (b : Backend) (ss : List Step) (i : Nat) (x : Cand) : PreRelease.Verdict :=
  let p := run c b ss
  verdict c (authorizedAt p.2 p.1 i) (p.2.fed.worlds i).node (p.2.obs i) x
/-- Whether the refined run admits node `i`'s fire pass at `envFire` with nothing withheld next. -/
def unwithheld (c : PreRelease.Cfg) (b : Backend) (ss : List Step) (i : Nat) : Bool :=
  let p := run c b ss
  PreRelease.admits c honest p.2 p.1 (fire i)
/-- A candidate's rows in the partial inventory. -/
def rows (p : Trace × State) (x : Cand) : List Exp := p.2.fed.parts.filter (·.cid == x.id)
/-- A candidate's record at node `i`. -/
def candAt (p : Trace × State) (i : Nat) (x : Cand) : Option Cand :=
  (p.2.fed.worlds i).node.cands.find? (·.id == x.id)

theorem start_fresh (b : Backend) : Sweep.Fresh honest (start b) := by
  have h : Federation.Fresh honest fed0 := by
    unfold Federation.Fresh
    decide
  exact ⟨h, rfl, fun _ => rfl⟩

theorem execution_of (c : PreRelease.Cfg) (b : Backend) (ss : List Step) (h : ok c b ss = true) :
    PreRelease.Execution c Kernel.current honest (run c b ss).1 (run c b ss).2 :=
  PreRelease.execution_of_legal (.init _ (start_fresh b)) h

theorem checked_second : Ingress.check ctx0 true req1 = .accepted sp1 es1 := by decide +kernel

/-- The base sweep, end to end. -/
def full : List Step :=
  arm ++ [.observe 1 vault, .observe 2 vault, fire 1, fire 2,
    .fed (.deliverPartial 1 envFire (part es0 2)), .observe 1 vault, assemble 1 es0.id envFire,
    send 1 es0.id envFire]

/-- **A useful base sweep.** Nodes 1 and 2 arm, each reads the vault, and each verdict releases rung 0:
the protected value is the coin, the fee reaches the floor at the maximum finalized vsize, coverage holds
and the coin's ancestry is admitted. Each node releases while it holds only its own signature, one of the
two needed, so the release needs no possession. Node 2's partial reaches node 1, which assembles, and its
send submits the Escape's transaction. -/
@[req "DUR-21"]
theorem base_sweep :
    ok (pcfg 1) vault full = true ∧
      verdictAt (pcfg 1) vault (arm ++ [.observe 1 vault]) 1 es0 = .release 0 ∧
      (candAt (run (pcfg 1) vault (arm ++ [.observe 1 vault])) 1 es0).map (·.heldSigners) = some [1] ∧
      rows (run (pcfg 1) vault full) es0 = [part es0 1, part es0 2] ∧
      submits Kernel.current (run (pcfg 1) vault full.dropLast).2 (send 1 es0.id envFire) = [es0.tx.id] ∧
      PreRelease.maxVsize (pcfg 1) 2 es0.tx = 221 := by
  decide +kernel

theorem base_sweep_execution :
    PreRelease.Execution (pcfg 1) Kernel.current honest (run (pcfg 1) vault full).1
      (run (pcfg 1) vault full).2 :=
  execution_of _ _ _ base_sweep.1

/-- Node 1's release attempt at instant `b`, reached by the chain and read. -/
def attemptAt (b : Backend) : List Step := arm ++ [.chain b, .observe 1 b]

/-- **Coverage at the bound.** A second coin of 470 000 makes the protected value 980 000, and the Escape's
499 800 is exactly 51 percent of it: rung 0 is released and its row leaves. One sat more, and coverage
fails: the pass withholds the Escape, adds no row, leaves its release cursor where it was, and a fire pass
claiming nothing withheld is refused. -/
@[req "DUR-24"]
theorem coverage_at_bound :
    499800 * 100 = 980000 * Coverage.floorPct ∧
      ok (pcfg 1) vault (attemptAt (withCoin 470000) ++ [fire 1]) = true ∧
      verdictAt (pcfg 1) vault (attemptAt (withCoin 470000)) 1 es0 = .release 0 ∧
      rows (run (pcfg 1) vault (attemptAt (withCoin 470000) ++ [fire 1])) es0 = [part es0 1] ∧
      ok (pcfg 1) vault (attemptAt (withCoin 470001) ++ [fire 1]) = true ∧
      verdictAt (pcfg 1) vault (attemptAt (withCoin 470001)) 1 es0 = .fail .coverage ∧
      rows (run (pcfg 1) vault (attemptAt (withCoin 470001) ++ [fire 1])) es0 = [] ∧
      (candAt (run (pcfg 1) vault (attemptAt (withCoin 470001) ++ [fire 1])) 1 es0).map (·.released) =
        some false ∧
      unwithheld (pcfg 1) vault (attemptAt (withCoin 470001)) 1 = false := by
  decide +kernel

/-- **The fee floor at the maximum finalized vsize.** At a floor of 47 the fee of 10 200 falls short of
47 × 221 = 10 387, so the attempt stops at the fee and nothing leaves, although a finalized transaction
whose witness took 200 weight units, vsize 151, would clear 47 × 151 = 7 097. At 46 it passes. -/
@[req "DUR-25"]
theorem fee_at_max_vsize :
    Witness.finalizedVsize 100 [200] = 151 ∧ 47 * 151 ≤ 10200 ∧ 10200 < 47 * 221 ∧
      ok (pcfg 47) vault (arm ++ [.observe 1 vault, fire 1]) = true ∧
      verdictAt (pcfg 47) vault (arm ++ [.observe 1 vault]) 1 es0 = .fail .fee ∧
      rows (run (pcfg 47) vault (arm ++ [.observe 1 vault, fire 1])) es0 = [] ∧
      verdictAt (pcfg 46) vault (arm ++ [.observe 1 vault]) 1 es0 = .release 0 := by
  decide +kernel

/-- **A missing prevout.** At an instant the coin is absent from, the protected value still counts the
Escape's input and coverage holds, but `WTC-24`'s ancestry refuses it: no new exposure. -/
@[req "WTC-24"]
theorem missing_prevout_withholds :
    ok (pcfg 1) vault (attemptAt vMissing ++ [fire 1]) = true ∧
      verdictAt (pcfg 1) vault (attemptAt vMissing) 1 es0 = .fail .ancestry ∧
      rows (run (pcfg 1) vault (attemptAt vMissing ++ [fire 1])) es0 = [] := by
  decide +kernel

/-- **A late deposit.** The request was accepted at the vault; a deposit of 1 000 000 confirms afterwards.
At the release-time read the protected value is 1 510 000, not the 510 000 it was, and coverage fails. -/
@[req "DUR-22"]
theorem late_deposit_moves_denominator :
    let p := run (pcfg 1) vault (attemptAt (withCoin 1000000))
    let q := run (pcfg 1) vault (arm ++ [.observe 1 vault])
    Coverage.denominator scfg.denominator scfg.external
        (passAt scfg (authorizedAt q.2 q.1 1) (q.2.fed.worlds 1).node vault) (escapeOf book es0.tx) =
        510000 ∧
      Coverage.denominator scfg.denominator scfg.external
        (passAt scfg (authorizedAt p.2 p.1 1) (p.2.fed.worlds 1).node (withCoin 1000000))
        (escapeOf book es0.tx) = 1510000 ∧
      ok (pcfg 1) vault (attemptAt (withCoin 1000000) ++ [fire 1]) = true ∧
      verdictAt (pcfg 1) vault (attemptAt (withCoin 1000000)) 1 es0 = .fail .coverage ∧
      rows (run (pcfg 1) vault (attemptAt (withCoin 1000000) ++ [fire 1])) es0 = [] := by
  decide +kernel

/-- Between ingress and release an outside transaction becomes resident over the coin. -/
def moved : List Step := arm ++ [.chain vConflict, .observe 1 vConflict, .observe 2 vault]

/-- **An observation change between ingress and release.** Node 1 reads the instant after the move and its
verdict stops at ancestry; node 2 reads the earlier instant, which the truth has been, and releases. The
two nodes decide differently on one Escape, and only node 2's partial leaves. -/
@[req "DUR-21"]
theorem observation_moves_decision :
    ok (pcfg 1) vault (moved ++ [fire 1, fire 2]) = true ∧
      verdictAt (pcfg 1) vault moved 1 es0 = .fail .ancestry ∧
      verdictAt (pcfg 1) vault moved 2 es0 = .release 0 ∧
      rows (run (pcfg 1) vault (moved ++ [fire 1, fire 2])) es0 = [part es0 2] := by
  decide +kernel

/-- Both requests at nodes 1 and 2, each under its own Carrier, under duress; node 1 reads the vault. -/
def twoPairs : List Step :=
  [acc 1 10 true, .fed (.process 1 env0 (.accept 20 true (Wall.sample 200) sp1 es1)),
   acc 2 10 true, .fed (.process 2 env0 (.accept 20 true (Wall.sample 200) sp1 es1)),
   .fed (.emit 1 10), .fed (.emit 1 20), .fed (.emit 2 10), .fed (.emit 2 20),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 1 env0 ⟨2, 20⟩), .fed (.deliver 2 env0 ⟨1, 10⟩),
   .fed (.deliver 2 env0 ⟨1, 20⟩), .observe 1 vault]

/-- **One Escape fails while another proceeds.** Both selected Escapes spend the one coin, so the protected
value is that coin for both. At a floor of 24, 24 × 221 = 5 304: the first Escape's fee of 10 200 passes and
the second's 5 100 does not. One fire pass at node 1 withholds the second alone and releases the first. -/
@[req "DUR-21"]
theorem one_fails_other_releases :
    ok (pcfg 24) vault (twoPairs ++ [fire 1]) = true ∧
      verdictAt (pcfg 24) vault twoPairs 1 es0 = .release 0 ∧
      verdictAt (pcfg 24) vault twoPairs 1 es1 = .fail .fee ∧
      rows (run (pcfg 24) vault (twoPairs ++ [fire 1])) es0 = [part es0 1] ∧
      rows (run (pcfg 24) vault (twoPairs ++ [fire 1])) es1 = [] := by
  decide +kernel

/-- **Arming and freezing while no Escape can release.** With no observation the verdict at both nodes is
`PreRelease.Stage.noRead`: both fire passes withhold the Escape, and a pass claiming nothing withheld is
refused. Both nodes are armed with the hot spend frozen. -/
@[req "DUR-19"]
theorem armed_without_release :
    let p := run (pcfg 1) vault (arm ++ [fire 1, fire 2])
    ok (pcfg 1) vault (arm ++ [fire 1, fire 2]) = true ∧
      verdictAt (pcfg 1) vault arm 1 es0 = .fail .noRead ∧
      verdictAt (pcfg 1) vault arm 2 es0 = .fail .noRead ∧
      unwithheld (pcfg 1) vault arm 1 = false ∧
      (p.2.fed.worlds 1).node.armed = true ∧ (p.2.fed.worlds 2).node.armed = true ∧
      (candAt p 1 sp0).map (·.frozen) = some true ∧ (candAt p 2 sp0).map (·.frozen) = some true ∧
      rows p es0 = [] := by
  decide +kernel

/-- **A later attempt succeeds.** The first pass at 120 has no observation and withholds; node 1 reads the
vault and its pass at 125, inside the window, releases. -/
@[req "DUR-21"]
theorem later_attempt_releases :
    ok (pcfg 1) vault (arm ++ [fire 1, .observe 1 vault, fire 1 envLater]) = true ∧
      rows (run (pcfg 1) vault (arm ++ [fire 1])) es0 = [] ∧
      rows (run (pcfg 1) vault (arm ++ [fire 1, .observe 1 vault, fire 1 envLater])) es0 = [part es0 1] := by
  decide +kernel

/-- Both nodes release at the vault and node 2's partial reaches node 1; then the coin is spent in the
mempool and node 1 reads it. -/
def releasedThenMoved : List Step :=
  arm ++ [.observe 1 vault, .observe 2 vault, fire 1, fire 2,
    .fed (.deliverPartial 1 envFire (part es0 2)), .chain vConflict, .observe 1 vConflict]

/-- **Earlier exposure survives a failed attempt.** Node 1's next pass, at 125, stops at ancestry; both
partials already released stay in the inventory, node 1 still holds node 2's, and its release cursor is
still set. -/
@[req "DUR-21"]
theorem earlier_exposure_survives :
    let p := run (pcfg 1) vault (releasedThenMoved ++ [fire 1 envLater])
    ok (pcfg 1) vault (releasedThenMoved ++ [fire 1 envLater]) = true ∧
      verdictAt (pcfg 1) vault releasedThenMoved 1 es0 = .fail .ancestry ∧
      rows p es0 = [part es0 1, part es0 2] ∧
      rows p es0 = rows (run (pcfg 1) vault releasedThenMoved) es0 ∧
      (candAt p 1 es0).map (fun c => (c.heldSigners, c.released)) = some ([1, 2], true) := by
  decide +kernel

/-- Node 1's attempt fails; then its key is copied and a partial is forged with it. -/
def failedThenForged : List Step :=
  arm ++ [.chain vConflict, .observe 1 vConflict, fire 1, .fed (.extract 1), .fed (.forge (part es0 1))]

/-- **A failed release, then extraction and forgery.** Node 1's honest pass withholds the Escape and emits
nothing; the adversary then copies node 1's key and forges node 1's partial, which the run admits: the row
is in the inventory with its signer extracted, the alternative `PreRelease.inventory_provenance` keeps. -/
@[req "DUR-21"]
theorem failed_then_forged :
    let p := run (pcfg 1) vault failedThenForged
    ok (pcfg 1) vault failedThenForged = true ∧
      verdictAt (pcfg 1) vault (failedThenForged.take 8) 1 es0 = .fail .ancestry ∧
      rows (run (pcfg 1) vault (failedThenForged.take 9)) es0 = [] ∧
      rows p es0 = [part es0 1] ∧ p.2.fed.extracted.contains 1 = true := by
  decide +kernel

/-- The armed run with the claw-back over the Escape's coin taken and released at both nodes at 70, before
`T`; then the chain moves through `bs` and node 1 reads each instant. -/
def clThen (bs : List Backend) : List Step :=
  arm ++ [clIn 1, clIn 2, fire 1 envCl, fire 2 envCl] ++ bs.flatMap (fun b => [.chain b, .observe 1 b])

/-- **A claw-back's residency, paired.** With the claw-back resident, or confirmed, at node 1's read, the
Escape's coverage holds and its ancestry does not, and node 1's fire pass at 120 releases no partial of it.
With the claw-back evicted before that read, the pass releases it. With the claw-back accepted and signed at
both nodes but never resident at the read, it releases too: accepting or signing the claw-back alone settles
nothing. The claw-back's own rows are there in every case. -/
@[req "DUR-36"]
theorem clawback_residency_pair :
    ok (pcfg 1) vault (clThen [vRes] ++ [fire 1]) = true ∧
      ok (pcfg 1) vault (clThen [vMined] ++ [fire 1]) = true ∧
      ok (pcfg 1) vault (clThen [vRes, vault] ++ [fire 1]) = true ∧
      ok (pcfg 1) vault (clThen [vault] ++ [fire 1]) = true ∧
      verdictAt (pcfg 1) vault (clThen [vRes]) 1 es0 = .fail .ancestry ∧
      verdictAt (pcfg 1) vault (clThen [vMined]) 1 es0 = .fail .ancestry ∧
      rows (run (pcfg 1) vault (clThen [vRes] ++ [fire 1])) es0 = [] ∧
      rows (run (pcfg 1) vault (clThen [vMined] ++ [fire 1])) es0 = [] ∧
      rows (run (pcfg 1) vault (clThen [vRes, vault] ++ [fire 1])) es0 = [part es0 1] ∧
      rows (run (pcfg 1) vault (clThen [vault] ++ [fire 1])) es0 = [part es0 1] ∧
      rows (run (pcfg 1) vault (clThen [vRes] ++ [fire 1])) cl0 = [part cl0 1, part cl0 2] := by
  decide +kernel

/-- The covered check at node 1 with the claw-back resident: `PreRelease.ancestry_after_selection`'s case. -/
theorem clawback_resident_covered :
    let p := run (pcfg 1) vault (clThen [vRes])
    covered scfg (authorizedAt p.2 p.1 1) (p.2.fed.worlds 1).node vRes es0 = true ∧
      ancestryOk scfg (authorizedAt p.2 p.1 1) vRes es0 = false := by
  decide +kernel

/-- Node 1 releases the Escape at 120 at an instant that does not cover it. -/
def bypass : List Step := arm ++ [.chain (withCoin 1000000), .observe 1 (withCoin 1000000), fire 1]

/-- **The old abstraction is broader.** The same schedule, with the fire pass releasing the Escape whatever
the instant says, is a `Sweep` run, in `Sweep.lift_unassembled`'s domain since it assembles nothing, and
leaves node 1's partial in the inventory; the refined run refuses that fire pass. -/
@[req "DUR-21"]
theorem bypass_not_refined :
    Sweep.legal scfg Kernel.current honest [] (start vault) bypass = true ∧
      PreRelease.legal (pcfg 1) Kernel.current honest [] (start vault) bypass = false ∧
      (record Kernel.current [] (start vault) bypass).2.fed.parts.filter (·.cid == es0.id) =
        [part es0 1] := by
  decide +kernel

end BtcPolicy.Exhibits.PreRelease

namespace BtcPolicy.Exhibits.CommonRun
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 lcfg checked_pair)
open BtcPolicy.Exhibits.EndToEnd (coin worlds honest part assemble send fire st0 st0_fresh runOf fedOf sc envHeld
  es1 tooLate ordinaryAll toRelease coerced coercedSteps v vLarge vSpent base)
open BtcPolicy.Ingress (check checkedTrace_of hot_binding code_injective frame_wf accepted_validates accepted_spend)
open BtcPolicy.Recovery (fedSteps fed_record sweepTrace failures)

/-! ### The first milestone on one composed run

Research task `bps-9oab.8`, its base-only part. The histories of `Exhibits.EndToEnd`, unchanged in their
federation steps, run again on the composed model with `DUR-21`'s check before each Escape release:
each fire pass is preceded by its node's read of the instant the truth then is (`readFirst`), and carries
the verdict `PreRelease.failing` computes there, written by `PreRelease.fill` and then checked
(`refined`), never assumed. The book is `Exhibits.PreRelease`'s, in sats, with one more coin, outpoint 9,
of 1 000 000, which no Escape spends; each instant of `Exhibits.EndToEnd` is the same instant with every
confirmed coin at this book's value (`inst`). `Recovery.to_prerelease` makes each such composed run a
`PreRelease.Execution` underneath, so every result of `BtcPolicy.PreRelease` is about it, with the
custody, death, latch and Recovery steps of `BtcPolicy.Recovery` beside it.

Where the check releases, the verdict is the empty one and the federation steps are exactly those of the
history as first written, so its checked ingress, its Hot ledgers, its admission bound and SILENCE on it
carry over by `Recovery.fed_record`. Where it fails, the pass withholds, and the run differs from the
history as first written exactly there. -/

/-- `Exhibits.PreRelease`'s book with a coin of 1 000 000 at outpoint 9. -/
def book : Book :=
  { Exhibits.PreRelease.book with
    value := fun o => if o == 9 then 1000000 else Exhibits.PreRelease.book.value o }

def scfg : Sweep.Cfg := { Exhibits.PreRelease.scfg with book := book }

/-- `Exhibits.EndToEnd`'s composed model at this book. -/
def icfg : Recovery.Cfg := { Exhibits.EndToEnd.rcfg with sweep := scfg }

/-- The check at a floor of 1 and a legacy length of 100 bytes, as in `Exhibits.PreRelease`. -/
def pc : PreRelease.Cfg := { sweep := scfg, legacyLen := fun _ => 100, floor := 1 }

theorem pc_sweep : pc.sweep = icfg.sweep := rfl

/-- An instant of `Exhibits.EndToEnd` with every confirmed coin at this book's value. -/
def inst (b : Backend) : Backend := { b with confirmed := b.confirmed.map fun p => (p.1, book.value p.1) }

/-- A step of `Exhibits.EndToEnd` over this book's instants. -/
def onBook : Step → Step
  | .observe i b => .observe i (inst b)
  | .chain b => .chain (inst b)
  | s => s

/-- Each fire pass preceded by its node's read of the instant the truth is then, `b` until a chain move. -/
def readFirst : Backend → List Step → List Step
  | _, [] => []
  | _, .chain b' :: ss => .chain b' :: readFirst b' ss
  | b, .fed (.process i env .firePass) :: ss =>
    .observe i b :: .fed (.process i env .firePass) :: readFirst b ss
  | b, s :: ss => s :: readFirst b ss

/-- A history of `Exhibits.EndToEnd` from instant `b`, with the release-time reads, over this book, each
fire pass carrying the verdict computed at its own state and history. -/
def integ (b : Backend) (ss : List Step) : List Recovery.Step :=
  (PreRelease.fill pc Kernel.current [] (st0 (inst b)).sw ((readFirst b ss).map onBook)).map .base

def isLegal (b : Backend) (xs : List Recovery.Step) : Bool :=
  Recovery.legal icfg Kernel.current honest [] (st0 (inst b)) xs

/-- Every sweep step of the composed run carries the verdict computed at its own state and history. -/
def refined (b : Backend) (xs : List Recovery.Step) : Bool :=
  PreRelease.checks pc (sweepTrace (runOf (inst b) xs).1)

theorem execution_of (b : Backend) (xs : List Recovery.Step) (h : isLegal b xs = true) :
    Recovery.Execution icfg Kernel.current honest (runOf (inst b) xs).1 (runOf (inst b) xs).2 :=
  Recovery.execution_of_legal (.init _ (st0_fresh (inst b))) h

/-- A legal, refined schedule is a refined execution underneath. -/
theorem prerelease_of (b : Backend) (xs : List Recovery.Step) (hl : isLegal b xs = true)
    (hc : refined b xs = true) :
    PreRelease.Execution pc Kernel.current honest (sweepTrace (runOf (inst b) xs).1) (runOf (inst b) xs).2.sw :=
  Recovery.to_prerelease pc_sweep (execution_of b xs hl) (PreRelease.checked_of_checks pc hc)

/-- Node `i`'s verdict on `x` after the first `k` steps of a schedule. -/
def verdictAt (b : Backend) (xs : List Recovery.Step) (k i : Nat) (x : Cand) : PreRelease.Verdict :=
  let p := runOf (inst b) (xs.take k)
  PreRelease.verdict pc (authorizedAt p.2.sw (sweepTrace p.1) i) (p.2.sw.fed.worlds i).node (p.2.sw.obs i) x

/-- A candidate's rows in the partial inventory at the end of a schedule. -/
def rows (b : Backend) (xs : List Recovery.Step) (x : Cand) : List Exp :=
  (runOf (inst b) xs).2.sw.fed.parts.filter (·.cid == x.id)

/-- Two schedules with one list of federation steps leave one federation state and one federation trace,
whatever their backend, observation, custody or latch steps. -/
theorem same_federation (b b' : Backend) (xs ys : List Recovery.Step) (h : fedSteps xs = fedSteps ys) :
    (runOf b xs).2.sw.fed = (runOf b' ys).2.sw.fed ∧ fedOf b xs = fedOf b' ys := by
  obtain ⟨h1, h2⟩ := fed_record Kernel.current xs [] (st0 b)
  obtain ⟨h3, h4⟩ := fed_record Kernel.current ys [] (st0 b')
  refine ⟨?_, ?_⟩
  · show (Recovery.record Kernel.current [] (st0 b) xs).2.sw.fed =
      (Recovery.record Kernel.current [] (st0 b') ys).2.sw.fed
    rw [h2, h4, h]; rfl
  · show Sweep.fedTrace (sweepTrace (Recovery.record Kernel.current [] (st0 b) xs).1) =
      Sweep.fedTrace (sweepTrace (Recovery.record Kernel.current [] (st0 b') ys).1)
    rw [h1, h3, h]; rfl

/-! #### The history as first written is not a refined run -/

/-- **The old history releases before any read.** `EndToEnd.coerced` over this book is a composed run,
but node 1's first fire pass comes before node 1 has read anything, so its verdict is
`PreRelease.Stage.noRead`, and a fire pass releasing the Escape there is not one the check admits. This is
the first class of `DUR-21`'s integration failure: the old execution was broader than the rule, and
adding the read before the pass, as `readFirst` does, restores a refined run over the same federation
steps (`coerced_refined`). -/
@[req "DUR-21"]
theorem old_history_not_refined :
    isLegal v ((coerced.map onBook).map .base) = true ∧
      refined v ((coerced.map onBook).map .base) = false ∧
      verdictAt v ((coerced.map onBook).map .base) 6 1 es0 = .fail .noRead := by
  decide +kernel

/-! #### Coerced, with a usable base Escape -/

/-- **The coerced history, checked before release.** Nodes 1 and 2 take the checked request under
duress and arm; each reads the vault before its fire pass, and each verdict releases rung 0, node 1's
while it holds only its own signature. Node 2's partial reaches node 1, whose read before assembly shows
coverage, ancestry and `t` distinct signers on every input; the assembly is admitted, the send submits the
Escape's transaction, and the chain alone confirms it. The schedule's federation steps are
`EndToEnd.coerced`'s, verdict included. -/
@[req "DUR-21"]
theorem coerced_refined :
    let xs := integ v coerced
    let p := runOf (inst v) (xs.take 12)
    let R := Federation.held 1 (Sweep.fedTrace (sweepTrace p.1)) p.2.sw.fed
    isLegal v xs = true ∧ refined v xs = true ∧ fedSteps xs = fedSteps (base coerced) ∧
      verdictAt v xs 7 1 es0 = .release 0 ∧ verdictAt v xs 9 2 es0 = .release 0 ∧
      ((((runOf (inst v) (xs.take 7)).2.sw.fed.worlds 1).node.cands.find? (·.id == es0.id)).map
        (·.heldSigners)) = some [1] ∧
      rows v (xs.take 8) es0 = [part es0 1] ∧ rows v xs es0 = [part es0 1, part es0 2] ∧
      Sweep.covered scfg (authorizedAt p.2.sw (sweepTrace p.1) 1) (p.2.sw.fed.worlds 1).node (inst v) es0 = true ∧
      Sweep.ancestryOk scfg (authorizedAt p.2.sw (sweepTrace p.1) 1) (inst v) es0 = true ∧
      Authority.quorum scfg.keys 2 es0.tx R = true ∧
      Sweep.submits Kernel.current (runOf (inst v) (xs.take 13)).2.sw (send 1 es0.id envFire) = [es0.tx.id] ∧
      Settlement.confirmedAt (runOf (inst v) (xs.take 14)).2.sw.truth es0.tx = false ∧
      Settlement.confirmedAt (runOf (inst v) xs).2.sw.truth es0.tx = true := by
  decide +kernel

/-- The same run is a `PreRelease.Execution` underneath, so `PreRelease.no_premature_exposure` reads its
inventory: every row was emitted by its signer's honest node past that node's verdict, since no key is
extracted. -/
@[req "DUR-21"]
theorem coerced_rows_emitted :
    ∀ x ∈ (runOf (inst v) (integ v coerced)).2.sw.fed.parts, x.signer ∈ honest ∧
      PreRelease.Emitted pc Kernel.current (sweepTrace (runOf (inst v) (integ v coerced)).1) x := by
  have h := coerced_refined
  intro x hx
  refine Recovery.no_premature_exposure pc_sweep (execution_of v _ h.1)
    (PreRelease.checked_of_checks pc h.2.1) hx ?_
  have he : (runOf (inst v) (integ v coerced)).2.sw.fed.extracted = [] := by decide +kernel
  rw [he]; exact List.not_mem_nil

/-- **What the first history established, on this one.** The federation state and trace are
`EndToEnd.coerced`'s, so: every acceptance is `Ingress.check`'s and the hot spend's message is bound
(`EndToEnd.coerced_checked`); the hot spend has no exposed quorum, by `Federation.cohort_no_exposed_quorum`
(`EndToEnd.duress_withholds`); gate 24 admits each acceptance over the Hot ledgers the run builds and the
ledgered replay is the run's (`LedgerSilence.coerced_ledgered`), with `POL-20`'s bound
(`LedgerSilence.coerced_admission_bound`); and the schedule SILENCE walks under the duress family is this
run's (`LedgerSilence.coerced_silent`), which stops at node 1's first fire pass, past `T`. -/
@[req "DUR-8"]
theorem coerced_carries :
    let xs := integ v coerced
    (Ingress.CheckedTrace ctx0 (fedOf (inst v) xs) ∧
        Federation.HotBinding (runOf (inst v) xs).2.sw.fed (sighash sp0.tx 0)) ∧
      exposedQuorum { node := (worlds 1).node, exposure := (runOf (inst v) xs).2.sw.fed.parts } sp0 = false ∧
      LedgerSilence.faithful lcfg xs = true ∧
      LedgerSilence.ledgered lcfg xs = LedgerSilence.ledgered lcfg (base coerced) ∧
      LedgerSilence.sched.map (·.step LedgerSilence.tblsD) = fedSteps xs := by
  have hf := coerced_refined.2.2.1
  obtain ⟨h1, h2⟩ := same_federation (inst v) v (integ v coerced) (base coerced) hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, h2]; exact EndToEnd.coerced_checked
  · rw [h1]; exact EndToEnd.duress_withholds
  · unfold LedgerSilence.faithful; rw [hf]; exact LedgerSilence.coerced_faithful
  · unfold LedgerSilence.ledgered; rw [hf]
  · rw [hf]; exact LedgerSilence.coerced_silent.2.1

/-! #### Ordinary -/

/-- **The ordinary history, checked.** With no duress the nodes stay unarmed; each reads before its fire
pass, where the Escape, never selected, is not due and the verdict withholds nothing. The hot spend's Hold
matures on each node's clock, node 1 holds `t` signers on every input with the user's signature, its send
submits the hot spend, the Escape never leaves, and the chain confirms the spend. The federation steps
are `EndToEnd.ordinaryAll`'s. -/
@[req "DUR-28"]
theorem ordinary_refined :
    let xs := integ v ordinaryAll
    let p := runOf (inst v) (xs.take 13)
    isLegal v xs = true ∧ refined v xs = true ∧ fedSteps xs = fedSteps (base ordinaryAll) ∧
      (p.2.sw.fed.worlds 1).node.armed = false ∧
      Authority.normal scfg.keys 2 sp0.tx sc.userSigs (Recovery.inventory p.2) = true ∧
      Sweep.submits Kernel.current p.2.sw (send 1 sp0.id envHeld) = [sp0.tx.id] ∧
      rows v xs es0 = [] ∧
      Settlement.confirmedAt (runOf (inst v) xs).2.sw.truth sp0.tx = true := by
  decide +kernel

/-- The ordinary history keeps its Hot ledgers: its federation steps are `EndToEnd.ordinaryAll`'s, which
gate 24 admits at cap 100 (`LedgerSilence.others_faithful`), so the ledgered replay is the run's. -/
@[req "POL-16"]
theorem ordinary_faithful : LedgerSilence.faithful lcfg (integ v ordinaryAll) = true := by
  unfold LedgerSilence.faithful
  rw [ordinary_refined.2.2.1]
  exact LedgerSilence.others_faithful.1

/-! #### Coerced, with an unusable Escape -/

/-- `EndToEnd.toRelease` at the vault holding the large coin, each pass preceded by its read, then node 1's
read; the schedule `EndToEnd.safe_without_progress` reads, less the delivery of node 2's Escape partial,
which the refined pass never emits. -/
def unusable : List Recovery.Step := integ vLarge (toRelease ++ [.observe 1 vLarge])

/-- `EndToEnd.withholds_on` at this book: `Federation.cohort_no_exposed_quorum` on a composed run of the
request, each premise decided on the run. -/
theorem withholds_at (b : Backend) (xs : List Recovery.Step) (hl : isLegal b xs = true)
    (hc : (Ingress.acceptPairs (fedOf (inst b) xs)).all
      (fun p => [req0].any fun q => check ctx0 true q == .accepted p.1 p.2) = true)
    (hcl : (Ingress.clawCands (fedOf (inst b) xs)).all
      (fun c => ([] : List Ingress.ClawbackRequest).any fun q =>
        Ingress.checkClawback ctx0 Classification.current q == some c) = true)
    (hp : ∀ i ∈ [1, 2], i ∈ honest ∧ i ∉ (runOf (inst b) xs).2.sw.fed.extracted ∧
      (Federation.project i (fedOf (inst b) xs)).all
        (Federation.holdFrame (sighash sp0.tx 0) (Mono.sample 10)) = true)
    (he : (runOf (inst b) xs).2.sw.fed.extracted = []) :
    exposedQuorum { node := (worlds 1).node, exposure := (runOf (inst b) xs).2.sw.fed.parts } sp0 = false := by
  have hexec : Federation.Execution Kernel.current honest (fedOf (inst b) xs) (runOf (inst b) xs).2.sw.fed :=
    Sweep.fed_execution (Settlement.to_sweep (Recovery.to_settlement (execution_of b xs hl)))
  have hchk := Ingress.checkedTrace_of_claws ctx0 _ [req0] [] hc hcl
  refine Federation.cohort_no_exposed_quorum (r := Kernel.current) rfl hexec (worlds 1).node sp0
    (hot_binding hexec hchk code_injective (frame_wf (accepted_validates checked_pair.1).1)
      (accepted_spend checked_pair.1).1)
    [1, 2] (fun _ => Mono.sample 10) ?_ [1, 2, 3] ?_ (by decide)
  · intro i hi
    obtain ⟨h1, h2, h3⟩ := hp i hi
    exact ⟨h1, h2, List.all_eq_true.1 h3⟩
  · intro j hj
    rcases hj with hj | hj
    · exact hj
    · rw [he] at hj
      cases hj

/-- **Safe, and the Escape does not leave.** At the vault holding the large coin, the protected value is
1 510 000 and the Escape's 499 800 falls short of the bound: both verdicts stop at coverage, both fire
passes withhold the Escape, and no partial of it is in the inventory. Both nodes are armed with the hot
spend frozen, the assembly is not admitted and the send submits nothing; the coin stands in three classes.
The history as first written released both Escape partials at that instant; that schedule, with its
reads, is not a legal refined run, since it delivers a partial the refined pass never emits. -/
@[req "DUR-19"]
theorem unusable_refined :
    let p := runOf (inst vLarge) unusable
    let q := runOf (inst vLarge) (unusable.take 7)
    isLegal vLarge unusable = true ∧ refined vLarge unusable = true ∧
      Coverage.denominator scfg.denominator scfg.external
          (passAt scfg (authorizedAt q.2.sw (sweepTrace q.1) 1) (q.2.sw.fed.worlds 1).node (inst vLarge))
          (escapeOf book es0.tx) = 1510000 ∧
      verdictAt vLarge unusable 7 1 es0 = .fail .coverage ∧ verdictAt vLarge unusable 9 2 es0 = .fail .coverage ∧
      rows vLarge unusable es0 = [] ∧
      (p.2.sw.fed.worlds 1).node.armed = true ∧ (p.2.sw.fed.worlds 2).node.armed = true ∧
      (p.2.sw.fed.worlds 1).node.cands.any (fun c => c.id == sp0.id && c.frozen) = true ∧
      Sweep.admits scfg honest p.2.sw (sweepTrace p.1) (assemble 1 es0.id envFire) = false ∧
      Sweep.submits Kernel.current p.2.sw (send 1 es0.id envFire) = [] ∧
      failures icfg p.2 p.1 honest sc = [.normalBlocked, .fastUnavailable, .notMature] ∧
      (runOf vLarge (base (EndToEnd.toRead vLarge))).2.sw.fed.parts.filter (·.cid == es0.id) =
        [part es0 1, part es0 2] ∧
      isLegal vLarge (integ vLarge (EndToEnd.toRead vLarge)) = false := by
  decide +kernel

/-- The hot spend has no exposed quorum at the end of `unusable`, from the cohort theorem. -/
@[req "DUR-8"]
theorem unusable_withholds :
    exposedQuorum { node := (worlds 1).node, exposure := (runOf (inst vLarge) unusable).2.sw.fed.parts } sp0 =
      false :=
  withholds_at vLarge unusable (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! #### Earlier exposure, then a failed attempt -/

/-- `EndToEnd.tooLate` with its reads; then the large coin confirms and node 1's pass at 120, inside the
second Escape's window, reads it. -/
def priorFailed : List Recovery.Step := integ v (tooLate ++ [.chain vLarge, fire 1 envHeld])
/-- The same pass at the vault. -/
def priorReleased : List Recovery.Step := integ v (tooLate ++ [fire 1 envHeld])

/-- **Earlier authority survives arming and a later failed attempt.** `EndToEnd.duress_too_late`'s
history, with its federation steps unchanged by the reads: both nodes released the hot spend before the
coercion arrived, then armed on the new commitment. Node 1's next pass reads the large coin; the new
Escape's verdict stops at coverage and the pass withholds both Escapes. The hot spend's rows are those the
history had before the pass, its quorum still exposed, and no Escape row is in the inventory. At the
vault the same pass releases the new Escape, so the withholding is the verdict's. -/
@[req "DUR-21"]
theorem prior_exposure_survives :
    let p := runOf (inst v) priorFailed
    isLegal v priorFailed = true ∧ refined v priorFailed = true ∧
      fedSteps (integ v tooLate) = fedSteps (base tooLate) ∧
      (p.2.sw.fed.worlds 1).node.armed = true ∧ (p.2.sw.fed.worlds 2).node.armed = true ∧
      verdictAt v priorFailed 18 1 es1 = .fail .coverage ∧
      rows v priorFailed sp0 = rows v (integ v tooLate) sp0 ∧ rows v priorFailed sp0 ≠ [] ∧
      exposedQuorum { node := (worlds 1).node, exposure := p.2.sw.fed.parts } sp0 = true ∧
      rows v priorFailed es0 = [] ∧ rows v priorFailed es1 = [] ∧
      isLegal v priorReleased = true ∧ refined v priorReleased = true ∧
      rows v priorReleased es1 = [part es1 1] := by
  decide +kernel

/-! #### Submitted, never included -/

/-- **Sent, and the chain never takes it.** The checked coerced history stopped before the chain move:
the Escape is out and unconfirmed, and the coin stands awaiting inclusion. -/
@[req "SEC-54"]
theorem sent_not_included_refined :
    let xs := integ v coercedSteps
    let p := runOf (inst v) xs
    isLegal v xs = true ∧ refined v xs = true ∧ Settlement.confirmedAt p.2.sw.truth es0.tx = false ∧
      failures icfg p.2 p.1 honest sc = [.normalBlocked, .notMature, .awaitingInclusion] := by
  decide +kernel

/-! #### The claw-back walk and the verdict -/

/-- **The verdict inside the claw-back walk.** `Exhibits.ClawSilence.clawback_inside_walk` starts with
this run's six arming steps. At its claw-back fire pass node 1 is armed in the duress family and not in
the normal one, and the two share one `Silence.pubNode`; by `PreRelease.failingAt_pub` they withhold the
same Escape ids at every observation and authorized set. At the vault both release the Escape's check,
and at the large coin both fail it. -/
@[req "DUR-1"]
theorem clawback_walk_verdict :
    let nD := ((ClawSilence.runK LedgerSilence.tblsD 9).fed.worlds 1).node
    let nN := ((ClawSilence.runK LedgerSilence.tblsN 9).fed.worlds 1).node
    (ClawSilence.clSched.take 6).map (·.step LedgerSilence.tblsD) = (fedSteps (integ v coerced)).take 6 ∧
      nD.armed = true ∧ nN.armed = false ∧
      (∀ A ob, PreRelease.failingAt pc A nD ob = PreRelease.failingAt pc A nN ob) ∧
      PreRelease.failingAt pc (Sweep.authorized [] nD) nD (some (inst v)) = [] ∧
      PreRelease.failingAt pc (Sweep.authorized [] nD) nD (some (inst vLarge)) = [es0.id] := by
  have hp : Silence.pubNode Kernel.current ((ClawSilence.runK LedgerSilence.tblsD 9).fed.worlds 1).node =
      Silence.pubNode Kernel.current ((ClawSilence.runK LedgerSilence.tblsN 9).fed.worlds 1).node := by
    decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    fun A ob => PreRelease.failingAt_pub pc A ob hp, by decide +kernel, by decide +kernel⟩

end BtcPolicy.Exhibits.CommonRun

namespace BtcPolicy.Exhibits.Coinbase
open BtcPolicy.Coinbase
open BtcPolicy.Feasibility (Vault composeEvery everyRequest)
open BtcPolicy.Coverage (Coin Outpoint)
open BtcPolicy.Exhibits.Feasibility (lim plain mk)

/-! ### The composer's immature coinbase

`OPR-33`, `OPR-38`, `OPR-65` and `OPR-68` over `Coinbase.accept`. Every instant below is a
`Feasibility` vault at a stated tip height, its coins valued as listed, each with a small parent, at
2-of-3 with `Exhibits.Feasibility.lim`'s assumed sizes and `MAN-9`'s floor of 51 as the coverage. The
feerate floor is 0 unless a state says 1, where one input's fee is 215. A record is ordinary when its
creating transaction spends a prevout, and a coinbase's output when its one input is the coinbase. -/

def vaultScript : Nat := 7

def ordinaryAt (h v : Nat) : Record :=
  { height := h, script := vaultScript,
    tx := { inputs := [.prevout 900], value := v, script := vaultScript, height := h, active := true } }

def coinbaseAt (h v : Nat) : Record :=
  { height := h, script := vaultScript,
    tx := { inputs := [.coinbase], value := v, script := vaultScript, height := h, active := true } }

/-- The instant at tip height `tip` over `coins`, each at its listed value. -/
def at_ (tip : Nat) (coins : List Coin) (floor : Nat := 0) : Vault :=
  let v := mk coins (fun o => (coins.lookup o).getD 0) (fun _ => some plain) floor
  { v with b := { v.b with tip := ⟨tip, 1000 + tip⟩ } }

def pass (rs : List (Outpoint × Record)) : Pass := { script := vaultScript, records := rs }

def err {ε α : Type} : Except ε α → Option ε
  | .error e => some e
  | .ok _ => none

/-! #### No coinbase outputs -/

def ordVault : Vault := at_ 200 [(1, 60000), (2, 40000)] 1
def ordPass : Pass := pass [(1, ordinaryAt 10 60000), (2, ordinaryAt 20 40000)]

/-- **No coinbase outputs: the existing composition is preserved.** The spend is
`Feasibility.composeEvery`'s request over the same instant, and `Coinbase.spend_reduces` says so for
every pass that leaves nothing out. -/
@[req "OPR-33"]
theorem no_coinbase_preserved :
    (composeSpend lim 9 ordVault ordPass).toOption = (composeEvery lim 9 ordVault).toOption ∧
      (composeEvery lim 9 ordVault).toOption = some (everyRequest lim 9 ordVault) ∧
      (accept ordVault ordPass).toOption.map (·.immature) = some [] := by
  decide +kernel

/-! #### Coverage -/

/-- 100 000 ordinary and a 5 000 coinbase confirmed at height 150, at tip 200: 51 confirmations. -/
def smallVault : Vault := at_ 200 [(1, 100000), (2, 5000)] 1
def smallPass : Pass := pass [(1, ordinaryAt 10 100000), (2, coinbaseAt 150 5000)]

/-- **Immature value absorbed by coverage: the spend composes.** It spends coin 1 alone, the backend
still holds coin 2, and the node's denominator at the same read counts it: 105 000, which is
`total_in + I`, so the node's `DUR-24` is the additional check (`Coinbase.node_covers_iff_extra`). -/
@[req "OPR-38"]
theorem absorbed_spend_composes :
    (composeSpend lim 9 smallVault smallPass).toOption =
        some { txid := 9, inputs := [1], fee := 215 } ∧
      (accept smallVault smallPass).toOption.map (·.value) = some 5000 ∧
      (2, 5000) ∈ smallVault.b.confirmed ∧
      smallVault.denominator { txid := 9, inputs := [1], fee := 215 } = 105000 ∧
      smallVault.coverOk { txid := 9, inputs := [1], fee := 215 } = true := by
  decide +kernel

/-- The same spend at a later read: an external 200 000 has confirmed. The node's denominator is
now 305 000 and the composed request no longer covers there. Composer success is coverage at the read
it was composed at, never at another. -/
@[req "DUR-22"]
theorem later_read_refuses :
    let later := at_ 201 [(1, 100000), (2, 5000), (3, 200000)] 1
    later.denominator { txid := 9, inputs := [1], fee := 215 } = 305000 ∧
      later.coverOk { txid := 9, inputs := [1], fee := 215 } = false := by
  decide +kernel

/-- 100 000 ordinary and a 100 000 coinbase confirmed at height 150, at tip 200. -/
def bigVault : Vault := at_ 200 [(1, 100000), (2, 100000)] 1
def bigPass : Pass := pass [(1, ordinaryAt 10 100000), (2, coinbaseAt 150 100000)]

/-- **Immature value beyond the coverage: the spend refuses before signing.** `CHN-21` alone passes
over coin 1 — the composer builds that request — but `99 785 × 100 < 200 000 × 51`, so the command
refuses with `I` and the height `150 + 99`, and no request exists to sign. -/
@[req "OPR-38"]
theorem exceeding_refuses :
    err (composeSpend lim 9 bigVault bigPass) = some (.immature 100000 249) ∧
      (composeEvery lim 9 (view bigVault [(1, 100000)])).toOption =
        some { txid := 9, inputs := [1], fee := 215 } ∧
      Coverage.covers 99785 100000 Coverage.floorPct = true := by
  decide +kernel

/-- **Coverage equality passes, and one satoshi more refuses.** With a zero fee, `51 000 × 100 =
(51 000 + 49 000) × 51`. -/
@[req "OPR-38"]
theorem equality_passes :
    (composeSpend lim 9 (at_ 200 [(1, 51000), (2, 49000)])
        (pass [(1, ordinaryAt 10 51000), (2, coinbaseAt 150 49000)])).toOption =
      some { txid := 9, inputs := [1], fee := 0 } ∧
    err (composeSpend lim 9 (at_ 200 [(1, 51000), (2, 49001)])
        (pass [(1, ordinaryAt 10 51000), (2, coinbaseAt 150 49001)])) = some (.immature 49001 249) := by
  decide +kernel

/-! #### Evidence -/

/-- **An invalid scanned coinbase record refuses the inventory instead of being left out.** The
creating transaction's output disagrees with the scanned value; its inputs mix the coinbase with a
prevout; its header is not on the active chain. Each refuses the whole spend, claw-back and refresh,
although the coin would otherwise be an immature coinbase. -/
@[req "OPR-33"]
theorem invalid_coinbase_refuses :
    let bad := pass [(1, ordinaryAt 10 100000),
      (2, { coinbaseAt 150 5000 with tx := { (coinbaseAt 150 5000).tx with value := 4999 } })]
    let mixed := pass [(1, ordinaryAt 10 100000),
      (2, { coinbaseAt 150 5000 with tx := { (coinbaseAt 150 5000).tx with inputs := [.coinbase, .prevout 3] } })]
    let stale := pass [(1, ordinaryAt 10 100000),
      (2, { coinbaseAt 150 5000 with tx := { (coinbaseAt 150 5000).tx with active := false } })]
    err (composeSpend lim 9 smallVault bad) = some (.inventory .evidence) ∧
      err (composeSpend lim 9 smallVault mixed) = some (.inventory .evidence) ∧
      err (composeSpend lim 9 smallVault stale) = some (.inventory .evidence) ∧
      err (composeClaw smallVault bad (.outpoints [1])) = some (.inventory .evidence) ∧
      err (composeClaw smallVault mixed (.outpoints [1])) = some (.inventory .evidence) ∧
      err (composeClaw smallVault stale (.outpoints [1])) = some (.inventory .evidence) ∧
      refresh smallVault bad (fun _ => true) = .refused .evidence ∧
      refresh smallVault mixed (fun _ => true) = .refused .evidence ∧
      refresh smallVault stale (fun _ => true) = .refused .evidence ∧
      kind [.coinbase, .prevout 3] = none := by
  decide +kernel

/-! #### The maturity boundary -/

/-- A 5 000 coinbase confirmed at height 100 beside 100 000 ordinary, at tip `tip`. -/
def boundary (tip : Nat) : Vault := at_ tip [(1, 100000), (2, 5000)]
def boundaryPass : Pass := pass [(1, ordinaryAt 10 100000), (2, coinbaseAt 100 5000)]

/-- **Confirmations 1, 98 and 99: still immature.** At tips 100, 197 and 198 the coin is left out of
`U` and counted in `I`. -/
@[req "OPR-33"]
theorem immature_below_hundred :
    [100, 197, 198].map (confirmations · 100) = [1, 98, 99] ∧
      [100, 197, 198].all (fun tip => !mature tip 100) ∧
      [100, 197, 198].all (fun tip =>
        (accept (boundary tip) boundaryPass).toOption.map (·.inventory) = some [(1, 100000)] &&
          (accept (boundary tip) boundaryPass).toOption.map (·.value) = some 5000) := by
  decide +kernel

/-- **Confirmations 100: equality admits maturity.** At tip 199 = 100 + 99 the coin is in `U` and the
spend spends it. -/
@[req "OPR-33"]
theorem mature_at_hundred :
    confirmations 199 100 = 100 ∧ mature 199 100 = true ∧
      (accept (boundary 199) boundaryPass).toOption.map (·.inventory) =
        some [(1, 100000), (2, 5000)] ∧
      (composeSpend lim 9 (boundary 199) boundaryPass).toOption.map (·.inputs) = some [1, 2] := by
  decide +kernel

/-! #### Several, and all -/

def severalVault : Vault := at_ 200 [(1, 10000), (2, 3000), (3, 4000), (4, 5000)]
def severalPass : Pass :=
  pass [(1, ordinaryAt 10 10000), (2, coinbaseAt 120 3000), (3, coinbaseAt 180 4000), (4, coinbaseAt 150 5000)]

/-- **Several immature coinbases at different heights.** `I` is 12 000, their sum, and the report's
height is 279: the last of them, confirmed at 180, matures there, and at 278 it has 99. -/
@[req "OPR-38"]
theorem several_sum_and_last :
    err (composeSpend lim 9 severalVault severalPass) = some (.immature 12000 279) ∧
      mature 278 180 = false ∧ [120, 180, 150].all (mature 279) := by
  decide +kernel

def allVault : Vault := at_ 200 [(2, 5000), (3, 6000)]
def allPass : Pass := pass [(2, coinbaseAt 150 5000), (3, coinbaseAt 160 6000)]

/-- **All scanned value immature: no empty spend and no empty all-coins claw-back.** The spend refuses
with the additional check's report, `--all` has no target, and refresh is the no-op holding both back. -/
@[req "OPR-33"]
theorem all_immature :
    err (composeSpend lim 9 allVault allPass) = some (.immature 11000 259) ∧
      err (composeClaw allVault allPass .all) = some .emptyTarget ∧
      refresh allVault allPass (fun _ => true) = .noop 2 := by
  decide +kernel

/-! #### Claw-back -/

def clawVault : Vault := at_ 200 [(1, 60000), (2, 40000), (3, 5000)]
def clawPass : Pass := pass [(1, ordinaryAt 10 60000), (2, ordinaryAt 20 40000), (3, coinbaseAt 150 5000)]

/-- **A known-outpoint claw-back over other valid coins composes.** The immature coin 3 outside `T` does
not refuse it; naming coin 3 refuses; `--all` names `U` and reports one coin left out; `--replace`
composes over its recorded outpoints without the scan. -/
@[req "OPR-68"]
theorem clawback_outside_target :
    (composeClaw clawVault clawPass (.outpoints [1, 2])).toOption =
        some { inputs := [1, 2], leftOutCount := none } ∧
      err (composeClaw clawVault clawPass (.outpoints [3])) = some .immatureTarget ∧
      err (composeClaw clawVault clawPass (.outpoints [2, 3])) = some .immatureTarget ∧
      err (composeClaw clawVault clawPass (.outpoints [4])) = some .notInventory ∧
      (composeClaw clawVault clawPass .all).toOption = some { inputs := [1, 2], leftOutCount := some 1 } ∧
      (composeClaw clawVault clawPass (.replace [3])).toOption = some { inputs := [3], leftOutCount := none } := by
  decide +kernel

/-! #### Refresh -/

/-- **Refresh over eligible ordinary coins does not select the immature output.** With every coin old
enough, it batches coins 1 and 2 and holds coin 3 back; with only coin 1 old enough, it holds back two. -/
@[req "OPR-65"]
theorem refresh_skips_immature :
    refresh clawVault clawPass (fun _ => true) = .batches [(1, 60000), (2, 40000)] 1 ∧
      refresh clawVault clawPass (fun o => o == 1) = .batches [(1, 60000)] 2 := by
  decide +kernel

/-- **A refresh scan of only valid immature coinbases is the successful no-op**: it holds both back,
exits `0` and writes no authorization. An empty scan is not that no-op: it refuses and exits `1`. -/
@[req "OPR-65"]
theorem refresh_only_immature_noop :
    refresh allVault allPass (fun _ => true) = .noop 2 ∧
      (refresh allVault allPass (fun _ => true)).exit = some 0 ∧
      (refresh allVault allPass (fun _ => true)).authorizes = some false ∧
      (refresh (at_ 200 []) (pass []) (fun _ => true)).exit = some 1 := by
  decide +kernel

/-! #### Reorganization and later passes -/

/-- **A reorganization after apparent maturity recomputes maturity and the inventory.** At tip 199 the
coinbase confirmed at height 100 has 100 confirmations and the spend spends it. A reorganization puts
its block at height 105 of the new chain, tip 200: 96 confirmations, so it is left out again and the
spend refuses with the new clearing height, 204. -/
@[req "OPR-33"]
theorem reorg_recomputes :
    (composeSpend lim 9 (at_ 199 [(1, 10000), (2, 50000)])
        (pass [(1, ordinaryAt 10 10000), (2, coinbaseAt 100 50000)])).toOption.map (·.inputs) = some [1, 2] ∧
    err (composeSpend lim 9 (at_ 200 [(1, 10000), (2, 50000)])
        (pass [(1, ordinaryAt 10 10000), (2, coinbaseAt 105 50000)])) = some (.immature 50000 204) := by
  decide +kernel

/-- **A later new immature coinbase: the old reported height is no outage bound.** The first pass, at
tip 200, refuses until 249. At tip 249 that coin is mature and spent, but a new 300 000 coinbase
confirmed at 240 refuses the spend again, until 339. -/
@[req "OPR-38"]
theorem later_coinbase_no_bound :
    err (composeSpend lim 9 bigVault bigPass) = some (.immature 100000 249) ∧
    err (composeSpend lim 9 (at_ 249 [(1, 100000), (2, 100000), (3, 300000)] 1)
        (pass [(1, ordinaryAt 10 100000), (2, coinbaseAt 150 100000), (3, coinbaseAt 240 300000)])) =
      some (.immature 300000 339) := by
  decide +kernel

/-- **A chain that does not advance.** The tip is a height, not a clock: at tip 200, with the mempool
read changed and the backend's sequence moved on, the pass refuses with the same report, below its
clearing height. Nothing in the model advances the tip, so no theorem here claims that waiting reaches
249. -/
@[req "OPR-38"]
theorem stalled_chain_no_progress :
    let later : Vault := { bigVault with b := { bigVault.b with sequence := 9, mempool := [(777, [55])] } }
    err (composeSpend lim 9 later bigPass) = err (composeSpend lim 9 bigVault bigPass) ∧
      err (composeSpend lim 9 later bigPass) = some (.immature 100000 249) ∧
      later.b.tip.height < 249 := by
  decide +kernel

end BtcPolicy.Exhibits.Coinbase
