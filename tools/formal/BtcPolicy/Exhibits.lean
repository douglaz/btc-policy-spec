import BtcPolicy.Evaluate
import BtcPolicy.Cursor
import BtcPolicy.Coverage
import BtcPolicy.Deadline
import BtcPolicy.Classification
import BtcPolicy.Membership
import BtcPolicy.RefreshAge
import BtcPolicy.Kernel
import BtcPolicy.Budget
import BtcPolicy.Ledger
import BtcPolicy.Silence
import BtcPolicy.Delivery
import BtcPolicy.Chain
import BtcPolicy.Watchtower
import BtcPolicy.VaultUnspent
import BtcPolicy.Alerts
import BtcPolicy.Package
import BtcPolicy.Trace
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
`DUR-30` now says (`split_finalizes_lower_latch`, for every such pair). Under the withdrawn
anchor nothing is released and nothing finalizes (`split_on_cursor_finalizes_nothing`). -/
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
      (fun c => c.id == 1 && due current envFire c && heldQuorum A.t c && !c.released) = true ∧
    assembled.node.cands.any (fun c => c.id == 1 && c.packageOk) = false := by
  decide

/-! ### `DUR-29`'s race under both values, over one `step` -/

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

/-! ### `F57` row 8: a defeated hot spend at Hold expiry after the claw-back is evicted -/

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

/-- `DEF-5` on the same trace: the defeated spend is off the pending projection and still
resident — one flag, one flip. -/
@[req "SPN-30"]
theorem def5_pending_is_projection :
    pending envFire (run current w0 f57Trace).1.node = [] ∧
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
admitted at 100, the age-out that lets the second acceptance pass `POL-16` at 121, and the
completion at 141 as a fresh exposure. The fifth — that pruning has not collected the first
candidate — is vacuous here, because the run prunes nothing. -/

def V : Nat := 100
def cfg : Config := { cap := V, window := Budget.params.window }

def A : Node :=
  { id := 0, t := Budget.params.t, armed := false, poisoned := false, lockedDown := false,
    carriers := [], cands := [], T := Wall.sample 0, sweepActive := false, selected := [],
    duressDelay := 200, epsilon := 5, combineSlack := Budget.params.slack }

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
def timedRun (mk : Nat → Env) (g : Settlement) :
    List (Nat × Event) → Sys → Sys × List (Nat × Effect)
  | [], sys => (sys, [])
  | (n, e) :: rest, sys =>
    let stepped := sysStep g cfg Kernel.current (mk n) sys e
    let ran := timedRun mk g rest stepped.1
    (ran.1, (stepped.2.map fun eff => (n, eff)) ++ ran.2)

def steps (mk : Nat → Env) (tr : List (Nat × Event)) : List (Env × Event) :=
  tr.map fun x => (mk x.1, x.2)

/-- Stamping the effects changes no state: the run is `Ledger.sysRun`'s. -/
theorem timedRun_is_sysRun (mk : Nat → Env) (g : Settlement) :
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
def completions (mk : Nat → Env) (g : Settlement) (tr : List (Nat × Event)) : List (Nat × Nat) :=
  (timedRun mk g tr sys0).2.filterMap fun x =>
    match x.2 with
    | .broadcast txid => some (x.1, amountOf txid)
    | .queuePartial _ _ _ _ => none

def completedInWindow (start window : Nat) (cs : List (Nat × Nat)) : Nat :=
  ((cs.filter fun c => start ≤ c.1 && c.1 < start + window).map (·.2)).sum

/-! ### `ADR-0014`'s delayed-holder trace -/

/-- The trace, at `Budget.timeline`'s instants. The holder decision arrives at 100, which is why
the first release and its completion are there and not at the Hold; the second acceptance is at
121, the first instant at which the first reservation has aged out under both of `POL-19`'s
disjuncts (`Budget.reservation_boundary`); its Hold matures at 141.

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
    (timedRun withClaw .refundOnAnySettlement def5 sys0).1.led.map (·.cid) = [7] ∧
    (timedRun withClaw .refundOnAnySettlement def5 sys0).1.world.node.cands.any (·.id == 7) = true ∧
    exposedQuorum (timedRun withClaw .refundOnAnySettlement def5 sys0).1.world s1 = true := by decide

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
/-- The expiry sweep, one sample past the twin's signed expiry and no further: its HotClock is
still inside the twin's trailing window, so age-out cannot collect it. -/
def sweepAt : Env := envOf (expiryOf twinAccept + 1) Budget.timeline.secondAccept

/-- Two commitments over one transaction are metered twice — `2V` against a cap of `V` — and the
two charges then leave by different doors. `markExposed` sets the released twin's bit; at
`deadAt` both of `POL-19`'s disjuncts are dead for that row and it ages out, while the twin
survives on its own later reservation; at `sweepAt` age-out STILL cannot collect the twin, and it
is the expiry sweep that does (`SPN-33`: "An unexposed retained charge may be refunded after its
signed expiry strictly passes"). The fifth conjunct is what makes the sweep load-bearing rather
than decorative: age-out at the sweep's own environment leaves the charge standing.

The single-commitment history reaches the same empty ledger without the sweep at all, which is
`F63`'s point that the refund reaches no state age-out would not have reached alone. -/
@[req "POL-18"]
theorem f63_twins_end_charging_nothing :
    liveSum (markExposed twinNode twinLed) = 2 * V ∧
    (markExposed twinNode twinLed).map (·.exposed) = [true, false] ∧
    liveSum (ageOut deadAt cfg.window (markExposed twinNode twinLed)) = V ∧
    (ageOut deadAt cfg.window (markExposed twinNode twinLed)).map (·.cid) = [9] ∧
    liveSum (ageOut sweepAt cfg.window
      (ageOut deadAt cfg.window (markExposed twinNode twinLed))) = V ∧
    liveSum (refundAtSweep sweepAt (ageOut sweepAt cfg.window
      (ageOut deadAt cfg.window (markExposed twinNode twinLed)))) = 0 ∧
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

/-- 2-of-3, `duress_delay_secs` 200, `epsilon_secs` 5, `combine_slack_secs` 40. -/
def A : Node :=
  { id := 0, t := 2, armed := false, poisoned := false, lockedDown := false, carriers := [],
    cands := [], T := Wall.sample 0, sweepActive := false, selected := [], duressDelay := 200,
    epsilon := 5, combineSlack := 40 }

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
/-- A hot spend whose Hold matures at 100, well before the `T` the arm wrote. -/
def s2 : Cand := cand 5 hot2 true (some 100) 400
def e2 : Cand := cand 6 esc2 false none 400

/-- Ingress at 50 under the PIN the first table makes a duress PIN, and the relay that reaches
`t` at 60: the holder decision writes `T = max(min(50 + 200, 300 − 5), 60) = 250` under both
tables (`DUR-13`), and arms only the first world. -/
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
dynamic `T`, with `SPN-32`'s preserving registration. Every guard-parameter hypothesis is
discharged here; the workflow holds each flip to its measured failures. -/
@[req "DUR-1"]
theorem silence_with_current {gs : Settlement} (tbl₀ tbl₁ : Enrolment)
    (tr : List (Env × Input)) (a b : Sys) (hc : Coupled a b)
    (hinv : ∀ env i rest, tr = (env, i) :: rest →
      NodeInv a.world.node env.eff ∧ NodeInv b.world.node env.eff)
    (hm : MonotoneSamples (tr.map fun x => (x.1, x.2.event tbl₀))) :
    ∀ y ∈ obsPair Silence.current gs cfg Kernel.current tbl₀ tbl₁ a b tr, y.1 = y.2 :=
  silence rfl rfl rfl rfl tbl₀ tbl₁ tr a b hc hinv hm

/-- The invariant the relation takes, at the state both runs start from: no candidate, no Carrier,
unarmed, with duplicate-free resident ids and `DUR-10`'s two flags agreeing. The other
clauses are vacuous on the empty candidate list. -/
theorem nodeInv_A (now : Effective) : NodeInv A now :=
  ⟨rfl, fun _ c hc => absurd hc (by simp [A]), fun h => absurd h (by simp [A]),
    fun c hc => absurd hc (by simp [A]), fun c hc => absurd hc (by simp [A]),
    fun h => absurd h (by simp [A]), by simp [A]⟩

/-- And the relation applied: every hypothesis discharged at a concrete pair of runs, so the
theorem is known to say something about the traces the exhibits below compute. -/
@[req "DUR-1"]
theorem silence_on_armTrace :
    ∀ y ∈ pairs Silence.current Kernel.current armTrace, y.1 = y.2 := by
  refine silence_with_current tblD tblN armTrace sys0 sys0 ⟨rfl, rfl, rfl⟩
    (fun _ _ _ _ => ⟨nodeInv_A _, nodeInv_A _⟩) ?_
  simp only [armTrace, List.map_cons, List.map_nil]
  exact ⟨by decide, by decide, trivial⟩

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

/-- Fill the Hot ledger, refuse a different pair, let the charge age out, and accept the pair
selected by the refused Carrier. No alternate evaluator or initial ledger is supplied. -/
def budgetRepeatTrace : List (Env × Input) :=
  [(envAt 1 1, .request 20 0 (Wall.sample 40)
      (cand 5 { id := 102, inputs := [2], outflow := 995 } true (some 30) 40)
      (cand 6 esc2 false none 40)),
   (envAt 50 50, .request 10 1 (Wall.sample 400) s1 e1),
   (envAt 60 60, .pinless (.receipt 10 1)),
   (envAt 130 130, .request 11 0 (Wall.sample 400) s1 e1),
   (envAt 140 140, .pinless (.receipt 11 1)),
   (envAt 150 150, .pinless .firePass)]

/-- Check each entering state by replaying its proper prefix through the composed transition.
This checks the horizon only; observation coverage is asserted independently below. -/
def allPreHorizon (r : Rules) (tbl : Enrolment) (tr : List (Env × Input)) : Bool :=
  tr.zipIdx.all fun ((env, _), j) => preHorizon env (runOf r tbl (tr.take j)).world.node

def fullSilent (g : Marker) (r : Rules) (tr : List (Env × Input)) : Prop :=
  (pairs g r tr).length = tr.length ∧
  allPreHorizon r tblD tr = true ∧ allPreHorizon r tblN tr = true ∧
  (pairs g r tr).all (fun y => y.1 == y.2) = true

instance (g : Marker) (r : Rules) (tr : List (Env × Input)) : Decidable (fullSilent g r tr) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- General equality, with the initial invariant, coupling and sample premises discharged. -/
@[req "DUR-1"]
theorem silence_on_resubTrace :
    ∀ y ∈ pairs Silence.current Kernel.current resubTrace, y.1 = y.2 := by
  apply silence_with_current tblD tblN resubTrace sys0 sys0 ⟨rfl, rfl, rfl⟩
    (fun _ _ _ _ => ⟨nodeInv_A _, nodeInv_A _⟩)
  simp only [resubTrace, armTrace, List.cons_append, List.nil_append, List.map_cons, List.map_nil, MonotoneSamples]
  decide

@[req "DUR-1"]
theorem silence_on_repeatTrace (samePin : Bool) :
    ∀ y ∈ pairs Silence.current Kernel.current (repeatTrace samePin), y.1 = y.2 := by
  apply silence_with_current tblD tblN (repeatTrace samePin) sys0 sys0 ⟨rfl, rfl, rfl⟩
    (fun _ _ _ _ => ⟨nodeInv_A _, nodeInv_A _⟩)
  simp only [repeatTrace, armTrace, List.cons_append, List.nil_append, List.map_cons, List.map_nil, MonotoneSamples]
  decide

@[req "DUR-1"]
theorem silence_on_refusedRepeatTrace (samePin hot : Bool) :
    ∀ y ∈ pairs Silence.current Kernel.current (refusedRepeatTrace samePin hot), y.1 = y.2 := by
  apply silence_with_current tblD tblN (refusedRepeatTrace samePin hot) sys0 sys0 ⟨rfl, rfl, rfl⟩
    (fun _ _ _ _ => ⟨nodeInv_A _, nodeInv_A _⟩)
  simp only [refusedRepeatTrace, List.map_cons, List.map_nil, MonotoneSamples]
  decide

@[req "DUR-1"]
theorem silence_on_budgetRepeatTrace :
    ∀ y ∈ pairs Silence.current Kernel.current budgetRepeatTrace, y.1 = y.2 := by
  apply silence_with_current tblD tblN budgetRepeatTrace sys0 sys0 ⟨rfl, rfl, rfl⟩
    (fun _ _ _ _ => ⟨nodeInv_A _, nodeInv_A _⟩)
  simp only [budgetRepeatTrace, List.map_cons, List.map_nil, MonotoneSamples]
  decide

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
pair, and stages a closed Carrier. Later age-out permits acceptance and its own holder decision. -/
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
recomputes `T` from `DUR-13`'s scan over exactly these candidates (`F64`). So this is the invariant
failing, not a trace of the partial leaving. -/
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

/-! ### `F64`: a later holder decision rewrites `T` on an armed node -/

def sp3 : Cand := cand 7 { id := 300, inputs := [4], outflow := 0 } false none 900
def es3 : Cand := cand 8 { id := 301, inputs := [4, 5], outflow := 0 } false none 900

/-- A second pair, of the same class under both tables, accepted at 600 and committed at 610 —
after the first spend's expiry, so `DUR-13`'s scan finds no pending hot candidate. -/
def growthTrace : List (Env × Input) :=
  armTrace ++ [ (envAt 600 600, .request 30 0 (Wall.sample 900) sp3 es3),
                (envAt 610 610, .pinless (.receipt 30 1)) ]

/-- `DUR-5` makes the overlay write pin-uniform and `DUR-13` gives its value, so every holder
decision writes `T` — and on an armed node a later one writes a LARGER `T` than the arm did. The
clause constrains "a later arm", not a later normal commit, and nothing else here bounds the
deadline from above. Recorded as `F64`; the SILENCE relation (`ADR-0023` decision 14) is unaffected, because the
value it needs is that `T` is at or before every pending hot candidate's fire time, which
`DUR-13`'s scan supplies at each write. -/
@[req "DUR-13"]
theorem later_commit_grows_T :
    (runOf Kernel.current tblD armTrace).world.node.T = Wall.sample 250 ∧
    (runOf Kernel.current tblD growthTrace).world.node.T = Wall.sample 800 ∧
    (runOf Kernel.current tblD growthTrace).world.node.armed = true := by
  decide

/-! ### `F60`: a backward effective sample after the arm, and what the premise is worth

`silence` carries `MonotoneSamples` on its trace, and its docstring says why: "without the last,
`F60`'s corrected clock opens a window below `T` in one world and not the other, and the relation
is false". That sentence is the claim executed here. Everything below is OUTSIDE the relation's
premises; none of it refutes `silence`, which says nothing about a trace that steps backward. -/

/-- `F60`'s hot candidate: the Hold matures at 90, so `DUR-13`'s ceiling is `90 − 5`. -/
def s60 : Cand := cand 1 hot1 true (some 90) 400

/-- `F60`'s trace. Ingress at 40 with `duress_delay_secs` 200, the holder decision at 100 writing
`T = max(min(40 + 200, 90 − 5), 100) = 100` under both tables (`DUR-13`), and then a wall
corrected back to 95 with no accept between — `SPN-13`'s high-water "is advanced, on an accept
only", so nothing holds the effective sample up — and a fire pass in the gap. -/
def backTrace : List (Env × Input) :=
  [ (envAt 40 40, .request 10 1 (Wall.sample 400) s60 e1),
    (envAt 100 100, .pinless (.receipt 10 1)),
    (envAt 95 101, .pinless .firePass) ]

/-- The step `MonotoneSamples` forbids, named on its own: the third environment's effective sample
is strictly before the second's, while its HotClock is not. `NCH-41`'s Mono is process-lifetime
and does not step back; `F60` corrects the wall alone, so only the first conjunct of the premise
fails. -/
theorem f60_sample_steps_backward :
    (envAt 100 100).eff.notAfter (envAt 95 101).eff = false ∧
    (envAt 100 100).mono.notAfter (envAt 95 101).mono = true := by decide

/-- The deadline the arm wrote, at the value `F60` records. -/
@[req "DUR-13"]
theorem f60_T_is_the_arm_sample :
    (runOf Kernel.current tblD backTrace).world.node.T = Wall.sample 100 := by decide

/-- And the leak. All three steps are inside the horizon — 95 is strictly below the `T` of 100, so
`preHorizon` admits the fire pass in both worlds — and the third pair is unequal: the world whose
table made the PIN ordinary queues a hot partial, and the armed world's `DUR-11` freeze holds it.
A PIN-dependent observable strictly before `T`, which `DUR-1` forbids: "Every observable a node
emits MUST be identical between a normal-PIN and a duress-PIN request".

This is `F60` reproduced, not a repair of it, and not a counterexample to `silence`: the trace
fails that theorem's `MonotoneSamples` premise at `f60_sample_steps_backward`. Neither direction
the finding names is chosen here. -/
@[req "DUR-1"]
theorem f60_backward_step_leaks :
    (pairs Silence.current Kernel.current backTrace).length = 3 ∧
    ((pairs Silence.current Kernel.current backTrace).map fun y => y.1 == y.2)
      = [true, true, false] ∧
    ((pairs Silence.current Kernel.current backTrace).map fun y => y.1.effects)
      = [[], [], []] ∧
    ((pairs Silence.current Kernel.current backTrace).map fun y => y.2.effects)
      = [[], [], [Effect.queuePartial (sighash hot1 0) 0 true 1]] := by
  decide

end BtcPolicy.Exhibits.TwoRun

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
theorem earliest_pair_ingress : timeChecks current.ingressTime = true := by decide

@[req "NCH-34"]
theorem tombstones_have_no_holder_authority : authorityChecks current = true := by decide

/-- The refusal and isolation regressions fix the inheritance choices, whose independent flips
are checked above; they exercise the local-acceptance boundary with inherited metadata. -/
@[req "DUR-5"]
theorem inherited_refusal_opens_nothing :
    InheritanceCases.refusalChecks { current with
      inheritance := .inherit, intentRetention := .tombstones, ingressTime := .earliestPair } = true := by decide

@[req "DUR-13"]
theorem unbound_and_unrelated_metadata_stay_separate :
    isolatedChecks { current with
      inheritance := .inherit, intentRetention := .tombstones, ingressTime := .earliestPair } = true := by decide

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

namespace BtcPolicy.Exhibits.Evaluate
open BtcPolicy.Evaluate

@[req "POL-10"]
def softenCode : Policy.Code → Policy.Code
  | .CHANGE_NOT_DERIVABLE => .DEST_NOT_ALLOWED
  | c => c

/-- Only the destination refusal spelling is collapsed; acceptance and other codes stay put.
The local induction reads the executable recognition line directly, independently of all
mutation-sensitive characterisation lemmas below. Equal wrong map lengths are included. -/
@[req "POL-10"]
theorem hints_never_admit (cfg : Cfg) (p : Psbt) (hs : List Bool)
    (hlen : hs.length = p.outputHints.length) :
    (evaluate cfg { p with outputHints := hs }).map softenCode =
      (evaluate cfg p).map softenCode := by
  have scan : ∀ os a b, (firstUnknown cfg os a).isSome = (firstUnknown cfg os b).isSome := by
    intro os
    induction os with
    | nil => intro a b; rfl
    | cons o os ih =>
      intro a b
      simp only [firstUnknown, recognised]
      split
      · exact ih a.tail b.tail
      · rfl
  have same : inconsistent { p with outputHints := hs } = inconsistent p := by
    simp [inconsistent, hlen]
  simp only [evaluate, request, same]
  by_cases hc : inconsistent p = true
  · simp [hc]
  · simp only [hc]
    have hscan := scan p.txOutputs hs p.outputHints
    simp only [destination, unknownInput, outputs, totalIn, totalOut]
    cases ha : firstUnknown cfg p.txOutputs hs with
    | none =>
      cases hb : firstUnknown cfg p.txOutputs p.outputHints with
      | none => rfl
      | some b => simp [ha, hb] at hscan
    | some a =>
      cases hb : firstUnknown cfg p.txOutputs p.outputHints with
      | none => simp [ha, hb] at hscan
      | some b =>
        generalize p.inputMaps.any (fun m => m.any fun o => !owned cfg o) = u
        cases u <;> cases a <;> cases b <;>
          simp [Policy.evaluateSpend, Policy.evaluate, Policy.Check.order, Policy.failure,
            softenCode, List.findSome?]

@[req "POL-10"]
theorem hints_acceptance_iff (cfg : Cfg) (p : Psbt) (hs : List Bool)
    (hlen : hs.length = p.outputHints.length) :
    evaluate cfg { p with outputHints := hs } = none ↔ evaluate cfg p = none := by
  have h := hints_never_admit cfg p hs hlen
  have hnone := congrArg (fun x => x = none) h
  simpa using hnone

@[req "POL-10"]
theorem recognised_iff (cfg : Cfg) (o : Encode.Output) (hint : Bool) :
    recognised cfg o hint = true ↔ (output cfg o).kind ≠ .unknown := by
  simp only [recognised, Classification.allowlisted, List.all_cons, List.all_nil,
    Bool.and_true, Classification.inVault, Classification.inAllowlist]
  rw [output_member]
  cases hk : Membership.kindOf cfg.derive cfg.max cfg.vault cfg.escape cfg.allow o.script <;>
    simp [output, hk]

@[req "POL-10"]
theorem firstUnknown_none_iff (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) :
    firstUnknown cfg os hs = none ↔ ∀ o ∈ os, (output cfg o).kind ≠ .unknown := by
  induction os generalizing hs with
  | nil => simp [firstUnknown]
  | cons o os ih =>
    simp only [firstUnknown]
    split <;> simp_all [recognised_iff]

/-- A recognised prefix followed by an unknown output identifies the least unknown position.
The suffix is unrestricted, including all of its hints. -/
@[req "POL-10"]
def FirstAt (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) (hint : Bool) : Prop :=
  ∃ pre o post, os = pre ++ o :: post ∧
    (∀ x ∈ pre, (output cfg x).kind ≠ .unknown) ∧
    (output cfg o).kind = .unknown ∧ hs[pre.length]?.getD false = hint

@[req "POL-10"]
theorem firstUnknown_some_iff (cfg : Cfg) (os : List Encode.Output) (hs : List Bool) (b : Bool) :
    firstUnknown cfg os hs = some b ↔ FirstAt cfg os hs b := by
  induction os generalizing hs with
  | nil => simp [firstUnknown, FirstAt]
  | cons o os ih =>
    simp only [firstUnknown]
    by_cases hk : (output cfg o).kind = .unknown
    · have hr : recognised cfg o (hs.headD false) = false := by
        simpa [Bool.eq_false_iff, recognised_iff] using hk
      simp only [hr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      constructor
      · intro hb
        exact ⟨[], o, os, rfl, by simp, hk, by cases hs <;> simpa using hb⟩
      · rintro ⟨pre, x, post, he, hp, hx, hb⟩
        cases pre with
        | nil => simp only [List.nil_append, List.cons.injEq] at he
                 obtain ⟨rfl, rfl⟩ := he
                 cases hs <;> simpa using hb
        | cons y pre =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, _⟩ := he
          exact False.elim (hp o (by simp) hk)
    · have hr := (recognised_iff cfg o (hs.headD false)).mpr hk
      simp only [hr, ↓reduceIte, ih]
      constructor
      · rintro ⟨pre, x, post, he, hp, hx, hb⟩
        refine ⟨o :: pre, x, post, by simp [he], ?_, hx, ?_⟩
        · simpa using And.intro hk hp
        · simpa using hb
      · rintro ⟨pre, x, post, he, hp, hx, hb⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, _⟩ := he
          exact False.elim (hk hx)
        | cons y pre =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, he⟩ := he
          exact ⟨pre, x, post, he, fun z hz => hp z (by simp [hz]), hx, by simpa using hb⟩

@[req "POL-10"]
theorem allowlisted_iff (cfg : Cfg) (p : Psbt) :
    Classification.allowlisted (outputs cfg p) = true ↔
      ∀ o ∈ p.txOutputs, (output cfg o).kind ≠ .unknown := by
  simp only [outputs, Classification.allowlisted, List.all_map, List.all_eq_true]
  apply forall_congr'; intro o
  apply imp_congr_right; intro _
  simpa [recognised, Classification.allowlisted] using recognised_iff cfg o false

@[req "POL-10"]
theorem dest_allowed_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).dest = .allowed ↔
      ∀ o ∈ p.txOutputs, (output cfg o).kind ≠ .unknown := by
  rw [← firstUnknown_none_iff cfg p.txOutputs p.outputHints]
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte, destination]
  cases firstUnknown cfg p.txOutputs p.outputHints with
  | none => simp
  | some b => cases b <;> simp

@[req "POL-10"]
theorem dest_notAllowed_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).dest = .notAllowed ↔ FirstAt cfg p.txOutputs p.outputHints false := by
  rw [← firstUnknown_some_iff]
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte, destination]
  cases firstUnknown cfg p.txOutputs p.outputHints with
  | none => simp
  | some b => cases b <;> simp

@[req "POL-10"]
theorem dest_changeNotDerivable_iff (cfg : Cfg) (p : Psbt) (h : Consistent p) :
    (request cfg p).dest = .changeNotDerivable ↔ FirstAt cfg p.txOutputs p.outputHints true := by
  rw [← firstUnknown_some_iff]
  simp only [request, (consistent_iff p).mpr h, Bool.false_eq_true, ↓reduceIte, destination]
  cases firstUnknown cfg p.txOutputs p.outputHints with
  | none => simp
  | some b => cases b <;> simp

@[req "POL-6"]
theorem acceptance_exact (cfg : Cfg) (p : Psbt) :
    evaluate cfg p = none ↔ Consistent p ∧ Owned cfg p ∧
      Classification.allowlisted (outputs cfg p) = true ∧
      Classification.hotBudgetOk (outputs cfg p) cfg.hotMaxPerTx = true ∧
      Classification.feeCapOk (totalIn p) (totalOut p) = true := by
  have abstract (r : Policy.Request) : Policy.evaluateSpend r = none ↔
      r.psbtInconsistent = false ∧ r.unknownInput = false ∧ r.dest = .allowed ∧
      r.overHotCap = false ∧ r.fee = .ok := by
    rcases r with ⟨a,b,c,d,e⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
  by_cases hc : Consistent p
  · rw [evaluate, abstract]
    have hd := dest_allowed_iff cfg p hc
    rw [← allowlisted_iff] at hd
    simp only [request, (consistent_iff p).mpr hc, Bool.false_eq_true, ↓reduceIte] at hd ⊢
    simp [hc, hd, unknownInput_false_iff, feeOf_ok_iff]
  · have hi : inconsistent p = true := by
      cases hi : inconsistent p
      · exact False.elim (hc ((consistent_iff p).mp hi))
      · rfl
    simp [evaluate, request, hi, hc, Policy.evaluateSpend, Policy.evaluate,
      Policy.Check.order, Policy.failure]

@[req "POL-10"]
theorem first_failing_output (cfg : Cfg) (p : Psbt) (hc : Consistent p) (ho : Owned cfg p)
    (pre : List Encode.Output) (o : Encode.Output) (post : List Encode.Output)
    (hp : p.txOutputs = pre ++ o :: post)
    (hr : ∀ x ∈ pre, (output cfg x).kind ≠ .unknown) (hu : (output cfg o).kind = .unknown) :
    evaluate cfg p = some (if p.outputHints[pre.length]?.getD false then
      .CHANGE_NOT_DERIVABLE else .DEST_NOT_ALLOWED) := by
  have hs := (firstUnknown_some_iff cfg p.txOutputs p.outputHints
    (p.outputHints[pre.length]?.getD false)).mpr ⟨pre, o, post, hp, hr, hu, rfl⟩
  have hi := (unknownInput_false_iff cfg p).mpr ho
  simp only [evaluate, request, (consistent_iff p).mpr hc, Bool.false_eq_true, ↓reduceIte,
    hi, destination, hs]
  cases p.outputHints[pre.length]?.getD false <;>
    simp [Policy.evaluateSpend, Policy.evaluate, Policy.Check.order, Policy.failure]

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

end BtcPolicy.Exhibits.Evaluate
