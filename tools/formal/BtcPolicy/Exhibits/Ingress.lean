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
