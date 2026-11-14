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

namespace BtcPolicy.Exhibits.Ladder
open BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Ladder (Part Read RCfg)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 escPsbt)
open BtcPolicy.Exhibits.EndToEnd (honest)
open BtcPolicy.Exhibits.PreRelease (book scfg pcfg vault withCoin arm run)

/-! ### `DUR-26`'s selection, `DUR-27`'s cumulative release and `DUR-28`'s finalization over the ladder

Research task `bps-9oab.6`. The request `Exhibits.Ingress.req0` with two rungs above its Escape, `reqL`,
which `Ingress.check` accepts with the same candidates (`Exhibits.Ladder.ladder_from_ingress`); its rung
transactions are `Ingress.tx` of the rung members, `r1` and `r2`. The composed states are those of
`Exhibits.PreRelease`: nodes 1 and 2 accept under duress and arm, and each node reads an instant; a pass's
read is that node's authorized set, registry and observation there (`Exhibits.Ladder.rdAt`). The book is a
model parameter in sats, in the checked PSBTs' proportions: over the 510 000 coin the base pays a fee of
10 200, `r1` 30 600 and `r2` 51 000, each delivering the rest to the escape descriptor, so every rung is
within `verify_escape`'s 10 percent. Every rung's maximum finalized vsize at 2 of 3 is 221, so the base
meets a `required` of at most 46, `r1` of at most 138 and `r2` of at most 230. The coverage is `MAN-9`'s
floor of 51, the feerate floor 1 and the cursor's anchor `Cursor.current` unless a case says otherwise. -/




/-- **The ladder comes from checked ingress.** `Ingress.check` accepts `reqL` with the candidates it gives
`req0`, the ladder's base is the Escape's transaction, the rungs share its inputs, and the rung count is
within `CHN-16`'s three. `req0` itself carries no rung: the ladder is optional. -/
@[req "SPN-27"]
theorem ladder_from_ingress :
    Ingress.check ctx0 true reqL = .accepted sp0 es0 ∧ reqL.rungs.map (Ingress.tx ctx0) = [r1, r2] ∧
      r1.inputs = es0.tx.inputs ∧ r2.inputs = es0.tx.inputs ∧
      reqL.rungs.length ≤ Classification.maxRungs ∧ req0.rungs = [] := by
  decide +kernel

/-- Node `i`'s read at the end of a composed schedule, with median `m` and rungs `rs` above the base. -/
def rdAt (p : Sweep.Trace × Sweep.State) (i : Nat) (m : Option Nat) (rs : List Tx) : Read :=
  { A := authorizedAt p.2 p.1 i, reg := (p.2.fed.worlds i).node, ob := p.2.obs i, median := m,
    rungs := fun k => if k = es0.id then rs else [] }

/-- Nodes 1, 2 and 3 read the vault. -/
def atVault : Sweep.Trace × Sweep.State :=
  run (pcfg 1) vault (arm ++ [.observe 1 vault, .observe 2 vault, .observe 3 vault])
/-- Node 1 reads a later instant at which a deposit of `x` has confirmed. -/
def atDeposit (x : Nat) : Sweep.Trace × Sweep.State :=
  run (pcfg 1) vault (arm ++ [.chain (withCoin x), .observe 1 (withCoin x)])

def ladder2 : List Tx := [r1, r2]

/-- **An empty optional ladder.** With no rung above the base, the ladder's verdict is `PreRelease.verdict` on every
median reading, rung 0; from a fresh latch and floor the pass releases it and leaves the floor at 1, after
which nothing is released again. -/
@[req "DUR-26"]
theorem empty_ladder :
    Ladder.verdict (lpre 1) (rdAt atVault 1 none []) es0 0 = .release 0 ∧
      Ladder.verdict (lpre 1) (rdAt atVault 1 (some 200) []) es0 0 =
        PreRelease.verdict (lpre 1) (authorizedAt atVault.2 atVault.1 1) (atVault.2.fed.worlds 1).node
          (atVault.2.obs 1) es0 ∧
      Ladder.release (lcfg 1 600) (rdAt atVault 1 (some 200) []) es0 {} = ({ latch := 0, floor := 1 }, [0]) ∧
      Ladder.release (lcfg 1 600) (rdAt atVault 1 (some 200) []) es0 { latch := 0, floor := 1 } =
        ({ latch := 0, floor := 1 }, []) := by
  decide +kernel

/-- **A valid nonempty ladder.** Over the base and two rungs, a median of 100 targets 100, which only `r1`
and above meet, and `r1` is selected; a median of 200 selects `r2`. With the budget wide enough, a fresh
pass at `r2` releases the cumulative prefix from the lowest admissible rung, the base, through the latch. -/
@[req "DUR-26"]
theorem valid_ladder :
    Ladder.verdict (lpre 1) (rdAt atVault 1 (some 100) ladder2) es0 0 = .release 1 ∧
      Ladder.verdict (lpre 1) (rdAt atVault 1 (some 200) ladder2) es0 0 = .release 2 ∧
      Ladder.release (lcfg 1 600) (rdAt atVault 1 (some 200) ladder2) es0 {} =
        ({ latch := 2, floor := 3 }, [0, 1, 2]) := by
  decide +kernel

/-- **A pressure-reading error.** No reading, an error, sets `target = 0`: the attempt is the one at a
median whose bump target is 0, `required` is the sealed floor, and the base is selected — here because it
is admissible, not because no reading means the base: from a latch at 1 the same read selects rung 1. -/
@[req "DUR-30"]
theorem pressure_error :
    Ladder.verdict (lpre 1) (rdAt atVault 1 none ladder2) es0 0 = .release 0 ∧
      Ladder.verdict (lpre 1) (rdAt atVault 1 (some 4) ladder2) es0 0 = .release 0 ∧
      Ladder.required 1 none = 1 ∧
      Ladder.verdict (lpre 1) (rdAt atVault 1 none ladder2) es0 1 = .release 1 := by
  decide +kernel

/-- **A downward target change.** After a pass at median 200 latched `r2` and released the prefix, the
median falls to nothing: `choice` is the base, `selected = max(choice, current latch)` stays at `r2`, and
the pass queues nothing anew, since the cursor is past the ladder's end: "the loop cannot bump, unbump and
rebump as a median jitters". -/
@[req "DUR-27"]
theorem downward_target :
    Ladder.verdict (lpre 1) (rdAt atVault 1 none ladder2) es0 2 = .release 2 ∧
      Ladder.release (lcfg 1 600) (rdAt atVault 1 none ladder2) es0 { latch := 2, floor := 3 } =
        ({ latch := 2, floor := 3 }, []) := by
  decide +kernel

/-- **A coverage change after a deposit, and an inadmissible latched rung.** At the vault every rung covers;
after a deposit of 400 000 the protected value is 910 000 and `r2`'s 459 000 falls below 51 percent of
it. With the latch at `r2`, the selection fails at the latch, although the base and `r1` are admissible:
nothing is released, and the latch and the floor stay. From a latch at 0 the same read selects `r1`. -/
@[req "DUR-27"]
theorem latched_inadmissible :
    (Ladder.attempt (lpre 1) (rdAt atVault 1 (some 200) ladder2) vault es0 0).adm = [true, true, true] ∧
      (Ladder.attempt (lpre 1) (rdAt (atDeposit 400000) 1 (some 200) ladder2) (withCoin 400000) es0 2).adm =
        [true, true, false] ∧
      (Ladder.attempt (lpre 1) (rdAt (atDeposit 400000) 1 (some 200) ladder2) (withCoin 400000) es0 2).protectedValue =
        910000 ∧
      Ladder.verdict (lpre 1) (rdAt (atDeposit 400000) 1 (some 200) ladder2) es0 2 = .fail .latched ∧
      Ladder.release (lcfg 1 600) (rdAt (atDeposit 400000) 1 (some 200) ladder2) es0 { latch := 2, floor := 1 } =
        ({ latch := 2, floor := 1 }, []) ∧
      Ladder.verdict (lpre 1) (rdAt (atDeposit 400000) 1 (some 200) ladder2) es0 0 = .release 1 := by
  decide +kernel

/-- **The sweep tops out.** At that deposit a median of 200 asks for `r2`, which is not admissible, so
`choice` is the most expensive admissible rung, `r1`, whose fee of 30 600 is below `required × vsize` =
44 200. The selection promises no fee the chain asks for and no confirmation. -/
@[req "DUR-24"]
theorem tops_out :
    Ladder.verdict (lpre 1) (rdAt (atDeposit 400000) 1 (some 200) ladder2) es0 0 = .release 1 ∧
      Ladder.feeOf lbook r1 = 30600 ∧ 30600 < Ladder.required 1 (some 200) * 221 := by
  decide +kernel

/-- **A ladder whose useful result is refusal.** After a deposit of 1 000 000 no rung covers 51 percent of
1 510 000: the verdict fails at coverage, nothing is released and nothing moves, so no partial that `t − 1`
compromised hands could finalize over an under-covering rung leaves. -/
@[req "DUR-27"]
theorem refusal_ladder :
    Ladder.verdict (lpre 1) (rdAt (atDeposit 1000000) 1 (some 200) ladder2) es0 0 = .fail .coverage ∧
      Ladder.release (lcfg 1 600) (rdAt (atDeposit 1000000) 1 (some 200) ladder2) es0 {} = ({}, []) := by
  decide +kernel

/-- **Repeated passes make progress.** At a quota of 3 one rung is affordable per pass: from a fresh cursor
with the latch at `r2`, three passes release the base, `r1` and `r2` in turn, each queued once, and a
fourth releases nothing. -/
@[req "SPN-38"]
theorem passes_progress :
    let rd := rdAt atVault 1 (some 200) ladder2
    Ladder.release (lcfg 1 3) rd es0 {} = ({ latch := 2, floor := 1 }, [0]) ∧
      Ladder.release (lcfg 1 3) rd es0 { latch := 2, floor := 1 } = ({ latch := 2, floor := 2 }, [1]) ∧
      Ladder.release (lcfg 1 3) rd es0 { latch := 2, floor := 2 } = ({ latch := 2, floor := 3 }, [2]) ∧
      Ladder.release (lcfg 1 3) rd es0 { latch := 2, floor := 3 } = ({ latch := 2, floor := 3 }, []) := by
  decide +kernel

/-- **A refused rung inside the prefix.** Over the base, `r1low` and `r2`, a median of 200 selects `r2` and
the cursor's interval is `[0, 2]`; `r1low` fails coverage, and it is released to nobody: the pass releases
the base and `r2` only. -/
@[req "DUR-27"]
theorem refused_inside_prefix :
    (Ladder.attempt (lpre 1) (rdAt atVault 1 (some 200) [r1low, r2]) vault es0 0).adm = [true, false, true] ∧
      Ladder.release (lcfg 1 600) (rdAt atVault 1 (some 200) [r1low, r2]) es0 {} =
        ({ latch := 2, floor := 3 }, [0, 2]) := by
  decide +kernel

/-- **`F51` on the ladder.** At a feerate floor of 47 the base's fee falls short at its maximum finalized vsize
and `a = 1`. At a quota of 3 the first pass releases `[1, 1]` under the anchor as it stands; under the
withdrawn cursor anchor it releases nothing and moves nothing (`Exhibits.f51_current_admits` and
`Cursor.f51_refused_on_cursor` are unchanged). -/
@[req "SPN-38"]
theorem f51_on_ladder :
    Ladder.release (lcfg 47 3) (rdAt atVault 1 none ladder2) es0 {} = ({ latch := 1, floor := 2 }, [1]) ∧
      Ladder.release (lcfg 47 3 .onCursor) (rdAt atVault 1 none ladder2) es0 {} = ({}, []) := by
  decide +kernel

/-! #### Runs across nodes -/

def st0 : Ladder.State := { nodes := fun _ => {} }
def rd (i : Nat) (m : Option Nat) : Read := rdAt atVault i m []
/-- Node `s`'s partial on rung `r` at input 0. -/
def rpart (r : Rung) (s : Nat) : Part := { txid := r.tx.id, userSig := r.userSig, input := 0, signer := s }
def bpart (s : Nat) (u : Nat := 0) : Part := { txid := es0.tx.id, userSig := u, input := 0, signer := s }
/-- What node `j` finalizes at the end of a schedule, from its own latch and possession. -/
def fin (c : RCfg) (ss : List Ladder.Step) (j : Nat) : Option Nat :=
  let st := (Ladder.record c [] st0 ss).2
  Ladder.finalize c.keys c.t (c.lad j) (Ladder.held c (st.nodes j) j) (st.nodes j).track.latch
def endOf (c : RCfg) (ss : List Ladder.Step) : Ladder.State := (Ladder.record c [] st0 ss).2

theorem st0_fresh : Ladder.Fresh st0 := ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Node 1 retains both rungs; nodes 2 and 3 retain the base alone. -/
def stripped : RCfg := rc fun i => if i = 1 then [R1, R2] else []
def strippedRun : List Ladder.Step :=
  [.pass 1 (rd 1 (some 200)), .pass 2 (rd 2 (some 200)), .pass 3 (rd 3 (some 200)),
   .deliver 1 (bpart 2), .deliver 2 (rpart R1 1)]

def strippedEnd : Ladder.Trace × Ladder.State := Ladder.record stripped [] st0 strippedRun

/-- **Compatible stripped subsets.** Node 1 latches `r2` and releases the prefix; nodes 2 and 3, holding the
base alone, release the base. Node 1's `r1` partial reaches node 2, which does not retain `r1` and stores
nothing ("the rung is found by txid"). Node 1 holds the base from itself and node 2, and finalizes the base
from its latch at `r2`: `DUR-28`'s downgrade, with every premise of `Ladder.common_base_fallback` holding. -/
@[req "DUR-28"]
theorem stripped_subsets :
    Ladder.legal stripped honest st0 strippedRun = true ∧
      (strippedEnd.2.nodes 1).track.latch = 2 ∧
      (strippedEnd.2.nodes 2).stored = [] ∧
      Ladder.finalize stripped.keys stripped.t (stripped.lad 1) (Ladder.held stripped (strippedEnd.2.nodes 1) 1)
        (strippedEnd.2.nodes 1).track.latch = some 0 ∧
      strippedEnd.2.extracted = [] ∧
      Authority.quorum stripped.keys stripped.t es0.tx (Ladder.held stripped (strippedEnd.2.nodes 1) 1) = true ∧
      ((stripped.lad 1).drop 1).all (fun r =>
        decide ((honest.filter fun s => Ladder.compat (stripped.lad 1) (stripped.lad s) r.tx.id).length <
          stripped.t)) = true := by
  decide +kernel

/-- The same run through `Ladder.common_base_fallback`: its premises hold on it, so they are not vacuous. -/
@[req "DUR-28"]
theorem stripped_fallback :
    Ladder.finalize stripped.keys stripped.t (stripped.lad 1) (Ladder.held stripped (strippedEnd.2.nodes 1) 1)
      (strippedEnd.2.nodes 1).track.latch = some 0 := by
  have hx : Ladder.Execution stripped honest strippedEnd.1 strippedEnd.2 :=
    Ladder.execution_of_legal (.init st0 st0_fresh) stripped_subsets.1
  have hs := stripped_subsets
  generalize strippedEnd = S at hx hs ⊢
  obtain ⟨-, -, -, -, he, hq, hall⟩ := hs
  refine Ladder.common_base_fallback hx (by decide) he hq ?_
  intro m r h1 _ hr
  have hm : r ∈ (stripped.lad 1).drop 1 := by
    have : ((stripped.lad 1).drop 1)[m - 1]? = some r := by
      rw [List.getElem?_drop]; rwa [show 1 + (m - 1) = m by omega]
    exact List.mem_of_getElem? this
  simpa using List.all_eq_true.1 hall r hm

/-- Node 3 also retains `r1`, under the same user-signature hash as node 1. -/
def possession : RCfg := rc fun i => if i = 1 then [R1, R2] else if i = 3 then [R1] else []
def possessionRun : List Ladder.Step :=
  [.pass 1 (rd 1 (some 200)), .pass 2 (rd 2 (some 200)), .pass 3 (rd 3 (some 200)), .deliver 1 (bpart 2)]

/-- **Possession, not the inventory.** Nodes 1 and 3 both release `r1`, so the partial inventory holds two
distinct signers on it; node 1 has not received node 3's, so it finalizes the base. Once node 3's partial
is delivered, it finalizes `r1`, the highest rung at or below its latch with the quorum. -/
@[req "DUR-28"]
theorem possession_not_inventory :
    Ladder.legal possession honest st0 possessionRun = true ∧
      Authority.quorum possession.keys 2 r1 ((endOf possession possessionRun).parts.map Part.sig) = true ∧
      fin possession possessionRun 1 = some 0 ∧
      Ladder.legal possession honest st0 (possessionRun ++ [.deliver 1 (rpart R1 3)]) = true ∧
      fin possession (possessionRun ++ [.deliver 1 (rpart R1 3)]) 1 = some 1 := by
  decide +kernel

/-- Node 2's base carries another user-signature hash. -/
def mismatch : RCfg := rc (fun i => if i = 1 then [R1, R2] else []) (fun i => if i = 2 then 7 else 0)
def mismatchRun : List Ladder.Step :=
  [.pass 1 (rd 1 (some 200)), .pass 2 (rd 2 (some 200)), .deliver 1 (bpart 2 7)]

/-- **Incompatible user-signature material.** The two nodes' bases share a txid, but node 2's partial carries
user-signature hash 7 and node 1's base 0: node 1's store refuses it ("the user-signature hash matches"), so
node 1 holds one signer on every rung and finalizes nothing. -/
@[req "NCH-24"]
theorem user_sig_mismatch :
    Ladder.legal mismatch honest st0 mismatchRun = true ∧
      ((endOf mismatch mismatchRun).nodes 1).stored = [] ∧
      fin mismatch mismatchRun 1 = none := by
  decide +kernel

/-- All three nodes retain both rungs, at threshold 3. -/
def split : RCfg := rc (fun _ => [R1, R2]) (t := 3)
def splitRun : List Ladder.Step :=
  [.pass 1 (rd 1 (some 200)), .pass 2 (rd 2 (some 200)), .pass 3 (rd 3 (some 200)),
   .deliver 1 (rpart R1 2), .deliver 1 (rpart R2 3)]

/-- **Signatures split across rungs.** Node 1 holds its own partial on every rung, node 2's on `r1` and node
3's on `r2`: three distinct signers in all, two on each of `r1` and `r2`, and node 1 finalizes nothing at
threshold 3. A count pooled across the two rungs would reach three. -/
@[req "DUR-28"]
theorem split_across_rungs :
    Ladder.legal split honest st0 splitRun = true ∧
      ((Ladder.held split ((endOf split splitRun).nodes 1) 1).map (·.signer)).eraseDups.length = 3 ∧
      Authority.quorum split.keys 3 r1 (Ladder.held split ((endOf split splitRun).nodes 1) 1) = false ∧
      Authority.quorum split.keys 3 r2 (Ladder.held split ((endOf split splitRun).nodes 1) 1) = false ∧
      fin split splitRun 1 = none := by
  decide +kernel

/-- A two-input Escape at a registry with nothing selected, over a vault of two confirmed coins. -/
def escM : Cand := RegistrationCases.cand 50 ⟨60, [8, 9], 0⟩ false none 200
def mbook : Book :=
  { value := fun o => if o == 8 then 510000 else if o == 9 then 490000 else if o == 1060 then 990000 else 0,
    outputs := fun tx => [tx + 1000],
    delivered := fun tx => if tx == 60 then 990000 else 0 }
def vM : Backend :=
  { tip := ⟨5, 105⟩, sequence := 1, confirmed := [(8, 510000), (9, 490000)], mempool := [], pending := [] }
def mcfg : RCfg :=
  { lc := { pre := { sweep := { scfg with book := mbook }, legacyLen := fun _ => 100, floor := 1 },
            quota := 600, anchor := Cursor.current },
    esc := escM, keys := [1, 2, 3], t := 2, baseSig := fun _ => 0, above := fun _ => [] }
def rdM : Read := { A := [], reg := RegistrationCases.A, ob := some vM, median := none }
def mpart (s k : Nat) : Part := { txid := 60, userSig := 0, input := k, signer := s }
def multiRun : List Ladder.Step := [.pass 1 rdM, .pass 2 rdM, .deliver 1 (mpart 2 0)]

/-- **Partial delivery across inputs.** Each node releases one partial per input. Node 1 receives node 2's
partial on input 0 only: two signers there, one on input 1, and nothing finalizes. With input 1's
delivered too, the base finalizes. -/
@[req "DUR-28"]
theorem partial_inputs :
    Ladder.legal mcfg honest st0 multiRun = true ∧
      (endOf mcfg multiRun).parts = [mpart 1 0, mpart 1 1, mpart 2 0, mpart 2 1] ∧
      fin mcfg multiRun 1 = none ∧
      fin mcfg (multiRun ++ [.deliver 1 (mpart 2 1)]) 1 = some 0 := by
  decide +kernel

/-- **Extraction, then forgery.** After nodes 1 and 2 release, node 2's key is extracted and a partial on
`r1` is forged under it and delivered to node 1, which holds the quorum on `r1` though node 2 retains no
rung above the base: the inventory row has the extracted-key origin and no honest emission
(`Ladder.inventory_provenance`). -/
@[req "DUR-27"]
theorem extracted_then_forged :
    let ss := strippedRun ++ [.extract 2, .forge (rpart R1 2), .deliver 1 (rpart R1 2)]
    Ladder.legal stripped honest st0 ss = true ∧ fin stripped ss 1 = some 1 ∧
      (endOf stripped ss).extracted = [2] ∧ (stripped.lad 2).length = 1 := by
  decide +kernel

end BtcPolicy.Exhibits.Ladder

namespace BtcPolicy.Exhibits.Assembly
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (coin honest part assemble send fire ordinarySteps ordinaryAll coercedSteps coerced
  toRelease v envHeld sp1 es1 runOf)
open BtcPolicy.Exhibits.Clawback (cl0 clIn envCl)
open BtcPolicy.Exhibits.CommonRun (integ isLegal refined inst pc scfg)
open BtcPolicy.Recovery (sweepTrace)

/-! ### Assembly and submission for each class

Research task `bps-9oab.7`. The composed model of `Exhibits.CommonRun`: three honest nodes under `Kernel.current`,
threshold 2, keys 1 to 3, the checked request `Exhibits.Ingress.req0` and the checked claw-back
`Exhibits.Clawback.cl0`, the book in sats, the pre-release check at a floor of 1 over 100-byte legacy lengths, and
each fire pass carrying the verdict `PreRelease.fill` computes. Each input's finalized witness weighs 476 units,
below the 480 of `W_N` at 2 of 3. The backend's package verdict (`core`) answers `txn-already-in-mempool` for a
resident transaction, another rejection for a txid it is told to reject, and allowed otherwise: a hand-chosen
stand-in for the backend, which the node only interprets. Every assembly below is decided by `Assembly.checks`
on the run, never assumed. -/



def acfg : BtcPolicy.Assembly.Cfg := acfgR []

/-- Every assembly of the composed run passes its class's check at its own state and history. -/
def asm (b : Backend) (xs : List Recovery.Step) : Bool :=
  BtcPolicy.Assembly.checks acfg (sweepTrace (runOf (inst b) xs).1)

/-- A legal, refined, assembly-checked schedule is an `Assembly.Execution` underneath. -/
theorem assembly_of (b : Backend) (xs : List Recovery.Step) (hl : isLegal b xs = true) (hc : refined b xs = true)
    (ha : asm b xs = true) :
    BtcPolicy.Assembly.Execution acfg Kernel.current honest (sweepTrace (runOf (inst b) xs).1)
      (runOf (inst b) xs).2.sw :=
  BtcPolicy.Assembly.execution_iff.2 ⟨CommonRun.prerelease_of b xs hl hc, BtcPolicy.Assembly.checked_of_checks _ ha⟩

/-- Node `i`'s resident under `c`'s id after the first `k` steps, or `c`. -/
def res (b : Backend) (xs : List Recovery.Step) (k i : Nat) (c : Cand) : Cand :=
  ((((runOf (inst b) (xs.take k)).2.sw.fed.worlds i).node.cands.find? (·.id == c.id))).getD c

/-- Node `i`'s check on `c`'s resident after the first `k` steps, at instant `ob` in place of its observation. -/
def checkAt (cf : BtcPolicy.Assembly.Cfg) (b : Backend) (xs : List Recovery.Step) (k i : Nat) (ob : Backend)
    (c : Cand) : Bool :=
  let p := runOf (inst b) (xs.take k)
  BtcPolicy.Assembly.checkAt cf (Sweep.authorizedAt p.2.sw (sweepTrace p.1) i)
    (BtcPolicy.Assembly.clawTxsAt p.2.sw (sweepTrace p.1) i) (p.2.sw.fed.worlds i).node
    (Federation.held i (Sweep.fedTrace (sweepTrace p.1)) p.2.sw.fed) ob (res b xs k i c)

/-- Node `i`'s ancestry verdict on `c`'s resident after the first `k` steps, at instant `ob`. -/
def ancAt (b : Backend) (xs : List Recovery.Step) (k i : Nat) (ob : Backend) (c : Cand) : Package.Verdict :=
  let p := runOf (inst b) (xs.take k)
  BtcPolicy.Assembly.ancestry scfg (Sweep.authorizedAt p.2.sw (sweepTrace p.1) i)
    (BtcPolicy.Assembly.clawTxsAt p.2.sw (sweepTrace p.1) i) ob (res b xs k i c)


/-! #### Successful assemblies, one per class -/

/-- **A Hot spend.** The ordinary history: node 1 holds `t` signers on every input, its read shows the coin
confirmed, the backend allows the package, and the assembly passes the spend's check, which reads no coverage and
no fee floor; the send, re-authorized at its own state, submits the spend. The coin gone from the read refuses the
same assembly as a missing prevout. -/
@[req "SPN-39"]
theorem hot_assembled :
    let xs := integ v ordinaryAll
    let p := runOf (inst v) (xs.take 13)
    isLegal v xs = true ∧ refined v xs = true ∧ asm v xs = true ∧
      BtcPolicy.Assembly.classOf (res v xs 12 1 sp0) = .spend ∧
      checkAt acfg v xs 12 1 (inst v) sp0 = true ∧
      Sweep.submits Kernel.current p.2.sw (send 1 sp0.id envHeld) = [sp0.tx.id] ∧
      checkAt acfg v xs 12 1 (inst vGone) sp0 = false ∧
      ancAt v xs 12 1 (inst vGone) sp0 = .refused (.unknownOrSpent coin) := by
  decide +kernel

/-- **A selected paired Escape.** The coerced history: node 1's assembly re-reads coverage at its own pass and the
floor at the exact finalized vsize, 220, below the 221 the release checked; the witnesses fit the candidate. The
coin gone from the read refuses it. Stopped before the chain move, the Escape is submitted and not included. -/
@[req "DUR-28"]
theorem escape_assembled :
    let xs := integ v coerced
    isLegal v xs = true ∧ refined v xs = true ∧ asm v xs = true ∧
      BtcPolicy.Assembly.classOf (res v xs 12 1 es0) = .escape ∧
      checkAt acfg v xs 12 1 (inst v) es0 = true ∧
      BtcPolicy.Assembly.exactVsize acfg es0.tx = 220 ∧ PreRelease.maxVsize pc 2 es0.tx = 221 ∧
      checkAt acfg v xs 12 1 (inst vGone) es0 = false ∧
      ancAt v xs 12 1 (inst vGone) es0 = .refused (.unknownOrSpent coin) ∧
      isLegal v (integ v coercedSteps) = true ∧ asm v (integ v coercedSteps) = true ∧
      Settlement.confirmedAt (runOf (inst v) (integ v coercedSteps)).2.sw.truth es0.tx = false := by
  decide +kernel

theorem escape_fits : BtcPolicy.Assembly.Fits acfg 2 es0.tx := by
  unfold BtcPolicy.Assembly.Fits; decide +kernel


/-- **A singleton claw-back.** Its resident is in the claw-back class, not the Escape role; the assembly passes
the claw-back's check and its send submits it. The coin gone refuses it, and so does a backend that rejects the
package for another reason. -/
@[req "SPN-51"]
theorem clawback_assembled :
    let xs := integ v clRun
    isLegal v xs = true ∧ refined v xs = true ∧ asm v xs = true ∧
      BtcPolicy.Assembly.classOf (res v xs 8 1 cl0) = .clawback ∧ (res v xs 8 1 cl0).isEscape = false ∧
      checkAt acfg v xs 8 1 (inst v) cl0 = true ∧
      Sweep.submits Kernel.current (runOf (inst v) (xs.take 9)).2.sw (send 1 cl0.id envCl) = [cl0.tx.id] ∧
      checkAt acfg v xs 8 1 (inst vGone) cl0 = false ∧
      ancAt v xs 8 1 (inst vGone) cl0 = .refused (.unknownOrSpent coin) ∧
      checkAt (acfgR [cl0.tx.id]) v xs 8 1 (inst v) cl0 = false := by
  decide +kernel

/-! #### The old abstraction was broader -/

/-- **A Hot spend assembled over a missing prevout.** The coin leaves the chain before node 1's assembly, and node
1 reads that. `PreRelease`'s run, whose backend check sits on the Escape role alone, admits the assembly; the
refined run does not. This is the first class of integration failure: the old execution was broader than
`SPN-39`, and the restriction (`Assembly.to_prerelease`) explains the difference. -/
@[req "SPN-39"]
theorem hot_old_broader :
    let xs := integ v (ordinarySteps.take 9 ++ [.chain vGone, .observe 1 vGone])
    let p := runOf (inst v) xs
    isLegal v xs = true ∧ refined v xs = true ∧ asm v xs = true ∧
      PreRelease.admits pc honest p.2.sw (sweepTrace p.1) (assemble 1 sp0.id envHeld) = true ∧
      BtcPolicy.Assembly.admits acfg honest p.2.sw (sweepTrace p.1) (assemble 1 sp0.id envHeld) = false := by
  decide +kernel

/-! #### Between assembly and send -/


/-- **A state change after assembly and before send.** The Hot spend's package test stands from its assembly, but
the holder decision between them freezes it, and the send, re-authorized at its own state, submits nothing: the
earlier assembly is no lasting authority. -/
@[req "DUR-11"]
theorem frozen_after_assembly :
    let xs := integ v frozenRun
    let n := ((runOf (inst v) xs).2.sw.fed.worlds 1).node
    isLegal v xs = true ∧ refined v xs = true ∧ asm v xs = true ∧ n.armed = true ∧
      n.cands.any (fun c => c.id == sp0.id && c.packageOk && c.frozen) = true ∧
      Sweep.submits Kernel.current (runOf (inst v) xs).2.sw (send 1 sp0.id envHeld) = [] := by
  decide +kernel


/-- **The backend moves after assembly.** After the ordinary assembly an outsider's transaction becomes resident
over the coin and node 1 reads it. The send reads what `DUR-29` assigns to it and not the backend, so it still
submits the spend; an assembly at that read would have been refused. -/
@[req "DUR-29"]
theorem backend_moves_after_assembly :
    let xs := integ v (ordinarySteps ++ [.chain vConflict, .observe 1 vConflict])
    let p := runOf (inst v) xs
    isLegal v xs = true ∧ refined v xs = true ∧ asm v xs = true ∧
      BtcPolicy.Assembly.admits acfg honest p.2.sw (sweepTrace p.1) (send 1 sp0.id envHeld) = true ∧
      Sweep.submits Kernel.current p.2.sw (send 1 sp0.id envHeld) = [sp0.tx.id] ∧
      checkAt acfg v xs 15 1 (inst vConflict) sp0 = false := by
  decide +kernel

/-! #### Parents, the ancestor bound and the diamond (`WTC-24`) -/

/-- A Hot spend over the coin, here an output of the resident transaction 7. -/
def spOver (ins : List Coverage.Outpoint) : Cand := { sp0 with tx := { id := 650, inputs := ins, outflow := 0 } }

/-- The coin unconfirmed: transaction 7 resident and creating it. -/
def vParent : Backend :=
  { inst v with sequence := 2, confirmed := [], mempool := [(7, [42])], pending := [(7, (coin, 510000))] }

/-- Transaction 7 resident over an output of transaction 8, also resident. -/
def vGrand : Backend := { vParent with mempool := [(7, [42]), (8, [43])] }
def grandCfg : Sweep.Cfg := { scfg with creator := fun o => if o == coin then 7 else if o == 42 then 8 else 0 }

/-- **Confirmed, resident authorized and external unconfirmed parents.** The success runs above spend a confirmed
parent. Over the coin unconfirmed, an authorized parent is admitted as the one ancestor; the same parent outside
the authorized set is refused: `WTC-10`'s snapshot leaves the output of an external resident out, so the prevout
is unknown. An authorized parent whose own parent is external is refused at that ancestor. A resident is not
confirmed: the walk counts it. -/
@[req "WTC-24"]
theorem parents_distinguished :
    BtcPolicy.Assembly.ancestry scfg [7] [] vParent (spOver [coin]) = .admitted [7] ∧
      BtcPolicy.Assembly.ancestry scfg [] [] vParent (spOver [coin]) = .refused (.unknownOrSpent coin) ∧
      BtcPolicy.Assembly.ancestry grandCfg [7] [] vGrand (spOver [coin]) = .refused (.notAuthorized 8) := by
  decide +kernel

/-- A chain of residents: transaction `0` over the confirmed outpoint 1000 and each `k ≤ n` over `k − 1`'s
output, all authorized; outpoint `o` is created by transaction `o`. -/
def chainCfg : Sweep.Cfg := { scfg with creator := fun o => o }
def chain (n : Nat) : Backend :=
  let m : Package.MempoolRead := (0, [1000]) :: (List.range n).map (fun k => (k + 1, [k]))
  { (inst v) with sequence := 2, confirmed := [], mempool := m, pending := [(n, (n, 1))] }

/-- **The ancestor bound.** A spend over the output of a chain of 24 distinct residents is admitted with 24
ancestors; one more is refused. -/
@[req "WTC-24"]
theorem ancestor_bound :
    BtcPolicy.Assembly.ancestry chainCfg (List.range 24) [] (chain 23) (spOver [23]) =
        .admitted (Package.ancestors (fun o => o) (chain 23).mempool [23]) ∧
      (Package.ancestors (fun o => o) (chain 23).mempool [23]).length = 24 ∧
      BtcPolicy.Assembly.ancestry chainCfg (List.range 25) [] (chain 24) (spOver [24]) =
        .refused (.tooManyAncestors 25) := by
  decide +kernel

def diamondCfg : Sweep.Cfg := { scfg with creator := Package.diamondCreator }
def vDiamond : Backend :=
  let m : Package.MempoolRead := Package.diamondMembership
  { (inst v) with sequence := 2, confirmed := [], mempool := m, pending := [(21, (31, 1)), (22, (32, 1))] }

/-- **A diamond.** Two resident parents over one resident grandparent: three distinct ancestors, not four. -/
@[req "WTC-24"]
theorem diamond_assembled :
    BtcPolicy.Assembly.ancestry diamondCfg Package.diamondAuthorized [] vDiamond (spOver [31, 32]) =
        .admitted (Package.ancestors Package.diamondCreator Package.diamondMembership [31, 32]) ∧
      (Package.ancestors Package.diamondCreator Package.diamondMembership [31, 32]).length = 3 := by
  decide +kernel

/-! #### Replacement (`WTC-25`) -/

/-- A claw-back over the given ordered inputs, in the claw-back class: unpaired and not hot. -/
def clOver (ins : List Coverage.Outpoint) : Cand := { cl0 with tx := { id := 610, inputs := ins, outflow := 0 } }

/-- A resident transaction 600 over the given inputs, beside the coin and outpoint 9, both confirmed. -/
def vResident (ins : List Coverage.Outpoint) : Backend :=
  { inst v with sequence := 2, confirmed := [(coin, 510000), (9, 1000)], mempool := [(600, ins)] }

/-- **A permitted replacement, and two that are not.** Transaction 600 is a claw-back this node registered,
resident over the coin and outpoint 9: a claw-back over exactly those ordered outpoints replaces it and is
admitted, though the mempool-inclusive read shows neither coin; the same coins reordered, or a subset, are refused.
-/
@[req "WTC-25"]
theorem clawback_replacement :
    BtcPolicy.Assembly.classOf (clOver [coin, 9]) = .clawback ∧
      BtcPolicy.Assembly.target [600] (vResident [coin, 9]) (clOver [coin, 9]) = some 600 ∧
      BtcPolicy.Assembly.ancestry scfg [600] [600] (vResident [coin, 9]) (clOver [coin, 9]) = .admitted [] ∧
      BtcPolicy.Assembly.ancestry scfg [600] [600] (vResident [coin, 9]) (clOver [9, coin]) =
        .refused .outpointsDiffer ∧
      BtcPolicy.Assembly.ancestry scfg [600] [600] (vResident [coin, 9]) (clOver [coin]) =
        .refused .outpointsDiffer := by
  decide +kernel

/-- **A resident the node must not replace.** The same resident, never registered here as a claw-back, is no
target, whether or not its txid is in the authorized set, and the claw-back is refused on the coin it spends. A
Hot spend never replaces. -/
@[req "WTC-25"]
theorem unregistered_not_target :
    BtcPolicy.Assembly.target [] (vResident [coin, 9]) (clOver [coin, 9]) = none ∧
      BtcPolicy.Assembly.ancestry scfg [] [] (vResident [coin, 9]) (clOver [coin, 9]) =
        .refused (.unknownOrSpent coin) ∧
      BtcPolicy.Assembly.ancestry scfg [600] [] (vResident [coin, 9]) (clOver [coin, 9]) =
        .refused (.unknownOrSpent coin) ∧
      BtcPolicy.Assembly.target [600] (vResident [coin, 9]) (spOver [coin, 9]) = none := by
  decide +kernel

/-- A rung above the base over the base's own input, and one over another set of coins. -/
def rung1 : Tx := { id := 700, inputs := es0.tx.inputs, outflow := 0 }
def rungOther : Tx := { id := 701, inputs := [coin, 9], outflow := 0 }
def vBaseResident : Backend :=
  { inst v with sequence := 2, confirmed := [(coin, 510000), (9, 1000)], mempool := [(es0.tx.id, es0.tx.inputs)] }
def rd (top : Tx) : Ladder.Read :=
  { A := [es0.tx.id], reg := (EndToEnd.worlds 1).node, ob := some vBaseResident, median := none,
    rungs := fun k => if k == es0.id then [top] else [] }

/-- **A higher rung's ancestry over the resident base.** With the base resident, rung 1 replaces it, and its
ancestry is admitted over the same ordered outpoint; a rung over other coins is refused. -/
@[req "DUR-29"]
theorem rung_replacement :
    Ladder.replacesOf (Ladder.txs (rd rung1) es0)
        (PreRelease.membership vBaseResident (Ladder.txs (rd rung1) es0)) 1 = some es0.tx.id ∧
      Ladder.ancestryTx scfg [es0.tx.id] vBaseResident rung1 (some es0.tx.id) = true ∧
      Package.validate scfg.ancestry scfg.creator (Sweep.snapshot [es0.tx.id] vBaseResident)
        vBaseResident.mempool [es0.tx.id] (Sweep.candidateOf rungOther) (some es0.tx.id) =
        .refused .outpointsDiffer := by
  decide +kernel

/-- `Exhibits.Ladder`'s fee ladder, its book and a floor of 1, each input's finalized witness at 476 units. -/
def lacfg (rej : List Nat) : BtcPolicy.Assembly.Cfg :=
  { pre := BtcPolicy.Exhibits.Ladder.lpre 1, witnesses := fun _ => [476], test := core rej }

/-- Node 1's ladder read at the vault, with `r1` and `r2` above the base, observing `b`. -/
def rdL (b : Backend) : Ladder.Read :=
  { BtcPolicy.Exhibits.Ladder.rdAt BtcPolicy.Exhibits.Ladder.atVault 1 (some 200) BtcPolicy.Exhibits.Ladder.ladder2
    with ob := some b }

/-- Node 1's possession at the end of a ladder run of `Exhibits.Ladder.possession`. -/
def lheld (xs : List Ladder.Step) : List Authority.Sig :=
  Ladder.held BtcPolicy.Exhibits.Ladder.possession
    ((BtcPolicy.Exhibits.Ladder.endOf BtcPolicy.Exhibits.Ladder.possession xs).nodes 1) 1

/-- The vault with the base Escape resident. -/
def vBase : Backend :=
  { BtcPolicy.Exhibits.PreRelease.vault with sequence := 2, mempool := [(es0.tx.id, es0.tx.inputs)] }

/-- **A higher rung's assembly.** On `Exhibits.Ladder`'s ladder, once node 3's `r1` partial reaches node 1
(`Exhibits.Ladder.possession_not_inventory`), rung 1's assembly passes its quorum, its coverage, the floor at its
exact finalized vsize of 220, its ancestry and the backend's verdict, both as a fresh rung at the vault and as the
replacement of the resident base. Before that partial node 1 holds one signer on `r1`, and the same assembly is
refused; so it is when the backend rejects `r1`, and so is rung 2, on which node 1 holds no quorum. The possession
is the ladder run's own. -/
@[req "DUR-29"]
theorem rung_assembled :
    let after := BtcPolicy.Exhibits.Ladder.possessionRun ++
      [.deliver 1 (BtcPolicy.Exhibits.Ladder.rpart BtcPolicy.Exhibits.Ladder.R1 3)]
    let vault := BtcPolicy.Exhibits.PreRelease.vault
    let r1 := BtcPolicy.Exhibits.Ladder.r1
    BtcPolicy.Assembly.rungCheck (lacfg []) (rdL vault) vault es0 (lheld after) 1 = true ∧
      BtcPolicy.Assembly.rungCheck (lacfg []) (rdL vBase) vBase es0 (lheld after) 1 = true ∧
      Ladder.replacesOf (Ladder.txs (rdL vBase) es0)
        (PreRelease.membership vBase (Ladder.txs (rdL vBase) es0)) 1 = some es0.tx.id ∧
      BtcPolicy.Assembly.exactVsize (lacfg []) r1 = 220 ∧
      BtcPolicy.Assembly.rungCheck (lacfg []) (rdL vault) vault es0
        (lheld BtcPolicy.Exhibits.Ladder.possessionRun) 1 = false ∧
      BtcPolicy.Assembly.rungCheck (lacfg [r1.id]) (rdL vault) vault es0 (lheld after) 1 = false ∧
      BtcPolicy.Assembly.rungCheck (lacfg []) (rdL vault) vault es0 (lheld after) 2 = false ∧
      Authority.quorum (lacfg []).pre.sweep.keys 2 BtcPolicy.Exhibits.Ladder.r2 (lheld after) = false := by
  decide +kernel

/-! #### The package verdict (`WTC-26`) and the exact size (`DUR-25`) -/

/-- **Every entry allowed, the one tolerated reason, and another.** -/
@[req "WTC-26"]
theorem package_entries :
    BtcPolicy.Assembly.accepts [5] [.allowed] = true ∧
      BtcPolicy.Assembly.accepts [5] [.alreadyInMempool] = true ∧
      BtcPolicy.Assembly.accepts [5] [.rejected 26] = false ∧
      BtcPolicy.Assembly.accepts [5] [] = false ∧
      BtcPolicy.Assembly.packageOk acfg vBaseResident es0.tx = true ∧
      BtcPolicy.Assembly.packageOk (acfgR [es0.tx.id]) (inst v) es0.tx = false := by
  decide +kernel

/-- A finalized witness that bears no relation to the candidate, at a floor of 40. -/
def acfgW : BtcPolicy.Assembly.Cfg := { acfg with pre := { pc with floor := 40 }, witnesses := fun _ => [5000] }

/-- **An unrelated size.** At a floor of 40 the Escape's fee meets the floor at its maximum finalized vsize, but a
supplied witness of 5 000 units, over `W_N`, gives an exact size of 1 351 at which it does not: without `Fits` the
exact recheck is not related to the check before release. -/
@[req "DUR-25"]
theorem unrelated_size :
    PreRelease.feeOk acfgW.pre (PreRelease.maxVsize acfgW.pre 2 es0.tx) es0.tx = true ∧
      BtcPolicy.Assembly.exactVsize acfgW es0.tx = 1351 ∧
      PreRelease.feeOk acfgW.pre (BtcPolicy.Assembly.exactVsize acfgW es0.tx) es0.tx = false ∧
      ¬ BtcPolicy.Assembly.Fits acfgW 2 es0.tx := by
  unfold BtcPolicy.Assembly.Fits
  decide +kernel

end BtcPolicy.Exhibits.Assembly

namespace BtcPolicy.Exhibits.Integrated
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Ladder (Read RCfg)
open BtcPolicy.Kernel.RegistrationCases (envFire)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.Clawback (cl0)
open BtcPolicy.Exhibits.EndToEnd (coin honest part fire assemble toRelease v vLarge ordinaryAll coerced
  coercedSteps runOf)
open BtcPolicy.Exhibits.CommonRun (integ isLegal refined inst pc scfg icfg verdictAt rows unusable priorFailed)
open BtcPolicy.Exhibits.Assembly (asm acfg)
open BtcPolicy.Recovery (sweepTrace)

/-! ### The integration on common executions

Research task `bps-9oab.8`, its second part, which leaves the rung releases open (`docs/research/proof-boundaries.md`,
section 18). The composed model of `Exhibits.CommonRun` with the class checks of `Exhibits.Assembly`: every history
below except the claw-back walk is a `Recovery.Execution` that takes no ladder pass, whose fire passes carry
`DUR-21`'s verdict and whose assemblies pass their class's check, each decided at its own state and history, so `Assembly.of_composed` makes it
an `Assembly.Execution` underneath. The claw-back walk is the kernel's two-family walk, checked at its own assembly
step with the vault and possession supplied alike to both families. Two histories are new: the ladder's passes read
at the fire passes of one composed run whose observations change, their releases, deliveries and latches on
`Ladder`'s own run and not on the composed run; and the composer's immature coinbase read at the instants of
another. -/

/-- A legal schedule of the composed run, refined and assembly-checked, is an `Assembly.Execution` underneath. -/
theorem assembled_of (b : Backend) (xs : List Recovery.Step) (hl : isLegal b xs = true)
    (hc : refined b xs = true) (ha : asm b xs = true) :
    BtcPolicy.Assembly.Execution acfg Kernel.current honest (sweepTrace (runOf (inst b) xs).1)
      (runOf (inst b) xs).2.sw :=
  BtcPolicy.Assembly.of_composed (rc := icfg) rfl (CommonRun.execution_of b xs hl)
    (PreRelease.checked_of_checks pc hc) (BtcPolicy.Assembly.checked_of_checks acfg ha)

/-- **Section 14's histories, with the class checks.** The ordinary, coerced, submitted-not-included,
unusable-Escape, earlier-exposure and claw-back histories pass every assembly check they reach, so each is an
`Assembly.Execution` (`assembled_of`). At the vault holding the large coin no assembly of the Escape is
admitted, by the class check as by the old one. -/
@[req "SPN-39"]
theorem common_assembled :
    (asm v (integ v ordinaryAll) && asm v (integ v coerced) && asm v (integ v coercedSteps) &&
      asm vLarge unusable && asm v priorFailed &&
      asm v (integ v BtcPolicy.Exhibits.Assembly.clRun)) = true ∧
    BtcPolicy.Assembly.admits acfg honest (runOf (inst vLarge) unusable).2.sw
      (sweepTrace (runOf (inst vLarge) unusable).1) (assemble 1 es0.id envFire) = false := by
  decide +kernel

/-- **The claw-back walk and the class check.** At the claw-back walk's step where node 1 is armed in the duress
family and not in the normal one, the two nodes share one `Silence.pubNode`, so by `Assembly.guard_pub` they
admit the same assembly of every commitment, at every authorized set, claw-back list, possession and instant. The
walk carries no backend and no possession: those are the premise, the same in both families. -/
@[req "DUR-1"]
theorem clawback_walk_guard :
    let nD := ((ClawSilence.runK LedgerSilence.tblsD 9).fed.worlds 1).node
    let nN := ((ClawSilence.runK LedgerSilence.tblsN 9).fed.worlds 1).node
    nD.armed = true ∧ nN.armed = false ∧
      ∀ A C R b cid, (nD.cands.all fun c => !(c.id == cid) || BtcPolicy.Assembly.checkAt acfg A C nD R b c) =
        (nN.cands.all fun c => !(c.id == cid) || BtcPolicy.Assembly.checkAt acfg A C nN R b c) := by
  have hp : Silence.pubNode Kernel.current ((ClawSilence.runK LedgerSilence.tblsD 9).fed.worlds 1).node =
      Silence.pubNode Kernel.current ((ClawSilence.runK LedgerSilence.tblsN 9).fed.worlds 1).node := by
    decide +kernel
  exact ⟨by decide +kernel, by decide +kernel,
    fun A C R b cid => BtcPolicy.Assembly.guard_pub acfg A C R b hp cid⟩

/-- The possession `Federation.held` gives node 1 at the walk's assembly step: its own signatures and node 2's
claw-back partial, delivered at the step before. -/
def walkHeld (n : Node) : List Authority.Sig :=
  Federation.ownSigs n ++ [{ msg := sighash cl0.tx 0, input := 0, signer := 2 }]

/-- **Both families admit the walk's claw-back assembly.** At step 12 of the claw-back walk, node 1's package check,
the duress family's node 1 is armed and the normal family's is not; at the vault, with node 1's own registrations as
the claw-back list, its authorized set and the possession its two partials give, the claw-back's class check passes
at both, so neither family's assembly is refused where the other's is admitted. -/
@[req "DUR-1"]
theorem clawback_walk_assembles :
    let nD := ((ClawSilence.runK LedgerSilence.tblsD 12).fed.worlds 1).node
    let nN := ((ClawSilence.runK LedgerSilence.tblsN 12).fed.worlds 1).node
    ClawSilence.clSched[12]? = some (.input 1 ClawSilence.envD (.pinless (.packageAccepted cl0.id))) ∧
      nD.armed = true ∧ nN.armed = false ∧
      (nD.cands.all fun c => !(c.id == cl0.id) || BtcPolicy.Assembly.checkAt acfg (Sweep.authorized [] nD)
        (BtcPolicy.Assembly.clawTxs [] nD) nD (walkHeld nD) (inst v) c) = true ∧
      (nN.cands.all fun c => !(c.id == cl0.id) || BtcPolicy.Assembly.checkAt acfg (Sweep.authorized [] nN)
        (BtcPolicy.Assembly.clawTxs [] nN) nN (walkHeld nN) (inst v) c) = true ∧
      nD.cands.any (·.id == cl0.id) = true := by
  decide +kernel

/-! #### The ladder with changing observations -/


/-- The ids the fire pass at step `k` withholds. -/
def withheldAt (xs : List Recovery.Step) (k : Nat) : List Nat :=
  match xs[k]? with
  | some (.base (.fed (.process _ env .firePass))) => env.withheld
  | _ => []

/-- The read node `i` takes at step `k` of a composed schedule from instant `b`: `Ladder.readOf` there. -/
def readAt (b : Backend) (xs : List Recovery.Step) (k i : Nat) (m : Option Nat) : Read :=
  let p := runOf (inst b) (xs.take k)
  Ladder.readOf p.2.sw (sweepTrace p.1) i m




/-- Every node retains both rungs of `Exhibits.Ladder.ladder_from_ingress`. -/
def irc : RCfg := { Exhibits.Ladder.rc (fun _ => [Exhibits.Ladder.R1, Exhibits.Ladder.R2]) with lc := ilc }

/-- The ladder's run over the Escape: each pass is node `i`'s at a fire pass of `lsched`, reading what that fire
pass reads, with a median of 100 and then 200; node 2's base and `r1` partials reach node 1. -/
def lrun : List Ladder.Step :=
  [.pass 1 (readAt v lsched 7 1 (some 100)), .pass 2 (readAt v lsched 9 2 (some 100)),
   .deliver 1 (Exhibits.Ladder.bpart 2), .deliver 1 (Exhibits.Ladder.rpart Exhibits.Ladder.R1 2),
   .pass 1 (readAt v lsched 11 1 (some 200)), .pass 1 (readAt v lsched 14 1 (some 200))]

def lend (n : Nat) : Ladder.State := (Ladder.record irc [] Exhibits.Ladder.st0 (lrun.take n)).2

/-- **The ladder with changing observations, on one composed run.** `lsched` is a refined, assembly-checked
composed run: its fire passes are at steps 7, 9, 11 and 14, the last reading the large coin. The ladder's run
`lrun` is legal and each of its passes reads what the matching fire pass reads (`Ladder.readOf`), with only the
median and the retained rungs supplied. Node 1 first latches `r1` and releases the prefix from the base; at a
higher median it latches `r2` and releases `r2` alone, the floor past the earlier prefix; at the large coin no
rung covers, nothing is released and the latch and floor stay. Node 1 finalizes `r1`, where node 2's partial
gives it two signers, and not `r2`, which it alone signed: nothing is pooled across rungs. On a ladder of the
base alone, the same reads give what the kernel's fire passes did: the base released at step 7 and withheld at
step 14 (`Ladder.fire_release`). The kernel itself releases only the base: the composed run's inventory holds
its two base partials and no rung. -/
@[req "DUR-27"]
theorem ladder_on_run :
    isLegal v lsched = true ∧ refined v lsched = true ∧ asm v lsched = true ∧
      fireAt lsched 7 1 = true ∧ fireAt lsched 9 2 = true ∧ fireAt lsched 11 1 = true ∧
      fireAt lsched 14 1 = true ∧
      (readAt v lsched 7 1 none).ob = some (inst v) ∧ (readAt v lsched 14 1 none).ob = some (inst vLarge) ∧
      Ladder.legal irc honest Exhibits.Ladder.st0 lrun = true ∧
      ((lend 1).nodes 1).track = { latch := 1, floor := 2 } ∧ (lend 1).parts = Ladder.emits irc 1 [0, 1] ∧
      ((lend 5).nodes 1).track = { latch := 2, floor := 3 } ∧
      (lend 5).parts = (lend 4).parts ++ Ladder.emits irc 1 [2] ∧
      ((lend 6).nodes 1).track = { latch := 2, floor := 3 } ∧ (lend 6).parts = (lend 5).parts ∧
      Ladder.verdict ilc.pre (irc.read 1 (readAt v lsched 14 1 (some 200))) es0 2 = .fail .coverage ∧
      Ladder.finalize irc.keys irc.t (irc.lad 1) (Ladder.held irc ((lend 6).nodes 1) 1) 2 = some 1 ∧
      Authority.quorum irc.keys irc.t Exhibits.Ladder.r2 (Ladder.held irc ((lend 6).nodes 1) 1) = false ∧
      withheldAt lsched 7 = [] ∧ withheldAt lsched 14 = [es0.id] ∧
      Ladder.release ilc (readAt v lsched 7 1 none) es0 {} = ({ latch := 0, floor := 1 }, [0]) ∧
      Ladder.release ilc (readAt v lsched 14 1 none) es0 {} = ({}, []) ∧
      rows v lsched es0 = [part es0 1, part es0 2] := by
  decide +kernel

/-- The ladder's book is the composed run's at every coin the run reads. -/
theorem ibook_agrees : ([coin, 9].all fun o => ibook.value o == CommonRun.book.value o) = true := by
  decide +kernel

/-! #### Immature value, then a later accepted pass -/

/-- The vault holding the large coin, here an immature coinbase confirmed at height 4, at tip 5, the outpoints
in canonical order: the coinbase, transaction 8, at height 4 beside the request coin's creator, transaction 7, at
height 3. -/
def vImm : Backend := { vLarge with confirmed := [(9, 1000), (coin, 100)], heights := [(7, 3), (8, 4)] }
/-- The same coins at tip 103, the coinbase's 100th confirmation. -/
def vMat : Backend := { vImm with tip := ⟨103, 2103⟩, sequence := 2 }

/-- The inventory pass's evidence: coin 9 a coinbase output confirmed at height 4, the request's coin ordinary. -/
def cbPass : Coinbase.Pass :=
  Exhibits.Coinbase.pass [(9, Exhibits.Coinbase.coinbaseAt 4 1000000), (coin, Exhibits.Coinbase.ordinaryAt 3 510000)]

/-- Section 14's guards and book with each outpoint's creator as the evidence has it: coin 9 is the output of
the coinbase transaction 8, every other outpoint of transaction 7. -/
def csw : Sweep.Cfg := { scfg with creator := fun o => if o == 9 then 8 else 7 }
def cpc : PreRelease.Cfg := { pc with sweep := csw }
def crc : Recovery.Cfg := { icfg with sweep := csw }
def cac : BtcPolicy.Assembly.Cfg := { acfg with pre := cpc }

/-- `Exhibits.CommonRun.integ` at these guards. -/
def cinteg (b : Backend) (ss : List Sweep.Step) : List Recovery.Step :=
  (PreRelease.fill cpc Kernel.current [] (EndToEnd.st0 (inst b)).sw
    ((CommonRun.readFirst b ss).map CommonRun.onBook)).map .base
def cLegal (b : Backend) (xs : List Recovery.Step) : Bool :=
  Recovery.legal crc Kernel.current honest [] (EndToEnd.st0 (inst b)) xs
def cRefined (b : Backend) (xs : List Recovery.Step) : Bool :=
  PreRelease.checks cpc (sweepTrace (runOf (inst b) xs).1)
def cAsm (b : Backend) (xs : List Recovery.Step) : Bool :=
  BtcPolicy.Assembly.checks cac (sweepTrace (runOf (inst b) xs).1)
def cVerdict (b : Backend) (xs : List Recovery.Step) (k i : Nat) (x : Cand) : PreRelease.Verdict :=
  let p := runOf (inst b) (xs.take k)
  PreRelease.verdict cpc (Sweep.authorizedAt p.2.sw (sweepTrace p.1) i) (p.2.sw.fed.worlds i).node (p.2.sw.obs i) x

/-- A legal schedule at these guards, refined and assembly-checked, is an `Assembly.Execution` underneath. -/
theorem c_assembled_of (b : Backend) (xs : List Recovery.Step) (hl : cLegal b xs = true)
    (hc : cRefined b xs = true) (ha : cAsm b xs = true) :
    BtcPolicy.Assembly.Execution cac Kernel.current honest (sweepTrace (runOf (inst b) xs).1)
      (runOf (inst b) xs).2.sw :=
  BtcPolicy.Assembly.of_composed (rc := crc) rfl
    (Recovery.execution_of_legal (.init _ (EndToEnd.st0_fresh (inst b))) hl)
    (PreRelease.checked_of_checks cpc hc) (BtcPolicy.Assembly.checked_of_checks cac ha)

/-- Nodes 1 and 2 arm and fire at the immature instant; the chain reaches tip 103 and node 1 fires again. -/
def cbSched : List Recovery.Step := cinteg vImm (toRelease ++ [.chain vMat, fire 1 envFire])

/-- The composer's vault at node `i`'s read after the first `k` steps: the run's guards, book and creators, the
node's authorized set and its observation. -/
def vaultAt (b : Backend) (xs : List Recovery.Step) (k i : Nat) : Feasibility.Vault :=
  let p := runOf (inst b) (xs.take k)
  { cfg := csw, A := Sweep.authorizedAt p.2.sw (sweepTrace p.1) i, b := (p.2.sw.obs i).getD (inst b),
    parentOf := fun _ => some Exhibits.Feasibility.plain, floor := 1 }

/-- **Immature-value refusal, then a later accepted pass, on one composed run.** At node 1's read before its
first fire pass the vault holds the 1 000 000 coinbase with two confirmations: the composer refuses the spend
with `I` = 1 000 000 and the clearing height 103, before any request exists. At that same read the node's
`DUR-21` verdict counts the coinbase and the Escape fails coverage, so the fire pass withholds it. At node 1's
read at tip 103 the composer's pass is accepted and composes a spend of both coins, which covers at the node's
read it was composed at. The Escape already registered still fails coverage there, and no Escape partial is in
the inventory: the accepted pass is a new request, not the progress of the old one. The run's guards give each
outpoint the creator its evidence names (`csw`), and the backend confirms both creators at the evidence's heights. -/
@[req "OPR-38"]
theorem immature_then_accepted :
    let s1 := vaultAt vImm cbSched 7 1
    let s2 := vaultAt vImm cbSched 12 1
    cLegal vImm cbSched = true ∧ cRefined vImm cbSched = true ∧ cAsm vImm cbSched = true ∧
      fireAt cbSched 7 1 = true ∧ fireAt cbSched 12 1 = true ∧
      csw.creator 9 = 8 ∧ csw.creator coin = 7 ∧ (inst vImm).heights = [(7, 3), (8, 4)] ∧
      s1.b = inst vImm ∧ s2.b = inst vMat ∧
      Exhibits.Coinbase.err (Coinbase.composeSpend Exhibits.Feasibility.lim 77 s1 cbPass) =
        some (.immature 1000000 103) ∧
      cVerdict vImm cbSched 7 1 es0 = .fail .coverage ∧ withheldAt cbSched 7 = [es0.id] ∧
      ((Coinbase.composeSpend Exhibits.Feasibility.lim 77 s2 cbPass).toOption.map (·.inputs)) = some [9, coin] ∧
      ((Coinbase.composeSpend Exhibits.Feasibility.lim 77 s2 cbPass).toOption.map s2.coverOk) = some true ∧
      cVerdict vImm cbSched 12 1 es0 = .fail .coverage ∧ rows vImm cbSched es0 = [] := by
  decide +kernel

end BtcPolicy.Exhibits.Integrated

namespace BtcPolicy.Exhibits.LadderPass
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire)
open BtcPolicy.Exhibits.Ingress (es0)
open BtcPolicy.Exhibits.EndToEnd (runOf v)
open BtcPolicy.Exhibits.CommonRun (inst pc)
open BtcPolicy.Exhibits.Integrated (lsched)
open BtcPolicy.Recovery (sweepTrace)

/-! ### The kernel's ladder pass

Research task `bps-9oab.8`, its third part: the rungs above the base released by the kernel itself
(`Kernel.ladderPass`), one kernel step at a time. No ladder pass of a refined execution queues a partial
(`PreRelease.ladder_releases_nothing`), and on a checked federation execution none of an honest node's does,
since checked ingress hands the kernel no rung (`Ingress.resident_no_rungs`). The fixtures are node 1's state
at step 7 of `Exhibits.Integrated.lsched`, where its Escape `es0` is due and its fire pass releases the base,
with the Escape given two rungs above the base: `Exhibits.Ladder.R1` and a rung spending two inputs. Checked
ingress hands the kernel no rungs (`Ingress.resident_no_rungs`), so the rungs are written into the state; which
release a pass lists is `Ladder`'s, and checking it on the composed run is the next part. -/

/-- A rung above `R1` that spends two inputs. -/
def wide : Rung := ⟨{ id := 77, inputs := [5, 6], outflow := 0 }, 13⟩


/-- The world with `es0` holding the rungs `R1` and `wide` above its base. -/
def withRungs (w : World) : World :=
  { w with node := { w.node with cands := w.node.cands.map fun c =>
      if c.id == es0.id then { c with above := [Exhibits.Ladder.R1, wide] } else c } }

/-- The fire pass's environment with one release listed for `es0`: latch 2, floor 3, the rungs `ms`. -/
def envL (ms : List Nat) : Env := { envFire with ladder := [(es0.id, { latch := 2, floor := 3 }, ms)] }

/-- **Rung partials on every input.** A ladder pass listing rungs 0, 1 and 2 for the due Escape, not yet
released, queues the base's partial (`Kernel.baseEffects`) and then one partial per input of each rung above the
base, on that input's own message, not hot, under the Escape's commitment; the federation's fan-out adds no row to
them; and the Escape's release state becomes the one listed. -/
@[req "DUR-27"]
theorem rung_rows :
    (step Kernel.current (envL [0, 1, 2]) (withRungs (wAt 7 1)) .ladderPass).2 =
      [.queuePartial (sighash es0.tx 0) 0 false es0.id,
       .queuePartial (sighash Exhibits.Ladder.R1.tx 0) 0 false es0.id,
       .queuePartial (sighash wide.tx 0) 0 false es0.id, .queuePartial (sighash wide.tx 1) 1 false es0.id] ∧
    Federation.fanout (withRungs (wAt 7 1))
        (step Kernel.current (envL [0, 1, 2]) (withRungs (wAt 7 1)) .ladderPass).2 =
      Federation.outbox (withRungs (wAt 7 1))
        (step Kernel.current (envL [0, 1, 2]) (withRungs (wAt 7 1)) .ladderPass).2 ∧
    (((step Kernel.current (envL [0, 1, 2]) (withRungs (wAt 7 1)) .ladderPass).1.node.cands.filter
        (·.id == es0.id)).map (·.track)) = [{ latch := 2, floor := 3 }] := by
  decide +kernel

/-- **Nothing listed, nothing released.** With the fire pass's environment, which lists no release, the ladder
pass leaves the world as it was and queues nothing (`Kernel.ladderPass_nothing`); and a release listed for an
Escape not yet due, at step 4, queues nothing either. -/
@[req "DUR-27"]
theorem nothing_listed :
    step Kernel.current envFire (withRungs (wAt 7 1)) .ladderPass = (withRungs (wAt 7 1), []) ∧
      ((wAt 4 1).node.cands.any (·.id == es0.id)) = true ∧
      (step Kernel.current (envL [0, 1, 2]) (withRungs (wAt 4 1)) .ladderPass).2 = [] := by
  decide +kernel

/-- **The base-only run.** On the composed run itself, whose Escape came through checked ingress and holds no
rung, a ladder pass listing every rung above the base queues nothing (`Kernel.ladderPass_no_rungs`), and one
listing the base as well queues the base's partial alone (`Kernel.ladderPass_no_rungs_base`); and the base-only
refinement admits a ladder pass only when it lists nothing (`PreRelease.releaseOk`,
`PreRelease.ladder_releases_nothing`). -/
@[req "DUR-21"]
theorem base_only :
    (step Kernel.current (envL [1, 2]) (wAt 7 1) .ladderPass).2 = [] ∧
      (step Kernel.current (envL [0, 1, 2]) (wAt 7 1) .ladderPass).2 =
        [.queuePartial (sighash es0.tx 0) 0 false es0.id] ∧
      PreRelease.releaseOk pc (runOf (inst v) (lsched.take 7)).2.sw
        (sweepTrace (runOf (inst v) (lsched.take 7)).1) (.fed (.process 1 (envL [1]) .ladderPass)) = false ∧
      PreRelease.releaseOk pc (runOf (inst v) (lsched.take 7)).2.sw
        (sweepTrace (runOf (inst v) (lsched.take 7)).1) (.fed (.process 1 envFire .ladderPass)) = true := by
  decide +kernel

/-- **Why a helper widened.** The rung's input-0 partial names no resident candidate's base message: the old
form of `Ingress.queued_cand`, kept as `Ingress.queued_cand_pre`, does not hold at a ladder pass, and the new
form names the rung of a resident candidate instead. -/
theorem rung_not_base :
    Effect.queuePartial (sighash Exhibits.Ladder.R1.tx 0) 0 false es0.id ∈
        (step Kernel.current (envL [1]) (withRungs (wAt 7 1)) .ladderPass).2 ∧
      ((withRungs (wAt 7 1)).node.cands.all fun c => sighash c.tx 0 != sighash Exhibits.Ladder.R1.tx 0) = true ∧
      ((withRungs (wAt 7 1)).node.cands.any fun c => c.above.contains Exhibits.Ladder.R1) = true := by
  decide +kernel

end BtcPolicy.Exhibits.LadderPass

namespace BtcPolicy.Exhibits.LadderShape
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.LadderShape
open BtcPolicy.Ingress (escapeSequence)
open BtcPolicy.Kernel.RegistrationCases (env0)
open BtcPolicy.Federation.Cases (fed0 fed0_fresh honest)
open BtcPolicy.Exhibits.Ingress (ctx0 txidA)

/-! ### `CHN-16`'s relations at checked ingress

Research task `bps-keml.4`. The configuration and identities are `Exhibits.Ingress.ctx0`'s; the template is 2 of 3.
Each input holds 10 000 at the vault script. The Escape `base` pays 9 800 to an Escape script, a fee of 200; the rungs
`g1` and `g2` pay 9 500 and 9 317, fees of 500 and 683. A one-input, one-output rung's maximum finalized vsize at 2 of
3 is 183, so `g2` is exactly at `CHN-16`'s minimum over `g1`, and `g2low`, paying 9 318, is one below it. The spend pays
55 to an allowlist script with the rest less 5 back to the vault. Every candidate below is computed by the checks. -/

def txidB : Encode.Bytes := List.replicate 31 0 ++ [2]





def g2low : Ingress.Member := esc 9318



/-- Both checks accept a request with the same candidates. -/
def both (q : RungIngress.Request) : Bool :=
  check ctx0 2 3 true q == .accepted (spOf q) (esOf q) &&
    RungIngress.check ctx0 true q == .accepted (spOf q) (esOf q)

/-- `RungIngress.check` accepts a request that this check refuses `PSBT_INCONSISTENT`. -/
def narrowed (q : RungIngress.Request) : Bool :=
  check ctx0 2 3 true q == .refused .PSBT_INCONSISTENT &&
    RungIngress.check ctx0 true q == .accepted (spOf q) (esOf q)

/-- **A useful ladder.** Both checks accept the Escape with `g1` and `g2` above it and the same candidates; the
fees are 200, 500 and 683, and `g2`'s increase over `g1` is exactly its maximum finalized vsize, 183. With no rung
both accept as well. -/
@[req "CHN-16"]
theorem shape_valid :
    both (req [g1, g2]) = true ∧ (esOf (req [g1, g2])).above.length = 2 ∧
      [base, g1, g2].map fee = [200, 500, 683] ∧ vsize 2 3 g2 = 183 ∧ fee g1 + vsize 2 3 g2 = fee g2 ∧
      both (req []) = true ∧ check ctx0 2 3 true (req []) = RungIngress.check ctx0 true (req []) := by
  decide +kernel

/-- What the acceptance carries, by `LadderShape.accepted_valid`, `LadderShape.accepted_inputs` and, with the
injective `Ingress.code`, `LadderShape.accepted_ids`. -/
theorem valid_derived :
    Valid 2 3 base [g1, g2] ∧ (∀ g ∈ (esOf (req [g1, g2])).ladder, g.tx.inputs = (esOf (req [g1, g2])).tx.inputs) ∧
      ((esOf (req [g1, g2])).ladder.map (·.tx.id)).Nodup := by
  have h : check ctx0 2 3 true (req [g1, g2]) = .accepted (spOf (req [g1, g2])) (esOf (req [g1, g2])) := by
    decide +kernel
  exact ⟨(accepted_valid h).1, accepted_inputs h, accepted_ids Ingress.code_injective h⟩

/-- **The minimum increment.** `g2low`'s increase over `g1` is 182, one below its maximum finalized vsize:
`RungIngress.check` accepts the ladder, this check refuses it. -/
@[req "CHN-16"]
theorem increment_boundary :
    fee g1 + vsize 2 3 g2low = fee g2low + 1 ∧ narrowed (req [g1, g2low]) = true := by
  decide +kernel

/-- **The same ordered input set.** Over two outpoints, a rung spending them in the other order is refused, and in
the base's order accepted; its increase, 400, is above the two-input vsize of 344 either way. -/
@[req "CHN-16"]
theorem reordered_refused :
    vsize 2 3 (escOf [txidB, txidA] [⟨[10, 0], 19400⟩]) = 344 ∧
      narrowed (reqOf [txidA, txidB] (escOf [txidA, txidB] [⟨[10, 0], 19800⟩])
        [escOf [txidB, txidA] [⟨[10, 0], 19400⟩]]) = true ∧
      both (reqOf [txidA, txidB] (escOf [txidA, txidB] [⟨[10, 0], 19800⟩])
        [escOf [txidA, txidB] [⟨[10, 0], 19400⟩]]) = true := by
  decide +kernel

/-- **The same ordered output script set.** A rung paying another Escape script is refused. -/
@[req "CHN-16"]
theorem script_refused : narrowed (req [escOf [txidA] [⟨[10, 1], 9500⟩]]) = true := by
  decide +kernel

/-- **Each output at or below the rung below's.** Over an Escape paying 9 000 and 800, a rung paying 8 600 and 900
raises its second output and is refused, though its fee rises by 300, above the two-output vsize of 194; the rung
paying 8 600 and 800 is accepted. -/
@[req "CHN-16"]
theorem value_refused :
    vsize 2 3 (escOf [txidA] [⟨[10, 0], 8600⟩, ⟨[10, 1], 900⟩]) = 194 ∧
      narrowed (reqOf [txidA] (escOf [txidA] [⟨[10, 0], 9000⟩, ⟨[10, 1], 800⟩])
        [escOf [txidA] [⟨[10, 0], 8600⟩, ⟨[10, 1], 900⟩]]) = true ∧
      both (reqOf [txidA] (escOf [txidA] [⟨[10, 0], 9000⟩, ⟨[10, 1], 800⟩])
        [escOf [txidA] [⟨[10, 0], 8600⟩, ⟨[10, 1], 800⟩]]) = true := by
  decide +kernel

/-- `g1` reporting 10 001 for its input. -/
def gPrev : Ingress.Member := { g1 with psbt := { g1.psbt with inputMaps := [some ⟨[12, 0], 10001⟩] } }

/-- `g1`'s outputs with its input reported at 10 100: over its own maps its increase is 200, over the Escape's 100. -/
def gOwn : Ingress.Member :=
  { esc 9700 with psbt := { (esc 9700).psbt with inputMaps := [some ⟨[12, 0], 10100⟩] } }

/-- **The Escape's prevouts.** A rung whose input maps are not the Escape's is refused, though `RungIngress.check`
accepts it; a rung whose own maps would meet the minimum increment is refused on the Escape's data, where it does
not. -/
@[req "SPN-27"]
theorem prevout_refused :
    narrowed (req [gPrev]) = true ∧ fee base + vsize 2 3 gOwn ≤ fee gOwn ∧
      feeOver base base + vsize 2 3 gOwn > feeOver base gOwn ∧ narrowed (req [gOwn]) = true := by
  decide +kernel

/-- **`nVersion` and `nLockTime`.** A rung with another version, and one with a non-zero lock time, are refused. -/
@[req "CHN-16"]
theorem fields_refused :
    narrowed (req [{ g1 with version := 1 }]) = true ∧ narrowed (req [{ g1 with lockTime := 5 }]) = true := by
  decide +kernel

/-- `g` with a failed upstream signature verdict. -/
def badSig (g : Ingress.Member) : Ingress.Member := { g with upstream := some .USER_SIG_INVALID }

/-- **The gate order.** A ladder failure comes after the earlier gates: with gate 24 failing it is staged
`HOT_VELOCITY_EXCEEDED`, with the Escape's own signature failing it is that refusal, and with four rungs gate 18
refuses, each as `RungIngress.check` decides. Inside gate 25 the ladder rules precede each rung's own verification:
`g2low` with a failed signature is refused by the ladder rule, where `RungIngress.check` returns the signature's
refusal; on a valid ladder the rung's own verification still runs. A refusal at gate 25 is no kernel event. -/
@[req "SPN-27"]
theorem gate_order :
    check ctx0 2 3 false (req [g1, g2low]) = .staged .HOT_VELOCITY_EXCEEDED
        ((spOf (req [g1, g2low])).id, (Ingress.cand ctx0 (req [g1, g2low]).plain base false none).id) ∧
      check ctx0 2 3 false (req [g1, g2low]) = RungIngress.check ctx0 false (req [g1, g2low]) ∧
      check ctx0 2 3 true (reqOf [txidA] (badSig base) [g1, g2low]) = .refused .USER_SIG_INVALID ∧
      check ctx0 2 3 true (req [g1, g1, g1, g1]) = .refused .PSBT_INCONSISTENT ∧
      RungIngress.check ctx0 true (req [g1, g1, g1, g1]) = .refused .PSBT_INCONSISTENT ∧
      check ctx0 2 3 true (req [g1, badSig g2low]) = .refused .PSBT_INCONSISTENT ∧
      RungIngress.check ctx0 true (req [g1, badSig g2low]) = .refused .USER_SIG_INVALID ∧
      check ctx0 2 3 true (req [g1, badSig g2]) = .refused .USER_SIG_INVALID ∧
      (check ctx0 2 3 true (req [g1, g2low])).event 10 false (Wall.sample 200) = none := by
  decide +kernel

/-- **Dropping rungs.** The ladder with `g1` alone and with `g2` alone is accepted, as `LadderShape.check_sublist`
says of every sublist; the two rungs in the other order are refused. The earlier fixture
`Exhibits.RungIngress.lreq`, whose rungs raise the fee by 4 each, is refused here. -/
@[req "CHN-16"]
theorem subsets_accepted :
    both (req [g1]) = true ∧ both (req [g2]) = true ∧ narrowed (req [g2, g1]) = true ∧
      narrowed Exhibits.RungIngress.lreq = true := by
  decide +kernel

/-- Nodes 1 and 2 take the checked pair. -/
def srun : List Federation.Step :=
  [.process 1 env0 (.accept 10 false (Wall.sample 200) (spOf (req [g1, g2])) (esOf (req [g1, g2]))),
   .process 2 env0 (.accept 10 false (Wall.sample 200) (spOf (req [g1, g2])) (esOf (req [g1, g2])))]

def strace : Federation.Trace := Federation.record Kernel.current [] fed0 srun
def sfinal : Federation.Fed := Federation.runFrom Kernel.current fed0 srun

/-- **A checked run that retains the ladder.** The run is legal, checked by this ingress, and node 1's Escape retains
both rungs, so `LadderShape.acceptance_valid` and, through `LadderShape.to_rung`, every result over
`RungIngress.CheckedTrace` apply to it. -/
@[req "CHN-16"]
theorem shape_run :
    Federation.legal Kernel.current honest fed0 srun = true ∧
      (Ingress.acceptPairs strace).all
        (fun p => [req [g1, g2]].any fun q => check ctx0 2 3 true q == .accepted p.1 p.2) = true ∧
      Ingress.clawCands strace = [] ∧
      ((sfinal.worlds 1).node.cands.filter (·.isEscape)).map (·.above.length) = [2] := by
  decide +kernel

theorem shape_checked : CheckedTrace ctx0 2 3 strace :=
  checkedTrace_of ctx0 2 3 _ [req [g1, g2]] [] shape_run.2.1 (by rw [shape_run.2.2.1]; rfl)

theorem shape_execution : Federation.Execution Kernel.current honest strace sfinal :=
  Federation.execution_of_legal (.init _ fed0_fresh) shape_run.1

theorem shape_classed :
    ∀ i ∈ honest, ∀ c ∈ (sfinal.worlds i).node.cands, Ingress.Classed ctx0 c ∧ RungIngress.RungsClassed ctx0 c :=
  (RungIngress.resident_classed shape_execution (to_rung shape_checked)).1

end BtcPolicy.Exhibits.LadderShape
