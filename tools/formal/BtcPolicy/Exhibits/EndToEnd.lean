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


theorem coin_is_input : sp0.tx.inputs = [coin] ∧ es0.tx.inputs = [coin] := by decide +kernel




/-- The uncovered vault at the coin's lock. -/
def vLargeRipe : Backend :=
  { vLarge with tip := ⟨9, 109⟩, sequence := 2, mtps := [(2, 1000), (5, 2000), (9, 1000 + 15552000)] }








abbrev base (ss : List Sweep.Step) : List BtcPolicy.Recovery.Step := ss.map .base
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



/-- `SPN-50`'s checks pass, and the claw-back is a transaction of its own over the Escape's coin, under a
commitment of its own, escape-class and not hot. -/
@[req "SPN-50"]
theorem checked_clawback :
    Ingress.checkClawback ctx0 Classification.current clReq = some cl0 ∧ cl0.hot = false ∧
      cl0.tx.inputs = es0.tx.inputs ∧ cl0.tx.id ≠ es0.tx.id ∧ cl0.id ≠ es0.id ∧
      Ingress.classOf ctx0 clReq.member = some .escape := by
  decide +kernel


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




/-- An observer that has seen `k` observations runs the `k`-th step of `sched`. -/
def replay : Observer where
  next h := sched[h.length]?

def apairs (c : Scheduler) (k : Nat) : List (FObs × FObs) :=
  awalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN c k L0 L0 [] []

/-- The ledgered run of the schedule's first `k` steps under one family. -/
def runK (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  lrun Ledger.current lcfg Kernel.current L0 ((sched.take k).map (·.step tbls))



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




/-- An observer that has seen `k` observations runs the `k`-th step of `clSched`. -/
def replay : Observer where
  next h := clSched[h.length]?

def apairs (n : Nat) : List (FObs × FObs) :=
  awalk Silence.current Ledger.current lcfg Kernel.current honest honest tblsD tblsN replay.sched n
    L0 L0 [] []


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
(`ClawHandler.hfed_silence_fresh`). A later exact retry of the second key answers 70, not the 80 that
request was given, as `SPN-50` has it: "a retained acceptance key MUST return the claw-back commitment's
first `Accepted` on this node verbatim" (`Exhibits.ClawHandler.retry_replays_first`). -/
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

/-- **The retry after re-registration replays the first `Accepted`.** After the run above, an exact retry
of the request with other PSBT bytes, under another nonce, is a replay in both families and answers the
commitment's first `Accepted`, at 70, though that request was answered `Accepted` at 80. `SPN-50`: "a
retained acceptance key MUST return the claw-back commitment's first `Accepted` on this node verbatim". -/
@[req "SPN-50"]
theorem retry_replays_first :
    caseOf (hrun tblsD 10 H0 psched) 1 { qS with nonce := 4, psbt := pB } = .replay (acc1 70) ∧
      caseOf (hrun tblsN 10 H0 psched) 1 { qS with nonce := 4, psbt := pB } = .replay (acc1 70) := by
  decide +kernel

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
by `PreRelease.fill` and then checked by `PreRelease.legal`, never assumed; no run below takes a ladder
pass. The book is a model parameter in sats: the coin holds 510 000, and the Escape pays 499 800, all of it to
the escape descriptor, so 98 of every 100 as its checked PSBT does; its fee is 10 200. The legacy length of
every transaction is 100 bytes, so the Escape's maximum finalized vsize at threshold 2 of 3 keys is 221, and
the floor is 1 unless a run says otherwise. -/

def sp1 : Cand := Ingress.cand ctx0 req1 req1.spend true req1.fireAt




/-- A later instant with an outside transaction resident over the coin. -/
def vConflict : Backend := { vault with sequence := 2, mempool := [(777, [coin])] }
/-- A later instant the coin is absent from. -/
def vMissing : Backend := { vault with sequence := 2, confirmed := [] }
/-- The claw-back resident. -/
def vRes : Backend := { vault with sequence := 2, mempool := [(cl0.tx.id, cl0.tx.inputs)] }
/-- The claw-back confirmed, the coin spent. -/
def vMined : Backend :=
  { vault with tip := ⟨6, 106⟩, sequence := 2, confirmed := [], mined := [(cl0.tx.id, cl0.tx.inputs)] }

def fire (i : Nat) (env : Env := envFire) : Step := .fed (.process i env .firePass)
def envLater : Env := envAt 125 65


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
