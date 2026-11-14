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
/-! Exhibit fixtures: the declarations more than one exhibit module uses, each in its own namespace, in
the order `Exhibits.lean` once held them. The exhibit modules import this one and nothing else of each
other. A declaration a CI control can break is never here: its users sit beside it instead. -/

namespace BtcPolicy.Exhibits.ReleaseKernel
open BtcPolicy.Clocks BtcPolicy.Kernel
abbrev tx1 := Kernel.RegistrationCases.tx1

abbrev txE := Kernel.RegistrationCases.txE

abbrev cand := Kernel.RegistrationCases.cand

abbrev envAt (wall mono : Nat) (seen : List Tx := []) : Env :=
  Kernel.RegistrationCases.envAt wall mono seen

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

end BtcPolicy.Exhibits.ReleaseKernel

namespace BtcPolicy.Exhibits.HotLedger
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt)
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

/-- `SPN-30`: "A hot-class spend's fire time is `ingress_now + hold_secs`." -/
def fireOf (accepted : Nat) : Nat := accepted + Budget.params.hold

/-- `SPN-10`'s ceiling on a signed expiry, which `ADR-0014` takes at equality. -/
def expiryOf (accepted : Nat) : Nat := accepted + Budget.params.window

def s1 : Cand := cand 1 hot1 true (some (fireOf Budget.timeline.firstAccept))
  (expiryOf Budget.timeline.firstAccept)

def e1 : Cand := cand 2 esc1 false none (expiryOf Budget.timeline.firstAccept)

def s2 : Cand := cand 5 hot2 true (some (fireOf Budget.timeline.secondAccept))
  (expiryOf Budget.timeline.secondAccept)

def e2 : Cand := cand 6 esc2 false none (expiryOf Budget.timeline.secondAccept)

/-- The chain view each step reads: empty, or holding the claw-back from the instant it arrives.
A claw-back visible before it was broadcast would be a different trace, and under `F57` row 8's
withdrawn reading of defeat it would be one where the first spend was never due. -/
def plain (n : Nat) : Env := envAt n n

def steps (mk : Nat → Env) (tr : List (Nat × Event)) : List (Env × Event) :=
  tr.map fun x => (mk x.1, x.2)

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

/-- `DEF-5`'s settlement refund (`F57`), every other ledger value as it stands. An explicit record,
so a flip of `current` cannot reach it. -/
def withdrawnSettlement : Guards :=
  { settlement := .refundOnAnySettlement, release := .acceptedAdmission, refund := .onCollection }

/-- The twin's acceptance. `CHN-27`: "A changed transaction or expiry gets a fresh commitment and
evaluation", so one re-quoted expiry over the SAME transaction is a second commitment taking its
own charge (`POL-18`, "idempotently per commitment"). No clause fixes WHEN the re-quote arrives;
this sample is the exhibit's own choice, inside the first charge's window and far enough in that
its own window outlives it. -/
def twinAccept : Nat := 60

/-- The twin itself: same transaction, later signed expiry, its own id. -/
def s1Twin : Cand := cand 9 hot1 true (some (fireOf twinAccept)) (expiryOf twinAccept)

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

end BtcPolicy.Exhibits.HotLedger

namespace BtcPolicy.Exhibits.TwoRun
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt withdrawnTraversal withdrawnDynamics)
/-- 2-of-3, `duress_delay_secs` 200, `epsilon_secs` 5, `combine_slack_secs` 40, `hold_secs` 0.
Each spend here is handed its `fire_at` directly, and the HotClock check of `SPN-38` is
`BtcPolicy.Exhibits.HotClockHold`'s subject. `OPS-13` says "`hold_secs` has no positive lower
bound", and 0 leaves the check satisfied by every acceptance. -/
def A : Node :=
  { id := 0, t := 2, armed := false, poisoned := false, lockedDown := false, carriers := [],
    cands := [], T := Wall.sample 0, sweepActive := false, selected := [], duressDelay := 200,
    epsilon := 5, combineSlack := 40, holdSecs := 0 }

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

def sp3 : Cand := cand 7 { id := 300, inputs := [4], outflow := 0 } false none 900

def es3 : Cand := cand 8 { id := 301, inputs := [4, 5], outflow := 0 } false none 900

/-- The hot close and the driver on the effective sample alone, beside every other value as it stands. -/
def withdrawnReadTime : Rules := { Kernel.current with closeTime := .effective, driverTime := .effective }

/-- The hot close at the time ratchet and the driver on the effective sample alone. -/
def withdrawnDriverTime : Rules := { Kernel.current with driverTime := .effective }

/-- The driver at the time ratchet and the hot close on the effective sample alone. -/
def withdrawnCloseTime : Rules := { Kernel.current with closeTime := .effective }

/-- `F60`'s hot candidate: its `fire_at` is 90, so `DUR-13`'s ceiling is `90 − 5`. -/
def s60 : Cand := cand 1 hot1 true (some 90) 400

/-- The expiry route's hot pair: a `fire_at` of 80 and an expiry of 120, which meets
`SPN-30`'s "`expiry ≥ fire_at + combine_slack_secs`, equality passing" at this node's 40. -/
def sLapsing : Cand := cand 1 hot1 true (some 80) 120

def eLapsing : Cand := cand 2 esc1 false none 120

end BtcPolicy.Exhibits.TwoRun

namespace BtcPolicy.Exhibits.Membership
open BtcPolicy.Membership
def externalPath : SinglePath := ⟨10, true⟩

def internalPath : SinglePath := ⟨11, true⟩

def definitePath : SinglePath := ⟨12, false⟩

def derive (p : SinglePath) (i : Nat) : Option Script :=
  some [p.id, if p.id = 12 then 0 else i]

end BtcPolicy.Exhibits.Membership

namespace BtcPolicy.Exhibits.EarlierRelease
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Kernel.ProvenanceCases
def node (self : Nat) : Node := { A with id := self, t := 3 }

def initial (self : Nat) : World := { node := node self, exposure := [] }

def target : Tx := ⟨100, [0, 1], 10⟩

def escape : Tx := ⟨101, [0, 1], 0⟩

def oldSpend := cand 1 target true (some 100) 900

def oldEscape := cand 2 escape false none 900

def newSpend := cand 5 target true (some 300) 1000

def newEscape := cand 6 escape false none 1000

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

end BtcPolicy.Exhibits.EarlierRelease

namespace BtcPolicy.Exhibits.Evaluate
open BtcPolicy.Evaluate
def cfg : Cfg :=
  { derive := Membership.derive, max := 2, vault := ⟨[Membership.definitePath]⟩,
    escape := ⟨[Membership.externalPath]⟩,
    allow := [⟨[Membership.externalPath, Membership.internalPath]⟩], hotMaxPerTx := 60 }

end BtcPolicy.Exhibits.Evaluate

namespace BtcPolicy.Exhibits.Ingress
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ingress
open BtcPolicy.Kernel.RegistrationCases (A env0 envFire envAt)
open BtcPolicy.Federation (Step Fed Trace HotBinding legal runFrom record execution_of_legal)
open BtcPolicy.Federation.Cases (fed0 fed0_fresh honest)
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

def lcfg : Ledger.Config := { cap := 100, window := 600 }

def rung (amount sequence : Nat) : Member :=
  ⟨{ escPsbt with txInputs := [⟨txidA, 0, sequence⟩], txOutputs := [⟨[10, 0], amount⟩] }, 2, 0, none⟩

def acc (c : Ctx) (i : Nat) (d : Bool) : Step :=
  .process i env0 (.accept 10 d (Wall.sample 200) (cand c req0 req0.spend true req0.fireAt)
    (cand c req0 req0.escape false none))

end BtcPolicy.Exhibits.Ingress

namespace BtcPolicy.Exhibits.Lifetime
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Lifetime
open BtcPolicy.Kernel.RegistrationCases (A env0 envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 spendPsbt escPsbt rung)
def conf (g : Subordination) : Lifetime.Cfg :=
  { g := g, lg := Ledger.current, cfg := { cap := 100, window := 600 }, r := Kernel.current,
    ctx := ctx0 }

end BtcPolicy.Exhibits.Lifetime

namespace BtcPolicy.Exhibits.Sweep
open BtcPolicy.Kernel BtcPolicy.Kernel.RegistrationCases BtcPolicy.Sweep BtcPolicy.Sweep.Cases
open BtcPolicy.Federation.Cases (honest)
def cfgNow : Cfg := Cases.cfg Coverage.current Coverage.currentExternal Package.current

end BtcPolicy.Exhibits.Sweep

namespace BtcPolicy.Exhibits.FedSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.Exhibits.TwoRun (sLapsing eLapsing sp3 es3 cfg tblD tblN withdrawnReadTime
  withdrawnCloseTime withdrawnDriverTime s60 hot1 esc1)
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt withdrawnTraversal)
/-- The commitment an acceptance names. -/
def acceptedCid : Resp → Option Nat
  | .accepted c _ _ => some c
  | _ => none

end BtcPolicy.Exhibits.FedSilence

namespace BtcPolicy.Exhibits.Feasibility
open BtcPolicy.Feasibility
open BtcPolicy.Coverage (Coin Outpoint)
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

def mk (confirmed : List Coin) (value : Outpoint → Nat) (parentOf : Nat → Option Parent)
    (floor : Nat := 1) (creator : Package.Creator := funding) : Vault :=
  { cfg := cfgOf value creator, A := [], b := instant confirmed, parentOf, floor }

section Run
open BtcPolicy.Sweep BtcPolicy.Sweep.Cases
open BtcPolicy.Federation.Cases (honest)
end Run
end BtcPolicy.Exhibits.Feasibility

namespace BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (A env0 envFire envAt)
open BtcPolicy.Ingress (check checkedTrace_of hot_binding code code_injective frame_wf accepted_validates accepted_spend)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 txidA checked_pair lcfg)
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Recovery
open BtcPolicy.Settlement (confirmedAt)
/-- The request's one outpoint. -/
def coin : Nat := code (txidA ++ Encode.be 4 0)

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

def runOf (b : Backend) (ss : List BtcPolicy.Recovery.Step) : Trace × St := record Kernel.current [] (st0 b) ss

/-- Past the Hold on each node's own HotClock. -/
def envHeld : Env := envAt 120 110

/-- With no duress, on the same request: both nodes take it, the Hold matures on each node's own clock,
each fires, node 2's partial reaches node 1, and node 1 assembles and sends the hot spend. -/
def ordinarySteps : List Sweep.Step :=
  [acc 1 10 false, acc 2 10 false, .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩), fire 1 envHeld, fire 2 envHeld,
   .fed (.deliverPartial 1 envHeld (part sp0 2)), .observe 1 v, assemble 1 sp0.id envHeld]

def ordinaryAll : List Sweep.Step := ordinarySteps ++ [send 1 sp0.id envHeld, .chain vSpent]

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

end BtcPolicy.Exhibits.EndToEnd

namespace BtcPolicy.Exhibits.Clawback
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envAt envFire)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 escPsbt)
open BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Recovery
def clReq : Ingress.ClawbackRequest :=
  { member := ⟨{ escPsbt with txOutputs := [⟨[10, 0], 97⟩] }, 2, 0, none⟩, expiry := 2000 }

/-- The candidate the checks hand the kernel. -/
def cl0 : Cand := (Ingress.checkClawback ctx0 Classification.current clReq).getD es0

def envCl : Env := envAt 70 20

def clIn (i : Nat) (env : Env := envCl) : Sweep.Step := .fed (.process i env (.clawback cl0))

end BtcPolicy.Exhibits.Clawback

namespace BtcPolicy.Exhibits.LedgerSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.Admission (lfaithful lrun_faithful checked_on_ledger fed_bridge Counted nodeTrace)
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 lcfg checked_pair)
open BtcPolicy.Exhibits.EndToEnd
open BtcPolicy.Exhibits.TwoRun (tblD tblN)
open BtcPolicy.Recovery
/-- The run's start, every honest ledger empty. -/
def L0 : LFed := { fed := fed0, leds := fun _ => [] }

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

theorem L0_fresh : Federation.Fresh honest L0.fed := (st0_fresh v).1.1

theorem L0_sweep : ∀ i ∈ honest, (L0.fed.worlds i).node.sweepActive = false := by decide

end BtcPolicy.Exhibits.LedgerSilence

namespace BtcPolicy.Exhibits.ClawSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 lcfg)
open BtcPolicy.Exhibits.EndToEnd (honest part)
open BtcPolicy.Exhibits.LedgerSilence (L0 L0_fresh L0_sweep sched tblsD tblsN)
open BtcPolicy.Exhibits.Clawback (cl0 envCl)
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

/-- The ledgered run of `clSched`'s first `k` steps under one family. -/
def runK (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  lrun Ledger.current lcfg Kernel.current L0 ((clSched.take k).map (·.step tbls))

end BtcPolicy.Exhibits.ClawSilence

namespace BtcPolicy.Exhibits.PreRelease
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 spendPsbt escPsbt)
open BtcPolicy.Exhibits.EndToEnd (coin fed0 honest acc part assemble send)
open BtcPolicy.Exhibits.Clawback (cl0 clIn envCl)
open BtcPolicy.PreRelease (verdict failing fill)
/-- A second checked request over the same coin, whose Escape pays 99 of 100: fee 5 100 in the book. -/
def req1 : Ingress.Request :=
  { req0 with
    spend := ⟨{ spendPsbt with txOutputs := [⟨[12, 0], 41⟩, ⟨[11, 1], 54⟩] }, 2, 0, none⟩,
    escape := ⟨{ escPsbt with txOutputs := [⟨[10, 0], 99⟩] }, 2, 0, none⟩ }

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

def start (b : Backend) : State := { fed := fed0, truth := b }

/-- Nodes 1 and 2 take the checked request under duress, relay, and arm at their holder decisions. -/
def arm : List Step :=
  [acc 1 10 true, acc 2 10 true, .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩)]

/-- A schedule with its fire passes' verdicts filled in, its run, and whether the refined run admits it. -/
def sched (c : PreRelease.Cfg) (b : Backend) (ss : List Step) : List Step :=
  fill c Kernel.current [] (start b) ss

def run (c : PreRelease.Cfg) (b : Backend) (ss : List Step) : Trace × State :=
  record Kernel.current [] (start b) (sched c b ss)

end BtcPolicy.Exhibits.PreRelease

namespace BtcPolicy.Exhibits.CommonRun
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 lcfg checked_pair)
open BtcPolicy.Exhibits.EndToEnd (coin worlds honest part assemble send fire st0 st0_fresh runOf envHeld es1 tooLate ordinaryAll toRelease coerced coercedSteps v vLarge vSpent)
open BtcPolicy.Ingress (check checkedTrace_of hot_binding code_injective frame_wf accepted_validates accepted_spend)
open BtcPolicy.Recovery (fedSteps fed_record sweepTrace failures)
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

/-- Every sweep step of the composed run carries the verdict computed at its own state and history, and every
ladder pass lists no release. -/
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

/-- `EndToEnd.toRelease` at the vault holding the large coin, each pass preceded by its read, then node 1's
read; the schedule `EndToEnd.safe_without_progress` reads, less the delivery of node 2's Escape partial,
which the refined pass never emits. -/
def unusable : List Recovery.Step := integ vLarge (toRelease ++ [.observe 1 vLarge])

/-- `EndToEnd.tooLate` with its reads; then the large coin confirms and node 1's pass at 120, inside the
second Escape's window, reads it. -/
def priorFailed : List Recovery.Step := integ v (tooLate ++ [.chain vLarge, fire 1 envHeld])

end BtcPolicy.Exhibits.CommonRun

namespace BtcPolicy.Exhibits.Ladder
open BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Ladder (Part Read RCfg)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0 escPsbt)
open BtcPolicy.Exhibits.EndToEnd (honest)
open BtcPolicy.Exhibits.PreRelease (book scfg pcfg vault withCoin arm run)
def m1 : Ingress.Member := ⟨{ escPsbt with txOutputs := [⟨[10, 0], 94⟩] }, 2, 0, none⟩

def m2 : Ingress.Member := ⟨{ escPsbt with txOutputs := [⟨[10, 0], 90⟩] }, 2, 0, none⟩

def m3 : Ingress.Member := ⟨{ escPsbt with txOutputs := [⟨[10, 0], 93⟩] }, 2, 0, none⟩

def reqL : Ingress.Request := { req0 with rungs := [m1, m2] }

def r1 : Tx := Ingress.tx ctx0 m1

def r2 : Tx := Ingress.tx ctx0 m2

/-- A rung whose book delivers only 100 000 to the escape descriptor, which `CHN-16`'s "every output value at
or below the value of the same output on the rung below" rules out for a real ladder over these outputs
and which this model does not check. -/
def r1low : Tx := Ingress.tx ctx0 m3

def lbook : Book :=
  { value := fun o => if o == r1.id + 1000 then 479400 else if o == r2.id + 1000 then 459000
      else if o == r1low.id + 1000 then 479400 else book.value o,
    outputs := book.outputs,
    delivered := fun tx => if tx == r1.id then 479400 else if tx == r2.id then 459000
      else if tx == r1low.id then 100000 else book.delivered tx }

def lpre (floor : Nat) : PreRelease.Cfg :=
  { sweep := { scfg with book := lbook }, legacyLen := fun _ => 100, floor := floor }

def lcfg (floor quota : Nat) (anchor : Cursor.Anchor := Cursor.current) : Ladder.Cfg :=
  { pre := lpre floor, quota := quota, anchor := anchor }

def R1 : Rung := ⟨r1, 11⟩

def R2 : Rung := ⟨r2, 12⟩

def rc (above : Nat → List Rung) (bs : Nat → Nat := fun _ => 0) (t : Nat := 2) : RCfg :=
  { lc := lcfg 1 600, esc := es0, keys := [1, 2, 3], t := t, baseSig := bs, above := above }

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
/-- Each input's finalized witness, 476 weight units, for the three transactions the runs finalize. -/
def wit (x : Nat) : List Nat := if x == es0.tx.id || x == sp0.tx.id || x == cl0.tx.id then [476] else []

/-- The backend's package verdict, one entry per member: resident, rejected by name, or allowed. -/
def core (rej : List Nat) (b : Backend) (pkg : List Nat) : List BtcPolicy.Assembly.Entry :=
  pkg.map fun x => if (b.mempool.lookup x).isSome then .alreadyInMempool else if rej.contains x then .rejected 26
    else .allowed

def acfgR (rej : List Nat) : BtcPolicy.Assembly.Cfg := { pre := pc, witnesses := wit, test := core rej }

/-- The vault with the coin gone from the chain: its prevout is missing. -/
def vGone : Backend := { v with sequence := 2, confirmed := [] }

/-- The claw-back's own run: nodes 1 and 2 take it, fire, node 2's partial reaches node 1, which reads the vault,
assembles and sends. -/
def clRun : List Sweep.Step :=
  [clIn 1, clIn 2, fire 1 envCl, fire 2 envCl, .fed (.deliverPartial 1 envCl (part cl0 2)), .observe 1 v,
    assemble 1 cl0.id envCl, send 1 cl0.id envCl]

/-- After the ordinary assembly, a duress request on a new commitment over the same transactions arms node 1. -/
def frozenRun : List Sweep.Step :=
  ordinarySteps ++
    [.fed (.process 1 envHeld (.accept 20 true (Wall.sample 300) sp1 es1)),
     .fed (.process 2 envHeld (.accept 20 true (Wall.sample 300) sp1 es1)),
     .fed (.emit 1 20), .fed (.emit 2 20),
     .fed (.deliver 1 envHeld ⟨2, 20⟩), .fed (.deliver 2 envHeld ⟨1, 20⟩)]

/-- A resident transaction outside the vault-authorized set over the coin. -/
def vConflict : Backend := { v with sequence := 2, mempool := [(777, [coin])] }

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
open BtcPolicy.Recovery (sweepTrace)
/-- Whether step `k` of a schedule is node `i`'s fire pass. -/
def fireAt (xs : List Recovery.Step) (k i : Nat) : Bool :=
  match xs[k]? with
  | some (.base (.fed (.process j _ .firePass))) => j == i
  | _ => false

/-- Nodes 1 and 2 arm and fire as in `EndToEnd.toRelease`; node 1 fires again at the vault; then the large coin
confirms and node 1 fires a third time, reading it. Each fire pass is preceded by its node's read. -/
def lsched : List Recovery.Step := integ v (toRelease ++ [fire 1 envFire, .chain vLarge, fire 1 envFire])

/-- `Exhibits.CommonRun.book` with the rung outputs of `Exhibits.Ladder.lbook`. -/
def ibook : Sweep.Book :=
  { Exhibits.Ladder.lbook with
    value := fun o => if o == 9 then 1000000 else Exhibits.Ladder.lbook.value o }

def isw : Sweep.Cfg := { scfg with book := ibook }

def ipre : PreRelease.Cfg := { pc with sweep := isw }

def ilc : Ladder.Cfg := { pre := ipre, quota := 600, anchor := Cursor.current }

end BtcPolicy.Exhibits.Integrated

namespace BtcPolicy.Exhibits.LadderPass
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire)
open BtcPolicy.Exhibits.Ingress (es0)
open BtcPolicy.Exhibits.EndToEnd (runOf v)
open BtcPolicy.Exhibits.CommonRun (inst pc)
open BtcPolicy.Exhibits.Integrated (lsched)
open BtcPolicy.Recovery (sweepTrace)
/-- Node `i`'s world after the first `k` steps of `lsched`. -/
def wAt (k i : Nat) : World := (runOf (inst v) (lsched.take k)).2.sw.fed.worlds i

end BtcPolicy.Exhibits.LadderPass

namespace BtcPolicy.Exhibits.RungRelease
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Kernel.RegistrationCases (envFire env0)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest v vLarge st0 st0_fresh part)
open BtcPolicy.Exhibits.CommonRun (inst onBook readFirst)
open BtcPolicy.Exhibits.Integrated (ilc)
/-- `es0` with the two rungs of `Exhibits.Ladder.ladder_from_ingress` above its base. -/
def esR : Cand := { es0 with above := [Exhibits.Ladder.R1, Exhibits.Ladder.R2] }

def accR (i : Nat) : Sweep.Step := .fed (.process i env0 (.accept 10 true (Wall.sample 200) sp0 esR))

def fire (i : Nat) : Sweep.Step := .fed (.process i envFire .firePass)

def lad (i : Nat) (l : List (Nat × Track × List Nat) := []) : Sweep.Step :=
  .fed (.process i { envFire with ladder := l } .ladderPass)

/-- An instant whose block at the anchor of its tip reports median `m` (`DUR-30`). -/
def withMedian (b : Backend) (m : Nat) : Backend := { b with medians := [(BumpTarget.anchor b.tip.height, m)] }

def vm : Backend := withMedian v 100

def vm2 : Backend := withMedian v 200

def vmL : Backend := withMedian vLarge 200

/-- The history as written: each fire pass and ladder pass lists nothing until `RungRelease.fill` computes it. -/
def raw : List Sweep.Step :=
  [accR 1, accR 2, .fed (.emit 1 10), .fed (.emit 2 10), .fed (.deliver 1 env0 ⟨2, 10⟩),
   .fed (.deliver 2 env0 ⟨1, 10⟩), fire 1, fire 2, lad 1, .chain vm2, fire 1, lad 1, .chain vmL, fire 1, lad 1]

/-- The history with each fire pass preceded by its node's read, and each fire pass and ladder pass carrying
the value computed at its own state and history. -/
def sched : List Sweep.Step :=
  RungRelease.fill ilc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm raw).map onBook)

/-- Node 1's partial on input 0 of rung transaction `g` under `es0`'s commitment. -/
def rrow (g : Tx) : Exp := { msg := sighash g 0, input := 0, signer := 1, hot := false, cid := es0.id }

end BtcPolicy.Exhibits.RungRelease

namespace BtcPolicy.Exhibits.LadderRelease
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Kernel.RegistrationCases (envFire env0)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh part)
open BtcPolicy.Exhibits.CommonRun (inst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (accR fire lad vm)
/-- Node 2's partial on input 0 of rung transaction `g` under `es0`'s commitment. -/
def row2 (g : Tx) : Exp := { msg := sighash g 0, input := 0, signer := 2, hot := false, cid := es0.id }

end BtcPolicy.Exhibits.LadderRelease

namespace BtcPolicy.Exhibits.RungIngress
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh)
open BtcPolicy.Exhibits.CommonRun (inst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (esR sched rrow vm)
def lreq : RungIngress.Request :=
  { spend := req0.spend, escape := ⟨req0.escape, 0⟩,
    rungs := [⟨Exhibits.Ladder.m1, 11⟩, ⟨Exhibits.Ladder.m2, 12⟩], expiry := req0.expiry, fireAt := req0.fireAt }

/-- The rung run with node 1's partial on input 0 of `r1` delivered to node 2 at the end. -/
def dsched : List Sweep.Step := sched ++ [.fed (.deliverPartial 2 envFire (rrow Exhibits.Ladder.r1))]

def runD : Sweep.Trace × Sweep.State := Sweep.record Kernel.current [] (st0 (inst vm)).sw dsched

end BtcPolicy.Exhibits.RungIngress

namespace BtcPolicy.Exhibits.RungAssembly
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire envLate)
open BtcPolicy.Exhibits.Ingress (ctx0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh)
open BtcPolicy.Exhibits.CommonRun (inst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (lad vm)
open BtcPolicy.Exhibits.RungIngress (lreq runD dsched)
open BtcPolicy.Exhibits.LadderRelease (row2)
/-- After `runD`: the truth back at the vault, node 2's read and ladder pass, node 2's `r1` partial delivered to node
1, and node 1's read, each pass carrying its computed value. -/
def more : List Sweep.Step :=
  LadderRelease.fill ilc Kernel.current runD.1 runD.2
    [.chain (inst vm), .observe 2 (inst vm), lad 2, .fed (.deliverPartial 1 envFire (row2 Exhibits.Ladder.r1)),
     .observe 1 (inst vm)]

/-- The whole history: `runD`'s schedule and `more` as sweep steps, then node 1's assembly of rung 1 and its send. -/
def esched : List RungAssembly.Step :=
  (dsched ++ more).map .base ++ [.assemble 1 es0.id 1, .send 1 envFire es0.id 1]

/-- Node 1's acceptances with the Escape's rung hashes raised by 10. -/
def twist : Sweep.Step → Sweep.Step
  | .fed (.process i env (.accept cid d E sp es)) =>
    .fed (.process i env (.accept cid d E sp
      (if i == 1 then { es with above := es.above.map fun g => { g with userSig := g.userSig + 10 } } else es)))
  | s => s

/-- `esched` with node 1's acceptances twisted. -/
def hsched : List RungAssembly.Step := esched.map fun
  | .base b => .base (twist b)
  | s => s

end BtcPolicy.Exhibits.RungAssembly

namespace BtcPolicy.Exhibits.LadderShape
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.LadderShape
open BtcPolicy.Ingress (escapeSequence)
open BtcPolicy.Kernel.RegistrationCases (env0)
open BtcPolicy.Federation.Cases (fed0 fed0_fresh honest)
open BtcPolicy.Exhibits.Ingress (ctx0 txidA)
def coin : Encode.Output := ⟨[12, 0], 10000⟩

/-- An Escape over the given outpoints, each holding `coin`, paying the given outputs. -/
def escOf (ins : List Encode.Bytes) (outs : List Encode.Output) : Ingress.Member :=
  ⟨{ txInputs := ins.map fun x => ⟨x, 0, escapeSequence⟩, txOutputs := outs,
     inputMaps := ins.map fun _ => some coin, outputHints := outs.map fun _ => false }, 2, 0, none⟩

def esc (amount : Nat) : Ingress.Member := escOf [txidA] [⟨[10, 0], amount⟩]

def spendOf (ins : List Encode.Bytes) : Ingress.Member :=
  ⟨{ txInputs := ins.map fun x => ⟨x, 0, 0⟩, txOutputs := [⟨[12, 0], 10000 * ins.length - 60⟩, ⟨[11, 1], 55⟩],
     inputMaps := ins.map fun _ => some coin, outputHints := [true, false] }, 2, 0, none⟩

/-- A SpendRequest over these outpoints with this Escape and these rungs, each rung's user-signature hash 11. -/
def reqOf (ins : List Encode.Bytes) (b : Ingress.Member) (rs : List Ingress.Member) : RungIngress.Request :=
  { spend := spendOf ins, escape := ⟨b, 0⟩, rungs := rs.map fun m => ⟨m, 11⟩, expiry := 200,
    fireAt := some (Wall.sample 100) }

def base : Ingress.Member := esc 9800

def g1 : Ingress.Member := esc 9500

def g2 : Ingress.Member := esc 9317

def req (rs : List Ingress.Member) : RungIngress.Request := reqOf [txidA] base rs

/-- The candidates a check hands the kernel for a request it accepts. -/
def spOf (q : RungIngress.Request) : Cand := Ingress.cand ctx0 q.plain q.spend true q.fireAt

def esOf (q : RungIngress.Request) : Cand :=
  RungIngress.withLadder ctx0 q (Ingress.cand ctx0 q.plain q.escape.member false none)

end BtcPolicy.Exhibits.LadderShape
