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

namespace BtcPolicy.Exhibits.RungIngress
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh)
open BtcPolicy.Exhibits.CommonRun (inst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (esR sched rrow vm)

/-! ### Checked ingress registers the ladder, and possession over it

Research task `bps-9oab.8`: checked ingress that registers the Escape's rungs (`RungIngress.check`) and a
node's possession over every rung it retains (`RungIngress.held`). The request is `Exhibits.Ladder.reqL`'s with
the base's user-signature hash 0 and the rungs' 11 and 12 (`Exhibits.RungIngress.lreq`). The run is
`Exhibits.RungRelease.rung_on_run`'s, whose ladder passes release `r1` and `r2`, with node 1's partial on `r1`
then delivered to node 2. -/


/-- **The ladder from checked ingress.** The check accepts `lreq` with `req0`'s spend and the Escape
`Exhibits.RungRelease.esR`, whose rungs are the rung members' transactions `r1` and `r2`; without the hashes the
request is `Exhibits.Ladder.reqL`. A rung missing `CHN-15`'s sequence refuses the whole request, and with no
rung the check accepts `req0`'s pair as `Ingress.check` does. -/
@[req "SPN-32"]
theorem ladder_registered :
    RungIngress.check ctx0 true lreq = .accepted sp0 esR ∧ lreq.plain = Exhibits.Ladder.reqL ∧
      esR.above.map (·.tx) = [Exhibits.Ladder.r1, Exhibits.Ladder.r2] ∧
      RungIngress.check ctx0 true
          { lreq with rungs := [⟨Exhibits.Ingress.rung 97 Ingress.escapeSequence, 11⟩,
            ⟨Exhibits.Ingress.rung 96 0, 12⟩] } = .refused .PSBT_INCONSISTENT ∧
      RungIngress.check ctx0 true { lreq with rungs := [] } = .accepted sp0 es0 ∧
      Ingress.check ctx0 true req0 = .accepted sp0 es0 := by
  decide +kernel



/-- **A rung's possession on the composed run.** The schedule is a legal run of the fire pass over the whole
ladder (`LadderRelease.legal`), every acceptance on it is `lreq`'s verdict under this check and it takes no
claw-back, and node 2's Escape retains both rungs, so `Ingress.CheckedTrace` cannot hold of it
(`Ingress.resident_no_rungs`). After the delivery node 2 holds two signers on `r1`'s one input, its own and node
1's, which is `DUR-28`'s quorum at a threshold of 2 over its possession on the ladder; `Federation.held`, which
reads the base alone, holds no `r1` record. On `r2` node 2 holds only its own signature: node 1's `r1` partial
does not count for it. A partial on a rung node 2 does not retain, `r1low`, is not stored. -/
@[req "DUR-28"]
theorem rung_held_on_run :
    LadderRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw dsched = true ∧
      (Ingress.acceptPairs (Sweep.fedTrace runD.1)).all
        (fun p => [lreq].any fun q => RungIngress.check ctx0 true q == .accepted p.1 p.2) = true ∧
      Ingress.clawCands (Sweep.fedTrace runD.1) = [] ∧
      (((runD.2.fed.worlds 2).node.cands.filter (·.isEscape)).map (·.above.length)) = [2] ∧
      Authority.quorum [1, 2, 3] 2 Exhibits.Ladder.r1
        (RungIngress.held 2 (Sweep.fedTrace runD.1) runD.2.fed) = true ∧
      ((Federation.held 2 (Sweep.fedTrace runD.1) runD.2.fed).filter
        (·.msg.1 == Exhibits.Ladder.r1.id)) = [] ∧
      Authority.quorum [1, 2, 3] 2 Exhibits.Ladder.r2
        (RungIngress.held 2 (Sweep.fedTrace runD.1) runD.2.fed) = false ∧
      RungIngress.storable (runD.2.fed.worlds 2).node (sighash Exhibits.Ladder.r1low 0) 0 es0.id = false ∧
      RungIngress.storable (runD.2.fed.worlds 2).node (sighash Exhibits.Ladder.r1 0) 0 es0.id = true ∧
      Federation.storable (runD.2.fed.worlds 2).node (sighash Exhibits.Ladder.r1 0) 0 es0.id = false := by
  decide +kernel

theorem rung_held_execution : LadderRelease.Execution ilc Kernel.current honest runD.1 runD.2 :=
  LadderRelease.execution_of_legal (.init _ (st0_fresh (inst vm)).1) rung_held_on_run.1

/-- The run is checked by this ingress, so `RungIngress.hot_binding` covers its inventory: no partial on it
outside the extracted set and under a non-hot candidate, rung partials included, shares the spend's input-0
message. -/
theorem rung_run_checked : RungIngress.CheckedTrace ctx0 (Sweep.fedTrace runD.1) :=
  RungIngress.checkedTrace_of ctx0 _ [lreq] [] rung_held_on_run.2.1 (by rw [rung_held_on_run.2.2.1]; rfl)

@[req "DUR-8"]
theorem rung_run_hot_binding :
    Federation.HotBinding runD.2.fed (sighash (Ingress.tx ctx0 req0.spend) 0) := by
  have h := ladder_registered.2.2.2.2.2
  exact RungIngress.hot_binding (Sweep.fed_execution (LadderRelease.to_sweep rung_held_execution))
    rung_run_checked Ingress.code_injective (Ingress.frame_wf (Ingress.accepted_validates h).1)
    (Ingress.accepted_spend h).1

/-! ### `SPN-32`'s ordered rung txids on a repeat

Node 2 at the end of `runD` retains `lreq`'s pair, its Escape with the rungs `r1` and `r2`. Each request below is
accepted by `RungIngress.check` with `lreq`'s spend commitment; at node 2 the kernel step and the response decide
it. -/

/-- `lreq` with the ladder `r1` alone, a proper prefix of the resident's. -/
def q1 : RungIngress.Request := { lreq with rungs := [⟨Exhibits.Ladder.m1, 11⟩] }

/-- `lreq` with its two rungs in the other order. -/
def q21 : RungIngress.Request := { lreq with rungs := [⟨Exhibits.Ladder.m2, 12⟩, ⟨Exhibits.Ladder.m1, 11⟩] }

/-- `lreq` with no rung. -/
def q0 : RungIngress.Request := { lreq with rungs := [] }

/-- `lreq` with a third rung appended: the resident's ladder is a proper prefix of the request's. -/
def q3 : RungIngress.Request := { lreq with rungs := lreq.rungs ++ [⟨Exhibits.Ladder.m3, 13⟩] }

/-- `lreq` with other user-signature hashes on both rungs, over the same transactions. -/
def qh : RungIngress.Request := { lreq with rungs := [⟨Exhibits.Ladder.m1, 21⟩, ⟨Exhibits.Ladder.m2, 22⟩] }

/-- `qh` with another user-signature hash on the base as well. -/
def qhb : RungIngress.Request := { qh with escape := ⟨req0.escape, 5⟩ }

/-- A fire time at the expiry, which gate 27 refuses at any positive slack. -/
def late : Option Clocks.Wall := some (Clocks.Wall.sample lreq.expiry)

/-- `q1` with the late fire time. -/
def q1late : RungIngress.Request := { q1 with fireAt := late }

/-- `lreq` with the late fire time. -/
def qlate : RungIngress.Request := { lreq with fireAt := late }

/-- Node 2 at the end of `runD`, retaining `lreq`'s pair with both rungs. -/
def n2 : Kernel.Node := (runD.2.fed.worlds 2).node

/-- The pair checked ingress hands the kernel for a request, if it accepts it. -/
def pairOf (q : RungIngress.Request) : Option (Cand × Cand) :=
  match RungIngress.check ctx0 true q with
  | .accepted sp es => some (sp, es)
  | _ => none

/-- The acceptance event for a checked pair, on a nonce node 2 has not seen. -/
def evOf (p : Cand × Cand) : Kernel.Event := .accept 77 false (Clocks.Wall.sample lreq.expiry) p.1 p.2

def lcfg : Ledger.Config := { cap := 1000, window := 120 }

/-- At node 2 after `runD`, the kernel step on a request's checked pair and its response: whether the registry
is unchanged, the new Carrier's `(accepted, mayOpen)`, and the response. -/
def atNode2 (q : RungIngress.Request) : Option (Bool × Option (Bool × Bool) × Silence.Resp) :=
  (pairOf q).map fun p =>
    let n := (Kernel.step Kernel.current envFire (runD.2.fed.worlds 2) (evOf p)).1.node
    (n.cands == n2.cands, (n.carriers.find? (·.cid == 77)).map (fun k => (k.accepted, k.mayOpen)),
      Silence.respond Kernel.current lcfg envFire { world := runD.2.fed.worlds 2, led := [] } (evOf p))

def isAccepted : Silence.Resp → Bool
  | .accepted .. => true
  | _ => false

/-- `runD` with `q1`'s checked pair processed at node 2. -/
def runR : Sweep.Trace × Sweep.State :=
  Sweep.record Kernel.current runD.1 runD.2
    [.fed (.process 2 envFire (evOf (sp0, RungIngress.withLadder ctx0 q1 es0)))]

set_option synthInstance.maxSize 4096 in
/-- **A repeat with other rung txids is a conflicting resident commitment.** `SPN-32`: "The resident Escape MUST
also have the same **ordered rung txids**, including the empty list", and "any immutable mismatch MUST refuse the
whole registration as `PSBT_INCONSISTENT` / `candidate_identity`, leaving every resident untouched". Node 2
retains `lreq`'s Escape with `r1` then `r2`. Checked ingress accepts `q1`, whose ladder is `r1` alone, with
`lreq`'s spend; the run `runR` appends that acceptance at node 2 to `runD`, legal and checked by this ingress. The
step leaves the registry as it was and stages a Carrier that is neither accepted nor may open, and the response
is `PSBT_INCONSISTENT`, where the earlier comparison (`Kernel.pairAdmitsPre`) retained the pair. So are the
reordered ladder, the empty one and the longer one whose prefix is the resident's. With a fire time gate 27
refuses, the same `q1` is `EXPIRY_TOO_SHORT`: the pair is not compatible, so gate 27 reads the request's own fire
time (`SPN-30`), and it refuses first; the exact repeat with that fire time reads the resident's and is accepted.
A repeat with other user-signature hashes on both rungs, and one with another on the base as well, over the same
transactions, are accepted with an accepted Carrier that may open, as the exact repeat is. -/
@[req "SPN-32"]
theorem repeat_rungs_refused :
    pairOf q1 = some (sp0, RungIngress.withLadder ctx0 q1 es0) ∧
      LadderRelease.legal ilc Kernel.current honest runD.1 runD.2
        [.fed (.process 2 envFire (evOf (sp0, RungIngress.withLadder ctx0 q1 es0)))] = true ∧
      (Ingress.acceptPairs (Sweep.fedTrace runR.1)).all
        (fun p => [lreq, q1].any fun q => RungIngress.check ctx0 true q == .accepted p.1 p.2) = true ∧
      Ingress.clawCands (Sweep.fedTrace runR.1) = [] ∧
      (runR.2.fed.worlds 2).node.cands = n2.cands ∧
      ((runR.2.fed.worlds 2).node.carriers.find? (·.cid == 77)).map (fun k => (k.accepted, k.mayOpen)) =
        some (false, false) ∧
      Silence.respond Kernel.current lcfg envFire { world := runD.2.fed.worlds 2, led := [] }
        (evOf (sp0, RungIngress.withLadder ctx0 q1 es0)) = .refused .PSBT_INCONSISTENT ∧
      Kernel.pairAdmitsPre Kernel.current n2 sp0 (RungIngress.withLadder ctx0 q1 es0) = true ∧
      [q21, q0, q3].map atNode2 =
        List.replicate 3 (some (true, some (false, false), .refused .PSBT_INCONSISTENT)) ∧
      (pairOf q1late).map (·.1.id) = some sp0.id ∧
      atNode2 q1late = some (true, some (false, false), .refused .EXPIRY_TOO_SHORT) ∧
      [qh, qhb, lreq, qlate].map (fun q => (atNode2 q).map fun x => (x.2.1, isAccepted x.2.2)) =
        List.replicate 4 (some (some (true, true), true)) := by
  decide +kernel

theorem repeat_run_execution : LadderRelease.Execution ilc Kernel.current honest runR.1 runR.2 :=
  LadderRelease.execution_of_legal rung_held_execution repeat_rungs_refused.2.1

theorem repeat_run_checked : RungIngress.CheckedTrace ctx0 (Sweep.fedTrace runR.1) :=
  RungIngress.checkedTrace_of ctx0 _ [lreq, q1] [] repeat_rungs_refused.2.2.1
    (by rw [repeat_rungs_refused.2.2.2.1]; rfl)

end BtcPolicy.Exhibits.RungIngress

namespace BtcPolicy.Exhibits.RungAssembly
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire envLate)
open BtcPolicy.Exhibits.Ingress (ctx0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh)
open BtcPolicy.Exhibits.CommonRun (inst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (lad vm)
open BtcPolicy.Exhibits.RungIngress (lreq runD dsched qh)
open BtcPolicy.Exhibits.LadderRelease (row2)

/-! ### A rung from checked ingress to its send

Research task `bps-9oab.8`: a rung's assembly and send as a layer over the run of the fire pass over the whole ladder
(`RungAssembly.Execution`). The run is `Exhibits.RungIngress.runD`'s: the Escape's ladder registered by checked
ingress (`Exhibits.RungIngress.lreq`), both nodes' fire passes, node 1's ladder passes releasing `r1` and then `r2`,
and node 1's `r1` partial delivered to node 2. It goes on: the truth returns to the vault at a median of 100, node 2
reads it and takes a ladder pass, which latches `r1` and queues node 2's `r1` partial; that partial reaches node 1,
which reads the vault, assembles `r1` and sends it. Each fire pass and ladder pass carries the value computed at its
own state and history (`LadderRelease.fill`). Each input's finalized witness weighs 476 units, and the backend's
package verdict is `Exhibits.Assembly.core`'s, as in section 17. -/

/-- Each input's finalized witness, 476 weight units, for the base and the two rungs. -/
def rwit (x : Nat) : List Nat :=
  if x == es0.tx.id || x == Exhibits.Ladder.r1.id || x == Exhibits.Ladder.r2.id then [476] else []

def rcfg : RungAssembly.Cfg := { lc := ilc, witnesses := rwit, test := Exhibits.Assembly.core [] }



def st0R : RungAssembly.State := { sw := (st0 (inst vm)).sw }

/-- The trace and state after the first `n` steps. -/
def runE (n : Nat) : RungAssembly.Trace × RungAssembly.State :=
  RungAssembly.record Kernel.current [] st0R (esched.take n)

/-- Node 1's Escape-role resident under the Escape's commitment after the first `n` steps, read through `f`. -/
def atNode1 {α : Type} (n : Nat) (f : RungAssembly.Trace × RungAssembly.State → Cand → α) : Option α :=
  (RungAssembly.escapeAt (((runE n).2.sw.fed.worlds 1).node) es0.id).map (f (runE n))

/-- **A rung from checked ingress to its send, on the composed run.** The schedule is a legal run of the layer
(`RungAssembly.legal`): every acceptance on its sweep trace is `lreq`'s verdict under `RungIngress.check` and it
takes no claw-back. At step 22 node 2's ladder pass lists `r1`'s release. Before the assembly, at step 25, node 1's
Escape is at latch 2 and its finalization over its possession on the ladder is rung 1: of the base, `r1` and `r2`,
only `r1` has two signers, node 1's own and node 2's delivered partial, and `r2` has node 1's alone. The assembly of
rung 1 passes `Assembly.rungCheck` there, and one of rung 2 is refused; a send before the assembly is refused. After
it, the send at the fire pass's instant is admitted, while one past the Escape's window (`envLate`) and one of rung 2,
which was never assembled, are refused. At the end node 1 has assembled and sent `r1` and nothing else, and no
candidate of node 1 carries the kernel's broadcast or package bit: the kernel does not see a rung's send. -/
@[req "DUR-29"]
theorem rung_sent_on_run :
    RungAssembly.legal rcfg Kernel.current honest [] st0R esched = true ∧ esched.length = 27 ∧
      (Ingress.acceptPairs (Sweep.fedTrace (RungAssembly.sweepTrace (runE 27).1))).all
        (fun p => [lreq].any fun q => RungIngress.check ctx0 true q == .accepted p.1 p.2) = true ∧
      Ingress.clawCands (Sweep.fedTrace (RungAssembly.sweepTrace (runE 27).1)) = [] ∧
      RungRelease.listed ilc (runE 22).2.sw (RungAssembly.sweepTrace (runE 22).1) 2 =
        [(es0.id, { latch := 1, floor := 2 }, [1])] ∧
      atNode1 25 (fun p c => (c.track.latch, RungAssembly.finalAt rcfg p.2.sw (RungAssembly.sweepTrace p.1) 1 c,
        (List.range 3).map fun k => Ladder.quorumAt [1, 2, 3] 2 c.ladder
          (RungAssembly.heldAt p.2.sw (RungAssembly.sweepTrace p.1) 1) k)) =
        some (2, some 1, [false, true, false]) ∧
      RungAssembly.admits rcfg Kernel.current honest (runE 25).2 (runE 25).1 (.assemble 1 es0.id 1) = true ∧
      RungAssembly.admits rcfg Kernel.current honest (runE 25).2 (runE 25).1 (.assemble 1 es0.id 2) = false ∧
      RungAssembly.admits rcfg Kernel.current honest (runE 25).2 (runE 25).1 (.send 1 envFire es0.id 1) = false ∧
      RungAssembly.admits rcfg Kernel.current honest (runE 26).2 (runE 26).1 (.send 1 envFire es0.id 1) = true ∧
      RungAssembly.admits rcfg Kernel.current honest (runE 26).2 (runE 26).1 (.send 1 envLate es0.id 1) = false ∧
      RungAssembly.admits rcfg Kernel.current honest (runE 26).2 (runE 26).1 (.send 1 envFire es0.id 2) = false ∧
      (runE 27).2.assembled = [(1, es0.id, Exhibits.Ladder.r1.id)] ∧
      (runE 27).2.sent = [(1, es0.id, Exhibits.Ladder.r1.id)] ∧
      (((runE 27).2.sw.fed.worlds 1).node.cands.all fun c => !c.broadcast && !c.packageOk) = true := by
  decide +kernel

theorem rung_sent_execution :
    RungAssembly.Execution rcfg Kernel.current honest (runE 27).1 (runE 27).2 := by
  have hx := RungAssembly.execution_of_legal (.init st0R ⟨(st0_fresh (inst vm)).1, rfl, rfl⟩)
    rung_sent_on_run.1
  have hl : esched.take 27 = esched := List.take_of_length_le (Nat.le_of_eq rung_sent_on_run.2.1)
  simpa [runE, hl] using hx

/-- The run's sweep trace is checked by `RungIngress.check`. -/
theorem rung_sent_checked :
    RungIngress.CheckedTrace ctx0 (Sweep.fedTrace (RungAssembly.sweepTrace (runE 27).1)) :=
  RungIngress.checkedTrace_of ctx0 _ [lreq] [] rung_sent_on_run.2.2.1 (by rw [rung_sent_on_run.2.2.2.1]; rfl)

/-- `RungAssembly.sent_in_order` on the run: node 1's send of `r1` was taken where the Escape was due and
authorized, after node 1's own admitted assembly of `r1`. -/
theorem rung_sent_in_order :
    1 ∈ honest ∧ ∃ T₁ T₂ st₀ env m, (runE 27).1 = T₂ ++ (st₀, .send 1 env es0.id m) :: T₁ ∧ ∃ c g,
      RungAssembly.escapeAt (st₀.sw.fed.worlds 1).node es0.id = some c ∧ c.ladder[m]? = some g ∧
      g.tx.id = Exhibits.Ladder.r1.id ∧ due Kernel.current env (st₀.sw.fed.worlds 1).node c = true ∧
      releaseAuthorized Kernel.current (st₀.sw.fed.worlds 1).node c = true ∧
      RungAssembly.AssembledRung rcfg T₁ 1 es0.id Exhibits.Ladder.r1.id :=
  RungAssembly.sent_in_order rung_sent_execution (by rw [rung_sent_on_run.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; simp)

/-! ### The store test without the user-signature hash

`NCH-24`'s store test checks that "the user-signature hash matches"; `RungIngress.storable` does not, since a partial
row carries no hash. The schedule below is `esched` with node 1's acceptances carrying its Escape's rung hashes 10
higher, 21 and 22, which is `Exhibits.RungIngress.qh`'s verdict; node 2's stay `lreq`'s 11 and 12. -/



def runH : RungAssembly.Trace × RungAssembly.State := RungAssembly.record Kernel.current [] st0R hsched

/-- `Ladder`'s own run with node 1 retaining the rungs under the hashes 21 and 22 and every other node under 11 and
12. -/
def hrc : Ladder.RCfg := Exhibits.Ladder.rc fun i =>
  if i == 1 then [{ Exhibits.Ladder.R1 with userSig := 21 }, { Exhibits.Ladder.R2 with userSig := 22 }]
  else [Exhibits.Ladder.R1, Exhibits.Ladder.R2]

/-- **The composed run's store test keeps a partial `NCH-24` drops.** The schedule is a legal run of the layer, and
every acceptance on its sweep trace is `lreq`'s or `Exhibits.RungIngress.qh`'s verdict under `RungIngress.check`:
both have the same rung transactions, so registration compares them as compatible (`SPN-32`). At the end node 1
retains the rungs under the hashes 21 and 22 and node 2 under 11 and 12, and node 1 has assembled and sent `r1`,
whose quorum counts node 2's delivered partial. On `Ladder`'s own run, with the same hashes, the store test refuses
node 2's partial on `r1` at node 1 (`Ladder.stores`), as `NCH-24` does. -/
@[req "NCH-24"]
theorem hash_mismatch_sent :
    RungAssembly.legal rcfg Kernel.current honest [] st0R hsched = true ∧
      (Ingress.acceptPairs (Sweep.fedTrace (RungAssembly.sweepTrace runH.1))).all
        (fun p => [lreq, qh].any fun q => RungIngress.check ctx0 true q == .accepted p.1 p.2) = true ∧
      Ingress.clawCands (Sweep.fedTrace (RungAssembly.sweepTrace runH.1)) = [] ∧
      (RungAssembly.escapeAt (runH.2.sw.fed.worlds 1).node es0.id).map (·.above.map (·.userSig)) =
        some [21, 22] ∧
      (RungAssembly.escapeAt (runH.2.sw.fed.worlds 2).node es0.id).map (·.above.map (·.userSig)) =
        some [11, 12] ∧
      runH.2.assembled = [(1, es0.id, Exhibits.Ladder.r1.id)] ∧
      runH.2.sent = [(1, es0.id, Exhibits.Ladder.r1.id)] ∧
      Ladder.stores hrc 1 { txid := Exhibits.Ladder.r1.id, userSig := 11, input := 0, signer := 2 } = false := by
  decide +kernel

theorem hash_mismatch_execution : RungAssembly.Execution rcfg Kernel.current honest runH.1 runH.2 :=
  RungAssembly.execution_of_legal (.init st0R ⟨(st0_fresh (inst vm)).1, rfl, rfl⟩) hash_mismatch_sent.1

theorem hash_mismatch_checked :
    RungIngress.CheckedTrace ctx0 (Sweep.fedTrace (RungAssembly.sweepTrace runH.1)) :=
  RungIngress.checkedTrace_of ctx0 _ [lreq, qh] [] hash_mismatch_sent.2.1
    (by rw [hash_mismatch_sent.2.2.1]; rfl)

end BtcPolicy.Exhibits.RungAssembly

namespace BtcPolicy.Exhibits.VariantReceipt
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire)
open BtcPolicy.Exhibits.Ingress (es0)
open BtcPolicy.Exhibits.EndToEnd (honest)
open BtcPolicy.Exhibits.LadderRelease (row2)
open BtcPolicy.Exhibits.RungAssembly (rcfg runE runH rung_sent_execution hash_mismatch_execution)
open BtcPolicy.Federation (Fed)

/-! ### The store test with the user-signature hash

Research task `bps-keml.2`: the user-signature hash carried with a partial from the sender's retained variant to the
receiver's store (`VariantReceipt`), on the federation runs of `Exhibits.RungAssembly`. Each run's federation trace is
labelled by `VariantReceipt.lift`, which is a labelled execution (`VariantReceipt.of_fed`); the receiver's keys are
the ladder's, `[1, 2, 3]`. On `runE`, where both nodes retain `r1` under the hash 11, node 2's `r1` partial is stored
at node 1 as before; on `runH`, where node 1 retains `r1` under 21, it is refused, while `RungIngress.held` keeps it. -/

/-- The federation trace of a run of the rung-assembly layer. -/
def fedOf (T : RungAssembly.Trace) : Federation.Trace := Sweep.fedTrace (RungAssembly.sweepTrace T)

/-- The receiver's configured keys: the ladder's. -/
def keys : List Nat := [1, 2, 3]

theorem keys_eq : rcfg.lc.pre.sweep.keys = keys := rfl

/-- `Exhibits.RungAssembly.runE`'s federation run, labelled. -/
def TE : VariantReceipt.LTrace := VariantReceipt.lift Kernel.current (fedOf (runE 27).1)
def fE : Fed := (runE 27).2.sw.fed

theorem labelled_E : VariantReceipt.Execution Kernel.current honest TE fE :=
  VariantReceipt.of_fed (Sweep.fed_execution (LadderRelease.to_sweep (RungAssembly.to_ladder rung_sent_execution)))

/-- `Exhibits.RungAssembly.runH`'s federation run, labelled. -/
def TH : VariantReceipt.LTrace := VariantReceipt.lift Kernel.current (fedOf runH.1)
def fH : Fed := runH.2.sw.fed

theorem labelled_H : VariantReceipt.Execution Kernel.current honest TH fH :=
  VariantReceipt.of_fed
    (Sweep.fed_execution (LadderRelease.to_sweep (RungAssembly.to_ladder hash_mismatch_execution)))

/-- Node 2's partial on `r1`, as a signature. -/
def sig2 : Authority.Sig := Authority.sig (row2 Exhibits.Ladder.r1)

/-- At node 1, for its Escape-role resident under the Escape's commitment: the quorum on rung 1 and the finalization
at its latch, over the records `R`. -/
def finalNode1 (f : Fed) (R : List Authority.Sig) : Option (Bool × Option Nat) :=
  (RungAssembly.escapeAt (f.worlds 1).node es0.id).map fun c =>
    (Ladder.quorumAt keys (f.worlds 1).node.t c.ladder R 1,
      Ladder.finalize keys (f.worlds 1).node.t c.ladder R c.track.latch)

/-- **Matching material is stored.** On `runE`, node 1's possession under the store that compares the hash has node
2's `r1` partial, rung 1 has its quorum there, and the finalization at node 1's latch is rung 1, as it is over
`RungIngress.held`: a useful ladder still reaches its quorum. -/
@[req "DUR-28"]
theorem matching_held :
    sig2 ∈ VariantReceipt.held keys 1 TE fE ∧
      finalNode1 fE (VariantReceipt.held keys 1 TE fE) = some (true, some 1) ∧
      finalNode1 fE (RungIngress.held 1 (fedOf (runE 27).1) fE) = some (true, some 1) := by
  decide +kernel

/-- **A mismatched hash is refused** (`NCH-24`: "the rung is found by txid; the user-signature hash matches; the input
and signer are in range"). On `runH`, node 2's `r1` partial is in node 1's `RungIngress.held`, as
`Exhibits.RungAssembly.hash_mismatch_sent` shows the old store took it, and rung 1 has its quorum there; it is not in
node 1's possession under the store that compares the hash, and rung 1 has no quorum there. Every envelope of that
partial carries node 2's hash 11, node 2 is not extracted, and node 1's store test refuses the partial under the label
11, at the end and at the delivery step itself, which carried that label: no admissible label stores it. The partial
is still in the inventory: the earlier exposure survives the failed store. -/
@[req "NCH-24"]
theorem mismatch_refused :
    sig2 ∈ RungIngress.held 1 (fedOf runH.1) fH ∧ sig2 ∉ VariantReceipt.held keys 1 TH fH ∧
      (finalNode1 fH (VariantReceipt.held keys 1 TH fH)).map (·.1) = some false ∧
      finalNode1 fH (RungIngress.held 1 (fedOf runH.1) fH) = some (true, some 1) ∧
      ((VariantReceipt.envelopes Kernel.current (fedOf runH.1)).filter (·.1 == row2 Exhibits.Ladder.r1)).map (·.2) =
        [some 11] ∧
      2 ∉ fH.extracted ∧
      VariantReceipt.storable keys (fH.worlds 1).node (row2 Exhibits.Ladder.r1).msg 0 2 es0.id (some 11) = false ∧
      TH.any (fun a => a.2.1 == .deliverPartial 1 envFire (row2 Exhibits.Ladder.r1) && a.2.2 == some 11 &&
        !VariantReceipt.storable keys (a.1.worlds 1).node (row2 Exhibits.Ladder.r1).msg 0 2 es0.id (some 11)) = true ∧
      row2 Exhibits.Ladder.r1 ∈ fH.parts := by
  decide +kernel

/-- **A signer outside the keys is refused.** At node 1's state at the end of `runE`, the store test takes node 2's
`r1` partial under the hash 11 and refuses the same partial signed by 4, a signer outside the keys `[1, 2, 3]`, which
`RungIngress.storable` takes: it never tested the signer's range. -/
@[req "NCH-24"]
theorem wrong_signer_refused :
    VariantReceipt.storable keys (fE.worlds 1).node (sighash Exhibits.Ladder.r1 0) 0 2 es0.id (some 11) = true ∧
      VariantReceipt.storable keys (fE.worlds 1).node (sighash Exhibits.Ladder.r1 0) 0 4 es0.id (some 11) = false ∧
      RungIngress.storable (fE.worlds 1).node (sighash Exhibits.Ladder.r1 0) 0 es0.id = true := by
  decide +kernel

/-- **An input out of range is refused.** `r1` has one input; at node 1's state at the end of `runE`, a partial on
input 1 is refused, by `RungIngress.storable` too: the input's range was already tested there. -/
@[req "NCH-24"]
theorem input_out_of_range_refused :
    Exhibits.Ladder.r1.inputs.length = 1 ∧
      VariantReceipt.storable keys (fE.worlds 1).node (sighash Exhibits.Ladder.r1 1) 1 2 es0.id (some 11) = false ∧
      RungIngress.storable (fE.worlds 1).node (sighash Exhibits.Ladder.r1 1) 1 es0.id = false := by
  decide +kernel

/-- A second delivery of node 2's `r1` partial to node 1, after `runE`, with the label of its envelope. -/
def sD : Federation.Step := .deliverPartial 1 envFire (row2 Exhibits.Ladder.r1)
def TD : VariantReceipt.LTrace := (fE, sD, some 11) :: TE
def fD : Fed := Federation.apply Kernel.current fE sD

/-- **A duplicate leaves possession unchanged** (`NCH-25`: "A duplicate is an idempotent `ACCEPTED` and never displaces
the first."). The second delivery is admitted with an admissible label, node 1's possession under this store is the
same list after it, and the finalization is still rung 1; `RungIngress.held` lists the partial a second time. -/
@[req "NCH-25"]
theorem duplicate_unchanged :
    Federation.admits honest fE sD = true ∧
      VariantReceipt.labelOk Kernel.current (VariantReceipt.forget TE) fE sD (some 11) = true ∧
      VariantReceipt.held keys 1 TD fD = VariantReceipt.held keys 1 TE fE ∧
      finalNode1 fD (VariantReceipt.held keys 1 TD fD) = some (true, some 1) ∧
      (RungIngress.held 1 (VariantReceipt.forget TD) fD).length =
        (RungIngress.held 1 (VariantReceipt.forget TE) fE).length + 1 := by
  decide +kernel

theorem duplicate_execution : VariantReceipt.Execution Kernel.current honest TD fD :=
  .next sD (some 11) duplicate_unchanged.1 duplicate_unchanged.2.1 labelled_E

end BtcPolicy.Exhibits.VariantReceipt

namespace BtcPolicy.Exhibits.ClassAssembly
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh assemble send ordinarySteps ordinaryAll v envHeld)
open BtcPolicy.Exhibits.Clawback (cl0 envCl)
open BtcPolicy.Exhibits.CommonRun (integ inst pc)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (vm)
open BtcPolicy.Exhibits.RungIngress (dsched)
open BtcPolicy.Exhibits.LadderRelease (row2)
open BtcPolicy.Exhibits.RungAssembly (rcfg more esched hsched st0R)
open BtcPolicy.Exhibits.Assembly (vGone clRun frozenRun vConflict wit core)

/-! ### Each class's check and the finalization on the ladder-bearing run

Research task `bps-keml.3`: the class checks of `BtcPolicy.Assembly` and the ladder's finalization on one run of the
rung-assembly layer, over the variant-bound store (`ClassAssembly`). Each schedule's labels are computed as
`VariantReceipt.lift` computes them (`ClassAssembly.labelFor`). The rung runs are `Exhibits.RungAssembly`'s, at its
configuration; the Hot and claw-back runs are `Exhibits.Assembly`'s, at the configuration whose class check is
`Exhibits.Assembly.acfgR`'s. Every check below is decided on the run, never assumed. -/

/-- The trace and state of the classed layer after the first `n` steps of a schedule from `Exhibits.RungAssembly`'s
start. -/
def runL (ss : List RungAssembly.Step) (n : Nat) : BtcPolicy.ClassAssembly.LTrace × RungAssembly.State :=
  BtcPolicy.ClassAssembly.record Kernel.current [] st0R (ss.take n)

/-- **The useful rung run stays reachable** (`DUR-28`, `DUR-29`). `Exhibits.RungAssembly.esched` is a legal run of the
classed layer: node 2's ladder pass at step 22 lists `r1`'s release; at step 25 node 1's finalization over the
variant-bound possession is rung 1, where only `r1` has the quorum; the assembly of rung 1 is admitted and one of
rung 2 refused; at the end node 1 has assembled and sent `r1` alone. -/
@[req "DUR-29"]
theorem rung_run_classed :
    BtcPolicy.ClassAssembly.legal rcfg Kernel.current honest [] st0R esched = true ∧ esched.length = 27 ∧
      RungRelease.listed ilc (runL esched 22).2.sw (BtcPolicy.ClassAssembly.sweepT (runL esched 22).1) 2 =
        [(es0.id, { latch := 1, floor := 2 }, [1])] ∧
      (RungAssembly.escapeAt ((runL esched 25).2.sw.fed.worlds 1).node es0.id).map (fun c =>
        (BtcPolicy.ClassAssembly.finalAt rcfg (runL esched 25).2 (runL esched 25).1 1 c,
          (List.range 3).map fun k => Ladder.quorumAt [1, 2, 3] 2 c.ladder
            (BtcPolicy.ClassAssembly.heldAt rcfg (runL esched 25).2 (runL esched 25).1 1) k)) =
        some (some 1, [false, true, false]) ∧
      BtcPolicy.ClassAssembly.admits rcfg Kernel.current honest (runL esched 25).2 (runL esched 25).1
        (.assemble 1 es0.id 1) = true ∧
      BtcPolicy.ClassAssembly.admits rcfg Kernel.current honest (runL esched 25).2 (runL esched 25).1
        (.assemble 1 es0.id 2) = false ∧
      (runL esched 27).2.assembled = [(1, es0.id, Exhibits.Ladder.r1.id)] ∧
      (runL esched 27).2.sent = [(1, es0.id, Exhibits.Ladder.r1.id)] := by
  decide +kernel

theorem rung_run_execution :
    BtcPolicy.ClassAssembly.Execution rcfg Kernel.current honest (runL esched 27).1 (runL esched 27).2 := by
  have hx := BtcPolicy.ClassAssembly.execution_of_legal (.init st0R ⟨(st0_fresh (inst vm)).1, rfl, rfl⟩)
    rung_run_classed.1
  have hl : esched.take 27 = esched := List.take_of_length_le (Nat.le_of_eq rung_run_classed.2.1)
  simpa [runL, hl] using hx

/-- **A partial the hash-comparing store refused is not assembled on.** On `Exhibits.RungAssembly.hsched`, where node 1
retains `r1` under a hash other than node 2's, the first 25 steps are a legal run of the classed layer; there node 1
has no finalization over the variant-bound possession, and its assembly of rung 1 is refused, while the
rung-assembly layer, counting `RungIngress.held`, admits it. -/
@[req "NCH-24"]
theorem mismatch_unassembled :
    BtcPolicy.ClassAssembly.legal rcfg Kernel.current honest [] st0R (hsched.take 25) = true ∧
      (RungAssembly.escapeAt ((runL hsched 25).2.sw.fed.worlds 1).node es0.id).map
        (BtcPolicy.ClassAssembly.finalAt rcfg (runL hsched 25).2 (runL hsched 25).1 1) = some none ∧
      BtcPolicy.ClassAssembly.admits rcfg Kernel.current honest (runL hsched 25).2 (runL hsched 25).1
        (.assemble 1 es0.id 1) = false ∧
      RungAssembly.admits rcfg Kernel.current honest (runL hsched 25).2
        (BtcPolicy.ClassAssembly.forget (runL hsched 25).1) (.assemble 1 es0.id 1) = true := by
  decide +kernel

/-- Node 1's assembly of the Escape's commitment on the base path. -/
def pa : RungAssembly.Step := .base (.fed (.process 1 envFire (.packageAccepted es0.id)))

/-- `runD` and `Exhibits.RungAssembly.more`, then node 2's base partial delivered to node 1, node 1's assembly on the
base path and its kernel send. -/
def bsched : List RungAssembly.Step :=
  (dsched ++ more).map .base ++ [.base (.fed (.deliverPartial 1 envFire (row2 es0.tx))), pa,
    .base (.fed (.process 1 envFire (.send es0.id)))]

/-- **The base path cannot bypass a higher rung's finalization** (`DUR-28`). The rung-assembly layer admits the whole
of `bsched`: once node 2's base partial reaches node 1, node 1 assembles the Escape on the base path and its kernel
send submits the base, although rung 1 is the finalization. In the classed layer the first 26 steps are a legal run;
there the base and `r1` both have the quorum over the variant-bound possession, rung 0's `Assembly.rungCheck` passes
at node 1's read, and the finalization at the latch is rung 1, so the base-path assembly is refused. -/
@[req "DUR-28"]
theorem base_cannot_bypass :
    RungAssembly.legal rcfg Kernel.current honest [] st0R bsched = true ∧ bsched.length = 28 ∧
      Sweep.submits Kernel.current (RungAssembly.record Kernel.current [] st0R (bsched.take 27)).2.sw
        (.fed (.process 1 envFire (.send es0.id))) = [es0.tx.id] ∧
      BtcPolicy.ClassAssembly.legal rcfg Kernel.current honest [] st0R (bsched.take 26) = true ∧
      (RungAssembly.escapeAt ((runL bsched 26).2.sw.fed.worlds 1).node es0.id).map (fun c =>
        (BtcPolicy.ClassAssembly.finalAt rcfg (runL bsched 26).2 (runL bsched 26).1 1 c,
          (List.range 3).map (fun k => Ladder.quorumAt [1, 2, 3] 2 c.ladder
            (BtcPolicy.ClassAssembly.heldAt rcfg (runL bsched 26).2 (runL bsched 26).1 1) k),
          ((runL bsched 26).2.sw.obs 1).map fun b =>
            BtcPolicy.Assembly.rungCheck rcfg.asm (BtcPolicy.ClassAssembly.readAt (runL bsched 26).2
              (runL bsched 26).1 1 c) b c
              (BtcPolicy.ClassAssembly.heldAt rcfg (runL bsched 26).2 (runL bsched 26).1 1) 0)) =
        some (some 1, [true, true, false], some true) ∧
      BtcPolicy.ClassAssembly.admits rcfg Kernel.current honest (runL bsched 26).2 (runL bsched 26).1 pa = false := by
  decide +kernel

/-! #### The class checks on the Hot and claw-back runs -/

/-- `Exhibits.Assembly.acfgR`'s class check at the ladder's configuration over `Exhibits.CommonRun.pc`. -/
def lcA : Ladder.Cfg := { pre := pc, quota := 600, anchor := Cursor.current }
def acL (rej : List Nat) : RungAssembly.Cfg := { lc := lcA, witnesses := wit, test := core rej }

theorem acL_asm (rej : List Nat) : (acL rej).asm = Exhibits.Assembly.acfgR rej := rfl

/-- A composed schedule's sweep steps as base steps of the layer. -/
def liftR (xs : List Recovery.Step) : List RungAssembly.Step := xs.filterMap fun
  | .base s => some (.base s)
  | _ => none

def stA : RungAssembly.State := { sw := (st0 (inst v)).sw }
def runA (xs : List Recovery.Step) : BtcPolicy.ClassAssembly.LTrace × RungAssembly.State :=
  BtcPolicy.ClassAssembly.record Kernel.current [] stA (liftR xs)
def okA (rej : List Nat) (xs : List Recovery.Step) : Bool :=
  BtcPolicy.ClassAssembly.legal (acL rej) Kernel.current honest [] stA (liftR xs)
/-- The classed layer's admission of sweep step `s` after `xs`. -/
def newA (rej : List Nat) (xs : List Recovery.Step) (s : Sweep.Step) : Bool :=
  BtcPolicy.ClassAssembly.admits (acL rej) Kernel.current honest (runA xs).2 (runA xs).1 (.base s)
/-- The rung-assembly layer's admission of sweep step `s` after `xs`. -/
def oldA (rej : List Nat) (xs : List Recovery.Step) (s : Sweep.Step) : Bool :=
  RungAssembly.admits (acL rej) Kernel.current honest (runA xs).2 (BtcPolicy.ClassAssembly.forget (runA xs).1) (.base s)

/-- **A Hot spend over a missing prevout is refused on the ladder-bearing run** (`SPN-39`). On
`Exhibits.Assembly.hot_old_broader`'s history, the coin gone and node 1 reading that, the history is a legal run of
the classed layer; the rung-assembly layer's base path, whose check sits on the Escape role alone, admits node 1's
assembly of the Hot spend, and the classed layer refuses it. The ordinary history, which assembles and sends the
Hot spend over the coin, is a legal run of the classed layer. -/
@[req "SPN-39"]
theorem hot_refused :
    let xs := integ v (ordinarySteps.take 9 ++ [.chain vGone, .observe 1 vGone])
    okA [] xs = true ∧ oldA [] xs (assemble 1 sp0.id envHeld) = true ∧
      newA [] xs (assemble 1 sp0.id envHeld) = false ∧ okA [] (integ v ordinaryAll) = true := by
  decide +kernel

/-- **A claw-back whose package the backend rejects is refused** (`SPN-51`, `WTC-26`). The claw-back's run is a legal
run of the classed layer under the accepting verdict. Under a verdict that rejects the claw-back's package for
another reason, its history before the assembly is a legal run; there the rung-assembly layer admits the assembly,
and the classed layer refuses it, while it admits the same assembly under the accepting verdict. -/
@[req "SPN-51"]
theorem clawback_refused :
    let xs := integ v (clRun.take 6)
    okA [] (integ v clRun) = true ∧ okA [cl0.tx.id] xs = true ∧
      oldA [cl0.tx.id] xs (assemble 1 cl0.id envCl) = true ∧
      newA [cl0.tx.id] xs (assemble 1 cl0.id envCl) = false ∧ newA [] xs (assemble 1 cl0.id envCl) = true := by
  decide +kernel

/-- **A state change after assembly removes authorization to send** (`DUR-11`). `Exhibits.Assembly.frozenRun` is a
legal run of the classed layer: the Hot spend is assembled, the holder decision freezes it, and the kernel send,
re-authorized at its own state, submits nothing. -/
@[req "DUR-11"]
theorem frozen_classed :
    okA [] (integ v frozenRun) = true ∧ Sweep.submits Kernel.current (runA (integ v frozenRun)).2.sw
      (send 1 sp0.id envHeld) = [] := by
  decide +kernel

/-- **The backend moves after assembly** (`DUR-29`). After the ordinary assembly an outsider's transaction becomes
resident over the coin and node 1 reads it: the history is a legal run of the classed layer, its send is admitted
and submits the Hot spend, since the send reads no backend, and an assembly at that read is refused. -/
@[req "DUR-29"]
theorem backend_moves_classed :
    let xs := integ v (ordinarySteps ++ [.chain vConflict, .observe 1 vConflict])
    okA [] xs = true ∧ newA [] xs (send 1 sp0.id envHeld) = true ∧
      Sweep.submits Kernel.current (runA xs).2.sw (send 1 sp0.id envHeld) = [sp0.tx.id] ∧
      newA [] xs (assemble 1 sp0.id envHeld) = false := by
  decide +kernel

end BtcPolicy.Exhibits.ClassAssembly
namespace BtcPolicy.Exhibits.AcceptedSet
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (envFire envLate)
open BtcPolicy.Exhibits.Ingress (ctx0 sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungIngress (lreq q1 q3 evOf pairOf runD dsched)
open BtcPolicy.Exhibits.RungAssembly (rcfg esched st0R)
open BtcPolicy.Exhibits.ClassAssembly (runL)

/-! ### Every accepted rung in the vault-authorized set

Research task `bps-keml.5`: `Sweep.authorized` collects the txid of every rung a registered candidate retains
(`BtcPolicy.AcceptedSet`). The runs are the rung runs of `Exhibits.RungIngress` and `Exhibits.ClassAssembly`, whose
acceptances are `RungIngress.check`'s; their ladder `Exhibits.RungIngress.lreq` raises the fee by 4 a rung, so
they are not runs of `LadderShape.check`. Every set below is the one the run computes at the node, never supplied:
`Sweep.authorizedAt` beside the earlier set `AcceptedSet.authorizedPreAt`. -/

/-- The refusal a resident read returns, if any. -/
def refusal : Except Package.Reason (List Coverage.Outpoint) → Option Package.Reason
  | .error e => some e
  | .ok _ => none

/-- `Exhibits.ClassAssembly.rung_run_classed`'s run at its end: node 1 has assembled and sent `r1`. -/
def preRun : BtcPolicy.ClassAssembly.LTrace × RungAssembly.State := runL esched 27

/-- The vault at a median of 200 with `r1` resident in the mempool. -/
def resident : Sweep.Backend :=
  { Exhibits.CommonRun.inst Exhibits.RungRelease.vm2 with
    mempool := [(Exhibits.Ladder.r1.id, Exhibits.Ladder.r1.inputs)] }

/-- The truth moves to `resident`; node 2 reads it and takes a ladder pass, which latches `r2`; node 2's `r2`
partial reaches node 1, which reads `resident`. Each pass carries the value computed at its own state. -/
def tail : List Sweep.Step :=
  LadderRelease.fill rcfg.lc Kernel.current (BtcPolicy.ClassAssembly.sweepT preRun.1) preRun.2.sw
    [.chain resident, .observe 2 resident, .fed (.process 2 envFire .ladderPass),
     .fed (.deliverPartial 1 envFire (Exhibits.LadderRelease.row2 Exhibits.Ladder.r2)), .observe 1 resident]

/-- The tail, then node 1's assembly of rung 2 and its send. -/
def upSteps : List RungAssembly.Step := tail.map .base ++ [.assemble 1 es0.id 2, .send 1 envFire es0.id 2]

/-- The run after the tail, before the assembly. -/
def atRead : BtcPolicy.ClassAssembly.LTrace × RungAssembly.State :=
  BtcPolicy.ClassAssembly.record Kernel.current preRun.1 preRun.2 (tail.map .base)

/-- The run after the assembly and the send. -/
def upRun : BtcPolicy.ClassAssembly.LTrace × RungAssembly.State :=
  BtcPolicy.ClassAssembly.record Kernel.current preRun.1 preRun.2 upSteps

/-- Node `i`'s set, and the earlier set, after the tail. -/
def setAt (i : Nat) : List Nat := Sweep.authorizedAt atRead.2.sw (BtcPolicy.ClassAssembly.sweepT atRead.1) i
def preAt (i : Nat) : List Nat :=
  BtcPolicy.AcceptedSet.authorizedPreAt atRead.2.sw (BtcPolicy.ClassAssembly.sweepT atRead.1) i

/-- Node 1's rung-2 assembly check after the tail, at its own read and at that read with set `A` in place of
its own. -/
def upCheck (A : Option (List Nat)) : Option Bool :=
  (RungAssembly.escapeAt (atRead.2.sw.fed.worlds 1).node es0.id).map fun c =>
    let rd := BtcPolicy.ClassAssembly.readAt atRead.2 atRead.1 1 c
    Assembly.rungCheck rcfg.asm (match A with | none => rd | some A => { rd with A := A }) resident c
      (BtcPolicy.ClassAssembly.heldAt rcfg atRead.2 atRead.1 1) 2

/-- The resident rung 2's selection replaces at node 1 after the tail. -/
def upReplaces : Option (Option Nat) :=
  (RungAssembly.escapeAt (atRead.2.sw.fed.worlds 1).node es0.id).map fun c =>
    let l := Ladder.txs (BtcPolicy.ClassAssembly.readAt atRead.2 atRead.1 1 c) c
    Ladder.replacesOf l (PreRelease.membership resident l) 2

/-- **A higher rung replaces a resident lower rung** (`WTC-25`, `SPN-33`, `DUR-29`). After node 1 has sent `r1`
and `r1` is resident, node 2's ladder pass at a median of 200 releases `r2`, its partial reaches node 1, and node
1's assembly of rung 2 is admitted on the classed layer: the schedule is legal. That assembly replaces `r1`
(`Ladder.replacesOf`), and `r1`'s txid is in node 1's set because node 1 registered it at its acceptance. With
the earlier set in place of node 1's own, the same check fails, the resident read refusing `r1` as a resident
the node never authorized. Node 1 then sends `r2`: at the end it has assembled and sent `r1` and then `r2`. -/
@[req "WTC-25"]
theorem lower_to_higher :
    BtcPolicy.ClassAssembly.legal rcfg Kernel.current honest preRun.1 preRun.2 upSteps = true ∧
      (setAt 1).contains Exhibits.Ladder.r1.id = true ∧ (preAt 1).contains Exhibits.Ladder.r1.id = false ∧
      upReplaces = some (some Exhibits.Ladder.r1.id) ∧
      upCheck none = some true ∧ upCheck (some (preAt 1)) = some false ∧
      refusal (Package.residentRead Package.current resident.mempool (preAt 1)
        (Sweep.candidateOf Exhibits.Ladder.r2) (some Exhibits.Ladder.r1.id)) =
        some (.residentNotAuthorized Exhibits.Ladder.r1.id) ∧
      BtcPolicy.ClassAssembly.admits rcfg Kernel.current honest atRead.2 atRead.1 (.assemble 1 es0.id 2) = true ∧
      upRun.2.assembled = [(1, es0.id, Exhibits.Ladder.r2.id), (1, es0.id, Exhibits.Ladder.r1.id)] ∧
      upRun.2.sent = [(1, es0.id, Exhibits.Ladder.r2.id), (1, es0.id, Exhibits.Ladder.r1.id)] := by
  decide +kernel

/-- The run is a reachable execution of the classed layer. -/
theorem lower_to_higher_execution :
    BtcPolicy.ClassAssembly.Execution rcfg Kernel.current honest upRun.1 upRun.2 :=
  BtcPolicy.ClassAssembly.execution_of_legal Exhibits.ClassAssembly.rung_run_execution lower_to_higher.1

/-- **A resident no node accepted, and the order of the inputs** (`WTC-25`). At node 1's own set after the tail,
the resident read refuses a resident the node never registered (txid 999, spending `r1`'s input) as
`residentNotAuthorized`, while it admits `r1`. Over a resident `r1` read as spending two outpoints, a candidate
spending the same two in the other order is refused as `outpointsDiffer`, and one spending them in the same order
is admitted: the set does not override `WTC-25`'s "exactly the same ordered outpoints". Node 3 never registered
the ladder, so its set lacks `r1` and its read refuses `r1` as a replacement target. -/
@[req "WTC-25"]
theorem replacement_refused :
    refusal (Package.residentRead Package.current [(999, Exhibits.Ladder.r1.inputs)] (setAt 1)
      (Sweep.candidateOf Exhibits.Ladder.r2) (some 999)) = some (.residentNotAuthorized 999) ∧
      refusal (Package.residentRead Package.current resident.mempool (setAt 1)
        (Sweep.candidateOf Exhibits.Ladder.r2) (some Exhibits.Ladder.r1.id)) = none ∧
      refusal (Package.residentRead .overResident [(Exhibits.Ladder.r1.id, [5, 6])] (setAt 1)
        { txid := Exhibits.Ladder.r2.id, inputs := [6, 5] } (some Exhibits.Ladder.r1.id)) = some .outpointsDiffer ∧
      refusal (Package.residentRead .overResident [(Exhibits.Ladder.r1.id, [5, 6])] (setAt 1)
        { txid := Exhibits.Ladder.r2.id, inputs := [5, 6] } (some Exhibits.Ladder.r1.id)) = none ∧
      (setAt 3).contains Exhibits.Ladder.r1.id = false ∧
      refusal (Package.residentRead Package.current resident.mempool (setAt 3)
        (Sweep.candidateOf Exhibits.Ladder.r2) (some Exhibits.Ladder.r1.id)) =
        some (.residentNotAuthorized Exhibits.Ladder.r1.id) := by
  decide +kernel

/-- `Exhibits.RungIngress.runD`, then node 1's pruning past the commitment's expiry. -/
def prSteps : List Sweep.Step := [.fed (.process 1 envLate .prune)]

def prRun : Sweep.Trace × Sweep.State := Sweep.record Kernel.current runD.1 runD.2 prSteps

/-- **A pruned candidate's rungs stay recognized** (`SPN-33`, `WTC-18`). On `runD` node 1 retains the Escape with
`r1` and `r2`; its pruning at 201, past the expiry, leaves its registry empty, and its set still holds the base,
`r1` and `r2`, read off the state its pruning step was taken in. The earlier set holds the base alone. -/
@[req "SPN-33"]
theorem pruned_recognized :
    LadderRelease.legal ilc Kernel.current honest runD.1 runD.2 prSteps = true ∧
      (prRun.2.fed.worlds 1).node.cands = [] ∧
      [es0.tx.id, Exhibits.Ladder.r1.id, Exhibits.Ladder.r2.id].map
        (fun x => ((Sweep.authorizedAt prRun.2 prRun.1 1).contains x,
          (BtcPolicy.AcceptedSet.authorizedPreAt prRun.2 prRun.1 1).contains x)) =
        [(true, true), (true, false), (true, false)] := by
  decide +kernel

theorem pruned_execution : LadderRelease.Execution ilc Kernel.current honest prRun.1 prRun.2 :=
  LadderRelease.execution_of_legal Exhibits.RungIngress.rung_held_execution pruned_recognized.1

/-- `lreq` with a third rung `r3` (`Exhibits.RungIngress.q3`). -/
def r3 : Tx := Ingress.tx ctx0 Exhibits.Ladder.m3

/-- After `runD`: node 2 takes `q3`'s checked pair, a repeat whose Escape proposes `r3` above the resident's two
rungs; node 3, which holds nothing, takes `q1`'s, whose ladder is `r1` alone. -/
def rpSteps : List Sweep.Step :=
  [.fed (.process 2 envFire (evOf (sp0, RungIngress.withLadder ctx0 q3 es0))),
   .fed (.process 3 envFire (evOf (sp0, RungIngress.withLadder ctx0 q1 es0)))]

def rpRun : Sweep.Trace × Sweep.State := Sweep.record Kernel.current runD.1 runD.2 rpSteps

/-- **A refused repeat adds no rung, and each node holds its own ladder** (`SPN-33`, `SPN-32`). The schedule is
legal and every acceptance on it is a checked request's (`lreq`, `q3`, `q1`). Node 2 refuses `q3`'s repeat
(`Kernel.pairAdmits`: the rung txids differ) and its registry is unchanged; on the base, the spend, `r1`, `r2`
and `r3`, membership of node 2's set is what it was after `runD`, and `r3` is in no node's set. Node 3's first
acceptance is the ladder with `r1` alone (a ladder with a rung dropped before acceptance): its set holds `r1`
and not `r2`, while nodes 1 and 2 hold both. -/
@[req "SPN-33"]
theorem repeat_adds_nothing :
    LadderRelease.legal ilc Kernel.current honest runD.1 runD.2 rpSteps = true ∧
      (Ingress.acceptPairs (Sweep.fedTrace rpRun.1)).all
        (fun p => [lreq, q3, q1].any fun q => RungIngress.check ctx0 true q == .accepted p.1 p.2) = true ∧
      Ingress.clawCands (Sweep.fedTrace rpRun.1) = [] ∧
      (rpRun.2.fed.worlds 2).node.cands = (runD.2.fed.worlds 2).node.cands ∧
      [es0.tx.id, sp0.tx.id, Exhibits.Ladder.r1.id, Exhibits.Ladder.r2.id, r3.id].map
        (fun x => ((Sweep.authorizedAt rpRun.2 rpRun.1 2).contains x,
          (Sweep.authorizedAt runD.2 runD.1 2).contains x)) =
        [(true, true), (true, true), (true, true), (true, true), (false, false)] ∧
      [Exhibits.Ladder.r1.id, Exhibits.Ladder.r2.id, r3.id].map
        (fun x => [1, 2, 3].map fun i => (Sweep.authorizedAt rpRun.2 rpRun.1 i).contains x) =
        [[true, true, true], [true, true, false], [false, false, false]] := by
  decide +kernel

theorem repeat_execution : LadderRelease.Execution ilc Kernel.current honest rpRun.1 rpRun.2 :=
  LadderRelease.execution_of_legal Exhibits.RungIngress.rung_held_execution repeat_adds_nothing.1

theorem repeat_checked : RungIngress.CheckedTrace ctx0 (Sweep.fedTrace rpRun.1) :=
  RungIngress.checkedTrace_of ctx0 _ [lreq, q3, q1] [] repeat_adds_nothing.2.1
    (by rw [repeat_adds_nothing.2.2.1]; rfl)

end BtcPolicy.Exhibits.AcceptedSet
