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

namespace BtcPolicy.Exhibits.RungRelease
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Kernel.RegistrationCases (envFire env0)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest v vLarge st0 st0_fresh part)
open BtcPolicy.Exhibits.CommonRun (inst onBook readFirst)
open BtcPolicy.Exhibits.Integrated (ilc)

/-! ### Rung releases on the composed run

Research task `bps-9oab.8`, its fourth part: the kernel's ladder pass on the composed sweep run, with the
release it lists computed (`RungRelease.releaseOk`). Nodes 1 and 2 take the coerced request of
`Exhibits.EndToEnd.toRelease`, its Escape `es0` registered with the two rungs `Exhibits.Ladder.R1` and
`Exhibits.Ladder.R2` above its base, arm, read the vault and fire. Node 1 then takes a ladder pass at each of
three instants: the vault with a median of 100, the vault with a median of 200, and the large coin with a
median of 200; each fire pass and ladder pass carries the value computed at its own state and history
(`RungRelease.fill`). The Escape is registered directly at `Kernel.accept`: checked ingress registers no rung
yet (`Ingress.resident_no_rungs`). -/







/-- The trace and state after the first `n` steps. -/
def runR (n : Nat) : Sweep.Trace × Sweep.State := Sweep.record Kernel.current [] (st0 (inst vm)).sw (sched.take n)


/-- The rows of the run's partial inventory under `es0`'s commitment. -/
def rowsR : List Exp := (runR 19).2.fed.parts.filter (·.cid == es0.id)

/-- **A rung release on the composed run, with changing observations.** The schedule is a legal run of the
ladder-aware refinement (`RungRelease.legal`), so a `RungRelease.Execution`. Its ladder passes are steps 10,
14 and 18. At step 10, reading the vault at a median of 100, node 1's computed release latches `r1` and
releases `r1`, the fire pass having released the base and set the floor to 1; at step 14, at a median of 200, it
latches `r2` and releases `r2` alone, the floor past the earlier prefix. The run's inventory under the Escape's commitment holds the two base
partials of the fire passes and node 1's partials on `r1` and `r2`, none hot, and node 1's Escape ends at
latch 2 and floor 3. The base's refinement does not admit this run (`PreRelease.checks`): its ladder passes
list a release. -/
@[req "DUR-27"]
theorem rung_on_run :
    RungRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw sched = true ∧ sched.length = 19 ∧
      RungRelease.listed ilc (runR 10).2 (runR 10).1 1 = [(es0.id, { latch := 1, floor := 2 }, [1])] ∧
      RungRelease.listed ilc (runR 14).2 (runR 14).1 1 = [(es0.id, { latch := 2, floor := 3 }, [2])] ∧
      rowsR = [part es0 1, part es0 2, rrow Exhibits.Ladder.r1, rrow Exhibits.Ladder.r2] ∧
      (((runR 19).2.fed.worlds 1).node.cands.filter (·.isEscape)).map (·.track) =
        [{ latch := 2, floor := 3 }] ∧
      PreRelease.checks ilc.pre (runR 19).1 = false := by
  decide +kernel

/-- The run is a reachable ladder-aware execution, so `RungRelease.inventory_provenance` covers its rung rows. -/
theorem rung_run_execution :
    RungRelease.Execution ilc Kernel.current honest (runR 19).1 (runR 19).2 := by
  have h := rung_on_run.1
  have hx := RungRelease.execution_of_legal (.init _ (st0_fresh (inst vm)).1) h
  have hl : sched.take 19 = sched := List.take_of_length_le (Nat.le_of_eq rung_on_run.2.1)
  simpa [runR, hl] using hx

/-- **A refused rung.** At step 18 node 1 reads the large coin: its own predicate admits no rung of the
Escape's ladder, the computed release lists nothing, and a ladder pass listing `r2` at the latch and floor it
holds is not admitted, while the pass the run takes is. -/
@[req "DUR-27"]
theorem refused_rung_on_run :
    RungRelease.listed ilc (runR 18).2 (runR 18).1 1 = [] ∧
      ((((runR 18).2.fed.worlds 1).node.cands.filter (·.isEscape)).map fun c =>
        match (RungRelease.readAt (runR 18).2 (runR 18).1 1 c).ob with
        | none => []
        | some b => (Ladder.attempt ilc.pre (RungRelease.readAt (runR 18).2 (runR 18).1 1 c) b c
            c.track.latch).adm) = [[false, false, false]] ∧
      RungRelease.admits ilc honest (runR 18).2 (runR 18).1
        (lad 1 [(es0.id, { latch := 2, floor := 3 }, [2])]) = false ∧
      RungRelease.admits ilc honest (runR 18).2 (runR 18).1 (lad 1) = true := by
  decide +kernel

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

/-! ### The fire pass over the whole ladder

Research task `bps-9oab.8`: the fire pass's check over each Escape's whole ladder (`LadderRelease.releaseOk`).
Nodes 1 and 2 take the coerced request with the Escape `Exhibits.RungRelease.esR`, which retains the rungs
`Exhibits.Ladder.R1` and `Exhibits.Ladder.R2` above its base, and arm. Node 2 reads the vault at a median of
100 and takes a ladder pass before its first fire pass: its computed release latches `r1`. A second coin of
450 000 then confirms, and node 2 reads it and fires. At that instant the base still covers the larger vault
and `r1` no longer does: the base's verdict releases rung 0, while the ladder's selection is refused at the
latch (`PreRelease.Stage.latched`). `RungRelease`'s fire pass, which judges the base alone, releases node 2's
base partial there; this refinement withholds it. -/

/-- The vault with a second confirmed coin of 450 000, at a median of 100. -/
def vMid : Backend := { vm with confirmed := (inst vm).confirmed ++ [(9, 450000)] }

/-- The history as written: node 2's ladder pass before its first fire pass, each pass listing nothing until a
refinement's `fill` computes it. -/
def raw : List Sweep.Step :=
  [accR 1, accR 2, .fed (.emit 1 10), .fed (.emit 2 10), .fed (.deliver 1 env0 ⟨2, 10⟩),
   .fed (.deliver 2 env0 ⟨1, 10⟩), .observe 2 (inst vm), lad 2, .chain vMid, .observe 2 vMid, fire 2]

/-- The history with each fire pass carrying the verdict over the whole ladder (`LadderRelease.fill`). -/
def sched : List Sweep.Step := LadderRelease.fill ilc Kernel.current [] (st0 (inst vm)).sw raw

/-- The same history with each fire pass carrying the base's verdict alone (`RungRelease.fill`). -/
def rsched : List Sweep.Step := RungRelease.fill ilc Kernel.current [] (st0 (inst vm)).sw raw

def runF (n : Nat) : Sweep.Trace × Sweep.State := Sweep.record Kernel.current [] (st0 (inst vm)).sw (sched.take n)
def runB (n : Nat) : Sweep.Trace × Sweep.State :=
  Sweep.record Kernel.current [] (st0 (inst vm)).sw (rsched.take n)


/-- **A refused ladder withholds its base.** The schedule is a legal run of this refinement. Node 2's ladder
pass at step 7 latches `r1` and releases the prefix from the base, which queues the base's partial and `r1`'s
(`Kernel.baseEffects`) and marks the base released. At step 10, reading the larger vault, the base is admissible
and `r1` is not: the base's verdict withholds nothing, the ladder's verdict is refused at the latch, and the fire
pass's verdict over the whole ladder withholds the Escape. The run's inventory under the Escape's commitment holds
node 2's base and `r1` partials, both from the ladder pass. On the same history `RungRelease`'s refinement fires
with nothing withheld, and its inventory gains no second base partial, the base being released; that fire pass is
not admitted here. -/
@[req "DUR-21"]
theorem base_withheld_on_run :
    LadderRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw sched = true ∧ sched.length = 11 ∧
      RungRelease.listed ilc (runF 7).2 (runF 7).1 2 = [(es0.id, { latch := 1, floor := 2 }, [0, 1])] ∧
      PreRelease.failing ilc.pre (runF 10).2 (runF 10).1 2 = [] ∧
      LadderRelease.withheldAt ilc (runF 10).2 (runF 10).1 2 = [es0.id] ∧
      ((((runF 10).2.fed.worlds 2).node.cands.filter (·.isEscape)).map fun c =>
        (match (RungRelease.readAt (runF 10).2 (runF 10).1 2 c).ob with
          | none => []
          | some b => (Ladder.attempt ilc.pre (RungRelease.readAt (runF 10).2 (runF 10).1 2 c) b c
              c.track.latch).adm,
         Ladder.verdict ilc.pre (RungRelease.readAt (runF 10).2 (runF 10).1 2 c) c c.track.latch)) =
        [([true, false, false], .fail .latched)] ∧
      (runF 11).2.fed.parts.filter (·.cid == es0.id) = [part es0 2, row2 Exhibits.Ladder.r1] ∧
      RungRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw rsched = true ∧
      (runB 11).2.fed.parts.filter (·.cid == es0.id) = [part es0 2, row2 Exhibits.Ladder.r1] ∧
      LadderRelease.admits ilc honest (runF 10).2 (runF 10).1 (rsched.getD 10 (fire 2)) = false := by
  decide +kernel

/-- The run is a reachable execution of this refinement, so `LadderRelease.inventory_provenance` covers it. -/
theorem base_run_execution :
    LadderRelease.Execution ilc Kernel.current honest (runF 11).1 (runF 11).2 := by
  have h := base_withheld_on_run.1
  have hx := LadderRelease.execution_of_legal (.init _ (st0_fresh (inst vm)).1) h
  have hl : sched.take 11 = sched := List.take_of_length_le (Nat.le_of_eq base_withheld_on_run.2.1)
  simpa [runF, hl] using hx

/-- **The base where the ladder releases.** `Exhibits.RungRelease.rung_on_run`'s schedule, whose fire passes
release both nodes' base partials and whose ladder passes release `r1` and `r2`, is a legal run of this
refinement too: at each of its fire passes the verdict over the whole ladder withholds what the base's does. -/
@[req "DUR-21"]
theorem base_on_run :
    LadderRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw Exhibits.RungRelease.sched = true := by
  decide +kernel

end BtcPolicy.Exhibits.LadderRelease
namespace BtcPolicy.Exhibits.Lifecycle
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envLate)
open BtcPolicy.Exhibits.Ingress (ctx0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh coin v)
open BtcPolicy.Exhibits.LadderShape (g1 g2 spOf esOf)
open BtcPolicy.Exhibits.RungRelease (withMedian lad)

/-! ### A complete rung transaction lifecycle

Research task `bps-keml.6` (`BtcPolicy.Lifecycle`): over the classed run, a rung send needs a live permit from the
same node's assembly of that txid, read at that assembly's observation, with no pass or pruning of the node, no
birth of a record under the commitment at the node and no settlement by the node of a rung of that ladder in between; a kernel send of an Escape is refused, so no Escape is marked broadcast; and the sends of both
paths enter one submission history. The ladder is `Exhibits.LadderShape`'s, so the acceptances are
`LadderShape.check`'s: fees 200, 500 and 683 over a coin of 10000, each rung's maximum vsize 183. -/

/-- The checked request and its pair, the base and the two rungs. -/
def q : RungIngress.Request := BtcPolicy.Exhibits.LadderShape.req [g1, g2]
def spL : Cand := spOf q
def esL : Cand := esOf q
def tB : Tx := esL.tx
def t1 : Tx := Ingress.tx ctx0 g1
def t2 : Tx := Ingress.tx ctx0 g2

/-- One coin of 10000; each of the three transactions pays one output, at its own fee. -/
def fbook : Sweep.Book :=
  { value := fun o => if o == coin then 10000 else if o == tB.id + 1000 then 9800
      else if o == t1.id + 1000 then 9500 else if o == t2.id + 1000 then 9317 else 0,
    outputs := fun tx => [tx + 1000],
    delivered := fun tx => if tx == tB.id then 9800 else if tx == t1.id then 9500
      else if tx == t2.id then 9317 else 0 }

/-- The release floor is 2 sat/vB, so the base (200 over 183) is inadmissible and rung 1 is the cheapest admissible
rung with no median reading; a median of 5 selects rung 2. -/
def fsw : Sweep.Cfg := { Exhibits.PreRelease.scfg with book := fbook }
def fpre : PreRelease.Cfg := { sweep := fsw, legacyLen := fun _ => 62, floor := 2 }
def flc : Ladder.Cfg := { pre := fpre, quota := 600, anchor := Cursor.current }
def fwit (x : Nat) : List Nat := if x == tB.id || x == t1.id || x == t2.id then [476] else []
def fcfg : RungAssembly.Cfg := { lc := flc, witnesses := fwit, test := Exhibits.Assembly.core [] }

/-- The coin confirmed; then `t1` resident at a median of 5; then `t2` confirmed and the coin spent. -/
def fv : Backend := { v with confirmed := [(coin, 10000)] }
def fvRes : Backend := withMedian { fv with sequence := 2, mempool := [(t1.id, t1.inputs)] } 5
def fvConf : Backend :=
  { fv with tip := ⟨6, 106⟩, sequence := 3, confirmed := [], mempool := [], mined := [(t2.id, t2.inputs)] }

def acc (i : Nat) : Sweep.Step := .fed (.process i env0 (.accept 10 true (Wall.sample 200) spL esL))
def row (s : Nat) (g : Tx) : Exp := { msg := sighash g 0, input := 0, signer := s, hot := false, cid := esL.id }

/-- Nodes 1 and 2 accept the checked pair under duress and exchange their relays; each reads `fv` and takes a ladder
pass, which latches rung 1; node 2's partial on `t1` reaches node 1 after node 1's own pass. -/
def raw1 : List Sweep.Step :=
  [acc 1, acc 2, .fed (.emit 1 10), .fed (.emit 2 10), .fed (.deliver 1 env0 ⟨2, 10⟩),
   .fed (.deliver 2 env0 ⟨1, 10⟩), .observe 2 fv, lad 2, .observe 1 fv, lad 1,
   .fed (.deliverPartial 1 envFire (row 2 t1))]

def stL : BtcPolicy.Lifecycle.State := { cs := { sw := (st0 fv).sw } }
def sched1 : List Sweep.Step := LadderRelease.fill flc Kernel.current [] (st0 fv).sw raw1

/-- `raw1`, then node 1's assembly of rung 1 and its send. -/
def steps1 : List RungAssembly.Step := sched1.map .base ++ [.assemble 1 esL.id 1, .send 1 envFire esL.id 1]
def run1 : BtcPolicy.Lifecycle.Trace × BtcPolicy.Lifecycle.State :=
  BtcPolicy.Lifecycle.record Kernel.current [] stL steps1

/-- The truth moves to `fvRes`; node 2 reads it and its pass latches rung 2; its partial on `t2` reaches node 1,
which reads `fvRes` and takes its pass. -/
def raw2 : List Sweep.Step :=
  [.chain fvRes, .observe 2 fvRes, lad 2, .fed (.deliverPartial 1 envFire (row 2 t2)), .observe 1 fvRes, lad 1]
def sched2 : List Sweep.Step :=
  LadderRelease.fill flc Kernel.current (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL run1.1))
    run1.2.cs.sw raw2

/-- `raw2`, node 1's assembly of rung 2 and its send, then `t2`'s confirmation and node 1's reading of it. -/
def steps2 : List RungAssembly.Step :=
  sched2.map .base ++
    [.assemble 1 esL.id 2, .send 1 envFire esL.id 2, .base (.chain fvConf), .base (.observe 1 fvConf)]
def whole : List RungAssembly.Step := steps1 ++ steps2

/-- A schedule's run from `stL` after its first `n` steps. -/
def runOf (ss : List RungAssembly.Step) (n : Nat) : BtcPolicy.Lifecycle.Trace × BtcPolicy.Lifecycle.State :=
  BtcPolicy.Lifecycle.record Kernel.current [] stL (ss.take n)
def runAt (n : Nat) : BtcPolicy.Lifecycle.Trace × BtcPolicy.Lifecycle.State := runOf whole n

/-- Node 1's Escape after the first `n` steps. -/
def escAt (ss : List RungAssembly.Step) (n : Nat) : Option Cand :=
  RungAssembly.escapeAt ((runOf ss n).2.cs.sw.fed.worlds 1).node esL.id

/-- Whether this layer, and the classed layer, admit `s` after the first `n` steps. -/
def admitsAt (cfg : RungAssembly.Cfg) (ss : List RungAssembly.Step) (n : Nat) (s : RungAssembly.Step) : Bool :=
  BtcPolicy.Lifecycle.admits cfg Kernel.current honest (runOf ss n).2 (runOf ss n).1 s
def classedAt (cfg : RungAssembly.Cfg) (ss : List RungAssembly.Step) (n : Nat) (s : RungAssembly.Step) : Bool :=
  BtcPolicy.ClassAssembly.admits cfg Kernel.current honest (runOf ss n).2.cs
    (BtcPolicy.Lifecycle.toL (runOf ss n).1) s

/-- The federation trace under the run. -/
def fedOf (n : Nat) : Federation.Trace :=
  Sweep.fedTrace (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (runAt n).1))

/-- **A rung's whole lifecycle** (`DUR-29`, `DUR-31`, `SPN-33`). The 23 steps are a legal run of the layer, and
every acceptance on it is `LadderShape.check`'s acceptance of `q`: node 1 registers the Escape with both rungs.
Node 2's ladder pass, at its own read, lists rung 1 (step 7); at node 1's assembly (step 11) the finalization over
the variant-bound possession is rung 1, which alone has the quorum on its input, and the assembly leaves one permit
naming rung 1's txid and the observation `fv`. The send consumes it and enters `t1` in the submission history. Node
1 then reads `fvRes`, where `t1` is resident; its assembly of rung 2 replaces `t1` (`Ladder.replacesOf`), and its
send enters `t2`. Node 1 reads `t2` confirmed. Over the history, a coin awaits at `fvRes` and no longer at `fvConf`,
while the history stays; `t1`, submitted, is neither resident nor confirmed at the final truth. -/
@[req "DUR-29"]
theorem lifecycle_run :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL whole = true ∧ whole.length = 23 ∧
      (Ingress.acceptPairs (fedOf 23)).all
        (fun p => [q].any fun q' => BtcPolicy.LadderShape.check ctx0 2 3 true q' == .accepted p.1 p.2) = true ∧
      Ingress.clawCands (fedOf 23) = [] ∧
      (((runAt 23).2.cs.sw.fed.worlds 1).node.cands.filter (·.isEscape)).map (·.above.length) = [2] ∧
      (RungRelease.listed flc (runAt 7).2.cs.sw
        (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (runAt 7).1)) 2).map
        (fun x => (x.1 == esL.id, x.2.1, x.2.2)) = [(true, { latch := 1, floor := 2 }, [1])] ∧
      (escAt whole 11).map (fun c =>
        (BtcPolicy.ClassAssembly.finalAt fcfg (runAt 11).2.cs (BtcPolicy.Lifecycle.toL (runAt 11).1) 1 c,
          (List.range 3).map fun k => Ladder.quorumAt [1, 2, 3] 2 c.ladder
            (BtcPolicy.ClassAssembly.heldAt fcfg (runAt 11).2.cs (BtcPolicy.Lifecycle.toL (runAt 11).1) 1) k)) =
        some (some 1, [false, true, false]) ∧
      (runAt 12).2.perm.map (fun p => (p.node, p.rung, p.txid == t1.id, p.obs == fv)) = [(1, 1, true, true)] ∧
      (runAt 13).2.subs = [(1, true, t1)] ∧ (runAt 13).2.perm = [] ∧
      ((runAt 18).2.cs.sw.obs 1).map (BtcPolicy.Settlement.resident · t1) = some true ∧
      (escAt whole 19).map (fun c =>
        let l := Ladder.txs (BtcPolicy.ClassAssembly.readAt (runAt 19).2.cs (BtcPolicy.Lifecycle.toL (runAt 19).1) 1 c) c
        Ladder.replacesOf l (PreRelease.membership fvRes l) 2) = some (some t1.id) ∧
      (runAt 23).2.subs = [(1, true, t2), (1, true, t1)] ∧
      ((runAt 23).2.cs.sw.obs 1).map (BtcPolicy.Settlement.confirmedAt · t2) = some true ∧
      BtcPolicy.Lifecycle.awaitingAt fvRes (runAt 23).2.subs coin = true ∧
      BtcPolicy.Lifecycle.awaitingAt fvConf (runAt 23).2.subs coin = false ∧
      BtcPolicy.Settlement.shows (runAt 23).2.cs.sw.truth t1 = false := by
  decide +kernel

theorem lifecycle_execution :
    BtcPolicy.Lifecycle.Execution fcfg Kernel.current honest (runAt 23).1 (runAt 23).2 := by
  have hx := BtcPolicy.Lifecycle.execution_of_legal (.init stL ⟨⟨(st0_fresh fv).1, rfl, rfl⟩, rfl, rfl, rfl⟩)
    lifecycle_run.1
  have hl : whole.take 23 = whole := List.take_of_length_le (Nat.le_of_eq lifecycle_run.2.1)
  simpa [runAt, runOf, hl] using hx

/-- The run's acceptances are checked by `LadderShape.check`. -/
theorem lifecycle_checked : BtcPolicy.LadderShape.CheckedTrace ctx0 2 3 (fedOf 23) :=
  BtcPolicy.LadderShape.checkedTrace_of ctx0 2 3 _ [q] [] lifecycle_run.2.2.1
    (by rw [lifecycle_run.2.2.2.1]; rfl)

/-- The run's sweep steps are a `Settlement.Execution`, and no Escape of an honest node is marked broadcast on it. -/
theorem lifecycle_settled :
    BtcPolicy.Settlement.Execution fsw Kernel.current honest
        (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (runAt 23).1)) (runAt 23).2.cs.sw ∧
      ∀ i ∈ honest, ∀ c ∈ ((runAt 23).2.cs.sw.fed.worlds i).node.cands, c.isEscape = true → c.broadcast = false :=
  ⟨BtcPolicy.Lifecycle.to_settlement lifecycle_execution,
    fun _ hi => BtcPolicy.Lifecycle.escape_never_broadcast lifecycle_execution hi⟩

/-- The truth with `t1` evicted. -/
def fvEv : Backend := { fv with sequence := 3 }

/-- `steps1`, then `t1` resident and read, then evicted and read, node 1's new assembly of rung 1 and its send. -/
def evict : List RungAssembly.Step :=
  steps1 ++ [.base (.chain fvRes), .base (.observe 1 fvRes), .base (.chain fvEv), .base (.observe 1 fvEv),
    .assemble 1 esL.id 1, .send 1 envFire esL.id 1]

/-- **The same rung again needs a new assembly** (`DUR-31`, `DUR-29`). Right after node 1 has sent `t1`, a second
send of rung 1 is refused here, its permit consumed, while the classed layer admits it on the historical assembly.
After `t1` is seen resident and then evicted, node 1's new assembly at the new reading gives a new permit and the
same rung is sent again: both sends are in the history, and after the eviction the federation's inventory still
holds node 2's partial on `t1`. -/
@[req "DUR-31"]
theorem resend_after_eviction :
    admitsAt fcfg steps1 13 (.send 1 envFire esL.id 1) = false ∧
      classedAt fcfg steps1 13 (.send 1 envFire esL.id 1) = true ∧
      BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL evict = true ∧
      (runOf evict 16).2.cs.sw.truth = fvEv ∧ (runOf evict 19).2.cs.sw.fed.parts.contains (row 2 t1) = true ∧
      (runOf evict 19).2.subs = [(1, true, t1), (1, true, t1)] := by
  decide +kernel

/-- The truth with `t1` confirmed and the coin spent; then a reorganization to another block at height 6 that holds
nothing, the coin unspent again. -/
def fvT1 : Backend := { fv with tip := ⟨6, 106⟩, sequence := 2, confirmed := [], mined := [(t1.id, t1.inputs)] }
def fvRg : Backend := { fv with tip := ⟨6, 206⟩, sequence := 3 }
def envR : Env := Kernel.RegistrationCases.envAt 130 70

/-- `steps1`, then `t1` confirmed, read and settled by node 1; the reorganization, read by node 1; node 1's new
assembly of rung 1 and its send. -/
def reorg : List RungAssembly.Step :=
  steps1 ++ [.base (.chain fvT1), .base (.observe 1 fvT1),
    .base (.fed (.process 1 (Kernel.RegistrationCases.envAt 125 65 [t1]) (.settle t1))), .base (.chain fvRg),
    .base (.observe 1 fvRg), .assemble 1 esL.id 1, .send 1 envR esL.id 1]

/-- **A confirmed rung, then an in-window reorganization: the same rung again** (`DUR-31`, `SPN-33`). Node 1 reads
`t1` confirmed and settles it: the hot spend sharing its input is marked terminal and its pending entry is cleared,
while the Escape, whose own transaction is the base, is not settled. After the reorganization, read by node 1, the
send of the earlier assembly is refused here (its permit consumed) and admitted by the classed layer; node 1's new
assembly of rung 1 at the new reading and its send, inside the window, are admitted, and the history holds `t1`
twice. The Escape's latch and floor are the same before the confirmation and after the resend. -/
@[req "DUR-31"]
theorem reorg_resend :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL reorg = true ∧ reorg.length = 20 ∧
      ((runOf reorg 15).2.cs.sw.obs 1).map (BtcPolicy.Settlement.confirmedAt · t1) = some true ∧
      ((runOf reorg 15).2.cs.sw.fed.worlds 1).node.pendingLog.entries.any (·.id == spL.id) = true ∧
      ((runOf reorg 16).2.cs.sw.fed.worlds 1).node.pendingLog.entries.any (·.id == spL.id) = false ∧
      ((runOf reorg 16).2.cs.sw.fed.worlds 1).node.pendingLog.cleared.contains spL.id = true ∧
      ((runOf reorg 16).2.cs.sw.fed.worlds 1).node.cands.any (fun c => c.id == spL.id && c.terminal) = true ∧
      (escAt reorg 13).map (fun c => (c.track, c.settled)) = some ({ latch := 1, floor := 2 }, false) ∧
      (escAt reorg 20).map (fun c => (c.track, c.settled)) = some ({ latch := 1, floor := 2 }, false) ∧
      admitsAt fcfg reorg 17 (.send 1 envR esL.id 1) = false ∧
      classedAt fcfg reorg 17 (.send 1 envR esL.id 1) = true ∧
      (runOf reorg 20).2.subs = [(1, true, t1), (1, true, t1)] := by
  decide +kernel

/-- `steps1`, then `t1` resident and read by node 1. -/
def resid : List RungAssembly.Step := steps1 ++ [.base (.chain fvRes), .base (.observe 1 fvRes)]

/-- **A resident rung at the latch: nothing** (`DUR-31`). Once node 1 reads `t1` resident, its assembly of rung 1
is refused, on this layer and on the classed one (the package test rejects a txid already in the mempool), so no
permit exists to send it; and that reading is not quiet for rung 1. -/
@[req "DUR-31"]
theorem resident_no_send :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL resid = true ∧
      classedAt fcfg resid 15 (.assemble 1 esL.id 1) = false ∧
      admitsAt fcfg resid 15 (.assemble 1 esL.id 1) = false ∧
      (runOf resid 15).2.perm = [] ∧
      (escAt resid 15).map (fun c => BtcPolicy.Lifecycle.quiet fvRes c 1) = some false := by
  decide +kernel

/-- `sched1` and node 1's assembly of rung 1, not yet sent. -/
def pre1 : List RungAssembly.Step := sched1.map .base ++ [.assemble 1 esL.id 1]

/-- `pre1`, then `t1` resident (another sender's), read by node 1 before its next ladder pass. -/
def stale : List RungAssembly.Step :=
  pre1 ++ (LadderRelease.fill flc Kernel.current (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL
    (runOf pre1 12).1)) (runOf pre1 12).2.cs.sw [.chain fvRes, .observe 1 fvRes, lad 1]).map .base

/-- `pre1`, then node 1 repeats its request for the same pair under Carrier id 10, which it has consumed. -/
def again : List RungAssembly.Step := pre1 ++ [.base (acc 1)]

/-- **An old assembly does not outlive its pass; a no-op request keeps it** (`DUR-29`). After node 1's next ladder
pass, at a reading where its assembly of rung 1 fails, the send of the earlier assembly is refused here and admitted by
the classed layer. Node 1's repeat of its request for the same pair, under the Carrier id it has consumed, is refused
by the kernel and leaves node 1's registry as it was: nothing is born, the permit stays, and the send is admitted
here. -/
@[req "DUR-29"]
theorem stale_tuple_refused :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL stale = true ∧
      admitsAt fcfg stale 15 (.assemble 1 esL.id 1) = false ∧
      admitsAt fcfg stale 15 (.send 1 envFire esL.id 1) = false ∧
      classedAt fcfg stale 15 (.send 1 envFire esL.id 1) = true ∧
      BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL again = true ∧
      ((runOf again 13).2.cs.sw.fed.worlds 1).node.cands = ((runOf again 12).2.cs.sw.fed.worlds 1).node.cands ∧
      (runOf again 13).2.perm = (runOf again 12).2.perm ∧ (runOf again 13).2.perm.length = 1 ∧
      admitsAt fcfg again 13 (.send 1 envFire esL.id 1) = true := by
  decide +kernel

/-- `steps1`, then node 1's pruning past the expiry. -/
def pruned : List RungAssembly.Step := steps1 ++ [.base (.fed (.process 1 envLate .prune))]

/-- **Pruning keeps the history** (`SPN-33`). Node 1's pruning empties its registry; the send of `t1` stays in the
history and no permit is left. -/
@[req "SPN-33"]
theorem prune_keeps_history :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL pruned = true ∧
      ((runOf pruned 14).2.cs.sw.fed.worlds 1).node.cands = [] ∧
      (runOf pruned 14).2.subs = [(1, true, t1)] ∧ (runOf pruned 14).2.perm = [] := by
  decide +kernel

def envP : Env := Kernel.RegistrationCases.envAt 150 90
/-- A ladder pass at `env`, its listing left for `LadderRelease.fill` to compute. -/
def ladAt (i : Nat) (env : Env) : Sweep.Step := .fed (.process i { env with ladder := [] } .ladderPass)
def acc11 (i : Nat) : Sweep.Step := .fed (.process i envP (.accept 11 true (Wall.sample 200) spL esL))

/-- `steps1`, then node 1 reads `fv` and assembles rung 1 again, and does not send it. -/
def pre2 : List RungAssembly.Step := steps1 ++ [.base (.observe 1 fv), .assemble 1 esL.id 1]

/-- Node 1's pruning at 150, past its armed horizon (`T` 95 and a slack of 40) and before the pair's expiry, which
removes the selected pair; a fresh request for the same pair under Carrier id 11 at nodes 1 and 2 (node 2's a repeat
of a resident pair); node 2's relay reaches node 1, whose holder decision writes the window at 150; node 1's ladder
pass; node 2's partial on `t1`, still in the inventory, reaches node 1 again; node 1 reads `fv`. -/
def raw3 : List Sweep.Step :=
  [.fed (.process 1 envP .prune), acc11 1, acc11 2, .fed (.emit 2 11), .fed (.deliver 1 envP ⟨2, 11⟩), ladAt 1 envP,
   .fed (.deliverPartial 1 envP (row 2 t1)), .observe 1 fv]
def sched3 : List Sweep.Step :=
  LadderRelease.fill flc Kernel.current (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (runOf pre2 15).1))
    (runOf pre2 15).2.cs.sw raw3

/-- `pre2`, `raw3`, then node 1's assembly of rung 1 in the new lifetime and its send. -/
def fresh : List RungAssembly.Step := pre2 ++ sched3.map .base ++ [.assemble 1 esL.id 1, .send 1 envP esL.id 1]

/-- Node 1's finalization for its Escape after the first `n` steps of `ss`, and its per-rung quorum over the
variant-bound possession. -/
def heldQuorum (ss : List RungAssembly.Step) (n : Nat) : Option (Option Nat × List Bool) :=
  (escAt ss n).map fun c =>
    (BtcPolicy.ClassAssembly.finalAt fcfg (runOf ss n).2.cs (BtcPolicy.Lifecycle.toL (runOf ss n).1) 1 c,
      (List.range 3).map fun k => Ladder.quorumAt [1, 2, 3] 2 c.ladder
        (BtcPolicy.ClassAssembly.heldAt fcfg (runOf ss n).2.cs (BtcPolicy.Lifecycle.toL (runOf ss n).1) 1) k)

/-- **Pruning, then a fresh registration** (`DUR-31`, `SPN-41`, `POL-18`). After `steps1` node 1 assembles rung 1
again and holds a permit for it (step 15). Its pruning at 150 empties its registry and ends the permit. A fresh
request for the same pair registers it again at node 1, and the holder decision opens the new window at 150. After the
new ladder pass the variant-bound possession holds no quorum on any rung, while the federation's inventory still holds node 2's partial on `t1`; that partial reaches node 1 again with no new release
by node 2, and rung 1 has its quorum. At that state (step 23) the history still holds the first send of `t1` and node 1
holds no permit: the classed layer admits a send on the old assembly tuple, which `RungAssembly.State.assembled` still
holds, and this layer refuses it. Node 1's assembly in the new lifetime and its send are admitted, and the history
holds `t1` twice. -/
@[req "DUR-31"]
theorem fresh_after_prune :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL fresh = true ∧ fresh.length = 25 ∧
      (runOf fresh 15).2.perm.length = 1 ∧
      ((runOf fresh 16).2.cs.sw.fed.worlds 1).node.cands = [] ∧ (runOf fresh 16).2.perm = [] ∧
      (escAt fresh 20).map (fun c => (c.fireAt, c.windowClose, c.quorum)) =
        some (some (Wall.sample 150), some (Wall.sample 190), true) ∧
      heldQuorum fresh 21 = some (none, [false, false, false]) ∧
      (runOf fresh 21).2.cs.sw.fed.parts.contains (row 2 t1) = true ∧
      heldQuorum fresh 23 = some (some 1, [false, true, false]) ∧
      (runOf fresh 23).2.subs = [(1, true, t1)] ∧ (runOf fresh 23).2.perm = [] ∧
      (runOf fresh 23).2.cs.assembled.contains (1, esL.id, t1.id) = true ∧
      classedAt fcfg fresh 23 (.send 1 envP esL.id 1) = true ∧
      admitsAt fcfg fresh 23 (.send 1 envP esL.id 1) = false ∧
      (runOf fresh 25).2.subs = [(1, true, t1), (1, true, t1)] := by
  decide +kernel

/-- A truth with an unrelated resident. -/
def fvX : Backend := { fv with sequence := 2, mempool := [(777, [5])] }

/-- `pre1`, then the truth moves, then node 1 sends. -/
def moved : List RungAssembly.Step := pre1 ++ [.base (.chain fvX), .send 1 envFire esL.id 1]

/-- **The send reads no backend; the window does count** (`DUR-29`). A truth that moves after node 1's assembly
does not stop the send, which reads the assembly's observation. At a send after the window closes the
re-authorization fails, on this layer and on the classed one. -/
@[req "DUR-29"]
theorem send_reauthorized :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL moved = true ∧
      (runOf moved 14).2.subs = [(1, true, t1)] ∧
      admitsAt fcfg pre1 12 (.send 1 envLate esL.id 1) = false ∧
      classedAt fcfg pre1 12 (.send 1 envLate esL.id 1) = false := by
  decide +kernel

/-- An instant with the coin not confirmed; one with another transaction, outside the ladder, spending it. -/
def fvNo : Backend := { fv with sequence := 2, confirmed := [] }
def fvU : Backend := { fv with sequence := 2, mempool := [(777, [coin])] }
def absent : List RungAssembly.Step := sched1.map .base ++ [.base (.chain fvNo), .base (.observe 1 fvNo)]
def unauth : List RungAssembly.Step := sched1.map .base ++ [.base (.chain fvU), .base (.observe 1 fvU)]

/-- **The reading refuses the assembly** (`DUR-29`, `WTC-24`). Where node 1's assembly of rung 1 at `fv` is admitted,
the same assembly is refused, here and on the classed layer, after node 1 reads an instant where the coin is not
confirmed, and after it reads one where a transaction outside the ladder spends it. -/
@[req "DUR-29"]
theorem read_refuses_assembly :
    admitsAt fcfg pre1 11 (.assemble 1 esL.id 1) = true ∧
      BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL absent = true ∧
      admitsAt fcfg absent 13 (.assemble 1 esL.id 1) = false ∧ classedAt fcfg absent 13 (.assemble 1 esL.id 1) = false ∧
      BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL unauth = true ∧
      admitsAt fcfg unauth 13 (.assemble 1 esL.id 1) = false ∧
      classedAt fcfg unauth 13 (.assemble 1 esL.id 1) = false := by
  decide +kernel

def envS1 : Env := Kernel.RegistrationCases.envAt 125 65 [t1]

/-- `pre1`, then `t1` confirmed, and node 1's reading and settlement of it. -/
def settleP : List RungAssembly.Step :=
  pre1 ++ [.base (.chain fvT1), .base (.observe 1 fvT1), .base (.fed (.process 1 envS1 (.settle t1)))]

/-- **A settled rung ends the permit** (`DUR-31`). Node 1 assembles rung 1 at `fv` and holds its permit; `t1` is then
confirmed, and node 1 reads and settles it. The settlement ends the permit, so its send is refused here, while the
classed layer, where the Escape is not settled, admits it on the historical assembly. -/
@[req "DUR-31"]
theorem settle_ends_permit :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL settleP = true ∧
      (runOf settleP 14).2.perm.length = 1 ∧ (runOf settleP 15).2.perm = [] ∧
      (escAt settleP 15).map (·.settled) = some false ∧
      admitsAt fcfg settleP 15 (.send 1 envR esL.id 1) = false ∧
      classedAt fcfg settleP 15 (.send 1 envR esL.id 1) = true := by
  decide +kernel

/-- At a floor of 1 the base is admissible with no median reading. -/
def kpre : PreRelease.Cfg := { fpre with floor := 1 }
def klc : Ladder.Cfg := { flc with pre := kpre }
def kcfg : RungAssembly.Cfg := { fcfg with lc := klc }
def fvM : Backend := withMedian { fv with sequence := 2 } 5
def pa : Sweep.Step := .fed (.process 1 envFire (.packageAccepted esL.id))
def ksend : Sweep.Step := .fed (.process 1 envFire (.send esL.id))

/-- Both nodes take fire and ladder passes at `fv`, latch 0; node 2's base partial reaches node 1, which assembles
the Escape on the base path; the median moves to 5, node 1's pass latches rung 2, and node 1 sends on the kernel
path. -/
def rawK : List Sweep.Step :=
  [acc 1, acc 2, .fed (.emit 1 10), .fed (.emit 2 10), .fed (.deliver 1 env0 ⟨2, 10⟩),
   .fed (.deliver 2 env0 ⟨1, 10⟩), .observe 2 fv, .fed (.process 2 envFire .firePass), lad 2,
   .observe 1 fv, .fed (.process 1 envFire .firePass), lad 1, .fed (.deliverPartial 1 envFire (row 2 tB)), pa,
   .chain fvM, .observe 1 fvM, lad 1, ksend]
def kgap : List RungAssembly.Step := (LadderRelease.fill klc Kernel.current [] (st0 fv).sw rawK).map .base
def classedRun (n : Nat) : BtcPolicy.ClassAssembly.LTrace × RungAssembly.State :=
  BtcPolicy.ClassAssembly.record Kernel.current [] stL.cs (kgap.take n)

/-- `kgap` up to its kernel send, then node 1's assembly of rung 0 on the rung path and its send. -/
def kroute : List RungAssembly.Step := kgap.take 17 ++ [.assemble 1 esL.id 0, .send 1 envFire esL.id 0]

/-- **The kernel's standing package test sends no Escape** (`DUR-31`, `DUR-29`). On the classed layer the whole of
`kgap` is legal: node 1's base-path assembly at latch 0 sets the Escape's package test, its latch then rises to 2,
and the kernel send still submits the base and marks the Escape broadcast. Here the run up to the send is legal and
the send is refused. Node 1 holds the quorum on the base alone, so rung 0 is the finalization at latch 2: its
assembly on the rung path, at the new reading, and its send are admitted, the base enters the submission history
as an Escape's, and the Escape stays unmarked. -/
@[req "DUR-31"]
theorem kernel_escape_refused :
    BtcPolicy.ClassAssembly.legal kcfg Kernel.current honest [] stL.cs kgap = true ∧ kgap.length = 18 ∧
      Sweep.submits Kernel.current (classedRun 17).2.sw ksend = [tB.id] ∧
      (((classedRun 18).2.sw.fed.worlds 1).node.cands.filter (·.isEscape)).map (·.broadcast) = [true] ∧
      BtcPolicy.Lifecycle.legal kcfg Kernel.current honest [] stL (kgap.take 17) = true ∧
      (escAt kgap 17).map (fun c => (c.track, c.packageOk)) = some ({ latch := 2, floor := 3 }, true) ∧
      admitsAt kcfg kgap 17 (.base ksend) = false ∧
      BtcPolicy.Lifecycle.legal kcfg Kernel.current honest [] stL kroute = true ∧
      (escAt kroute 17).map (fun c =>
        BtcPolicy.ClassAssembly.finalAt kcfg (runOf kroute 17).2.cs (BtcPolicy.Lifecycle.toL (runOf kroute 17).1) 1 c) =
        some (some 0) ∧
      (runOf kroute 19).2.subs = [(1, true, tB)] ∧
      ((((runOf kroute 19).2.cs.sw.fed.worlds 1).node.cands.filter (·.isEscape)).map (·.broadcast)) = [false] := by
  decide +kernel

/-- The base confirmed and the coin spent; then a reorganization, the coin unspent again. -/
def fvB : Backend := { fv with tip := ⟨6, 106⟩, sequence := 3, confirmed := [], mined := [(tB.id, tB.inputs)] }
def fvBr : Backend := { fv with tip := ⟨6, 206⟩, sequence := 4 }

/-- After `kroute`: the base confirmed and read by node 1, settled there or not, the reorganization read by node 1,
and node 1's new assembly of rung 0 and its send inside the window. -/
def tailK (settle : Bool) : List RungAssembly.Step :=
  [.base (.chain fvB), .base (.observe 1 fvB)] ++
    (if settle then [.base (.fed (.process 1 (Kernel.RegistrationCases.envAt 125 65 [tB]) (.settle tB)))] else []) ++
    [.base (.chain fvBr), .base (.observe 1 fvBr), .assemble 1 esL.id 0, .send 1 envR esL.id 0]
def kS : List RungAssembly.Step := kroute ++ tailK true
def kN : List RungAssembly.Step := kroute ++ tailK false

/-- **A settled base no longer blocks its resend** (`DUR-31`, `SPN-39`, `SPN-38`). `Kernel.settle` marks settled every
resident whose transaction is the settled one, and the base is the Escape's own transaction: once node 1 settles the
confirmed base, its Escape is settled, and it stays settled through the reorganization. While node 1's reading shows
the base confirmed, its assembly of rung 0 is refused. After the reorganization, read by node 1, its new assembly of
rung 0, which `ClassAssembly.assembleOk` admits only as the finalization there (`DUR-28`), is admitted, and its send
inside the window is admitted here and on the classed layer: at that state `Kernel.due` holds of the Escape and
`Kernel.duePre` does not. A send after the window closes is refused on both layers. The latch and floor are the same
before the confirmation and after the resend, and the history holds the base twice, with or without the
settlement. -/
@[req "DUR-31"]
theorem settled_base_blocks_resend :
    BtcPolicy.Lifecycle.legal kcfg Kernel.current honest [] stL kS = true ∧ kS.length = 26 ∧
      (escAt kS 19).map (·.track) = some { latch := 2, floor := 3 } ∧
      (escAt kS 21).map (·.settled) = some false ∧ (escAt kS 22).map (·.settled) = some true ∧
      admitsAt kcfg kS 22 (.assemble 1 esL.id 0) = false ∧
      (escAt kS 25).map (fun c => (due Kernel.current envR ((runOf kS 25).2.cs.sw.fed.worlds 1).node c,
        duePre Kernel.current envR ((runOf kS 25).2.cs.sw.fed.worlds 1).node c)) = some (true, false) ∧
      admitsAt kcfg kS 25 (.send 1 envR esL.id 0) = true ∧ classedAt kcfg kS 25 (.send 1 envR esL.id 0) = true ∧
      admitsAt kcfg kS 25 (.send 1 envLate esL.id 0) = false ∧
      classedAt kcfg kS 25 (.send 1 envLate esL.id 0) = false ∧
      (escAt kS 26).map (fun c => (c.track, c.settled, c.broadcast)) = some ({ latch := 2, floor := 3 }, true, false) ∧
      (runOf kS 26).2.subs = [(1, true, tB), (1, true, tB)] ∧
      BtcPolicy.Lifecycle.legal kcfg Kernel.current honest [] stL kN = true ∧
      (runOf kN 25).2.subs = [(1, true, tB), (1, true, tB)] := by
  decide +kernel

/-- The base resident, another sender's. -/
def fvBres : Backend := { fv with sequence := 2, mempool := [(tB.id, tB.inputs)] }
def envSB : Env := Kernel.RegistrationCases.envAt 125 65 [tB]

/-- `sched1`, then the base resident and read by node 1, settled there or not, and node 1's assembly of rung 1, its
replacement, and its send. -/
def repl (settle : Bool) : List RungAssembly.Step :=
  sched1.map .base ++ [.base (.chain fvBres), .base (.observe 1 fvBres)] ++
    (if settle then [.base (.fed (.process 1 envSB (.settle tB)))] else []) ++
    [.assemble 1 esL.id 1, .send 1 envR esL.id 1]

/-- **A settled base no longer blocks the replacement** (`DUR-31`, `DUR-29`). Node 1, at latch 1, reads the base
resident, another sender's, with no reorganization and no earlier send of its own. Its settlement of the base clears
the paired spend's pending entry and marks the Escape settled, not broadcast and not terminal, at latch 1. Its
assembly of rung 1, the replacement of the resident base, is admitted and leaves a permit; the send is admitted, here
and on the classed layer, and enters `t1` in the history, the latch and floor as they were. A send after the window
closes is refused on both layers. The same steps without the settlement send `t1` too. -/
@[req "DUR-31"]
theorem settled_base_blocks_replacement :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL (repl true) = true ∧
      (repl true).length = 16 ∧
      ((runOf (repl true) 13).2.cs.sw.fed.worlds 1).node.pendingLog.entries.any (·.id == spL.id) = true ∧
      ((runOf (repl true) 14).2.cs.sw.fed.worlds 1).node.pendingLog.entries.any (·.id == spL.id) = false ∧
      ((runOf (repl true) 14).2.cs.sw.fed.worlds 1).node.pendingLog.cleared.contains spL.id = true ∧
      (escAt (repl true) 13).map (·.settled) = some false ∧
      (escAt (repl true) 14).map (fun c => (c.settled, c.broadcast, c.terminal, c.track)) =
        some (true, false, false, { latch := 1, floor := 2 }) ∧
      (runOf (repl true) 15).2.perm.length = 1 ∧
      admitsAt fcfg (repl true) 15 (.send 1 envR esL.id 1) = true ∧
      classedAt fcfg (repl true) 15 (.send 1 envR esL.id 1) = true ∧
      admitsAt fcfg (repl true) 15 (.send 1 envLate esL.id 1) = false ∧
      classedAt fcfg (repl true) 15 (.send 1 envLate esL.id 1) = false ∧
      (runOf (repl true) 16).2.subs = [(1, true, t1)] ∧
      (escAt (repl true) 16).map (·.track) = some { latch := 1, floor := 2 } ∧
      BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL (repl false) = true ∧
      (runOf (repl false) 15).2.subs = [(1, true, t1)] := by
  decide +kernel

/-- `sched1`, then the base resident and read by node 1, node 1's assembly of rung 1, and its settlement of the base. -/
def staleB : List RungAssembly.Step :=
  sched1.map .base ++ [.base (.chain fvBres), .base (.observe 1 fvBres), .assemble 1 esL.id 1,
    .base (.fed (.process 1 envSB (.settle tB)))]

/-- **A base settlement ends the permit read before it** (`DUR-31`). Node 1 assembles rung 1 at the reading where
the base is resident and holds its permit; it then settles the base, which marks the Escape settled and ends the
permit, so the send is refused here. The classed layer, which reads no permit and no longer refuses a settled Escape,
admits it on the historical assembly. -/
@[req "DUR-31"]
theorem base_settle_ends_permit :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL staleB = true ∧
      (runOf staleB 14).2.perm.length = 1 ∧ (runOf staleB 15).2.perm = [] ∧
      (escAt staleB 15).map (·.settled) = some true ∧
      admitsAt fcfg staleB 15 (.send 1 envR esL.id 1) = false ∧
      classedAt fcfg staleB 15 (.send 1 envR esL.id 1) = true := by
  decide +kernel

/-- The median reading of 5 with the base resident, another sender's. -/
def fvMB : Backend := { fvM with sequence := 3, mempool := [(tB.id, tB.inputs)] }

/-- `kgap` up to its kernel send, then the base resident and read by node 1, node 1's settlement of it, and the
kernel send. -/
def kW : List RungAssembly.Step :=
  kgap.take 17 ++ [.base (.chain fvMB), .base (.observe 1 fvMB), .base (.fed (.process 1 envSB (.settle tB))),
    .base ksend]
def classedW (n : Nat) : BtcPolicy.ClassAssembly.LTrace × RungAssembly.State :=
  BtcPolicy.ClassAssembly.record Kernel.current [] stL.cs (kW.take n)

/-- **The kernel path is wider** (`SPN-39`, `DUR-31`). On the classed layer, node 1's settlement of the base, resident
as another sender's, marks its Escape settled; the Escape is still due, so the kernel send on the package test of
the earlier base-path assembly is admitted and submits the base again, which `Kernel.duePre` would have refused.
This layer refuses that send, as it refuses every kernel send of an Escape. -/
@[req "DUR-31"]
theorem settled_kernel_send_widened :
    BtcPolicy.ClassAssembly.legal kcfg Kernel.current honest [] stL.cs kW = true ∧ kW.length = 21 ∧
      (((classedW 20).2.sw.fed.worlds 1).node.cands.filter (·.isEscape)).map
        (fun c => (c.settled, c.packageOk, due Kernel.current envFire ((classedW 20).2.sw.fed.worlds 1).node c,
          duePre Kernel.current envFire ((classedW 20).2.sw.fed.worlds 1).node c)) = [(true, true, true, false)] ∧
      Sweep.submits Kernel.current (classedW 20).2.sw ksend = [tB.id] ∧
      BtcPolicy.Lifecycle.legal kcfg Kernel.current honest [] stL (kW.take 20) = true ∧
      admitsAt kcfg kW 20 (.base ksend) = false := by
  decide +kernel

/-- **Off a settled Escape nothing moves** (`SPN-38`). On the whole lifecycle run no step settles the base of an
Escape-role resident of node 1, so by `Lifecycle.due_eq_pre_run` every resident of node 1 is due under `Kernel.due`
exactly when it is under `Kernel.duePre`, at every environment. -/
@[req "SPN-38"]
theorem lifecycle_due_pre (env : Env) :
    ∀ c ∈ ((runAt 23).2.cs.sw.fed.worlds 1).node.cands,
      due Kernel.current env ((runAt 23).2.cs.sw.fed.worlds 1).node c =
        duePre Kernel.current env ((runAt 23).2.cs.sw.fed.worlds 1).node c := by
  have hn : (fedOf 23).all (fun y => !BtcPolicy.Lifecycle.settlesEscape y.1 y.2 1) = true := by decide +kernel
  refine BtcPolicy.Lifecycle.due_eq_pre_run
    (Sweep.fed_execution (Settlement.to_sweep (BtcPolicy.Lifecycle.to_settlement lifecycle_execution)))
    (by decide) (fun y hy => ?_) env
  have := List.all_eq_true.1 hn y hy
  simpa using this

end BtcPolicy.Exhibits.Lifecycle

namespace BtcPolicy.Exhibits.Retained
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Exhibits.Lifecycle (runOf runAt whole fresh esL fcfg stL)
open BtcPolicy.Exhibits.EndToEnd (honest)

/-! ### One retained lifetime on the lifecycle runs

`BtcPolicy.Retained` over the runs of `Exhibits.Lifecycle`: the latch and floor of node 1's Escape rise across one
lifetime; a pruning and a fresh registration start a new lifetime at zero, which the lifetime theorem does not
forbid; and node 2's repeat of its resident pair keeps its records and its Held partial set. -/

/-- A run's sweep trace. -/
def swOf (ss : List RungAssembly.Step) (n : Nat) : Sweep.Trace :=
  BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (runOf ss n).1)

/-- Node `i`'s Escape-role records in sweep state `st`, by their release state. -/
def tracks (st : Sweep.State) (i : Nat) : List Track :=
  ((st.fed.worlds i).node.cands.filter (·.isEscape)).map (·.track)

theorem split_at (l : Sweep.Trace) (n : Nat) (h : n < l.length) : l = l.take n ++ l[n] :: l.drop (n + 1) := by
  conv => lhs; rw [← List.take_append_drop n l]
  rw [List.drop_eq_getElem_cons h]

/-- **The latch and floor rise across one lifetime** (`DUR-27`). On the whole lifecycle run, from the state after
node 1's acceptance, no step births a record under the Escape's id at node 1; node 1's Escape starts at latch 0 and
floor 0 and ends at latch 2 and floor 3, its own two ladder passes raising them, and `Retained.lifetime_mono` gives every record under the id at the end
an ancestor at the start with the same registration-owned fields. -/
@[req "DUR-27"]
theorem lifetime_on_run :
    (swOf whole 23).length = 19 ∧
      (((swOf whole 23).take 17) ++ [(swOf whole 23).getD 17 (stL.cs.sw, .observe 0 BtcPolicy.Exhibits.Lifecycle.fv)]).all
        (fun y => !BtcPolicy.Lifecycle.births Kernel.current y.1 y.2 1 esL.id) = true ∧
      tracks ((swOf whole 23).getD 17 (stL.cs.sw, .observe 0 BtcPolicy.Exhibits.Lifecycle.fv)).1 1 = [{ latch := 0, floor := 0 }] ∧
      tracks (runAt 23).2.cs.sw 1 = [{ latch := 2, floor := 3 }] ∧
      ∀ c ∈ ((runAt 23).2.cs.sw.fed.worlds 1).node.cands, c.id = esL.id →
        ∃ d ∈ ((((swOf whole 23).getD 17 (stL.cs.sw, .observe 0 BtcPolicy.Exhibits.Lifecycle.fv)).1).fed.worlds 1).node.cands,
          BtcPolicy.Retained.reg d = BtcPolicy.Retained.reg c ∧ d.track.floor ≤ c.track.floor ∧
            d.track.latch ≤ c.track.latch := by
  have hd : (swOf whole 23).length = 19 ∧
      (((swOf whole 23).take 17) ++ [(swOf whole 23).getD 17 (stL.cs.sw, .observe 0 BtcPolicy.Exhibits.Lifecycle.fv)]).all
        (fun y => !BtcPolicy.Lifecycle.births Kernel.current y.1 y.2 1 esL.id) = true ∧
      tracks ((swOf whole 23).getD 17 (stL.cs.sw, .observe 0 BtcPolicy.Exhibits.Lifecycle.fv)).1 1 = [{ latch := 0, floor := 0 }] ∧
      tracks (runAt 23).2.cs.sw 1 = [{ latch := 2, floor := 3 }] := by
    decide +kernel
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, ?_⟩
  have hlt : 17 < (swOf whole 23).length := by rw [hd.1]; decide
  have hg : (swOf whole 23).getD 17 (stL.cs.sw, .observe 0 BtcPolicy.Exhibits.Lifecycle.fv) = (swOf whole 23)[17] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  have hb := hd.2.1
  rw [hg] at hb ⊢
  have hx := BtcPolicy.Lifecycle.to_ladder BtcPolicy.Exhibits.Lifecycle.lifecycle_execution
  have hs := split_at (swOf whole 23) 17 hlt
  apply BtcPolicy.Retained.lifetime_mono hx (by decide) (T₁ := (swOf whole 23).drop (17 + 1))
    (T₂ := (swOf whole 23).take 17) (st₀ := ((swOf whole 23)[17]).1) (s₀ := ((swOf whole 23)[17]).2) hs
  intro y hy
  have := List.all_eq_true.1 hb y hy
  simpa using this

/-- **A fresh registration starts a new lifetime at zero** (`DUR-27`, `SPN-32`). On the run of
`Exhibits.Lifecycle.fresh_after_prune`, node 1's Escape holds latch 1 and floor 2 before its pruning; the pruning
removes it, and the fresh registration of the same pair births a record whose latch and floor are 0. That stretch
births a record under the id at node 1, so `Retained.lifetime_mono` does not apply, and its conclusion is false there:
no record before the pruning has the new one's fields with a latch at or below 0. The reset is a legitimate new
lifetime, and the lifetime theorem does not forbid it. -/
@[req "DUR-27"]
theorem fresh_resets :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL (fresh.take 17) = true ∧
      tracks (runOf fresh 15).2.cs.sw 1 = [{ latch := 1, floor := 2 }] ∧
      ((runOf fresh 16).2.cs.sw.fed.worlds 1).node.cands = [] ∧
      tracks (runOf fresh 17).2.cs.sw 1 = [{ latch := 0, floor := 0 }] ∧
      ((swOf fresh 17).take 2).any (fun y => BtcPolicy.Lifecycle.births Kernel.current y.1 y.2 1 esL.id) = true ∧
      (((runOf fresh 17).2.cs.sw.fed.worlds 1).node.cands.any fun c => c.id == esL.id &&
        ((runOf fresh 15).2.cs.sw.fed.worlds 1).node.cands.all fun d =>
          !(BtcPolicy.Retained.reg d == BtcPolicy.Retained.reg c && decide (d.track.latch ≤ c.track.latch))) = true := by
  decide +kernel

/-- **A repeat keeps the records and the Held set** (`SPN-32`, `DUR-28`). On the same run, node 2's acceptance under
Carrier id 11 (`Exhibits.Lifecycle.acc11`, the eighteenth step) repeats its resident pair: its registry's registration-owned fields and release states, its Escape at
latch 1 and floor 2, and its Held partial set are the same after it as before, as `Retained.repeat_keeps` and
`Retained.repeat_held` state for every such acceptance under `Registration.preserve`, the value `Kernel.current` takes. -/
@[req "SPN-32"]
theorem repeat_on_run :
    (((runOf fresh 17).2.cs.sw.fed.worlds 2).node.cands.any (·.id == BtcPolicy.Exhibits.Lifecycle.spL.id) &&
      (((runOf fresh 18).2.cs.sw.fed.worlds 2).node.cands.map (fun c => (BtcPolicy.Retained.reg c, c.track)) ==
        ((runOf fresh 17).2.cs.sw.fed.worlds 2).node.cands.map (fun c => (BtcPolicy.Retained.reg c, c.track))) &&
      (tracks (runOf fresh 18).2.cs.sw 2 == [{ latch := 1, floor := 2 }]) &&
      (BtcPolicy.ClassAssembly.heldAt fcfg (runOf fresh 18).2.cs (BtcPolicy.Lifecycle.toL (runOf fresh 18).1) 2 ==
        BtcPolicy.ClassAssembly.heldAt fcfg (runOf fresh 17).2.cs (BtcPolicy.Lifecycle.toL (runOf fresh 17).1) 2)) =
      true := by
  decide +kernel

/-- `Retained.latch_on_ladder` on the whole lifecycle run, at both honest nodes. -/
theorem latch_on_run :
    ∀ i ∈ honest, ∀ c ∈ ((runAt 23).2.cs.sw.fed.worlds i).node.cands, c.track.latch < c.ladder.length :=
  fun _ hi => BtcPolicy.Retained.life_latch_on_ladder BtcPolicy.Exhibits.Lifecycle.lifecycle_execution hi

/-- **A refused rung keeps the release state** (`SPN-38`, `DUR-27`). On the run of
`Exhibits.RungRelease.rung_on_run`, the nineteenth step is node 1's ladder pass at the read where every rung of its
Escape is refused (`Exhibits.RungRelease.refused_rung_on_run`): the release computed for each of its Escapes lists
nothing, the run takes the pass that lists nothing, and the Escape holds latch 2 and floor 3 before the pass and
after it. `Retained.quiet_keeps`, applied to that admitted pass, keeps the release state of every record whose own
computed release lists nothing. -/
@[req "SPN-38"]
theorem refused_pass_keeps :
    (BtcPolicy.Exhibits.RungRelease.sched.getD 18 (.chain BtcPolicy.Exhibits.RungRelease.vm) =
        BtcPolicy.Exhibits.RungRelease.lad 1 ∧
      (((BtcPolicy.Exhibits.RungRelease.runR 18).2.fed.worlds 1).node.cands.filter (·.isEscape)).all (fun c =>
        (BtcPolicy.Ladder.release BtcPolicy.Exhibits.Integrated.ilc
          (BtcPolicy.RungRelease.readAt (BtcPolicy.Exhibits.RungRelease.runR 18).2
            (BtcPolicy.Exhibits.RungRelease.runR 18).1 1 c) c c.track).2.isEmpty) = true ∧
      tracks (BtcPolicy.Exhibits.RungRelease.runR 18).2 1 = [{ latch := 2, floor := 3 }] ∧
      tracks (BtcPolicy.Exhibits.RungRelease.runR 19).2 1 = [{ latch := 2, floor := 3 }]) ∧
    ∀ c' ∈ ((Federation.apply Kernel.current (BtcPolicy.Exhibits.RungRelease.runR 18).2.fed
        (.process 1 { BtcPolicy.Kernel.RegistrationCases.envFire with ladder := [] } .ladderPass)).worlds 1).node.cands,
      ∃ c ∈ ((BtcPolicy.Exhibits.RungRelease.runR 18).2.fed.worlds 1).node.cands,
        BtcPolicy.Retained.reg c = BtcPolicy.Retained.reg c' ∧
        ((BtcPolicy.Ladder.release BtcPolicy.Exhibits.Integrated.ilc
          (BtcPolicy.RungRelease.readAt (BtcPolicy.Exhibits.RungRelease.runR 18).2
            (BtcPolicy.Exhibits.RungRelease.runR 18).1 1 c) c c.track).2 = [] → c'.track = c.track) := by
  refine ⟨by decide +kernel, ?_⟩
  have h : BtcPolicy.RungRelease.admits BtcPolicy.Exhibits.Integrated.ilc honest
      (BtcPolicy.Exhibits.RungRelease.runR 18).2 (BtcPolicy.Exhibits.RungRelease.runR 18).1
      (.fed (.process 1 { BtcPolicy.Kernel.RegistrationCases.envFire with ladder := [] } .ladderPass)) = true :=
    BtcPolicy.Exhibits.RungRelease.refused_rung_on_run.2.2.2
  exact BtcPolicy.Retained.quiet_keeps (lc := BtcPolicy.Exhibits.Integrated.ilc)
    (st := (BtcPolicy.Exhibits.RungRelease.runR 18).2) (T := (BtcPolicy.Exhibits.RungRelease.runR 18).1) (i := 1) h
    Kernel.current

end BtcPolicy.Exhibits.Retained

namespace BtcPolicy.Exhibits.ReceiptExpiry
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.FedSilence BtcPolicy.ReceiptExpiry
open BtcPolicy.Kernel.RegistrationCases (env0 envAt)
open BtcPolicy.Exhibits.Ingress (ctx0 req0 sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (fed0 honest part envHeld)

/-! ### Receipt-time expiry on the ledgered run

Research task `bps-8bbx.1`. The request `Exhibits.Ingress.req0`, whose pair `Ingress.check` computes, on three honest
nodes with Hot ledgers (`FedSilence.LFed`), each delivered partial taken through `ReceiptExpiry.sysRecv`. Its
signed expiry is 200. -/

def F0 : LFed := { fed := fed0, leds := fun _ => [] }
def cfg : Config := { cap := 1000, window := 600 }
/-- Node `i` takes the checked pair, under the duress PIN when `d`. -/
def accS (i : Nat) (d : Bool) : Federation.Step := .process i env0 (.accept 10 d (Wall.sample 200) sp0 es0)
/-- Wall 200, the expiry itself; wall 201, one second past it. -/
def envEq : Env := envAt 200 195
def envLate : Env := envAt 201 196
/-- A holder decision at wall 150; a receipt at wall 260. -/
def envD : Env := envAt 150 150
def envW : Env := envAt 260 255

/-- All three nodes take the pair under the normal PIN. Nodes 1 and 2 exchange relays, decide at wall 50 (the
Escape's inert window closes at 135) and release the hot spend at their fire passes. Then, at node 3: node 2's
partial at the expiry, twice (steps 10, 11), and node 1's one second past it, twice (steps 12, 14); between them
node 2's partial at node 1 past the expiry (step 13). Node 2 then prunes and receives node 1's partial (15, 16). -/
def ord : List Federation.Step :=
  [accS 1 false, accS 2 false, accS 3 false, .emit 1 10, .emit 2 10,
   .deliver 1 env0 ⟨2, 10⟩, .deliver 2 env0 ⟨1, 10⟩, .process 1 envHeld .firePass, .process 2 envHeld .firePass,
   .deliverPartial 3 envEq (part sp0 2), .deliverPartial 3 envEq (part sp0 2),
   .deliverPartial 3 envLate (part sp0 1), .deliverPartial 1 envLate (part sp0 2),
   .deliverPartial 3 envLate (part sp0 1),
   .process 2 envLate .prune, .deliverPartial 2 envLate (part sp0 1)]

/-- The run after the first `n` steps of a schedule. -/
def runAt (ss : List Federation.Step) (n : Nat) : LFed := xrun Ledger.current cfg Kernel.current F0 (ss.take n)
/-- Node `i`'s lookup of `cid` at `env`, after the first `n` steps. -/
def lookAt (ss : List Federation.Step) (n i : Nat) (env : Env) (cid : Nat) : Lookup :=
  lookup env ((runAt ss n).fed.worlds i).node cid
def resident (F : LFed) (i cid : Nat) : Bool := (F.fed.worlds i).node.cands.any (·.id == cid)
/-- The exposure bits of node `i`'s rows under `cid`: `[]` when it charges nothing. -/
def charged (F : LFed) (i cid : Nat) : List Bool := ((F.leds i).filter (·.cid == cid)).map (·.exposed)

/-- **Eviction, answer and refund from one receipt** (`NCH-24`, `POL-18`). The pair is `Ingress.check`'s, and every
step of `ord` is admitted. Node 3 took the hot spend and never released it. At step 12 the wall reads 201: its
lookup finds the spend expired with no open Escape window beside it, answers `UNKNOWN_CANDIDATE`, and evicts it,
and the unexposed charge it held goes in the same step. Its Escape, not looked up, stays resident; the partial
inventory is unchanged. -/
@[req "NCH-24"]
theorem evicts_and_refunds :
    Ingress.check ctx0 true req0 = .accepted sp0 es0 ∧
    xlegal Ledger.current cfg Kernel.current honest F0 ord = true ∧
    lookAt ord 11 3 envLate sp0.id = .expired ∧
    answer envLate ((runAt ord 11).fed.worlds 3).node sp0.id = .unknownCandidate ∧
    resident (runAt ord 11) 3 sp0.id = true ∧ charged (runAt ord 11) 3 sp0.id = [false] ∧
    resident (runAt ord 12) 3 sp0.id = false ∧ charged (runAt ord 12) 3 sp0.id = [] ∧
    resident (runAt ord 12) 3 es0.id = true ∧
    (runAt ord 12).fed.parts = (runAt ord 11).fed.parts := by
  decide +kernel

/-- **At the expiry the candidate is unexpired** (`SPN-41`: "The last authorized second is `now == expiry`"). At
wall 200 node 3's lookup is live, and node 2's partial is stored on the spend; the charge stays. -/
@[req "SPN-41"]
theorem equality_unexpired :
    lookAt ord 9 3 envEq sp0.id = .live ∧
    ((runAt ord 10).fed.worlds 3).node.cands.map (·.heldSigners) = [[3, 2], [3]] ∧
    charged (runAt ord 10) 3 sp0.id = [false] := by
  decide +kernel

/-- **Duplicates change nothing** (`NCH-25`). The second copy of a stored partial (step 11) and the second copy
reaching an evicted candidate (step 14) leave node 3's registry and ledger as the first copies left them. -/
@[req "NCH-25"]
theorem duplicate_receipts_unchanged :
    ((runAt ord 11).fed.worlds 3).node = ((runAt ord 10).fed.worlds 3).node ∧
    (runAt ord 11).leds 3 = (runAt ord 10).leds 3 ∧
    ((runAt ord 14).fed.worlds 3).node = ((runAt ord 13).fed.worlds 3).node ∧
    (runAt ord 14).leds 3 = (runAt ord 13).leds 3 := by
  decide +kernel

/-- **An exposed charge stands, and so does the authority** (`POL-18`: "A partial that has left the node is
finalizable authority in `t − 1` compromised hands and meters exactly as a broadcast does"). Node 1 released its
partial at its fire pass. Past the expiry its lookup evicts the spend, yet its charge stays, still exposed. Both
released partials on the spend stay in the inventory, and node 1's own exposure row stays first in its history. -/
@[req "POL-18"]
theorem exposed_charge_stands :
    lookAt ord 12 1 envLate sp0.id = .expired ∧
    resident (runAt ord 13) 1 sp0.id = false ∧ charged (runAt ord 12) 1 sp0.id = [true] ∧
    charged (runAt ord 13) 1 sp0.id = [true] ∧
    ((runAt ord 13).fed.parts.filter (·.cid == sp0.id)).map (·.signer) = [1, 2] ∧
    ((runAt ord 13).fed.worlds 1).exposure.take 1 = ((runAt ord 12).fed.worlds 1).exposure.take 1 := by
  decide +kernel

/-- **A candidate already pruned** (`NCH-24`: "the candidate exists, else `UNKNOWN_CANDIDATE`"). Node 2's prune pass
collected the spend; the partial that reaches it next finds nothing, and its registry and ledger are as the prune
pass left them. The exposed charge stands there too. -/
@[req "NCH-24"]
theorem pruned_answers_unknown :
    resident (runAt ord 15) 2 sp0.id = false ∧ lookAt ord 15 2 envLate sp0.id = .unknown ∧
    ((runAt ord 16).fed.worlds 2).node = ((runAt ord 15).fed.worlds 2).node ∧
    (runAt ord 16).leds 2 = (runAt ord 15).leds 2 ∧ charged (runAt ord 16) 2 sp0.id = [true] := by
  decide +kernel

/-- Nodes 1 and 2 take the pair under one PIN and decide at wall 150, which writes the Escape's window to close
past the expiry (390 under the normal PIN, 290 under the duress PIN); signer 3's key is copied and its partials on
both candidates enter the inventory. -/
def slot (d : Bool) : List Federation.Step :=
  [accS 1 d, accS 2 d, .emit 1 10, .emit 2 10, .deliver 1 envD ⟨2, 10⟩, .deliver 2 envD ⟨1, 10⟩,
   .extract 3, .forge (part sp0 3), .forge (part es0 3)]

/-- **The delayed slot, under both PINs** (`SPN-41`: "the exemption is granted to the normal PIN's inert slot
too"). Under either PIN, at wall 260, past the expiry, node 1's lookups of the spend and of its Escape are live:
the Escape is not broadcast and its window is open. Delivering both partials there is admitted. At wall 400 the
window has closed and the spend's lookup evicts. Node 1 is armed exactly under the duress PIN. -/
@[req "SPN-41"]
theorem delayed_slot_both_pins :
    [false, true].all (fun d =>
      xlegal Ledger.current cfg Kernel.current honest F0 (slot d ++ [.deliverPartial 1 envW (part sp0 3),
        .deliverPartial 1 envW (part es0 3)]) &&
      (((runAt (slot d) 9).fed.worlds 1).node.armed == d) &&
      lookAt (slot d) 9 1 envW sp0.id == .live && lookAt (slot d) 9 1 envW es0.id == .live &&
      lookAt (slot d) 9 1 (envAt 400 395) sp0.id == .expired) = true := by
  decide +kernel

/-- **The rung lifecycle is untouched** (`DUR-29`). On `Exhibits.Lifecycle.lifecycle_run`'s federation trace no
delivered partial meets an expired lookup, so `ReceiptExpiry.receive` is `Kernel.receivePartial` at every delivery
of that run (`ReceiptExpiry.receive_unexpired`). -/
@[req "DUR-29"]
theorem lifecycle_unevicted : Unevicted (BtcPolicy.Exhibits.Lifecycle.fedOf 23) = true := by
  decide +kernel

/-- **The observer sees the answer** (`NCH-24`). From the same state, node 1's partial reaching node 3 at wall 200
is observed as found, and at wall 201 as `UNKNOWN_CANDIDATE`. -/
@[req "NCH-24"]
theorem answer_detects_expiry :
    (xfobs Silence.current Ledger.current cfg Kernel.current [1, 2, 3] (runAt ord 11)
      (.deliverPartial 3 envEq (part sp0 1))).answer = some (3, 1, .found) ∧
    (xfobs Silence.current Ledger.current cfg Kernel.current [1, 2, 3] (runAt ord 11)
      (.deliverPartial 3 envLate (part sp0 1))).answer = some (3, 1, .unknownCandidate) := by
  decide +kernel

end BtcPolicy.Exhibits.ReceiptExpiry

namespace BtcPolicy.Exhibits.ReleaseQuota
open BtcPolicy.Clocks BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Kernel.RegistrationCases (envFire env0)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest v st0 st0_fresh coin)
open BtcPolicy.Exhibits.CommonRun (inst onBook readFirst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (esR fire lad withMedian vm vm2 rrow)
open BtcPolicy.Exhibits.Retained (tracks)

/-! ### `SPN-38`'s quota accounting on the runs

Research task `bps-8bbx.4` (`BtcPolicy.ReleaseQuota`): what one pass emits, consumes and leaves as the release floor,
read off the release the run itself computes. Each summary is a ladder pass's account for each Escape-role record of
the acting node (`ReleaseQuota.passAccount`): the cursor's interval, the rungs listed, the slots consumed
(`ReleaseQuota.consumed`) and the release state after the pass; `added` is the rows the step adds to the partial
inventory under a commitment. The runs are `Exhibits.Lifecycle.lifecycle_run`'s and runs of `RungRelease`'s and
`LadderRelease`'s refinements on `Exhibits.RungRelease`'s request, at a quota of 3 (one rung affordable per pass at
one input) or `Exhibits.Integrated.ilc`'s 600. -/

/-- Node `i`'s ladder pass at step `n` of a lifecycle schedule: its account for each Escape-role record, as the
interval, the rungs, the slots consumed and the release state after it; `[]` at any other step. -/
def lifeAccounts (ss : List RungAssembly.Step) (n i : Nat) : List (Option (Nat × Nat) × List Nat × Nat × Track) :=
  match ss.getD n (.base (.observe 0 BtcPolicy.Exhibits.Lifecycle.fv)) with
  | .base (.fed (.process j env .ladderPass)) =>
    if j = i then
      (((BtcPolicy.Exhibits.Lifecycle.runOf ss n).2.cs.sw.fed.worlds i).node.cands.filter (·.isEscape)).map fun c =>
        let x := BtcPolicy.ReleaseQuota.passAccount BtcPolicy.Exhibits.Lifecycle.flc Kernel.current
          (BtcPolicy.Exhibits.Lifecycle.runOf ss n).2.cs.sw
          (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (BtcPolicy.Exhibits.Lifecycle.runOf ss n).1)) i env c
        (x.interval, x.rungs, BtcPolicy.ReleaseQuota.consumed x, x.track)
    else []
  | _ => []

/-- The same over a sweep schedule and its run. -/
def accountsAt (lc : Ladder.Cfg) (sched : List Sweep.Step) (run : Nat → Sweep.Trace × Sweep.State) (n i : Nat) :
    List (Option (Nat × Nat) × List Nat × Nat × Track) :=
  match sched.getD n (.chain vm) with
  | .fed (.process j env .ladderPass) =>
    if j = i then
      (((run n).2.fed.worlds i).node.cands.filter (·.isEscape)).map fun c =>
        let x := BtcPolicy.ReleaseQuota.passAccount lc Kernel.current (run n).2 (run n).1 i env c
        (x.interval, x.rungs, BtcPolicy.ReleaseQuota.consumed x, x.track)
    else []
  | _ => []

/-- The rows step `n` of a run adds to the partial inventory under commitment `cid`. -/
def added (run : Nat → Sweep.Trace × Sweep.State) (n cid : Nat) : List Exp :=
  ((run (n + 1)).2.fed.parts.drop (run n).2.fed.parts.length).filter (·.cid == cid)

set_option synthInstance.maxSize 4096 in
/-- **The lifecycle run's accounts** (`SPN-38`). On `Exhibits.Lifecycle.lifecycle_run`, unchanged, node 2's ladder
passes (steps 7 and 15) and node 1's (steps 9 and 18) each compute one interval of one rung: `[1, 1]` at the
observation `fv`, where the base is inadmissible and `a = 1`, then `[2, 2]` at `fvRes`, from the floor 2 the first
pass left. Each lists its interval's rung, consumes one slot and sets the floor past it; the release state the account
gives is the one the run records after the pass. -/
@[req "SPN-38"]
theorem lifecycle_accounts :
    lifeAccounts BtcPolicy.Exhibits.Lifecycle.whole 7 2 = [(some (1, 1), [1], 1, { latch := 1, floor := 2 })] ∧
      lifeAccounts BtcPolicy.Exhibits.Lifecycle.whole 9 1 = [(some (1, 1), [1], 1, { latch := 1, floor := 2 })] ∧
      tracks (BtcPolicy.Exhibits.Lifecycle.runAt 10).2.cs.sw 1 = [{ latch := 1, floor := 2 }] ∧
      lifeAccounts BtcPolicy.Exhibits.Lifecycle.whole 15 2 = [(some (2, 2), [2], 1, { latch := 2, floor := 3 })] ∧
      lifeAccounts BtcPolicy.Exhibits.Lifecycle.whole 18 1 = [(some (2, 2), [2], 1, { latch := 2, floor := 3 })] ∧
      tracks (BtcPolicy.Exhibits.Lifecycle.runAt 19).2.cs.sw 1 = [{ latch := 2, floor := 3 }] := by
  decide +kernel

/-- `SPN-38`'s quota at 3: `rung_budget = max(3 − 2, 1) = 1`, one rung affordable at one input. -/
def qlc : Ladder.Cfg := { ilc with quota := 3 }

/-- Nodes 1 and 2 take the coerced request with the Escape `c`, exchange relays, and decide. -/
def pre (c : Cand) : List Sweep.Step :=
  [.fed (.process 1 env0 (.accept 10 true (Wall.sample 200) sp0 c)),
   .fed (.process 2 env0 (.accept 10 true (Wall.sample 200) sp0 c)), .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩)]

/-- `Exhibits.RungRelease.esR`'s request; the truth moves to the vault at a median of 200; both nodes fire; node 1
takes four ladder passes at that reading. -/
def qraw : List Sweep.Step := pre esR ++ [.chain vm2, fire 1, fire 2, lad 1, lad 1, lad 1, lad 1]
def qsched : List Sweep.Step :=
  RungRelease.fill qlc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm qraw).map onBook)
def runQ (n : Nat) : Sweep.Trace × Sweep.State := Sweep.record Kernel.current [] (st0 (inst vm)).sw (qsched.take n)

set_option synthInstance.maxSize 4096 in
/-- **A quota smaller than the available rungs** (`SPN-38`). At a quota of 3 one rung is affordable; node 1's verdict
at the median of 200 latches rung 2 over the base and two rungs, and its first ladder pass (step 11), after the fire
pass released the base and set the floor to 1, computes the interval `[1, 1]`,
`U = min(latch, F + affordable_rungs − 1) = 1`: it lists rung 1, consumes its one slot, sets the floor to 2 and
queues `r1`'s row. -/
@[req "SPN-38"]
theorem quota_short :
    Cursor.affordableRungs qlc.quota es0.tx.inputs.length = 1 ∧ esR.ladder.length = 3 ∧
      accountsAt qlc qsched runQ 11 1 = [(some (1, 1), [1], 1, { latch := 2, floor := 2 })] ∧
      added runQ 11 es0.id = [rrow Exhibits.Ladder.r1] := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
/-- **Cumulative progress over passes** (`SPN-38`, `DUR-27`). The schedule is a legal run of `RungRelease`'s
refinement. The fire passes queue the base rows of nodes 1 and 2 and set their floors to 1; node 1's four ladder
passes compute `[1, 1]`, `[2, 2]` and then no interval twice (`F = 3 > U = 2`), floors 2, 3, 3 and 3, one slot each
at the first two and none after; rung rows come from the first two, `r1`'s then `r2`'s, and nothing is queued
again. -/
@[req "SPN-38"]
theorem cumulative_passes :
    RungRelease.legal qlc Kernel.current honest [] (st0 (inst vm)).sw qsched = true ∧ qsched.length = 15 ∧
      added runQ 8 es0.id = [BtcPolicy.Exhibits.EndToEnd.part es0 1] ∧
      added runQ 10 es0.id = [BtcPolicy.Exhibits.EndToEnd.part es0 2] ∧
      accountsAt qlc qsched runQ 11 1 = [(some (1, 1), [1], 1, { latch := 2, floor := 2 })] ∧
      accountsAt qlc qsched runQ 12 1 = [(some (2, 2), [2], 1, { latch := 2, floor := 3 })] ∧
      accountsAt qlc qsched runQ 13 1 = [(none, [], 0, { latch := 2, floor := 3 })] ∧
      accountsAt qlc qsched runQ 14 1 = [(none, [], 0, { latch := 2, floor := 3 })] ∧
      added runQ 11 es0.id = [rrow Exhibits.Ladder.r1] ∧ added runQ 12 es0.id = [rrow Exhibits.Ladder.r2] ∧
      added runQ 13 es0.id = [] ∧ added runQ 14 es0.id = [] ∧
      tracks (runQ 15).2 1 = [{ latch := 2, floor := 3 }] := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
/-- **The fire pass moves the floor** (`SPN-38`: "Only a pass that released at least one rung MUST set
`release_floor = U + 1`"). On the quota run, at a quota of 3 where one rung is affordable, node 1's fire pass
(step 8) sends the base's row, marks the base released and sets the floor to `U + 1 = 1`, the latch untouched; node 1's
next ladder pass (step 11) computes an interval starting at 1, spends no slot on rung 0, and lists rung 1. -/
@[req "SPN-38"]
theorem fire_floor :
    Cursor.affordableRungs qlc.quota es0.tx.inputs.length = 1 ∧
      tracks (runQ 8).2 1 = [{}] ∧
      added runQ 8 es0.id = [BtcPolicy.Exhibits.EndToEnd.part es0 1] ∧
      (((runQ 9).2.fed.worlds 1).node.cands.filter (·.isEscape)).map (fun c => (c.released, c.track)) =
        [(true, { floor := 1 })] ∧
      (accountsAt qlc qsched runQ 11 1).map (fun a => (a.1, a.2.1, a.2.2.1)) = [(some (1, 1), [1], 1)] := by
  decide +kernel

/-- The quota run is a reachable execution of `RungRelease`'s refinement. -/
theorem quota_run_execution : RungRelease.Execution qlc Kernel.current honest (runQ 15).1 (runQ 15).2 := by
  have hx := RungRelease.execution_of_legal (.init _ (st0_fresh (inst vm)).1) cumulative_passes.1
  have hl : qsched.take 15 = qsched := List.take_of_length_le (Nat.le_of_eq cumulative_passes.2.1)
  simpa [runQ, hl] using hx

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
/-- **The count theorem on the run** (`SPN-38`, `NCH-23`). At node 1's second ladder pass of the quota run
(step 12), which `RungRelease.ladder_available` admits with the computed list, `ReleaseQuota.pass_count`'s premise
holds for node 1's Escape (both rungs spend the base's one input), so the rows under its commitment number at most
`consumed × inputs`, within `rung_budget`; there the run's own count is 1, one slot consumed at one input. -/
@[req "SPN-38"]
theorem count_on_run :
    let st := (runQ 12).2
    let T := (runQ 12).1
    let env : Env := { envFire with ladder := RungRelease.listed qlc st T 1 }
    qsched.getD 12 (.chain vm) = .fed (.process 1 env .ladderPass) ∧
      (((st.fed.worlds 1).node.cands.filter (·.isEscape)).map fun c =>
        (((step Kernel.current env (st.fed.worlds 1) .ladderPass).2.filter
          (BtcPolicy.ReleaseQuota.under c.id)).length,
         BtcPolicy.ReleaseQuota.consumed (BtcPolicy.ReleaseQuota.passAccount qlc Kernel.current st T 1 env c),
         c.tx.inputs.length)) = [(1, 1, 1)] ∧
      ∀ c ∈ (st.fed.worlds 1).node.cands, c.isEscape = true →
        ((step Kernel.current env (st.fed.worlds 1) .ladderPass).2.filter
            (BtcPolicy.ReleaseQuota.under c.id)).length ≤
          BtcPolicy.ReleaseQuota.consumed (BtcPolicy.ReleaseQuota.passAccount qlc Kernel.current st T 1 env c) *
            c.tx.inputs.length ∧
        BtcPolicy.ReleaseQuota.consumed (BtcPolicy.ReleaseQuota.passAccount qlc Kernel.current st T 1 env c) *
            c.tx.inputs.length ≤ Cursor.rungBudget qlc.quota := by
  intro st T env
  have hd : qsched.getD 12 (.chain vm) = .fed (.process 1 env .ladderPass) ∧
      (((st.fed.worlds 1).node.cands.filter (·.isEscape)).map fun c =>
        (((step Kernel.current env (st.fed.worlds 1) .ladderPass).2.filter
          (BtcPolicy.ReleaseQuota.under c.id)).length,
         BtcPolicy.ReleaseQuota.consumed (BtcPolicy.ReleaseQuota.passAccount qlc Kernel.current st T 1 env c),
         c.tx.inputs.length)) = [(1, 1, 1)] ∧
      (PreRelease.escapeIds (st.fed.worlds 1).node).Nodup ∧
      ((st.fed.worlds 1).node.cands.all fun c =>
        !c.isEscape || c.above.all fun g => g.tx.inputs.length == c.tx.inputs.length) = true := by
    decide +kernel
  refine ⟨hd.1, hd.2.1, fun c hc hesc => ?_⟩
  have ha := RungRelease.ladder_available qlc honest st T (i := 1) (by decide) hd.2.2.1 envFire
  have hin : ∀ g ∈ c.above, g.tx.inputs.length = c.tx.inputs.length := by
    have h := List.all_eq_true.1 hd.2.2.2 c hc
    simp only [hesc, Bool.not_true, Bool.false_or, List.all_eq_true, beq_iff_eq] at h
    exact h
  obtain ⟨h1, h2, -⟩ := BtcPolicy.ReleaseQuota.pass_count ha Kernel.current hc hesc hin
  exact ⟨h1, h2⟩

/-- `Exhibits.RungRelease.esR` with `r1` replaced by `Exhibits.Ladder.r1low`, which fails coverage at the vault. -/
def esLow : Cand := { es0 with above := [⟨Exhibits.Ladder.r1low, 11⟩, Exhibits.Ladder.R2] }
def lraw : List Sweep.Step := pre esLow ++ [.chain vm2, fire 1, fire 2, lad 1, lad 1]
def lsched : List Sweep.Step :=
  RungRelease.fill ilc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm lraw).map onBook)
def runL (n : Nat) : Sweep.Trace × Sweep.State := Sweep.record Kernel.current [] (st0 (inst vm)).sw (lsched.take n)

set_option synthInstance.maxSize 4096 in
/-- **A refused rung inside the interval** (`SPN-38`, `DUR-27`). On a legal run of `RungRelease`'s refinement, node 1's
first ladder pass at a median of 200 latches rung 2 and, the fire pass having released the base and set the floor to
1, computes the interval `[1, 2]`; `r1low`, rung 1, is refused at that attempt. It is listed to nobody, yet its slot
is passed: the pass lists rung 2, consumes two slots and sets the floor to `U + 1 = 3`, and its only row is `r2`'s.
The next pass computes no interval. -/
@[req "SPN-38"]
theorem refused_inside_interval :
    RungRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw lsched = true ∧ lsched.length = 13 ∧
      ((((runL 11).2.fed.worlds 1).node.cands.filter (·.isEscape)).map fun c =>
        match (RungRelease.readAt (runL 11).2 (runL 11).1 1 c).ob with
        | none => []
        | some b => (Ladder.attempt ilc.pre (RungRelease.readAt (runL 11).2 (runL 11).1 1 c) b c c.track.latch).adm) =
        [[true, false, true]] ∧
      accountsAt ilc lsched runL 11 1 = [(some (1, 2), [2], 2, { latch := 2, floor := 3 })] ∧
      added runL 11 es0.id = [rrow Exhibits.Ladder.r2] ∧
      accountsAt ilc lsched runL 12 1 = [(none, [], 0, { latch := 2, floor := 3 })] ∧ added runL 12 es0.id = [] := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
/-- **Nothing released, nothing moved** (`SPN-38`). On `Exhibits.RungRelease.rung_on_run`'s run, node 1's ladder pass
at step 18 reads the large coin, where every rung is refused: its account computes no interval, lists nothing,
consumes nothing and keeps latch 2 and floor 3, and the step adds no row. -/
@[req "SPN-38"]
theorem nothing_released :
    accountsAt ilc BtcPolicy.Exhibits.RungRelease.sched BtcPolicy.Exhibits.RungRelease.runR 18 1 =
        [(none, [], 0, { latch := 2, floor := 3 })] ∧
      added BtcPolicy.Exhibits.RungRelease.runR 18 es0.id = [] ∧
      tracks (BtcPolicy.Exhibits.RungRelease.runR 19).2 1 = [{ latch := 2, floor := 3 }] := by
  decide +kernel

/-- A two-input Escape over the base's coin and a second coin of 1, retaining `r1` and `r2`. -/
def esW : Cand :=
  { es0 with tx := { es0.tx with inputs := [coin, 77] }, above := [Exhibits.Ladder.R1, Exhibits.Ladder.R2] }
def vW : Backend := withMedian { v with confirmed := [(coin, 100), (77, 1)] } 200
def wraw : List Sweep.Step := pre esW ++ [.chain vW, fire 1, lad 1]
def wsched (lc : Ladder.Cfg) : List Sweep.Step :=
  LadderRelease.fill lc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm wraw).map onBook)
def runW (lc : Ladder.Cfg) (n : Nat) : Sweep.Trace × Sweep.State :=
  Sweep.record Kernel.current [] (st0 (inst vm)).sw ((wsched lc).take n)

/-- The rows of a run's partial inventory under `es0`'s commitment on the base's own transaction. -/
def baseRows (run : Nat → Sweep.Trace × Sweep.State) (n : Nat) : List Exp :=
  (run n).2.fed.parts.filter fun x => x.cid == es0.id && x.msg.1 == es0.tx.id

set_option synthInstance.maxSize 4096 in
/-- **The base under the quota** (`SPN-38`, `DUR-21`). With a two-input base at a quota of 3, `rung_budget = 1` and
`affordable_rungs = 0`. On a legal run of `LadderRelease`'s refinement, the Escape is starved at node 1's fire pass
(step 8, `LadderRelease.starvedAt`), which queues nothing for it; its ladder pass (step 9) computes no interval,
lists nothing and keeps the release state at zero, the base unreleased; and the run's inventory holds no row under
the Escape's commitment: `SPN-38`'s "If `affordable_rungs = 0`, release nothing" holds of the base as of the
cursor. At a quota of 600 the same fire pass queues the base's row, one per input, and sets the floor to 1, and the
same ladder pass lists both rungs above it. -/
@[req "SPN-38"]
theorem base_metered :
    Cursor.affordableRungs qlc.quota esW.tx.inputs.length = 0 ∧
      LadderRelease.legal qlc Kernel.current honest [] (st0 (inst vm)).sw (wsched qlc) = true ∧
      (wsched qlc).length = 10 ∧
      es0.id ∈ LadderRelease.starvedAt qlc (runW qlc 8).2 (runW qlc 8).1 1 ∧
      added (runW qlc) 8 es0.id = [] ∧
      accountsAt qlc (wsched qlc) (runW qlc) 9 1 = [(none, [], 0, {})] ∧ added (runW qlc) 9 es0.id = [] ∧
      (((runW qlc 10).2.fed.worlds 1).node.cands.filter (·.isEscape)).map (fun c => (c.track, c.released)) =
        [({}, false)] ∧
      (runW qlc 10).2.fed.parts.filter (·.cid == es0.id) = [] ∧
      LadderRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw (wsched ilc) = true ∧
      (added (runW ilc) 8 es0.id).map (fun x => (x.signer, x.input, x.msg.1 == es0.tx.id)) =
        [(1, 0, true), (1, 1, true)] ∧
      accountsAt ilc (wsched ilc) (runW ilc) 9 1 = [(some (1, 2), [1, 2], 2, { latch := 2, floor := 3 })] := by
  decide +kernel

/-- `wraw` with each fire pass carrying the base's verdict alone and no account (`RungRelease.fill`). -/
def rwsched (lc : Ladder.Cfg) : List Sweep.Step :=
  RungRelease.fill lc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm wraw).map onBook)
def runRW (lc : Ladder.Cfg) (n : Nat) : Sweep.Trace × Sweep.State :=
  Sweep.record Kernel.current [] (st0 (inst vm)).sw ((rwsched lc).take n)

set_option synthInstance.maxSize 4096 in
/-- **The base outside the quota, one layer down** (`SPN-38`, `DUR-21`). `base_metered`'s history on
`RungRelease`'s refinement, whose fire pass is not bound to the account: at a quota of 3 node 1's fire pass
(step 8) still queues the base's row, one per input, marks the base released and sets the floor to 1, and its
ladder pass (step 9) computes no interval, lists nothing and keeps that release state. That refinement leaves the base outside the
quota; `LadderRelease`'s binding of `Env.starved` is what meters it. -/
@[req "SPN-38"]
theorem base_separate :
    Cursor.affordableRungs qlc.quota esW.tx.inputs.length = 0 ∧
      RungRelease.legal qlc Kernel.current honest [] (st0 (inst vm)).sw (rwsched qlc) = true ∧
      (rwsched qlc).length = 10 ∧
      (added (runRW qlc) 8 es0.id).map (fun x => (x.signer, x.input, x.msg.1 == es0.tx.id)) =
        [(1, 0, true), (1, 1, true)] ∧
      accountsAt qlc (rwsched qlc) (runRW qlc) 9 1 = [(none, [], 0, { floor := 1 })] ∧
        added (runRW qlc) 9 es0.id = [] ∧
      (((runRW qlc 10).2.fed.worlds 1).node.cands.filter (·.isEscape)).map (fun c => (c.track, c.released)) =
        [({ floor := 1 }, true)] := by
  decide +kernel

/-- `Exhibits.RungRelease.esR`'s request; node 1 reads the vault at a median of 100 and takes a ladder pass before
any fire pass, then fires, takes a second ladder pass, and after the truth moves to a median of 200 fires and takes a
ladder pass again. -/
def braw : List Sweep.Step :=
  pre esR ++ [.observe 1 vm, lad 1, fire 1, lad 1, .chain vm2, fire 1, lad 1]
def bsched (lc : Ladder.Cfg) : List Sweep.Step :=
  LadderRelease.fill lc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm braw).map onBook)
def runBL (lc : Ladder.Cfg) (n : Nat) : Sweep.Trace × Sweep.State :=
  Sweep.record Kernel.current [] (st0 (inst vm)).sw ((bsched lc).take n)

set_option synthInstance.maxSize 4096 in
/-- **The base by the ladder** (`SPN-38`). On a legal run of `LadderRelease`'s refinement at a quota of 600, node 1's
ladder pass before any fire pass (step 7) lists rung 0 with rung 1: it queues the base's row and `r1`'s and marks
the base released, and node 1's later fire passes (steps 9 and 13) queue nothing for it. In the other order, on
`base_metered`'s run at the same quota, the fire pass (step 8) queues the base's rows and sets the floor to 1, and
the ladder pass (step 9) lists the rungs above the base, spends no slot on rung 0 and queues only the rungs' rows. -/
@[req "SPN-38"]
theorem base_by_ladder :
    LadderRelease.legal ilc Kernel.current honest [] (st0 (inst vm)).sw (bsched ilc) = true ∧
      (bsched ilc).length = 15 ∧
      accountsAt ilc (bsched ilc) (runBL ilc) 7 1 = [(some (0, 1), [0, 1], 2, { latch := 1, floor := 2 })] ∧
      added (runBL ilc) 7 es0.id = [BtcPolicy.Exhibits.EndToEnd.part es0 1, rrow Exhibits.Ladder.r1] ∧
      (((runBL ilc 8).2.fed.worlds 1).node.cands.filter (·.isEscape)).map (·.released) = [true] ∧
      added (runBL ilc) 9 es0.id = [] ∧ added (runBL ilc) 13 es0.id = [] ∧
      (accountsAt ilc (wsched ilc) (runW ilc) 9 1).map (·.2.1) = [[1, 2]] ∧
      (added (runW ilc) 9 es0.id).all (fun x => x.msg.1 != es0.tx.id) = true := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
/-- **Repeated passes queue the base once** (`SPN-38`, `ReleaseQuota.base_once_paths`). `base_by_ladder`'s history at
a quota of 3, a legal run of `LadderRelease`'s refinement: node 1's three ladder passes list `[0]`, `[1]` and `[2]`,
one slot each, and its two fire passes queue nothing; over the whole run the inventory holds one row on the base's
own transaction. -/
@[req "SPN-38"]
theorem repeat_passes :
    LadderRelease.legal qlc Kernel.current honest [] (st0 (inst vm)).sw (bsched qlc) = true ∧
      (accountsAt qlc (bsched qlc) (runBL qlc) 7 1).map (·.2.1) = [[0]] ∧
      (accountsAt qlc (bsched qlc) (runBL qlc) 10 1).map (·.2.1) = [[1]] ∧
      (accountsAt qlc (bsched qlc) (runBL qlc) 14 1).map (·.2.1) = [[2]] ∧
      added (runBL qlc) 9 es0.id = [] ∧ added (runBL qlc) 13 es0.id = [] ∧
      baseRows (runBL qlc) 15 = [BtcPolicy.Exhibits.EndToEnd.part es0 1] := by
  decide +kernel

/-- `esW` with no rung above its base: two inputs. -/
def esN : Cand := { esW with above := [] }
/-- The request with the Escape `c`; the truth moves to `b`; node 1 fires and takes a ladder pass. -/
def oraw (c : Cand) (b : Backend) : List Sweep.Step := pre c ++ [.chain b, fire 1, lad 1]
def osched (c : Cand) (b : Backend) : List Sweep.Step :=
  LadderRelease.fill qlc Kernel.current [] (st0 (inst vm)).sw ((readFirst vm (oraw c b)).map onBook)
def runO (c : Cand) (b : Backend) (n : Nat) : Sweep.Trace × Sweep.State :=
  Sweep.record Kernel.current [] (st0 (inst vm)).sw ((osched c b).take n)

set_option synthInstance.maxSize 4096 in
/-- **A base with no ladder** (`SPN-38`). At a quota of 3, on legal runs of `LadderRelease`'s refinement: the Escape
`es0`, one input and no rung, has one rung affordable, and node 1's fire pass (step 8) releases its base; `esN`, two
inputs and no rung, has none affordable, and nothing is released under its commitment. -/
@[req "SPN-38"]
theorem base_no_ladder :
    es0.above = [] ∧ Cursor.affordableRungs qlc.quota es0.tx.inputs.length = 1 ∧
      LadderRelease.legal qlc Kernel.current honest [] (st0 (inst vm)).sw (osched es0 vm2) = true ∧
      added (runO es0 vm2) 8 es0.id = [BtcPolicy.Exhibits.EndToEnd.part es0 1] ∧
      Cursor.affordableRungs qlc.quota esN.tx.inputs.length = 0 ∧
      LadderRelease.legal qlc Kernel.current honest [] (st0 (inst vm)).sw (osched esN vW) = true ∧
      (runO esN vW 10).2.fed.parts.filter (·.cid == es0.id) = [] := by
  decide +kernel

/-- A second Escape beside `es0`: node 1's record of `es0` at step 7 of `Exhibits.LadderPass`, under its own
commitment, registered as the Escape of its pair, one input on the coin 77. -/
def es1 : Cand :=
  let c := ((BtcPolicy.Exhibits.LadderPass.wAt 7 1).node.cands.find? (·.id == es0.id)).getD es0
  { c with id := c.id + 1, pair := c.pair.map (fun p => (p.1, c.id + 1)),
           tx := { c.tx with id := 902, inputs := [77] } }
/-- Node 1's world of `Exhibits.LadderPass`, both Escapes resident and due. -/
def wShared : World :=
  { BtcPolicy.Exhibits.LadderPass.wAt 7 1 with
    node := { (BtcPolicy.Exhibits.LadderPass.wAt 7 1).node with
      cands := (BtcPolicy.Exhibits.LadderPass.wAt 7 1).node.cands ++ [es1] } }

set_option synthInstance.maxSize 4096 in
/-- **Each account its own, the peer's shared** (`SPN-38`, `NCH-15`). Two Escapes at node 1, one input each at a quota
of 3: each has one rung affordable and an untouched cursor, so neither is starved and the fire pass's environment
starves nothing. One fire pass queues both bases, two rows to the same peers, above `rung_budget = 1`: an account kept
per candidate is not `NCH-15`'s shared rate limit. -/
@[req "SPN-38"]
theorem shared_peer :
    ((wShared.node.cands.filter (·.isEscape)).map fun c =>
        (Cursor.affordableRungs qlc.quota c.tx.inputs.length, c.released, c.track.floor)) =
      [(1, false, 0), (1, false, 0)] ∧
      envFire.starved = [] ∧
      (Federation.fanout wShared (step Kernel.current envFire wShared .firePass).2).map (fun x => (x.signer, x.cid)) =
        [(1, es0.id), (1, es1.id)] ∧
      Cursor.rungBudget qlc.quota = 1 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
/-- **Redelivery is not a release** (`SPN-38`). On `Exhibits.Lifecycle.lifecycle_run`, node 2's partial on `t1`
reaches node 1 at step 10, after node 1's pass listed rung 1: the inventory gains no row and node 1's release state
stays, and its next pass (step 18) lists rung 2 and not rung 1. On `Exhibits.Lifecycle.fresh_after_prune`'s run the
same partial reaches node 1 again at step 21, after node 1 was pruned and registered afresh: again no row and no
move. The fresh registration is a birth, so `ReleaseQuota.no_relist` does not reach across it, and node 1's pass of
the new lifetime (step 20) lists rung 1 again. -/
@[req "SPN-38"]
theorem redelivery_not_release :
    (BtcPolicy.Exhibits.Lifecycle.runAt 11).2.cs.sw.fed.parts = (BtcPolicy.Exhibits.Lifecycle.runAt 10).2.cs.sw.fed.parts ∧
      tracks (BtcPolicy.Exhibits.Lifecycle.runAt 11).2.cs.sw 1 = tracks (BtcPolicy.Exhibits.Lifecycle.runAt 10).2.cs.sw 1 ∧
      (BtcPolicy.Exhibits.Lifecycle.runAt 10).2.cs.sw.fed.parts.contains
        (BtcPolicy.Exhibits.Lifecycle.row 2 BtcPolicy.Exhibits.Lifecycle.t1) = true ∧
      (lifeAccounts BtcPolicy.Exhibits.Lifecycle.whole 18 1).map (·.2.1) = [[2]] ∧
      (BtcPolicy.Exhibits.Lifecycle.runOf BtcPolicy.Exhibits.Lifecycle.fresh 22).2.cs.sw.fed.parts =
        (BtcPolicy.Exhibits.Lifecycle.runOf BtcPolicy.Exhibits.Lifecycle.fresh 21).2.cs.sw.fed.parts ∧
      tracks (BtcPolicy.Exhibits.Lifecycle.runOf BtcPolicy.Exhibits.Lifecycle.fresh 22).2.cs.sw 1 =
        tracks (BtcPolicy.Exhibits.Lifecycle.runOf BtcPolicy.Exhibits.Lifecycle.fresh 21).2.cs.sw 1 ∧
      (BtcPolicy.Exhibits.Lifecycle.runOf BtcPolicy.Exhibits.Lifecycle.fresh 21).2.cs.sw.fed.parts.contains
        (BtcPolicy.Exhibits.Lifecycle.row 2 BtcPolicy.Exhibits.Lifecycle.t1) = true ∧
      (lifeAccounts BtcPolicy.Exhibits.Lifecycle.fresh 20 1).map (·.2.1) = [[1]] := by
  decide +kernel

/-- Node `i`'s environment at a sweep step, if the step is its ladder pass. -/
def ladderEnv (i : Nat) : Sweep.Step → Option Env
  | .fed (.process j env .ladderPass) => if j = i then some env else none
  | _ => none

theorem ladderEnv_some {i : Nat} {s : Sweep.Step} {env : Env} (h : ladderEnv i s = some env) :
    s = .fed (.process i env .ladderPass) := by
  unfold ladderEnv at h
  split at h
  · rename_i j env'
    split at h
    · rename_i hj
      simp only [Option.some.injEq] at h
      subst h hj
      rfl
    · simp at h
  · simp at h

/-- Node 1's account for record `c` at the sweep step `y` with history `T₁`, if `y` is node 1's ladder pass. -/
def accountAt (y : Sweep.State × Sweep.Step) (T₁ : Sweep.Trace) (c : Cand) : BtcPolicy.ReleaseQuota.Account :=
  match ladderEnv 1 y.2 with
  | some env => BtcPolicy.ReleaseQuota.passAccount BtcPolicy.Exhibits.Lifecycle.flc Kernel.current y.1 T₁ 1 env c
  | none => BtcPolicy.ReleaseQuota.quiet c.track

/-- **No re-release on the lifecycle run** (`SPN-38`). `ReleaseQuota.life_no_relist` applied to
`Exhibits.Lifecycle.lifecycle_run`: node 1's first ladder pass (step 9) lists rung 1 for its Escape, no step after
it up to step 18 births a record under the Escape's id at node 1, so every rung any account at step 18 lists for a
record under that id is above rung 1. The theorem's premises hold on the run. -/
@[req "SPN-38"]
theorem no_relist_on_run (env₂ : Env) :
    ∀ c ∈ ((BtcPolicy.Exhibits.Lifecycle.runAt 18).2.cs.sw.fed.worlds 1).node.cands,
      c.id = BtcPolicy.Exhibits.Lifecycle.esL.id →
      ∀ m' ∈ (BtcPolicy.ReleaseQuota.passAccount BtcPolicy.Exhibits.Lifecycle.flc Kernel.current
          (BtcPolicy.Exhibits.Lifecycle.runAt 18).2.cs.sw
          (BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (BtcPolicy.Exhibits.Lifecycle.runAt 18).1))
          1 env₂ c).rungs, 1 < m' := by
  intro c₂ hc₂ hk₂ m' hm'
  have hx : BtcPolicy.Lifecycle.Execution BtcPolicy.Exhibits.Lifecycle.fcfg Kernel.current honest
      (BtcPolicy.Exhibits.Lifecycle.runAt 18).1 (BtcPolicy.Exhibits.Lifecycle.runAt 18).2 := by
    have hl : BtcPolicy.Lifecycle.legal BtcPolicy.Exhibits.Lifecycle.fcfg Kernel.current honest []
        BtcPolicy.Exhibits.Lifecycle.stL (BtcPolicy.Exhibits.Lifecycle.whole.take 18) = true := by
      decide +kernel
    exact BtcPolicy.Lifecycle.execution_of_legal
      (.init BtcPolicy.Exhibits.Lifecycle.stL ⟨⟨(st0_fresh BtcPolicy.Exhibits.Lifecycle.fv).1, rfl, rfl⟩, rfl, rfl, rfl⟩) hl
  generalize hL : BtcPolicy.ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (BtcPolicy.Exhibits.Lifecycle.runAt 18).1) = L
    at hm'
  have hd : L.length = 16 ∧ (ladderEnv 1 (L.getD 6 ((BtcPolicy.Exhibits.Lifecycle.runAt 0).2.cs.sw, .chain vm)).2).isSome ∧
      ((L.take 6).all fun y => !BtcPolicy.Lifecycle.births Kernel.current y.1 y.2 1 BtcPolicy.Exhibits.Lifecycle.esL.id) ∧
      ((((L.getD 6 ((BtcPolicy.Exhibits.Lifecycle.runAt 0).2.cs.sw, .chain vm)).1.fed.worlds 1).node.cands.filter
        (·.id == BtcPolicy.Exhibits.Lifecycle.esL.id)).any fun c =>
          (accountAt (L.getD 6 ((BtcPolicy.Exhibits.Lifecycle.runAt 0).2.cs.sw, .chain vm)) (L.drop 7) c).rungs.contains 1) := by
    subst hL
    decide +kernel
  obtain ⟨hlen, hsome, hb, hany⟩ := hd
  have hlt : 6 < L.length := by rw [hlen]; decide
  have hg : L.getD 6 ((BtcPolicy.Exhibits.Lifecycle.runAt 0).2.cs.sw, .chain vm) = L[6] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rw [hg] at hsome hany
  obtain ⟨e₁, he₁⟩ := Option.isSome_iff_exists.1 hsome
  have hy : L[6] = (L[6].1, .fed (.process 1 e₁ .ladderPass)) := by
    rw [← ladderEnv_some he₁]
  have hT : L = L.take 6 ++ (L[6].1, .fed (.process 1 e₁ .ladderPass)) :: L.drop 7 := by
    rw [← hy]; exact BtcPolicy.Exhibits.Retained.split_at L 6 hlt
  obtain ⟨c₁, hc₁f, hm⟩ := List.any_eq_true.1 hany
  obtain ⟨hc₁, hk₁⟩ := List.mem_filter.1 hc₁f
  have hm1 : 1 ∈ (BtcPolicy.ReleaseQuota.passAccount BtcPolicy.Exhibits.Lifecycle.flc Kernel.current L[6].1
      (L.drop 7) 1 e₁ c₁).rungs := by
    have : accountAt L[6] (L.drop 7) c₁ =
        BtcPolicy.ReleaseQuota.passAccount BtcPolicy.Exhibits.Lifecycle.flc Kernel.current L[6].1 (L.drop 7) 1 e₁ c₁ := by
      simp [accountAt, he₁]
    rw [← this]
    simpa using hm
  rw [← hL] at hm'
  exact BtcPolicy.ReleaseQuota.life_no_relist rfl hx (by decide) (hL.trans hT)
    (fun y hy => by simpa using List.all_eq_true.1 hb y hy) hc₁ (by simpa using hk₁) hm1 hc₂ hk₂ hm'

end BtcPolicy.Exhibits.ReleaseQuota

namespace BtcPolicy.Exhibits.Possession
open BtcPolicy.Kernel
open BtcPolicy.Kernel.RegistrationCases (env0 envFire envLate)
open BtcPolicy.Exhibits.EndToEnd (honest st0_fresh)
open BtcPolicy.Exhibits.Lifecycle (fcfg fv stL whole runAt esL t1 row lifecycle_run)

/-! ### Release to possession on the lifecycle run

Research task `bps-8bbx.3` (`BtcPolicy.Possession`): a Held quorum at a receiving node derived on the lifecycle run
from a contributor's release, its delivery and the receiver's retention, each a premise met on the run, and the runs
where exactly one of them fails. The run is `Exhibits.Lifecycle.lifecycle_run`'s, unchanged, offered slot by slot
(`Possession.play_list`). -/

/-- `Exhibits.Lifecycle.whole` offered in order, one step per slot, and nothing after it. -/
def sched (u : Nat) : Option RungAssembly.Step := whole[u]?

/-- Rung 1 of the Escape: `t1` with its user-signature hash. -/
def g1 : Rung := esL.ladder.getD 1 ⟨t1, 0⟩

/-- The environment a slot's federation step carries. -/
def envOf : Option RungAssembly.Step → Env
  | some (.base (.fed (.process _ env _))) => env
  | some (.base (.fed (.deliverPartial _ env _))) => env
  | _ => env0

theorem stL_fresh : BtcPolicy.Lifecycle.Fresh honest stL := ⟨⟨(st0_fresh fv).1, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem play_runAt {n : Nat} (hn : n ≤ 23) : Possession.play fcfg Kernel.current honest stL sched n = runAt n :=
  Possession.play_list lifecycle_run.1 n (by rw [lifecycle_run.2.1]; exact hn)

/-- What the run shows at the slots the headline reads: node 2's ladder pass offered at slot 7, admitted, its account
listing rung 1 for its Escape; the delivery of node 2's row of `t1` to node 1 offered at slot 10 and at no other slot of
`[8, 10]`, its chain view read off node 1's observation and every envelope of the row labelled with rung 1's hash;
and node 1 retaining compatible material under the Escape's commitment at every slot of `[8, 11]`. -/
theorem slot_facts :
    Possession.passOf 2 .ladderPass (sched 7) = true ∧
      BtcPolicy.Lifecycle.admits fcfg Kernel.current honest (runAt 7).2 (runAt 7).1
        (.base (.fed (.process 2 (envOf (sched 7)) .ladderPass))) = true ∧
      (∃ c ∈ ((runAt 7).2.cs.sw.fed.worlds 2).node.cands, c.id = esL.id ∧
        1 ∈ (ReleaseQuota.passAccount fcfg.lc Kernel.current (runAt 7).2.cs.sw
          (ClassAssembly.sweepT (BtcPolicy.Lifecycle.toL (runAt 7).1)) 2 (envOf (sched 7)) c).rungs ∧
        c.above[0]? = some g1 ∧ ∀ k < g1.tx.inputs.length, VariantReceipt.rungOf c (sighash g1.tx k) k = some g1) ∧
      Possession.rowOf 2 esL.id g1 0 = row 2 t1 ∧
      Possession.deliverOf 1 (row 2 t1) (sched 8) = false ∧ Possession.deliverOf 1 (row 2 t1) (sched 9) = false ∧
      Possession.deliverOf 1 (row 2 t1) (sched 10) = true ∧
      Settlement.viewOk (runAt 10).2.cs.sw 1 (envOf (sched 10)) = true ∧
      (∀ z ∈ VariantReceipt.envelopes Kernel.current (Possession.fedT (runAt 10).1), z.1 = row 2 t1 →
        z.2 = some g1.userSig) ∧
      (∀ u ∈ [8, 9, 10, 11], ∃ cj ∈ ((runAt u).2.cs.sw.fed.worlds 1).node.cands, cj.id = esL.id ∧
        ∀ k < g1.tx.inputs.length, VariantReceipt.rungOf cj (sighash g1.tx k) k = some g1) ∧
      g1.tx.inputs.length = 1 ∧ 1 ∈ fcfg.lc.pre.sweep.keys ∧ 2 ∈ fcfg.lc.pre.sweep.keys ∧ 1 ∈ honest ∧
      ((runAt 11).2.cs.sw.fed.worlds 1).node.t = 2 ∧
      (∃ c ∈ ((runAt 11).2.cs.sw.fed.worlds 1).node.cands, c.id = esL.id ∧ c.ladder[1]? = some g1 ∧
        1 ≤ c.track.latch) := by
  decide +kernel

/-- **The premises hold on the useful run** (`DUR-28`). `Possession.possession_window` applied to
`Exhibits.Lifecycle.lifecycle_run`, unchanged, with node 2 the one contributor (`S = [2]`), node 1 the receiver
counted by its own signature, and rung 1 released at node 2's ladder pass: the pass window is slot 7, the delivery
window `[8, 10]`, the retention window `[8, 11]`. The theorem, not a decision, gives node 1's Held quorum on `t1` at
slot 11 at node 1's threshold, and with it a finalization of node 1's Escape at rung 1 or above
(`Possession.final_of_quorum`). The schedule's service is the window form: a finite run offers node 2's pass and the
delivery once each, so `Progress.Profile.bounded` does not hold of it from every instant. -/
@[req "DUR-28"]
theorem lifecycle_possession :
    Authority.quorum fcfg.lc.pre.sweep.keys 2 g1.tx
        (ClassAssembly.heldAt fcfg (runAt 11).2.cs (BtcPolicy.Lifecycle.toL (runAt 11).1) 1) = true ∧
      ∃ c ∈ ((runAt 11).2.cs.sw.fed.worlds 1).node.cands, c.id = esL.id ∧
        ∃ m', ClassAssembly.finalAt fcfg (runAt 11).2.cs (BtcPolicy.Lifecycle.toL (runAt 11).1) 1 c = some m' ∧
          1 ≤ m' := by
  obtain ⟨hp7, ha7, hr7, hrow, hd8, hd9, hd10, hview, hlab, hret, hlen, hk1, hk2, hh1, ht11, c, hc, hcid, hcl,
    hlat⟩ := slot_facts
  have hq : Authority.quorum fcfg.lc.pre.sweep.keys 2 g1.tx
      (ClassAssembly.heldAt fcfg (Possession.play fcfg Kernel.current honest stL sched (7 + 0 + 2 + 2)).2.cs
        (BtcPolicy.Lifecycle.toL (Possession.play fcfg Kernel.current honest stL sched (7 + 0 + 2 + 2)).1) 1) =
      true := by
    refine Possession.possession_window (cfg := fcfg) (r := Kernel.current) (honest := honest) (st0 := stL)
      (sched := sched) (S := [2]) (j := 1) (cid := esL.id) (t := 2) (g := g1) (t0 := 7) (B₁ := 0) (B₂ := 2)
      stL_fresh rfl (.rung 0) hh1 hk1 (by decide)
      (by decide) (fun s hs => by simp at hs; subst hs; exact hk2) (by decide) (fun h => by rw [h] at hlen; cases hlen)
      (fun s hs => ⟨7, by omega, by omega, by simp at hs; subst hs; exact hp7⟩) ?_ ?_ ?_ ?_
    · intro s hs u h1 h2 _ env he
      simp at hs; subst hs
      obtain rfl : u = 7 := by omega
      have henv : env = envOf (sched 7) := by rw [he]; rfl
      subst henv
      rw [play_runAt (by omega)]
      exact ⟨ha7, hr7⟩
    · intro s hs k hk
      simp at hs; subst hs
      obtain rfl : k = 0 := by omega
      exact ⟨10, by omega, by omega, by rw [hrow]; exact hd10⟩
    · intro s hs k hk u h1 h2 _ env he
      simp at hs; subst hs
      obtain rfl : k = 0 := by omega
      rw [hrow] at he ⊢
      have hdu : Possession.deliverOf 1 (row 2 t1) (sched u) = true := by rw [he]; simp [Possession.deliverOf]
      obtain rfl | rfl | rfl : u = 8 ∨ u = 9 ∨ u = 10 := by omega
      · rw [hd8] at hdu; cases hdu
      · rw [hd9] at hdu; cases hdu
      · have henv : env = envOf (sched 10) := by rw [he]; rfl
        subst henv
        rw [play_runAt (by omega)]
        exact ⟨hview, hlab⟩
    · intro u h1 h2
      rw [play_runAt (by omega)]
      exact hret u (by
        obtain rfl | rfl | rfl | rfl : u = 8 ∨ u = 9 ∨ u = 10 ∨ u = 11 := by omega
        all_goals simp)
  rw [play_runAt (by omega)] at hq
  refine ⟨hq, c, hc, hcid, Possession.final_of_quorum hcl hlat ?_⟩
  rw [ht11]
  exact hq

/-- `whole`'s first ten steps: node 2's ladder pass is taken, and the run stops before node 1 is handed node 2's row
of `t1`. -/
def cut : List RungAssembly.Step := whole.take 10

theorem cut_facts :
    (∀ u < 10, Possession.deliverOf 1 (row 2 t1) cut[u]? = false) ∧ cut.length = 10 ∧
      Authority.quorum fcfg.lc.pre.sweep.keys 2 g1.tx
        (ClassAssembly.heldAt fcfg (runAt 10).2.cs (BtcPolicy.Lifecycle.toL (runAt 10).1) 1) = false ∧
      row 2 t1 ∈ (runAt 10).2.cs.sw.fed.parts := by
  decide +kernel

/-- **Starvation: the delivery is never offered** (condition 5's service fails). The schedule offers
`Exhibits.Lifecycle.whole`'s first ten steps and then nothing: node 2's release of rung 1 is taken and its row stays in
the inventory at every later slot, the delivery of that row to node 1 is offered at no slot, and node 1's possession
has no quorum on `t1` at any slot from 10 on. -/
@[req "DUR-28"]
theorem starved :
    (∀ u : Nat, Possession.deliverOf 1 (row 2 t1) cut[u]? = false) ∧
      ∀ u : Nat, 10 ≤ u →
        Authority.quorum fcfg.lc.pre.sweep.keys 2 g1.tx
          (ClassAssembly.heldAt fcfg (Possession.play fcfg Kernel.current honest stL (fun v => cut[v]?) u).2.cs
            (BtcPolicy.Lifecycle.toL (Possession.play fcfg Kernel.current honest stL (fun v => cut[v]?) u).1) 1) =
          false ∧
        row 2 t1 ∈ (Possession.play fcfg Kernel.current honest stL (fun v => cut[v]?) u).2.cs.sw.fed.parts := by
  obtain ⟨hd, hlen, hq, hp⟩ := cut_facts
  have h10 : Possession.play fcfg Kernel.current honest stL (fun v => cut[v]?) 10 = runAt 10 := by
    have hl : BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL cut = true :=
      Possession.legal_take lifecycle_run.1 10
    rw [Possession.play_list hl 10 (Nat.le_of_eq hlen.symm)]
    simp only [cut, runAt, BtcPolicy.Exhibits.Lifecycle.runOf, List.take_take, Nat.min_self]
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · by_cases h : u < 10
    · exact hd u h
    · rw [List.getElem?_eq_none (by omega)]; rfl
  · have he := Possession.play_after (cfg := fcfg) (r := Kernel.current) (honest := honest) (st0 := stL) (ss := cut)
      (u - 10)
    rw [hlen, show 10 + (u - 10) = u by omega, h10] at he
    rw [he]
    exact ⟨hq, hp⟩

/-- `whole`'s first eleven steps, the delivery to node 1 included, then node 1's prune at a late instant, past the
Escape's expiry. -/
def loss : List RungAssembly.Step := whole.take 11 ++ [.base (.fed (.process 1 envLate .prune))]

/-- **Retention: the receiver loses the candidate** (condition 6 fails). On `loss`, a legal run of the layer, node 1
keeps node 2's record on `t1` after the delivery, and its Held quorum on `t1` holds; its prune then removes every
resident under the Escape's commitment, the kept list holds no record under it, and the quorum is gone, while the
row stays in the inventory (`VariantReceipt.kept_resident`). -/
@[req "NCH-25"]
theorem lost :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL loss = true ∧
      (Possession.keptAt fcfg.lc.pre.sweep.keys (BtcPolicy.Exhibits.Lifecycle.runOf loss 11).1
        (BtcPolicy.Exhibits.Lifecycle.runOf loss 11).2 1).map (fun p => (p.1 == esL.id, p.2.signer)) = [(true, 2)] ∧
      Authority.quorum fcfg.lc.pre.sweep.keys 2 g1.tx (ClassAssembly.heldAt fcfg
        (BtcPolicy.Exhibits.Lifecycle.runOf loss 11).2.cs
        (BtcPolicy.Lifecycle.toL (BtcPolicy.Exhibits.Lifecycle.runOf loss 11).1) 1) = true ∧
      ((BtcPolicy.Exhibits.Lifecycle.runOf loss 12).2.cs.sw.fed.worlds 1).node.cands.any (·.id == esL.id) = false ∧
      (Possession.keptAt fcfg.lc.pre.sweep.keys (BtcPolicy.Exhibits.Lifecycle.runOf loss 12).1
        (BtcPolicy.Exhibits.Lifecycle.runOf loss 12).2 1).filter (·.1 == esL.id) = [] ∧
      Authority.quorum fcfg.lc.pre.sweep.keys 2 g1.tx (ClassAssembly.heldAt fcfg
        (BtcPolicy.Exhibits.Lifecycle.runOf loss 12).2.cs
        (BtcPolicy.Lifecycle.toL (BtcPolicy.Exhibits.Lifecycle.runOf loss 12).1) 1) = false ∧
      row 2 t1 ∈ (BtcPolicy.Exhibits.Lifecycle.runOf loss 12).2.cs.sw.fed.parts := by
  decide +kernel

/-- `whole`'s first ten steps, then node 1's prune at the late instant, then the delivery of node 2's row of `t1`. -/
def lossEarly : List RungAssembly.Step :=
  whole.take 10 ++ [.base (.fed (.process 1 envLate .prune)), .base (.fed (.deliverPartial 1 envFire (row 2 t1)))]

/-- **Retention before the delivery** (condition 6 fails at arrival). Node 1 prunes the Escape before node 2's row
reaches it: the delivery is admitted and taken, its store test fails at node 1 (no resident under the commitment), no
record is kept and there is no quorum on `t1`. -/
@[req "NCH-24"]
theorem lost_early :
    BtcPolicy.Lifecycle.legal fcfg Kernel.current honest [] stL lossEarly = true ∧
      VariantReceipt.storable fcfg.lc.pre.sweep.keys
        ((BtcPolicy.Exhibits.Lifecycle.runOf lossEarly 11).2.cs.sw.fed.worlds 1).node (row 2 t1).msg 0 2 esL.id
        (some g1.userSig) = false ∧
      (BtcPolicy.Exhibits.Lifecycle.runOf lossEarly 12).1.length = 12 ∧
      (Possession.keptAt fcfg.lc.pre.sweep.keys (BtcPolicy.Exhibits.Lifecycle.runOf lossEarly 12).1
        (BtcPolicy.Exhibits.Lifecycle.runOf lossEarly 12).2 1) = [] ∧
      Authority.quorum fcfg.lc.pre.sweep.keys 2 g1.tx (ClassAssembly.heldAt fcfg
        (BtcPolicy.Exhibits.Lifecycle.runOf lossEarly 12).2.cs
        (BtcPolicy.Lifecycle.toL (BtcPolicy.Exhibits.Lifecycle.runOf lossEarly 12).1) 1) = false := by
  decide +kernel

end BtcPolicy.Exhibits.Possession

namespace BtcPolicy.Exhibits.ExpirySilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.ReceiptExpiry BtcPolicy.ExpirySilence
open BtcPolicy.Kernel.RegistrationCases (envAt)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (part honest)
open BtcPolicy.Exhibits.ReceiptExpiry (cfg envD envW)
open BtcPolicy.Exhibits.LedgerSilence (L0 L0_fresh L0_sweep tblsD tblsN request)

/-! ### SILENCE over the expiry-aware receipt

Research task `bps-8bbx.2`, first tranche. The request `Exhibits.Ingress.req0`, whose signed expiry is 200, presented
with PIN 1 at nodes 1, 2 and 3 from `EndToEnd.fed0` with empty Hot ledgers. PIN 1 is the duress PIN in the first
family (`tblsD`) and an ordinary PIN in the second (`tblsN`). Every delivered partial goes through
`ReceiptExpiry.sysRecv`. -/

/-- Wall 201, one second past the expiry; wall 230. -/
def envE : Env := envAt 201 196
def envF : Env := envAt 230 225

/-- Nodes 1, 2 and 3 take the request; nodes 1 and 2 exchange relays and decide at wall 150, which arms both in the
first family at `T = 250` and neither in the second; node 3 never decides. Signer 2's key is copied and its partials
on both members are forged. Signer 2's spend partial then reaches node 3 at wall 201 (step 10) and node 1 at wall 201
(step 11), and its Escape partial reaches node 1 at wall 230 (step 12). -/
def early : List PStep :=
  [request 1, request 2, request 3, .net (.emit 1 10), .net (.emit 2 10),
   .net (.deliver 1 envD ⟨2, 10⟩), .net (.deliver 2 envD ⟨1, 10⟩),
   .net (.extract 2), .net (.forge (part sp0 2)), .net (.forge (part es0 2)),
   .net (.deliverPartial 3 envE (part sp0 2)), .net (.deliverPartial 1 envE (part sp0 2)),
   .net (.deliverPartial 1 envF (part es0 2))]

/-- Signer 2's spend partial again at node 1, at wall 260: past the first family's `T`. -/
def late : PStep := .net (.deliverPartial 1 envW (part sp0 2))

def sched : List PStep := early ++ [late]

/-- The two families walked together. -/
def walkE : List (XObs × XObs) :=
  xwalk Silence.current Ledger.current cfg Kernel.current honest honest tblsD tblsN L0 L0 sched

/-- One family's run after the schedule's first `k` steps. -/
def runE (tbls : Nat → Enrolment) (k : Nat) : LFed :=
  xrun Ledger.current cfg Kernel.current L0 ((sched.take k).map (·.step tbls))

/-- Whether node `i` holds a record under `cid`, and whether its Hot ledger charges `cid`. -/
def resident (F : LFed) (i cid : Nat) : Bool := (F.fed.worlds i).node.cands.any (·.id == cid)
def charges (F : LFed) (i cid : Nat) : Bool := (F.leds i).any (·.cid == cid)

/-- **An evicting delivery inside the walk, under both PINs** (`DUR-1`, `NCH-24`). `ExpirySilence.xfed_silence_fresh`
at the values as they stand: the two families emit equal `ReceiptExpiry.XObs` at every step of the walk, and the
comparison computed on the walk agrees. The walk covers the first 13 steps. Nodes 1 and 2 are armed at `T = 250` in
the first family and neither in the second. At step 10 node 3's lookup finds the spend past its expiry with no open
Escape window beside it, in both families: both evict it, both answer `UNKNOWN_CANDIDATE`, and in both the
unexposed charge goes with it. -/
@[req "DUR-1"]
theorem eviction_silent :
    (∀ y ∈ walkE, y.1 = y.2) ∧
    walkE.all (fun y => y.1 == y.2) = true ∧ walkE.length = 13 ∧
    ((runE tblsD 7).fed.worlds 1).node.armed = true ∧ ((runE tblsD 7).fed.worlds 2).node.armed = true ∧
    ((runE tblsD 7).fed.worlds 1).node.T = Wall.sample 250 ∧
    ((runE tblsN 7).fed.worlds 1).node.armed = false ∧ ((runE tblsN 7).fed.worlds 2).node.armed = false ∧
    ((walkE.drop 10).take 1).map (fun y => (y.1.answer, y.2.answer)) =
      [(some (3, 2, .unknownCandidate), some (3, 2, .unknownCandidate))] ∧
    [tblsD, tblsN].all (fun tbls =>
      evicts envE ((runE tbls 10).fed.worlds 3).node sp0.id && resident (runE tbls 10) 3 sp0.id &&
        charges (runE tbls 10) 3 sp0.id && !resident (runE tbls 11) 3 sp0.id &&
        !charges (runE tbls 11) 3 sp0.id && resident (runE tbls 11) 3 es0.id) = true :=
  ⟨xfed_silence_fresh rfl rfl rfl rfl rfl rfl honest honest tblsD tblsN L0 L0_fresh L0_sweep sched,
    by decide +kernel⟩

/-- **The delayed slot, inside the walk, under both PINs** (`SPN-41`: "the exemption is granted to the normal PIN's
inert slot too"). At wall 201 and at wall 230, past the spend's expiry and before the first family's `T`, node 1's
Escape is not broadcast and its window is open: it closes at 290 in the first family and at 390 in the second, the
inert slot. The lookup keeps the spend and the Escape, and both families answer found at steps 11 and 12. -/
@[req "SPN-41"]
theorem exemption_silent :
    ((walkE.drop 11).map fun y => (y.1.answer, y.2.answer)) =
      [(some (1, 2, .found), some (1, 2, .found)), (some (1, 2, .found), some (1, 2, .found))] ∧
    ((runE tblsD 11).fed.worlds 1).node.cands.map (·.windowClose) = [none, some (Wall.sample 290)] ∧
    ((runE tblsN 11).fed.worlds 1).node.cands.map (·.windowClose) = [none, some (Wall.sample 390)] ∧
    [tblsD, tblsN].all (fun tbls =>
      ((runE tbls 11).fed.worlds 1).node.cands.all (fun c => c.expiry == Wall.sample 200) &&
        lookup envE ((runE tbls 11).fed.worlds 1).node sp0.id == .live &&
        lookup envF ((runE tbls 12).fed.worlds 1).node es0.id == .live) = true := by
  decide +kernel

/-- **The horizon is `FedSilence.walk`'s.** The walk stops at step 13, the first step past the first family's
`T`: node 1 there is armed with `T = 250` reached at wall 260, and in the second family it is inside. -/
@[req "DUR-7"]
theorem eviction_horizon :
    sched.length = 14 ∧ walkE.length = 13 ∧
    Federation.admits honest (runE tblsD 13).fed (late.step tblsD) = true ∧
    inside Kernel.current (runE tblsD 13) (late.step tblsD) = false ∧
    inside Kernel.current (runE tblsN 13) (late.step tblsN) = true := by
  decide +kernel

/-! ### The leak the comparison detects -/

/-- Not a rule the protocol has had: `SPN-41`'s delayed-slot exemption read on an armed node only, so the normal
PIN's inert slot is not exempt. -/
def keepsArmed (env : Env) (n : Node) (c : Cand) : Bool :=
  env.eff.atOrBefore c.expiry || (n.armed && n.cands.any fun e => e.pair == c.pair && exemptEscape env e)

/-- The answer with that keep test. -/
def answerArmed (env : Env) (n : Node) (cid : Nat) : Answer :=
  match n.cands.find? (·.id == cid) with
  | some c => if keepsArmed env n c then .found else .unknownCandidate
  | none => .unknownCandidate

/-- The observation the walk compares at a delivered partial, with the answer that keep test gives. -/
def leakObs (F : LFed) : Federation.Step → XObs
  | s@(.deliverPartial i env x) =>
    { xfobs Silence.current Ledger.current cfg Kernel.current honest F s with
      answer := some (i, x.signer, answerArmed env (F.fed.worlds i).node x.cid) }
  | s => xfobs Silence.current Ledger.current cfg Kernel.current honest F s

/-- Step 11: signer 2's spend partial at node 1, at wall 201. -/
def step11 : PStep := .net (.deliverPartial 1 envE (part sp0 2))

/-- **An exemption read on the arm bit is a difference the comparison sees.** Step 11 is admitted and inside the
horizon in both families. With the exemption granted to an armed node only, node 1 keeps the spend and answers
found in the first family, evicts it and answers `UNKNOWN_CANDIDATE` in the second, and the two observations
differ. -/
@[req "SPN-41"]
theorem armed_only_exemption_leaks :
    sched.drop 11 = step11 :: sched.drop 12 ∧
    Federation.admits honest (runE tblsD 11).fed (step11.step tblsD) = true ∧
    inside Kernel.current (runE tblsD 11) (step11.step tblsD) = true ∧
    inside Kernel.current (runE tblsN 11) (step11.step tblsN) = true ∧
    (leakObs (runE tblsD 11) (step11.step tblsD)).answer = some (1, 2, .found) ∧
    (leakObs (runE tblsN 11) (step11.step tblsN)).answer = some (1, 2, .unknownCandidate) ∧
    leakObs (runE tblsD 11) (step11.step tblsD) ≠ leakObs (runE tblsN 11) (step11.step tblsN) := by
  decide +kernel

end BtcPolicy.Exhibits.ExpirySilence

namespace BtcPolicy.Exhibits.VariantSilence
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence BtcPolicy.FedSilence
open BtcPolicy.VariantSilence
open BtcPolicy.Kernel.RegistrationCases (envAt)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (part honest)
open BtcPolicy.Exhibits.ReceiptExpiry (cfg envD envW)
open BtcPolicy.Exhibits.LedgerSilence (L0 L0_fresh L0_sweep tblsD tblsN request)

/-! ### SILENCE over the variant-aware receipt

Research task `bps-8bbx.2`, the variant-aware tranche. The request `Exhibits.Ingress.req0` (signed expiry 200),
presented with PIN 1 at nodes 1, 2 and 3 from `EndToEnd.fed0` with empty Hot ledgers. PIN 1 is the duress PIN in the
first family (`tblsD`) and an ordinary PIN in the second (`tblsN`). Every delivered partial goes through the
variant-bound store, with the receivers' keys 1, 2 and 3. The Escape `es0` is Escape-role at every node, with one
input and the hash 0 on its base; the spend `sp0` is not Escape-role. -/

/-- Wall 170: after the holder decisions at wall 150, before the signed expiry and the first family's `T = 250`. -/
def envR : Env := envAt 170 165

/-- Signer 2's Escape partial named on input 5, outside the Escape's one input. -/
def wrongInput : Exp := { part es0 2 with msg := sighash es0.tx 5, input := 5 }

/-- Signer 2's Escape partial under a commitment id no node holds. -/
def missingCand : Exp := { part es0 2 with cid := 77 }

/-- The receivers' configured keys. -/
def keys : List Nat := honest

/-- Nodes 1, 2 and 3 take the request; nodes 1 and 2 exchange relays and decide at wall 150, which arms both in the
first family at `T = 250` and neither in the second. Signers 2 and 9 have their keys copied; signer 2's partials on
both members, signer 9's on the Escape, and the two malformed partials are forged into the inventory. -/
def setup : List LStep :=
  [(request 1, none), (request 2, none), (request 3, none), (.net (.emit 1 10), none), (.net (.emit 2 10), none),
   (.net (.deliver 1 envD ⟨2, 10⟩), none), (.net (.deliver 2 envD ⟨1, 10⟩), none),
   (.net (.extract 2), none), (.net (.forge (part sp0 2)), none), (.net (.forge (part es0 2)), none),
   (.net (.extract 9), none), (.net (.forge (part es0 9)), none), (.net (.forge wrongInput), none),
   (.net (.forge missingCand), none)]

/-- At node 1, armed in the first family, at wall 170: signer 2's Escape partial under hash 1 (step 14), then under
the Escape's hash 0 twice (steps 15 and 16); the partial on input 5 (17); signer 9's (18); the partial under an
unknown id (19); and signer 2's spend partial under the arbitrary label 999 (20). -/
def deliveries : List LStep :=
  [(.net (.deliverPartial 1 envR (part es0 2)), some 1), (.net (.deliverPartial 1 envR (part es0 2)), some 0),
   (.net (.deliverPartial 1 envR (part es0 2)), some 0), (.net (.deliverPartial 1 envR wrongInput), some 0),
   (.net (.deliverPartial 1 envR (part es0 9)), some 0), (.net (.deliverPartial 1 envR missingCand), some 0),
   (.net (.deliverPartial 1 envR (part sp0 2)), some 999)]

/-- The spend partial again at node 1, at wall 260: past the first family's `T`. -/
def late : LStep := (.net (.deliverPartial 1 envW (part sp0 2)), some 999)

def sched : List LStep := setup ++ deliveries ++ [late]

/-- The two families walked together. -/
def walkV : List (VObs × VObs) :=
  vwalk Silence.current Ledger.current cfg Kernel.current honest honest keys tblsD tblsN (VFed.init L0) (VFed.init L0)
    sched

/-- One family's labelled run after the schedule's first `k` steps. -/
def runV (tbls : Nat → Enrolment) (k : Nat) : VFed :=
  vrun keys Ledger.current cfg Kernel.current (VFed.init L0) ((sched.take k).map fun p => (p.1.step tbls, p.2))

/-- The store's decisions the two families report at each delivery to node 1. -/
def decisions : List (Option Checks × Option Checks) :=
  ((walkV.drop 14).take 7).map fun y => (y.1.store.map (·.checks), y.2.store.map (·.checks))

/-- Signer 2's record on the Escape's input 0, and on the spend's. -/
def recEs : Nat × Authority.Sig := (es0.id, { msg := sighash es0.tx 0, input := 0, signer := 2 })
def recSp : Nat × Authority.Sig := (sp0.id, { msg := sighash sp0.tx 0, input := 0, signer := 2 })

/-- **The variant-bound store inside the walk, under both PINs** (`DUR-1`, `NCH-24`). `VariantSilence.vfed_silence_fresh`
at the values as they stand: the two families emit equal `VariantSilence.VObs` at every step of the walk, and the
comparison computed on the walk agrees. The walk covers the first 21 steps. Nodes 1 and 2 are armed at `T = 250` in
the first family and neither in the second, and node 1's records and Held projection at the end are the same in
both. -/
@[req "DUR-1"]
theorem variant_silent :
    (∀ y ∈ walkV, y.1 = y.2) ∧
    walkV.all (fun y => y.1 == y.2) = true ∧ walkV.length = 21 ∧
    ((runV tblsD 7).lf.fed.worlds 1).node.armed = true ∧ ((runV tblsD 7).lf.fed.worlds 2).node.armed = true ∧
    ((runV tblsD 7).lf.fed.worlds 1).node.T = Wall.sample 250 ∧
    ((runV tblsN 7).lf.fed.worlds 1).node.armed = false ∧ ((runV tblsN 7).lf.fed.worlds 2).node.armed = false ∧
    (runV tblsD 21).store 1 = (runV tblsN 21).store 1 ∧ vheld (runV tblsD 21) 1 = vheld (runV tblsN 21) 1 :=
  ⟨vfed_silence_fresh rfl rfl rfl rfl rfl rfl honest honest keys tblsD tblsN L0 L0_fresh L0_sweep sched,
    by decide +kernel⟩

/-- **Each acceptance case, alike in both families** (`NCH-24`, `NCH-25`, `POL-18`). At node 1, armed in the first
family:
- step 14, the Escape partial under hash 1: the lookup finds the Escape and the rung and the input is in range, but
  the hash does not match, so the store refuses it, and the partial stays in the inventory;
- step 15, under the Escape's hash 0: the store keeps signer 2's record;
- step 16, the same again: the store takes it but keeps no second record, and the first is unchanged;
- step 17, input 5 out of range, and step 18, signer 9 outside the keys: refused, nothing kept;
- step 19, an unknown commitment id: the lookup fails, nothing is kept and no candidate is created under that id;
- step 20, the spend partial under the label 999: the spend is not Escape-role, so no hash is compared and the store
  keeps the record. The label is admissible only because signer 2's key is extracted: no honest node sent any
  envelope, so nothing ties it to a sender's variant. -/
@[req "NCH-24"]
theorem variant_cases :
    decisions =
      [(some ⟨true, true, true, false, true, false, true⟩, some ⟨true, true, true, false, true, false, true⟩),
       (some ⟨true, true, true, true, true, true, true⟩, some ⟨true, true, true, true, true, true, true⟩),
       (some ⟨true, true, true, true, true, true, false⟩, some ⟨true, true, true, true, true, true, false⟩),
       (some ⟨true, true, false, false, true, false, true⟩, some ⟨true, true, false, false, true, false, true⟩),
       (some ⟨true, true, true, true, false, false, true⟩, some ⟨true, true, true, true, false, false, true⟩),
       (some ⟨false, false, false, false, true, false, true⟩, some ⟨false, false, false, false, true, false, true⟩),
       (some ⟨true, true, true, true, true, true, true⟩, some ⟨true, true, true, true, true, true, true⟩)] ∧
    [tblsD, tblsN].all (fun tbls =>
      (runV tbls 15).store 1 == [] && (runV tbls 15).lf.fed.parts.contains (part es0 2) &&
        (runV tbls 16).store 1 == [recEs] && (runV tbls 17).store 1 == [recEs] &&
        (runV tbls 20).store 1 == [recEs] && (runV tbls 21).store 1 == [recEs, recSp] &&
        vheld (runV tbls 20) 1 == vheld (runV tbls 16) 1 &&
        !((runV tbls 20).lf.fed.worlds 1).node.cands.any (·.id == missingCand.cid) &&
        (runV tbls 20).envs.isEmpty && (runV tbls 20).lf.fed.extracted.contains 2 &&
        vlabelOk (runV tbls 20) (.deliverPartial 1 envR (part sp0 2)) (some 999)) = true := by
  decide +kernel

/-- **The walked run is a labelled execution.** In each family the labelled schedule is admitted with admissible
labels (`VariantSilence.vlegal`), so `VariantSilence.vrun_execution` makes it a `VariantReceipt.Execution` whose kept
records are the layer's: the Held projection the walk compares is `VariantReceipt.held` (`VariantSilence.vheld_held`). -/
@[req "NCH-24"]
theorem variant_labelled (tbls : Nat → Enrolment) (ht : tbls = tblsD ∨ tbls = tblsN) :
    VariantReceipt.Execution Kernel.current honest
        (vtrace keys Ledger.current cfg Kernel.current [] (VFed.init L0) (sched.map fun p => (p.1.step tbls, p.2)))
        (vrun keys Ledger.current cfg Kernel.current (VFed.init L0) (sched.map fun p => (p.1.step tbls, p.2))).lf.fed ∧
      Agrees keys Kernel.current
        (vtrace keys Ledger.current cfg Kernel.current [] (VFed.init L0) (sched.map fun p => (p.1.step tbls, p.2)))
        (vrun keys Ledger.current cfg Kernel.current (VFed.init L0) (sched.map fun p => (p.1.step tbls, p.2))) := by
  refine vrun_execution (.init _ L0_fresh) (agrees_init keys _ L0) _ ?_
  rcases ht with rfl | rfl <;> decide +kernel

/-- **The horizon is `FedSilence.walk`'s.** The walk stops at step 21, the first step past the first family's `T`:
node 1 there is armed with `T = 250` reached at wall 260, and in the second family it is inside. -/
@[req "DUR-7"]
theorem variant_horizon :
    sched.length = 22 ∧ walkV.length = 21 ∧
    Federation.admits honest (runV tblsD 21).lf.fed (late.1.step tblsD) = true ∧
    inside Kernel.current (runV tblsD 21).lf (late.1.step tblsD) = false ∧
    inside Kernel.current (runV tblsN 21).lf (late.1.step tblsN) = true := by
  decide +kernel

/-! ### The leak the comparison detects -/

/-- Not a rule the protocol has had: the store skips the user-signature hash comparison on an armed node. -/
def storableArmed (keys : List Nat) (n : Node) (m : Sighash) (k s cid : Nat) (h : Option Nat) : Bool :=
  keys.contains s && n.cands.any fun c => c.id == cid &&
    match VariantReceipt.rungOf c m k with
    | none => false
    | some g => decide (k < g.tx.inputs.length) && (!c.isEscape || n.armed || h == some g.userSig)

/-- The observation the walk compares at a delivered partial, with that store decision. -/
def leakObs (V : VFed) : Federation.Step → Option Nat → VObs
  | s@(.deliverPartial i _ x), h =>
    let o := vobs Silence.current Ledger.current cfg Kernel.current honest keys V s h
    { o with store := o.store.map fun so =>
        { so with checks := { so.checks with
          stored := storableArmed keys (V.lf.fed.worlds i).node x.msg x.input x.signer x.cid h } } }
  | s, h => vobs Silence.current Ledger.current cfg Kernel.current honest keys V s h

/-- Step 14: signer 2's Escape partial at node 1 under hash 1. -/
def step14 : LStep := (.net (.deliverPartial 1 envR (part es0 2)), some 1)

/-- **A store decision read on the arm bit is a difference the comparison sees.** Step 14 is admitted and inside
the horizon in both families. With the hash comparison skipped on an armed node, node 1 stores the mismatched
partial in the first family and refuses it in the second, and the two observations differ. -/
@[req "NCH-24"]
theorem armed_store_leaks :
    sched.drop 14 = step14 :: sched.drop 15 ∧
    Federation.admits honest (runV tblsD 14).lf.fed (step14.1.step tblsD) = true ∧
    inside Kernel.current (runV tblsD 14).lf (step14.1.step tblsD) = true ∧
    inside Kernel.current (runV tblsN 14).lf (step14.1.step tblsN) = true ∧
    (leakObs (runV tblsD 14) (step14.1.step tblsD) step14.2).store.map (·.checks.stored) = some true ∧
    (leakObs (runV tblsN 14) (step14.1.step tblsN) step14.2).store.map (·.checks.stored) = some false ∧
    leakObs (runV tblsD 14) (step14.1.step tblsD) step14.2 ≠ leakObs (runV tblsN 14) (step14.1.step tblsN) step14.2 := by
  decide +kernel

end BtcPolicy.Exhibits.VariantSilence
