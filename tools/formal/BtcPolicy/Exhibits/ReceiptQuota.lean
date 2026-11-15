import BtcPolicy.ReceiptQuota
import BtcPolicy.Exhibits.Fixtures

namespace BtcPolicy.Exhibits.ReceiptQuota
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger
open BtcPolicy.Sweep (Backend)
open BtcPolicy.Kernel.RegistrationCases (env0 envLate envAt)
open BtcPolicy.Exhibits.Ingress (sp0 es0)
open BtcPolicy.Exhibits.EndToEnd (honest st0 st0_fresh part coin v)
open BtcPolicy.Exhibits.CommonRun (inst onBook readFirst)
open BtcPolicy.Exhibits.Integrated (ilc)
open BtcPolicy.Exhibits.RungRelease (fire lad vm vm2 rrow withMedian)

/-! ### `SPN-38`'s release accounting on the expiry-aware lifecycle layer

Research task `bps-xmq1.5` (`BtcPolicy.ReceiptQuota`). Every run here is one of `ReceiptLifecycle`'s layer from
`Exhibits.EndToEnd.st0` at the instant `Exhibits.RungRelease.vm`, with empty Hot ledgers, under `Ledger.current`
and a budget of a million, which no acceptance here reaches; a delivery carries the label
`ReceiptLifecycle.labelFor` gives. The request is `Exhibits.Ingress.req0`'s pair with two rungs above the base, the
first of which, `Exhibits.Ladder.r1low`, fails coverage at the vault; its signed expiry is 200, and under the duress
PIN with the holder decision at wall 50 its Escape's window closes before wall 201. The Ladder configuration is
`Exhibits.Integrated.ilc` (floor 1, quota 600) or the same at a quota of 3. Each fire pass carries the verdict and the
account computed at its own state and history on the layer, and each ladder pass the computed release (`lfill`,
`LadderRelease.fill` over the layer's step). -/

/-- The Hot budget, and the layer's configuration over a Ladder configuration. -/
def lcfg : Config := { cap := 1000000, window := 600 }
def qcfg (lc : Ladder.Cfg) : RungAssembly.Cfg :=
  { lc := lc, witnesses := fun _ => [], test := Exhibits.Assembly.core [] }
def L0 : BtcPolicy.ReceiptLifecycle.State := { ls := { cs := { sw := (st0 (inst vm)).sw } }, leds := fun _ => [] }

theorem layer_fresh : BtcPolicy.ReceiptLifecycle.Fresh honest L0 :=
  ⟨⟨⟨(st0_fresh (inst vm)).1, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, fun _ => rfl⟩

/-- A schedule: each step with the label it names, or `none` for `ReceiptLifecycle.labelFor`'s. -/
abbrev Sched := List (RungAssembly.Step × Option (Option Nat))
def auto (ss : List RungAssembly.Step) : Sched := ss.map fun s => (s, none)
def fed (s : Federation.Step) : RungAssembly.Step := .base (.fed s)

/-- The sweep history the layer's admission reads. -/
def sweepOf (T : BtcPolicy.ReceiptLifecycle.Trace) : Sweep.Trace :=
  BtcPolicy.ClassAssembly.sweepT (BtcPolicy.ReceiptLifecycle.cls Ledger.current lcfg T)

/-- `LadderRelease.fill` over the layer's step: each fire pass carries the verdict and the starved ids, and each
ladder pass the release, computed at its own state and history on the layer, after any eviction. -/
def lfill (lc : Ladder.Cfg) : BtcPolicy.ReceiptLifecycle.Trace → BtcPolicy.ReceiptLifecycle.State → Sched → Sched
  | _, _, [] => []
  | T, st, (s, h) :: ss =>
    let s' : RungAssembly.Step := match s with
      | .base (.fed (.process i env .firePass)) =>
        let w := LadderRelease.withheldAt lc st.ls.cs.sw (sweepOf T) i
        let x := LadderRelease.starvedAt lc st.ls.cs.sw (sweepOf T) i
        fed (.process i { env with withheld := w, starved := x } .firePass)
      | .base (.fed (.process i env .ladderPass)) =>
        fed (.process i { env with ladder := RungRelease.listed lc st.ls.cs.sw (sweepOf T) i } .ladderPass)
      | s => s
    let lab := BtcPolicy.ReceiptLifecycle.labelOf st (s', h)
    (s', h) :: lfill lc ((st, s', lab) :: T)
      (BtcPolicy.ReceiptLifecycle.apply lc.pre.sweep.keys Ledger.current lcfg Kernel.current st s' lab) ss

/-- A schedule's whole run, and its run after the first `n` steps. -/
def runAll (lc : Ladder.Cfg) (ss : Sched) :
    BtcPolicy.ReceiptLifecycle.Trace × BtcPolicy.ReceiptLifecycle.State :=
  BtcPolicy.ReceiptLifecycle.record lc.pre.sweep.keys Ledger.current lcfg Kernel.current [] L0 ss
def runL (lc : Ladder.Cfg) (ss : Sched) (n : Nat) :
    BtcPolicy.ReceiptLifecycle.Trace × BtcPolicy.ReceiptLifecycle.State := runAll lc (ss.take n)
def legalL (lc : Ladder.Cfg) (ss : Sched) : Bool :=
  BtcPolicy.ReceiptLifecycle.legal (qcfg lc) Ledger.current lcfg Kernel.current honest [] L0 ss

def nodeAt (lc : Ladder.Cfg) (ss : Sched) (n i : Nat) : Node := ((runL lc ss n).2.ls.cs.sw.fed.worlds i).node
/-- Node `i`'s resident ids; its Escape-role records' `released` bit and release state. -/
def idsAt (lc : Ladder.Cfg) (ss : Sched) (n i : Nat) : List Nat := (nodeAt lc ss n i).cands.map (·.id)
def escAt (lc : Ladder.Cfg) (ss : Sched) (n i : Nat) : List (Bool × Track) :=
  ((nodeAt lc ss n i).cands.filter (·.isEscape)).map fun c => (c.released, c.track)
/-- The rows step `n` adds to the partial inventory under commitment `cid`. -/
def added (lc : Ladder.Cfg) (ss : Sched) (n cid : Nat) : List Exp :=
  ((runL lc ss (n + 1)).2.ls.cs.sw.fed.parts.drop (runL lc ss n).2.ls.cs.sw.fed.parts.length).filter (·.cid == cid)
/-- Node `i`'s ladder pass at step `n`: its account for each Escape-role record, as the interval, the rungs, the
slots consumed and the release state after it; `[]` at any other step. -/
def accounts (lc : Ladder.Cfg) (ss : Sched) (n i : Nat) : List (Option (Nat × Nat) × List Nat × Nat × Track) :=
  match (ss.map (·.1)).getD n (.base (.observe 0 vm)) with
  | .base (.fed (.process j env .ladderPass)) =>
    if j = i then
      let p := runL lc ss n
      ((p.2.ls.cs.sw.fed.worlds i).node.cands.filter (·.isEscape)).map fun c =>
        let x := BtcPolicy.ReleaseQuota.passAccount lc Kernel.current p.2.ls.cs.sw (sweepOf p.1) i env c
        (x.interval, x.rungs, BtcPolicy.ReleaseQuota.consumed x, x.track)
    else []
  | _ => []
/-- Node `i`'s attempt after the first `n` steps: which rungs of each Escape-role record are admissible. -/
def adm (lc : Ladder.Cfg) (ss : Sched) (n i : Nat) : List (List Bool) :=
  let p := runL lc ss n
  ((p.2.ls.cs.sw.fed.worlds i).node.cands.filter (·.isEscape)).map fun c =>
    match (RungRelease.readAt p.2.ls.cs.sw (sweepOf p.1) i c).ob with
    | none => []
    | some b => (Ladder.attempt lc.pre (RungRelease.readAt p.2.ls.cs.sw (sweepOf p.1) i c) b c c.track.latch).adm
/-- Whether step `n` births a record under `cid` at node `i` (`ReceiptLifecycle.born`). -/
def bornAt (lc : Ladder.Cfg) (ss : Sched) (n i cid : Nat) : Bool :=
  match ss[n]? with
  | some a =>
    let st := (runL lc ss n).2
    BtcPolicy.ReceiptLifecycle.born lc.pre.sweep.keys Ledger.current lcfg Kernel.current st a.1
      (BtcPolicy.ReceiptLifecycle.labelOf st a) i cid
  | none => false

/-- `req0`'s Escape with `r1low` and `r2` above its base; the same Escape as a later request carries it, with a release
state of its own: marked released, latch 2 and floor 3. -/
def esLow : Cand := { es0 with above := [⟨Exhibits.Ladder.r1low, 11⟩, Exhibits.Ladder.R2] }
def esRel : Cand := { esLow with released := true, track := { latch := 2, floor := 3 } }
/-- Nodes 1 and 2 take the request with the Escape `c` under the duress PIN, exchange relays, and decide at wall 50. -/
def pre (c : Cand) : List Sweep.Step :=
  [.fed (.process 1 env0 (.accept 10 true (Wall.sample 200) sp0 c)),
   .fed (.process 2 env0 (.accept 10 true (Wall.sample 200) sp0 c)), .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩)]
/-- Wall 150, an effective time earlier than the evictions' 201. -/
def envP : Env := envAt 150 90

/-- The truth moves to the vault at a median of 200; both nodes fire; node 1 takes a ladder pass. -/
def raw1 : List Sweep.Step := pre esLow ++ [.chain vm2, fire 1, fire 2, lad 1]
/-- Signer 3's key is copied and its partial on the spend forged; past the expiry (wall 201) it reaches node 1, and
then node 2's partial on the Escape does (steps 14 and 15); node 2 prunes (16). Then nodes 1 and 2 take the request
again under Carrier id 11 at wall 150, with the Escape `c` (17, 18); node 2's relay reaches node 1 (19, 20); node 1
reads the vault (21), fires (22) and takes a ladder pass (23). -/
def tailR (c : Cand) : List RungAssembly.Step :=
  [fed (.extract 3), fed (.forge (part sp0 3)), fed (.deliverPartial 1 envLate (part sp0 3)),
   fed (.deliverPartial 1 envLate (part es0 2)), fed (.process 2 envLate .prune),
   fed (.process 1 envP (.accept 11 true (Wall.sample 200) sp0 c)),
   fed (.process 2 envP (.accept 11 true (Wall.sample 200) sp0 c)), fed (.emit 2 11),
   fed (.deliver 1 envP ⟨2, 11⟩), .base (.observe 1 (inst vm2)),
   fed (.process 1 envP .firePass), fed (.process 1 envP .ladderPass)]
/-- The whole history: `raw1` with each fire pass preceded by its node's read, then `tailR esRel`. -/
def life : Sched := lfill ilc [] L0 (auto (((readFirst vm raw1).map onBook).map .base ++ tailR esRel))

set_option synthInstance.maxSize 4096 in
/-- **The quota on a run of the layer with evictions** (`SPN-38`, `NCH-24`, `DUR-27`). The 24 steps are a legal run of
the layer. Node 1's fire pass (step 8) queues the base's row and sets the floor to 1. Its ladder pass (step 11), at
the median of 200, latches rung 2; its account computes the interval `[1, 2]`, which holds `r1low`, refused at that
attempt: it lists rung 2, consumes two slots, sets latch 2 and floor 3, and the one row it queues is `r2`'s, the row
its account names. Past the expiry the spend's eviction (step 14) and the Escape's (step 15) leave node 1 holding
nothing and the partial inventory as it was. In the lifetime the re-registration begins, node 1's ladder pass
(step 23) computes the same interval, again from the floor 1 its fire pass left, with the same refused rung inside,
and queues `r2`'s row again. -/
@[req "SPN-38"]
theorem quota_on_layer :
    legalL ilc life = true ∧ life.length = 24 ∧
      added ilc life 8 es0.id = [part es0 1] ∧ escAt ilc life 9 1 = [(true, { latch := 0, floor := 1 })] ∧
      adm ilc life 11 1 = [[true, false, true]] ∧
      accounts ilc life 11 1 = [(some (1, 2), [2], 2, { latch := 2, floor := 3 })] ∧
      added ilc life 11 es0.id = [rrow Exhibits.Ladder.r2] ∧
      idsAt ilc life 14 1 = [sp0.id, es0.id] ∧ idsAt ilc life 15 1 = [es0.id] ∧ idsAt ilc life 16 1 = [] ∧
      (runL ilc life 16).2.ls.cs.sw.fed.parts = (runL ilc life 14).2.ls.cs.sw.fed.parts ∧
      adm ilc life 23 1 = [[true, false, true]] ∧
      accounts ilc life 23 1 = [(some (1, 2), [2], 2, { latch := 2, floor := 3 })] ∧
      added ilc life 23 es0.id = [rrow Exhibits.Ladder.r2] := by
  decide +kernel

/-- The history is a reachable execution of the layer (`ReceiptLifecycle.execution_of_legal`), so every result of
`ReceiptQuota` applies to it. -/
theorem life_execution :
    BtcPolicy.ReceiptLifecycle.Execution (qcfg ilc) Ledger.current lcfg Kernel.current honest (runAll ilc life).1
      (runAll ilc life).2 :=
  BtcPolicy.ReceiptLifecycle.execution_of_legal (.init L0 layer_fresh) quota_on_layer.1

set_option synthInstance.maxSize 4096 in
/-- **A new lifetime queues the base again, and exposure stays** (`SPN-38`, `DUR-27`, `NCH-24`; the acceptance case
of `ReceiptQuota.birth_fresh`). After the evictions node 1 holds no record under the Escape's id. The request at wall
150 (step 17) births one, though the Escape it carries is marked released with latch 2 and floor 3: the record born
is unreleased at the empty release state. Node 1's fire pass (step 22) queues the base's row again and sets the
floor to 1. The rows of the first lifetime stay in the partial inventory: under the commitment it holds node 1's
base row, node 2's, `r2`'s row, then the base row and `r2`'s row again; and node 1's exposure history before the
re-registration is a prefix of its history at the end. -/
@[req "SPN-38"]
theorem rebirth_requeues :
    idsAt ilc life 17 1 = [] ∧ bornAt ilc life 17 1 es0.id = true ∧
      esRel.released = true ∧ esRel.track = { latch := 2, floor := 3 } ∧
      escAt ilc life 18 1 = [(false, { latch := 0, floor := 0 })] ∧
      added ilc life 22 es0.id = [part es0 1] ∧ escAt ilc life 23 1 = [(true, { latch := 0, floor := 1 })] ∧
      (runAll ilc life).2.ls.cs.sw.fed.parts.filter (·.cid == es0.id) =
        [part es0 1, part es0 2, rrow Exhibits.Ladder.r2, part es0 1, rrow Exhibits.Ladder.r2] ∧
      ((runL ilc life 17).2.ls.cs.sw.fed.worlds 1).exposure.isPrefixOf
        ((runAll ilc life).2.ls.cs.sw.fed.worlds 1).exposure = true ∧
      ((runL ilc life 17).2.ls.cs.sw.fed.worlds 1).exposure.length = 4 ∧
      ((runAll ilc life).2.ls.cs.sw.fed.worlds 1).exposure.length = 6 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
/-- **No limit spans the lifetimes** (`SPN-38`; the limit of the model). Over the history node 1 queues, under the one
commitment, the base's row and `r2`'s row in each lifetime: four rows, each pair within its own passes' accounts
(two slots consumed at each ladder pass, under `rung_budget = 598`). Nothing in the model bounds the rows of the two
lifetimes together: `Cursor.rungBudget` is a function of the quota alone, an eviction refunds only the Hot ledger,
and no rate limit shared across lifetimes (`NCH-15`) is represented. -/
@[req "SPN-38"]
theorem no_shared_limit :
    ((runAll ilc life).2.ls.cs.sw.fed.parts.filter fun x => x.cid == es0.id && x.signer == 1) =
        [part es0 1, rrow Exhibits.Ladder.r2, part es0 1, rrow Exhibits.Ladder.r2] ∧
      Cursor.rungBudget ilc.quota = 598 ∧
      (accounts ilc life 11 1).map (·.2.2.1) = [2] ∧ (accounts ilc life 23 1).map (·.2.2.1) = [2] := by
  decide +kernel

/-- `SPN-38`'s quota at 3, and a two-input Escape over the base's coin and a second coin of 1, retaining `r1` and
`r2`, read at a median of 200. -/
def qlc3 : Ladder.Cfg := { ilc with quota := 3 }
def esW : Cand :=
  { es0 with tx := { es0.tx with inputs := [coin, 77] }, above := [Exhibits.Ladder.R1, Exhibits.Ladder.R2] }
def vW : Backend := withMedian { v with confirmed := [(coin, 100), (77, 1)] } 200
/-- Nodes 1 and 2 take the request with `esW`; the truth moves to `vW`; node 1 fires and takes a ladder pass. -/
def starvedRun : Sched :=
  lfill qlc3 [] L0 (auto ((readFirst vm (pre esW ++ [.chain vW, fire 1, lad 1])).map fun s => .base (onBook s)))

set_option synthInstance.maxSize 4096 in
/-- **A starved record on the layer** (`SPN-38`: "If `affordable_rungs = 0`, release nothing"; the acceptance case of
`ReceiptQuota.starved_silent_layer`). At a quota of 3 the two-input Escape has no rung affordable. On a legal run of
the layer node 1's fire pass (step 8) starves it (`LadderRelease.starvedAt`) and queues nothing under its
commitment; its ladder pass (step 9) computes no interval, lists nothing and consumes nothing; the record stays
unreleased at the empty release state. -/
@[req "SPN-38"]
theorem starved_on_layer :
    legalL qlc3 starvedRun = true ∧ starvedRun.length = 10 ∧
      Cursor.affordableRungs qlc3.quota esW.tx.inputs.length = 0 ∧
      es0.id ∈ LadderRelease.starvedAt qlc3 (runL qlc3 starvedRun 8).2.ls.cs.sw (sweepOf (runL qlc3 starvedRun 8).1) 1 ∧
      added qlc3 starvedRun 8 es0.id = [] ∧
      accounts qlc3 starvedRun 9 1 = [(none, [], 0, { latch := 0, floor := 0 })] ∧
      added qlc3 starvedRun 9 es0.id = [] ∧ escAt qlc3 starvedRun 10 1 = [(false, { latch := 0, floor := 0 })] := by
  decide +kernel

end BtcPolicy.Exhibits.ReceiptQuota
