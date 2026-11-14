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

namespace BtcPolicy.Exhibits.TwoRun
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.Silence
open BtcPolicy.Exhibits.ReleaseKernel (cand envAt withdrawnTraversal withdrawnDynamics)

/-! ## SILENCE as a two-run relation: `DEF-12`'s marker, `F54`'s conditional traversal, `DUR-14`'s
static `T`, and the horizon itself

One request body under two enrolment tables (`Silence.Enrolment`): the same bytes, the same
delivery, the same chain view and the same samples, and only the class the table gives the
presented PIN differs. The workflow attributes each guard-parameter flip to the declarations it
refutes; the full-prefix exhibits also check coverage of the observation walk. -/


def sys0 : Sys := { world := { node := A, exposure := [] }, led := [] }




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
