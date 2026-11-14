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
