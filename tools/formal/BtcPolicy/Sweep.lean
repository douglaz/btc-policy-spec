import BtcPolicy.Federation
import BtcPolicy.Package
/-! The composed sweep: a federation execution over one backend world, where an honest node's
assembly of an Escape reads that world through its own observation. Each node moves by
`Kernel.step` through `Federation.apply` and nothing else; this module adds the backend, each
node's reads of it, and one guard on the assembly step. There is no second release machine here.

**The world.** `Sweep.Backend` is one instant of chain truth: the tip and the mempool sequence, the
confirmed vault outputs, the mempool's resident transactions with their ordered inputs, the
vault-script outputs of those transactions, and the confirmed transactions with their ordered
inputs, which only `BtcPolicy.Settlement` reads. `Step.chain` moves the truth to any instant, recording
the one it leaves, so a reorg, an eviction, a deposit and a confirmation are all in the alphabet and
none is required. `Step.observe` hands one node an instant the truth has actually been, now or
earlier: a node never reads a world that never existed, and it may read one that has since moved,
which is observation delay. Two nodes may hold different instants, and nothing makes them agree.

**What a node reads, and from where.** At its assembly a node reads, all from its latest
observation and its own projected history:

* `Sweep.authorized`, `SPN-33`'s vault-authorized set, written at acceptance: the txid of every
  candidate this node has registered, read off its history;
* `Sweep.snapshot`, `WTC-10`'s snapshot of that instant, which is `VaultUnspent.attempt` on the
  instant's own tip and sequence (`Sweep.snapshot_attempt`);
* `Sweep.passAt`, `DUR-22`'s pass, built by `VaultUnspent.passOf` from that snapshot, this node's
  selected Escapes and the instant's unconfirmed outputs whose creator is outside the set;
* the mempool membership read, the instant's own;
* `Federation.held`, this node's possession on every input.

`DUR-22` says the protected value "MUST be computed on every pass from this node's current reads and
never stored": an assembly consumes the observation it read, so the next one needs another.

**The guard.** `Sweep.check` is `DUR-24`'s coverage at that pass (`Coverage.covers` against
`Coverage.denominator`), `WTC-24`'s ancestry at that snapshot (`Package.validate`) and `DUR-28`'s
"`≥ t` distinct valid partials on every input" over the node's possession (`Authority.quorum`).
`Sweep.admits` lets a node take the kernel's `Event.packageAccepted` only when every resident
registered in the Escape role under that id passes it. No other step reads the backend.

**What it establishes.** `Sweep.fed_execution`: forgetting the backend leaves a
`Federation.Execution`, so every federation and kernel result applies. `Sweep.lift_unassembled`:
every federation history with no assembly is a sweep history over every backend world, so arming,
freezing and every release take place whatever the Escape's feasibility, and
`Sweep.armed_freezes_hot` holds on every sweep execution. `Sweep.assembled_of_packageOk`: an Escape
whose package test is standing was assembled earlier in the trace, at a state where it passed the
guard and the kernel's package test. `Sweep.submitted_in_order`: a submission happens at a send
whose own pre-state re-authorizes the candidate (`DUR-29`), after that assembly.
`Sweep.single_sweep_needs_common_floor` is `Coverage.per_node_single_sweep` with both coverage
verdicts read off two checks, at one node or two: what remains is a floor each measuring pass must
reach.

**Not modelled.** `DUR-21`'s check before release: here a fire pass's verdict (`Kernel.Env.withholds`) is
unconstrained, so a node may release an Escape's partial whatever the backend shows. The guard here sits at
assembly, where `DUR-28` requires the finalized transaction to "pass `DUR-23` and `DUR-24` again at its exact
vsize". `BtcPolicy.PreRelease` is this run with the check (`PreRelease.execution_iff`), and its results reach this
module through `PreRelease.to_sweep`. The ladder:
`Kernel.packageAccepted` assembles one rung per candidate, so `DUR-26`'s selection, `DUR-27`'s latch
and a resident lower rung's replacement are outside (`BtcPolicy.Ladder` checks them before release,
over reads supplied per pass, and is not this run), and `Package.validate` is read with no resident
named. `DUR-23`'s fee floor and vsize. `WTC-26`'s acceptance verdict: neither
`Kernel.packageAccepted` nor the guard is the backend's mempool-acceptance test.
`DUR-22`'s "Empty is an error". The kernel's own chain view (`Kernel.ChainView`, which
`Kernel.settle` reads) stays the per-step environment input it is in `Federation`, untied to the
backend here; `Settlement.Execution` ties it to each node's latest observation. What the backend
does with a submission, and whether anything
confirms, is not here: a submission is the kernel's broadcast effect and nothing more. A node's
mempool is the instant's own: two backends that disagree beyond delay are not represented.
Per-txid facts the kernel's `Tx` does not carry — each input's `witness_utxo` value, the outputs,
what reaches the escape descriptor — and each outpoint's creator are model parameters keyed by id,
as `Package.Creator` is. -/

namespace BtcPolicy.Sweep
open BtcPolicy.Clocks BtcPolicy.Kernel BtcPolicy.Federation
open BtcPolicy.Coverage (Coin Outpoint)
open BtcPolicy.VaultUnspent (Snapshot)

/-! ## The backend world -/

/-- One instant of chain truth. `pending` holds the vault-script outputs of the resident
transactions, each with its creating txid. -/
@[req "WTC-10"]
structure Backend where
  tip : Chain.Anchor
  sequence : Nat
  confirmed : List Coin
  mempool : Package.MempoolRead
  pending : List (Nat × Coin)
  /-- The transactions confirmed at this instant, each with its ordered inputs. -/
  mined : List (Nat × List Outpoint) := []
  /-- The block holding each confirmed transaction on this instant's chain, which only
  `BtcPolicy.Recovery` reads. A reorganization moves it. -/
  heights : List (Nat × Nat) := []
  /-- Each block's median-time-past on this instant's chain (BIP113), which only `BtcPolicy.Recovery`
  reads. -/
  mtps : List (Nat × Nat) := []
  /-- Each block's 50th-percentile feerate on this instant's chain, as the backend reports it (`WTC-15`),
  which only `BtcPolicy.RungRelease` reads, at the anchor of the tip (`DUR-30`). A block with no entry is
  an absent reading. -/
  medians : List (Nat × Nat) := []
  deriving DecidableEq, Repr

/-- An outpoint some resident transaction spends: the mempool-inclusive read drops it. -/
def spentInMempool (b : Backend) (o : Outpoint) : Bool := b.mempool.any fun m => m.2.contains o

/-- The view one instant shows: its own tip, active at its height. -/
def Backend.view (b : Backend) : Chain.View :=
  { activeAt := fun h => if h = b.tip.height then some b.tip.hash else none, tip := b.tip }

/-- The vault-unspent cache at that instant, anchored at its tip. -/
def Backend.cache (b : Backend) : VaultUnspent.Cache := { outputs := b.confirmed, anchor := b.tip }

/-- The unconfirmed outputs `WTC-10` adds: those of resident transactions in the authorized set,
not spent by another resident. -/
@[req "WTC-10"]
def additions (A : List Nat) (b : Backend) : List Coin :=
  (b.pending.filter fun p => A.contains p.1 && !spentInMempool b p.2.1).map (·.2)

/-- `WTC-10`'s snapshot of one instant, with the authorized set `A`: the confirmed outputs the
mempool-inclusive read keeps, then the additions. -/
@[req "WTC-10"]
def snapshot (A : List Nat) (b : Backend) : Snapshot :=
  { tip := b.tip, sequence := b.sequence,
    read := b.confirmed.filter (fun c => !spentInMempool b c.1) ++ additions A b }

/-- The snapshot is `VaultUnspent.attempt` over that instant: its cache at its tip, the
re-validation dropping what a resident spends, and a tip and sequence that did not move. -/
@[req "WTC-10"]
theorem snapshot_attempt (A : List Nat) (b : Backend) :
    VaultUnspent.attempt b.view b.cache b.sequence (fun c => !spentInMempool b c.1) (additions A b)
      b.tip b.sequence = some (snapshot A b) := by
  simp [VaultUnspent.attempt, VaultUnspent.fireTimeRead, Backend.cache, Backend.view, snapshot]

/-- The unconfirmed external deposits at that instant: the outputs of resident transactions
outside the authorized set (`DUR-22`). -/
@[req "DUR-22"]
def unconfirmedExternal (A : List Nat) (b : Backend) : List Outpoint :=
  (b.pending.filter fun p => !A.contains p.1).map (·.2.1)

/-! ## What the kernel's transaction does not carry -/

/-- Per-txid facts keyed by id: each outpoint's claimed `witness_utxo` value, a transaction's
outputs, and what it delivers to the escape descriptor (`DUR-24`). -/
structure Book where
  value : Outpoint → Nat
  outputs : Nat → List Outpoint
  delivered : Nat → Nat

/-- The sweep's parameters: the sealed coverage percentage (`MAN-9`), the federation's keys,
the book, each outpoint's creator, and the three guard parameters the reads go through. -/
structure Cfg where
  pct : Nat
  keys : List Nat
  book : Book
  creator : Package.Creator
  denominator : Coverage.Denominator
  external : Coverage.External
  ancestry : Package.ReplacementAncestry

/-- A transaction as the denominator sees it. -/
def escapeOf (bk : Book) (tx : Tx) : Coverage.Escape :=
  { id := tx.id, inputs := tx.inputs.map fun o => (o, bk.value o), outputs := bk.outputs tx.id,
    delivered := bk.delivered tx.id }

/-- A transaction as the ancestry walk sees it. -/
def candidateOf (tx : Tx) : Package.Candidate := { txid := tx.id, inputs := tx.inputs }

/-! ## A node's reads -/

/-- `SPN-33`: "On acceptance the node MUST add the spend's, the Escape's and every rung's txid to its
**vault-authorized set**". Here, the txid of every candidate this node has registered, read off its
registry now and before each step of its history. Nothing removes one. -/
@[req "SPN-33"]
def authorized (h : History) (n : Node) : List Nat :=
  n.cands.map (·.tx.id) ++ h.flatMap fun a => a.1.node.cands.map (·.tx.id)

/-- `DUR-10`'s `selected_escapes`, as the residents they name: each candidate registered in the
Escape role whose id the set carries. -/
@[req "DUR-22"]
def selectedEscapes (n : Node) : List Cand :=
  n.cands.filter fun c => c.isEscape && n.selected.any (·.1 == c.id)

/-- `DUR-22`'s pass at one node: the snapshot's read, the selected Escapes, the outputs of those
whose transaction is resident, and the unconfirmed external deposits. -/
@[req "DUR-22"]
def passAt (cfg : Cfg) (A : List Nat) (n : Node) (b : Backend) : Coverage.Pass :=
  VaultUnspent.passOf (snapshot A b) ((selectedEscapes n).map fun c => escapeOf cfg.book c.tx)
    (((selectedEscapes n).filter fun c => (b.mempool.lookup c.tx.id).isSome).flatMap
      fun c => cfg.book.outputs c.tx.id)
    (unconfirmedExternal A b)

/-- `DUR-24` on this candidate at that pass. -/
@[req "DUR-24"]
def covered (cfg : Cfg) (A : List Nat) (n : Node) (b : Backend) (c : Cand) : Bool :=
  Coverage.covers (cfg.book.delivered c.tx.id)
    (Coverage.denominator cfg.denominator cfg.external (passAt cfg A n b) (escapeOf cfg.book c.tx))
    cfg.pct

/-- `WTC-24` on this candidate at that snapshot, its membership read and the authorized set. -/
@[req "WTC-24"]
def ancestryOk (cfg : Cfg) (A : List Nat) (b : Backend) (c : Cand) : Bool :=
  (Package.validate cfg.ancestry cfg.creator (snapshot A b) b.mempool A (candidateOf c.tx)
    none).isAdmitted

/-- `DUR-28`'s possession on every input of this candidate's transaction. -/
@[req "DUR-28"]
def possessed (cfg : Cfg) (t : Nat) (R : List Authority.Sig) (c : Cand) : Bool :=
  Authority.quorum cfg.keys t c.tx R

/-! ## The composed state and steps -/

/-- The federation, the backend's truth now, every instant it has been, and each node's latest
observation. -/
structure State where
  fed : Fed
  truth : Backend
  past : List Backend := []
  obs : Nat → Option Backend := fun _ => none

inductive Step
  /-- A federation step, as `Federation.apply` takes it. -/
  | fed (s : Federation.Step)
  /-- The backend's truth moves to this instant. -/
  | chain (b : Backend)
  /-- A node reads an instant the truth has been. -/
  | observe (i : Nat) (b : Backend)
  deriving DecidableEq, Repr

/-- A composed history, newest first, each step with the state it was taken in. -/
abbrev Trace := List (State × Step)

/-- The federation steps of a composed history, with their federation states. -/
def fedTrace : Trace → Federation.Trace
  | [] => []
  | (st, .fed s) :: T => (st.fed, s) :: fedTrace T
  | _ :: T => fedTrace T

/-- The node and commitment of an assembly step. -/
def assembly : Federation.Step → Option (Nat × Nat)
  | .process i _ (.packageAccepted cid) => some (i, cid)
  | _ => none

/-- The authorized set node `i` reads in state `st` after history `T`. -/
def authorizedAt (st : State) (T : Trace) (i : Nat) : List Nat :=
  authorized (project i (fedTrace T)) (st.fed.worlds i).node

/-- The pass node `i` measures on, over instant `b`, in state `st` after history `T`. -/
def readsAt (cfg : Cfg) (st : State) (T : Trace) (i : Nat) (b : Backend) : Coverage.Pass :=
  passAt cfg (authorizedAt st T i) (st.fed.worlds i).node b

/-- The guard on one candidate at node `i`, in state `st` after history `T`: coverage, ancestry and
possession, each read from this node's latest observation and its own history. No observation, no
pass. -/
@[req "DUR-29"]
def check (cfg : Cfg) (st : State) (T : Trace) (i : Nat) (c : Cand) : Bool :=
  match st.obs i with
  | none => false
  | some b =>
    covered cfg (authorizedAt st T i) (st.fed.worlds i).node b c &&
      ancestryOk cfg (authorizedAt st T i) b c &&
      possessed cfg (st.fed.worlds i).node.t (held i (fedTrace T) st.fed) c

/-- An assembly of a commitment needs the guard on every resident registered in the Escape role
under that id. Every other step passes. -/
@[req "DUR-29"]
def assemblyOk (cfg : Cfg) (st : State) (T : Trace) : Federation.Step → Bool
  | .process i _ (.packageAccepted cid) =>
    (st.fed.worlds i).node.cands.all fun c => !(c.id == cid && c.isEscape) || check cfg st T i c
  | _ => true

/-- Which steps may be taken: a federation step its own guard admits and, for an assembly, the
sweep's; any move of the truth; an honest node's read of an instant the truth has been. -/
def admits (cfg : Cfg) (honest : List Nat) (st : State) (T : Trace) : Step → Bool
  | .fed s => Federation.admits honest st.fed s && assemblyOk cfg st T s
  | .chain _ => true
  | .observe i b => honest.contains i && (b == st.truth || st.past.contains b)

/-- The step. An assembly consumes its node's observation. -/
def apply (r : Rules) (st : State) : Step → State
  | .fed s =>
    { st with fed := Federation.apply r st.fed s,
              obs := match assembly s with
                | some (i, _) => fun j => if j = i then none else st.obs j
                | none => st.obs }
  | .chain b => { st with truth := b, past := st.truth :: st.past }
  | .observe i b => { st with obs := fun j => if j = i then some b else st.obs j }

/-- The transactions a step submits: the broadcast effects of the kernel step it runs. -/
def submits (r : Rules) (st : State) : Step → List Nat
  | .fed (.process i env e) =>
    (step r env (st.fed.worlds i) e).2.filterMap fun
      | .broadcast x => some x
      | _ => none
  | _ => []

/-- `Federation.Fresh`, no earlier instant and no observation. -/
def Fresh (honest : List Nat) (st : State) : Prop :=
  Federation.Fresh honest st.fed ∧ st.past = [] ∧ ∀ i, st.obs i = none

/-- A reachable composed execution, retaining its trace. -/
inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Step) (ha : admits cfg honest st T s = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s) :: T) (apply r st s)

/-! ## The federation underneath -/

/-- Forgetting the backend leaves a federation execution. -/
@[req "DUR-29"]
theorem fed_execution {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) : Federation.Execution r honest (fedTrace T) st.fed := by
  induction hx with
  | init st h => exact .init _ h.1
  | next s ha _ ih =>
    cases s with
    | fed s =>
      simp only [admits, Bool.and_eq_true] at ha
      exact .next s ha.1 ih
    | chain b => exact ih
    | observe i b => exact ih

theorem assemblyOk_of_none (cfg : Cfg) (st : State) (T : Trace) {s : Federation.Step}
    (h : assembly s = none) : assemblyOk cfg st T s = true := by
  cases s with
  | process i env e => cases e <;> simp_all [assembly, assemblyOk]
  | _ => rfl

/-- The composed trace of a federation trace over one fixed instant, with no observation. -/
def liftTrace (b : Backend) : Federation.Trace → Trace
  | [] => []
  | (f, s) :: t => ({ fed := f, truth := b }, .fed s) :: liftTrace b t

theorem fedTrace_lift (b : Backend) (t : Federation.Trace) : fedTrace (liftTrace b t) = t := by
  induction t with
  | nil => rfl
  | cons p t ih => obtain ⟨f, s⟩ := p; simp [liftTrace, fedTrace, ih]

/-- Arming and freezing do not wait on the Escape: every federation history with no assembly is a
sweep history over every backend instant, whatever that instant makes of the Escape. The receipts
that arm, the holder decisions that freeze every hot candidate, every release and every partial
are in such a history. -/
@[req "DUR-19"]
theorem lift_unassembled {cfg : Cfg} {r : Rules} {honest : List Nat} {t : Federation.Trace}
    {f : Fed} (hx : Federation.Execution r honest t f) (hno : ∀ p ∈ t, assembly p.2 = none)
    (b : Backend) :
    Execution cfg r honest (liftTrace b t) { fed := f, truth := b } ∧
      fedTrace (liftTrace b t) = t := by
  refine ⟨?_, fedTrace_lift b t⟩
  induction hx with
  | init f h => exact .init _ ⟨h, rfl, fun _ => rfl⟩
  | next s ha _ ih =>
    have hs : assembly s = none := hno _ List.mem_cons_self
    have hx' := Execution.next (cfg := cfg) (.fed s)
      (by simp [admits, ha, assemblyOk_of_none cfg _ _ hs])
      (ih fun p hp => hno p (List.mem_cons_of_mem _ hp))
    simpa [apply, hs] using hx'

/-- `DUR-11` on every sweep execution, whatever the backend: an armed honest node holds every hot
candidate frozen. -/
@[req "DUR-11"]
theorem armed_freezes_hot {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) : Kernel.Inv (st.fed.worlds i) :=
  inv_reachable r _ (project_execution (fed_execution hx) hi).reachable

/-! ## Assembly before send -/

theorem withWindow_packageOk (r : Rules) (sel : List (Nat × Bool)) (T : Wall) (slack : Secs)
    (c : Cand) : (withWindow r sel T slack c).packageOk = c.packageOk := by
  unfold withWindow; split <;> rfl

/-- A standing package test after a kernel step was standing before it on a resident with the same
id, transaction and pair, or the step is that id's package test and passed on such a resident. -/
@[req "SPN-39"]
theorem packageOk_origin (r : Rules) (env : Env) (w : World) (e : Event) {c : Cand}
    (hc : c ∈ (step r env w e).1.node.cands) (hp : c.packageOk = true) :
    (∃ d ∈ w.node.cands, d.id = c.id ∧ d.tx = c.tx ∧ d.pair = c.pair ∧ d.packageOk = true) ∨
    (e = .packageAccepted c.id ∧ ∃ d ∈ w.node.cands, d.id = c.id ∧ d.tx = c.tx ∧ d.pair = c.pair ∧
      due r env w.node d = true ∧ releaseAuthorized r w.node d = true ∧ d.released = true ∧
      heldQuorum w.node.t d = true) := by
  have keep (h : c ∈ w.node.cands) :
      ∃ d ∈ w.node.cands, d.id = c.id ∧ d.tx = c.tx ∧ d.pair = c.pair ∧ d.packageOk = true :=
    ⟨c, h, rfl, rfl, rfl, hp⟩
  have frame (f : Cand → Cand)
      (hf : ∀ d, (f d).id = d.id ∧ (f d).tx = d.tx ∧ (f d).pair = d.pair ∧
        (f d).packageOk = d.packageOk)
      (h : c ∈ w.node.cands.map f) :
      ∃ d ∈ w.node.cands, d.id = c.id ∧ d.tx = c.tx ∧ d.pair = c.pair ∧ d.packageOk = true := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2, h3, h4⟩ := hf d
    exact ⟨d, hd, h1.symm, h2.symm, h3.symm, by rw [← h4]; exact hp⟩
  cases e with
  | accept cid dd E sp es =>
    have reg (x : Cand) (hx : x ∈ register r w.node env sp es) (hpx : x.packageOk = true) :
        x ∈ w.node.cands := by
      rcases List.mem_cons.1 (mem_register hx) with rfl | hx
      · simp [born] at hpx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp [born] at hpx
      · exact hx
    refine .inl ?_
    simp only [step, accept] at hc
    split at hc
    · simp only [refuse] at hc
      split at hc
      · exact keep hc
      · split at hc <;> exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
          rw [withWindow_packageOk] at hp
          exact ⟨x, reg x hx hp, (withWindow_id ..).symm, (withWindow_tx ..).symm,
            (withWindow_pair ..).symm, hp⟩
        · exact keep (reg c hc hp)
  | receipt cid s =>
    refine .inl ?_
    simp only [step, receipt] at hc
    split at hc
    · exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · simp only [holderDecision] at hc
          exact frame _ (fun d => ⟨by rw [withWindow_id], by rw [withWindow_tx],
            by rw [withWindow_pair], by rw [withWindow_packageOk]⟩) hc
        · exact keep hc
  | refuse cid d E pair code =>
    refine .inl (keep ?_)
    simp only [step, refuse] at hc
    split at hc
    · exact hc
    · split at hc <;> exact hc
  | firePass =>
    refine .inl ?_
    simp only [step, firePass] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> simp) hc
  | ladderPass =>
    refine .inl ?_
    simp only [step, ladderPass] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by simp) hc
  | packageAccepted cid =>
    simp only [step, packageAccepted] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    by_cases h : (d.id == cid && due r env w.node d && releaseAuthorized r w.node d && d.released &&
        heldQuorum w.node.t d) = true
    · rw [if_pos h]
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      exact .inr ⟨by simp [h1], d, hd, rfl, rfl, rfl, h2, h3, h4, h5⟩
    · rw [if_neg h] at hp ⊢
      exact .inl ⟨d, hd, rfl, rfl, rfl, hp⟩
  | send cid =>
    refine .inl ?_
    simp only [step, send] at hc
    split at hc
    · exact keep hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      by_cases h : (d.id == cid) = true
      · rw [if_pos h] at hp; simp at hp
      · rw [if_neg h] at hp ⊢
        exact ⟨d, hd, rfl, rfl, rfl, hp⟩
  | settle tx =>
    refine .inl ?_
    simp only [step, settle] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> (try split) <;> simp) hc
  | prune => exact .inl (keep (List.mem_filter.1 hc).1)
  | tick | panic | adversaryExposes _ _ _ _ => exact .inl (keep hc)
  | receivePartial m i s cid' =>
    exact .inl (frame _ (fun d => by split <;> simp) hc)
  | clawback x =>
    rcases mem_clawback (by simpa [step] using hc) with hc | ⟨rfl, -⟩
    · exact .inl (keep hc)
    · simp [clawbackBorn, born] at hp

/-- Node `i` assembled this Escape earlier in `T`: an assembly step for its id, taken in a state where
a resident with the same id, transaction and pair passed the sweep's check against the reads of that
state and the kernel's own package test. `T₁` is the history before that step. -/
def Assembled (cfg : Cfg) (r : Rules) (T : Trace) (i : Nat) (c : Cand) : Prop :=
  ∃ T₁ T₂ st env d, T = T₂ ++ (st, .fed (.process i env (.packageAccepted c.id))) :: T₁ ∧
    d ∈ (st.fed.worlds i).node.cands ∧ d.id = c.id ∧ d.tx = c.tx ∧ d.pair = c.pair ∧
    check cfg st T₁ i d = true ∧ due r env (st.fed.worlds i).node d = true ∧
    releaseAuthorized r (st.fed.worlds i).node d = true ∧ d.released = true ∧
    heldQuorum (st.fed.worlds i).node.t d = true

theorem Assembled.cons {cfg : Cfg} {r : Rules} {T : Trace} {i : Nat} {c : Cand} (x : State × Step)
    (h : Assembled cfg r T i c) : Assembled cfg r (x :: T) i c := by
  obtain ⟨T₁, T₂, st, env, d, rfl, rest⟩ := h
  exact ⟨T₁, x :: T₂, st, env, d, rfl, rest⟩

theorem Assembled.congr {cfg : Cfg} {r : Rules} {T : Trace} {i : Nat} {c c' : Cand}
    (h : Assembled cfg r T i c) (h1 : c'.id = c.id) (h2 : c'.tx = c.tx) (h3 : c'.pair = c.pair) :
    Assembled cfg r T i c' := by
  obtain ⟨T₁, T₂, st, env, d, hT, hd, e1, e2, e3, rest⟩ := h
  exact ⟨T₁, T₂, st, env, d, by rw [h1]; exact hT, hd, e1.trans h1.symm, e2.trans h2.symm,
    e3.trans h3.symm, rest⟩

theorem isEscape_congr {c d : Cand} (h1 : d.id = c.id) (h3 : d.pair = c.pair) :
    d.isEscape = c.isEscape := by
  simp [Cand.isEscape, h1, h3]

theorem actor_packageAccepted {s : Federation.Step} {i : Nat} {env : Env} {cid : Nat}
    (h : actor s = some (i, env, .packageAccepted cid)) :
    s = .process i env (.packageAccepted cid) := by
  cases s <;> simp only [actor, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case process => obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  all_goals simp_all

/-- An Escape's standing package test was earned in this trace: some earlier assembly step passed
the sweep's check against that step's own reads, and the kernel's package test, on a resident with
the same id, transaction and pair. -/
@[req "DUR-29"]
theorem assembled_of_packageOk {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) :
    ∀ c ∈ (st.fed.worlds i).node.cands, c.isEscape = true → c.packageOk = true →
      Assembled cfg r T i c := by
  induction hx with
  | init st h =>
    intro c hc
    rw [(h.1.2.2 i hi).2.2.2.1] at hc
    cases hc
  | next s ha _ ih =>
    intro c hc he hp
    cases s with
    | chain b => exact (ih c hc he hp).cons _
    | observe j b => exact (ih c hc he hp).cons _
    | fed s =>
      simp only [apply] at hc
      cases hact : actor s with
      | none =>
        rw [apply_no_actor r _ s hact i] at hc
        exact (ih c hc he hp).cons _
      | some a =>
        obtain ⟨j, env, e⟩ := a
        rw [apply_of_actor r _ s hact i] at hc
        split at hc
        · rename_i hij
          subst hij
          rcases packageOk_origin r env _ e hc hp with
            ⟨d, hd, h1, h2, h3, hpd⟩ | ⟨rfl, d, hd, h1, h2, h3, hdue, hauth, hrel, hq⟩
          · exact ((ih d hd (by rw [isEscape_congr h1 h3]; exact he) hpd).congr h1.symm h2.symm
              h3.symm).cons _
          · have hs := actor_packageAccepted hact
            subst hs
            simp only [admits, assemblyOk, Bool.and_eq_true, List.all_eq_true] at ha
            have hck := ha.2 d hd
            simp only [h1, isEscape_congr h1 h3, he, beq_self_eq_true, Bool.and_self,
              Bool.not_true, Bool.false_or] at hck
            exact ⟨_, [], _, env, d, rfl, hd, h1, h2, h3, hck, hdue, hauth, hrel, hq⟩
        · exact (ih c hc he hp).cons _

/-- `DUR-29`'s order on every submission: what a send submits is a resident under that id whose
package test is standing and which the send's own state re-authorizes — due and released by
`DUR-10`'s gate, read at that step and not at the assembly — and, for an Escape, that package test
was earned at an earlier assembly that passed the sweep's check (`Sweep.Assembled`). -/
@[req "DUR-29"]
theorem submitted_in_order {cfg : Cfg} {r : Rules} (hr : r.reauth = .beforeSend) {honest : List Nat}
    {T : Trace} {st : State} (hx : Execution cfg r honest T st) {i : Nat} {env : Env} {cid x : Nat}
    (ha : admits cfg honest st T (.fed (.process i env (.send cid))) = true)
    (hs : x ∈ submits r st (.fed (.process i env (.send cid)))) :
    ∃ c ∈ (st.fed.worlds i).node.cands, c.id = cid ∧ c.tx.id = x ∧ c.packageOk = true ∧
      due r env (st.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.fed.worlds i).node c = true ∧
      (c.isEscape = true → Assembled cfg r T i c) := by
  have hi : i ∈ honest := by
    simp only [admits, Federation.admits, Bool.and_eq_true, List.contains_iff_mem] at ha
    exact ha.1.1
  simp only [submits, step, send] at hs
  split at hs
  · simp at hs
  · rename_i c hc
    have hcm := List.mem_of_find?_eq_some hc
    have hid : c.id = cid := by simpa using List.find?_some hc
    split at hs
    · rename_i hgo
      have hb : (Reauth.beforeSend == Reauth.beforeAssembly) = false := rfl
      simp only [hr, hb, Bool.false_or, Bool.and_eq_true] at hgo
      simp only [List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hs
      exact ⟨c, hcm, hid, hs.symm, hgo.1, hgo.2.1, hgo.2.2,
        fun he => assembled_of_packageOk hx hi c hcm he hgo.1⟩
    · simp at hs

/-! ## The common view a global result would need -/

/-- `Coverage.per_node_single_sweep` over two checks, at one node or two, at the passes they read:
both coverage verdicts and both passes come from the composed run (`Sweep.check`), and what remains
is the floor, stated here as each measuring pass's selected inputs reaching `S`, with `S` covering
the two deliveries. `Exhibits.Sweep.different_selected_sets` is a composed run in which that floor
fails at one node and both Escapes are submitted. -/
@[req "DUR-22"]
theorem single_sweep_needs_common_floor (cfg : Cfg) (hd : cfg.denominator = .restoreAll)
    (he : cfg.external = .countedWhenSpent) (hpct : Coverage.floorPct ≤ cfg.pct)
    {st₁ st₂ : State} {T₁ T₂ : Trace} {i j : Nat} {d₁ d₂ : Cand} {b₁ b₂ : Backend}
    (h₁ : check cfg st₁ T₁ i d₁ = true) (h₂ : check cfg st₂ T₂ j d₂ = true)
    (hb₁ : st₁.obs i = some b₁) (hb₂ : st₂.obs j = some b₂) (S : Nat) (hS : 0 < S)
    (hconserve : cfg.book.delivered d₁.tx.id + cfg.book.delivered d₂.tx.id ≤ S)
    (hf₁ : S ≤ Coverage.selectedInputs (readsAt cfg st₁ T₁ i b₁))
    (hf₂ : S ≤ Coverage.selectedInputs (readsAt cfg st₂ T₂ j b₂)) : False := by
  simp only [check, hb₁, Bool.and_eq_true] at h₁
  simp only [check, hb₂, Bool.and_eq_true] at h₂
  have c₁ := h₁.1.1
  have c₂ := h₂.1.1
  simp only [covered, hd, he] at c₁ c₂
  exact Coverage.per_node_single_sweep _ _ (escapeOf cfg.book d₁.tx) (escapeOf cfg.book d₂.tx)
    cfg.pct S hpct hS hconserve hf₁ hf₂ c₁ c₂

/-! ## Running a schedule -/

def legal (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → List Step → Bool
  | _, _, [] => true
  | T, st, s :: ss => admits cfg honest st T s && legal cfg r honest ((st, s) :: T) (apply r st s) ss

def record (r : Rules) : Trace → State → List Step → Trace × State
  | T, st, [] => (T, st)
  | T, st, s :: ss => record r ((st, s) :: T) (apply r st s) ss

theorem execution_of_legal {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {ss : List Step} (hl : legal cfg r honest T st ss = true) :
    Execution cfg r honest (record r T st ss).1 (record r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s hl.1 hx) hl.2

/-! ## Fixtures -/

namespace Cases
open BtcPolicy.Kernel.RegistrationCases
open BtcPolicy.Federation.Cases (fed0)

/-- Outpoints 0 and 1 are worth 40 and 60, outpoint 2 is worth 40 and outpoint 3 is worth 100.
`txE` (101) delivers 90 to the escape descriptor, its twin 103 delivers 40, and the two Escapes of
the split runs deliver 60 (201) and 140 (202). -/
def book : Book :=
  { value := fun o => if o == 0 then 40 else if o == 1 then 60 else if o == 2 then 40
      else if o == 3 then 100 else 0,
    outputs := fun tx => [tx + 1000],
    delivered := fun tx => if tx == 101 then 90 else if tx == 103 then 40 else if tx == 201 then 60
      else if tx == 202 then 140 else 0 }

/-- Outpoint 3 is created by the external transaction 300; every other outpoint by a confirmed
funding transaction, 7. -/
def creator : Package.Creator := fun o => if o == 3 then 300 else 7

/-- The coverage at `MAN-9`'s floor, keys 1 to 4, and the three guard values given. -/
def cfg (d : Coverage.Denominator) (x : Coverage.External) (g : Package.ReplacementAncestry) : Cfg :=
  { pct := Coverage.floorPct, keys := [1, 2, 3, 4], book, creator, denominator := d, external := x,
    ancestry := g }

/-- The vault: outpoints 0 and 1, confirmed, nothing resident. -/
def vault : Backend :=
  { tip := ⟨5, 105⟩, sequence := 1, confirmed := [(0, 40), (1, 60)], mempool := [], pending := [] }
/-- The same vault with a third confirmed output, outpoint 9, that no Escape spends. -/
def vaultLarge : Backend := { vault with confirmed := [(0, 40), (1, 60), (9, 1000)] }
/-- The vault after an external transaction, 777, became resident over outpoint 1. -/
def vaultConflict : Backend := { vault with sequence := 2, mempool := [(777, [1])] }

def start (b : Backend) : State := { fed := fed0, truth := b }

def duressAt (i cid : Nat) (sp es : Cand) : Step :=
  .fed (.process i env0 (.accept cid true (Wall.sample 200) sp es))
def assemble (i cid : Nat) (env : Env := envFire) : Step := .fed (.process i env (.packageAccepted cid))
def sendAt (i cid : Nat) (env : Env := envFire) : Step := .fed (.process i env (.send cid))

/-- Signer `s`'s partial over input `k` of a candidate, as `Federation.fanout` queues it. -/
def part (c : Cand) (s k : Nat) : Exp :=
  { msg := sighash c.tx k, input := k, signer := s, hot := c.hot, cid := c.id }

/-- Nodes 1 and 2 accept `(c1, e1)` under duress, relay, arm at their holder decisions and release
the Escape; the hot spend is frozen at both. -/
def armed : List Step :=
  [duressAt 1 10 c1 e1, duressAt 2 10 c1 e1, .fed (.emit 1 10), .fed (.emit 2 10),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩),
   .fed (.process 1 envFire .firePass), .fed (.process 2 envFire .firePass)]

/-- Then node 2's partial on each input of the Escape reaches node 1. -/
def delivered : List Step :=
  armed ++ [.fed (.deliverPartial 1 envFire (part e1 2 0)), .fed (.deliverPartial 1 envFire (part e1 2 1))]

/-- Then node 1 reads the vault and assembles. -/
def sweep : List Step := delivered ++ [.observe 1 vault, assemble 1 e1.id]

/-- Only input 0's partial reaches node 1. -/
def inputZeroOnly : List Step :=
  armed ++ [.fed (.deliverPartial 1 envFire (part e1 2 0)), .observe 1 vault]

/-- The truth moves after node 1's read and before its assembly, and node 1 reads again. -/
def movedBeforeAssembly : List Step :=
  delivered ++ [.observe 1 vault, .chain vaultConflict, .observe 1 vaultConflict]

/-- The truth moves after node 1's assembly and before its send, and node 1 reads again. -/
def movedBeforeSend : List Step := sweep ++ [.chain vaultConflict, .observe 1 vaultConflict]

/-- Two pairs at nodes 1 and 2, both under duress: `(c1, e1)` and `(c2, e2)`, whose Escapes spend
the same ordered outpoints, 0 and 1. Both Escapes are released and node 2's partials on both reach
node 1, which reads the vault. -/
def twoEscapes : List Step :=
  [duressAt 1 10 c1 e1, duressAt 1 20 c2 e2, duressAt 2 10 c1 e1, duressAt 2 20 c2 e2,
   .fed (.emit 1 10), .fed (.emit 1 20), .fed (.emit 2 10), .fed (.emit 2 20),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 1 env0 ⟨2, 20⟩),
   .fed (.deliver 2 env0 ⟨1, 10⟩), .fed (.deliver 2 env0 ⟨1, 20⟩),
   .fed (.process 1 envFire .firePass), .fed (.process 2 envFire .firePass),
   .fed (.deliverPartial 1 envFire (part e1 2 0)), .fed (.deliverPartial 1 envFire (part e1 2 1)),
   .fed (.deliverPartial 1 envFire (part e2 2 0)), .fed (.deliverPartial 1 envFire (part e2 2 1)),
   .observe 1 vault]

/-! Two input-disjoint pairs at four nodes: nodes 1 and 2 hold `(s1, f1)`, whose Escape spends
outpoint 1; nodes 3 and 4 hold `(s2, f2)`, whose Escape spends outpoints 2 and 3. Outpoint 3 is the
output of the external transaction 300, resident in the first instant and confirmed in the second;
in the second, `f1`'s transaction is resident over outpoint 1. -/

def txS1 : Tx := { id := 211, inputs := [1], outflow := 100 }
def txF1 : Tx := { id := 201, inputs := [1], outflow := 0 }
def txS2 : Tx := { id := 212, inputs := [2], outflow := 100 }
def txF2 : Tx := { id := 202, inputs := [2, 3], outflow := 0 }
def s1 : Cand := cand 11 txS1 true (some 100) 200
def f1 : Cand := cand 12 txF1 false none 200
def s2 : Cand := cand 13 txS2 true (some 100) 200
def f2 : Cand := cand 14 txF2 false none 200
def honest4 : List Nat := [1, 2, 3, 4]

def before : Backend :=
  { tip := ⟨5, 105⟩, sequence := 1, confirmed := [(1, 60), (2, 40)], mempool := [(300, [99])],
    pending := [(300, (3, 100))] }
def after : Backend :=
  { tip := ⟨6, 106⟩, sequence := 2, confirmed := [(1, 60), (2, 40), (3, 100)],
    mempool := [(201, [1])], pending := [] }

/-- Each pair's nodes arm and release; node 1 reads the first instant, assembles and sends `f1`;
the truth moves; node 3 reads the second instant and assembles `f2`. -/
def split : List Step :=
  [duressAt 1 10 s1 f1, duressAt 2 10 s1 f1, duressAt 3 20 s2 f2, duressAt 4 20 s2 f2,
   .fed (.emit 1 10), .fed (.emit 2 10), .fed (.emit 3 20), .fed (.emit 4 20),
   .fed (.deliver 1 env0 ⟨2, 10⟩), .fed (.deliver 2 env0 ⟨1, 10⟩),
   .fed (.deliver 3 env0 ⟨4, 20⟩), .fed (.deliver 4 env0 ⟨3, 20⟩),
   .fed (.process 1 envFire .firePass), .fed (.process 2 envFire .firePass),
   .fed (.process 3 envFire .firePass), .fed (.process 4 envFire .firePass),
   .fed (.deliverPartial 1 envFire (part f1 2 0)),
   .fed (.deliverPartial 3 envFire (part f2 4 0)), .fed (.deliverPartial 3 envFire (part f2 4 1)),
   .observe 1 before, assemble 1 f1.id, sendAt 1 f1.id, .chain after, .observe 3 after,
   assemble 3 f2.id]

end Cases

end BtcPolicy.Sweep
