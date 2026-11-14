import BtcPolicy.ClassAssembly
import BtcPolicy.Recovery
/-! A rung's transaction from its admitted assembly to the common submission history and the observations after it
(`DUR-29`, `DUR-31`), on the ladder-bearing run of `BtcPolicy.ClassAssembly`. On that run a rung's send reads
`RungAssembly.sendOk`, which asks only that the node assembled the rung's txid at some earlier step
(`RungAssembly.State.assembled`), so one assembly authorizes a send at any later pass, after a new registration
lifetime, and as often as the send's own state re-authorizes the Escape; a rung's assembly reads the node's observation
without consuming it, where the sweep's assembly consumes it (`Sweep.apply`); a rung's send is in neither
`Sweep.submits` nor `Recovery.St.sent`; and the kernel's send of an Escape stands on a package test set at an
earlier base assembly, read by no finalization. This module is a guard-and-bookkeeping layer over that run, as
`BtcPolicy.ClassAssembly` is over `RungAssembly`'s: no new kernel event and no existing definition changed. Its state
is `ClassAssembly`'s with three more fields (`Lifecycle.State`), its steps are `RungAssembly.Step` with
`ClassAssembly`'s labels, and every step it admits `ClassAssembly.admits` admits.

**The assembly's permission.** A rung's assembly at node `i` records a permit (`Lifecycle.Permit`): the node, the
commitment id, the rung index, the rung's txid and the observation the assembly read. A rung's send needs a live
permit for that rung and txid (`Lifecycle.sendOk`), and consumes every permit of the node under that id. The node's
permits are dropped at its fire pass, its ladder pass and its prune (`Lifecycle.ends`); a permit under `cid` at any
step after which node `i`'s registry holds more records under `cid` than before (`Lifecycle.births`), a fresh
registration of that commitment or a rebirth, and at node `i`'s settlement of a transaction of its Escape's ladder
under `cid` (`Lifecycle.settlesAt`). A new pass, a new registration lifetime or a settled rung needs a new assembly,
and with it the package check of that attempt (`Lifecycle.permit_lifetime`, `Lifecycle.permit_birth`,
`Lifecycle.permit_settle`, `Lifecycle.permit_consumed`). A settlement of an unrelated transaction keeps the permit. Under `Registration.preserve` an acceptance, refused or not, of a pair whose spend is
resident births nothing (`Lifecycle.accept_repeat_count`), so it keeps the permit. A rung's assembly needs a node whose current observation no rung assembly has read (`Lifecycle.State.used`);
the node's next observation clears it. This is the sweep's one assembly per observation, kept beside the sweep state so
that `ClassAssembly`'s state is the same.

**The send.** Besides the permit, `DUR-31`'s classification at the permit's observation: no rung of the Escape's
ladder confirmed, none at or above the latch resident ("a rung resident at or above the latch ⇒ nothing"), and the
rung being sent not resident either (`Lifecycle.quiet`). The send reads no backend: the observation is the attempt's.
On the base path a kernel send of a commitment id under which any resident is Escape-role is refused
(`Lifecycle.kernelSendOk`), so a selected Escape is sent through the rung's path alone, rung 0 included, and no Escape is
ever marked broadcast (`Lifecycle.escape_never_broadcast`), which is `DUR-31`'s "A selected Escape MUST NOT be marked
broadcast". Every base step's chain view is shown by the acting node's observation (`Settlement.readOk`).

**The submission history.** `Lifecycle.State.subs`, newest first, `(node, isEscape, tx)`: a kernel send adds
`Recovery.sentBy`'s entry and a rung's send adds `(node, true, rung tx)`; nothing removes one
(`Lifecycle.history_kept`). `Lifecycle.submitted_origin`: every Escape entry is a rung's, sent by an honest node at a
step whose own state re-authorizes the Escape (`Kernel.due`, `Kernel.releaseAuthorized`) on a live permit whose
observation the classification passed, recorded at an earlier admitted assembly of the same txid by the same node
with no step between that ends the node's permits or consumes them (`Lifecycle.Permitted`).
`Lifecycle.base_origin`: every other entry is a kernel send's, with `ClassAssembly.Assembled`'s origin. A send moves
no chain or ledger state (`Lifecycle.send_moves_no_chain`). `Lifecycle.awaiting_tie` reads `Recovery.awaiting` over the
history at the truth.

**The relation to the earlier layers.** Forgetting the three fields leaves a `ClassAssembly.Execution`
(`Lifecycle.to_classed`); forgetting the labels and the rung steps as well leaves a `LadderRelease.Execution`
(`Lifecycle.to_ladder`); the sweep steps are a `Settlement.Execution` (`Lifecycle.to_settlement`); and the labelled
federation steps of the classed run are a `VariantReceipt.Execution` (`ClassAssembly.to_labelled`). A result proved
over every execution of one of these four, or of a layer one of them projects to (`LadderRelease.to_sweep`,
`Settlement.to_sweep`, `Sweep.fed_execution`, `Federation.project_execution`), holds of this layer's runs through
these theorems. No theorem projects a run of this layer, or of `ClassAssembly`, onto a `RungAssembly.Execution` that
keeps its rung steps: `RungAssembly`'s broader possession can select a higher rung or count a partial the
variant-bound store refused (`Exhibits.ClassAssembly.mismatch_unassembled`), and `RungAssembly.of_ladder` reaches only
its runs with no rung step. `RungAssembly`'s results about rung steps are restated over the variant-bound possession
(`ClassAssembly.assemble_sound`, `ClassAssembly.assembled_origin`, `ClassAssembly.sent_in_order`,
`ClassAssembly.held_origin`), and this layer's own sends are stated by `Lifecycle.submitted_origin`. The relations run
one way: an earlier concrete execution is not thereby one of this layer's.

**Not modelled here.** The backend's package verdict and every chain event stay supplied, and nothing here concludes
an inclusion or a confirmation. Receipt-time expiry, `SPN-38`'s quota and cursor, the transaction bytes and the
scheduling of passes.

**A settled base.** `Kernel.settle` marks settled every resident whose transaction is the settled one, and an
Escape's own transaction is its base, so a node's settlement of its Escape's base, on a mempool sighting of another
sender's base as on a confirmation, marks the Escape settled. `Kernel.due` does not read that mark on an Escape-role
candidate (`Kernel.due_escape_pre`); `Kernel.duePre`, the earlier body, did, and refused every later rung send of the
Escape, as this layer's earlier theorem `settled_refuses_send` stated; that theorem is withdrawn with the repair. So
after the settlement `DUR-29`'s replacement of the resident base by a higher rung and `DUR-31`'s re-send
after a reorganization are admitted here (`Exhibits.Lifecycle.settled_base_blocks_replacement`,
`Exhibits.Lifecycle.settled_base_blocks_resend`), the latch and floor as they were (`Kernel.settle_track`,
`Lifecycle.ladder_track_mono`), and the settlement ends the node's permits under the id
(`Exhibits.Lifecycle.base_settle_ends_permit`). `SPN-39`'s first step is read at each attempt: the reading that
refuses a re-send is the permit's observation (`Lifecycle.quiet`), not the mark. On a history in which the node
settles no Escape's base, `due` and `duePre` agree on every resident at every state (`Lifecycle.no_settled_escape`,
`Lifecycle.due_eq_pre_run`). Below this layer the kernel's send reads no network, so a settled Escape is due again at
the fire pass, the package test and the kernel send there (`Exhibits.Lifecycle.settled_kernel_send_widened`), a
widening chosen explicitly; this layer refuses every kernel send of an Escape. -/

namespace BtcPolicy.Lifecycle
open BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.RungAssembly (Cfg Step escapeAt rungAt)

/-! ## The layer -/

/-- A live permission to send, recorded at a rung's assembly: the node, the commitment id, the rung index, the rung's
txid and the observation the assembly read. -/
structure Permit where
  node : Nat
  cid : Nat
  rung : Nat
  txid : Nat
  obs : Backend
  deriving DecidableEq, Repr

/-- `ClassAssembly`'s state, the live permits, the nodes whose current observation a rung assembly has read, and the
submission history, newest first, each entry the sending node, whether it is an Escape, and the transaction. -/
structure State where
  cs : RungAssembly.State
  perm : List Permit := []
  used : List Nat := []
  subs : List (Nat × Bool × Tx) := []

/-- A history, newest first, each step with the state it was taken in and its label. -/
abbrev Trace := List (State × Step × Option Nat)

/-- The history as `ClassAssembly`'s. -/
def toL (T : Trace) : ClassAssembly.LTrace := T.map fun a => (a.1.cs, a.2.1, a.2.2)

theorem toL_cons (st : State) (s : Step) (h : Option Nat) (T : Trace) :
    toL ((st, s, h) :: T) = (st.cs, s, h) :: toL T := rfl

/-- The kernel events at a node that end all its permits: a fire pass, a ladder pass and a prune. -/
def ends : Event → Bool
  | .firePass | .ladderPass | .prune => true
  | _ => false

/-- The node whose permits a sweep step ends. -/
def endsAt : Sweep.Step → Option Nat
  | .fed (.process i _ e) => if ends e then some i else none
  | _ => none

/-- How many records node `j`'s registry holds under id `cid`. -/
def countAt (sw : Sweep.State) (j cid : Nat) : Nat := (sw.fed.worlds j).node.cands.countP (·.id == cid)

/-- Whether a sweep step births a record under `cid` at node `j`: after it, node `j`'s registry holds more records
with that id than before, as at a fresh registration, or a rebirth under `Registration.rebirth`. A refused request,
which leaves the registry as it was, and a repeat that `Registration.preserve` leaves exactly as is, birth nothing. -/
def births (r : Rules) (sw : Sweep.State) (s : Sweep.Step) (j cid : Nat) : Bool :=
  decide (countAt sw j cid < countAt (Sweep.apply r sw s) j cid)

/-- Whether a sweep step is node `j`'s settlement of a transaction of the ladder of its Escape-role resident under
`cid` (`RungAssembly.escapeAt`), read in the state before it. A settlement of any other transaction is not one. -/
def settlesAt (sw : Sweep.State) (s : Sweep.Step) (j cid : Nat) : Bool :=
  match s with
  | .fed (.process i _ (.settle tx)) => i == j &&
    match escapeAt (sw.fed.worlds i).node cid with
    | some c => c.ladder.any (·.tx.id == tx.id)
    | none => false
  | _ => false

/-- Whether a step taken in state `st` keeps a permit of node `i` under commitment `cid`: not node `i`'s pass or
prune, not a birth under `cid` at node `i`, not node `i`'s settlement of a rung of its Escape under `cid`, and not node
`i`'s send under `cid`. -/
def keeps (r : Rules) (i cid : Nat) (st : State) : Step → Bool
  | .base s => (match endsAt s with
      | some j => i != j
      | none => true) && !births r st.cs.sw s i cid && !settlesAt st.cs.sw s i cid
  | .assemble .. => true
  | .send j _ c _ => !(i == j && cid == c)

/-- A kernel send of commitment `cid` at node `i` needs no Escape-role resident under that id. Every other step
passes. -/
@[req "DUR-31"]
def kernelSendOk (st : RungAssembly.State) : Sweep.Step → Bool
  | .fed (.process i _ (.send cid)) =>
    !((st.sw.fed.worlds i).node.cands.any fun c => c.id == cid && c.isEscape)
  | _ => true

/-- `DUR-31`'s classification of candidate `c`'s ladder at observation `b` for a send of rung `m`: no rung confirmed,
and none at or above the latch, nor rung `m` itself, resident. -/
@[req "DUR-31"]
def quiet (b : Backend) (c : Cand) (m : Nat) : Bool :=
  (List.range c.ladder.length).all fun k =>
    match c.ladder[k]? with
    | none => true
    | some g => !Settlement.confirmedAt b g.tx &&
        !((decide (c.track.latch ≤ k) || k == m) && Settlement.resident b g.tx)

/-- A live permit of node `i` for rung `m` of `c` under `cid`, with txid `g`'s, whose observation is quiet. -/
def permitOk (st : State) (i cid m : Nat) (c : Cand) (g : Rung) : Bool :=
  st.perm.any fun p => p.node == i && p.cid == cid && p.rung == m && p.txid == g.tx.id && quiet p.obs c m

/-- What a rung's send needs here beyond `RungAssembly.sendOk`: a live permit for that rung of the node's
Escape-role resident under the id. -/
@[req "DUR-29"]
def sendOk (st : State) (i cid m : Nat) : Bool :=
  match escapeAt (st.cs.sw.fed.worlds i).node cid with
  | none => false
  | some c =>
    match c.ladder[m]? with
    | none => false
    | some g => permitOk st i cid m c g

/-- Which steps may be taken: a step `ClassAssembly.admits` admits and, for a sweep step, its chain view read off the
acting node's observation and no kernel send of an Escape; for a rung's assembly, an observation no rung assembly has
read; for a rung's send, a live permit. -/
def admits (cfg : Cfg) (r : Rules) (honest : List Nat) (st : State) (T : Trace) : Step → Bool
  | .base s => ClassAssembly.admits cfg r honest st.cs (toL T) (.base s) && Settlement.readOk st.cs.sw s &&
      kernelSendOk st.cs s
  | .assemble i cid m => ClassAssembly.admits cfg r honest st.cs (toL T) (.assemble i cid m) && !st.used.contains i
  | .send i env cid m => ClassAssembly.admits cfg r honest st.cs (toL T) (.send i env cid m) && sendOk st i cid m

/-- The permits after a step. -/
def permAfter (r : Rules) (st : State) : Step → List Permit
  | .base s => st.perm.filter fun p => keeps r p.node p.cid st (.base s)
  | .assemble i cid m =>
    match rungAt (st.cs.sw.fed.worlds i).node cid m, st.cs.sw.obs i with
    | some g, some b => ⟨i, cid, m, g.tx.id, b⟩ :: st.perm
    | _, _ => st.perm
  | .send i _ cid _ => st.perm.filter fun p => !(p.node == i && p.cid == cid)

/-- The nodes whose current observation a rung assembly has read, after a step. -/
def usedAfter (st : State) : Step → List Nat
  | .base (.observe i _) => st.used.filter (· != i)
  | .assemble i _ _ => i :: st.used
  | _ => st.used

/-- What a sweep step submits, with its node: `Recovery.sentBy`'s entry of a kernel send. -/
def sentAt (r : Rules) (sw : Sweep.State) (s : Sweep.Step) : List (Nat × Bool × Tx) :=
  match s with
  | .fed (.process i _ (.send _)) => (Recovery.sentBy r sw s).map fun p => (i, p)
  | _ => []

/-- The submission history after a step. -/
def subsAfter (r : Rules) (st : State) : Step → List (Nat × Bool × Tx)
  | .base s => sentAt r st.cs.sw s ++ st.subs
  | .assemble .. => st.subs
  | .send i _ cid m =>
    match rungAt (st.cs.sw.fed.worlds i).node cid m with
    | some g => (i, true, g.tx) :: st.subs
    | none => st.subs

def apply (r : Rules) (st : State) (s : Step) : State :=
  { cs := RungAssembly.apply r st.cs s, perm := permAfter r st s, used := usedAfter st s, subs := subsAfter r st s }

/-- A fresh start: `RungAssembly`'s, no permit, no read consumed, nothing submitted. -/
def Fresh (honest : List Nat) (st : State) : Prop :=
  RungAssembly.Fresh honest st.cs ∧ st.perm = [] ∧ st.used = [] ∧ st.subs = []

/-- A reachable execution of the layer. -/
inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Step) (h : Option Nat) (ha : admits cfg r honest st T s = true)
      (hl : ClassAssembly.labelOk r st.cs (toL T) s h = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s, h) :: T) (apply r st s)

/-! ## The relation to the earlier layers -/

theorem admits_classed {cfg : Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {s : Step}
    (h : admits cfg r honest st T s = true) : ClassAssembly.admits cfg r honest st.cs (toL T) s = true := by
  cases s with
  | base b => simp only [admits, Bool.and_eq_true] at h; exact h.1.1
  | assemble i cid m => simp only [admits, Bool.and_eq_true] at h; exact h.1
  | send i env cid m => simp only [admits, Bool.and_eq_true] at h; exact h.1

theorem admits_base {cfg : Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {b : Sweep.Step}
    (h : admits cfg r honest st T (.base b) = true) :
    ClassAssembly.admits cfg r honest st.cs (toL T) (.base b) = true ∧ Settlement.readOk st.cs.sw b = true ∧
      kernelSendOk st.cs b = true := by
  simp only [admits, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The layer over `ClassAssembly`.** Forgetting the permits, the consumed reads and the submission history leaves a
`ClassAssembly.Execution`, so every result over all of its executions applies. -/
@[req "DUR-29"]
theorem to_classed {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) : ClassAssembly.Execution cfg r honest (toL T) st.cs := by
  induction hx with
  | init st h => exact .init _ h.1
  | next s h ha hl _ ih => exact .next s h (admits_classed ha) hl ih

/-- Forgetting the labels, the rung steps and the three fields leaves a `LadderRelease.Execution`. -/
theorem to_ladder {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) :
    LadderRelease.Execution cfg.lc r honest (ClassAssembly.sweepT (toL T)) st.cs.sw :=
  ClassAssembly.to_ladder (to_classed hx)

/-- **The sweep steps read the chain through observation.** They are a `Settlement.Execution`, so its results apply:
every settlement a node acts on was shown to it, and exposure survives every chain move. -/
@[req "SPN-33"]
theorem to_settlement {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) :
    Settlement.Execution cfg.lc.pre.sweep r honest (ClassAssembly.sweepT (toL T)) st.cs.sw := by
  induction hx with
  | init st h => exact .init _ h.1.1
  | @next T st s h ha hl _ ih =>
    cases s with
    | base b =>
      obtain ⟨hc, hr, -⟩ := admits_base ha
      simp only [ClassAssembly.admits, LadderRelease.admits, Bool.and_eq_true] at hc
      exact .next b (by simp only [Settlement.admits, Bool.and_eq_true]; exact ⟨hc.1.1, hr⟩) ih
    | assemble i cid m =>
      have e : (apply r st (.assemble i cid m)).cs.sw = st.cs.sw :=
        RungAssembly.apply_sw (s := .assemble i cid m) r st.cs (by simp)
      rw [e]; exact ih
    | send i env cid m =>
      have e : (apply r st (.send i env cid m)).cs.sw = st.cs.sw :=
        RungAssembly.apply_sw (s := .send i env cid m) r st.cs (by simp)
      rw [e]; exact ih

/-- A step of an execution was admitted at its own state, after a reachable history, with an admissible label. -/
theorem prefix_exec {cfg : Cfg} {r : Rules} {honest : List Nat} :
    ∀ {T : Trace} {st : State}, Execution cfg r honest T st →
      ∀ {T₂ T₁ : Trace} {st₀ : State} {s : Step} {h : Option Nat}, T = T₂ ++ (st₀, s, h) :: T₁ →
        Execution cfg r honest T₁ st₀ ∧ admits cfg r honest st₀ T₁ s = true := by
  intro T st hx
  induction hx with
  | init st h => intro T₂ T₁ st₀ s h' hT; cases T₂ <;> cases hT
  | next s' h' ha hl hx ih =>
    intro T₂ T₁ st₀ s h hT
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hT
      exact ⟨hx, ha⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      exact ih hT.2

/-! ## No Escape is marked broadcast -/

/-- A candidate marked broadcast after a kernel step was marked before it on a resident with the same id and pair, or
the step is a send of its id over such a resident. -/
theorem broadcast_origin (r : Rules) (env : Env) (w : World) (e : Event) {c : Cand}
    (hc : c ∈ (step r env w e).1.node.cands) (hb : c.broadcast = true) :
    (∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair ∧ d.broadcast = true) ∨
    (e = .send c.id ∧ ∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair) := by
  have keep (h : c ∈ w.node.cands) : ∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair ∧ d.broadcast = true :=
    ⟨c, h, rfl, rfl, hb⟩
  have frame (f : Cand → Cand)
      (hf : ∀ d, (f d).id = d.id ∧ (f d).pair = d.pair ∧ (f d).broadcast = d.broadcast)
      (h : c ∈ w.node.cands.map f) :
      ∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair ∧ d.broadcast = true := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2, h3⟩ := hf d
    exact ⟨d, hd, h1.symm, h2.symm, by rw [← h3]; exact hb⟩
  cases e with
  | accept cid dd E sp es =>
    have reg (x : Cand) (hx : x ∈ register r w.node env sp es) (hbx : x.broadcast = true) :
        x ∈ w.node.cands := by
      rcases List.mem_cons.1 (mem_register hx) with rfl | hx
      · simp [born] at hbx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp [born] at hbx
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
          rw [withWindow_broadcast] at hb
          exact ⟨x, reg x hx hb, (withWindow_id ..).symm, (withWindow_pair ..).symm, hb⟩
        · exact keep (reg c hc hb)
  | receipt cid s =>
    refine .inl ?_
    simp only [step, receipt] at hc
    split at hc
    · exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · simp only [holderDecision] at hc
          exact frame _ (fun d => ⟨by rw [withWindow_id], by rw [withWindow_pair],
            by rw [withWindow_broadcast]⟩) hc
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
    · exact frame _ (fun d => by split <;> (try split) <;> simp) hc
  | ladderPass =>
    refine .inl ?_
    simp only [step, ladderPass] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by simp) hc
  | packageAccepted cid =>
    simp only [step, packageAccepted] at hc
    exact .inl (frame _ (fun d => by split <;> simp) hc)
  | send cid =>
    simp only [step, send] at hc
    split at hc
    · exact .inl (keep hc)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      by_cases h : (d.id == cid) = true
      · rw [if_pos h] at hb ⊢
        have hid : d.id = cid := by simpa using h
        cases hdb : d.broadcast
        · exact .inr ⟨by simp [hid], d, hd, rfl, rfl⟩
        · exact .inl ⟨d, hd, rfl, rfl, hdb⟩
      · rw [if_neg h] at hb ⊢
        exact .inl ⟨d, hd, rfl, rfl, hb⟩
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
    · simp [clawbackBorn, born] at hb

theorem actor_send {s : Federation.Step} {i : Nat} {env : Env} {cid : Nat}
    (h : Federation.actor s = some (i, env, .send cid)) : s = .process i env (.send cid) := by
  cases s <;> simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case process => obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  all_goals simp_all

/-- **No Escape is marked broadcast** (`DUR-31`: "A selected Escape MUST NOT be marked broadcast"). At every state of
an execution, no Escape-role resident of an honest node carries the kernel's broadcast bit: its sends go through the
rung's path, rung 0 included, which sets none. -/
@[req "DUR-31"]
theorem escape_never_broadcast {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) :
    ∀ c ∈ (st.cs.sw.fed.worlds i).node.cands, c.isEscape = true → c.broadcast = false := by
  induction hx with
  | init st h =>
    intro c hc
    rw [(h.1.1.1.2.2 i hi).2.2.2.1] at hc
    cases hc
  | @next T st s lab ha hl _ ih =>
    intro c hc he
    cases s with
    | assemble j cid m =>
      have e : (apply r st (.assemble j cid m)).cs.sw = st.cs.sw :=
        RungAssembly.apply_sw (s := .assemble j cid m) r st.cs (by simp)
      rw [e] at hc; exact ih c hc he
    | send j env cid m =>
      have e : (apply r st (.send j env cid m)).cs.sw = st.cs.sw :=
        RungAssembly.apply_sw (s := .send j env cid m) r st.cs (by simp)
      rw [e] at hc; exact ih c hc he
    | base b =>
      cases b with
      | chain b => exact ih c hc he
      | observe j b => exact ih c hc he
      | fed s =>
        have hc' : c ∈ ((Federation.apply r st.cs.sw.fed s).worlds i).node.cands := hc
        cases hact : Federation.actor s with
        | none =>
          rw [Federation.apply_no_actor r _ s hact i] at hc'
          exact ih c hc' he
        | some a =>
          obtain ⟨j, env, e⟩ := a
          rw [Federation.apply_of_actor r _ s hact i] at hc'
          split at hc'
          · rename_i hij
            subst hij
            cases hb : c.broadcast
            · rfl
            · exfalso
              rcases broadcast_origin r env _ e hc' hb with ⟨d, hd, h1, h2, h3⟩ | ⟨rfl, d, hd, h1, h2⟩
              · have hde : d.isEscape = true := by rw [Sweep.isEscape_congr h1 h2]; exact he
                rw [ih d hd hde] at h3
                cases h3
              · have hs := actor_send hact
                subst hs
                obtain ⟨-, -, hk⟩ := admits_base ha
                simp only [kernelSendOk, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
                  not_and] at hk
                have hde : d.isEscape = true := by rw [Sweep.isEscape_congr h1 h2]; exact he
                exact hk d hd h1 hde
          · exact ih c hc' he

/-! ## A settled Escape -/

/-- A candidate marked settled after a kernel step was marked before it on a resident with the same id and pair, or
the step is a settlement of a transaction with the txid of such a resident. -/
theorem settled_origin (r : Rules) (env : Env) (w : World) (e : Event) {c : Cand}
    (hc : c ∈ (step r env w e).1.node.cands) (hs : c.settled = true) :
    (∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair ∧ d.settled = true) ∨
    (∃ tx, e = .settle tx ∧ ∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair ∧ d.tx.id = tx.id) := by
  have keep (h : c ∈ w.node.cands) : ∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair ∧ d.settled = true :=
    ⟨c, h, rfl, rfl, hs⟩
  have frame (f : Cand → Cand)
      (hf : ∀ d, (f d).id = d.id ∧ (f d).pair = d.pair ∧ (f d).settled = d.settled)
      (h : c ∈ w.node.cands.map f) :
      ∃ d ∈ w.node.cands, d.id = c.id ∧ d.pair = c.pair ∧ d.settled = true := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2, h3⟩ := hf d
    exact ⟨d, hd, h1.symm, h2.symm, by rw [← h3]; exact hs⟩
  have wset : ∀ sel T slack (d : Cand), (withWindow r sel T slack d).settled = d.settled := by
    intro sel T slack d; unfold withWindow; split <;> rfl
  cases e with
  | accept cid dd E sp es =>
    have reg (x : Cand) (hx : x ∈ register r w.node env sp es) (hsx : x.settled = true) :
        x ∈ w.node.cands := by
      rcases List.mem_cons.1 (mem_register hx) with rfl | hx
      · simp [born] at hsx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp [born] at hsx
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
          rw [wset] at hs
          exact ⟨x, reg x hx hs, (withWindow_id ..).symm, (withWindow_pair ..).symm, hs⟩
        · exact keep (reg c hc hs)
  | receipt cid s =>
    refine .inl ?_
    simp only [step, receipt] at hc
    split at hc
    · exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · simp only [holderDecision] at hc
          exact frame _ (fun d => ⟨by rw [withWindow_id], by rw [withWindow_pair], by rw [wset]⟩) hc
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
    · exact frame _ (fun d => by split <;> (try split) <;> simp) hc
  | ladderPass =>
    refine .inl ?_
    simp only [step, ladderPass] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by simp) hc
  | packageAccepted cid =>
    simp only [step, packageAccepted] at hc
    exact .inl (frame _ (fun d => by split <;> simp) hc)
  | send cid =>
    simp only [step, send] at hc
    split at hc
    · exact .inl (keep hc)
    · exact .inl (frame _ (fun d => by split <;> simp) hc)
  | settle tx =>
    simp only [step, settle] at hc
    split at hc
    · exact .inl (keep hc)
    · obtain ⟨d, hd, hdc⟩ := List.mem_map.1 hc
      split at hdc
      · rename_i h
        subst hdc
        exact .inr ⟨tx, rfl, d, hd, rfl, rfl, by simpa using h⟩
      · refine .inl ⟨d, hd, ?_⟩
        split at hdc <;> subst hdc <;> exact ⟨rfl, rfl, hs⟩
  | prune => exact .inl (keep (List.mem_filter.1 hc).1)
  | tick | panic | adversaryExposes _ _ _ _ => exact .inl (keep hc)
  | receivePartial m i s cid' =>
    exact .inl (frame _ (fun d => by split <;> simp) hc)
  | clawback x =>
    rcases mem_clawback (by simpa [step] using hc) with hc | ⟨rfl, -⟩
    · exact .inl (keep hc)
    · simp [clawbackBorn, born] at hs

/-- Whether federation step `s` is node `i`'s settlement of a transaction with the txid of an Escape-role resident
of node `i`, read in `f`: its base, since an Escape's own transaction is its base. -/
def settlesEscape (f : Federation.Fed) (s : Federation.Step) (i : Nat) : Bool :=
  match s with
  | .process j _ (.settle tx) => j == i && (f.worlds i).node.cands.any fun c => c.isEscape && c.tx.id == tx.id
  | _ => false

/-- **No Escape is marked settled before its node settles its base.** At every state of a federation execution, an
honest node none of whose steps settled the base of an Escape-role resident holds no Escape-role resident marked
settled. -/
@[req "SPN-33"]
theorem no_settled_escape {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Federation.Fed}
    (hx : Federation.Execution r honest t f) {i : Nat} (hi : i ∈ honest)
    (hn : ∀ y ∈ t, settlesEscape y.1 y.2 i = false) :
    ∀ c ∈ (f.worlds i).node.cands, c.isEscape = true → c.settled = false := by
  induction hx with
  | init f h =>
    intro c hc
    rw [(h.2.2 i hi).2.2.2.1] at hc
    cases hc
  | @next t f s _ _ ih =>
    have ih' := ih fun y hy => hn y (List.mem_cons_of_mem _ hy)
    have hs0 := hn (f, s) (List.mem_cons_self ..)
    intro c hc he
    cases hact : Federation.actor s with
    | none =>
      rw [Federation.apply_no_actor r _ s hact i] at hc
      exact ih' c hc he
    | some a =>
      obtain ⟨j, env, e⟩ := a
      rw [Federation.apply_of_actor r _ s hact i] at hc
      split at hc
      · rename_i hij
        subst hij
        cases hb : c.settled
        · rfl
        · exfalso
          rcases settled_origin r env _ e hc hb with ⟨d, hd, h1, h2, h3⟩ | ⟨tx, rfl, d, hd, h1, h2, h3⟩
          · have hde : d.isEscape = true := by rw [Sweep.isEscape_congr h1 h2]; exact he
            rw [ih' d hd hde] at h3
            cases h3
          · have hde : d.isEscape = true := by rw [Sweep.isEscape_congr h1 h2]; exact he
            have hps : s = .process i env (.settle tx) := by
              cases s <;> simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hact
              case process => obtain ⟨rfl, rfl, rfl⟩ := hact; rfl
              all_goals simp_all
            subst hps
            simp only [settlesEscape, beq_self_eq_true, Bool.true_and, List.any_eq_false, Bool.and_eq_true,
              beq_iff_eq, not_and] at hs0
            exact hs0 d hd hde h3
      · exact ih' c hc he

/-- **Off a settled Escape the change is invisible** (`SPN-38`). On such a history every resident of the node is due
under `Kernel.due` exactly when it is under `Kernel.duePre`, at every environment, so every reader of `due` at that
state reads what it read before. -/
@[req "SPN-38"]
theorem due_eq_pre_run {r : Rules} {honest : List Nat} {t : Federation.Trace} {f : Federation.Fed}
    (hx : Federation.Execution r honest t f) {i : Nat} (hi : i ∈ honest)
    (hn : ∀ y ∈ t, settlesEscape y.1 y.2 i = false) (env : Env) :
    ∀ c ∈ (f.worlds i).node.cands, due r env (f.worlds i).node c = duePre r env (f.worlds i).node c :=
  due_eq_pre_node r env _ (no_settled_escape hx hi hn)

/-- **An admitted ladder pass lowers no latch or floor** (`DUR-27`). After an honest node's ladder pass that
`RungRelease.admits`, each resident has the id and pair of one before it whose floor it does not lower, nor its
latch while that latch is on the ladder the resident's read gives. A settled Escape, which `Kernel.due` no longer
refuses, takes ladder passes again under this. -/
@[req "DUR-27"]
theorem ladder_track_mono {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules) :
    ∀ c' ∈ ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands,
      ∃ c ∈ (st.fed.worlds i).node.cands, c'.id = c.id ∧ c'.pair = c.pair ∧ c.track.floor ≤ c'.track.floor ∧
        (c.track.latch < (Ladder.txs (RungRelease.readAt st T i c) c).length → c.track.latch ≤ c'.track.latch) := by
  intro c' hc'
  rw [Federation.apply_of_actor r _ _ rfl i, if_pos rfl] at hc'
  simp only [step, ladderPass] at hc'
  split at hc'
  · exact ⟨c', hc', rfl, rfl, Nat.le_refl _, fun _ => Nat.le_refl _⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine ⟨c, hc, rfl, rfl, ?_⟩
    cases hl : ladderAt r env (st.fed.worlds i).node c with
    | none => simp
    | some p =>
      obtain ⟨tr, ms⟩ := p
      obtain ⟨-, -, -, -, hrel⟩ := RungRelease.ladderAt_own ha r hc hl
      simp only [Option.map_some, Option.getD_some]
      have hf := Ladder.release_floor lc (RungRelease.readAt st T i c) c c.track
      have hla := Ladder.release_latch lc (RungRelease.readAt st T i c) c c.track
      rw [hrel] at hf hla
      exact ⟨hf, fun h => (hla h).1⟩

/-! ## The permits -/

/-- Permit `p` was recorded earlier in `T`, `T₁` the history before that step: an admitted rung assembly of its rung
at its node under its id, `ClassAssembly.assembleOk` at that state, at a node whose current observation no rung
assembly had read, that observation the permit's, and the rung's txid the permit's; and no step since, in `T₂`, ended
the node's permits or consumed them, each read at the state it was taken in (`Lifecycle.keeps`). -/
def Permitted (cfg : Cfg) (r : Rules) (T : Trace) (p : Permit) : Prop :=
  ∃ T₁ T₂ st h, T = T₂ ++ (st, .assemble p.node p.cid p.rung, h) :: T₁ ∧
    ClassAssembly.assembleOk cfg st.cs (toL T₁) p.node p.cid p.rung = true ∧ p.node ∉ st.used ∧
    st.cs.sw.obs p.node = some p.obs ∧
    (∃ g, rungAt (st.cs.sw.fed.worlds p.node).node p.cid p.rung = some g ∧ g.tx.id = p.txid) ∧
    ∀ q ∈ T₂, keeps r p.node p.cid q.1 q.2.1 = true

theorem Permitted.cons {cfg : Cfg} {r : Rules} {T : Trace} {p : Permit} (y : State × Step × Option Nat)
    (h : Permitted cfg r T p) (hk : keeps r p.node p.cid y.1 y.2.1 = true) : Permitted cfg r (y :: T) p := by
  obtain ⟨T₁, T₂, st, h', rfl, h1, h2, h3, h4, hT₂⟩ := h
  refine ⟨T₁, y :: T₂, st, h', rfl, h1, h2, h3, h4, fun q hq => ?_⟩
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hk
  · exact hT₂ q hq

/-- **Every permit was earned.** Each live permit is an honest node's, recorded at an earlier admitted rung assembly
of the same rung and txid at that node, over the observation it carries, with no step since that ended the node's
permits or consumed them (`Lifecycle.Permitted`). -/
@[req "DUR-29"]
theorem permit_origin {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {p : Permit} (hp : p ∈ st.perm) :
    p.node ∈ honest ∧ Permitted cfg r T p := by
  induction hx with
  | init st h => rw [h.2.1] at hp; cases hp
  | @next T st s lab ha hl hx ih =>
    change p ∈ permAfter r st s at hp
    cases s with
    | base b =>
      change p ∈ st.perm.filter (fun p => keeps r p.node p.cid st (.base b)) at hp
      obtain ⟨hp, hk⟩ := List.mem_filter.1 hp
      obtain ⟨hi, hP⟩ := ih hp
      exact ⟨hi, hP.cons _ hk⟩
    | send j env cid m =>
      simp only [permAfter] at hp
      obtain ⟨hp, hk⟩ := List.mem_filter.1 hp
      obtain ⟨hi, hP⟩ := ih hp
      exact ⟨hi, hP.cons _ hk⟩
    | assemble j cid m =>
      simp only [permAfter] at hp
      cases hg : rungAt (st.cs.sw.fed.worlds j).node cid m with
      | none =>
        simp only [hg] at hp
        obtain ⟨hi, hP⟩ := ih hp
        exact ⟨hi, hP.cons _ rfl⟩
      | some g =>
        cases hb : st.cs.sw.obs j with
        | none =>
          simp only [hg, hb] at hp
          obtain ⟨hi, hP⟩ := ih hp
          exact ⟨hi, hP.cons _ rfl⟩
        | some b =>
          simp only [hg, hb] at hp
          rcases List.mem_cons.1 hp with rfl | hp
          · simp only [admits, ClassAssembly.admits, Bool.and_eq_true, List.contains_iff_mem,
              Bool.not_eq_true'] at ha
            obtain ⟨⟨hi, hok⟩, hu⟩ := ha
            exact ⟨hi, T, [], st, lab, rfl, hok, by simpa using hu, hb, ⟨g, hg, rfl⟩, by simp⟩
          · obtain ⟨hi, hP⟩ := ih hp
            exact ⟨hi, hP.cons _ rfl⟩

/-- **No permit outlives its pass.** After a fire pass, a ladder pass or a prune at node `i`, node `i` holds no
permit: a later send needs a later assembly. -/
@[req "DUR-31"]
theorem permit_lifetime (r : Rules) (st : State) {i : Nat} {env : Env} {e : Event} (he : ends e = true) :
    ∀ p ∈ (apply r st (.base (.fed (.process i env e)))).perm, p.node ≠ i := by
  intro p hp
  change p ∈ st.perm.filter (fun p => keeps r p.node p.cid st (.base (.fed (.process i env e)))) at hp
  obtain ⟨-, hk⟩ := List.mem_filter.1 hp
  simp only [keeps, endsAt, he, ↓reduceIte, Bool.and_eq_true] at hk
  simpa using hk.1.1

/-- **No permit outlives its registration lifetime.** After a step that births a record under `cid` at node `i`, a
fresh registration of that commitment or a rebirth, node `i` holds no permit under `cid`: a send in the new lifetime
needs an assembly in it. -/
@[req "DUR-31"]
theorem permit_birth (r : Rules) (st : State) {b : Sweep.Step} {i cid : Nat} (hb : births r st.cs.sw b i cid = true) :
    ∀ p ∈ (apply r st (.base b)).perm, ¬(p.node = i ∧ p.cid = cid) := by
  intro p hp ⟨h1, h2⟩
  change p ∈ st.perm.filter (fun p => keeps r p.node p.cid st (.base b)) at hp
  obtain ⟨-, hk⟩ := List.mem_filter.1 hp
  subst h1 h2
  simp [keeps, hb] at hk

/-- **No permit outlives a settlement of its ladder.** After node `i` settles a transaction of the ladder of its
Escape-role resident under `cid`, a rung of it seen in the mempool or confirmed, node `i` holds no permit under
`cid`: a permit read before that sighting authorizes no send after the node has acted on it. -/
@[req "DUR-31"]
theorem permit_settle (r : Rules) (st : State) {i cid : Nat} {env : Env} {tx : Tx} {c : Cand} {g : Rung}
    (hc : escapeAt (st.cs.sw.fed.worlds i).node cid = some c) (hg : g ∈ c.ladder) (htx : g.tx.id = tx.id) :
    ∀ p ∈ (apply r st (.base (.fed (.process i env (.settle tx))))).perm, ¬(p.node = i ∧ p.cid = cid) := by
  have hs : settlesAt st.cs.sw (.fed (.process i env (.settle tx))) i cid = true := by
    simp only [settlesAt, beq_self_eq_true, Bool.true_and, hc, List.any_eq_true, beq_iff_eq]
    exact ⟨g, hg, htx⟩
  intro p hp ⟨h1, h2⟩
  change p ∈ st.perm.filter (fun p => keeps r p.node p.cid st (.base (.fed (.process i env (.settle tx))))) at hp
  obtain ⟨-, hk⟩ := List.mem_filter.1 hp
  subst h1 h2
  simp [keeps, hs] at hk

/-- An acceptance under `Registration.preserve` of a pair whose spend is resident leaves the number of records under
every id as it was, refused or not: it births nothing, and keeps every permit it does not end otherwise. -/
@[req "SPN-32"]
theorem accept_repeat_count (r : Rules) (hr : r.registration = .preserve) (env : Env) (n : Node) (cid : Nat)
    (d : Bool) (E : Clocks.Wall) (sp es : Cand) (hres : n.cands.any (·.id == sp.id) = true) (x : Nat) :
    (accept r env n cid d E sp es).cands.countP (·.id == x) = n.cands.countP (·.id == x) := by
  have hreg : register r n env sp es = n.cands := by simp [register, hr, hres]
  unfold accept
  split
  · rw [refuse_cands]
  · split
    · rfl
    · simp only [hreg]
      split
      · simp [writeWindows, List.countP_map, Function.comp_def, withWindow_id]
      · rfl

/-- **A send consumes its permit.** After node `i`'s send under `cid`, node `i` holds no permit under that id: a
resend of the same rung needs a new assembly. -/
@[req "DUR-31"]
theorem permit_consumed (r : Rules) (st : State) (i : Nat) (env : Env) (cid m : Nat) :
    ∀ p ∈ (apply r st (.send i env cid m)).perm, ¬(p.node = i ∧ p.cid = cid) := by
  intro p hp
  change p ∈ permAfter r st (.send i env cid m) at hp
  simp only [permAfter] at hp
  obtain ⟨-, hk⟩ := List.mem_filter.1 hp
  rintro ⟨h1, h2⟩
  simp [h1, h2] at hk

/-! ## The submission history -/

/-- What a sweep step submits is a kernel send's `Recovery.sentBy` entry, with that send's node. -/
theorem mem_sentAt {r : Rules} {sw : Sweep.State} {b : Sweep.Step} {q : Nat × Bool × Tx}
    (hq : q ∈ sentAt r sw b) :
    ∃ j env cid p, b = .fed (.process j env (.send cid)) ∧ p ∈ Recovery.sentBy r sw b ∧ q = (j, p) := by
  cases b with
  | fed s =>
    cases s with
    | process j env e =>
      cases e with
      | send cid =>
        simp only [sentAt, List.mem_map] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        exact ⟨j, env, cid, p, rfl, hp, rfl⟩
      | _ => simp [sentAt] at hq
    | _ => simp [sentAt] at hq
  | _ => simp [sentAt] at hq

/-- A kernel send's `Recovery.sentBy` entry: the resident `Kernel.send` selects, its package test standing and its
re-authorization passing, and the step submits its transaction. -/
theorem sentBy_send {r : Rules} {sw : Sweep.State} {i : Nat} {env : Env} {cid : Nat} {p : Bool × Tx}
    (hp : p ∈ Recovery.sentBy r sw (.fed (.process i env (.send cid)))) :
    ∃ c, (sw.fed.worlds i).node.cands.find? (·.id == cid) = some c ∧ p = (c.isEscape, c.tx) ∧
      c.packageOk = true ∧ (r.reauth == .beforeAssembly || (due r env (sw.fed.worlds i).node c &&
        releaseAuthorized r (sw.fed.worlds i).node c)) = true ∧
      Sweep.submits r sw (.fed (.process i env (.send cid))) = [c.tx.id] := by
  cases hc : (sw.fed.worlds i).node.cands.find? (·.id == cid) with
  | none => simp [Recovery.sentBy, hc] at hp
  | some c =>
    cases hs : Sweep.submits r sw (.fed (.process i env (.send cid))) with
    | nil => simp [Recovery.sentBy, hc, hs] at hp
    | cons x xs =>
      simp only [Recovery.sentBy, hc, hs, List.mem_singleton] at hp
      have hs' := hs
      simp only [Sweep.submits, step, send, hc] at hs'
      split at hs'
      · rename_i hgo
        simp only [List.filterMap_cons, List.filterMap_nil, List.cons.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        simp only [Bool.and_eq_true] at hgo
        exact ⟨c, rfl, hp, hgo.1, hgo.2, rfl⟩
      · simp at hs'

/-- At an admitted sweep step, what it submits is not an Escape: a kernel send of an Escape is refused. -/
theorem sentAt_not_escape {cfg : Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {b : Sweep.Step}
    (ha : admits cfg r honest st T (.base b) = true) {q : Nat × Bool × Tx} (hq : q ∈ sentAt r st.cs.sw b) :
    q.2.1 = false := by
  obtain ⟨-, -, hk⟩ := admits_base ha
  obtain ⟨j, env, cid, p, rfl, hp, rfl⟩ := mem_sentAt hq
  obtain ⟨c, hc, rfl, -⟩ := sentBy_send hp
  have hcm := List.mem_of_find?_eq_some hc
  have hid : c.id = cid := by simpa using List.find?_some hc
  simp only [kernelSendOk, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
    not_and] at hk
  cases he : c.isEscape
  · rfl
  · exact absurd he (hk c hcm hid)

theorem honest_of_kernel {cfg : Cfg} {r : Rules} {honest : List Nat} {st : RungAssembly.State}
    {T : ClassAssembly.LTrace} {i : Nat} {env : Env} {e : Event}
    (ha : ClassAssembly.admits cfg r honest st T (.base (.fed (.process i env e))) = true) : i ∈ honest := by
  simp only [ClassAssembly.admits, LadderRelease.admits, Sweep.admits, Federation.admits, Bool.and_eq_true,
    List.contains_iff_mem] at ha
  exact ha.1.1.1.1

/-- **Every Escape submission is a rung's admitted send** (`DUR-29`, `DUR-31`). Each Escape entry of the submission
history, node `i` and transaction `tx`, was added at a rung's send by honest node `i`, at a step where `tx` is rung `m`
of its Escape-role resident under the id, which the send's own state and instant re-authorize; the send used a live
permit `p` of node `i` for that rung and txid whose observation passed `DUR-31`'s classification, and `p` was recorded
at an earlier admitted assembly of that rung and txid by node `i`, with no step between that ended node `i`'s permits
(its fire pass, ladder pass or prune), birthed a record under the id at node `i`, was node `i`'s settlement of a rung
of that Escape, or consumed them (its send under the id) (`Lifecycle.Permitted`).
No kernel send adds one. -/
@[req "DUR-29"]
theorem submitted_origin {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} {tx : Tx} (h : (i, true, tx) ∈ st.subs) :
    i ∈ honest ∧ ∃ T₁ T₂ st₀ env cid m lab, T = T₂ ++ (st₀, .send i env cid m, lab) :: T₁ ∧
      ∃ c g p, escapeAt (st₀.cs.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some g ∧ g.tx = tx ∧
        due r env (st₀.cs.sw.fed.worlds i).node c = true ∧
        releaseAuthorized r (st₀.cs.sw.fed.worlds i).node c = true ∧
        p ∈ st₀.perm ∧ p.node = i ∧ p.cid = cid ∧ p.rung = m ∧ p.txid = g.tx.id ∧ quiet p.obs c m = true ∧
        Permitted cfg r T₁ p := by
  induction hx with
  | init st h0 => rw [h0.2.2.2] at h; cases h
  | @next T st s lab ha hl hx ih =>
    have lift (h : (i, true, tx) ∈ st.subs) : i ∈ honest ∧ ∃ T₁ T₂ st₀ env cid m lab',
        (st, s, lab) :: T = T₂ ++ (st₀, .send i env cid m, lab') :: T₁ ∧
        ∃ c g p, escapeAt (st₀.cs.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some g ∧ g.tx = tx ∧
          due r env (st₀.cs.sw.fed.worlds i).node c = true ∧
          releaseAuthorized r (st₀.cs.sw.fed.worlds i).node c = true ∧
          p ∈ st₀.perm ∧ p.node = i ∧ p.cid = cid ∧ p.rung = m ∧ p.txid = g.tx.id ∧ quiet p.obs c m = true ∧
          Permitted cfg r T₁ p := by
      obtain ⟨hi, T₁, T₂, st₀, env, cid, m, lab', rfl, rest⟩ := ih h
      exact ⟨hi, T₁, (st, s, lab) :: T₂, st₀, env, cid, m, lab', rfl, rest⟩
    change (i, true, tx) ∈ subsAfter r st s at h
    cases s with
    | assemble j cid m => exact lift h
    | base b =>
      simp only [subsAfter, List.mem_append] at h
      rcases h with h | h
      · have := sentAt_not_escape ha h
        cases this
      · exact lift h
    | send j env cid m =>
      simp only [subsAfter] at h
      cases hg : rungAt (st.cs.sw.fed.worlds j).node cid m with
      | none => simp only [hg] at h; exact lift h
      | some g =>
        simp only [hg] at h
        rcases List.mem_cons.1 h with he | h
        · simp only [Prod.mk.injEq, true_and] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [admits, ClassAssembly.admits, Bool.and_eq_true, List.contains_iff_mem] at ha
          obtain ⟨⟨hi, hok⟩, hperm⟩ := ha
          obtain ⟨c, g', hc, hg', -, hdue, hauth⟩ := RungAssembly.sendOk_iff.1 hok
          rw [RungAssembly.rungAt_of hc, hg'] at hg
          simp only [Option.some.injEq] at hg
          subst hg
          simp only [sendOk, hc, hg', permitOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hperm
          obtain ⟨p, hp, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩ := hperm
          exact ⟨hi, T, [], st, env, cid, m, lab, rfl, c, g', p, hc, hg', rfl, hdue, hauth, hp, h1, h2, h3, h4, h5,
            (permit_origin hx hp).2⟩
        · exact lift h

/-- **Every other submission is a kernel send's** (`DUR-29`). Each entry of the submission history that is not an
Escape was added at a kernel send by honest node `i`, of the resident `Kernel.send` selects under the id, which is not
Escape-role, whose package test stands and which the send's own state re-authorizes; the step submits its
transaction, and its package test was earned at an earlier admitted assembly passing `ClassAssembly.candOk` for that
resident (`ClassAssembly.Assembled`). -/
@[req "DUR-29"]
theorem base_origin {cfg : Cfg} {r : Rules} (hr : r.reauth = .beforeSend) {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution cfg r honest T st) {i : Nat} {tx : Tx} (h : (i, false, tx) ∈ st.subs) :
    i ∈ honest ∧ ∃ T₁ T₂ st₀ env cid lab, T = T₂ ++ (st₀, .base (.fed (.process i env (.send cid))), lab) :: T₁ ∧
      ∃ c ∈ (st₀.cs.sw.fed.worlds i).node.cands, c.id = cid ∧ c.tx = tx ∧ c.isEscape = false ∧
        c.packageOk = true ∧ due r env (st₀.cs.sw.fed.worlds i).node c = true ∧
        releaseAuthorized r (st₀.cs.sw.fed.worlds i).node c = true ∧
        Sweep.submits r st₀.cs.sw (.fed (.process i env (.send cid))) = [tx.id] ∧
        ClassAssembly.Assembled cfg r (toL T₁) i c := by
  induction hx with
  | init st h0 => rw [h0.2.2.2] at h; cases h
  | @next T st s lab ha hl hx ih =>
    have lift (h : (i, false, tx) ∈ st.subs) : i ∈ honest ∧ ∃ T₁ T₂ st₀ env cid lab',
        (st, s, lab) :: T = T₂ ++ (st₀, .base (.fed (.process i env (.send cid))), lab') :: T₁ ∧
        ∃ c ∈ (st₀.cs.sw.fed.worlds i).node.cands, c.id = cid ∧ c.tx = tx ∧ c.isEscape = false ∧
          c.packageOk = true ∧ due r env (st₀.cs.sw.fed.worlds i).node c = true ∧
          releaseAuthorized r (st₀.cs.sw.fed.worlds i).node c = true ∧
          Sweep.submits r st₀.cs.sw (.fed (.process i env (.send cid))) = [tx.id] ∧
          ClassAssembly.Assembled cfg r (toL T₁) i c := by
      obtain ⟨hi, T₁, T₂, st₀, env, cid, lab', rfl, rest⟩ := ih h
      exact ⟨hi, T₁, (st, s, lab) :: T₂, st₀, env, cid, lab', rfl, rest⟩
    change (i, false, tx) ∈ subsAfter r st s at h
    cases s with
    | assemble j cid m => exact lift h
    | send j env cid m =>
      simp only [subsAfter] at h
      cases hg : rungAt (st.cs.sw.fed.worlds j).node cid m with
      | none => simp only [hg] at h; exact lift h
      | some g =>
        simp only [hg] at h
        rcases List.mem_cons.1 h with he | h
        · simp at he
        · exact lift h
    | base b =>
      simp only [subsAfter, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨j, env, cid, p, rfl, hp, hq⟩ := mem_sentAt h
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨c, hc, hpc, hpk, hgo, hsub⟩ := sentBy_send hp
        simp only [Prod.mk.injEq] at hpc
        obtain ⟨he, rfl⟩ := hpc
        have hi : i ∈ honest := honest_of_kernel (admits_base ha).1
        have hcm := List.mem_of_find?_eq_some hc
        have hid : c.id = cid := by simpa using List.find?_some hc
        have hb : (Reauth.beforeSend == Reauth.beforeAssembly) = false := rfl
        simp only [hr, hb, Bool.false_or, Bool.and_eq_true] at hgo
        exact ⟨hi, T, [], st, env, cid, lab, rfl, c, hcm, hid, rfl, he.symm, hpk, hgo.1, hgo.2, hsub,
          ClassAssembly.assembled_of_packageOk (to_classed hx) hi c hcm hpk⟩
      · exact lift h

/-! ## What a step keeps -/

/-- One step keeps the federation's partial inventory, its extracted keys, every node's exposure rows and the
submission history. -/
theorem step_kept (r : Rules) (st : State) (s : Step) :
    (∀ x ∈ st.cs.sw.fed.parts, x ∈ (apply r st s).cs.sw.fed.parts) ∧
      (∀ j ∈ st.cs.sw.fed.extracted, j ∈ (apply r st s).cs.sw.fed.extracted) ∧
      (∀ i, ∀ x ∈ (st.cs.sw.fed.worlds i).exposure, x ∈ ((apply r st s).cs.sw.fed.worlds i).exposure) ∧
      ∀ x ∈ st.subs, x ∈ (apply r st s).subs := by
  cases s with
  | base b =>
    obtain ⟨h1, h2, h3⟩ := Settlement.step_keeps_exposure r st.cs.sw b
    exact ⟨h1, h2, h3, fun x hx => List.mem_append_right _ hx⟩
  | assemble i cid m =>
    have e : (apply r st (.assemble i cid m)).cs.sw = st.cs.sw :=
      RungAssembly.apply_sw (s := .assemble i cid m) r st.cs (by simp)
    rw [e]
    exact ⟨fun _ h => h, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  | send i env cid m =>
    have e : (apply r st (.send i env cid m)).cs.sw = st.cs.sw :=
      RungAssembly.apply_sw (s := .send i env cid m) r st.cs (by simp)
    rw [e]
    refine ⟨fun _ h => h, fun _ h => h, fun _ _ h => h, fun x hx => ?_⟩
    change x ∈ subsAfter r st (.send i env cid m)
    simp only [subsAfter]
    split
    · exact List.mem_cons_of_mem _ hx
    · exact hx

/-- **A submission stays submitted, and exposure stays exposed** (`POL-18`, `SEC-54`). What any earlier state of an
execution held in the federation's partial inventory, its extracted set, any node's exposure rows or the submission
history, the final state holds: across every chain move, a reorg or an eviction included, every prune and every
candidate's removal. -/
@[req "POL-18"]
theorem history_kept {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {st₀ : State} {s : Step} {lab : Option Nat} (hm : (st₀, s, lab) ∈ T) :
    (∀ x ∈ st₀.cs.sw.fed.parts, x ∈ st.cs.sw.fed.parts) ∧
      (∀ j ∈ st₀.cs.sw.fed.extracted, j ∈ st.cs.sw.fed.extracted) ∧
      (∀ i, ∀ x ∈ (st₀.cs.sw.fed.worlds i).exposure, x ∈ (st.cs.sw.fed.worlds i).exposure) ∧
      ∀ x ∈ st₀.subs, x ∈ st.subs := by
  induction hx with
  | init st h => cases hm
  | @next T st' s' h' _ _ _ ih =>
    rcases List.mem_cons.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact step_kept r _ _
    · obtain ⟨h1, h2, h3, h4⟩ := ih hm
      obtain ⟨k1, k2, k3, k4⟩ := step_kept r st' s'
      exact ⟨fun x hx => k1 x (h1 x hx), fun j hj => k2 j (h2 j hj), fun i x hx => k3 i x (h3 i x hx),
        fun x hx => k4 x (h4 x hx)⟩

/-- **A send moves no chain** (`DUR-31`). A rung's send leaves the composed sweep state as it was, the truth, every
earlier instant, every observation and the federation included, and the assembled set and consumed reads too; it adds
at most its own entry to the submission history. Repeated sends add entries and nothing else. -/
@[req "DUR-31"]
theorem send_moves_no_chain (r : Rules) (st : State) (i : Nat) (env : Env) (cid m : Nat) :
    (apply r st (.send i env cid m)).cs.sw = st.cs.sw ∧
      (apply r st (.send i env cid m)).cs.assembled = st.cs.assembled ∧
      (apply r st (.send i env cid m)).used = st.used ∧
      ((apply r st (.send i env cid m)).subs = st.subs ∨ ∃ g, rungAt (st.cs.sw.fed.worlds i).node cid m = some g ∧
        (apply r st (.send i env cid m)).subs = (i, true, g.tx) :: st.subs) := by
  refine ⟨RungAssembly.apply_sw (s := .send i env cid m) r st.cs (by simp), ?_, rfl, ?_⟩
  · simp only [apply, RungAssembly.apply]
    split <;> rfl
  · simp only [apply, subsAfter]
    cases hg : rungAt (st.cs.sw.fed.worlds i).node cid m with
    | none => exact .inl rfl
    | some g => exact .inr ⟨g, rfl, rfl⟩

/-- **A chain move rewrites no history.** It moves the truth and records the instant it leaves, and keeps the
submission history, the permits, every observation and the federation. -/
@[req "SPN-33"]
theorem chain_step (r : Rules) (st : State) (b : Backend) :
    (apply r st (.base (.chain b))).subs = st.subs ∧ (apply r st (.base (.chain b))).perm = st.perm ∧
      (apply r st (.base (.chain b))).cs.sw.truth = b ∧
      (apply r st (.base (.chain b))).cs.sw.past = st.cs.sw.truth :: st.cs.sw.past ∧
      (apply r st (.base (.chain b))).cs.sw.obs = st.cs.sw.obs ∧
      (apply r st (.base (.chain b))).cs.sw.fed = st.cs.sw.fed :=
  ⟨rfl, List.filter_eq_self.2 fun _ _ => by simp [keeps, endsAt, births, countAt, Sweep.apply, settlesAt], rfl, rfl,
    rfl, rfl⟩

/-! ## The observation tie -/

/-- `Recovery.awaiting`'s reading of a submission history at an instant: some entry spends the coin, is not
confirmed there and is not conflicted there. Each entry carries the transaction's id and ordered inputs, which are
what `Settlement.resident` and `Settlement.confirmedAt` compare. -/
@[req "SEC-54"]
def awaitingAt (b : Backend) (subs : List (Nat × Bool × Tx)) (coin : Nat) : Bool :=
  subs.any fun p => p.2.2.inputs.contains coin && !Settlement.confirmedAt b p.2.2 && !Recovery.conflicted b p.2.2

/-- **The history is `Recovery`'s record.** With no Recovery spend published and the submission history's
transactions as `Recovery.St.sent`, `Recovery.awaiting` is the history's reading at the truth, so a chain move
changes it while the history stays (`Lifecycle.chain_step`). -/
@[req "SEC-54"]
theorem awaiting_tie (st : Recovery.St) (subs : List (Nat × Bool × Tx)) (hp : st.published = [])
    (hs : st.sent = subs.map (·.2)) (coin : Nat) :
    Recovery.awaiting st coin = awaitingAt st.sw.truth subs coin := by
  simp [Recovery.awaiting, awaitingAt, hp, hs, List.any_map, Function.comp_def]

/-! ## Running a schedule -/

def record (r : Rules) : Trace → State → List Step → Trace × State
  | T, st, [] => (T, st)
  | T, st, s :: ss => record r ((st, s, ClassAssembly.labelFor r (toL T) s) :: T) (apply r st s) ss

def legal (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → List Step → Bool
  | _, _, [] => true
  | T, st, s :: ss => admits cfg r honest st T s && ClassAssembly.labelOk r st.cs (toL T) s
      (ClassAssembly.labelFor r (toL T) s) &&
      legal cfg r honest ((st, s, ClassAssembly.labelFor r (toL T) s) :: T) (apply r st s) ss

theorem execution_of_legal {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {ss : List Step} (hl : legal cfg r honest T st ss = true) :
    Execution cfg r honest (record r T st ss).1 (record r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s _ hl.1.1 hl.1.2 hx) hl.2

end BtcPolicy.Lifecycle
