import BtcPolicy.LadderRelease
import BtcPolicy.RungIngress
import BtcPolicy.Assembly
/-! `DUR-28`'s finalization and `DUR-29`'s assembly and send of a rung above the base, on the composed sweep run. The
kernel's assembly (`Kernel.packageAccepted`) and send (`Kernel.send`) read the base alone: the send broadcasts the
candidate's own transaction, and `Assembly.checkOf` counts `Federation.held`, which stores no rung partial. This module
is a refinement layer over `LadderRelease`'s run, as `BtcPolicy.Sweep` and `BtcPolicy.Recovery` are layers over the
federation and the sweep: no new kernel event and no new model beside the existing modules. Its state is the composed
sweep state with the rungs each node assembled and sent (`RungAssembly.State`); its steps are a step of the sweep, a
rung's assembly and a rung's send (`RungAssembly.Step`); the sweep steps are admitted exactly as `LadderRelease.admits`
admits them, and the two rung steps change nothing of the sweep state (`RungAssembly.apply_sw`).

**The assembly.** `RungAssembly.assembleOk`: at an honest node with an observation, for its first Escape-role resident
under the commitment id (`RungAssembly.escapeAt`), the rung index is `DUR-28`'s finalization, "the highest rung at or
below the latch with `≥ t` distinct valid partials on every input" (`Ladder.finalize`), over the node's possession on
the ladder (`RungIngress.held`), and that rung passes `Assembly.rungCheck` at the node's own read
(`RungRelease.readAt`) and observation: its quorum, its coverage, the floor at its exact finalized vsize, its ancestry
as a replacement of a resident lower rung, and the backend's package verdict. `RungAssembly.assemble_sound` unfolds
what an admitted assembly established; the count reads only the rung's own transaction's records
(`Ladder.quorum_own_rung`), so authority on one rung never counts for another.

**The send.** `RungAssembly.sendOk`: the rung at that index of the same resident was assembled by this node, as a
txid, and the send's own state and instant re-authorize the Escape: `DUR-29`'s "this Escape still in
`selected_escapes` with `sweep_active` AND its own duress bit set, not frozen, window open — immediately before the
send", which is `Kernel.due` and `Kernel.releaseAuthorized`, as `Kernel.send` reads them under
`Kernel.Reauth.beforeSend`. `RungAssembly.sent_in_order`: every rung a node sent was sent at a step whose own state
re-authorized it, after an earlier admitted assembly of the same txid by the same node
(`RungAssembly.AssembledRung`); `RungAssembly.assembled_possession`: the records that assembly counted are the node's
own signatures or partials of the inventory.

**The relation to `LadderRelease`.** Forgetting the rung steps leaves a `LadderRelease.Execution`
(`RungAssembly.to_ladder`), so every result about it, `RungIngress`, `Sweep`, `Federation` and the kernel applies; and
every `LadderRelease.Execution` is a run of this layer that takes no rung step (`RungAssembly.of_ladder`). Nothing but a
rung's assembly and send is constrained.

**Not modelled here.** The kernel's own bits do not see a rung step: a rung's assembly sets no
`Kernel.Cand.packageOk`, and a rung's send sets no `Kernel.Cand.broadcast` and adds no `Kernel.Effect.broadcast`, so
`Kernel.due`'s "not broadcast" does not stop a later rung or base send of the same Escape, and `Sweep.submits` and
`Recovery.St.sent` do not list it. The send reads no backend, as `Kernel.send` does not. A rung's assembly does not
consume the node's observation, as the sweep's does. The Escape the steps act on is the first Escape-role resident
under the id; the kernel's send takes the first resident under it. -/

namespace BtcPolicy.RungAssembly
open BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)

/-! ## The layer -/

/-- The ladder's parameters, and the class check's supplied witnesses and backend verdict (`Assembly.Cfg`). -/
structure Cfg where
  lc : Ladder.Cfg
  witnesses : Nat → List Nat
  test : Backend → List Nat → List Assembly.Entry

/-- The class check's configuration at the ladder's pre-release parameters. -/
def Cfg.asm (cfg : Cfg) : Assembly.Cfg := { pre := cfg.lc.pre, witnesses := cfg.witnesses, test := cfg.test }

/-- The composed sweep state, with the rungs each node assembled and sent, each as (node, commitment id, rung txid). -/
structure State where
  sw : Sweep.State
  assembled : List (Nat × Nat × Nat) := []
  sent : List (Nat × Nat × Nat) := []

inductive Step
  /-- A step of the composed sweep, as `LadderRelease.admits` admits it. -/
  | base (s : Sweep.Step)
  /-- Node `i` assembles rung `m` of its Escape under commitment `cid`. -/
  | assemble (i cid m : Nat)
  /-- Node `i` sends rung `m` of its Escape under commitment `cid`, at instant `env`. -/
  | send (i : Nat) (env : Env) (cid m : Nat)

/-- A history, newest first, each step with the state it was taken in. -/
abbrev Trace := List (State × Step)

/-- The composed sweep's own steps in a history. -/
def sweepTrace : Trace → Sweep.Trace
  | [] => []
  | (st, .base s) :: T => (st.sw, s) :: sweepTrace T
  | _ :: T => sweepTrace T

/-- The Escape a rung step at a node acts on: its first Escape-role resident under the commitment id. -/
def escapeAt (n : Node) (cid : Nat) : Option Cand := n.cands.find? fun c => c.id == cid && c.isEscape

theorem escapeAt_some {n : Node} {cid : Nat} {c : Cand} (h : escapeAt n cid = some c) :
    c ∈ n.cands ∧ c.id = cid ∧ c.isEscape = true := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp.1, hp.2⟩

/-- Rung `m` of that Escape's ladder, the base at 0. -/
def rungAt (n : Node) (cid m : Nat) : Option Rung := (escapeAt n cid).bind fun c => c.ladder[m]?

/-- Node `i`'s possession over the ladder in state `st` after history `T`. -/
def heldAt (st : Sweep.State) (T : Sweep.Trace) (i : Nat) : List Authority.Sig :=
  RungIngress.held i (Sweep.fedTrace T) st.fed

/-- `DUR-28`'s finalization at node `i` for candidate `c`: the highest rung at or below its latch with the quorum on
every input in the node's possession. -/
@[req "DUR-28"]
def finalAt (cfg : Cfg) (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (c : Cand) : Option Nat :=
  Ladder.finalize cfg.lc.pre.sweep.keys (st.fed.worlds i).node.t c.ladder (heldAt st T i) c.track.latch

/-- A rung's assembly at node `i`: an observation, the rung is the finalization's, and it passes `Assembly.rungCheck`
at the node's own read and observation over its possession. -/
@[req "DUR-29"]
def assembleOk (cfg : Cfg) (st : Sweep.State) (T : Sweep.Trace) (i cid m : Nat) : Bool :=
  match escapeAt (st.fed.worlds i).node cid, st.obs i with
  | some c, some b => finalAt cfg st T i c == some m &&
      Assembly.rungCheck cfg.asm (RungRelease.readAt st T i c) b c (heldAt st T i) m
  | _, _ => false

/-- A rung's send at node `i`, instant `env`: this node assembled that rung's txid, and the send's own state
re-authorizes the Escape. -/
@[req "DUR-29"]
def sendOk (r : Rules) (env : Env) (st : State) (i cid m : Nat) : Bool :=
  match escapeAt (st.sw.fed.worlds i).node cid with
  | none => false
  | some c =>
    match c.ladder[m]? with
    | none => false
    | some g => st.assembled.contains (i, cid, g.tx.id) && due r env (st.sw.fed.worlds i).node c &&
        releaseAuthorized r (st.sw.fed.worlds i).node c

/-- Which steps may be taken: a sweep step `LadderRelease` admits, or a rung step at an honest node. -/
def admits (cfg : Cfg) (r : Rules) (honest : List Nat) (st : State) (T : Trace) : Step → Bool
  | .base s => LadderRelease.admits cfg.lc honest st.sw (sweepTrace T) s
  | .assemble i cid m => honest.contains i && assembleOk cfg st.sw (sweepTrace T) i cid m
  | .send i env cid m => honest.contains i && sendOk r env st i cid m

def apply (r : Rules) (st : State) : Step → State
  | .base s => { st with sw := Sweep.apply r st.sw s }
  | .assemble i cid m =>
    match rungAt (st.sw.fed.worlds i).node cid m with
    | some g => { st with assembled := (i, cid, g.tx.id) :: st.assembled }
    | none => st
  | .send i _ cid m =>
    match rungAt (st.sw.fed.worlds i).node cid m with
    | some g => { st with sent := (i, cid, g.tx.id) :: st.sent }
    | none => st

/-- A fresh start: the sweep's, nothing assembled or sent. -/
def Fresh (honest : List Nat) (st : State) : Prop :=
  Sweep.Fresh honest st.sw ∧ st.assembled = [] ∧ st.sent = []

/-- A reachable execution of the layer. -/
inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Step) (ha : admits cfg r honest st T s = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s) :: T) (apply r st s)

/-! ## The relation to `LadderRelease` -/

/-- A rung step changes nothing of the composed sweep state, the kernel's candidates included. -/
theorem apply_sw (r : Rules) (st : State) {s : Step} (h : ∀ b, s ≠ .base b) : (apply r st s).sw = st.sw := by
  cases s with
  | base b => exact absurd rfl (h b)
  | assemble i cid m => simp only [apply]; split <;> rfl
  | send i env cid m => simp only [apply]; split <;> rfl

/-- **The layer over `LadderRelease`.** Forgetting the rung steps leaves a `LadderRelease.Execution`. -/
@[req "DUR-29"]
theorem to_ladder {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) : LadderRelease.Execution cfg.lc r honest (sweepTrace T) st.sw := by
  induction hx with
  | init st h => exact .init _ h.1
  | next s ha _ ih =>
    cases s with
    | base s => exact .next s ha ih
    | assemble i cid m => rw [apply_sw r _ (by simp)]; exact ih
    | send i env cid m => rw [apply_sw r _ (by simp)]; exact ih

/-- A sweep history as a history of the layer with no rung step. -/
def liftTrace : Sweep.Trace → Trace
  | [] => []
  | (st, s) :: T => ({ sw := st }, .base s) :: liftTrace T

theorem sweepTrace_lift : ∀ T : Sweep.Trace, sweepTrace (liftTrace T) = T
  | [] => rfl
  | (_, _) :: T => by simp [liftTrace, sweepTrace, sweepTrace_lift T]

/-- **Nothing but a rung step is constrained.** Every `LadderRelease.Execution` is a run of the layer that takes no
rung step, with the same sweep trace and state. -/
@[req "DUR-29"]
theorem of_ladder {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : LadderRelease.Execution cfg.lc r honest T st) : Execution cfg r honest (liftTrace T) { sw := st } := by
  induction hx with
  | init st h => exact .init _ ⟨h, rfl, rfl⟩
  | @next T st s ha _ ih =>
    have ha' : admits cfg r honest { sw := st } (liftTrace T) (.base s) = true := by
      simp only [admits, sweepTrace_lift]; exact ha
    exact .next (.base s) ha' ih

/-- A step of an execution was admitted at its own state, after a reachable history. -/
theorem prefix_exec {cfg : Cfg} {r : Rules} {honest : List Nat} :
    ∀ {T : Trace} {st : State}, Execution cfg r honest T st →
      ∀ {T₂ T₁ : Trace} {st₀ : State} {s : Step}, T = T₂ ++ (st₀, s) :: T₁ →
        Execution cfg r honest T₁ st₀ ∧ admits cfg r honest st₀ T₁ s = true := by
  intro T st hx
  induction hx with
  | init st h => intro T₂ T₁ st₀ s hT; cases T₂ <;> cases hT
  | next s' ha hx ih =>
    intro T₂ T₁ st₀ s hT
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hT
      exact ⟨hx, ha⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      exact ih hT.2

theorem sweepTrace_append (T₂ T₁ : Trace) : sweepTrace (T₂ ++ T₁) = sweepTrace T₂ ++ sweepTrace T₁ := by
  induction T₂ with
  | nil => rfl
  | cons y T₂ ih =>
    obtain ⟨st, s⟩ := y
    cases s <;> simp [sweepTrace, ih]

/-! ## The assembly -/

/-- The ladder's transactions at the node's own read are the candidate's ladder. -/
theorem txs_readAt (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (c : Cand) :
    Ladder.txs (RungRelease.readAt st T i c) c = c.ladder.map (·.tx) := by
  simp [Ladder.txs, RungRelease.readAt, Ladder.Read.own, Cand.ladder]

/-- No rung above the finalization's, at or below the latch, has the quorum. -/
@[req "DUR-28"]
theorem finalize_above {keys : List Nat} {t : Nat} {l : List Rung} {R : List Authority.Sig} {top m : Nat}
    (h : Ladder.finalize keys t l R top = some m) {k : Nat} (hmk : m < k) (hk : k ≤ top) :
    Ladder.quorumAt keys t l R k = false := by
  cases hq : Ladder.quorumAt keys t l R k
  · rfl
  · obtain ⟨m', hm', hle⟩ := Ladder.finalize_highest keys t l R top k hk hq
    rw [h] at hm'
    simp only [Option.some.injEq] at hm'
    omega

/-- **What a rung's assembly established** (`DUR-28`, `DUR-29`). At an admitted assembly the node has an observation
and an Escape-role resident under the id, and the assembled rung `g` is at index `m` of its ladder, at or below its
latch; `g`'s own transaction has `t` distinct signers on every input among the records on that transaction alone in
the node's possession, so no other rung's records count; no rung above it at or below the latch has that quorum; and
at the node's own read, `g` is covered at the ladder's pass, meets the floor at its exact finalized vsize, has
`WTC-24`'s admitted ancestry as a replacement of the resident lower rung if any, and the backend accepts its package. -/
@[req "DUR-29"]
theorem assemble_sound {cfg : Cfg} {st : Sweep.State} {T : Sweep.Trace} {i cid m : Nat}
    (h : assembleOk cfg st T i cid m = true) :
    ∃ c b g, escapeAt (st.fed.worlds i).node cid = some c ∧ st.obs i = some b ∧ c.ladder[m]? = some g ∧
      m ≤ c.track.latch ∧
      Authority.quorum cfg.lc.pre.sweep.keys (st.fed.worlds i).node.t g.tx
        ((heldAt st T i).filter fun s => s.msg.1 == g.tx.id) = true ∧
      (∀ k, m < k → k ≤ c.track.latch →
        Ladder.quorumAt cfg.lc.pre.sweep.keys (st.fed.worlds i).node.t c.ladder (heldAt st T i) k = false) ∧
      Ladder.coveredTx cfg.lc.pre.sweep (Ladder.passAt cfg.lc.pre.sweep (RungRelease.readAt st T i c) b) g.tx = true ∧
      PreRelease.feeOk cfg.lc.pre (Assembly.exactVsize cfg.asm g.tx) g.tx = true ∧
      (∃ anc, Package.validate cfg.lc.pre.sweep.ancestry cfg.lc.pre.sweep.creator
        (Sweep.snapshot (RungRelease.readAt st T i c).A b) b.mempool (RungRelease.readAt st T i c).A
        (Sweep.candidateOf g.tx)
        (Ladder.replacesOf (c.ladder.map (·.tx)) (PreRelease.membership b (c.ladder.map (·.tx))) m) =
          .admitted anc) ∧
      Assembly.packageOk cfg.asm b g.tx = true := by
  unfold assembleOk at h
  cases hc : escapeAt (st.fed.worlds i).node cid with
  | none => simp [hc] at h
  | some c =>
    cases hb : st.obs i with
    | none => simp [hc, hb] at h
    | some b =>
      simp only [hc, hb, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hf, hr⟩ := h
      obtain ⟨hq, hle⟩ := Ladder.finalize_sound _ _ _ _ _ _ hf
      unfold Ladder.quorumAt at hq
      cases hg : c.ladder[m]? with
      | none => rw [hg] at hq; cases hq
      | some g =>
        rw [hg] at hq
        obtain ⟨tx, htx, -, hcov, hfee, hanc, hpk⟩ := Assembly.rungCheck_sound hr
        rw [txs_readAt, List.getElem?_map, hg] at htx
        simp only [Option.map_some, Option.some.injEq] at htx
        subst htx
        rw [txs_readAt] at hanc
        refine ⟨c, b, g, rfl, rfl, hg, hle, ?_, fun k hk hkl => finalize_above hf hk hkl, hcov, hfee, hanc, hpk⟩
        rw [← Ladder.quorum_own_rung]
        exact hq

/-- Node `i` assembled rung txid `x` under commitment `cid` earlier in `T`, `T₁` the history before that step: its
Escape-role resident under the id, its observation, rung `m` of that Escape's ladder with txid `x`, the
finalization's index, and `Assembly.rungCheck` passed there. -/
def AssembledRung (cfg : Cfg) (T : Trace) (i cid x : Nat) : Prop :=
  ∃ T₁ T₂ st m, T = T₂ ++ (st, .assemble i cid m) :: T₁ ∧ ∃ c b g,
    escapeAt (st.sw.fed.worlds i).node cid = some c ∧ st.sw.obs i = some b ∧ c.ladder[m]? = some g ∧ g.tx.id = x ∧
    finalAt cfg st.sw (sweepTrace T₁) i c = some m ∧
    Assembly.rungCheck cfg.asm (RungRelease.readAt st.sw (sweepTrace T₁) i c) b c (heldAt st.sw (sweepTrace T₁) i) m =
      true

theorem AssembledRung.cons {cfg : Cfg} {T : Trace} {i cid x : Nat} (y : State × Step)
    (h : AssembledRung cfg T i cid x) : AssembledRung cfg (y :: T) i cid x := by
  obtain ⟨T₁, T₂, st, m, rfl, rest⟩ := h
  exact ⟨T₁, y :: T₂, st, m, rfl, rest⟩

theorem rungAt_of {n : Node} {cid m : Nat} {c : Cand} (hc : escapeAt n cid = some c) :
    rungAt n cid m = c.ladder[m]? := by
  simp [rungAt, hc]

/-- **Every assembled rung was assembled.** Each (node, commitment id, txid) the layer records as assembled is an
honest node's, from an admitted assembly earlier in the history (`RungAssembly.AssembledRung`). -/
@[req "DUR-28"]
theorem assembled_origin {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {i cid x : Nat} (h : (i, cid, x) ∈ st.assembled) :
    i ∈ honest ∧ AssembledRung cfg T i cid x := by
  induction hx with
  | init st h0 => rw [h0.2.1] at h; cases h
  | @next T st s ha hx ih =>
    cases s with
    | base s =>
      obtain ⟨hi, ha'⟩ := ih h
      exact ⟨hi, ha'.cons _⟩
    | send j env cid' m =>
      simp only [apply] at h
      split at h <;> (obtain ⟨hi, ha'⟩ := ih h; exact ⟨hi, ha'.cons _⟩)
    | assemble j cid' m =>
      simp only [apply] at h
      split at h
      · rename_i g hg
        rcases List.mem_cons.1 h with he | h
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          simp only [admits, Bool.and_eq_true, List.contains_iff_mem] at ha
          obtain ⟨hi, hok⟩ := ha
          refine ⟨hi, T, [], st, m, rfl, ?_⟩
          unfold assembleOk at hok
          cases hc : escapeAt (st.sw.fed.worlds i).node cid with
          | none => simp [hc] at hok
          | some c =>
            cases hb : st.sw.obs i with
            | none => simp [hc, hb] at hok
            | some b =>
              simp only [hc, hb, Bool.and_eq_true, beq_iff_eq] at hok
              rw [rungAt_of hc] at hg
              exact ⟨c, b, g, rfl, rfl, hg, rfl, hok.1, hok.2⟩
        · obtain ⟨hi, ha'⟩ := ih h
          exact ⟨hi, ha'.cons _⟩
      · obtain ⟨hi, ha'⟩ := ih h
        exact ⟨hi, ha'.cons _⟩

/-- **The records an assembly counted are actual possession.** At every assembly of an execution, every record in the
assembling node's possession is its own signature or a partial of the inventory at that state, with the same message,
input and signer (`RungIngress.held_origin`). -/
@[req "DUR-28"]
theorem assembled_possession {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {T₁ T₂ : Trace} {st₀ : State} {i cid m : Nat}
    (hT : T = T₂ ++ (st₀, .assemble i cid m) :: T₁) {y : Authority.Sig}
    (hy : y ∈ heldAt st₀.sw (sweepTrace T₁) i) :
    y.signer = i ∨ ∃ z ∈ st₀.sw.fed.parts, Authority.sig z = y := by
  obtain ⟨hx₁, ha⟩ := prefix_exec hx hT
  have hi : i ∈ honest := by
    simp only [admits, Bool.and_eq_true, List.contains_iff_mem] at ha
    exact ha.1
  have hfx := Sweep.fed_execution (LadderRelease.to_sweep (to_ladder hx₁))
  exact RungIngress.held_origin hfx hi hy

/-! ## The send -/

/-- **`DUR-29`'s order on a rung's send.** Every rung a node sent, recorded by txid, was sent by an honest node at a
step taken in a state where that txid is rung `m` of its Escape-role resident under the id, and which the send's own
state and instant re-authorize, due and released by `DUR-10`'s gate, read at that step and not at the assembly; and
before that step the same node assembled the same txid under the same id (`RungAssembly.AssembledRung`). -/
@[req "DUR-29"]
theorem sent_in_order {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {i cid x : Nat} (h : (i, cid, x) ∈ st.sent) :
    i ∈ honest ∧ ∃ T₁ T₂ st₀ env m, T = T₂ ++ (st₀, .send i env cid m) :: T₁ ∧ ∃ c g,
      escapeAt (st₀.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some g ∧ g.tx.id = x ∧
      due r env (st₀.sw.fed.worlds i).node c = true ∧
      releaseAuthorized r (st₀.sw.fed.worlds i).node c = true ∧ AssembledRung cfg T₁ i cid x := by
  induction hx with
  | init st h0 => rw [h0.2.2] at h; cases h
  | @next T st s ha hx ih =>
    have lift (h : (i, cid, x) ∈ st.sent) : i ∈ honest ∧ ∃ T₁ T₂ st₀ env m,
        (st, s) :: T = T₂ ++ (st₀, .send i env cid m) :: T₁ ∧ ∃ c g,
          escapeAt (st₀.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some g ∧ g.tx.id = x ∧
          due r env (st₀.sw.fed.worlds i).node c = true ∧
          releaseAuthorized r (st₀.sw.fed.worlds i).node c = true ∧ AssembledRung cfg T₁ i cid x := by
      obtain ⟨hi, T₁, T₂, st₀, env, m, rfl, rest⟩ := ih h
      exact ⟨hi, T₁, (st, s) :: T₂, st₀, env, m, rfl, rest⟩
    cases s with
    | base s => exact lift h
    | assemble j cid' m => simp only [apply] at h; split at h <;> exact lift h
    | send j env cid' m =>
      simp only [apply] at h
      split at h
      · rename_i g hg
        rcases List.mem_cons.1 h with he | h
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          simp only [admits, Bool.and_eq_true, List.contains_iff_mem] at ha
          obtain ⟨hi, hok⟩ := ha
          refine ⟨hi, T, [], st, env, m, rfl, ?_⟩
          unfold sendOk at hok
          cases hc : escapeAt (st.sw.fed.worlds i).node cid with
          | none => simp [hc] at hok
          | some c =>
            rw [rungAt_of hc] at hg
            simp only [hc, hg, Bool.and_eq_true, List.contains_iff_mem] at hok
            obtain ⟨⟨hmem, hdue⟩, hauth⟩ := hok
            exact ⟨c, g, rfl, hg, rfl, hdue, hauth, (assembled_origin hx hmem).2⟩
        · exact lift h
      · exact lift h

/-- A rung's send, unfolded at its own state: the rung's txid was assembled by this node, and the Escape is due and
authorized at the send's state and instant. -/
@[req "DUR-29"]
theorem sendOk_iff {r : Rules} {env : Env} {st : State} {i cid m : Nat} :
    sendOk r env st i cid m = true ↔ ∃ c g, escapeAt (st.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some g ∧
      (i, cid, g.tx.id) ∈ st.assembled ∧ due r env (st.sw.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.sw.fed.worlds i).node c = true := by
  unfold sendOk
  constructor
  · intro h
    cases hc : escapeAt (st.sw.fed.worlds i).node cid with
    | none => simp [hc] at h
    | some c =>
      cases hg : c.ladder[m]? with
      | none => simp [hc, hg] at h
      | some g =>
        simp only [hc, hg, Bool.and_eq_true, List.contains_iff_mem] at h
        exact ⟨c, g, rfl, hg, h.1.1, h.1.2, h.2⟩
  · rintro ⟨c, g, hc, hg, hm, hd, ha⟩
    simp [hc, hg, hm, hd, ha]

/-! ## Running a schedule -/

def record (r : Rules) : Trace → State → List Step → Trace × State
  | T, st, [] => (T, st)
  | T, st, s :: ss => record r ((st, s) :: T) (apply r st s) ss

def legal (cfg : Cfg) (r : Rules) (honest : List Nat) : Trace → State → List Step → Bool
  | _, _, [] => true
  | T, st, s :: ss => admits cfg r honest st T s && legal cfg r honest ((st, s) :: T) (apply r st s) ss

theorem execution_of_legal {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution cfg r honest T st) {ss : List Step} (hl : legal cfg r honest T st ss = true) :
    Execution cfg r honest (record r T st ss).1 (record r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s hl.1 hx) hl.2

end BtcPolicy.RungAssembly
