import BtcPolicy.RungAssembly
import BtcPolicy.VariantReceipt
/-! Each class's assembly check and the ladder's finalization on one ladder-bearing run. On `RungAssembly`'s run an
inherited base step is admitted as `LadderRelease.admits` admits it, so an assembly (`Kernel.Event.packageAccepted`)
passes `Sweep.assemblyOk` alone, which checks the Escape role and counts `Federation.held`; the all-class
`Assembly.assemblyOk` is not conjoined there, and a Hot spend over a missing prevout, or a claw-back whose package
the backend rejects, is assembled (`Exhibits.ClassAssembly.hot_refused`, `Exhibits.ClassAssembly.clawback_refused`).
Its rung steps count `RungIngress.held`, which compares no user-signature hash. This module is a labelled layer over
`RungAssembly`'s states and steps, as `BtcPolicy.VariantReceipt` is over the federation's: no new kernel event and
no existing definition changed. A history carries one label with each step (`ClassAssembly.LTrace`); its labelled
federation steps (`ClassAssembly.fedL`) carry `VariantReceipt.labelOk`, so every assembly here counts
`VariantReceipt.held` (`ClassAssembly.heldAt`), the store that compares the hash.

**An inherited assembly.** `ClassAssembly.guard`: an assembly of a commitment id needs every resident under that id
to pass `ClassAssembly.candOk` at the node's latest observation, its own history and its possession under the
variant-bound store. A resident that is not Escape-role passes `Assembly.checkAt`, the class check of
`BtcPolicy.Assembly` (a Hot spend's or a singleton claw-back's, `Assembly.checkAt_spend`, `Assembly.checkAt_clawback`).
An Escape-role resident passes only as the ladder's finalization of rung 0: `Ladder.finalize` over the same
possession at its latch is rung 0, and rung 0 passes `Assembly.rungCheck` at the node's own read
(`RungRelease.readAt`). So the base path cannot assemble an Escape whose finalization is a higher rung
(`Exhibits.ClassAssembly.base_cannot_bypass`). `ClassAssembly.guard_sound` and `ClassAssembly.escape_sound` unfold
what an admitted inherited assembly established.

**A rung's assembly and send.** `ClassAssembly.assembleOk` is `RungAssembly.assembleOk` with the variant-bound
possession: the rung is the finalization's and passes `Assembly.rungCheck` for that rung, with no base check for a
higher rung. The send is `RungAssembly.sendOk`. `ClassAssembly.assemble_sound`, `ClassAssembly.assembled_origin`
and `ClassAssembly.sent_in_order` restate `RungAssembly`'s results over this possession; on the base path
`ClassAssembly.assembled_of_packageOk` and `ClassAssembly.submitted_in_order` say that a standing package test, and so
every kernel submission, was earned at an earlier admitted assembly whose guard passed for that resident's class and
transaction (`ClassAssembly.Assembled`). One configuration (`RungAssembly.Cfg`) gives the ladder, the release check,
the threshold's key list, the store's key list, the class check's witnesses and the backend verdict.

**The relation to the earlier layers.** Forgetting the labels and the rung steps leaves a `LadderRelease.Execution`
(`ClassAssembly.to_ladder`), and the labelled federation steps are a `VariantReceipt.Execution`
(`ClassAssembly.to_labelled`), so the results of `LadderRelease`, `RungRelease`, `Sweep`, `Federation`,
`VariantReceipt` and the kernel apply. A rung step is not one of `RungAssembly`'s: its broader possession can select
a higher rung or count a partial this store refused (`Exhibits.ClassAssembly.mismatch_unassembled`). On the base-only
domain, where no node retains a rung at any state and every ladder pass lists nothing, the run is an
`Assembly.Execution` of the same configuration's class check (`ClassAssembly.to_assembly`); there the guard is
exactly `Assembly.assemblyOk` when the two possession sets have the same members (`ClassAssembly.guard_bare`), which
is what compatible accepted metadata gives. The absence of rungs alone does not give it: a partial the hash-comparing
store refuses is still in `Federation.held`.

**Not modelled here.** Refresh ingress. The kernel's own bits: a package test set at a base assembly stands when the
latch later rises, and the kernel's send reads no finalization, so a base Escape assembled at rung 0 can still be
sent after a higher rung becomes finalizable; that is the lifecycle's to connect. A resident txid outside the ladder
in the batched read. A hash source for the rows of a class that is not Escape-role (`VariantReceipt.storable`
compares none). `NCH-24`'s expiry branch. -/

namespace BtcPolicy.ClassAssembly
open BtcPolicy.Kernel
open BtcPolicy.Sweep (Backend)
open BtcPolicy.RungAssembly (Cfg State Step escapeAt)

/-! ## The labelled history -/

/-- A history of the rung-assembly layer, newest first, each step with the state it was taken in and its label. -/
abbrev LTrace := List (State × Step × Option Nat)

/-- The history without its labels. -/
def forget (T : LTrace) : RungAssembly.Trace := T.map fun a => (a.1, a.2.1)

/-- The composed sweep steps of a labelled history. -/
def sweepT (T : LTrace) : Sweep.Trace := RungAssembly.sweepTrace (forget T)

/-- The labelled federation steps of a labelled history, each with its federation state. -/
def fedL : LTrace → VariantReceipt.LTrace
  | [] => []
  | (st, .base (.fed s), h) :: T => (st.sw.fed, s, h) :: fedL T
  | _ :: T => fedL T

theorem forget_fedL : ∀ T : LTrace, VariantReceipt.forget (fedL T) = Sweep.fedTrace (sweepT T)
  | [] => rfl
  | (st, s, h) :: T => by
    cases s with
    | base b =>
      cases b with
      | fed s =>
        simp only [fedL, sweepT, forget, List.map_cons, RungAssembly.sweepTrace, Sweep.fedTrace,
          VariantReceipt.forget] at *
        rw [← VariantReceipt.forget.eq_1, forget_fedL T]; rfl
      | chain b =>
        simp only [fedL, sweepT, forget, List.map_cons, RungAssembly.sweepTrace, Sweep.fedTrace]
        exact forget_fedL T
      | observe j b =>
        simp only [fedL, sweepT, forget, List.map_cons, RungAssembly.sweepTrace, Sweep.fedTrace]
        exact forget_fedL T
    | assemble i cid m =>
      simp only [fedL, sweepT, forget, List.map_cons, RungAssembly.sweepTrace]
      exact forget_fedL T
    | send i env cid m =>
      simp only [fedL, sweepT, forget, List.map_cons, RungAssembly.sweepTrace]
      exact forget_fedL T

theorem sweepT_base (st : State) (s : Sweep.Step) (h : Option Nat) (T : LTrace) :
    sweepT ((st, .base s, h) :: T) = (st.sw, s) :: sweepT T := rfl

theorem sweepT_assemble (st : State) (i cid m : Nat) (h : Option Nat) (T : LTrace) :
    sweepT ((st, .assemble i cid m, h) :: T) = sweepT T := rfl

theorem sweepT_send (st : State) (i : Nat) (env : Env) (cid m : Nat) (h : Option Nat) (T : LTrace) :
    sweepT ((st, .send i env cid m, h) :: T) = sweepT T := rfl

/-- A step of the sweep trace is a base step of the labelled history, at the same sweep state. -/
theorem mem_sweepT : ∀ {T : LTrace} {p : Sweep.State × Sweep.Step}, p ∈ sweepT T →
    ∃ q ∈ T, q.1.sw = p.1 ∧ q.2.1 = .base p.2
  | [], _, hp => by cases hp
  | (st, s, h) :: T, p, hp => by
    cases s with
    | base b =>
      rw [sweepT_base] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
      · obtain ⟨q, hq, h1, h2⟩ := mem_sweepT hp
        exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
    | assemble i cid m =>
      rw [sweepT_assemble] at hp
      obtain ⟨q, hq, h1, h2⟩ := mem_sweepT hp
      exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
    | send i env cid m =>
      rw [sweepT_send] at hp
      obtain ⟨q, hq, h1, h2⟩ := mem_sweepT hp
      exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-! ## The possession and the finalization -/

/-- Node `i`'s possession in state `st` after history `T`: `VariantReceipt.held` over the labelled federation steps,
with the ladder's key list as the store's. -/
@[req "DUR-28"]
def heldAt (cfg : Cfg) (st : State) (T : LTrace) (i : Nat) : List Authority.Sig :=
  VariantReceipt.held cfg.lc.pre.sweep.keys i (fedL T) st.sw.fed

/-- `DUR-28`'s finalization at node `i` for candidate `c` over that possession, at its latch. -/
@[req "DUR-28"]
def finalAt (cfg : Cfg) (st : State) (T : LTrace) (i : Nat) (c : Cand) : Option Nat :=
  Ladder.finalize cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t c.ladder (heldAt cfg st T i) c.track.latch

/-- Node `i`'s own read for candidate `c`: `RungRelease.readAt` on the sweep trace. -/
def readAt (st : State) (T : LTrace) (i : Nat) (c : Cand) : Ladder.Read := RungRelease.readAt st.sw (sweepT T) i c

/-! ## The inherited assembly -/

/-- The check one resident owes at an inherited assembly at node `i`: an observation, and then, for an Escape-role
resident, the finalization of rung 0 with rung 0's `Assembly.rungCheck` at the node's own read; for every other
resident, its class's `Assembly.checkAt`. Each over the variant-bound possession. -/
@[req "SPN-39"]
def candOk (cfg : Cfg) (st : State) (T : LTrace) (i : Nat) (c : Cand) : Bool :=
  match st.sw.obs i with
  | none => false
  | some b =>
    if c.isEscape then
      finalAt cfg st T i c == some 0 && Assembly.rungCheck cfg.asm (readAt st T i c) b c (heldAt cfg st T i) 0
    else
      Assembly.checkAt cfg.asm (Sweep.authorizedAt st.sw (sweepT T) i) (Assembly.clawTxsAt st.sw (sweepT T) i)
        (st.sw.fed.worlds i).node (heldAt cfg st T i) b c

/-- An assembly of a commitment needs `ClassAssembly.candOk` on every resident under that id, whatever its class.
Every other step passes. -/
@[req "SPN-39"]
def guard (cfg : Cfg) (st : State) (T : LTrace) : Sweep.Step → Bool
  | .fed (.process i _ (.packageAccepted cid)) =>
    (st.sw.fed.worlds i).node.cands.all fun c =>
      !(c.id == cid) || candOk cfg st T i c
  | _ => true

/-- A rung's assembly at node `i`: an observation, the rung is the finalization's over the variant-bound possession,
and it passes `Assembly.rungCheck` for that rung at the node's own read. -/
@[req "DUR-29"]
def assembleOk (cfg : Cfg) (st : State) (T : LTrace) (i cid m : Nat) : Bool :=
  match escapeAt (st.sw.fed.worlds i).node cid, st.sw.obs i with
  | some c, some b => finalAt cfg st T i c == some m &&
      Assembly.rungCheck cfg.asm (readAt st T i c) b c (heldAt cfg st T i) m
  | _, _ => false

/-! ## The layer -/

/-- Which steps may be taken: a sweep step `LadderRelease` admits and the guard passes, or a rung step at an honest
node. -/
def admits (cfg : Cfg) (r : Rules) (honest : List Nat) (st : State) (T : LTrace) : Step → Bool
  | .base s => LadderRelease.admits cfg.lc honest st.sw (sweepT T) s && guard cfg st T s
  | .assemble i cid m => honest.contains i && assembleOk cfg st T i cid m
  | .send i env cid m => honest.contains i && RungAssembly.sendOk r env st i cid m

/-- Which label a step may carry: a federation step's is `VariantReceipt.labelOk`'s over the labelled federation
history; every other step's is not read. -/
@[req "NCH-24"]
def labelOk (r : Rules) (st : State) (T : LTrace) : Step → Option Nat → Bool
  | .base (.fed s), h => VariantReceipt.labelOk r (VariantReceipt.forget (fedL T)) st.sw.fed s h
  | _, _ => true

/-- A reachable execution of the layer. -/
inductive Execution (cfg : Cfg) (r : Rules) (honest : List Nat) : LTrace → State → Prop
  | init (st : State) (h : RungAssembly.Fresh honest st) : Execution cfg r honest [] st
  | next {T st} (s : Step) (h : Option Nat) (ha : admits cfg r honest st T s = true)
      (hl : labelOk r st T s h = true) : Execution cfg r honest T st →
      Execution cfg r honest ((st, s, h) :: T) (RungAssembly.apply r st s)

/-! ## The relation to the earlier layers -/

/-- **The layer over `LadderRelease`.** Forgetting the labels and the rung steps leaves a `LadderRelease.Execution`. -/
@[req "SPN-39"]
theorem to_ladder {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) : LadderRelease.Execution cfg.lc r honest (sweepT T) st.sw := by
  induction hx with
  | init st h => exact .init _ h.1
  | next s h ha _ _ ih =>
    cases s with
    | base s =>
      simp only [admits, Bool.and_eq_true] at ha
      exact .next s ha.1 ih
    | assemble i cid m => rw [RungAssembly.apply_sw r _ (by simp)]; exact ih
    | send i env cid m => rw [RungAssembly.apply_sw r _ (by simp)]; exact ih

/-- **The labelled federation steps.** They are a `VariantReceipt.Execution`, so its store results apply. -/
@[req "NCH-24"]
theorem to_labelled {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) : VariantReceipt.Execution r honest (fedL T) st.sw.fed := by
  induction hx with
  | init st h => exact .init _ h.1.1
  | next s h ha hl _ ih =>
    cases s with
    | base b =>
      cases b with
      | fed s =>
        simp only [admits, LadderRelease.admits, Sweep.admits, Bool.and_eq_true] at ha
        exact .next s h ha.1.1.1 hl ih
      | chain b => exact ih
      | observe j b => exact ih
    | assemble i cid m => rw [RungAssembly.apply_sw r _ (by simp)]; exact ih
    | send i env cid m => rw [RungAssembly.apply_sw r _ (by simp)]; exact ih

/-- A step of an execution was admitted at its own state, after a reachable history, with an admissible label. -/
theorem prefix_exec {cfg : Cfg} {r : Rules} {honest : List Nat} :
    ∀ {T : LTrace} {st : State}, Execution cfg r honest T st →
      ∀ {T₂ T₁ : LTrace} {st₀ : State} {s : Step} {h : Option Nat}, T = T₂ ++ (st₀, s, h) :: T₁ →
        Execution cfg r honest T₁ st₀ ∧ admits cfg r honest st₀ T₁ s = true ∧ labelOk r st₀ T₁ s h = true := by
  intro T st hx
  induction hx with
  | init st h => intro T₂ T₁ st₀ s h' hT; cases T₂ <;> cases hT
  | next s' h' ha hl hx ih =>
    intro T₂ T₁ st₀ s h hT
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hT
      exact ⟨hx, ha, hl⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      exact ih hT.2

/-- Each signature an honest node holds under the variant-bound store is its own or a partial of the inventory. -/
@[req "DUR-28"]
theorem held_origin {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) {x : Authority.Sig}
    (hm : x ∈ heldAt cfg st T i) : x.signer = i ∨ ∃ y ∈ st.sw.fed.parts, Authority.sig y = x :=
  VariantReceipt.held_origin (to_labelled hx) hi hm

/-! ## What an assembly established -/

/-- What a finalized rung's `Assembly.rungCheck` established at a read whose ladder is the candidate's: the rung is at
index `m`, at or below the latch, its own transaction has the quorum among its own records, no rung above it at or
below the latch has the quorum, and it is covered, meets the floor at its exact finalized vsize, has its admitted
ancestry and the backend's acceptance. -/
@[req "DUR-28"]
theorem rung_sound {cfg : Cfg} {rd : Ladder.Read} {b : Backend} {c : Cand} {R : List Authority.Sig} {m : Nat}
    (hrd : Ladder.txs rd c = c.ladder.map (·.tx))
    (hf : Ladder.finalize cfg.lc.pre.sweep.keys rd.reg.t c.ladder R c.track.latch = some m)
    (hr : Assembly.rungCheck cfg.asm rd b c R m = true) :
    ∃ g, c.ladder[m]? = some g ∧ m ≤ c.track.latch ∧
      Authority.quorum cfg.lc.pre.sweep.keys rd.reg.t g.tx (R.filter fun s => s.msg.1 == g.tx.id) = true ∧
      (∀ k, m < k → k ≤ c.track.latch →
        Ladder.quorumAt cfg.lc.pre.sweep.keys rd.reg.t c.ladder R k = false) ∧
      Ladder.coveredTx cfg.lc.pre.sweep (Ladder.passAt cfg.lc.pre.sweep rd b) g.tx = true ∧
      PreRelease.feeOk cfg.lc.pre (Assembly.exactVsize cfg.asm g.tx) g.tx = true ∧
      (∃ anc, Package.validate cfg.lc.pre.sweep.ancestry cfg.lc.pre.sweep.creator (Sweep.snapshot rd.A b)
        b.mempool rd.A (Sweep.candidateOf g.tx)
        (Ladder.replacesOf (c.ladder.map (·.tx)) (PreRelease.membership b (c.ladder.map (·.tx))) m) =
          .admitted anc) ∧
      Assembly.packageOk cfg.asm b g.tx = true := by
  obtain ⟨hq, hle⟩ := Ladder.finalize_sound _ _ _ _ _ _ hf
  unfold Ladder.quorumAt at hq
  cases hg : c.ladder[m]? with
  | none => rw [hg] at hq; cases hq
  | some g =>
    rw [hg] at hq
    obtain ⟨tx, htx, -, hcov, hfee, hanc, hpk⟩ := Assembly.rungCheck_sound hr
    rw [hrd, List.getElem?_map, hg] at htx
    simp only [Option.map_some, Option.some.injEq] at htx
    subst htx
    rw [hrd] at hanc
    refine ⟨g, rfl, hle, ?_, fun k hk hkl => RungAssembly.finalize_above hf hk hkl, hcov, hfee, hanc, hpk⟩
    rw [← Ladder.quorum_own_rung]
    exact hq

theorem txs_readAt (st : State) (T : LTrace) (i : Nat) (c : Cand) :
    Ladder.txs (readAt st T i c) c = c.ladder.map (·.tx) := RungAssembly.txs_readAt _ _ _ _

theorem reg_readAt (st : State) (T : LTrace) (i : Nat) (c : Cand) :
    (readAt st T i c).reg = (st.sw.fed.worlds i).node := rfl

theorem A_readAt (st : State) (T : LTrace) (i : Nat) (c : Cand) :
    (readAt st T i c).A = Sweep.authorizedAt st.sw (sweepT T) i := rfl

/-- **What an inherited assembly established** (`SPN-39`). At an admitted assembly of commitment `cid` at node `i`,
each resident `c` under `cid` finds an observation `b` at the node and passed its check there over the variant-bound
possession: an Escape-role resident as the finalization of rung 0 with rung 0's `Assembly.rungCheck` at the node's
own read, and every other resident its class's `Assembly.checkAt` at the node's authorized set and registered
claw-backs. -/
@[req "SPN-39"]
theorem guard_sound {cfg : Cfg} {r : Rules} {honest : List Nat} {st : State} {T : LTrace} {i : Nat} {env : Env}
    {cid : Nat} (ha : admits cfg r honest st T (.base (.fed (.process i env (.packageAccepted cid)))) = true)
    {c : Cand} (hc : c ∈ (st.sw.fed.worlds i).node.cands) (hid : c.id = cid) :
    ∃ b, st.sw.obs i = some b ∧
      (c.isEscape = true → finalAt cfg st T i c = some 0 ∧
        Assembly.rungCheck cfg.asm (readAt st T i c) b c (heldAt cfg st T i) 0 = true) ∧
      (c.isEscape = false → Assembly.checkAt cfg.asm (Sweep.authorizedAt st.sw (sweepT T) i)
        (Assembly.clawTxsAt st.sw (sweepT T) i) (st.sw.fed.worlds i).node (heldAt cfg st T i) b c = true) := by
  simp only [admits, guard, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at ha
  have hk : candOk cfg st T i c = true := by
    rcases ha.2 c hc with h | h
    · exact absurd hid h
    · exact h
  unfold candOk at hk
  cases hb : st.sw.obs i with
  | none => rw [hb] at hk; cases hk
  | some b =>
    rw [hb] at hk
    refine ⟨b, rfl, fun he => ?_, fun he => ?_⟩
    · simp only [he, if_true, Bool.and_eq_true, beq_iff_eq] at hk
      exact hk
    · simp only [he] at hk
      exact hk

/-- **An inherited Escape assembly is rung 0's finalization** (`DUR-28`). What `ClassAssembly.guard_sound` gives on an
Escape-role resident unfolds as a rung's assembly at rung 0: the base's own quorum over the variant-bound possession,
no rung above it at or below the latch with the quorum, coverage at the ladder's pass, the floor at the exact
finalized vsize, its ancestry and the backend's acceptance. -/
@[req "DUR-28"]
theorem escape_sound {cfg : Cfg} {r : Rules} {honest : List Nat} {st : State} {T : LTrace} {i : Nat} {env : Env}
    {cid : Nat} (ha : admits cfg r honest st T (.base (.fed (.process i env (.packageAccepted cid)))) = true)
    {c : Cand} (hc : c ∈ (st.sw.fed.worlds i).node.cands) (hid : c.id = cid) (he : c.isEscape = true) :
    ∃ b, st.sw.obs i = some b ∧
      Authority.quorum cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t c.tx
        ((heldAt cfg st T i).filter fun s => s.msg.1 == c.tx.id) = true ∧
      (∀ k, 0 < k → k ≤ c.track.latch →
        Ladder.quorumAt cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t c.ladder (heldAt cfg st T i) k = false) ∧
      Ladder.coveredTx cfg.lc.pre.sweep (Ladder.passAt cfg.lc.pre.sweep (readAt st T i c) b) c.tx = true ∧
      PreRelease.feeOk cfg.lc.pre (Assembly.exactVsize cfg.asm c.tx) c.tx = true ∧
      (∃ anc, Package.validate cfg.lc.pre.sweep.ancestry cfg.lc.pre.sweep.creator
        (Sweep.snapshot (readAt st T i c).A b) b.mempool (readAt st T i c).A (Sweep.candidateOf c.tx)
        (Ladder.replacesOf (c.ladder.map (·.tx)) (PreRelease.membership b (c.ladder.map (·.tx))) 0) =
          .admitted anc) ∧
      Assembly.packageOk cfg.asm b c.tx = true := by
  obtain ⟨b, hb, hesc, -⟩ := guard_sound ha hc hid
  obtain ⟨hf, hr⟩ := hesc he
  obtain ⟨g, hg, -, hq, habove, hcov, hfee, hanc, hpk⟩ := rung_sound (txs_readAt st T i c) hf hr
  simp only [Cand.ladder, List.getElem?_cons_zero, Option.some.injEq] at hg
  subst hg
  exact ⟨b, hb, hq, habove, hcov, hfee, hanc, hpk⟩

/-- **What a rung's assembly established** (`DUR-28`, `DUR-29`), over the variant-bound possession: an observation and
an Escape-role resident under the id, the assembled rung at index `m` at or below its latch with its own quorum and
no rung above it at or below the latch with one, and that rung's coverage, exact fee, ancestry as a replacement of a
resident lower rung, and package verdict. -/
@[req "DUR-29"]
theorem assemble_sound {cfg : Cfg} {st : State} {T : LTrace} {i cid m : Nat}
    (h : assembleOk cfg st T i cid m = true) :
    ∃ c b g, escapeAt (st.sw.fed.worlds i).node cid = some c ∧ st.sw.obs i = some b ∧ c.ladder[m]? = some g ∧
      m ≤ c.track.latch ∧
      Authority.quorum cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t g.tx
        ((heldAt cfg st T i).filter fun s => s.msg.1 == g.tx.id) = true ∧
      (∀ k, m < k → k ≤ c.track.latch →
        Ladder.quorumAt cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t c.ladder (heldAt cfg st T i) k = false) ∧
      Ladder.coveredTx cfg.lc.pre.sweep (Ladder.passAt cfg.lc.pre.sweep (readAt st T i c) b) g.tx = true ∧
      PreRelease.feeOk cfg.lc.pre (Assembly.exactVsize cfg.asm g.tx) g.tx = true ∧
      (∃ anc, Package.validate cfg.lc.pre.sweep.ancestry cfg.lc.pre.sweep.creator
        (Sweep.snapshot (readAt st T i c).A b) b.mempool (readAt st T i c).A (Sweep.candidateOf g.tx)
        (Ladder.replacesOf (c.ladder.map (·.tx)) (PreRelease.membership b (c.ladder.map (·.tx))) m) =
          .admitted anc) ∧
      Assembly.packageOk cfg.asm b g.tx = true := by
  unfold assembleOk at h
  cases hc : escapeAt (st.sw.fed.worlds i).node cid with
  | none => simp [hc] at h
  | some c =>
    cases hb : st.sw.obs i with
    | none => simp [hc, hb] at h
    | some b =>
      simp only [hc, hb, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨g, hg, hle, hq, habove, hcov, hfee, hanc, hpk⟩ := rung_sound (txs_readAt st T i c) h.1 h.2
      exact ⟨c, b, g, rfl, rfl, hg, hle, hq, habove, hcov, hfee, hanc, hpk⟩

/-! ## Every assembly has an origin -/

/-- Node `i` assembled rung txid `x` under commitment `cid` earlier in `T`, `T₁` the history before that step: its
Escape-role resident under the id, its observation, rung `m` of that Escape's ladder with txid `x`, the
finalization's index over the variant-bound possession, and `Assembly.rungCheck` passed there. -/
def AssembledRung (cfg : Cfg) (T : LTrace) (i cid x : Nat) : Prop :=
  ∃ T₁ T₂ st m h, T = T₂ ++ (st, .assemble i cid m, h) :: T₁ ∧ ∃ c b g,
    escapeAt (st.sw.fed.worlds i).node cid = some c ∧ st.sw.obs i = some b ∧ c.ladder[m]? = some g ∧ g.tx.id = x ∧
    finalAt cfg st T₁ i c = some m ∧
    Assembly.rungCheck cfg.asm (readAt st T₁ i c) b c (heldAt cfg st T₁ i) m = true

theorem AssembledRung.cons {cfg : Cfg} {T : LTrace} {i cid x : Nat} (y : State × Step × Option Nat)
    (h : AssembledRung cfg T i cid x) : AssembledRung cfg (y :: T) i cid x := by
  obtain ⟨T₁, T₂, st, m, h', rfl, rest⟩ := h
  exact ⟨T₁, y :: T₂, st, m, h', rfl, rest⟩

/-- **Every assembled rung was assembled.** Each (node, commitment id, txid) recorded as assembled is an honest
node's, from an admitted rung assembly earlier in the history over the variant-bound possession. -/
@[req "DUR-28"]
theorem assembled_origin {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) {i cid x : Nat} (h : (i, cid, x) ∈ st.assembled) :
    i ∈ honest ∧ AssembledRung cfg T i cid x := by
  induction hx with
  | init st h0 => rw [h0.2.1] at h; cases h
  | @next T st s lab ha hl hx ih =>
    cases s with
    | base s =>
      obtain ⟨hi, ha'⟩ := ih h
      exact ⟨hi, ha'.cons _⟩
    | send j env cid' m =>
      simp only [RungAssembly.apply] at h
      split at h <;> (obtain ⟨hi, ha'⟩ := ih h; exact ⟨hi, ha'.cons _⟩)
    | assemble j cid' m =>
      simp only [RungAssembly.apply] at h
      split at h
      · rename_i g hg
        rcases List.mem_cons.1 h with he | h
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          simp only [admits, Bool.and_eq_true, List.contains_iff_mem] at ha
          obtain ⟨hi, hok⟩ := ha
          refine ⟨hi, T, [], st, m, lab, rfl, ?_⟩
          unfold assembleOk at hok
          cases hc : escapeAt (st.sw.fed.worlds i).node cid with
          | none => simp [hc] at hok
          | some c =>
            cases hb : st.sw.obs i with
            | none => simp [hc, hb] at hok
            | some b =>
              simp only [hc, hb, Bool.and_eq_true, beq_iff_eq] at hok
              rw [RungAssembly.rungAt_of hc] at hg
              exact ⟨c, b, g, rfl, rfl, hg, rfl, hok.1, hok.2⟩
        · obtain ⟨hi, ha'⟩ := ih h
          exact ⟨hi, ha'.cons _⟩
      · obtain ⟨hi, ha'⟩ := ih h
        exact ⟨hi, ha'.cons _⟩

/-- **`DUR-29`'s order on a rung's send.** Every rung a node sent was sent by an honest node at a step whose own state
and instant re-authorize the Escape, after that node's own admitted assembly of the same txid over the variant-bound
possession (`ClassAssembly.AssembledRung`). -/
@[req "DUR-29"]
theorem sent_in_order {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) {i cid x : Nat} (h : (i, cid, x) ∈ st.sent) :
    i ∈ honest ∧ ∃ T₁ T₂ st₀ env m lab, T = T₂ ++ (st₀, .send i env cid m, lab) :: T₁ ∧ ∃ c g,
      escapeAt (st₀.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some g ∧ g.tx.id = x ∧
      due r env (st₀.sw.fed.worlds i).node c = true ∧
      releaseAuthorized r (st₀.sw.fed.worlds i).node c = true ∧ AssembledRung cfg T₁ i cid x := by
  induction hx with
  | init st h0 => rw [h0.2.2] at h; cases h
  | @next T st s lab ha hl hx ih =>
    have lift (h : (i, cid, x) ∈ st.sent) : i ∈ honest ∧ ∃ T₁ T₂ st₀ env m lab',
        (st, s, lab) :: T = T₂ ++ (st₀, .send i env cid m, lab') :: T₁ ∧ ∃ c g,
          escapeAt (st₀.sw.fed.worlds i).node cid = some c ∧ c.ladder[m]? = some g ∧ g.tx.id = x ∧
          due r env (st₀.sw.fed.worlds i).node c = true ∧
          releaseAuthorized r (st₀.sw.fed.worlds i).node c = true ∧ AssembledRung cfg T₁ i cid x := by
      obtain ⟨hi, T₁, T₂, st₀, env, m, lab', rfl, rest⟩ := ih h
      exact ⟨hi, T₁, (st, s, lab) :: T₂, st₀, env, m, lab', rfl, rest⟩
    cases s with
    | base s => exact lift h
    | assemble j cid' m => simp only [RungAssembly.apply] at h; split at h <;> exact lift h
    | send j env cid' m =>
      simp only [RungAssembly.apply] at h
      split at h
      · rename_i g hg
        rcases List.mem_cons.1 h with he | h
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          simp only [admits, Bool.and_eq_true, List.contains_iff_mem] at ha
          obtain ⟨hi, hok⟩ := ha
          refine ⟨hi, T, [], st, env, m, lab, rfl, ?_⟩
          obtain ⟨c, g', hc, hg', hmem, hdue, hauth⟩ := RungAssembly.sendOk_iff.1 hok
          rw [RungAssembly.rungAt_of hc, hg'] at hg
          simp only [Option.some.injEq] at hg
          subst hg
          exact ⟨c, g', hc, hg', rfl, hdue, hauth, (assembled_origin hx hmem).2⟩
        · exact lift h
      · exact lift h

/-! ## The inherited assembly before a kernel send -/

/-- Node `i` assembled this candidate earlier in `T` on the base path: an assembly step for its id, taken in a state
where a resident with the same id, transaction and pair passed `ClassAssembly.candOk` against the reads of that
state, and the kernel's own package test. `T₁` is the history before that step. -/
def Assembled (cfg : Cfg) (r : Rules) (T : LTrace) (i : Nat) (c : Cand) : Prop :=
  ∃ T₁ T₂ st env h d, T = T₂ ++ (st, .base (.fed (.process i env (.packageAccepted c.id))), h) :: T₁ ∧
    d ∈ (st.sw.fed.worlds i).node.cands ∧ d.id = c.id ∧ d.tx = c.tx ∧ d.pair = c.pair ∧
    candOk cfg st T₁ i d = true ∧ due r env (st.sw.fed.worlds i).node d = true ∧
    releaseAuthorized r (st.sw.fed.worlds i).node d = true ∧ d.released = true ∧
    heldQuorum (st.sw.fed.worlds i).node.t d = true

theorem Assembled.cons {cfg : Cfg} {r : Rules} {T : LTrace} {i : Nat} {c : Cand} (y : State × Step × Option Nat)
    (h : Assembled cfg r T i c) : Assembled cfg r (y :: T) i c := by
  obtain ⟨T₁, T₂, st, env, h', d, rfl, rest⟩ := h
  exact ⟨T₁, y :: T₂, st, env, h', d, rfl, rest⟩

theorem Assembled.congr {cfg : Cfg} {r : Rules} {T : LTrace} {i : Nat} {c c' : Cand}
    (h : Assembled cfg r T i c) (h1 : c'.id = c.id) (h2 : c'.tx = c.tx) (h3 : c'.pair = c.pair) :
    Assembled cfg r T i c' := by
  obtain ⟨T₁, T₂, st, env, h', d, hT, hd, e1, e2, e3, rest⟩ := h
  exact ⟨T₁, T₂, st, env, h', d, by rw [h1]; exact hT, hd, e1.trans h1.symm, e2.trans h2.symm,
    e3.trans h3.symm, rest⟩

/-- **A standing package test was earned here.** On any resident of an honest node, a package test was set at an
earlier admitted assembly whose guard passed `ClassAssembly.candOk` on a resident with the same id, transaction and
pair: for an Escape, rung 0's finalization; for every other class, its class check; each over the variant-bound
possession. -/
@[req "SPN-39"]
theorem assembled_of_packageOk {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) :
    ∀ c ∈ (st.sw.fed.worlds i).node.cands, c.packageOk = true → Assembled cfg r T i c := by
  induction hx with
  | init st h =>
    intro c hc
    rw [(h.1.1.2.2 i hi).2.2.2.1] at hc
    cases hc
  | @next T st s lab ha hl _ ih =>
    intro c hc hp
    cases s with
    | assemble j cid m =>
      rw [RungAssembly.apply_sw r _ (by simp)] at hc
      exact (ih c hc hp).cons _
    | send j env cid m =>
      rw [RungAssembly.apply_sw r _ (by simp)] at hc
      exact (ih c hc hp).cons _
    | base b =>
      cases b with
      | chain b => exact (ih c hc hp).cons _
      | observe j b => exact (ih c hc hp).cons _
      | fed s =>
        simp only [RungAssembly.apply, Sweep.apply] at hc
        cases hact : Federation.actor s with
        | none =>
          rw [Federation.apply_no_actor r _ s hact i] at hc
          exact (ih c hc hp).cons _
        | some a =>
          obtain ⟨j, env, e⟩ := a
          rw [Federation.apply_of_actor r _ s hact i] at hc
          split at hc
          · rename_i hij
            subst hij
            rcases Sweep.packageOk_origin r env _ e hc hp with
              ⟨d, hd, h1, h2, h3, hpd⟩ | ⟨rfl, d, hd, h1, h2, h3, hdue, hauth, hrel, hq⟩
            · exact ((ih d hd hpd).congr h1.symm h2.symm h3.symm).cons _
            · have hs := Sweep.actor_packageAccepted hact
              subst hs
              simp only [admits, guard, Bool.and_eq_true, List.all_eq_true] at ha
              have hck := ha.2 d hd
              simp only [h1, beq_self_eq_true, Bool.not_true, Bool.false_or] at hck
              exact ⟨_, [], _, env, lab, d, rfl, hd, h1, h2, h3, hck, hdue, hauth, hrel, hq⟩
          · exact (ih c hc hp).cons _

/-- **`DUR-29`'s order on every kernel submission, of every class.** What a kernel send of this run submits is a
resident under that id whose package test stands, which the send's own state re-authorizes, and whose package test
was earned at an earlier admitted assembly passing `ClassAssembly.candOk` for that resident (`ClassAssembly.Assembled`):
rung 0's finalization for an Escape, its class check otherwise. -/
@[req "DUR-29"]
theorem submitted_in_order {cfg : Cfg} {r : Rules} (hr : r.reauth = .beforeSend) {honest : List Nat}
    {T : LTrace} {st : State} (hx : Execution cfg r honest T st) {i : Nat} {env : Env} {cid x : Nat}
    (ha : admits cfg r honest st T (.base (.fed (.process i env (.send cid)))) = true)
    (hs : x ∈ Sweep.submits r st.sw (.fed (.process i env (.send cid)))) :
    ∃ c ∈ (st.sw.fed.worlds i).node.cands, c.id = cid ∧ c.tx.id = x ∧ c.packageOk = true ∧
      due r env (st.sw.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.sw.fed.worlds i).node c = true ∧ Assembled cfg r T i c := by
  have ha' : Sweep.admits cfg.lc.pre.sweep honest st.sw (sweepT T) (.fed (.process i env (.send cid))) = true := by
    simp only [admits, LadderRelease.admits, Bool.and_eq_true] at ha
    exact ha.1.1
  have hi : i ∈ honest := by
    simp only [Sweep.admits, Federation.admits, Bool.and_eq_true, List.contains_iff_mem] at ha'
    exact ha'.1.1
  obtain ⟨c, hc, hid, hx', hp, hdue, hauth, -⟩ :=
    Sweep.submitted_in_order hr (LadderRelease.to_sweep (to_ladder hx)) ha' hs
  exact ⟨c, hc, hid, hx', hp, hdue, hauth, assembled_of_packageOk hx hi c hc hp⟩

/-! ## The base-only domain -/

/-- More records never lower a quorum. -/
theorem quorum_mono {keys : List Nat} {t : Nat} {X : Tx} {R R' : List Authority.Sig} (hR : ∀ x ∈ R, x ∈ R')
    (h : Authority.quorum keys t X R = true) : Authority.quorum keys t X R' = true := by
  simp only [Authority.quorum, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, fun k hk => Nat.le_trans (h.2 k hk) (Authority.signers_mono (fun s h => h) hR)⟩

/-- More records never refuse a class check that passed. -/
theorem checkAt_mono {cfg : Assembly.Cfg} {A C : List Nat} {n : Node} {R R' : List Authority.Sig} {b : Backend}
    {c : Cand} (hR : ∀ x ∈ R, x ∈ R') (h : Assembly.checkAt cfg A C n R b c = true) :
    Assembly.checkAt cfg A C n R' b c = true := by
  simp only [Assembly.checkAt, Sweep.possessed, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨quorum_mono hR h.1.1.1, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- On a ladder of the base alone, the finalization is rung 0 exactly when the base has the quorum. -/
theorem finalize_single (keys : List Nat) (t : Nat) (g : Rung) (R : List Authority.Sig) :
    ∀ top, Ladder.finalize keys t [g] R top = if Authority.quorum keys t g.tx R then some 0 else none
  | 0 => by simp [Ladder.finalize, Ladder.quorumAt]
  | top + 1 => by
    simp only [Ladder.finalize, Ladder.quorumAt, List.getElem?_cons_succ, List.getElem?_nil]
    exact finalize_single keys t g R top

/-- With no rung retained at the node, the node's own read lists no rung. -/
theorem readAt_bare {st : State} {T : LTrace} {i : Nat} {c : Cand}
    (hn : ∀ d ∈ (st.sw.fed.worlds i).node.cands, d.above = []) (hc : c.above = []) (k : Nat) :
    (readAt st T i c).rungs k = [] := by
  simp only [readAt, RungRelease.readAt, Ladder.Read.own, RungRelease.rungsOf]
  split
  · simp [hc]
  · cases hf : (st.sw.fed.worlds i).node.cands.find? (fun d => d.id == k && d.isEscape) with
    | none => rfl
    | some d => simp [hn d (List.mem_of_find?_eq_some hf)]

/-- **A resident's check on the base-only domain.** With no rung at the node, a resident's check over records `R` is
`Assembly.checkAt`'s, whatever its class, at the node's authorized set and registered claw-backs. -/
theorem candOk_bare {cfg : Cfg} {st : State} {T : LTrace} {i : Nat} {c : Cand}
    (hn : ∀ d ∈ (st.sw.fed.worlds i).node.cands, d.above = []) (hc : c ∈ (st.sw.fed.worlds i).node.cands) :
    candOk cfg st T i c = match st.sw.obs i with
      | none => false
      | some b => Assembly.checkAt cfg.asm (Sweep.authorizedAt st.sw (sweepT T) i)
          (Assembly.clawTxsAt st.sw (sweepT T) i) (st.sw.fed.worlds i).node (heldAt cfg st T i) b c := by
  unfold candOk
  cases st.sw.obs i with
  | none => rfl
  | some b =>
    simp only
    cases he : c.isEscape
    · rfl
    · simp only [if_true]
      have hca := hn c hc
      rw [Assembly.rungCheck_base cfg.asm (readAt st T i c) (Assembly.clawTxsAt st.sw (sweepT T) i) b c _
        (readAt_bare hn hca) he]
      have hl : c.ladder = [⟨c.tx, c.baseSig⟩] := by simp [Cand.ladder, hca]
      unfold finalAt
      rw [hl, finalize_single]
      have hq : Authority.quorum cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t c.tx (heldAt cfg st T i) =
          Sweep.possessed cfg.asm.pre.sweep (st.sw.fed.worlds i).node.t (heldAt cfg st T i) c := rfl
      cases hck : Assembly.checkAt cfg.asm (readAt st T i c).A (Assembly.clawTxsAt st.sw (sweepT T) i)
        (readAt st T i c).reg (heldAt cfg st T i) b c
      · simp [A_readAt, reg_readAt] at hck ⊢; simp [hck]
      · have hp : Authority.quorum cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t c.tx
            (heldAt cfg st T i) = true := by
          simp only [Assembly.checkAt, Bool.and_eq_true] at hck
          exact hck.1.1.1
        simp only [hp, if_true, beq_self_eq_true, Bool.true_and]
        rw [← hck]; rfl

theorem all_congr {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ c ∈ l, f c = g c) → l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, all_congr fun c hc => h c (List.mem_cons_of_mem _ hc)]

/-- **The guard on the base-only domain.** With no rung at the node and the same members in the variant-bound
possession as in `Federation.held` (compatible accepted metadata), the guard is `Assembly.assemblyOk`. -/
@[req "SPN-39"]
theorem guard_bare {cfg : Cfg} {st : State} {T : LTrace} (s : Sweep.Step)
    (hn : ∀ i, ∀ d ∈ (st.sw.fed.worlds i).node.cands, d.above = [])
    (hR : ∀ i x, x ∈ heldAt cfg st T i ↔ x ∈ Federation.held i (Sweep.fedTrace (sweepT T)) st.sw.fed) :
    guard cfg st T s = Assembly.assemblyOk cfg.asm st.sw (sweepT T) s := by
  cases s with
  | fed s =>
    cases s with
    | process i env e =>
      cases e with
      | packageAccepted cid =>
        simp only [guard, Assembly.assemblyOk, Assembly.guardOk]
        apply all_congr
        intro c hc
        rw [candOk_bare (hn i) hc]
        unfold Assembly.checkOf
        cases st.sw.obs i with
        | none => rfl
        | some b =>
          simp only
          congr 1
          cases h1 : Assembly.checkAt cfg.asm (Sweep.authorizedAt st.sw (sweepT T) i)
              (Assembly.clawTxsAt st.sw (sweepT T) i) (st.sw.fed.worlds i).node (heldAt cfg st T i) b c <;>
            cases h2 : Assembly.checkAt cfg.asm (Sweep.authorizedAt st.sw (sweepT T) i)
              (Assembly.clawTxsAt st.sw (sweepT T) i) (st.sw.fed.worlds i).node
              (Federation.held i (Sweep.fedTrace (sweepT T)) st.sw.fed) b c
          · rfl
          · rw [checkAt_mono (fun x hx => (hR i x).2 hx) h2] at h1; cases h1
          · rw [checkAt_mono (fun x hx => (hR i x).1 hx) h1] at h2; cases h2
          · rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- No node retains a rung at any state of a history. -/
def NoRungs (T : LTrace) : Prop := ∀ p ∈ T, ∀ i, ∀ c ∈ (p.1.sw.fed.worlds i).node.cands, c.above = []

/-- With no rung at the node and none in its history, the variant-bound possession is within `Federation.held`. -/
theorem held_bare_sub {cfg : Cfg} {st : State} {T : LTrace} {i : Nat}
    (hn : ∀ d ∈ (st.sw.fed.worlds i).node.cands, d.above = []) (hT : NoRungs T) {x : Authority.Sig}
    (hx : x ∈ heldAt cfg st T i) : x ∈ Federation.held i (Sweep.fedTrace (sweepT T)) st.sw.fed := by
  have h := VariantReceipt.held_sub hx
  rw [forget_fedL] at h
  rw [RungIngress.held_bare i _ _ hn] at h
  · exact h
  · intro a ha c hc
    obtain ⟨y, hy, he⟩ := RungIngress.project_world ha
    obtain ⟨y', hy', hyy⟩ : ∃ y' ∈ sweepT T, y.1 = y'.1.fed := by
      clear ha he
      revert hy
      generalize sweepT T = U
      intro hy
      induction U with
      | nil => cases hy
      | cons z U ih =>
        obtain ⟨zst, zs⟩ := z
        cases zs with
        | fed s =>
          simp only [Sweep.fedTrace, List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact ⟨(zst, .fed s), List.mem_cons_self, rfl⟩
          · obtain ⟨y', h1, h2⟩ := ih hy
            exact ⟨y', List.mem_cons_of_mem _ h1, h2⟩
        | chain b =>
          obtain ⟨y', h1, h2⟩ := ih hy
          exact ⟨y', List.mem_cons_of_mem _ h1, h2⟩
        | observe j b =>
          obtain ⟨y', h1, h2⟩ := ih hy
          exact ⟨y', List.mem_cons_of_mem _ h1, h2⟩
    obtain ⟨q, hq, h1, -⟩ := mem_sweepT hy'
    rw [he, hyy, ← h1] at hc
    exact hT q hq i c hc

/-- The guard implies `Assembly.assemblyOk` on the base-only domain. -/
theorem guard_bare_le {cfg : Cfg} {st : State} {T : LTrace} {s : Sweep.Step}
    (hn : ∀ i, ∀ d ∈ (st.sw.fed.worlds i).node.cands, d.above = []) (hT : NoRungs T)
    (h : guard cfg st T s = true) : Assembly.assemblyOk cfg.asm st.sw (sweepT T) s = true := by
  cases s with
  | fed s =>
    cases s with
    | process i env e =>
      cases e with
      | packageAccepted cid =>
        simp only [guard, Assembly.assemblyOk, Assembly.guardOk, List.all_eq_true, Bool.or_eq_true] at h ⊢
        intro c hc
        rcases h c hc with h | h
        · exact .inl h
        · right
          rw [candOk_bare (hn i) hc] at h
          unfold Assembly.checkOf
          cases hb : st.sw.obs i with
          | none => rw [hb] at h; cases h
          | some b =>
            rw [hb] at h
            exact checkAt_mono (fun x hx => held_bare_sub (hn i) hT hx) h
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- **The older base-only result on its restricted domain.** An execution in which no node retains a rung at any
state, the final one included, and every ladder pass lists nothing, is on its sweep trace an `Assembly.Execution` of
the same configuration's class check, so every result of `BtcPolicy.Assembly` applies to it. The variant-bound store
may hold less than `Federation.held`, never more, so no premise on the labels is needed in this direction. -/
@[req "SPN-39"]
theorem to_assembly {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) (hT : NoRungs T)
    (hlad : ∀ p ∈ T, ∀ i env, p.2.1 = .base (.fed (.process i env .ladderPass)) → env.ladder = []) :
    Assembly.Execution cfg.asm r honest (sweepT T) st.sw := by
  have hb : LadderRelease.Bare (sweepT T) := by
    clear hx hlad
    induction T with
    | nil => trivial
    | cons p T ih =>
      have hT' : NoRungs T := fun q hq => hT q (List.mem_cons_of_mem _ hq)
      obtain ⟨st₀, s, lab⟩ := p
      cases s with
      | base b =>
        rw [sweepT_base]
        exact ⟨fun i env _ c hc _ => hT _ List.mem_cons_self i c hc, ih hT'⟩
      | assemble i cid m => rw [sweepT_assemble]; exact ih hT'
      | send i env cid m => rw [sweepT_send]; exact ih hT'
  have hpre : PreRelease.Execution cfg.lc.pre r honest (sweepT T) st.sw := by
    refine RungRelease.to_pre ((LadderRelease.rung_iff hb).1 (to_ladder hx)) ?_
    intro p hp i env he
    obtain ⟨q, hq, -, h2⟩ := mem_sweepT hp
    rw [he] at h2
    exact hlad q hq i env h2
  refine Assembly.execution_iff.2 ⟨hpre, ?_⟩
  clear hpre hb hlad
  induction hx with
  | init st h => trivial
  | @next T st s lab ha hl hx ih =>
    have hT' : NoRungs T := fun q hq => hT q (List.mem_cons_of_mem _ hq)
    have hn : ∀ i, ∀ d ∈ (st.sw.fed.worlds i).node.cands, d.above = [] := hT _ List.mem_cons_self
    cases s with
    | base b =>
      rw [sweepT_base]
      simp only [admits, Bool.and_eq_true] at ha
      exact ⟨guard_bare_le hn hT' ha.2, ih hT'⟩
    | assemble i cid m => rw [sweepT_assemble]; exact ih hT'
    | send i env cid m => rw [sweepT_send]; exact ih hT'

/-! ## Running a schedule -/

/-- The label a schedule step takes after history `T`: a delivery's newest envelope, as `VariantReceipt.lift` chooses. -/
def labelFor (r : Rules) (T : LTrace) : Step → Option Nat
  | .base (.fed s) => VariantReceipt.labelFor r (VariantReceipt.forget (fedL T)) s
  | _ => none

def record (r : Rules) : LTrace → State → List Step → LTrace × State
  | T, st, [] => (T, st)
  | T, st, s :: ss => record r ((st, s, labelFor r T s) :: T) (RungAssembly.apply r st s) ss

def legal (cfg : Cfg) (r : Rules) (honest : List Nat) : LTrace → State → List Step → Bool
  | _, _, [] => true
  | T, st, s :: ss => admits cfg r honest st T s && labelOk r st T s (labelFor r T s) &&
      legal cfg r honest ((st, s, labelFor r T s) :: T) (RungAssembly.apply r st s) ss

theorem execution_of_legal {cfg : Cfg} {r : Rules} {honest : List Nat} {T : LTrace} {st : State}
    (hx : Execution cfg r honest T st) {ss : List Step} (hl : legal cfg r honest T st ss = true) :
    Execution cfg r honest (record r T st ss).1 (record r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s _ hl.1.1 hl.1.2 hx) hl.2

end BtcPolicy.ClassAssembly
