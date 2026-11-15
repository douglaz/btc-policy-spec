import BtcPolicy.ReleaseQuota
import BtcPolicy.ReceiptLifecycle
import BtcPolicy.LadderShape
import BtcPolicy.AcceptedSet
/-! `SPN-38`'s release accounting on the expiry-aware lifecycle layer (`ReceiptLifecycle.Execution`), evicting
deliveries included: research task `bps-xmq1.5`. A layer beside the existing definitions: no definition or theorem
statement changes, and no kernel event is added.

**Why a port.** `ReleaseQuota`'s run results (`ReleaseQuota.starved_silent`, `no_relist`, `base_once_paths`) are
stated over `LadderRelease.Execution`, which `ReceiptLifecycle.to_lifecycle` reaches only on a run whose deliveries
never evict. Here they are restated over every run of the layer. The per-pass results need only the layer's admission:
a fire or ladder pass the layer admits is `LadderRelease`-admitted at the layer's sweep state and history
(`ReceiptQuota.pass_admits`), and moves the federation as `Federation.apply` does (`ReceiptQuota.pass_fed`). The
results across a lifetime re-run their induction on the layer, with `ReceiptLifecycle.ids_nodup` for the one record
per id and `ReceiptQuota.layer_origin` for each step: a step either keeps a record whole, a delivery included, or is a
kernel step of the record's node.

**Results.**
* One pass: `ReceiptQuota.pass_quota_layer` (`ReleaseQuota.pass_quota` on the layer) and
  `ReceiptQuota.starved_silent_layer` (`ReleaseQuota.starved_silent`).
* The equal-input premise: on a run whose federation steps are `LadderShape.CheckedTrace`'s, every resident record
  of an honest node has its rungs above the base spend as many inputs as its base (`ReceiptQuota.inputs_inv`), so
  `ReceiptQuota.pass_count_checked` is `ReleaseQuota.pass_count` with no such premise.
* A lifetime: `ReceiptQuota.no_relist_layer`, `ReceiptQuota.base_once_layer`, and their composition
  `ReceiptQuota.fire_no_base_slot`: after a fire pass sends the base, the floor is past rung 0 for the rest of the
  lifetime, so no ladder pass of it lists rung 0.
* A delivery: `ReceiptQuota.redelivery_layer` (no row is added and every record is kept with its release state) and
  `ReceiptQuota.evict_removes` (an evicting delivery only removes records).
* A birth: `ReceiptQuota.birth_fresh` (a record born at a step starts at the empty release state).

**Outside.** A new lifetime's base, queued again, and the earlier lifetime's rows that stay in the partial inventory
are exhibited, not stated. No shared rate limit across lifetimes is modelled: `Cursor.rungBudget` is a function of
the quota alone, and an eviction or refund resets no other budget. -/

namespace BtcPolicy.ReceiptQuota

open BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.FedSilence
open BtcPolicy.ReleaseQuota (passAccount consumed under baseOut)

/-! ## The layer's sweep history -/

/-- The sweep history the layer's admission reads (`ReceiptLifecycle.admits`). -/
abbrev sweepT (g : Guards) (lcfg : Config) (T : ReceiptLifecycle.Trace) : Sweep.Trace :=
  ClassAssembly.sweepT (ReceiptLifecycle.cls g lcfg T)

/-- The federation steps under a history of the layer, each acceptance as the Hot budget leaves it. -/
abbrev fedT (g : Guards) (lcfg : Config) (T : ReceiptLifecycle.Trace) : Federation.Trace :=
  Sweep.fedTrace (sweepT g lcfg T)

/-! ## One step of the layer -/

/-- A federation step other than a delivered partial moves the federation as `Federation.apply` of the step the Hot
budget leaves. -/
theorem fed_step (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (s : Federation.Step) (h : Option Nat) (hs : ∀ j env x, s ≠ .deliverPartial j env x) :
    (ReceiptLifecycle.apply keys g lcfg r st (.base (.fed s)) h).ls.cs.sw.fed =
      Federation.apply r st.ls.cs.sw.fed (kernelStep g lcfg st.lf s) := by
  have he : ReceiptExpiry.evictsAt st.lf s = false := by
    cases s with
    | deliverPartial j env x => exact absurd rfl (hs j env x)
    | _ => rfl
  exact (congrArg LFed.fed (ReceiptExpiry.xapply_unevicted g lcfg r st.lf s he)).trans (lapply_fed g lcfg r st.lf s)

/-- **A pass on the layer is the federation's** (`SPN-38`). A fire or ladder pass, which the Hot budget leaves as it
is, moves the federation as `Federation.apply`. -/
theorem pass_fed (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State) (i : Nat)
    (env : Env) {e : Event} (he : e = .firePass ∨ e = .ladderPass) (h : Option Nat) :
    (ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.process i env e))) h).ls.cs.sw.fed =
      Federation.apply r st.ls.cs.sw.fed (.process i env e) := by
  rcases he with rfl | rfl <;> exact fed_step keys g lcfg r st _ h (fun _ _ _ hc => by cases hc)

/-- **A pass the layer admits is `LadderRelease`'s** (`SPN-38`). At a fire or ladder pass the layer admits, the
release conjunct holds at the layer's sweep state and history: the Hot budget maps only acceptances. -/
theorem pass_admits {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st : ReceiptLifecycle.State} {T : ReceiptLifecycle.Trace} {i : Nat} {env : Env} {e : Event}
    (he : e = .firePass ∨ e = .ladderPass)
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process i env e))) = true) :
    LadderRelease.admits cfg.lc honest st.ls.cs.sw (sweepT g lcfg T) (.fed (.process i env e)) = true := by
  rcases he with rfl | rfl <;>
  · simp only [ReceiptLifecycle.admits, ReceiptLifecycle.mapStep, Bool.and_eq_true] at ha
    exact ha.1.1.1

/-- The receiving node after a delivered partial: `ReceiptExpiry.receive`, an eviction or `Kernel.receivePartial`. -/
theorem deliver_node (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (j : Nat) (env : Env) (x : Exp) (h : Option Nat) :
    ((ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x))) h).ls.cs.sw.fed.worlds j).node =
      ReceiptExpiry.receive env (st.ls.cs.sw.fed.worlds j).node x.msg x.input x.signer x.cid := by
  show ((ReceiptExpiry.xapply g lcfg r st.lf (.deliverPartial j env x)).fed.worlds j).node = _
  simp [ReceiptExpiry.xapply, ReceiptExpiry.sysRecv, ReceiptExpiry.wstep, LFed.sys, ReceiptLifecycle.State.lf]

/-- **A delivery keeps every record whole** (`NCH-24`, `SPN-38`). Each record of each node after a delivered
partial, evicting or not, is one before it with the same registration-owned fields, release state and `released`
bit: an eviction only removes records, and a stored partial changes only the record's held signers. -/
theorem deliver_from (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (j : Nat) (env : Env) (x : Exp) (h : Option Nat) (i : Nat) {c : Cand}
    (hc : c ∈ ((ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x))) h).ls.cs.sw.fed.worlds
      i).node.cands) :
    ∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands,
      Retained.reg d = Retained.reg c ∧ d.track = c.track ∧ d.released = c.released := by
  by_cases hij : i = j
  · subst hij
    rw [deliver_node] at hc
    unfold ReceiptExpiry.receive at hc
    split at hc
    · exact ⟨c, (ReceiptExpiry.mem_evict.1 hc).1, rfl, rfl, rfl⟩
    · rw [ReceiptExpiry.receivePartial_stored] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      refine ⟨d, hd, ?_⟩
      unfold ReceiptExpiry.stored
      split <;> exact ⟨rfl, rfl, rfl⟩
  · have hc' : c ∈ ((ReceiptExpiry.xapply g lcfg r st.lf (.deliverPartial j env x)).fed.worlds i).node.cands := hc
    rw [ReceiptLifecycle.xapply_other g lcfg r st.lf _ rfl hij] at hc'
    exact ⟨c, hc', rfl, rfl, rfl⟩

/-- **Where a record after a step of the layer comes from.** It is a record before it, kept whole (its
registration-owned fields, release state and `released` bit), or the step is a kernel step of the record's node,
whose world after it is `Kernel.step`'s. -/
theorem layer_origin (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (s : RungAssembly.Step) (h : Option Nat) (i : Nat) {c : Cand}
    (hc : c ∈ ((ReceiptLifecycle.apply keys g lcfg r st s h).ls.cs.sw.fed.worlds i).node.cands) :
    (∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands,
        Retained.reg d = Retained.reg c ∧ d.track = c.track ∧ d.released = c.released) ∨
      ∃ s₀ env e, s = .base (.fed s₀) ∧ Federation.actor (kernelStep g lcfg st.lf s₀) = some (i, env, e) ∧
        (ReceiptLifecycle.apply keys g lcfg r st s h).ls.cs.sw.fed.worlds i =
          (step r env (st.ls.cs.sw.fed.worlds i) e).1 := by
  have keep (hc : c ∈ (st.ls.cs.sw.fed.worlds i).node.cands) :
      ∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands,
        Retained.reg d = Retained.reg c ∧ d.track = c.track ∧ d.released = c.released := ⟨c, hc, rfl, rfl, rfl⟩
  cases s with
  | assemble j cid m => rw [ReceiptLifecycle.fed_nonfed (by simp)] at hc; exact .inl (keep hc)
  | send j env cid m => rw [ReceiptLifecycle.fed_nonfed (by simp)] at hc; exact .inl (keep hc)
  | base b =>
    cases b with
    | chain b => rw [ReceiptLifecycle.fed_nonfed (by simp)] at hc; exact .inl (keep hc)
    | observe j b => rw [ReceiptLifecycle.fed_nonfed (by simp)] at hc; exact .inl (keep hc)
    | fed s₀ =>
      by_cases hd : ∃ j env x, s₀ = .deliverPartial j env x
      · obtain ⟨j, env, x, rfl⟩ := hd
        exact .inl (deliver_from keys g lcfg r st j env x h i hc)
      · have hf := fed_step keys g lcfg r st s₀ h fun j env x he => hd ⟨j, env, x, he⟩
        cases hact : Federation.actor (kernelStep g lcfg st.lf s₀) with
        | none =>
          rw [hf, Federation.apply_no_actor r _ _ hact i] at hc
          exact .inl (keep hc)
        | some a =>
          obtain ⟨j, env, e⟩ := a
          by_cases hij : i = j
          · subst hij
            refine .inr ⟨s₀, env, e, rfl, hact, ?_⟩
            rw [hf, Federation.apply_of_actor r _ _ hact i, if_pos rfl]
          · rw [hf, Federation.apply_of_actor r _ _ hact i, if_neg hij] at hc
            exact .inl (keep hc)

/-- A step of the layer, at node `i`: each record after it is one before it with the same id whose `released` bit it
does not clear, or the step births a record under its id there (`ReceiptLifecycle.born`). -/
theorem released_step (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (s : RungAssembly.Step) (h : Option Nat) (i : Nat) {c : Cand}
    (hc : c ∈ ((ReceiptLifecycle.apply keys g lcfg r st s h).ls.cs.sw.fed.worlds i).node.cands) :
    (∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands, d.id = c.id ∧ (d.released = true → c.released = true)) ∨
      ReceiptLifecycle.born keys g lcfg r st s h i c.id = true := by
  rcases layer_origin keys g lcfg r st s h i hc with ⟨d, hd, h1, -, h3⟩ | ⟨s₀, env, e, rfl, -, hw⟩
  · exact .inl ⟨d, hd, (Retained.reg_eq h1).1, fun hr => by rw [← h3]; exact hr⟩
  · rw [hw] at hc
    rcases ReleaseQuota.step_released r env _ e hc with hk | hk
    · exact .inl hk
    · refine .inr ?_
      unfold ReceiptLifecycle.born ReceiptLifecycle.fcount
      rw [hw]
      exact decide_eq_true hk

/-- One step of a lifetime on the layer, with the `released` bit: under `Registration.preserve`, at an admitted step
that births no record under `k` at honest node `i`, each record under `k` after it is one before it with the same
registration-owned fields, a floor no lower and its `released` bit kept. -/
theorem step_desc {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hr : r.registration = .preserve)
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {s : RungAssembly.Step}
    {h : Option Nat} (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T s = true) {k : Nat}
    (hb : ReceiptLifecycle.born cfg.lc.pre.sweep.keys g lcfg r st s h i k = false) :
    ∀ c ∈ ((ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st s h).ls.cs.sw.fed.worlds i).node.cands,
      c.id = k → ∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands, Retained.reg d = Retained.reg c ∧
        d.track.floor ≤ c.track.floor ∧ (d.released = true → c.released = true) := by
  intro c hc hk
  obtain ⟨d, hd, h1, h2, -⟩ := ReceiptLifecycle.life_step hx hi ha hb c hc hk
  rcases released_step cfg.lc.pre.sweep.keys g lcfg r st s h i hc with ⟨d', hd', h1', h2'⟩ | hb'
  · have hdd : d' = d :=
      ReceiptLifecycle.eq_of_nodup_id (ReceiptLifecycle.ids_nodup hr hx hi) hd' hd
        (by rw [h1', (Retained.reg_eq h1).1])
    subst hdd
    exact ⟨d', hd', h1, h2, h2'⟩
  · rw [hk, hb] at hb'
    cases hb'

/-- **From a step of the layer onward** (`DUR-27`, `SPN-38`), `ReleaseQuota.lifetime_after` on the layer, with the
`released` bit. Under `Registration.preserve`, the step was admitted at its own state and history, which the run
reached, and over the steps after it, none of which births a record under `k` at honest node `i`, every record under
`k` at the end descends from one right after the step with the same registration-owned fields, a floor no higher and
a `released` bit no later set. Evicting deliveries are among those steps. -/
@[req "DUR-27"]
theorem life_after {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hr : r.registration = .preserve)
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    {T₁ T₂ : ReceiptLifecycle.Trace} {st₁ : ReceiptLifecycle.State} {s₁ : RungAssembly.Step} {h₁ : Option Nat}
    (hT : T = T₂ ++ (st₁, s₁, h₁) :: T₁)
    (hb : ∀ y ∈ T₂, ReceiptLifecycle.born cfg.lc.pre.sweep.keys g lcfg r y.1 y.2.1 y.2.2 i k = false) :
    ReceiptLifecycle.Execution cfg g lcfg r honest T₁ st₁ ∧
      ReceiptLifecycle.admits cfg g lcfg r honest st₁ T₁ s₁ = true ∧
      ∀ c ∈ (st.ls.cs.sw.fed.worlds i).node.cands, c.id = k →
        ∃ d ∈ ((ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st₁ s₁ h₁).ls.cs.sw.fed.worlds i).node.cands,
          Retained.reg d = Retained.reg c ∧ d.track.floor ≤ c.track.floor ∧
            (d.released = true → c.released = true) := by
  induction hx generalizing T₂ with
  | init st h => cases T₂ <;> simp at hT
  | @next T st s lab ha hl hx' ih =>
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hT
      exact ⟨hx', ha, fun c hc _ => ⟨c, hc, rfl, Nat.le_refl _, id⟩⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      obtain ⟨hx₁, ha₁, hanc⟩ := ih hT (fun z hz => hb z (List.mem_cons_of_mem _ hz))
      refine ⟨hx₁, ha₁, fun c hc hk => ?_⟩
      obtain ⟨d, hd, h1, h2, h3⟩ := step_desc hr hx' hi ha (hb _ List.mem_cons_self) c hc hk
      obtain ⟨e, he, g1, g2, g3⟩ := hanc d hd (by rw [(Retained.reg_eq h1).1]; exact hk)
      exact ⟨e, he, g1.trans h1, Nat.le_trans g2 h2, fun hr => h3 (g3 hr)⟩

/-! ## One pass on the layer -/

/-- **One ladder pass for one record, whole, on the layer** (`SPN-38`, `NCH-23`): `ReleaseQuota.pass_quota` at a
ladder pass `ReceiptLifecycle.Execution` admits, evicting deliveries before it included, for an Escape-role record
whose variants above the base spend as many inputs as its base (the premise `hin`, derived on a checked run by
`ReceiptQuota.inputs_inv`). -/
@[req "SPN-38"]
theorem pass_quota_layer {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st : ReceiptLifecycle.State} {T : ReceiptLifecycle.Trace} {i : Nat} {env : Env}
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process i env .ladderPass))) = true)
    (h : Option Nat) {c : Cand} (hc : c ∈ (st.ls.cs.sw.fed.worlds i).node.cands) (hesc : c.isEscape = true)
    (hin : ∀ x ∈ c.above, x.tx.inputs.length = c.tx.inputs.length) :
    ((passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).rungs ≠ [] →
      ∃ b k F U, (RungRelease.readAt st.ls.cs.sw (sweepT g lcfg T) i c).ob = some b ∧
        (Ladder.attempt cfg.lc.pre (RungRelease.readAt st.ls.cs.sw (sweepT g lcfg T) i c) b c
          c.track.latch).verdict = .release k ∧
        (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).interval = some (F, U) ∧
        F = max c.track.floor (Ladder.lowest (Ladder.attempt cfg.lc.pre
          (RungRelease.readAt st.ls.cs.sw (sweepT g lcfg T) i c) b c c.track.latch)) ∧
        F ≤ U ∧ U ≤ k ∧
        (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).rungs =
          Ladder.relOf (Ladder.attempt cfg.lc.pre
            (RungRelease.readAt st.ls.cs.sw (sweepT g lcfg T) i c) b c c.track.latch) F U ∧
        (step r env (st.ls.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id) =
          baseEffects c (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).rungs ++
            rungEffects c (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).rungs ∧
        ((step r env (st.ls.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id)).length ≤
          consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) * c.tx.inputs.length ∧
        consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) * c.tx.inputs.length ≤
          Cursor.rungBudget cfg.lc.quota ∧
        consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) = U + 1 - F ∧
        consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) ≤
          Cursor.affordableRungs cfg.lc.quota c.tx.inputs.length ∧
        (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).track = { latch := k, floor := U + 1 } ∧
        { c with track := { latch := k, floor := U + 1 },
                 released := c.released ||
                   (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).rungs.contains 0 } ∈
          ((ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed (.process i env .ladderPass)))
            h).ls.cs.sw.fed.worlds i).node.cands) ∧
    ((passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).rungs = [] →
      (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).track = c.track ∧
        consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) = 0 ∧
        (step r env (st.ls.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id) = [] ∧
        c ∈ ((ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed (.process i env .ladderPass)))
          h).ls.cs.sw.fed.worlds i).node.cands) := by
  rw [pass_fed cfg.lc.pre.sweep.keys g lcfg r st i env (.inr rfl) h]
  exact ReleaseQuota.pass_quota (LadderRelease.admits_ladder (pass_admits (.inr rfl) ha)) r hc hesc hin

/-- `ReleaseQuota.starved_silent` at a node whose ids are distinct, at a pass `LadderRelease.admits` admits. -/
theorem starved_nodup {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    {i : Nat} (hn : ((st.fed.worlds i).node.cands.map Cand.id).Nodup) {env : Env} {e : Event}
    (he : e = .firePass ∨ e = .ladderPass)
    (ha : LadderRelease.admits lc honest st T (.fed (.process i env e)) = true)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands)
    (hz : Cursor.affordableRungs lc.quota c.tx.inputs.length = 0) :
    (step r env (st.fed.worlds i) e).2.filter (under c.id) = [] ∧
      ∀ d ∈ ((Federation.apply r st.fed (.process i env e)).worlds i).node.cands, d.id = c.id →
        d.released = c.released ∧ d.track = c.track := by
  rcases he with rfl | rfl
  · have hst := (LadderRelease.fire_env ha).2
    have hsc : c.released = false → env.starves c = true := by
      intro hrel
      have hm : c.id ∈ LadderRelease.starvedAt lc st T i :=
        (LadderRelease.starved_iff lc st T i c.id).2 ⟨c, hc, rfl, hrel, .inl hz⟩
      rw [← hst] at hm
      simp [Env.starves, hm]
    refine ⟨?_, fun d hd hdc => ?_⟩
    · apply List.filter_eq_nil_iff.2
      intro eff heff hu
      obtain ⟨d, hd, -, -, -, hds, hdr, rfl⟩ := firePass_effect_fed r env _ heff
      have hdk : d.id = c.id := by simpa [under] using hu
      rw [Kernel.eq_of_mem_ids_nodup hn hd hc hdk] at hds hdr
      rw [hsc hdr] at hds
      cases hds
    · change d ∈ ((Federation.apply r st.fed (.process i env .firePass)).worlds i).node.cands at hd
      rw [Federation.apply_of_actor r _ _ rfl i, if_pos rfl] at hd
      change d ∈ (firePass r env (st.fed.worlds i).node).1.cands at hd
      unfold firePass at hd
      split at hd
      · rw [Kernel.eq_of_mem_ids_nodup hn hd hc hdc]
        exact ⟨rfl, rfl⟩
      · obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
        have hid : d₀.id = c.id := by split at hdc <;> (try split at hdc) <;> simpa using hdc
        rw [Kernel.eq_of_mem_ids_nodup hn hd₀ hc hid]
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          cases hrel : c.released
          · rw [hsc hrel] at hcond
            cases hcond.2
          · simp [hrel]
        · exact ⟨rfl, rfl⟩
  · have har := LadderRelease.admits_ladder ha
    have hq : passAccount lc r st T i env c = ReleaseQuota.quiet c.track := ReleaseQuota.pass_zero lc r st T i env hz
    refine ⟨?_, fun d hd hdc => ?_⟩
    · rw [(ReleaseQuota.pass_account har r).2, ReleaseQuota.filter_flatMap]
      simp only [ReleaseQuota.effects_under]
      refine (ReleaseQuota.flatMap_own hn hc _).trans ?_
      simp [hq, ReleaseQuota.quiet, baseEffects, rungEffects]
    · rw [(ReleaseQuota.pass_account har r).1] at hd
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hd
      have hcc : c' = c := Kernel.eq_of_mem_ids_nodup hn hc' hc hdc
      subst hcc
      simp [hq, ReleaseQuota.quiet]

/-- **A starved record is silent on the layer** (`SPN-38`: "If `affordable_rungs = 0`, release nothing and advance no
release bookkeeping on this pass"), `ReleaseQuota.starved_silent` over `ReceiptLifecycle.Execution`. Under
`Registration.preserve`, at an admitted fire or ladder pass of honest node `i`, a resident record with no rung
affordable at its input count gets no row under its commitment, its base included, and the record under its id after
the pass keeps its `released` bit and its release state. -/
@[req "SPN-38"]
theorem starved_silent_layer {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hr : r.registration = .preserve)
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {env : Env} {e : Event}
    (he : e = .firePass ∨ e = .ladderPass)
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process i env e))) = true) (h : Option Nat)
    {c : Cand} (hc : c ∈ (st.ls.cs.sw.fed.worlds i).node.cands)
    (hz : Cursor.affordableRungs cfg.lc.quota c.tx.inputs.length = 0) :
    (step r env (st.ls.cs.sw.fed.worlds i) e).2.filter (under c.id) = [] ∧
      ∀ d ∈ ((ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed (.process i env e)))
          h).ls.cs.sw.fed.worlds i).node.cands, d.id = c.id →
        d.released = c.released ∧ d.track = c.track := by
  rw [pass_fed cfg.lc.pre.sweep.keys g lcfg r st i env he h]
  exact starved_nodup (ReceiptLifecycle.ids_nodup hr hx hi) he (pass_admits he ha) hc hz

/-! ## The equal-input premise on a checked run -/

theorem fedT_mono (g : Guards) (lcfg : Config) (y : ReceiptLifecycle.State × RungAssembly.Step × Option Nat)
    (T : ReceiptLifecycle.Trace) : ∀ z ∈ fedT g lcfg T, z ∈ fedT g lcfg (y :: T) := by
  obtain ⟨st, s, h⟩ := y
  intro z hz
  cases s with
  | base b =>
    cases b with
    | fed s₀ => exact List.mem_cons_of_mem _ hz
    | chain b => exact hz
    | observe j b => exact hz
  | assemble j cid m => exact hz
  | send j env cid m => exact hz

theorem checked_tail {ctx : Ingress.Ctx} {t n : Nat} {g : Guards} {lcfg : Config}
    {y : ReceiptLifecycle.State × RungAssembly.Step × Option Nat} {T : ReceiptLifecycle.Trace}
    (hC : LadderShape.CheckedTrace ctx t n (fedT g lcfg (y :: T))) : LadderShape.CheckedTrace ctx t n (fedT g lcfg T) :=
  ⟨fun z hz => hC.1 z (fedT_mono g lcfg y T z hz), fun z hz => hC.2 z (fedT_mono g lcfg y T z hz)⟩

theorem actor_process {s : Federation.Step} {i : Nat} {env : Env} {e : Event}
    (h : Federation.actor s = some (i, env, e)) (hr : ∀ cid sn, e ≠ .receipt cid sn)
    (hp : ∀ m inp sg cid, e ≠ .receivePartial m inp sg cid) : s = .process i env e := by
  cases s with
  | process i' env' e' =>
    simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | deliver i' env' m =>
    simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq] at h
    exact absurd h.2.2.symm (hr _ _)
  | deliverPartial i' env' x =>
    simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq] at h
    exact absurd h.2.2.symm (hp _ _ _ _)
  | _ => simp [Federation.actor] at h

/-- **The equal-input premise, derived** (`CHN-16`, `SPN-38`). On a run of the layer whose federation steps are
checked by `LadderShape.check` (`LadderShape.CheckedTrace`: every acceptance is that check's verdict on some request,
every claw-back `Ingress.checkClawback`'s candidate), every resident record of an honest node has each rung above its
base spending as many inputs as its base. An accepted Escape's rungs spend the base's inputs in order
(`LadderShape.accepted_inputs`); an accepted spend and a checked claw-back carry no rung; every other step, an
evicting delivery included, keeps a record's base and rungs. -/
@[req "CHN-16"]
theorem inputs_inv {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st)
    {ctx : Ingress.Ctx} {t n : Nat} (hC : LadderShape.CheckedTrace ctx t n (fedT g lcfg T)) {i : Nat}
    (hi : i ∈ honest) :
    ∀ c ∈ (st.ls.cs.sw.fed.worlds i).node.cands, ∀ x ∈ c.above, x.tx.inputs.length = c.tx.inputs.length := by
  induction hx with
  | init st h =>
    intro c hc
    rw [(h.1.1.1.1.2.2 i hi).2.2.2.1] at hc
    cases hc
  | @next T st s lab ha hl hx ih =>
    have ih' := ih (checked_tail hC)
    intro c hc x hxc
    have old : ∀ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands, d.tx = c.tx → d.above = c.above →
        x.tx.inputs.length = c.tx.inputs.length := by
      intro d hd h1 h2
      rw [← h1]
      exact ih' d hd x (by rw [h2]; exact hxc)
    rcases layer_origin cfg.lc.pre.sweep.keys g lcfg r st s lab i hc with
      ⟨d, hd, h1, -, -⟩ | ⟨s₀, env, e, rfl, hact, hw⟩
    · simp only [Retained.reg, Prod.mk.injEq] at h1
      exact old d hd h1.2.2.1 h1.2.2.2.2
    · rw [hw] at hc
      have hC' : LadderShape.CheckedTrace ctx t n
          ((st.ls.cs.sw.fed, kernelStep g lcfg st.lf s₀) :: fedT g lcfg T) := hC
      rcases AcceptedSet.key_origin r env _ e hc with
        ⟨d, hd, hk⟩ | ⟨cid, dd, E, sp, es, rfl, hk⟩ | ⟨y, rfl, hk⟩
      · simp only [AcceptedSet.key, Prod.mk.injEq] at hk
        exact old d hd hk.1 hk.2
      · obtain ⟨q, hq⟩ := hC'.1 _ (List.mem_cons_self ..) i env cid dd E sp es
          (actor_process hact (fun _ _ he => by cases he) (fun _ _ _ _ he => by cases he))
        simp only [AcceptedSet.key, Prod.mk.injEq] at hk
        rcases hk with ⟨-, hka⟩ | ⟨hkt, hka⟩
        · rw [hka, (RungIngress.accepted_rungs (LadderShape.check_refines hq)).2.2.1] at hxc
          cases hxc
        · rw [hka] at hxc
          rw [LadderShape.accepted_inputs hq x (List.mem_cons_of_mem _ hxc), hkt]
      · obtain ⟨q, hq⟩ := hC'.2 _ (List.mem_cons_self ..) i env y
          (actor_process hact (fun _ _ he => by cases he) (fun _ _ _ _ he => by cases he))
        simp only [AcceptedSet.key, Prod.mk.injEq] at hk
        rw [hk.2, Ingress.checkClawback_above hq] at hxc
        cases hxc

/-- **The count on a checked run of the layer** (`SPN-38`, `NCH-23`): `ReleaseQuota.pass_count` at a ladder pass the
layer admits, with the equal-input premise derived (`ReceiptQuota.inputs_inv`) rather than taken. -/
@[req "SPN-38"]
theorem pass_count_checked {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st)
    {ctx : Ingress.Ctx} {t n : Nat} (hC : LadderShape.CheckedTrace ctx t n (fedT g lcfg T)) {i : Nat}
    (hi : i ∈ honest) {env : Env}
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process i env .ladderPass))) = true)
    {c : Cand} (hc : c ∈ (st.ls.cs.sw.fed.worlds i).node.cands) (hesc : c.isEscape = true) :
    ((step r env (st.ls.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id)).length ≤
        consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) * c.tx.inputs.length ∧
      consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) * c.tx.inputs.length ≤
        Cursor.rungBudget cfg.lc.quota ∧
      (0 ∈ (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c).rungs →
        ((step r env (st.ls.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id)).length ≤
          (consumed (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env c) - 1) * c.tx.inputs.length + 1) :=
  ReleaseQuota.pass_count (LadderRelease.admits_ladder (pass_admits (.inr rfl) ha)) r hc hesc
    (inputs_inv hx hC hi c hc)

/-! ## Across a lifetime on the layer -/

/-- **No rung is listed twice in a lifetime on the layer** (`SPN-38`: "rungs already queued … MUST NOT be re-queued
merely to reconstruct the prefix"), `ReleaseQuota.no_relist` over `ReceiptLifecycle.Execution`. Under
`Registration.preserve`, take a ladder pass of honest node `i` and the steps after it, none of which births a record
under `k` at `i`, evicting deliveries included. A rung listed for the record under `k` at that pass is below every
rung the account at the state reached lists for a record under `k`, at any environment. -/
@[req "SPN-38"]
theorem no_relist_layer {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hr : r.registration = .preserve)
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    {T₁ T₂ : ReceiptLifecycle.Trace} {st₁ : ReceiptLifecycle.State} {env₁ : Env} {h₁ : Option Nat}
    (hT : T = T₂ ++ (st₁, .base (.fed (.process i env₁ .ladderPass)), h₁) :: T₁)
    (hb : ∀ y ∈ T₂, ReceiptLifecycle.born cfg.lc.pre.sweep.keys g lcfg r y.1 y.2.1 y.2.2 i k = false)
    {c₁ : Cand} (hc₁ : c₁ ∈ (st₁.ls.cs.sw.fed.worlds i).node.cands) (hk₁ : c₁.id = k) {m : Nat}
    (hm : m ∈ (passAccount cfg.lc r st₁.ls.cs.sw (sweepT g lcfg T₁) i env₁ c₁).rungs)
    {env₂ : Env} {c₂ : Cand} (hc₂ : c₂ ∈ (st.ls.cs.sw.fed.worlds i).node.cands) (hk₂ : c₂.id = k) {m' : Nat}
    (hm' : m' ∈ (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env₂ c₂).rungs) : m < m' := by
  obtain ⟨hx₁, ha₁, hanc⟩ := life_after hr hx hi hT hb
  obtain ⟨d, hd, hreg, hfl, -⟩ := hanc c₂ hc₂ hk₂
  have hcands := (ReleaseQuota.pass_account (LadderRelease.admits_ladder (pass_admits (.inr rfl) ha₁)) r).1
  rw [pass_fed cfg.lc.pre.sweep.keys g lcfg r st₁ i env₁ (.inr rfl) h₁, hcands] at hd
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hd
  have hid : c₀.id = c₁.id := by
    have := (Retained.reg_eq hreg).1
    simp only at this
    rw [this, hk₂, hk₁]
  have hc01 : c₀ = c₁ := Kernel.eq_of_mem_ids_nodup (ReceiptLifecycle.ids_nodup hr hx₁ hi) hc₀ hc₁ hid
  subst hc01
  have h1 := (ReleaseQuota.pass_mem hm).2
  have h2 := (ReleaseQuota.pass_mem hm').1
  simp only at hfl
  omega

/-- With every record under `k` released, a step queues no base row under `k`. -/
theorem baseOut_released (r : Rules) (env : Env) (n : Node) (k : Nat) (e : Event)
    (h : ∀ c ∈ n.cands, c.id = k → c.released = true) : baseOut r env n k e = [] := by
  cases e with
  | firePass =>
    show (firePass r env n).2.filter (under k) = []
    apply List.filter_eq_nil_iff.2
    intro eff he hu
    obtain ⟨c, hc, -, -, -, hc0, rfl⟩ := firePass_effect r env n he
    have hck : c.id = k := by simpa [under] using hu
    rw [h c hc hck] at hc0
    cases hc0
  | ladderPass =>
    simp only [baseOut]
    split
    · rfl
    · apply List.flatMap_eq_nil_iff.2
      intro c hc
      obtain ⟨hc, hck⟩ := List.mem_filter.1 hc
      have := h c hc (by simpa using hck)
      simp [baseEffects, this]
  | _ => simp [baseOut]

/-- **The base at most once in a lifetime on the layer, by either path** (`SPN-36`'s `released`, `SPN-38`),
`ReleaseQuota.base_once_paths` over `ReceiptLifecycle.Execution`. Under `Registration.preserve`, once any pass of
honest node `i`, fire or ladder, queues a base row under commitment `k`, no pass of `i` after it, at any environment,
queues one, over every stretch of steps none of which births a record under `k` at `i`, evicting deliveries
included. -/
@[req "SPN-38"]
theorem base_once_layer {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hr : r.registration = .preserve)
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    {T₁ T₂ : ReceiptLifecycle.Trace} {st₁ : ReceiptLifecycle.State} {env₁ : Env} {e₁ : Event} {h₁ : Option Nat}
    (hT : T = T₂ ++ (st₁, .base (.fed (.process i env₁ e₁)), h₁) :: T₁)
    (hb : ∀ y ∈ T₂, ReceiptLifecycle.born cfg.lc.pre.sweep.keys g lcfg r y.1 y.2.1 y.2.2 i k = false)
    (h₁' : baseOut r env₁ (st₁.ls.cs.sw.fed.worlds i).node k e₁ ≠ []) (env₂ : Env) (e₂ : Event) :
    baseOut r env₂ (st.ls.cs.sw.fed.worlds i).node k e₂ = [] := by
  have he₁ : e₁ = .firePass ∨ e₁ = .ladderPass := by
    cases e₁ with
    | firePass => exact .inl rfl
    | ladderPass => exact .inr rfl
    | _ => exact (h₁' (by simp [baseOut])).elim
  obtain ⟨hx₁, -, hanc⟩ := life_after hr hx hi hT hb
  have hmark := ReleaseQuota.baseOut_marks (ReceiptLifecycle.ids_nodup hr hx₁ hi) h₁'
  apply baseOut_released
  intro c hc hck
  obtain ⟨d, hd, hreg, -, hdr⟩ := hanc c hc hck
  rw [pass_fed cfg.lc.pre.sweep.keys g lcfg r st₁ i env₁ he₁ h₁, Federation.apply_of_actor r _ _ rfl i,
    if_pos rfl] at hd
  exact hdr (hmark d hd (by rw [(Retained.reg_eq hreg).1]; exact hck))

/-- A fire pass that queues a row under commitment `k`, at a node whose ids are distinct, leaves the record under `k`
with its floor past rung 0. -/
theorem firePass_floor {r : Rules} {env : Env} {n : Node} (hn : (n.cands.map Cand.id).Nodup) {eff : Effect}
    (he : eff ∈ (firePass r env n).2) {k : Nat} (hk : under k eff = true) :
    ∀ d ∈ (firePass r env n).1.cands, d.id = k → 1 ≤ d.track.floor := by
  obtain ⟨c, hc, hdue, hauth, hw, hs, hrel, rfl⟩ := firePass_effect_fed r env n he
  have hck : c.id = k := by simpa [under] using hk
  unfold firePass at he ⊢
  split at he
  · simp at he
  · rename_i hp
    rw [if_neg hp]
    intro d hd hdk
    obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
    have hid : d₀.id = c.id := by
      rw [hck]
      split at hdk <;> (try split at hdk) <;> simpa using hdk
    have := Kernel.eq_of_mem_ids_nodup hn hd₀ hc hid
    subst this
    simp [hdue, hauth, hw, hs, hrel, Nat.le_max_right]

/-- **A fire pass that sends the base moves the floor past rung 0 for the lifetime** (`SPN-38`: "Only a pass that
released at least one rung MUST set `release_floor = U + 1`"; `SPN-36`'s `released`). Under `Registration.preserve`,
once a fire pass of honest node `i` queues a row under commitment `k`, over every later stretch of steps none of which
births a record under `k` at `i`, evicting deliveries included, every record under `k` has its floor at least 1, so no
ladder pass account of it, at any environment, lists rung 0. -/
@[req "SPN-38"]
theorem fire_no_base_slot {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hr : r.registration = .preserve)
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    {T₁ T₂ : ReceiptLifecycle.Trace} {st₁ : ReceiptLifecycle.State} {env₁ : Env} {h₁ : Option Nat}
    (hT : T = T₂ ++ (st₁, .base (.fed (.process i env₁ .firePass)), h₁) :: T₁)
    (hb : ∀ y ∈ T₂, ReceiptLifecycle.born cfg.lc.pre.sweep.keys g lcfg r y.1 y.2.1 y.2.2 i k = false)
    (h₁' : (step r env₁ (st₁.ls.cs.sw.fed.worlds i) .firePass).2.filter (under k) ≠ [])
    {c : Cand} (hc : c ∈ (st.ls.cs.sw.fed.worlds i).node.cands) (hck : c.id = k) (env₂ : Env) :
    1 ≤ c.track.floor ∧ 0 ∉ (passAccount cfg.lc r st.ls.cs.sw (sweepT g lcfg T) i env₂ c).rungs := by
  obtain ⟨hx₁, -, hanc⟩ := life_after hr hx hi hT hb
  obtain ⟨eff, hm⟩ := List.exists_mem_of_ne_nil _ h₁'
  obtain ⟨he, hu⟩ := List.mem_filter.1 hm
  have hfl := firePass_floor (ReceiptLifecycle.ids_nodup hr hx₁ hi) he hu
  obtain ⟨d, hd, hreg, hfd, -⟩ := hanc c hc hck
  rw [pass_fed cfg.lc.pre.sweep.keys g lcfg r st₁ i env₁ (.inl rfl) h₁, Federation.apply_of_actor r _ _ rfl i,
    if_pos rfl] at hd
  have h1 := hfl d hd (by rw [(Retained.reg_eq hreg).1]; exact hck)
  refine ⟨Nat.le_trans h1 hfd, fun h0 => ?_⟩
  have := (ReleaseQuota.pass_mem h0).1
  omega

/-! ## Deliveries and births -/

/-- **Redelivery is not a release on the layer** (`SPN-38`: "The cursor records that a rung has been queued for
transport, not that a peer received it"; `NCH-24`). A delivered partial, evicting or not, adds no row to the partial
inventory, and every record of every node after it is one before it with the same registration-owned fields, release
state and `released` bit. -/
@[req "SPN-38"]
theorem redelivery_layer (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (j : Nat) (env : Env) (x : Exp) (h : Option Nat) :
    (ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x))) h).ls.cs.sw.fed.parts =
        st.ls.cs.sw.fed.parts ∧
      ∀ i, ∀ c ∈ ((ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x)))
          h).ls.cs.sw.fed.worlds i).node.cands,
        ∃ d ∈ (st.ls.cs.sw.fed.worlds i).node.cands,
          Retained.reg d = Retained.reg c ∧ d.track = c.track ∧ d.released = c.released :=
  ⟨rfl, fun i _ hc => deliver_from keys g lcfg r st j env x h i hc⟩

/-- **An evicting delivery only removes records** (`NCH-24`). At a delivered partial whose receiver's lookup evicts,
every record of every node after it was resident there before it, unchanged. -/
@[req "NCH-24"]
theorem evict_removes (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (j : Nat) (env : Env) (x : Exp) (h : Option Nat)
    (he : ReceiptExpiry.evicts env (st.ls.cs.sw.fed.worlds j).node x.cid = true) (i : Nat) :
    ∀ c ∈ ((ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x)))
      h).ls.cs.sw.fed.worlds i).node.cands, c ∈ (st.ls.cs.sw.fed.worlds i).node.cands := by
  intro c hc
  by_cases hij : i = j
  · subst hij
    rw [deliver_node] at hc
    unfold ReceiptExpiry.receive at hc
    rw [if_pos he] at hc
    exact (ReceiptExpiry.mem_evict.1 hc).1
  · have hc' : c ∈ ((ReceiptExpiry.xapply g lcfg r st.lf (.deliverPartial j env x)).fed.worlds i).node.cands := hc
    rw [ReceiptLifecycle.xapply_other g lcfg r st.lf _ rfl hij] at hc'
    exact hc'

/-- **A birth starts at the fresh release state** (`SPN-38`, `DUR-27`, `SPN-32`). Under `Registration.preserve`, at
a step of a run of the layer that births a record under `k` at honest node `i`, a re-registration after an eviction
included, the record under `k` after it has the empty release state: latch 0 and floor 0. No release progress of an
earlier lifetime under the id carries over. -/
@[req "SPN-38"]
theorem birth_fresh {cfg : RungAssembly.Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    (hr : r.registration = .preserve) {T₀ : ReceiptLifecycle.Trace} {st₀ : ReceiptLifecycle.State}
    {s : RungAssembly.Step} {h : Option Nat} {st : ReceiptLifecycle.State}
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest ((st₀, s, h) :: T₀) st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    (hb : ReceiptLifecycle.born cfg.lc.pre.sweep.keys g lcfg r st₀ s h i k = true) :
    ∀ c ∈ (st.ls.cs.sw.fed.worlds i).node.cands, c.id = k → c.track = {} := by
  have hn := ReceiptLifecycle.ids_nodup hr hx hi
  cases hx with
  | next _ _ ha _ _ =>
    intro c hc hk
    rcases ReceiptLifecycle.sweep_step ha i hc with ⟨d, hd, h1, -, -⟩ | ⟨h1, -⟩
    · exfalso
      have hdk : d.id = k := by rw [(Retained.reg_eq h1).1, hk]
      have h0 : 0 < ReceiptLifecycle.fcount st₀.ls.cs.sw.fed i k := by
        unfold ReceiptLifecycle.fcount
        exact List.countP_pos_iff.2 ⟨d, hd, by simp [hdk]⟩
      have h2 : ReceiptLifecycle.fcount
          (ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st₀ s h).ls.cs.sw.fed i k ≤ 1 := by
        unfold ReceiptLifecycle.fcount
        rw [List.countP_eq_length_filter]
        exact ReleaseQuota.filter_id_length hn k
      simp only [ReceiptLifecycle.born, decide_eq_true_eq] at hb
      omega
    · exact h1

end BtcPolicy.ReceiptQuota
