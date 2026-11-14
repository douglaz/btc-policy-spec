import BtcPolicy.ReleaseQuota
import BtcPolicy.Progress
/-! A Held quorum at a receiving node derived on the lifecycle run (`BtcPolicy.Lifecycle`, the current composed
domain) from honest releases, their delivery and the receiver's retention, under explicit conditions on service,
quota, delivery, retention and admissibility. `Ladder.common_base_fallback` takes the finalizing node's base quorum as
a premise; here a quorum is concluded, for the base or for a rung above it, and nothing here changes a definition or
adds a kernel event. The possession is the one the run reads, `ClassAssembly.heldAt`: the node's own signatures
(`RungIngress.ownSigs`) and the partials its variant-bound store kept (`VariantReceipt.kept`).

**The run.** `Possession.play` drives the lifecycle run by a schedule (`Nat → Option RungAssembly.Step`): slot `u`
offers `sched u`, which is taken, with the label `Lifecycle.record` gives it, when `Lifecycle.admits` and the label
check pass, and otherwise the slot stutters. Every slot is a `Lifecycle.Execution` (`Possession.play_execution`), and
a legal list run is the play of the schedule offering its steps in order (`Possession.play_list`,
`Possession.play_after`), so `Exhibits.Lifecycle.runAt` is a play. A slot is an opportunity for service; a bound in
slots is not a bound in seconds.

**Reaching a goal.** `Possession.reached_within`: a goal that persists across a window `[t0, t0 + B]`, service at some
slot of it, and an enabling asked only at a served slot where the goal does not hold yet, which takes the goal one slot
later, give the goal at `t0 + B + 1` (`Possession.reached_bounded` under `Progress.Profile.bounded B`). Enabling asked
across the whole window would be vacuous for a one-shot release: once the base's `released` bit is set, its release is
no longer enabled.

**Emission.** At an admitted fire pass of node `s` where `Possession.BaseReady` holds, and at an admitted ladder pass
where `Possession.RungReady` holds, every row of the rung (`Possession.rowOf`) enters the partial inventory and is
sent as an envelope labelled with the rung's user-signature hash (`Possession.emits_base`, `Possession.emits_rung`,
`Possession.emits`). The ids at `s` are distinct under `Registration.preserve` (`ReleaseQuota.ids_nodup_run`); the
rung's rows are the run's own account's (`ReleaseQuota.pass_account_life`), and the base's, under the account
(`Kernel.Env.starved`), are queued by the fire pass (`Kernel.firePass`), as stated here, or by a ladder pass whose
listing holds rung 0 (`Kernel.baseEffects`, not stated here), with `Federation.fanout`'s other inputs. Emission
persists (`Possession.emitted_step`).

**Delivery.** A delivery on the lifecycle run is admitted exactly when the receiver is honest, the row is in the
inventory and the step's chain view is read off the receiver's latest observation (`Possession.deliver_admits`); the
last is the delivery's residual environment condition. Its label check passes once the row has an envelope, and its
label is the rung's hash when every envelope of the row carries it (`Possession.deliver_label`). A delivery to a node
retaining compatible material stores the row's record (`Possession.deliver_kept`), and a kept record stays kept across
every step after which its commitment is still resident at the node (`Possession.kept_frame`).

**The quorum.** `Possession.held_quorum`: distinct keys with their records kept on every input, plus the receiver's
own signature, give the rung's transaction `DUR-28`'s quorum in the receiver's possession;
`Possession.final_of_quorum` turns that quorum, at the node's own threshold and for a rung at or below the candidate's
latch, into a finalization at or above the rung (`Ladder.finalize_highest`); the headline concludes the quorum only.

**The headline.** `Possession.possession_window`, and `Possession.possession_within` under bounded service: from a
fresh start, under `Registration.preserve`, the quorum holds at slot `t0 + B₁ + B₂ + 2`. Each of the seven conditions
is a named premise or definition:
1. compatible material: the contributors `S` are distinct keys, the receiver `j` a key outside them at an honest node;
   each contributor retains under `cid` a candidate whose rung is `g`, the same transaction and hash
   (`Possession.Ready`); every envelope of a row carries `g`'s hash (`hde`); `j` retains a candidate whose ladder finds
   `g` by its txid at every input (`Possession.Retains`). A contributor's honesty is derived from its pass's admission;
2. the candidate stays usable: at each served slot of `[t0, t0 + B₁]` where the contributor's rows are not yet
   emitted, its release conditions hold (`hpe`): not poisoned under the gate, due and authorized (`DUR-10`), for the
   base not hot;
3. the passes get service: each contributor's pass is offered within `[t0, t0 + B₁]` (`hps`);
4. quotas allow the emissions: for the base the `released` bit is clear (`ReleaseQuota.base_once`); for a rung above
   the base the run's own account (`ReleaseQuota.passAccount`) lists it;
5. delivery within the window: each row's delivery to `j` is offered within `[t0 + B₁ + 1, t0 + B₁ + 1 + B₂]` (`hds`),
   and at an offered slot where its record is not yet kept the step's chain view is read off `j`'s observation
   (`hde`); the delivery's admission and its label check are derived;
6. the receiver keeps the candidate and the partials: `Possession.Retains` at every slot of
   `[t0 + B₁ + 1, t0 + B₁ + B₂ + 2]` (`hret`);
7. the backend checks keep permitting: the pass is admitted (`hpe`, which reads `LadderRelease.withheldAt` and
   `RungRelease.listed` through `Lifecycle.admits`), the base not withheld by `DUR-21`'s verdict, the rung listed by
   the account.

**Not claimed.** No inclusion, no confirmation, no submission and no assembly: the quorum is possession, and
`Lifecycle.submitted_origin` and the backend stay as they are. No bound in seconds and no finite Lockdown latency. No
fairness is added to any safety theorem, no clock is repaired, no lock is modelled and the deadline driver is not
changed. A pass's admission is supplied, not derived. The common-base fallback on this run
(`Ladder.common_base_fallback`'s conclusion over `ClassAssembly.held_origin`) is not restated here.

**Limits.** Service: nothing need ever be served (`Progress.adversarial_starves`), eventual
service misses every finite expiry (`Progress.eventual_misses_any_expiry`), a bound says nothing about a narrower
window (`Progress.bounded_misses_narrower_window`), and service that alternates with enabling never meets it
(`Progress.service_without_stable_enabling`); the clock-induced outages are `Progress.f3_blackhole` and
`Progress.f4_every_request_refused`. Delivery: a run that never offers the delivery reaches no quorum
(`Exhibits.Possession.starved`). Retention: a receiver that prunes the candidate after the delivery loses the record and
the quorum, and one that prunes it before refuses the row (`Exhibits.Possession.lost`,
`Exhibits.Possession.lost_early`). Compatible material: a label that is not the receiver's retained hash is refused
while the row stays exposed (`Exhibits.VariantReceipt.mismatch_refused`), and the finalization then has no rung
(`Exhibits.ClassAssembly.mismatch_unassembled`). A quorum is not an inclusion: a sent transaction can stay unconfirmed
(`Exhibits.EndToEnd.sent_not_included`, and `Exhibits.Lifecycle.lifecycle_run`'s `t1`). -/

namespace BtcPolicy.Possession
open BtcPolicy.Kernel
open BtcPolicy.RungAssembly (Cfg Step)

/-! ## A schedule-driven lifecycle run -/

/-- One slot of a schedule: the offered step is taken, with the label `Lifecycle.record` gives it, when
`Lifecycle.admits` and the label check pass; otherwise, and when nothing is offered, the slot stutters. -/
def offer (cfg : Cfg) (r : Rules) (honest : List Nat) (p : Lifecycle.Trace × Lifecycle.State) :
    Option Step → Lifecycle.Trace × Lifecycle.State
  | none => p
  | some s =>
    if Lifecycle.admits cfg r honest p.2 p.1 s &&
        ClassAssembly.labelOk r p.2.cs (Lifecycle.toL p.1) s (ClassAssembly.labelFor r (Lifecycle.toL p.1) s) then
      ((p.2, s, ClassAssembly.labelFor r (Lifecycle.toL p.1) s) :: p.1, Lifecycle.apply r p.2 s)
    else p

/-- The lifecycle run a schedule drives from `st0`: slot `u` offers `sched u`. -/
def play (cfg : Cfg) (r : Rules) (honest : List Nat) (st0 : Lifecycle.State) (sched : Nat → Option Step) :
    Nat → Lifecycle.Trace × Lifecycle.State
  | 0 => ([], st0)
  | u + 1 => offer cfg r honest (play cfg r honest st0 sched u) (sched u)

theorem offer_execution {cfg : Cfg} {r : Rules} {honest : List Nat} {p : Lifecycle.Trace × Lifecycle.State}
    (hx : Lifecycle.Execution cfg r honest p.1 p.2) (o : Option Step) :
    Lifecycle.Execution cfg r honest (offer cfg r honest p o).1 (offer cfg r honest p o).2 := by
  cases o with
  | none => exact hx
  | some s =>
    by_cases h : (Lifecycle.admits cfg r honest p.2 p.1 s &&
        ClassAssembly.labelOk r p.2.cs (Lifecycle.toL p.1) s (ClassAssembly.labelFor r (Lifecycle.toL p.1) s)) = true
    · simp only [offer, if_pos h]
      simp only [Bool.and_eq_true] at h
      exact .next s _ h.1 h.2 hx
    · simp only [offer, if_neg h]
      exact hx

/-- **Every slot of a play is an execution.** From a fresh start, the history and state a schedule has reached at
every slot are a `Lifecycle.Execution`, whatever the schedule offers. -/
@[req "DUR-28"]
theorem play_execution {cfg : Cfg} {r : Rules} {honest : List Nat} {st0 : Lifecycle.State}
    {sched : Nat → Option Step} (hf : Lifecycle.Fresh honest st0) :
    ∀ u, Lifecycle.Execution cfg r honest (play cfg r honest st0 sched u).1 (play cfg r honest st0 sched u).2
  | 0 => .init _ hf
  | u + 1 => offer_execution (play_execution hf u) _

/-- A slot either stutters or takes one step at the state and history before it. -/
theorem offer_cases (cfg : Cfg) (r : Rules) (honest : List Nat) (p : Lifecycle.Trace × Lifecycle.State)
    (o : Option Step) :
    offer cfg r honest p o = p ∨ ∃ s h, offer cfg r honest p o = ((p.2, s, h) :: p.1, Lifecycle.apply r p.2 s) := by
  cases o with
  | none => exact .inl rfl
  | some s =>
    by_cases h : (Lifecycle.admits cfg r honest p.2 p.1 s &&
        ClassAssembly.labelOk r p.2.cs (Lifecycle.toL p.1) s (ClassAssembly.labelFor r (Lifecycle.toL p.1) s)) = true
    · simp only [offer, if_pos h]
      exact .inr ⟨s, _, rfl⟩
    · exact .inl (by simp only [offer, if_neg h])

theorem offer_taken {cfg : Cfg} {r : Rules} {honest : List Nat} {p : Lifecycle.Trace × Lifecycle.State} {s : Step}
    (ha : Lifecycle.admits cfg r honest p.2 p.1 s = true)
    (hl : ClassAssembly.labelOk r p.2.cs (Lifecycle.toL p.1) s (ClassAssembly.labelFor r (Lifecycle.toL p.1) s) = true) :
    offer cfg r honest p (some s) =
      ((p.2, s, ClassAssembly.labelFor r (Lifecycle.toL p.1) s) :: p.1, Lifecycle.apply r p.2 s) := by
  simp [offer, ha, hl]

theorem record_append (r : Rules) : ∀ (T : Lifecycle.Trace) (st : Lifecycle.State) (a b : List Step),
    Lifecycle.record r T st (a ++ b) =
      Lifecycle.record r (Lifecycle.record r T st a).1 (Lifecycle.record r T st a).2 b
  | _, _, [], _ => rfl
  | _, _, _ :: a, b => record_append r _ _ a b

theorem legal_append (cfg : Cfg) (r : Rules) (honest : List Nat) : ∀ (T : Lifecycle.Trace) (st : Lifecycle.State)
    (a b : List Step), Lifecycle.legal cfg r honest T st (a ++ b) =
      (Lifecycle.legal cfg r honest T st a &&
        Lifecycle.legal cfg r honest (Lifecycle.record r T st a).1 (Lifecycle.record r T st a).2 b)
  | _, _, [], _ => by simp [Lifecycle.legal, Lifecycle.record]
  | T, st, s :: a, b => by
    simp only [List.cons_append, Lifecycle.legal, Lifecycle.record, Bool.and_assoc]
    rw [legal_append cfg r honest _ _ a b]

/-- **A legal list run is a play.** The schedule that offers a list's steps in order, and nothing after them, reaches
after `n` slots the run `Lifecycle.record` makes of the list's first `n` steps. -/
@[req "DUR-28"]
theorem play_list {cfg : Cfg} {r : Rules} {honest : List Nat} {st0 : Lifecycle.State} {ss : List Step}
    (hl : Lifecycle.legal cfg r honest [] st0 ss = true) :
    ∀ n, n ≤ ss.length → play cfg r honest st0 (fun u => ss[u]?) n = Lifecycle.record r [] st0 (ss.take n)
  | 0, _ => rfl
  | n + 1, hn => by
    have hlt : n < ss.length := by omega
    have ih := play_list hl n (by omega)
    have hl' := hl
    rw [← List.take_append_drop n ss, List.drop_eq_getElem_cons hlt, legal_append] at hl'
    simp only [Lifecycle.legal, Bool.and_eq_true] at hl'
    show offer cfg r honest (play cfg r honest st0 (fun u => ss[u]?) n) ss[n]? = _
    rw [ih, List.getElem?_eq_getElem hlt, offer_taken hl'.2.1.1 hl'.2.1.2, List.take_succ_eq_append_getElem hlt,
      record_append]
    rfl

/-- Each step of a legal list run is admitted at the state and history its prefix reached. -/
theorem legal_admits {cfg : Cfg} {r : Rules} {honest : List Nat} {st0 : Lifecycle.State} {ss : List Step}
    (hl : Lifecycle.legal cfg r honest [] st0 ss = true) {n : Nat} (hn : n < ss.length) :
    Lifecycle.admits cfg r honest (Lifecycle.record r [] st0 (ss.take n)).2 (Lifecycle.record r [] st0 (ss.take n)).1
      ss[n] = true := by
  rw [← List.take_append_drop n ss, List.drop_eq_getElem_cons hn, legal_append] at hl
  simp only [Lifecycle.legal, Bool.and_eq_true] at hl
  exact hl.2.1.1

/-- A prefix of a legal list run is legal. -/
theorem legal_take {cfg : Cfg} {r : Rules} {honest : List Nat} {st0 : Lifecycle.State} {ss : List Step}
    (hl : Lifecycle.legal cfg r honest [] st0 ss = true) (n : Nat) :
    Lifecycle.legal cfg r honest [] st0 (ss.take n) = true := by
  rw [← List.take_append_drop n ss, legal_append] at hl
  simp only [Bool.and_eq_true] at hl
  exact hl.1

/-- After a list's last step its play stutters. -/
theorem play_after {cfg : Cfg} {r : Rules} {honest : List Nat} {st0 : Lifecycle.State} {ss : List Step} :
    ∀ d, play cfg r honest st0 (fun u => ss[u]?) (ss.length + d) = play cfg r honest st0 (fun u => ss[u]?) ss.length
  | 0 => rfl
  | d + 1 => by
    show offer cfg r honest (play cfg r honest st0 (fun u => ss[u]?) (ss.length + d)) ss[ss.length + d]? = _
    rw [List.getElem?_eq_none (by omega), play_after d]
    rfl

/-! ## Reaching a goal under bounded service -/

/-- **A goal reached within a window** (`DUR-28`). A goal `G` that persists across the window, a service that serves
at some slot of `[t0, t0 + B]`, and an enabling that holds at a served slot of the window where the goal has not yet
been reached and takes the goal one slot later: the goal holds at `t0 + B + 1`. The enabling is asked only where the
goal does not hold yet, which a one-shot release can meet: once the base's `released` bit is set the release is no
longer enabled, and the goal it reached persists. -/
@[req "DUR-28"]
theorem reached_within {G : Nat → Prop} {s : Progress.Service} {en : Nat → Prop} {t0 B : Nat}
    (hs : ∃ u, t0 ≤ u ∧ u ≤ t0 + B ∧ s u = true)
    (hkeep : ∀ u, t0 ≤ u → u ≤ t0 + B → G u → G (u + 1))
    (hen : ∀ u, t0 ≤ u → u ≤ t0 + B → ¬G u → s u = true → en u)
    (hgo : ∀ u, t0 ≤ u → u ≤ t0 + B → en u → s u = true → G (u + 1)) : G (t0 + B + 1) := by
  obtain ⟨u, h1, h2, hsu⟩ := hs
  have hu : G (u + 1) := by
    by_cases hg : G u
    · exact hkeep u h1 h2 hg
    · exact hgo u h1 h2 (hen u h1 h2 hg hsu) hsu
  have hd : ∀ d, u + 1 + d ≤ t0 + B + 1 → G (u + 1 + d) := by
    intro d
    induction d with
    | zero => intro _; exact hu
    | succ d ih => intro hd; exact hkeep (u + 1 + d) (by omega) (by omega) (ih (by omega))
  have := hd (t0 + B - u) (by omega)
  rwa [show u + 1 + (t0 + B - u) = t0 + B + 1 by omega] at this

/-- `Possession.reached_within` under `Progress.Profile.bounded B`, which serves within every window of `B + 1`
slots. -/
@[req "DUR-28"]
theorem reached_bounded {G : Nat → Prop} {s : Progress.Service} {en : Nat → Prop} {t0 B : Nat}
    (hs : (Progress.Profile.bounded B).Holds s)
    (hkeep : ∀ u, t0 ≤ u → u ≤ t0 + B → G u → G (u + 1))
    (hen : ∀ u, t0 ≤ u → u ≤ t0 + B → ¬G u → s u = true → en u)
    (hgo : ∀ u, t0 ≤ u → u ≤ t0 + B → en u → s u = true → G (u + 1)) : G (t0 + B + 1) :=
  reached_within (hs t0) hkeep hen hgo

/-! ## What a lifecycle history carries -/

/-- The federation history under a lifecycle history: its labelled federation steps without their labels. -/
def fedT (T : Lifecycle.Trace) : Federation.Trace := VariantReceipt.forget (ClassAssembly.fedL (Lifecycle.toL T))

/-- Node `j`'s kept records after lifecycle history `T` in state `st`: `VariantReceipt.kept` over its own labelled
history, filtered by its registry in `st`. -/
def keptAt (keys : List Nat) (T : Lifecycle.Trace) (st : Lifecycle.State) (j : Nat) : List (Nat × Authority.Sig) :=
  VariantReceipt.kept keys (VariantReceipt.lproject j (ClassAssembly.fedL (Lifecycle.toL T))) (st.cs.sw.fed.worlds j).node

/-- Signer `s`'s row for input `k` of rung `g` under commitment `cid`, as an honest release of `g` queues it. -/
def rowOf (s cid : Nat) (g : Rung) (k : Nat) : Exp :=
  { msg := sighash g.tx k, input := k, signer := s, hot := false, cid := cid }

/-- Every row of rung `g` from signer `s` under `cid` is in the partial inventory, and each was sent as an envelope
labelled with `g`'s user-signature hash. -/
def Emitted (r : Rules) (T : Lifecycle.Trace) (st : Lifecycle.State) (s cid : Nat) (g : Rung) : Prop :=
  ∀ k < g.tx.inputs.length, rowOf s cid g k ∈ st.cs.sw.fed.parts ∧
    (rowOf s cid g k, some g.userSig) ∈ VariantReceipt.envelopes r (fedT T)

theorem fed_step (r : Rules) (st : Lifecycle.State) (fs : Federation.Step) (h : Option Nat) (T : Lifecycle.Trace) :
    (Lifecycle.apply r st (.base (.fed fs))).cs.sw.fed = Federation.apply r st.cs.sw.fed fs ∧
      ClassAssembly.fedL (Lifecycle.toL ((st, .base (.fed fs), h) :: T)) =
        (st.cs.sw.fed, fs, h) :: ClassAssembly.fedL (Lifecycle.toL T) := ⟨rfl, rfl⟩

/-- A step that is not a federation step leaves the federation state and the federation history as they were. -/
theorem nonfed (r : Rules) (st : Lifecycle.State) {s : Step} (hs : ∀ fs, s ≠ .base (.fed fs)) (h : Option Nat)
    (T : Lifecycle.Trace) :
    (Lifecycle.apply r st s).cs.sw.fed = st.cs.sw.fed ∧
      ClassAssembly.fedL (Lifecycle.toL ((st, s, h) :: T)) = ClassAssembly.fedL (Lifecycle.toL T) := by
  cases s with
  | base b =>
    cases b with
    | fed fs => exact absurd rfl (hs fs)
    | chain b => exact ⟨rfl, rfl⟩
    | observe i b => exact ⟨rfl, rfl⟩
  | assemble i cid m =>
    exact ⟨congrArg (·.fed) (RungAssembly.apply_sw r st.cs (s := .assemble i cid m) (by simp)), rfl⟩
  | send i env cid m =>
    exact ⟨congrArg (·.fed) (RungAssembly.apply_sw r st.cs (s := .send i env cid m) (by simp)), rfl⟩

theorem envelopes_cons {r : Rules} {t : Federation.Trace} {z : Exp × Option Nat} (y : Federation.Fed × Federation.Step)
    (hz : z ∈ VariantReceipt.envelopes r t) : z ∈ VariantReceipt.envelopes r (y :: t) := by
  obtain ⟨g, i, env, e, hg, he⟩ := VariantReceipt.mem_envelopes.1 hz
  exact VariantReceipt.mem_envelopes.2 ⟨g, i, env, e, List.mem_cons_of_mem _ hg, he⟩

/-- **Emission persists.** The inventory and the envelopes only grow, so rows emitted stay emitted across every
step. -/
@[req "NCH-23"]
theorem emitted_step {r : Rules} {T : Lifecycle.Trace} {st : Lifecycle.State} {s cid : Nat} {g : Rung}
    (he : Emitted r T st s cid g) (x : Step) (h : Option Nat) :
    Emitted r ((st, x, h) :: T) (Lifecycle.apply r st x) s cid g := by
  intro k hk
  obtain ⟨hp, hv⟩ := he k hk
  by_cases hf : ∃ fs, x = .base (.fed fs)
  · obtain ⟨fs, rfl⟩ := hf
    rw [(fed_step r st fs h T).1]
    refine ⟨Federation.parts_grows r _ fs hp, ?_⟩
    show _ ∈ VariantReceipt.envelopes r ((st.cs.sw.fed, fs) :: fedT T)
    exact envelopes_cons _ hv
  · have hn := nonfed r st (s := x) (fun fs h' => hf ⟨fs, h'⟩) h T
    refine ⟨by rw [hn.1]; exact hp, ?_⟩
    show _ ∈ VariantReceipt.envelopes r (VariantReceipt.forget (ClassAssembly.fedL (Lifecycle.toL ((st, x, h) :: T))))
    rw [hn.2]
    exact hv

/-! ## Emission at a contributor's pass -/

theorem find_own {l : List Cand} (hn : (l.map Cand.id).Nodup) {c : Cand} (hc : c ∈ l) {p : Cand → Bool}
    (hp : p c = true) (hid : ∀ d, p d = true → d.id = c.id) : l.find? p = some c := by
  induction l with
  | nil => cases hc
  | cons d l ih =>
    obtain ⟨hnd, hns⟩ := List.nodup_cons.1 hn
    by_cases hpd : p d = true
    · rw [List.find?_cons_of_pos hpd]
      have hdc : d.id = c.id := hid d hpd
      rcases List.mem_cons.1 hc with h | h
      · rw [h]
      · exact absurd (hdc ▸ List.mem_map_of_mem h) hnd
    · rw [List.find?_cons_of_neg hpd]
      rcases List.mem_cons.1 hc with h | h
      · subst h; exact absurd hp hpd
      · exact ih hns h

/-- On a node whose ids are distinct, the retained variant of a partial under a resident's own id is that resident's
rung for it. -/
@[req "SPN-36"]
theorem variantOf_own {n : Node} (hn : (n.cands.map Cand.id).Nodup) {c : Cand} (hc : c ∈ n.cands) {m : Sighash}
    {k : Nat} {g : Rung} (hg : VariantReceipt.rungOf c m k = some g) :
    VariantReceipt.variantOf n m k c.id = some g.userSig := by
  unfold VariantReceipt.variantOf
  rw [find_own hn hc (p := fun d => d.id == c.id && (VariantReceipt.rungOf d m k).isSome) (by simp [hg])
    (fun d hd => by simp only [Bool.and_eq_true, beq_iff_eq] at hd; exact hd.1)]
  simp [hg]

theorem honest_of_process {cfg : Cfg} {r : Rules} {honest : List Nat} {st : Lifecycle.State}
    {T : Lifecycle.Trace} {s : Nat} {env : Env} {e : Event}
    (ha : Lifecycle.admits cfg r honest st T (.base (.fed (.process s env e))) = true) : s ∈ honest := by
  have h := ReleaseQuota.life_admits ha
  simp only [LadderRelease.admits, Sweep.admits, Federation.admits, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1

theorem node_id {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace} {st : Lifecycle.State}
    (hx : Lifecycle.Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) : (st.cs.sw.fed.worlds i).node.id = i :=
  Federation.node_id (VariantReceipt.to_fed (ClassAssembly.to_labelled (Lifecycle.to_classed hx))) hi

/-- What an emission at a pass needs: each row of `g` in the step's fan-out, and the sender's retained variant for it
being `g`'s hash. Then the rows are in the inventory with their envelopes after the step. -/
theorem emitted_of_fanout {r : Rules} {T : Lifecycle.Trace} {st : Lifecycle.State} {s : Nat} {env : Env} {e : Event}
    {cid : Nat} {g : Rung} (h : Option Nat)
    (hrow : ∀ k < g.tx.inputs.length, rowOf s cid g k ∈
      Federation.fanout (st.cs.sw.fed.worlds s) (step r env (st.cs.sw.fed.worlds s) e).2)
    (hvar : ∀ k < g.tx.inputs.length,
      VariantReceipt.variantOf (st.cs.sw.fed.worlds s).node (sighash g.tx k) k cid = some g.userSig) :
    Emitted r ((st, .base (.fed (.process s env e)), h) :: T) (Lifecycle.apply r st (.base (.fed (.process s env e))))
      s cid g := by
  intro k hk
  refine ⟨List.mem_append_right _ (hrow k hk), ?_⟩
  show _ ∈ VariantReceipt.emitted r (st.cs.sw.fed.worlds s) env e ++ VariantReceipt.envelopes r (fedT T)
  refine List.mem_append_left _ (List.mem_map.2 ⟨rowOf s cid g k, hrow k hk, ?_⟩)
  simp only [rowOf, hvar k hk]

/-- The release conditions of the base at a fire pass of node `s` (conditions 2, 4 and 7): the node not poisoned
under `Kernel.PoisonGate.asserted`, and a resident `c` under `cid`, not hot, due and authorized (`DUR-10`) as the
pass reads them, not withheld by `DUR-21`'s verdict, not starved by `SPN-38`'s account (`Kernel.Env.starves`; at an
admitted pass, some rung is affordable at its input count and its floor is at rung 0, `LadderRelease.starved_iff`),
its `released` bit clear; `g` is its base. -/
def BaseReady (r : Rules) (st : Lifecycle.State) (s : Nat) (env : Env) (cid : Nat) (g : Rung) : Prop :=
  (r.poison == .asserted && (st.cs.sw.fed.worlds s).node.poisoned) = false ∧
    ∃ c ∈ (st.cs.sw.fed.worlds s).node.cands, c.id = cid ∧ c.hot = false ∧
      due r env (st.cs.sw.fed.worlds s).node c = true ∧
      releaseAuthorized r (st.cs.sw.fed.worlds s).node c = true ∧
      env.withholds c = false ∧ env.starves c = false ∧ c.released = false ∧ g = ⟨c.tx, c.baseSig⟩

/-- The release conditions of rung `m + 1` at a ladder pass of node `s` (conditions 2, 4 and 7): a resident `c` under
`cid` whose account at the pass (`ReleaseQuota.passAccount`, the run's own computed release) lists `m + 1`, whose
rung `m + 1` is `g`, and whose ladder finds `g` first by `g`'s txid at each input (no earlier rung of the ladder shares its txid). -/
def RungReady (cfg : Cfg) (r : Rules) (st : Lifecycle.State) (T : Lifecycle.Trace) (m s : Nat) (env : Env)
    (cid : Nat) (g : Rung) : Prop :=
  ∃ c ∈ (st.cs.sw.fed.worlds s).node.cands, c.id = cid ∧
    m + 1 ∈ (ReleaseQuota.passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) s env c).rungs ∧
    c.above[m]? = some g ∧ ∀ k < g.tx.inputs.length, VariantReceipt.rungOf c (sighash g.tx k) k = some g

theorem fanout_head {w : World} {effs : List Effect} {x : Exp} (hx : x ∈ Federation.outbox w effs) :
    x ∈ Federation.fanout w effs :=
  List.mem_flatMap.2 ⟨x, hx, List.mem_cons_self⟩

theorem outbox_mem {w : World} {effs : List Effect} {m : Sighash} {k : Nat} {h : Bool} {cid : Nat}
    (he : Effect.queuePartial m k h cid ∈ effs) :
    ({ msg := m, input := k, signer := w.node.id, hot := h, cid := cid } : Exp) ∈ Federation.outbox w effs :=
  List.mem_filterMap.2 ⟨_, he, rfl⟩

/-- **The base's rows at a fire pass** (`DUR-21`, `NCH-23`). At an admitted fire pass of node `s` where the base's
release conditions hold for `c` (`Possession.BaseReady`), on a run whose ids stay distinct
(`Registration.preserve`, `ReleaseQuota.ids_nodup_run`), the step queues the row of every input of `c`'s base, with
the base's user-signature hash as its envelope's label. -/
@[req "DUR-21"]
theorem emits_base {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace} {st : Lifecycle.State}
    (hx : Lifecycle.Execution cfg r honest T st) (hr : r.registration = .preserve) {s : Nat} {env : Env}
    (ha : Lifecycle.admits cfg r honest st T (.base (.fed (.process s env .firePass))) = true) {cid : Nat} {g : Rung}
    (hready : BaseReady r st s env cid g) (h : Option Nat) :
    Emitted r ((st, .base (.fed (.process s env .firePass)), h) :: T)
      (Lifecycle.apply r st (.base (.fed (.process s env .firePass)))) s cid g := by
  have hs := honest_of_process ha
  have hn := ReleaseQuota.ids_nodup_run hr (Lifecycle.to_ladder hx) hs
  have hid := node_id hx hs
  obtain ⟨hp, c, hc, rfl, hhot, hdue, hauth, hw, hst, hrel, rfl⟩ := hready
  generalize hwd : st.cs.sw.fed.worlds s = w at hn hid hc hdue hauth hp
  have he : Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id ∈ (step r env w .firePass).2 := by
    show _ ∈ (firePass r env w.node).2
    unfold firePass
    rw [if_neg (by simp [hp])]
    exact List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hdue, hauth, hw, hst, hrel]⟩, rfl⟩
  have hx0 := outbox_mem (w := w) he
  have hoth : Federation.others w (Exp.mk (sighash c.tx 0) 0 w.node.id c.hot c.id) =
      ((List.range c.tx.inputs.length).drop 1).map fun k => Exp.mk (sighash c.tx k) k w.node.id c.hot c.id := by
    unfold Federation.others
    rw [find_own hn hc (p := fun d => d.id == c.id && sighash d.tx 0 == sighash c.tx 0) (by simp)
      (fun d hd => by simp only [Bool.and_eq_true, beq_iff_eq] at hd; exact hd.1)]
  refine emitted_of_fanout h (fun k hk => ?_) (fun k hk => ?_)
  · rw [hwd]
    simp only [rowOf, hid.symm, hhot.symm]
    by_cases hk0 : k = 0
    · subst hk0; exact fanout_head hx0
    · refine List.mem_flatMap.2 ⟨_, hx0, List.mem_cons_of_mem _ ?_⟩
      rw [hoth]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine List.mem_map.2 ⟨k' + 1, ?_, rfl⟩
      rw [List.mem_iff_getElem]
      refine ⟨k', by simp at hk ⊢; omega, by simp; omega⟩
  · rw [hwd]
    exact variantOf_own hn hc (by simp [VariantReceipt.rungOf, Cand.ladder])

theorem mem_rungEffects_of {c : Cand} {ms : List Nat} {m : Nat} {g : Rung} (hm : m + 1 ∈ ms)
    (hg : c.above[m]? = some g) {k : Nat} (hk : k < g.tx.inputs.length) :
    Effect.queuePartial (sighash g.tx k) k false c.id ∈ rungEffects c ms := by
  simp only [rungEffects, List.mem_flatMap]
  exact ⟨m + 1, hm, by simp [hg, hk]⟩

/-- **A rung's rows at a ladder pass** (`DUR-27`, `NCH-23`, `SPN-38`). At an admitted ladder pass of node `s` where
rung `m + 1`'s release conditions hold for `c` (`Possession.RungReady`: the run's own account lists it), on a run whose
ids stay distinct, the step queues the row of every input of `g`, with `g`'s user-signature hash as its envelope's
label. -/
@[req "DUR-27"]
theorem emits_rung {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace} {st : Lifecycle.State}
    (hx : Lifecycle.Execution cfg r honest T st) (hr : r.registration = .preserve) {s : Nat} {env : Env}
    (ha : Lifecycle.admits cfg r honest st T (.base (.fed (.process s env .ladderPass))) = true) {m cid : Nat}
    {g : Rung} (hready : RungReady cfg r st T m s env cid g) (h : Option Nat) :
    Emitted r ((st, .base (.fed (.process s env .ladderPass)), h) :: T)
      (Lifecycle.apply r st (.base (.fed (.process s env .ladderPass)))) s cid g := by
  have hs := honest_of_process ha
  have hn := ReleaseQuota.ids_nodup_run hr (Lifecycle.to_ladder hx) hs
  have hid := node_id hx hs
  have heff := (ReleaseQuota.pass_account_life ha).2
  obtain ⟨c, hc, rfl, hm, hg, hrung⟩ := hready
  refine emitted_of_fanout h (fun k hk => ?_) (fun k hk => variantOf_own hn hc (hrung k hk))
  have he : Effect.queuePartial (sighash g.tx k) k false c.id ∈
      (step r env (st.cs.sw.fed.worlds s) .ladderPass).2 := by
    rw [heff]
    exact List.mem_flatMap.2 ⟨c, hc, List.mem_append_right _ (mem_rungEffects_of hm hg hk)⟩
  have hx0 := outbox_mem (w := st.cs.sw.fed.worlds s) he
  rw [hid] at hx0
  exact fanout_head hx0

/-! ## Delivery into possession -/

/-- **What a delivery's admission needs** (condition 5). On the lifecycle run a delivery of `x` to node `j` is
admitted exactly when `j` is honest, `x` is in the inventory and the step's chain view is read off `j`'s latest
observation (`Settlement.viewOk`), the delivery's residual environment condition. -/
@[req "NCH-24"]
theorem deliver_admits {cfg : Cfg} {r : Rules} {honest : List Nat} {st : Lifecycle.State} {T : Lifecycle.Trace}
    {j : Nat} {env : Env} {x : Exp} :
    Lifecycle.admits cfg r honest st T (.base (.fed (.deliverPartial j env x))) = true ↔
      j ∈ honest ∧ x ∈ st.cs.sw.fed.parts ∧ Settlement.viewOk st.cs.sw j env = true := by
  simp [Lifecycle.admits, ClassAssembly.admits, LadderRelease.admits, Sweep.admits, Federation.admits,
    Sweep.assemblyOk, LadderRelease.releaseOk, ClassAssembly.guard, Settlement.readOk, Federation.actor,
    Lifecycle.kernelSendOk, and_assoc]

/-- A delivery's label check passes once the partial has an envelope: the label `Lifecycle.record` gives it is its
newest envelope's. If every envelope of the partial carries the hash `lab`, that label is `some lab`. -/
@[req "NCH-24"]
theorem deliver_label {r : Rules} {st : Lifecycle.State} {T : Lifecycle.Trace} {j : Nat} {env : Env} {x : Exp}
    {lab : Nat} (he : (x, some lab) ∈ VariantReceipt.envelopes r (fedT T)) :
    ClassAssembly.labelOk r st.cs (Lifecycle.toL T) (.base (.fed (.deliverPartial j env x)))
        (ClassAssembly.labelFor r (Lifecycle.toL T) (.base (.fed (.deliverPartial j env x)))) = true ∧
      ((∀ z ∈ VariantReceipt.envelopes r (fedT T), z.1 = x → z.2 = some lab) →
        ClassAssembly.labelFor r (Lifecycle.toL T) (.base (.fed (.deliverPartial j env x))) = some lab) := by
  have hf : ∃ z, (VariantReceipt.envelopes r (fedT T)).find? (fun z => z.1 == x) = some z := by
    cases hq : (VariantReceipt.envelopes r (fedT T)).find? (fun z => z.1 == x) with
    | none => exact absurd (List.find?_eq_none.1 hq _ he) (by simp)
    | some z => exact ⟨z, rfl⟩
  obtain ⟨z, hz⟩ := hf
  have hzm := List.mem_of_find?_eq_some hz
  have hzx : z.1 = x := by simpa using List.find?_some hz
  have hl : ClassAssembly.labelFor r (Lifecycle.toL T) (.base (.fed (.deliverPartial j env x))) = z.2 := by
    show ((VariantReceipt.envelopes r (fedT T)).find? fun z => z.1 == x).bind (·.2) = _
    rw [hz]; rfl
  refine ⟨?_, fun hu => by rw [hl]; exact hu z hzm hzx⟩
  rw [hl]
  show ((VariantReceipt.envelopes r (fedT T)).contains (x, z.2) || _) = true
  obtain ⟨z1, z2⟩ := z
  simp only at hzx
  subst hzx
  simp [hzm]

/-- **A delivery stores a compatible partial** (`NCH-24`). At node `j`'s delivery of `x` with label `h`, when `j`
retains a resident `cj` under `x`'s commitment whose ladder finds a rung `g'` by `x`'s message at `x`'s input, the
input in range, the label `g'`'s hash on an Escape-role `cj`, and the signer one of the store's keys, the record of
`x` is kept after the step. -/
@[req "NCH-24"]
theorem deliver_kept {keys : List Nat} {r : Rules} {st : Lifecycle.State} {T : Lifecycle.Trace} {j : Nat} {env : Env}
    {x : Exp} {h : Option Nat} {cj : Cand} {g' : Rung} (hcj : cj ∈ (st.cs.sw.fed.worlds j).node.cands)
    (hid : cj.id = x.cid) (hg : VariantReceipt.rungOf cj x.msg x.input = some g')
    (hk : x.input < g'.tx.inputs.length) (hh : cj.isEscape = true → h = some g'.userSig) (hkey : x.signer ∈ keys) :
    (x.cid, Authority.sig x) ∈ keptAt keys ((st, .base (.fed (.deliverPartial j env x)), h) :: T)
      (Lifecycle.apply r st (.base (.fed (.deliverPartial j env x)))) j := by
  have hs : VariantReceipt.storable keys (st.cs.sw.fed.worlds j).node x.msg x.input x.signer x.cid h = true :=
    VariantReceipt.storable_iff.2 ⟨hkey, cj, hcj, hid, g', hg, hk, hh⟩
  have hw : (Lifecycle.apply r st (.base (.fed (.deliverPartial j env x)))).cs.sw.fed.worlds j =
      (step r env (st.cs.sw.fed.worlds j) (.receivePartial x.msg x.input x.signer x.cid)).1 := by
    show (Federation.apply r st.cs.sw.fed (.deliverPartial j env x)).worlds j = _
    rw [Federation.apply_of_actor r _ _ rfl j, if_pos rfl]
  unfold keptAt
  rw [hw, (fed_step r st _ h T).2]
  simp only [VariantReceipt.lproject, Federation.actor, if_true, VariantReceipt.kept, VariantReceipt.addNew,
    VariantReceipt.arrival, hs, List.mem_filter, List.mem_append]
  refine ⟨?_, ?_⟩
  · by_cases hin : (x.cid, Authority.sig x) ∈ VariantReceipt.kept keys
        (VariantReceipt.lproject j (ClassAssembly.fedL (Lifecycle.toL T))) (st.cs.sw.fed.worlds j).node
    · exact .inl hin
    · exact .inr ⟨List.mem_singleton_self _, by simpa using hin⟩
  · simp only [step, VariantReceipt.resident_receive]
    exact List.any_eq_true.2 ⟨cj, hcj, by simp [hid]⟩

/-- **A kept record stays kept while its commitment stays resident** (condition 6). Across any lifecycle step after
which node `j` still has a resident under the record's commitment, the record stays among `j`'s kept records: steps
of other nodes, steps that are not the federation's and rung steps leave `j`'s labelled history and world as they
were, and `j`'s own frames keep what was kept and filter by residency after the frame. -/
@[req "NCH-25"]
theorem kept_frame {keys : List Nat} {r : Rules} {st : Lifecycle.State} {T : Lifecycle.Trace} {j : Nat}
    {p : Nat × Authority.Sig} (hp : p ∈ keptAt keys T st j) (x : Step) (h : Option Nat)
    (hres : ((Lifecycle.apply r st x).cs.sw.fed.worlds j).node.cands.any (·.id == p.1) = true) :
    p ∈ keptAt keys ((st, x, h) :: T) (Lifecycle.apply r st x) j := by
  unfold keptAt at hp ⊢
  by_cases hf : ∃ fs, x = .base (.fed fs)
  · obtain ⟨fs, rfl⟩ := hf
    rw [(fed_step r st fs h T).2]
    rw [(fed_step r st fs h T).1] at hres ⊢
    cases hact : Federation.actor fs with
    | none =>
      rw [Federation.apply_no_actor r _ fs hact j]
      simpa only [VariantReceipt.lproject, hact] using hp
    | some a =>
      obtain ⟨i, env, e⟩ := a
      by_cases hij : i = j
      · subst hij
        simp only [VariantReceipt.lproject, hact, if_true, VariantReceipt.kept, VariantReceipt.addNew,
          List.mem_filter, List.mem_append]
        exact ⟨.inl hp, hres⟩
      · rw [Federation.apply_of_actor r _ fs hact j, if_neg (Ne.symm hij)]
        simpa only [VariantReceipt.lproject, hact, hij, if_false] using hp
  · have hn := nonfed r st (s := x) (fun fs h' => hf ⟨fs, h'⟩) h T
    rw [hn.1, hn.2]
    exact hp

/-! ## The quorum -/

/-- `DUR-28`'s count over records: distinct keys, at least `t` of them, each with its record on every input of `X`,
give `X` the quorum. -/
@[req "DUR-28"]
theorem quorum_of_records {keys : List Nat} {t : Nat} {X : Tx} {R : List Authority.Sig} {S : List Nat}
    (hX : X.inputs ≠ []) (hnd : S.Nodup) (hk : ∀ s ∈ S, s ∈ keys) (ht : t ≤ S.length)
    (hR : ∀ s ∈ S, ∀ k < X.inputs.length, ({ msg := sighash X k, input := k, signer := s } : Authority.Sig) ∈ R) :
    Authority.quorum keys t X R = true := by
  unfold Authority.quorum
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨hX, fun k hkl => Nat.le_trans ht (length_le_of_nodup_subset hnd fun s hs => ?_)⟩
  exact Authority.mem_signers.2 ⟨hk s hs, hR s hs k hkl⟩

/-- **The Held quorum at the receiver** (`DUR-28`). On a lifecycle execution, at honest node `j`, one of the keys,
with a resident whose ladder holds `g`: if every contributor in `S` (distinct keys, `j` not among them, `t` at most
their count plus one) has the record of its row of `g` kept at `j` on every input, then `g`'s transaction has the
quorum in `j`'s variant-bound possession, `j`'s own signature counted. -/
@[req "DUR-28"]
theorem held_quorum {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace} {st : Lifecycle.State}
    (hx : Lifecycle.Execution cfg r honest T st) {j cid t : Nat} {g : Rung} {S : List Nat} (hj : j ∈ honest)
    (hjk : j ∈ cfg.lc.pre.sweep.keys) (hjS : j ∉ S) (hnd : S.Nodup) (hk : ∀ s ∈ S, s ∈ cfg.lc.pre.sweep.keys)
    (ht : t ≤ S.length + 1) (hX : g.tx.inputs ≠ [])
    (hown : ∃ c ∈ (st.cs.sw.fed.worlds j).node.cands, g ∈ c.ladder)
    (hkept : ∀ s ∈ S, ∀ k < g.tx.inputs.length,
      (cid, Authority.sig (rowOf s cid g k)) ∈ keptAt cfg.lc.pre.sweep.keys T st j) :
    Authority.quorum cfg.lc.pre.sweep.keys t g.tx (ClassAssembly.heldAt cfg st.cs (Lifecycle.toL T) j) = true := by
  have hid := node_id hx hj
  obtain ⟨c, hc, hg⟩ := hown
  refine quorum_of_records hX (List.nodup_cons.2 ⟨hjS, hnd⟩)
    (fun s hs => (List.mem_cons.1 hs).elim (fun e => e ▸ hjk) (hk s)) (by simpa using ht) ?_
  intro s hs k hkl
  unfold ClassAssembly.heldAt VariantReceipt.held
  rcases List.mem_cons.1 hs with rfl | hs
  · refine List.mem_append_left _ ?_
    unfold RungIngress.ownSigs
    refine List.mem_flatMap.2 ⟨c, hc, List.mem_flatMap.2 ⟨g, hg, List.mem_map.2 ⟨k, List.mem_range.2 hkl, ?_⟩⟩⟩
    rw [hid]
  · exact List.mem_append_right _ (List.mem_map.2 ⟨_, hkept s hs k hkl, rfl⟩)

/-- **The finalization reaches the rung** (`DUR-28`, `Ladder.finalize_highest`). When rung `m` of `c`'s ladder, at
or below its latch, has the quorum at node `i`'s threshold in `i`'s possession, `i`'s finalization for `c` is a rung
at or above `m`. -/
@[req "DUR-28"]
theorem final_of_quorum {cfg : Cfg} {st : RungAssembly.State} {T : ClassAssembly.LTrace} {i m : Nat} {c : Cand}
    {g : Rung} (hg : c.ladder[m]? = some g) (hm : m ≤ c.track.latch)
    (hq : Authority.quorum cfg.lc.pre.sweep.keys (st.sw.fed.worlds i).node.t g.tx
      (ClassAssembly.heldAt cfg st T i) = true) :
    ∃ m', ClassAssembly.finalAt cfg st T i c = some m' ∧ m ≤ m' :=
  Ladder.finalize_highest _ _ _ _ _ _ hm (by simp only [Ladder.quorumAt, hg]; exact hq)

/-! ## The schedule, the passes and the deliveries -/

/-- Which pass releases the rung, as this module states it: the base at a fire pass, or rung `m + 1` at a ladder
pass. A ladder pass whose listing holds rung 0 may release the base instead (`Kernel.baseEffects`); this module
does not state that path. -/
inductive Pass
  | base
  | rung (m : Nat)
  deriving DecidableEq, Repr

/-- The kernel event of a pass. -/
def Pass.event : Pass → Event
  | .base => .firePass
  | .rung _ => .ladderPass

/-- A pass's release conditions: `Possession.BaseReady` for the base, `Possession.RungReady` for a rung. -/
def Ready (cfg : Cfg) (r : Rules) : Pass → Lifecycle.State → Lifecycle.Trace → Nat → Env → Nat → Rung → Prop
  | .base, st, _, s, env, cid, g => BaseReady r st s env cid g
  | .rung m, st, T, s, env, cid, g => RungReady cfg r st T m s env cid g

/-- **Emission at a pass** (`NCH-23`), either kind. -/
@[req "NCH-23"]
theorem emits {cfg : Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace} {st : Lifecycle.State}
    (hx : Lifecycle.Execution cfg r honest T st) (hr : r.registration = .preserve) {p : Pass} {s : Nat} {env : Env}
    (ha : Lifecycle.admits cfg r honest st T (.base (.fed (.process s env p.event))) = true) {cid : Nat} {g : Rung}
    (hready : Ready cfg r p st T s env cid g) (h : Option Nat) :
    Emitted r ((st, .base (.fed (.process s env p.event)), h) :: T)
      (Lifecycle.apply r st (.base (.fed (.process s env p.event)))) s cid g := by
  cases p with
  | base => exact emits_base hx hr ha hready h
  | rung m => exact emits_rung hx hr ha hready h

/-- Whether a slot offers node `s`'s pass of kind `e`, at any environment. -/
def passOf (s : Nat) (e : Event) : Option Step → Bool
  | some (.base (.fed (.process i _ e'))) => i == s && e' == e
  | _ => false

theorem passOf_some {s : Nat} {e : Event} {o : Option Step} (h : passOf s e o = true) :
    ∃ env, o = some (.base (.fed (.process s env e))) := by
  match o, h with
  | some (.base (.fed (.process i env e'))), h =>
    simp only [passOf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨env, rfl⟩

/-- Whether a slot offers the delivery of `x` to node `j`, at any environment. -/
def deliverOf (j : Nat) (x : Exp) : Option Step → Bool
  | some (.base (.fed (.deliverPartial i _ y))) => i == j && y == x
  | _ => false

theorem deliverOf_some {j : Nat} {x : Exp} {o : Option Step} (h : deliverOf j x o = true) :
    ∃ env, o = some (.base (.fed (.deliverPartial j env x))) := by
  rcases o with _ | ⟨b | _ | _⟩
  · simp [deliverOf] at h
  · rcases b with fs | _ | _
    · cases fs
      case deliverPartial i env y =>
        simp only [deliverOf, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨env, rfl⟩
      all_goals simp [deliverOf] at h
    all_goals simp [deliverOf] at h
  all_goals simp [deliverOf] at h

/-- Node `j` retains, under commitment `cid`, a resident whose ladder finds `g` by `g`'s txid at every input of `g`:
compatible material, the same transaction and the same user-signature hash. -/
def Retains (st : Lifecycle.State) (j cid : Nat) (g : Rung) : Prop :=
  ∃ cj ∈ (st.cs.sw.fed.worlds j).node.cands, cj.id = cid ∧
    ∀ k < g.tx.inputs.length, VariantReceipt.rungOf cj (sighash g.tx k) k = some g

theorem play_succ (cfg : Cfg) (r : Rules) (honest : List Nat) (st0 : Lifecycle.State) (sched : Nat → Option Step)
    (u : Nat) : play cfg r honest st0 sched (u + 1) = offer cfg r honest (play cfg r honest st0 sched u) (sched u) :=
  rfl

theorem emitted_offer {cfg : Cfg} {r : Rules} {honest : List Nat} {p : Lifecycle.Trace × Lifecycle.State}
    {s cid : Nat} {g : Rung} (he : Emitted r p.1 p.2 s cid g) (o : Option Step) :
    Emitted r (offer cfg r honest p o).1 (offer cfg r honest p o).2 s cid g := by
  rcases offer_cases cfg r honest p o with e | ⟨x, h, e⟩ <;> rw [e]
  · exact he
  · exact emitted_step he x h

/-- **Possession within a window** (`DUR-28`, `NCH-23`, `NCH-24`, `SPN-38`). On the lifecycle run a schedule drives
from a fresh start, under `Registration.preserve`: let the contributors `S` be distinct keys, `j` a key outside them
at an honest node, and `t` at most their count plus one, `j`'s own signature counted. If

* each contributor's pass of kind `p` is offered at some slot of `[t0, t0 + B₁]` (condition 3), and at every offered
  slot of that window where its rows are not yet emitted the pass is admitted and its release conditions hold
  (`Possession.Ready`: conditions 2, 4 and 7, and on the contributor's side condition 1);
* each row of each contributor's release of `g` is offered for delivery to `j` at some slot of
  `[t0 + B₁ + 1, t0 + B₁ + 1 + B₂]`, and at every offered slot of that window where its record is not yet kept, the
  step's chain view is read off `j`'s observation and every envelope of the row carries `g`'s hash (condition 5, and
  condition 1 on the wire);
* `j` retains compatible material under `cid` at every slot of `[t0 + B₁ + 1, t0 + B₁ + B₂ + 2]` (condition 6);

then at slot `t0 + B₁ + B₂ + 2` rung `g`'s transaction has the quorum in `j`'s variant-bound possession. The
contributors' honesty, the deliveries' admission and labels and the receiver's own signature are derived. -/
@[req "DUR-28"]
theorem possession_window {cfg : Cfg} {r : Rules} {honest : List Nat} {st0 : Lifecycle.State}
    {sched : Nat → Option Step} (hf : Lifecycle.Fresh honest st0) (hr : r.registration = .preserve)
    {S : List Nat} {j cid t : Nat} {g : Rung} (p : Pass) {t0 B₁ B₂ : Nat}
    (hj : j ∈ honest) (hjk : j ∈ cfg.lc.pre.sweep.keys) (hjS : j ∉ S) (hnd : S.Nodup)
    (hk : ∀ s ∈ S, s ∈ cfg.lc.pre.sweep.keys) (ht : t ≤ S.length + 1) (hX : g.tx.inputs ≠ [])
    (hps : ∀ s ∈ S, ∃ u, t0 ≤ u ∧ u ≤ t0 + B₁ ∧ passOf s p.event (sched u) = true)
    (hpe : ∀ s ∈ S, ∀ u, t0 ≤ u → u ≤ t0 + B₁ →
      ¬Emitted r (play cfg r honest st0 sched u).1 (play cfg r honest st0 sched u).2 s cid g →
      ∀ env, sched u = some (.base (.fed (.process s env p.event))) →
        Lifecycle.admits cfg r honest (play cfg r honest st0 sched u).2 (play cfg r honest st0 sched u).1
            (.base (.fed (.process s env p.event))) = true ∧
          Ready cfg r p (play cfg r honest st0 sched u).2 (play cfg r honest st0 sched u).1 s env cid g)
    (hds : ∀ s ∈ S, ∀ k < g.tx.inputs.length,
      ∃ u, t0 + B₁ + 1 ≤ u ∧ u ≤ t0 + B₁ + 1 + B₂ ∧ deliverOf j (rowOf s cid g k) (sched u) = true)
    (hde : ∀ s ∈ S, ∀ k < g.tx.inputs.length, ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + 1 + B₂ →
      (cid, Authority.sig (rowOf s cid g k)) ∉
        keptAt cfg.lc.pre.sweep.keys (play cfg r honest st0 sched u).1 (play cfg r honest st0 sched u).2 j →
      ∀ env, sched u = some (.base (.fed (.deliverPartial j env (rowOf s cid g k)))) →
        Settlement.viewOk (play cfg r honest st0 sched u).2.cs.sw j env = true ∧
          ∀ z ∈ VariantReceipt.envelopes r (fedT (play cfg r honest st0 sched u).1),
            z.1 = rowOf s cid g k → z.2 = some g.userSig)
    (hret : ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + B₂ + 2 → Retains (play cfg r honest st0 sched u).2 j cid g) :
    Authority.quorum cfg.lc.pre.sweep.keys t g.tx
      (ClassAssembly.heldAt cfg (play cfg r honest st0 sched (t0 + B₁ + B₂ + 2)).2.cs
        (Lifecycle.toL (play cfg r honest st0 sched (t0 + B₁ + B₂ + 2)).1) j) = true := by
  let P := play cfg r honest st0 sched
  have hx : ∀ u, Lifecycle.Execution cfg r honest (P u).1 (P u).2 := play_execution hf
  -- the passes
  have hem : ∀ s ∈ S, Emitted r (P (t0 + B₁ + 1)).1 (P (t0 + B₁ + 1)).2 s cid g := by
    intro s hs
    refine reached_within (G := fun u => Emitted r (P u).1 (P u).2 s cid g)
      (s := fun u => passOf s p.event (sched u))
      (en := fun u => ∀ env, sched u = some (.base (.fed (.process s env p.event))) →
        Lifecycle.admits cfg r honest (P u).2 (P u).1 (.base (.fed (.process s env p.event))) = true ∧
          Ready cfg r p (P u).2 (P u).1 s env cid g)
      (hps s hs) (fun u _ _ he => emitted_offer he _) (fun u h1 h2 hn _ => hpe s hs u h1 h2 hn)
      (fun u _ _ hen hsu => ?_)
    obtain ⟨env, he⟩ := passOf_some hsu
    obtain ⟨ha, hready⟩ := hen env he
    show Emitted r (offer cfg r honest (P u) (sched u)).1 (offer cfg r honest (P u) (sched u)).2 s cid g
    rw [he, offer_taken ha rfl]
    exact emits (hx u) hr ha hready _
  have hem' : ∀ s ∈ S, ∀ d, Emitted r (P (t0 + B₁ + 1 + d)).1 (P (t0 + B₁ + 1 + d)).2 s cid g := by
    intro s hs d
    induction d with
    | zero => exact hem s hs
    | succ d ih => exact emitted_offer ih _
  -- the deliveries
  have hkept : ∀ s ∈ S, ∀ k < g.tx.inputs.length,
      (cid, Authority.sig (rowOf s cid g k)) ∈ keptAt cfg.lc.pre.sweep.keys (P (t0 + B₁ + B₂ + 2)).1
        (P (t0 + B₁ + B₂ + 2)).2 j := by
    intro s hs k hkl
    have hE : t0 + B₁ + B₂ + 2 = t0 + B₁ + 1 + B₂ + 1 := by omega
    rw [hE]
    refine reached_within (G := fun u => (cid, Authority.sig (rowOf s cid g k)) ∈
        keptAt cfg.lc.pre.sweep.keys (P u).1 (P u).2 j)
      (s := fun u => deliverOf j (rowOf s cid g k) (sched u))
      (en := fun u => ∀ env, sched u = some (.base (.fed (.deliverPartial j env (rowOf s cid g k)))) →
        Settlement.viewOk (P u).2.cs.sw j env = true ∧
          ∀ z ∈ VariantReceipt.envelopes r (fedT (P u).1), z.1 = rowOf s cid g k → z.2 = some g.userSig)
      (hds s hs k hkl) (fun u h1 h2 hg => ?_)
      (fun u h1 h2 hn _ => hde s hs k hkl u h1 h2 hn) (fun u h1 h2 hen hsu => ?_)
    · show _ ∈ keptAt _ (offer cfg r honest (P u) (sched u)).1 (offer cfg r honest (P u) (sched u)).2 j
      obtain ⟨cj, hcj, hid, -⟩ := hret (u + 1) (by omega) (by omega)
      rcases offer_cases cfg r honest (P u) (sched u) with e | ⟨x, h, e⟩
      · rw [e]; exact hg
      · have hres : ((Lifecycle.apply r (P u).2 x).cs.sw.fed.worlds j).node.cands.any (·.id == cid) = true := by
          have : (P (u + 1)).2 = Lifecycle.apply r (P u).2 x := by
            show (offer cfg r honest (P u) (sched u)).2 = _
            rw [e]
          rw [← this]
          exact List.any_eq_true.2 ⟨cj, hcj, by simp [hid]⟩
        rw [e]
        exact kept_frame hg x h hres
    · obtain ⟨env, he⟩ := deliverOf_some hsu
      obtain ⟨hview, hu⟩ := hen env he
      obtain ⟨hpart, henv⟩ := hem' s hs (u - (t0 + B₁ + 1)) k hkl
      rw [show t0 + B₁ + 1 + (u - (t0 + B₁ + 1)) = u by omega] at hpart henv
      have ha : Lifecycle.admits cfg r honest (P u).2 (P u).1 (.base (.fed (.deliverPartial j env (rowOf s cid g k))))
          = true := deliver_admits.2 ⟨hj, hpart, hview⟩
      obtain ⟨hl, hlab⟩ := deliver_label (st := (P u).2) (j := j) (env := env) henv
      obtain ⟨cj, hcj, hid, hrung⟩ := hret u (by omega) (by omega)
      show _ ∈ keptAt _ (offer cfg r honest (P u) (sched u)).1 (offer cfg r honest (P u) (sched u)).2 j
      rw [he, offer_taken ha hl]
      exact deliver_kept hcj hid (hrung k hkl) hkl (fun _ => hlab hu) (hk s hs)
  -- the quorum
  obtain ⟨cj, hcj, -, hrung⟩ := hret (t0 + B₁ + B₂ + 2) (by omega) (Nat.le_refl _)
  have h0 : 0 < g.tx.inputs.length := List.length_pos_iff.2 hX
  exact held_quorum (hx _) hj hjk hjS hnd hk ht hX
    ⟨cj, hcj, (VariantReceipt.rungOf_some (hrung 0 h0)).1⟩ hkept

/-- **Possession under bounded service** (`DUR-28`). `Possession.possession_window` with each pass and each delivery
served under `Progress.Profile.bounded`: every window of `B₁ + 1` slots offers each contributor's pass, and every window
of `B₂ + 1` slots offers each row's delivery to `j` (condition 3, and the service of condition 5). A slot is an
opportunity for service, not a second: the bound is in slots. -/
@[req "DUR-28"]
theorem possession_within {cfg : Cfg} {r : Rules} {honest : List Nat} {st0 : Lifecycle.State}
    {sched : Nat → Option Step} (hf : Lifecycle.Fresh honest st0) (hr : r.registration = .preserve)
    {S : List Nat} {j cid t : Nat} {g : Rung} (p : Pass) {t0 B₁ B₂ : Nat}
    (hj : j ∈ honest) (hjk : j ∈ cfg.lc.pre.sweep.keys) (hjS : j ∉ S) (hnd : S.Nodup)
    (hk : ∀ s ∈ S, s ∈ cfg.lc.pre.sweep.keys) (ht : t ≤ S.length + 1) (hX : g.tx.inputs ≠ [])
    (hps : ∀ s ∈ S, (Progress.Profile.bounded B₁).Holds fun u => passOf s p.event (sched u))
    (hpe : ∀ s ∈ S, ∀ u, t0 ≤ u → u ≤ t0 + B₁ →
      ¬Emitted r (play cfg r honest st0 sched u).1 (play cfg r honest st0 sched u).2 s cid g →
      ∀ env, sched u = some (.base (.fed (.process s env p.event))) →
        Lifecycle.admits cfg r honest (play cfg r honest st0 sched u).2 (play cfg r honest st0 sched u).1
            (.base (.fed (.process s env p.event))) = true ∧
          Ready cfg r p (play cfg r honest st0 sched u).2 (play cfg r honest st0 sched u).1 s env cid g)
    (hds : ∀ s ∈ S, ∀ k < g.tx.inputs.length,
      (Progress.Profile.bounded B₂).Holds fun u => deliverOf j (rowOf s cid g k) (sched u))
    (hde : ∀ s ∈ S, ∀ k < g.tx.inputs.length, ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + 1 + B₂ →
      (cid, Authority.sig (rowOf s cid g k)) ∉
        keptAt cfg.lc.pre.sweep.keys (play cfg r honest st0 sched u).1 (play cfg r honest st0 sched u).2 j →
      ∀ env, sched u = some (.base (.fed (.deliverPartial j env (rowOf s cid g k)))) →
        Settlement.viewOk (play cfg r honest st0 sched u).2.cs.sw j env = true ∧
          ∀ z ∈ VariantReceipt.envelopes r (fedT (play cfg r honest st0 sched u).1),
            z.1 = rowOf s cid g k → z.2 = some g.userSig)
    (hret : ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + B₂ + 2 → Retains (play cfg r honest st0 sched u).2 j cid g) :
    Authority.quorum cfg.lc.pre.sweep.keys t g.tx
      (ClassAssembly.heldAt cfg (play cfg r honest st0 sched (t0 + B₁ + B₂ + 2)).2.cs
        (Lifecycle.toL (play cfg r honest st0 sched (t0 + B₁ + B₂ + 2)).1) j) = true :=
  possession_window hf hr p hj hjk hjS hnd hk ht hX (fun s hs => hps s hs t0) hpe
    (fun s hs k hk => hds s hs k hk (t0 + B₁ + 1)) hde hret

end BtcPolicy.Possession
