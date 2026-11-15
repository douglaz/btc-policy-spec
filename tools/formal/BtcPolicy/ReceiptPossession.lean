import BtcPolicy.Possession
import BtcPolicy.ReceiptQuota
/-! `Possession.possession_window` on the expiry-aware lifecycle layer (`ReceiptLifecycle.Execution`), research task
`bps-xmq1.5`: a locally usable quorum in a receiving node's possession on the layer, `ReceiptLifecycle.heldAt` (its own
signatures and the records its store keeps, `ReceiptLifecycle.State.store`), derived from honest releases, their
delivery and the receiver's retention. A layer beside the existing definitions: no definition or theorem statement
changes, and no kernel event is added.

**The run.** `ReceiptPossession.play` drives the layer by a schedule, as `Possession.play` drives the lifecycle run:
slot `u` offers `sched u`, which is taken, with the label `ReceiptLifecycle.labelFor` gives it, when
`ReceiptLifecycle.admits` and `ReceiptLifecycle.labelOk` pass; otherwise, and when nothing is offered, the slot
stutters. Every slot is a `ReceiptLifecycle.Execution` (`ReceiptPossession.play_execution`), and a legal list run of
`ReceiptLifecycle.record` whose entries name no label is the play of the schedule offering its steps in order
(`ReceiptPossession.play_list`, `ReceiptPossession.play_after`). A slot is an opportunity for service; a bound in slots
is not a bound in seconds. Goals are reached with `Possession.reached_within`, which reads no run.

**Emission.** At a pass the layer admits, the node is honest (`ReceiptQuota.pass_admits`) and the federation moves as
`Federation.apply` (`ReceiptQuota.pass_fed`); under `Registration.preserve` its ids are distinct
(`ReceiptLifecycle.ids_nodup`). Every row of the rung (`Possession.rowOf`) then enters the partial inventory and the
layer's envelopes (`ReceiptLifecycle.State.envs`) with the rung's user-signature hash: the base at a fire pass
(`ReceiptPossession.emits_base`, under `Possession.BaseReady`), the base at a ladder pass whose account lists rung 0
(`ReceiptPossession.emits_ladder_base`, `Kernel.baseEffects`), and a rung above the base at a ladder pass whose account
lists it (`ReceiptPossession.emits_rung`, under `Possession.RungReady` over the layer's sweep history,
`ReceiptQuota.sweepT`). Emission persists (`ReceiptPossession.emitted_step`).

**Delivery, store and retention.** A delivery is admitted exactly when the receiver is honest, the row is in the
inventory and the step's chain view is read off the receiver's latest observation
(`ReceiptPossession.deliver_admits`); its label check passes once the row has an envelope, and the label is the rung's
hash when every envelope of the row carries it (`ReceiptPossession.deliver_label`). A delivery whose lookup does not
evict, to a receiver retaining compatible material, keeps the row's record (`ReceiptPossession.deliver_kept`). With
one record per id, a delivery after which the receiver still holds a record under the commitment did not evict
(`ReceiptPossession.unevicted_of_resident`): its lookup at the delivery's own sample was live or exempt
(`ReceiptPossession.deliver_live`). A kept record stays kept across a step after which the node still holds a record
under its id and which births none there (`ReceiptPossession.kept_frame`), and a step after which the node holds at most
one record under an id it held before births none there (`ReceiptPossession.unborn_of_resident`).

**The quorum.** `ReceiptPossession.held_quorum`: distinct keys with their records kept on every input, plus the
receiver's own signature, give the rung's transaction `DUR-28`'s quorum in `ReceiptLifecycle.heldAt`;
`ReceiptPossession.final_of_quorum` turns it, at the node's threshold and for a rung at or below the latch, into
`ReceiptLifecycle.finalAt` at or above the rung. The headline concludes the quorum only.

**The headline.** `ReceiptPossession.possession_window`, and `ReceiptPossession.possession_within` under bounded
service: from `ReceiptLifecycle.Fresh` under `Registration.preserve`, the quorum holds in the receiver's possession on
the layer at slot `t0 + B₁ + B₂ + 2`. Its docstring lists each condition and whether it is a premise or derived.

**Not claimed.** No assembly, send, submission, inclusion or confirmation: the quorum is possession. No bound in
seconds, no fairness added to any safety theorem, no shared per-peer quota (`NCH-15`), no retransmission (`NCH-8`), no
bytes on the wire, and no SILENCE over the layer's passes or the possession they lead to. The label premise (every
envelope of a row carries the rung's hash) is not derived. -/

namespace BtcPolicy.ReceiptPossession
open BtcPolicy.Kernel BtcPolicy.Ledger BtcPolicy.FedSilence
open BtcPolicy.RungAssembly (Cfg Step)

/-! ## A schedule-driven run of the layer -/

/-- One slot of a schedule on the layer: the offered step is taken, with the label `ReceiptLifecycle.labelFor` gives
it, when `ReceiptLifecycle.admits` and the label check pass; otherwise, and when nothing is offered, the slot
stutters. -/
def offer (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat)
    (p : ReceiptLifecycle.Trace × ReceiptLifecycle.State) :
    Option Step → ReceiptLifecycle.Trace × ReceiptLifecycle.State
  | none => p
  | some s =>
    if ReceiptLifecycle.admits cfg g lcfg r honest p.2 p.1 s &&
        ReceiptLifecycle.labelOk p.2 s (ReceiptLifecycle.labelFor p.2 s) then
      ((p.2, s, ReceiptLifecycle.labelFor p.2 s) :: p.1,
        ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r p.2 s (ReceiptLifecycle.labelFor p.2 s))
    else p

/-- The run of the layer a schedule drives from `st0`: slot `u` offers `sched u`. -/
def play (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat) (st0 : ReceiptLifecycle.State)
    (sched : Nat → Option Step) : Nat → ReceiptLifecycle.Trace × ReceiptLifecycle.State
  | 0 => ([], st0)
  | u + 1 => offer cfg g lcfg r honest (play cfg g lcfg r honest st0 sched u) (sched u)

theorem offer_execution {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {p : ReceiptLifecycle.Trace × ReceiptLifecycle.State}
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest p.1 p.2) (o : Option Step) :
    ReceiptLifecycle.Execution cfg g lcfg r honest (offer cfg g lcfg r honest p o).1
      (offer cfg g lcfg r honest p o).2 := by
  cases o with
  | none => exact hx
  | some s =>
    by_cases h : (ReceiptLifecycle.admits cfg g lcfg r honest p.2 p.1 s &&
        ReceiptLifecycle.labelOk p.2 s (ReceiptLifecycle.labelFor p.2 s)) = true
    · simp only [offer, if_pos h]
      simp only [Bool.and_eq_true] at h
      exact .next s _ h.1 h.2 hx
    · simp only [offer, if_neg h]
      exact hx

/-- **Every slot of a play is an execution of the layer.** From a fresh start, the history and state a schedule has
reached at every slot are a `ReceiptLifecycle.Execution`, whatever the schedule offers. -/
@[req "DUR-28"]
theorem play_execution {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st0 : ReceiptLifecycle.State} {sched : Nat → Option Step} (hf : ReceiptLifecycle.Fresh honest st0) :
    ∀ u, ReceiptLifecycle.Execution cfg g lcfg r honest (play cfg g lcfg r honest st0 sched u).1
      (play cfg g lcfg r honest st0 sched u).2
  | 0 => .init _ hf
  | u + 1 => offer_execution (play_execution hf u) _

/-- A slot either stutters or takes one step at the state and history before it. -/
theorem offer_cases (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat)
    (p : ReceiptLifecycle.Trace × ReceiptLifecycle.State) (o : Option Step) :
    offer cfg g lcfg r honest p o = p ∨ ∃ s h, offer cfg g lcfg r honest p o =
      ((p.2, s, h) :: p.1, ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r p.2 s h) := by
  cases o with
  | none => exact .inl rfl
  | some s =>
    by_cases h : (ReceiptLifecycle.admits cfg g lcfg r honest p.2 p.1 s &&
        ReceiptLifecycle.labelOk p.2 s (ReceiptLifecycle.labelFor p.2 s)) = true
    · simp only [offer, if_pos h]
      exact .inr ⟨s, _, rfl⟩
    · exact .inl (by simp only [offer, if_neg h])

theorem offer_taken {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {p : ReceiptLifecycle.Trace × ReceiptLifecycle.State} {s : Step}
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest p.2 p.1 s = true)
    (hl : ReceiptLifecycle.labelOk p.2 s (ReceiptLifecycle.labelFor p.2 s) = true) :
    offer cfg g lcfg r honest p (some s) =
      ((p.2, s, ReceiptLifecycle.labelFor p.2 s) :: p.1,
        ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r p.2 s (ReceiptLifecycle.labelFor p.2 s)) := by
  simp [offer, ha, hl]

theorem record_append (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) :
    ∀ (T : ReceiptLifecycle.Trace) (st : ReceiptLifecycle.State) (a b : List (Step × Option (Option Nat))),
      ReceiptLifecycle.record keys g lcfg r T st (a ++ b) =
        ReceiptLifecycle.record keys g lcfg r (ReceiptLifecycle.record keys g lcfg r T st a).1
          (ReceiptLifecycle.record keys g lcfg r T st a).2 b
  | _, _, [], _ => rfl
  | _, _, _ :: a, b => record_append keys g lcfg r _ _ a b

theorem legal_append (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (honest : List Nat) :
    ∀ (T : ReceiptLifecycle.Trace) (st : ReceiptLifecycle.State) (a b : List (Step × Option (Option Nat))),
      ReceiptLifecycle.legal cfg g lcfg r honest T st (a ++ b) =
        (ReceiptLifecycle.legal cfg g lcfg r honest T st a &&
          ReceiptLifecycle.legal cfg g lcfg r honest
            (ReceiptLifecycle.record cfg.lc.pre.sweep.keys g lcfg r T st a).1
            (ReceiptLifecycle.record cfg.lc.pre.sweep.keys g lcfg r T st a).2 b)
  | _, _, [], _ => by simp [ReceiptLifecycle.legal, ReceiptLifecycle.record]
  | T, st, s :: a, b => by
    simp only [List.cons_append, ReceiptLifecycle.legal, ReceiptLifecycle.record, Bool.and_assoc]
    rw [legal_append cfg g lcfg r honest _ _ a b]

/-- **A legal list run is a play.** The schedule that offers a list's steps in order, and nothing after them, reaches
after `n` slots the run `ReceiptLifecycle.record` makes of the list's first `n` steps, each labelled by
`ReceiptLifecycle.labelFor`. -/
@[req "DUR-28"]
theorem play_list {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st0 : ReceiptLifecycle.State} {ss : List Step}
    (hl : ReceiptLifecycle.legal cfg g lcfg r honest [] st0 (ss.map fun s => (s, none)) = true) :
    ∀ n, n ≤ ss.length → play cfg g lcfg r honest st0 (fun u => ss[u]?) n =
      ReceiptLifecycle.record cfg.lc.pre.sweep.keys g lcfg r [] st0 ((ss.map fun s => (s, none)).take n)
  | 0, _ => rfl
  | n + 1, hn => by
    have hlt : n < ss.length := by omega
    have hlt' : n < (ss.map fun s => ((s, none) : Step × Option (Option Nat))).length := by simpa using hlt
    have ih := play_list hl n (by omega)
    have hl' := hl
    rw [← List.take_append_drop n (ss.map fun s => (s, none)), List.drop_eq_getElem_cons hlt',
      legal_append] at hl'
    simp only [ReceiptLifecycle.legal, Bool.and_eq_true, List.getElem_map, ReceiptLifecycle.labelOf] at hl'
    show offer cfg g lcfg r honest (play cfg g lcfg r honest st0 (fun u => ss[u]?) n) ss[n]? = _
    rw [ih, List.getElem?_eq_getElem hlt, offer_taken hl'.2.1.1 hl'.2.1.2, List.take_succ_eq_append_getElem hlt',
      record_append]
    simp only [List.getElem_map]
    rfl

/-- A prefix of a legal list run is legal. -/
theorem legal_take {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st0 : ReceiptLifecycle.State} {ss : List (Step × Option (Option Nat))}
    (hl : ReceiptLifecycle.legal cfg g lcfg r honest [] st0 ss = true) (n : Nat) :
    ReceiptLifecycle.legal cfg g lcfg r honest [] st0 (ss.take n) = true := by
  rw [← List.take_append_drop n ss, legal_append] at hl
  simp only [Bool.and_eq_true] at hl
  exact hl.1

/-- After a list's last step its play stutters. -/
theorem play_after {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st0 : ReceiptLifecycle.State} {ss : List Step} :
    ∀ d, play cfg g lcfg r honest st0 (fun u => ss[u]?) (ss.length + d) =
      play cfg g lcfg r honest st0 (fun u => ss[u]?) ss.length
  | 0 => rfl
  | d + 1 => by
    show offer cfg g lcfg r honest (play cfg g lcfg r honest st0 (fun u => ss[u]?) (ss.length + d))
      ss[ss.length + d]? = _
    rw [List.getElem?_eq_none (by omega), play_after d]
    rfl

/-! ## What a state of the layer carries -/

/-- Every row of rung `gr` from signer `s` under `cid` is in the layer's partial inventory, and each was sent as an
envelope labelled with `gr`'s user-signature hash (the layer's honest envelopes, `ReceiptLifecycle.State.envs`). -/
def Emitted (st : ReceiptLifecycle.State) (s cid : Nat) (gr : Rung) : Prop :=
  ∀ k < gr.tx.inputs.length, Possession.rowOf s cid gr k ∈ st.ls.cs.sw.fed.parts ∧
    (Possession.rowOf s cid gr k, some gr.userSig) ∈ st.envs

/-- The envelopes only grow. -/
theorem envs_step (keys : List Nat) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State) (x : Step)
    (h : Option Nat) {z : Exp × Option Nat} (hz : z ∈ st.envs) :
    z ∈ (ReceiptLifecycle.apply keys g lcfg r st x h).envs := by
  cases x with
  | base b =>
    cases b with
    | fed s => exact List.mem_append_right _ hz
    | chain b => exact hz
    | observe i b => exact hz
  | assemble i cid m => exact hz
  | send i env cid m => exact hz

/-- **Emission persists** (`NCH-23`). The inventory (`ReceiptLifecycle.step_kept`, evicting deliveries included) and
the envelopes only grow, so rows emitted stay emitted across every step. -/
@[req "NCH-23"]
theorem emitted_step {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules} {st : ReceiptLifecycle.State}
    {s cid : Nat} {gr : Rung} (he : Emitted st s cid gr) (x : Step) (h : Option Nat) :
    Emitted (ReceiptLifecycle.apply keys g lcfg r st x h) s cid gr := by
  exact fun k hk =>
    ⟨(ReceiptLifecycle.step_kept keys g lcfg r st x h).1 _ (he k hk).1, envs_step keys g lcfg r st x h (he k hk).2⟩

theorem emitted_offer {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {p : ReceiptLifecycle.Trace × ReceiptLifecycle.State} {s cid : Nat} {gr : Rung} (he : Emitted p.2 s cid gr)
    (o : Option Step) : Emitted (offer cfg g lcfg r honest p o).2 s cid gr := by
  rcases offer_cases cfg g lcfg r honest p o with e | ⟨x, h, e⟩ <;> rw [e]
  · exact he
  · exact emitted_step he x h

/-- A node's id has no writer: at every state of a run, an honest node's id is its own. -/
theorem node_id {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State} (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st)
    {i : Nat} (hi : i ∈ honest) : (st.ls.cs.sw.fed.worlds i).node.id = i := by
  induction hx with
  | init st h => exact (h.1.1.1.1.2.2 i hi).2.1
  | @next T st s lab ha hl hx ih =>
    cases s with
    | base b =>
      cases b with
      | fed s =>
        by_cases hd : ∃ j env x, s = .deliverPartial j env x
        · obtain ⟨j, env, x, rfl⟩ := hd
          by_cases hij : i = j
          · subst hij
            rw [ReceiptQuota.deliver_node]
            unfold ReceiptExpiry.receive
            split
            · exact ih
            · exact ih
          · show ((ReceiptExpiry.xapply g lcfg r st.lf (.deliverPartial j env x)).fed.worlds i).node.id = i
            rw [ReceiptLifecycle.xapply_other g lcfg r st.lf _ rfl hij]
            exact ih
        · rw [ReceiptQuota.fed_step _ g lcfg r st s lab (fun j env x he => hd ⟨j, env, x, he⟩)]
          cases hact : Federation.actor (kernelStep g lcfg st.lf s) with
          | none => rw [Federation.apply_no_actor r _ _ hact i]; exact ih
          | some a =>
            obtain ⟨j, env, e⟩ := a
            rw [Federation.apply_of_actor r _ _ hact i]
            split
            · next hij => subst hij; rw [step_id]; exact ih
            · exact ih
      | chain b => rw [ReceiptLifecycle.fed_nonfed (by simp)]; exact ih
      | observe j b => rw [ReceiptLifecycle.fed_nonfed (by simp)]; exact ih
    | assemble j cid m => rw [ReceiptLifecycle.fed_nonfed (by simp)]; exact ih
    | send j env cid m => rw [ReceiptLifecycle.fed_nonfed (by simp)]; exact ih

/-! ## Emission at a contributor's pass -/

/-- At a fire or ladder pass the layer admits, the acting node is honest. -/
theorem honest_of_pass {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st : ReceiptLifecycle.State} {T : ReceiptLifecycle.Trace} {s : Nat} {env : Env} {e : Event}
    (he : e = .firePass ∨ e = .ladderPass)
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process s env e))) = true) : s ∈ honest := by
  have h := ReceiptQuota.pass_admits he ha
  simp only [LadderRelease.admits, Sweep.admits, Federation.admits, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1

/-- What an emission at a pass needs: each row of `gr` in the step's fan-out, and the sender's retained variant for it
being `gr`'s hash. Then the rows are in the inventory and the layer's envelopes after the step. -/
theorem emitted_of_fanout {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules} {st : ReceiptLifecycle.State}
    {s : Nat} {env : Env} {e : Event} {cid : Nat} {gr : Rung} (h : Option Nat) (he : e = .firePass ∨ e = .ladderPass)
    (hrow : ∀ k < gr.tx.inputs.length, Possession.rowOf s cid gr k ∈
      Federation.fanout (st.ls.cs.sw.fed.worlds s) (step r env (st.ls.cs.sw.fed.worlds s) e).2)
    (hvar : ∀ k < gr.tx.inputs.length,
      VariantReceipt.variantOf (st.ls.cs.sw.fed.worlds s).node (sighash gr.tx k) k cid = some gr.userSig) :
    Emitted (ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.process s env e))) h) s cid gr := by
  intro k hk
  refine ⟨?_, ?_⟩
  · rw [ReceiptQuota.pass_fed keys g lcfg r st s env he h]
    exact List.mem_append_right _ (hrow k hk)
  · have hne : VariantSilence.newEnvs r g lcfg st.lf (.process s env e) =
        VariantReceipt.emitted r (st.ls.cs.sw.fed.worlds s) env e := by
      rcases he with rfl | rfl <;> rfl
    show _ ∈ VariantSilence.newEnvs r g lcfg st.lf (.process s env e) ++ st.envs
    rw [hne]
    refine List.mem_append_left _ (List.mem_map.2 ⟨Possession.rowOf s cid gr k, hrow k hk, ?_⟩)
    simp only [Possession.rowOf, hvar k hk]

/-- The base's rows a queued base row fans out to: on a node whose ids are distinct, a queued row of `c`'s base on
input 0, not hot, is followed by its other inputs' rows. -/
theorem base_rows {w : World} {effs : List Effect} (hn : (w.node.cands.map Cand.id).Nodup) {c : Cand}
    (hc : c ∈ w.node.cands) (hhot : c.hot = false)
    (he : Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id ∈ effs) :
    ∀ k < c.tx.inputs.length, Possession.rowOf w.node.id c.id ⟨c.tx, c.baseSig⟩ k ∈ Federation.fanout w effs := by
  have hx0 := Possession.outbox_mem (w := w) he
  have hoth : Federation.others w (Exp.mk (sighash c.tx 0) 0 w.node.id c.hot c.id) =
      ((List.range c.tx.inputs.length).drop 1).map fun k => Exp.mk (sighash c.tx k) k w.node.id c.hot c.id := by
    unfold Federation.others
    rw [Possession.find_own hn hc (p := fun d => d.id == c.id && sighash d.tx 0 == sighash c.tx 0) (by simp)
      (fun d hd => by simp only [Bool.and_eq_true, beq_iff_eq] at hd; exact hd.1)]
  intro k hk
  simp only [Possession.rowOf, hhot.symm]
  by_cases hk0 : k = 0
  · subst hk0; exact Possession.fanout_head hx0
  · refine List.mem_flatMap.2 ⟨_, hx0, List.mem_cons_of_mem _ ?_⟩
    rw [hoth]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine List.mem_map.2 ⟨k' + 1, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨k', by simp at hk ⊢; omega, by simp; omega⟩

/-- **The base's rows at a fire pass on the layer** (`DUR-21`, `NCH-23`). At a fire pass of node `s` the layer admits,
where the base's release conditions hold for `c` (`Possession.BaseReady` on the layer's lifecycle state), under
`Registration.preserve`, the step queues the row of every input of `c`'s base, with the base's user-signature hash as
its envelope's label. -/
@[req "DUR-21"]
theorem emits_base {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State}
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) (hr : r.registration = .preserve) {s : Nat} {env : Env}
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process s env .firePass))) = true)
    {cid : Nat} {gr : Rung} (hready : Possession.BaseReady r st.ls s env cid gr) (h : Option Nat) :
    Emitted (ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed (.process s env .firePass))) h)
      s cid gr := by
  have hs := honest_of_pass (.inl rfl) ha
  have hn := ReceiptLifecycle.ids_nodup hr hx hs
  have hid := node_id hx hs
  obtain ⟨hp, c, hc, rfl, hhot, hdue, hauth, hw, hst, hrel, rfl⟩ := hready
  have he : Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id ∈
      (step r env (st.ls.cs.sw.fed.worlds s) .firePass).2 := by
    show _ ∈ (firePass r env (st.ls.cs.sw.fed.worlds s).node).2
    unfold firePass
    rw [if_neg (by simp [hp])]
    exact List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hdue, hauth, hw, hst, hrel]⟩, rfl⟩
  have hrows := base_rows hn hc hhot he
  rw [hid] at hrows
  exact emitted_of_fanout h (.inl rfl) hrows
    (fun k hk => Possession.variantOf_own hn hc (by simp [VariantReceipt.rungOf, Cand.ladder]))

/-- The release conditions of the base at a ladder pass of node `s` (`Kernel.baseEffects`): a resident `c` under
`cid`, not hot and not yet released, whose account at the pass over the layer's sweep history
(`ReleaseQuota.passAccount`, `ReceiptQuota.sweepT`) lists rung 0; `gr` is its base. -/
def LadderBaseReady (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) (st : ReceiptLifecycle.State)
    (T : ReceiptLifecycle.Trace) (s : Nat) (env : Env) (cid : Nat) (gr : Rung) : Prop :=
  ∃ c ∈ (st.ls.cs.sw.fed.worlds s).node.cands, c.id = cid ∧ c.hot = false ∧ c.released = false ∧
    0 ∈ (ReleaseQuota.passAccount cfg.lc r st.ls.cs.sw (ReceiptQuota.sweepT g lcfg T) s env c).rungs ∧
    gr = ⟨c.tx, c.baseSig⟩

/-- **The base's rows at a ladder pass on the layer** (`SPN-38`, `NCH-23`). At a ladder pass of node `s` the layer
admits, where its account lists rung 0 for an unreleased, not hot `c` (`ReceiptPossession.LadderBaseReady`), under
`Registration.preserve`, the step queues the row of every input of `c`'s base (`Kernel.baseEffects`), with the base's
user-signature hash as its envelope's label. -/
@[req "SPN-38"]
theorem emits_ladder_base {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State}
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) (hr : r.registration = .preserve) {s : Nat} {env : Env}
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process s env .ladderPass))) = true)
    {cid : Nat} {gr : Rung} (hready : LadderBaseReady cfg g lcfg r st T s env cid gr) (h : Option Nat) :
    Emitted (ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed (.process s env .ladderPass))) h)
      s cid gr := by
  have hs := honest_of_pass (.inr rfl) ha
  have hn := ReceiptLifecycle.ids_nodup hr hx hs
  have hid := node_id hx hs
  have heff := (ReleaseQuota.pass_account_ladder (ReceiptQuota.pass_admits (.inr rfl) ha) r).2
  obtain ⟨c, hc, rfl, hhot, hrel, h0, rfl⟩ := hready
  have he : Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id ∈
      (step r env (st.ls.cs.sw.fed.worlds s) .ladderPass).2 := by
    rw [heff]
    refine List.mem_flatMap.2 ⟨c, hc, List.mem_append_left _ ?_⟩
    simp [baseEffects, hrel, h0]
  have hrows := base_rows hn hc hhot he
  rw [hid] at hrows
  exact emitted_of_fanout h (.inr rfl) hrows
    (fun k hk => Possession.variantOf_own hn hc (by simp [VariantReceipt.rungOf, Cand.ladder]))

/-- **A rung's rows at a ladder pass on the layer** (`DUR-27`, `NCH-23`, `SPN-38`). At a ladder pass of node `s` the
layer admits, where rung `m + 1`'s release conditions hold for `c` (`Possession.RungReady` over the layer's history:
its account, over `ReceiptQuota.sweepT`, lists the rung), under `Registration.preserve`, the step queues the row of
every input of `gr`, with `gr`'s user-signature hash as its envelope's label. -/
@[req "DUR-27"]
theorem emits_rung {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State}
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) (hr : r.registration = .preserve) {s : Nat} {env : Env}
    (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process s env .ladderPass))) = true)
    {m cid : Nat} {gr : Rung}
    (hready : Possession.RungReady cfg r st.ls (ReceiptLifecycle.forget g lcfg T) m s env cid gr) (h : Option Nat) :
    Emitted (ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed (.process s env .ladderPass))) h)
      s cid gr := by
  have hs := honest_of_pass (.inr rfl) ha
  have hn := ReceiptLifecycle.ids_nodup hr hx hs
  have hid := node_id hx hs
  have heff := (ReleaseQuota.pass_account_ladder (ReceiptQuota.pass_admits (.inr rfl) ha) r).2
  obtain ⟨c, hc, rfl, hm, hg, hrung⟩ := hready
  refine emitted_of_fanout h (.inr rfl) (fun k hk => ?_) (fun k hk => Possession.variantOf_own hn hc (hrung k hk))
  have he : Effect.queuePartial (sighash gr.tx k) k false c.id ∈
      (step r env (st.ls.cs.sw.fed.worlds s) .ladderPass).2 := by
    rw [heff]
    exact List.mem_flatMap.2 ⟨c, hc, List.mem_append_right _ (Possession.mem_rungEffects_of hm hg hk)⟩
  have hx0 := Possession.outbox_mem (w := st.ls.cs.sw.fed.worlds s) he
  rw [hid] at hx0
  exact Possession.fanout_head hx0

/-- Which pass releases the rung on the layer: the base at a fire pass, the base at a ladder pass whose account lists
rung 0, or rung `m + 1` at a ladder pass. -/
inductive Pass
  | fire
  | ladderBase
  | rung (m : Nat)
  deriving DecidableEq, Repr

/-- The kernel event of a pass. -/
def Pass.event : Pass → Event
  | .fire => .firePass
  | .ladderBase => .ladderPass
  | .rung _ => .ladderPass

theorem Pass.event_pass (p : Pass) : p.event = .firePass ∨ p.event = .ladderPass := by
  cases p
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr rfl

/-- A pass's release conditions on the layer: `Possession.BaseReady` on the layer's lifecycle state for the fire
pass, `ReceiptPossession.LadderBaseReady` for the base at a ladder pass, and `Possession.RungReady` over the layer's
history for a rung, whose account reads `ReceiptQuota.sweepT` (`ReceiptLifecycle.forget`'s sweep history). -/
def Ready (cfg : Cfg) (g : Guards) (lcfg : Config) (r : Rules) :
    Pass → ReceiptLifecycle.State → ReceiptLifecycle.Trace → Nat → Env → Nat → Rung → Prop
  | .fire, st, _, s, env, cid, gr => Possession.BaseReady r st.ls s env cid gr
  | .ladderBase, st, T, s, env, cid, gr => LadderBaseReady cfg g lcfg r st T s env cid gr
  | .rung m, st, T, s, env, cid, gr => Possession.RungReady cfg r st.ls (ReceiptLifecycle.forget g lcfg T) m s env cid gr

/-- **Emission at a pass on the layer** (`NCH-23`), any form. -/
@[req "NCH-23"]
theorem emits {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State}
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) (hr : r.registration = .preserve) {p : Pass} {s : Nat}
    {env : Env} (ha : ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.process s env p.event))) = true)
    {cid : Nat} {gr : Rung} (hready : Ready cfg g lcfg r p st T s env cid gr) (h : Option Nat) :
    Emitted (ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r st (.base (.fed (.process s env p.event))) h)
      s cid gr := by
  cases p with
  | fire => exact emits_base hx hr ha hready h
  | ladderBase => exact emits_ladder_base hx hr ha hready h
  | rung m => exact emits_rung hx hr ha hready h

/-! ## Delivery into the layer's possession -/

/-- **What a delivery's admission needs on the layer** (`NCH-24`). A delivery of `x` to node `j` is admitted exactly
when `j` is honest, `x` is in the inventory and the step's chain view is read off `j`'s latest observation
(`Settlement.viewOk`). The lookup is not part of admission: an evicting delivery is admitted all the same. -/
@[req "NCH-24"]
theorem deliver_admits {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st : ReceiptLifecycle.State} {T : ReceiptLifecycle.Trace} {j : Nat} {env : Env} {x : Exp} :
    ReceiptLifecycle.admits cfg g lcfg r honest st T (.base (.fed (.deliverPartial j env x))) = true ↔
      j ∈ honest ∧ x ∈ st.ls.cs.sw.fed.parts ∧ Settlement.viewOk st.ls.cs.sw j env = true := by
  simp [ReceiptLifecycle.admits, ReceiptLifecycle.mapStep, kernelStep, LadderRelease.admits, Sweep.admits,
    Federation.admits, Sweep.assemblyOk, LadderRelease.releaseOk, ReceiptLifecycle.guard, Settlement.readOk,
    Federation.actor, Lifecycle.kernelSendOk, and_assoc]

/-- **A delivery's label on the layer** (`NCH-24`). Its label check passes once the partial has an envelope: the label
`ReceiptLifecycle.labelFor` gives it is its newest envelope's. If every envelope of the partial carries the hash `lab`,
that label is `some lab`. -/
@[req "NCH-24"]
theorem deliver_label {st : ReceiptLifecycle.State} {j : Nat} {env : Env} {x : Exp} {lab : Nat}
    (he : (x, some lab) ∈ st.envs) :
    ReceiptLifecycle.labelOk st (.base (.fed (.deliverPartial j env x)))
        (ReceiptLifecycle.labelFor st (.base (.fed (.deliverPartial j env x)))) = true ∧
      ((∀ z ∈ st.envs, z.1 = x → z.2 = some lab) →
        ReceiptLifecycle.labelFor st (.base (.fed (.deliverPartial j env x))) = some lab) := by
  have hf : ∃ z, st.envs.find? (fun z => z.1 == x) = some z := by
    cases hq : st.envs.find? (fun z => z.1 == x) with
    | none => exact absurd (List.find?_eq_none.1 hq _ he) (by simp)
    | some z => exact ⟨z, rfl⟩
  obtain ⟨z, hz⟩ := hf
  have hzm := List.mem_of_find?_eq_some hz
  have hzx : z.1 = x := by simpa using List.find?_some hz
  have hl : ReceiptLifecycle.labelFor st (.base (.fed (.deliverPartial j env x))) = z.2 := by
    show (st.envs.find? fun z => z.1 == x).bind (·.2) = _
    rw [hz]; rfl
  refine ⟨?_, fun hu => by rw [hl]; exact hu z hzm hzx⟩
  rw [hl]
  show (st.envs.contains (x, z.2) || _) = true
  obtain ⟨z1, z2⟩ := z
  simp only at hzx
  subst hzx
  simp [hzm]

/-- **A delivery that does not evict stores a compatible partial** (`NCH-24`, `NCH-25`). At node `j`'s delivery of
`x` with label `h`, when `j`'s lookup at the delivery's sample does not evict and `j` retains a resident `cj` under
`x`'s commitment whose ladder finds a rung `g'` by `x`'s message at `x`'s input, the input in range, the label `g'`'s
hash on an Escape-role `cj`, and the signer one of the store's keys, the record of `x` is in `j`'s store after the step.
A delivery births nothing (`ReceiptLifecycle.count_receivePartial`), so the store's birth filter keeps it. -/
@[req "NCH-24"]
theorem deliver_kept {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules} {st : ReceiptLifecycle.State}
    {j : Nat} {env : Env} {x : Exp} {h : Option Nat} {cj : Cand} {g' : Rung}
    (he : ReceiptExpiry.evictsAt st.lf (.deliverPartial j env x) = false)
    (hcj : cj ∈ (st.ls.cs.sw.fed.worlds j).node.cands) (hid : cj.id = x.cid)
    (hg : VariantReceipt.rungOf cj x.msg x.input = some g') (hk : x.input < g'.tx.inputs.length)
    (hh : cj.isEscape = true → h = some g'.userSig) (hkey : x.signer ∈ keys) :
    (x.cid, Authority.sig x) ∈
      (ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x))) h).store j := by
  have hs : VariantReceipt.storable keys (st.ls.cs.sw.fed.worlds j).node x.msg x.input x.signer x.cid h = true :=
    VariantReceipt.storable_iff.2 ⟨hkey, cj, hcj, hid, g', hg, hk, hh⟩
  have hev : ReceiptExpiry.evicts env (st.ls.cs.sw.fed.worlds j).node x.cid = false := he
  have hnode : ((ReceiptExpiry.xapply g lcfg r st.lf (.deliverPartial j env x)).fed.worlds j).node =
      receivePartial (st.ls.cs.sw.fed.worlds j).node x.msg x.input x.signer x.cid := by
    have := ReceiptQuota.deliver_node keys g lcfg r st j env x h
    rw [ReceiptExpiry.receive_unexpired hev] at this
    exact this
  have hres : ((ReceiptExpiry.xapply g lcfg r st.lf (.deliverPartial j env x)).fed.worlds j).node.cands.any
      (·.id == x.cid) = true := by
    rw [hnode, VariantReceipt.resident_receive]
    exact List.any_eq_true.2 ⟨cj, hcj, by simp [hid]⟩
  have hborn : ReceiptLifecycle.bornAt g lcfg r st.lf (.deliverPartial j env x) j x.cid = false := by
    unfold ReceiptLifecycle.bornAt ReceiptLifecycle.fcount
    rw [hnode, ReceiptLifecycle.count_receivePartial]
    exact decide_eq_false (Nat.lt_irrefl _)
  have harr : VariantReceipt.arrival keys
      (st.ls.cs.sw.fed.worlds j, env, .receivePartial x.msg x.input x.signer x.cid, h) =
      [(x.cid, Authority.sig x)] := by
    simp [VariantReceipt.arrival, hs, Authority.sig]
  show (x.cid, Authority.sig x) ∈ ReceiptLifecycle.xstore keys g lcfg r st.vf (.deliverPartial j env x) h j
  unfold ReceiptLifecycle.xstore
  simp only [kernelStep, Federation.actor, if_pos]
  rw [if_neg (by simpa [ReceiptLifecycle.State.vf] using he)]
  refine List.mem_filter.2 ⟨?_, ?_⟩
  · show _ ∈ VariantReceipt.addNew _ (VariantReceipt.arrival keys
      (st.ls.cs.sw.fed.worlds j, env, .receivePartial x.msg x.input x.signer x.cid, h))
    rw [harr]
    by_cases hin : (x.cid, Authority.sig x) ∈ st.vf.store j
    · exact List.mem_append_left _ hin
    · exact List.mem_append_right _ (List.mem_filter.2 ⟨List.mem_singleton_self _, by simpa using hin⟩)
  · simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hres, hborn⟩

/-- **A delivery after which the receiver still holds the candidate did not evict** (`NCH-24`). With one record per
id at node `j`, a delivery of `x` after which `j` still has a record under `x`'s commitment was not an evicting one: an
eviction leaves no record under the id (`ReceiptLifecycle.evict_clears`). -/
@[req "NCH-24"]
theorem unevicted_of_resident {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules}
    {st : ReceiptLifecycle.State} {j : Nat} {env : Env} {x : Exp} {h : Option Nat}
    (hn : ((st.ls.cs.sw.fed.worlds j).node.cands.map Cand.id).Nodup)
    (hres : ((ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x))) h).ls.cs.sw.fed.worlds
      j).node.cands.any (·.id == x.cid) = true) :
    ReceiptExpiry.evictsAt st.lf (.deliverPartial j env x) = false := by
  cases he : ReceiptExpiry.evictsAt st.lf (.deliverPartial j env x) with
  | false => rfl
  | true =>
    exfalso
    have he' : ReceiptExpiry.evicts env (st.ls.cs.sw.fed.worlds j).node x.cid = true := he
    rw [ReceiptQuota.deliver_node, ReceiptExpiry.receive, if_pos he'] at hres
    have h0 := ReceiptLifecycle.evict_clears hn he'
    rw [List.countP_eq_zero] at h0
    obtain ⟨c, hc, hid⟩ := List.any_eq_true.1 hres
    exact h0 c hc hid

/-- **Live or exempt at the delivery** (`NCH-24`, `SPN-41`). With one record per id at node `j`, a delivery of `x` to
`j` holding a record under `x`'s commitment before it and after it found that record live or exempt at the delivery's
own sample: the lookup's keep test, `ReceiptExpiry.keepsAt`, passed there. -/
@[req "NCH-24"]
theorem deliver_live {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules}
    {st : ReceiptLifecycle.State} {j : Nat} {env : Env} {x : Exp} {h : Option Nat}
    (hn : ((st.ls.cs.sw.fed.worlds j).node.cands.map Cand.id).Nodup)
    (hres₀ : (st.ls.cs.sw.fed.worlds j).node.cands.any (·.id == x.cid) = true)
    (hres : ((ReceiptLifecycle.apply keys g lcfg r st (.base (.fed (.deliverPartial j env x))) h).ls.cs.sw.fed.worlds
      j).node.cands.any (·.id == x.cid) = true) :
    ReceiptExpiry.lookup env (st.ls.cs.sw.fed.worlds j).node x.cid = .live := by
  exact ReceiptLifecycle.live_of (unevicted_of_resident hn hres) hres₀

/-- **A kept record stays kept while it stays resident and unborn** (`NCH-25`). Across any step after which node `j`
still has a record under the kept record's id, and which births no record under that id at `j`, the record stays in
`j`'s store: other nodes' steps and the steps that are not the federation's leave it, and `j`'s own steps keep what was
kept and filter by residency and birth after the step (`ReceiptLifecycle.xstore`). -/
@[req "NCH-25"]
theorem kept_frame {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules} {st : ReceiptLifecycle.State}
    {j : Nat} {p : Nat × Authority.Sig} (hp : p ∈ st.store j) (x : Step) (h : Option Nat)
    (hres : ((ReceiptLifecycle.apply keys g lcfg r st x h).ls.cs.sw.fed.worlds j).node.cands.any (·.id == p.1) = true)
    (hb : ReceiptLifecycle.born keys g lcfg r st x h j p.1 = false) :
    p ∈ (ReceiptLifecycle.apply keys g lcfg r st x h).store j := by
  cases x with
  | base b =>
    cases b with
    | fed s =>
      show p ∈ ReceiptLifecycle.xstore keys g lcfg r st.vf s h j
      unfold ReceiptLifecycle.xstore
      split
      · next i env e hact =>
        split
        · next hji =>
          subst hji
          refine List.mem_filter.2 ⟨List.mem_append_left _ hp, ?_⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true']
          exact ⟨hres, hb⟩
        · exact hp
      · exact hp
    | chain b => exact hp
    | observe i b => exact hp
  | assemble i cid m => exact hp
  | send i env cid m => exact hp

/-- **No birth under a resident id** (`SPN-32`). A step after which node `j` holds at most one record per id (under
`Registration.preserve` at an honest node: `ReceiptLifecycle.ids_nodup`), from a state where `j` held a record under
`cid`, births no record under `cid` at `j`. -/
@[req "SPN-32"]
theorem unborn_of_resident {keys : List Nat} {g : Guards} {lcfg : Config} {r : Rules} {st : ReceiptLifecycle.State}
    {x : Step} {h : Option Nat} {j cid : Nat}
    (hres : (st.ls.cs.sw.fed.worlds j).node.cands.any (·.id == cid) = true)
    (hn : (((ReceiptLifecycle.apply keys g lcfg r st x h).ls.cs.sw.fed.worlds j).node.cands.map Cand.id).Nodup) :
    ReceiptLifecycle.born keys g lcfg r st x h j cid = false := by
  unfold ReceiptLifecycle.born ReceiptLifecycle.fcount
  apply decide_eq_false
  intro hlt
  have h1 : 0 < (st.ls.cs.sw.fed.worlds j).node.cands.countP (·.id == cid) :=
    List.countP_pos_iff.2 (List.any_eq_true.1 hres)
  have h2 : ((ReceiptLifecycle.apply keys g lcfg r st x h).ls.cs.sw.fed.worlds j).node.cands.countP (·.id == cid) ≤ 1 := by
    have := List.nodup_iff_count.1 hn cid
    rw [List.count_eq_countP, List.countP_map] at this
    exact Nat.le_trans (Nat.le_of_eq (List.countP_congr (fun c _ => by simp [Function.comp]))) this
  omega

/-! ## The quorum in the layer's possession -/

/-- **The quorum at the receiver on the layer** (`DUR-28`). On an execution of the layer, at honest node `j`, one of the
keys, with a resident whose ladder holds `gr`: if every contributor in `S` (distinct keys, `j` not among them, `t` at
most their count plus one) has the record of its row of `gr` in `j`'s store on every input, then `gr`'s transaction has
the quorum in `j`'s possession on the layer (`ReceiptLifecycle.heldAt`), `j`'s own signature counted. -/
@[req "DUR-28"]
theorem held_quorum {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {T : ReceiptLifecycle.Trace} {st : ReceiptLifecycle.State}
    (hx : ReceiptLifecycle.Execution cfg g lcfg r honest T st) {j cid t : Nat} {gr : Rung} {S : List Nat}
    (hj : j ∈ honest) (hjk : j ∈ cfg.lc.pre.sweep.keys) (hjS : j ∉ S) (hnd : S.Nodup)
    (hk : ∀ s ∈ S, s ∈ cfg.lc.pre.sweep.keys) (ht : t ≤ S.length + 1) (hX : gr.tx.inputs ≠ [])
    (hown : ∃ c ∈ (st.ls.cs.sw.fed.worlds j).node.cands, gr ∈ c.ladder)
    (hkept : ∀ s ∈ S, ∀ k < gr.tx.inputs.length, (cid, Authority.sig (Possession.rowOf s cid gr k)) ∈ st.store j) :
    Authority.quorum cfg.lc.pre.sweep.keys t gr.tx (ReceiptLifecycle.heldAt st j) = true := by
  have hid := node_id hx hj
  obtain ⟨c, hc, hg⟩ := hown
  refine Possession.quorum_of_records hX (List.nodup_cons.2 ⟨hjS, hnd⟩)
    (fun s hs => (List.mem_cons.1 hs).elim (fun e => e ▸ hjk) (hk s)) (by simpa using ht) ?_
  intro s hs k hkl
  show _ ∈ RungIngress.ownSigs (st.ls.cs.sw.fed.worlds j).node ++ (st.store j).map Prod.snd
  rcases List.mem_cons.1 hs with rfl | hs
  · refine List.mem_append_left _ ?_
    unfold RungIngress.ownSigs
    refine List.mem_flatMap.2 ⟨c, hc, List.mem_flatMap.2 ⟨gr, hg, List.mem_map.2 ⟨k, List.mem_range.2 hkl, ?_⟩⟩⟩
    rw [hid]
  · exact List.mem_append_right _ (List.mem_map.2 ⟨_, hkept s hs k hkl, rfl⟩)

/-- **The finalization on the layer reaches the rung** (`DUR-28`, `Ladder.finalize_highest`). When rung `m` of `c`'s
ladder, at or below its latch, has the quorum at node `i`'s threshold in `i`'s possession on the layer,
`ReceiptLifecycle.finalAt` for `c` is a rung at or above `m`. -/
@[req "DUR-28"]
theorem final_of_quorum {cfg : Cfg} {st : ReceiptLifecycle.State} {i m : Nat} {c : Cand} {gr : Rung}
    (hg : c.ladder[m]? = some gr) (hm : m ≤ c.track.latch)
    (hq : Authority.quorum cfg.lc.pre.sweep.keys (st.ls.cs.sw.fed.worlds i).node.t gr.tx
      (ReceiptLifecycle.heldAt st i) = true) :
    ∃ m', ReceiptLifecycle.finalAt cfg st i c = some m' ∧ m ≤ m' := by
  exact Ladder.finalize_highest _ _ _ _ _ _ hm (by simp only [Ladder.quorumAt, hg]; exact hq)

/-! ## The headline -/

theorem resident_of_retains {st : ReceiptLifecycle.State} {j cid : Nat} {gr : Rung}
    (h : Possession.Retains st.ls j cid gr) : (st.ls.cs.sw.fed.worlds j).node.cands.any (·.id == cid) = true := by
  obtain ⟨cj, hcj, hid, -⟩ := h
  exact List.any_eq_true.2 ⟨cj, hcj, by simp [hid]⟩

/-- **Possession within a window on the layer** (`DUR-28`, `NCH-23`, `NCH-24`, `NCH-25`, `SPN-38`). On the run of the
expiry-aware lifecycle layer a schedule drives from `ReceiptLifecycle.Fresh`, under `Registration.preserve`: let the
contributors `S` be distinct keys, `j` a key outside them at an honest node, and `t` at most their count plus one,
`j`'s own signature counted (condition 1: the actual key list `cfg.lc.pre.sweep.keys` and threshold), and let `gr`'s
transaction have at least one input (`Authority.quorum` holds of no transaction without inputs). If

* each contributor's pass of kind `p` is offered at some slot of `[t0, t0 + B₁]` (condition 3, the release
  opportunity), and at every offered slot of that window where its rows are not yet emitted the layer admits the pass
  and its release conditions hold (`ReceiptPossession.Ready`: the release predicate at the served opportunity, with
  the quota's listing for a rung and the `released` bit for the base);
* each row of each contributor's release of `gr` is offered for delivery to `j` at some slot of
  `[t0 + B₁ + 1, t0 + B₁ + 1 + B₂]` (the service of condition 5), and at every offered slot of that window where its
  record is not yet in `j`'s store, the step's chain view is read off `j`'s observation and every envelope of the row
  in the layer's envelopes carries `gr`'s hash (the recipient's observation and the required label);
* `j` retains, under `cid`, a record whose ladder finds `gr` by its txid at every input (`Possession.Retains`) at every
  slot of `[t0 + B₁ + 1, t0 + B₁ + B₂ + 2]` (the compatible retained variant, and no eviction, prune or other
  lifetime-ending loss before the conclusion);

then at slot `t0 + B₁ + B₂ + 2` `gr`'s transaction has the quorum in `j`'s possession on the layer
(`ReceiptLifecycle.heldAt`: `j`'s own signatures and its store). Derived: each contributor's honesty (from its pass's
admission), the emitted rows and their envelopes, the deliveries' admission and labels, that each served delivery's
lookup did not evict (its record live or exempt at the delivery's own sample: `ReceiptPossession.unevicted_of_resident`,
from retention one slot later), that no step of the delivery window births under `cid` at `j`
(`ReceiptPossession.unborn_of_resident`, from one record per id), the records' persistence and `j`'s own signature.
Slot windows are slot windows: no bound in seconds. -/
@[req "DUR-28"]
theorem possession_window {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st0 : ReceiptLifecycle.State} {sched : Nat → Option Step} (hf : ReceiptLifecycle.Fresh honest st0)
    (hr : r.registration = .preserve) {S : List Nat} {j cid t : Nat} {gr : Rung} (p : Pass) {t0 B₁ B₂ : Nat}
    (hj : j ∈ honest) (hjk : j ∈ cfg.lc.pre.sweep.keys) (hjS : j ∉ S) (hnd : S.Nodup)
    (hk : ∀ s ∈ S, s ∈ cfg.lc.pre.sweep.keys) (ht : t ≤ S.length + 1) (hX : gr.tx.inputs ≠ [])
    (hps : ∀ s ∈ S, ∃ u, t0 ≤ u ∧ u ≤ t0 + B₁ ∧ Possession.passOf s p.event (sched u) = true)
    (hpe : ∀ s ∈ S, ∀ u, t0 ≤ u → u ≤ t0 + B₁ →
      ¬Emitted (play cfg g lcfg r honest st0 sched u).2 s cid gr →
      ∀ env, sched u = some (.base (.fed (.process s env p.event))) →
        ReceiptLifecycle.admits cfg g lcfg r honest (play cfg g lcfg r honest st0 sched u).2
            (play cfg g lcfg r honest st0 sched u).1 (.base (.fed (.process s env p.event))) = true ∧
          Ready cfg g lcfg r p (play cfg g lcfg r honest st0 sched u).2 (play cfg g lcfg r honest st0 sched u).1
            s env cid gr)
    (hds : ∀ s ∈ S, ∀ k < gr.tx.inputs.length, ∃ u, t0 + B₁ + 1 ≤ u ∧ u ≤ t0 + B₁ + 1 + B₂ ∧
      Possession.deliverOf j (Possession.rowOf s cid gr k) (sched u) = true)
    (hde : ∀ s ∈ S, ∀ k < gr.tx.inputs.length, ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + 1 + B₂ →
      (cid, Authority.sig (Possession.rowOf s cid gr k)) ∉ (play cfg g lcfg r honest st0 sched u).2.store j →
      ∀ env, sched u = some (.base (.fed (.deliverPartial j env (Possession.rowOf s cid gr k)))) →
        Settlement.viewOk (play cfg g lcfg r honest st0 sched u).2.ls.cs.sw j env = true ∧
          ∀ z ∈ (play cfg g lcfg r honest st0 sched u).2.envs, z.1 = Possession.rowOf s cid gr k →
            z.2 = some gr.userSig)
    (hret : ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + B₂ + 2 →
      Possession.Retains (play cfg g lcfg r honest st0 sched u).2.ls j cid gr) :
    Authority.quorum cfg.lc.pre.sweep.keys t gr.tx
      (ReceiptLifecycle.heldAt (play cfg g lcfg r honest st0 sched (t0 + B₁ + B₂ + 2)).2 j) = true := by
  let P := play cfg g lcfg r honest st0 sched
  have hx : ∀ u, ReceiptLifecycle.Execution cfg g lcfg r honest (P u).1 (P u).2 := play_execution hf
  -- the passes
  have hem : ∀ s ∈ S, Emitted (P (t0 + B₁ + 1)).2 s cid gr := by
    intro s hs
    refine Possession.reached_within (G := fun u => Emitted (P u).2 s cid gr)
      (s := fun u => Possession.passOf s p.event (sched u))
      (en := fun u => ∀ env, sched u = some (.base (.fed (.process s env p.event))) →
        ReceiptLifecycle.admits cfg g lcfg r honest (P u).2 (P u).1 (.base (.fed (.process s env p.event))) = true ∧
          Ready cfg g lcfg r p (P u).2 (P u).1 s env cid gr)
      (hps s hs) (fun u _ _ he => emitted_offer he _) (fun u h1 h2 hn _ => hpe s hs u h1 h2 hn)
      (fun u _ _ hen hsu => ?_)
    obtain ⟨env, he⟩ := Possession.passOf_some hsu
    obtain ⟨ha, hready⟩ := hen env he
    show Emitted (offer cfg g lcfg r honest (P u) (sched u)).2 s cid gr
    rw [he, offer_taken ha (by cases p <;> rfl)]
    exact emits (hx u) hr ha hready _
  have hem' : ∀ s ∈ S, ∀ d, Emitted (P (t0 + B₁ + 1 + d)).2 s cid gr := by
    intro s hs d
    induction d with
    | zero => exact hem s hs
    | succ d ih => exact emitted_offer ih _
  -- the deliveries
  have hkept : ∀ s ∈ S, ∀ k < gr.tx.inputs.length,
      (cid, Authority.sig (Possession.rowOf s cid gr k)) ∈ (P (t0 + B₁ + B₂ + 2)).2.store j := by
    intro s hs k hkl
    have hE : t0 + B₁ + B₂ + 2 = t0 + B₁ + 1 + B₂ + 1 := by omega
    rw [hE]
    refine Possession.reached_within
      (G := fun u => (cid, Authority.sig (Possession.rowOf s cid gr k)) ∈ (P u).2.store j)
      (s := fun u => Possession.deliverOf j (Possession.rowOf s cid gr k) (sched u))
      (en := fun u => ∀ env, sched u = some (.base (.fed (.deliverPartial j env (Possession.rowOf s cid gr k)))) →
        Settlement.viewOk (P u).2.ls.cs.sw j env = true ∧
          ∀ z ∈ (P u).2.envs, z.1 = Possession.rowOf s cid gr k → z.2 = some gr.userSig)
      (hds s hs k hkl) (fun u h1 h2 hg => ?_)
      (fun u h1 h2 hn _ => hde s hs k hkl u h1 h2 hn) (fun u h1 h2 hen hsu => ?_)
    · show _ ∈ (offer cfg g lcfg r honest (P u) (sched u)).2.store j
      rcases offer_cases cfg g lcfg r honest (P u) (sched u) with e | ⟨x, h, e⟩
      · rw [e]; exact hg
      · have hst : (P (u + 1)).2 = ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r (P u).2 x h := by
          show (offer cfg g lcfg r honest (P u) (sched u)).2 = _
          rw [e]
        have hres1 := resident_of_retains (hret (u + 1) (by omega) (by omega))
        have hres0 := resident_of_retains (hret u (by omega) (by omega))
        have hn1 := ReceiptLifecycle.ids_nodup hr (hx (u + 1)) hj
        rw [hst] at hres1 hn1
        rw [e]
        exact kept_frame hg x h hres1 (unborn_of_resident hres0 hn1)
    · obtain ⟨env, he⟩ := Possession.deliverOf_some hsu
      obtain ⟨hview, hu⟩ := hen env he
      obtain ⟨hpart, henv⟩ := hem' s hs (u - (t0 + B₁ + 1)) k hkl
      rw [show t0 + B₁ + 1 + (u - (t0 + B₁ + 1)) = u by omega] at hpart henv
      have ha : ReceiptLifecycle.admits cfg g lcfg r honest (P u).2 (P u).1
          (.base (.fed (.deliverPartial j env (Possession.rowOf s cid gr k)))) = true :=
        deliver_admits.2 ⟨hj, hpart, hview⟩
      obtain ⟨hl, hlab⟩ := deliver_label (st := (P u).2) (j := j) (env := env) henv
      obtain ⟨cj, hcj, hid, hrung⟩ := hret u (by omega) (by omega)
      have hst : (P (u + 1)).2 = ReceiptLifecycle.apply cfg.lc.pre.sweep.keys g lcfg r (P u).2
          (.base (.fed (.deliverPartial j env (Possession.rowOf s cid gr k))))
          (ReceiptLifecycle.labelFor (P u).2 (.base (.fed (.deliverPartial j env (Possession.rowOf s cid gr k))))) := by
        show (offer cfg g lcfg r honest (P u) (sched u)).2 = _
        rw [he, offer_taken ha hl]
      have hres1 := resident_of_retains (hret (u + 1) (by omega) (by omega))
      rw [hst] at hres1
      have hev := unevicted_of_resident (ReceiptLifecycle.ids_nodup hr (hx u) hj) hres1
      show _ ∈ (offer cfg g lcfg r honest (P u) (sched u)).2.store j
      rw [he, offer_taken ha hl]
      exact deliver_kept hev hcj hid (hrung k hkl) hkl (fun _ => hlab hu) (hk s hs)
  -- the quorum
  obtain ⟨cj, hcj, -, hrung⟩ := hret (t0 + B₁ + B₂ + 2) (by omega) (Nat.le_refl _)
  have h0 : 0 < gr.tx.inputs.length := List.length_pos_iff.2 hX
  exact held_quorum (hx _) hj hjk hjS hnd hk ht hX ⟨cj, hcj, (VariantReceipt.rungOf_some (hrung 0 h0)).1⟩ hkept

/-- **Possession under bounded service on the layer** (`DUR-28`). `ReceiptPossession.possession_window` with each
pass and each delivery served under `Progress.Profile.bounded`: every window of `B₁ + 1` slots offers each
contributor's pass, and every window of `B₂ + 1` slots offers each row's delivery to `j`. A slot is an opportunity for
service, not a second: the bound is in slots. -/
@[req "DUR-28"]
theorem possession_within {cfg : Cfg} {g : Guards} {lcfg : Config} {r : Rules} {honest : List Nat}
    {st0 : ReceiptLifecycle.State} {sched : Nat → Option Step} (hf : ReceiptLifecycle.Fresh honest st0)
    (hr : r.registration = .preserve) {S : List Nat} {j cid t : Nat} {gr : Rung} (p : Pass) {t0 B₁ B₂ : Nat}
    (hj : j ∈ honest) (hjk : j ∈ cfg.lc.pre.sweep.keys) (hjS : j ∉ S) (hnd : S.Nodup)
    (hk : ∀ s ∈ S, s ∈ cfg.lc.pre.sweep.keys) (ht : t ≤ S.length + 1) (hX : gr.tx.inputs ≠ [])
    (hps : ∀ s ∈ S, (Progress.Profile.bounded B₁).Holds fun u => Possession.passOf s p.event (sched u))
    (hpe : ∀ s ∈ S, ∀ u, t0 ≤ u → u ≤ t0 + B₁ →
      ¬Emitted (play cfg g lcfg r honest st0 sched u).2 s cid gr →
      ∀ env, sched u = some (.base (.fed (.process s env p.event))) →
        ReceiptLifecycle.admits cfg g lcfg r honest (play cfg g lcfg r honest st0 sched u).2
            (play cfg g lcfg r honest st0 sched u).1 (.base (.fed (.process s env p.event))) = true ∧
          Ready cfg g lcfg r p (play cfg g lcfg r honest st0 sched u).2 (play cfg g lcfg r honest st0 sched u).1
            s env cid gr)
    (hds : ∀ s ∈ S, ∀ k < gr.tx.inputs.length,
      (Progress.Profile.bounded B₂).Holds fun u => Possession.deliverOf j (Possession.rowOf s cid gr k) (sched u))
    (hde : ∀ s ∈ S, ∀ k < gr.tx.inputs.length, ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + 1 + B₂ →
      (cid, Authority.sig (Possession.rowOf s cid gr k)) ∉ (play cfg g lcfg r honest st0 sched u).2.store j →
      ∀ env, sched u = some (.base (.fed (.deliverPartial j env (Possession.rowOf s cid gr k)))) →
        Settlement.viewOk (play cfg g lcfg r honest st0 sched u).2.ls.cs.sw j env = true ∧
          ∀ z ∈ (play cfg g lcfg r honest st0 sched u).2.envs, z.1 = Possession.rowOf s cid gr k →
            z.2 = some gr.userSig)
    (hret : ∀ u, t0 + B₁ + 1 ≤ u → u ≤ t0 + B₁ + B₂ + 2 →
      Possession.Retains (play cfg g lcfg r honest st0 sched u).2.ls j cid gr) :
    Authority.quorum cfg.lc.pre.sweep.keys t gr.tx
      (ReceiptLifecycle.heldAt (play cfg g lcfg r honest st0 sched (t0 + B₁ + B₂ + 2)).2 j) = true := by
  exact possession_window hf hr p hj hjk hjS hnd hk ht hX (fun s hs => hps s hs t0) hpe
    (fun s hs k hk => hds s hs k hk (t0 + B₁ + 1)) hde hret

end BtcPolicy.ReceiptPossession
