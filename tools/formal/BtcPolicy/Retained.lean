import BtcPolicy.Lifecycle
/-! The local ladder properties of one retained candidate lifetime, carried over the checked composed run
(`DUR-27`, `SPN-32`, `SPN-38`). `Ladder.release_latch`, `Ladder.release_floor`, `RungRelease.ladderAt_own` and
`Lifecycle.ladder_track_mono` state them one pass at a time; this module carries them across every step of a
`LadderRelease.Execution`, and so of every `Lifecycle.Execution` (`Lifecycle.to_ladder`), at an honest node. No
definition changes and no kernel event is added.

**The lifetime.** A record's registration-owned fields are its commitment id, its pair, its base, the base's
user-signature hash and the rungs above it (`Retained.reg`); its release state is `Kernel.Cand.track`. Only a
birth writes those fields (`Kernel.born`, `Kernel.clawbackBorn`), with a fresh release state; only a ladder pass
writes the release state of a record already resident (`Retained.step_frame`, `Kernel.ladderPass_keeps`). A
lifetime of commitment `k` at node `i` is a stretch of steps none of which births a record under `k` at `i`
(`Lifecycle.births`): a fresh registration after pruning, or a rebirth, starts a new one with the latch and the
floor at zero, and nothing here forbids that reset (`Exhibits.Retained.fresh_resets`).

**What it establishes.** On every reachable state each resident of an honest node holds its latch on its own
ladder (`Retained.latch_on_ladder`), the bound `Ladder.release_latch` and `Ladder.select_sound` take as a
premise. Across a lifetime every record under the id descends from one at its start with the same
registration-owned fields, a floor and a latch no lower (`Retained.lifetime_mono`). At an admitted ladder pass
a record's release state either stays or becomes the release its own read and release state compute, and only
when that release lists a rung (`Retained.pass_track`), so a pass that releases no rung of it keeps it
(`Retained.quiet_keeps`) whatever the pass releases for other records. Under `Registration.preserve` an
acceptance, refused or not, of a pair whose spend is resident keeps every record's registration-owned fields
and release state (`Retained.repeat_keeps`) and the node's Held partial set (`Retained.repeat_held`). Every row
of the partial inventory on the lifecycle run names an extracted signer or has its admitted release origin
(`Retained.inventory_provenance`), and every Escape submission is the rung its assembly finalized inside the
lifetime the send was taken in (`Retained.escape_sent_selected`).

**The base and the cursor.** The two emissions are separate: a base row comes only from a fire pass, which
queues it for a candidate whose `released` bit is clear and sets the bit (`Kernel.firePass`), and a rung row only
from a ladder pass, for a rung above the base (`Kernel.rungEffects` queues nothing for index 0). The ladder's
cursor, with its floor, is read by the ladder pass alone, and the fire pass reads neither; `released` is not the
cursor. `Retained.inventory_provenance` states both alternatives and nothing about their relation beyond that.
No condition here asks an assembling node to emit a fresh partial in the pass it assembles in.

**Not established here.** `SPN-38`'s complete quota accounting over the common run: `Ladder.release` runs the
cursor per candidate, but no theorem here ties the base's `released` bit to the cursor's interval, nor the
quota to the emitted rows across passes, so the monotone latch and floor are not cursor or quota conformance.
Receipt-time expiry (`NCH-24`'s expiry branch), the bytes on the wire and scheduling stay outside. -/

namespace BtcPolicy.Retained
open BtcPolicy.Kernel

/-! ## One kernel step -/

/-- A record's registration-owned fields: its commitment id, its pair, its base, the base's user-signature hash and
the rungs above it. -/
def reg (c : Cand) : Nat × Option (Nat × Nat) × Tx × Nat × List Rung := (c.id, c.pair, c.tx, c.baseSig, c.above)

theorem reg_eq {c d : Cand} (h : reg d = reg c) :
    d.id = c.id ∧ d.pair = c.pair ∧ d.ladder = c.ladder ∧ d.isEscape = c.isEscape := by
  simp only [reg, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, by simp [Cand.ladder, h3, h4, h5], Sweep.isEscape_congr h1 h2⟩

theorem withWindow_frame (r : Rules) (sel : List (Nat × Bool)) (T : Clocks.Wall) (slack : Clocks.Secs) (c : Cand) :
    reg (withWindow r sel T slack c) = reg c ∧ (withWindow r sel T slack c).track = c.track := by
  unfold withWindow; split <;> exact ⟨rfl, rfl⟩

/-- The records under `k` in a list mapped by an id-preserving function, after new records ahead of it, one of
them under `k`: more than before. -/
theorem countP_lt {l pre : List Cand} {f : Cand → Cand} (hf : ∀ d, (f d).id = d.id) {x : Cand} (hx : x ∈ pre) :
    l.countP (·.id == x.id) < ((pre ++ l).map f).countP (·.id == x.id) := by
  rw [List.countP_map, List.countP_append]
  have hc : (fun d => (f d).id == x.id) = (fun d : Cand => d.id == x.id) := by funext d; rw [hf]
  have hp : 0 < pre.countP (fun d => (f d).id == x.id) := by
    rw [hc]; exact List.countP_pos_iff.2 ⟨x, hx, by simp⟩
  have hl : l.countP (fun d => (f d).id == x.id) = l.countP (·.id == x.id) := by rw [hc]
  simp only [Function.comp_def]
  omega

/-- **One kernel step other than the ladder pass.** Each record after it is one before it with the same
registration-owned fields and release state, or a record born at the step, with a fresh release state, after which
the node holds more records under its id than before. -/
theorem step_frame (r : Rules) (env : Env) (w : World) (e : Event) (he : e ≠ .ladderPass) {c : Cand}
    (hc : c ∈ (step r env w e).1.node.cands) :
    (∃ d ∈ w.node.cands, reg d = reg c ∧ d.track = c.track) ∨
      (c.track = {} ∧ w.node.cands.countP (·.id == c.id) < (step r env w e).1.node.cands.countP (·.id == c.id)) := by
  have keep (h : c ∈ w.node.cands) : ∃ d ∈ w.node.cands, reg d = reg c ∧ d.track = c.track := ⟨c, h, rfl, rfl⟩
  have frame (f : Cand → Cand) (hf : ∀ d, reg (f d) = reg d ∧ (f d).track = d.track)
      (h : c ∈ w.node.cands.map f) : ∃ d ∈ w.node.cands, reg d = reg c ∧ d.track = c.track := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    exact ⟨d, hd, (hf d).1.symm, (hf d).2.symm⟩
  cases e with
  | accept cid dd E sp es =>
    revert hc
    simp only [step, accept]
    split
    · intro hc; exact .inl (keep (by simpa using hc))
    · split
      · intro hc; exact .inl (keep hc)
      · have born_case (f : Cand → Cand) (hf : ∀ d, (f d).id = d.id ∧ (f d).track = d.track)
            (hcm : c ∈ (register r w.node env sp es).map f) :
            (∃ d ∈ w.node.cands, reg d = reg c ∧ d.track = c.track) ∨
              (c.track = {} ∧ w.node.cands.countP (·.id == c.id) <
                ((register r w.node env sp es).map f).countP (·.id == c.id)) ∨
              (∃ d ∈ w.node.cands, c = f d) := by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hcm
          unfold register at hx ⊢
          split at hx
          · exact .inr (.inr ⟨x, hx, rfl⟩)
          · rename_i hreg
            simp only [hreg]
            rcases List.mem_cons.1 hx with rfl | hx'
            · refine .inr (.inl ⟨by rw [(hf _).2]; rfl, ?_⟩)
              rw [(hf _).1]
              exact countP_lt (pre := [_, _]) (fun d => (hf d).1) (List.mem_cons_self ..)
            rcases List.mem_cons.1 hx' with rfl | hx''
            · refine .inr (.inl ⟨by rw [(hf _).2]; rfl, ?_⟩)
              rw [(hf _).1]
              exact countP_lt (pre := [_, _]) (fun d => (hf d).1)
                (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            · exact .inr (.inr ⟨x, hx'', rfl⟩)
        split
        · intro hc
          rcases born_case _ (fun d => ⟨withWindow_id .., (withWindow_frame ..).2⟩) hc with h | h | ⟨d, hd, rfl⟩
          · exact .inl h
          · exact .inr h
          · exact .inl ⟨d, hd, (withWindow_frame ..).1.symm, (withWindow_frame ..).2.symm⟩
        · intro hc
          have hc' : c ∈ (register r w.node env sp es).map id := by simpa using hc
          rcases born_case id (fun d => ⟨rfl, rfl⟩) hc' with h | h | ⟨d, hd, hcd⟩
          · exact .inl h
          · right; simpa using h
          · exact .inl ⟨d, hd, by rw [hcd]; rfl, by rw [hcd]; rfl⟩
  | receipt cid s =>
    refine .inl ?_
    simp only [step, receipt] at hc
    split at hc
    · exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · simp only [holderDecision] at hc
          exact frame _ (fun d => ⟨by rw [(withWindow_frame ..).1]; rfl, by rw [(withWindow_frame ..).2]⟩) hc
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
    · exact frame _ (fun d => by split <;> exact ⟨rfl, rfl⟩) hc
  | ladderPass => exact absurd rfl he
  | packageAccepted cid =>
    simp only [step, packageAccepted] at hc
    exact .inl (frame _ (fun d => by split <;> exact ⟨rfl, rfl⟩) hc)
  | send cid =>
    simp only [step, send] at hc
    split at hc
    · exact .inl (keep hc)
    · exact .inl (frame _ (fun d => by split <;> exact ⟨rfl, rfl⟩) hc)
  | settle tx =>
    refine .inl ?_
    simp only [step, settle] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> (try split) <;> exact ⟨rfl, rfl⟩) hc
  | prune => exact .inl (keep (List.mem_filter.1 hc).1)
  | tick | panic | adversaryExposes _ _ _ _ => exact .inl (keep hc)
  | receivePartial m i s cid' =>
    exact .inl (frame _ (fun d => by split <;> exact ⟨rfl, rfl⟩) hc)
  | clawback x =>
    have hc' : c ∈ (clawback env w.node x).cands := by simpa [step] using hc
    rcases mem_clawback hc' with hc | ⟨rfl, hl, hn⟩
    · exact .inl (keep hc)
    · refine .inr ⟨rfl, ?_⟩
      have e : (step r env w (.clawback x)).1.node.cands =
          ([clawbackBorn w.node.id w.node.combineSlack env x] ++ w.node.cands).map id := by
        simp only [step, clawback, hl, Bool.false_or, List.map_id, List.singleton_append]
        have : w.node.cands.any (·.id == x.id) = false := by
          simpa using fun a ha => hn a ha
        simp [this]
      rw [e]
      exact countP_lt (fun d => rfl) (List.mem_singleton_self _)

/-- The ladder's length on a candidate's own read is its retained ladder's. -/
theorem txs_length (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (c : Cand) :
    (Ladder.txs (RungRelease.readAt st T i c) c).length = c.ladder.length := by
  simp [Ladder.txs, RungRelease.readAt, Ladder.Read.own, Cand.ladder]

theorem ladder_pos (c : Cand) : 0 < c.ladder.length := by simp [Cand.ladder]

/-- **One admitted step of the checked run, at node `i`.** Each record after it is one before it with the same
registration-owned fields, a floor no lower and, while the earlier latch is on the ladder, a latch no lower and on
the ladder; or a record born at the step, with a fresh release state, after which the node holds more records under
its id than before. -/
theorem sweep_step {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace}
    {s : Sweep.Step} (ha : LadderRelease.admits lc honest st T s = true) (i : Nat) {c : Cand}
    (hc : c ∈ ((Sweep.apply r st s).fed.worlds i).node.cands) :
    (∃ d ∈ (st.fed.worlds i).node.cands, reg d = reg c ∧ d.track.floor ≤ c.track.floor ∧
        (d.track.latch < d.ladder.length → d.track.latch ≤ c.track.latch ∧ c.track.latch < c.ladder.length)) ∨
      (c.track = {} ∧ Lifecycle.countAt st i c.id < Lifecycle.countAt (Sweep.apply r st s) i c.id) := by
  have same (d : Cand) (hd : d ∈ (st.fed.worlds i).node.cands) (h1 : reg d = reg c) (h2 : d.track = c.track) :
      ∃ d ∈ (st.fed.worlds i).node.cands, reg d = reg c ∧ d.track.floor ≤ c.track.floor ∧
        (d.track.latch < d.ladder.length → d.track.latch ≤ c.track.latch ∧ c.track.latch < c.ladder.length) :=
    ⟨d, hd, h1, by rw [h2]; exact Nat.le_refl _, fun hl => ⟨by rw [h2]; exact Nat.le_refl _, by rw [← h2, ← (reg_eq h1).2.2.1]; exact hl⟩⟩
  cases s with
  | chain b => exact .inl (same c hc rfl rfl)
  | observe j b => exact .inl (same c hc rfl rfl)
  | fed fs =>
    have hc' : c ∈ ((Federation.apply r st.fed fs).worlds i).node.cands := hc
    cases hact : Federation.actor fs with
    | none =>
      rw [Federation.apply_no_actor r _ fs hact i] at hc'
      exact .inl (same c hc' rfl rfl)
    | some a =>
      obtain ⟨j, env, e⟩ := a
      have hw := Federation.apply_of_actor r st.fed fs hact i
      rw [hw] at hc'
      split at hc'
      · rename_i hij
        subst hij
        by_cases hl : e = .ladderPass
        · subst hl
          have hps : fs = .process i env .ladderPass := by
            cases fs <;> simp only [Federation.actor, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hact
            case process => obtain ⟨rfl, rfl, rfl⟩ := hact; rfl
            all_goals simp_all
          subst hps
          have har := LadderRelease.admits_ladder ha
          simp only [step, ladderPass] at hc'
          split at hc'
          · exact .inl (same c hc' rfl rfl)
          · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
            refine .inl ⟨d, hd, rfl, ?_⟩
            cases hl : ladderAt r env (st.fed.worlds i).node d with
            | none => simp
            | some p =>
              obtain ⟨tr, ms⟩ := p
              obtain ⟨-, -, -, -, hrel⟩ := RungRelease.ladderAt_own har r hd hl
              simp only [Option.map_some, Option.getD_some]
              have hf := Ladder.release_floor lc (RungRelease.readAt st T i d) d d.track
              have hla := Ladder.release_latch lc (RungRelease.readAt st T i d) d d.track
              rw [hrel] at hf hla
              rw [txs_length] at hla
              exact ⟨hf, fun h => hla h⟩
        · rcases step_frame r env _ e hl hc' with ⟨d, hd, h1, h2⟩ | ⟨h1, h2⟩
          · exact .inl (same d hd h1 h2)
          · refine .inr ⟨h1, ?_⟩
            unfold Lifecycle.countAt
            simp only [Sweep.apply]
            rw [hw, if_pos rfl]
            exact h2
      · exact .inl (same c hc' rfl rfl)

/-! ## Over the checked run -/

/-- **The latch stays on the retained ladder** (`DUR-27`). At every state of the checked run, each resident of an
honest node has its latch below its own ladder's length: the premise `Ladder.release_latch` and
`Ladder.select_sound` take, discharged on the run. -/
@[req "DUR-27"]
theorem latch_on_ladder {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest) :
    ∀ c ∈ (st.fed.worlds i).node.cands, c.track.latch < c.ladder.length := by
  induction hx with
  | init st h =>
    intro c hc
    rw [(h.1.2.2 i hi).2.2.2.1] at hc
    cases hc
  | next s ha _ ih =>
    intro c hc
    rcases sweep_step ha i hc with ⟨d, hd, -, -, hl⟩ | ⟨h1, -⟩
    · exact (hl (ih d hd)).2
    · rw [h1]; exact ladder_pos c

/-- **One step of a lifetime.** At an admitted step that births no record under `k` at an honest node, each record
under `k` after it is one before it with the same registration-owned fields, its floor and its latch no lower. -/
@[req "DUR-27"]
theorem life_step {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest) {s : Sweep.Step}
    (ha : LadderRelease.admits lc honest st T s = true) {k : Nat} (hb : Lifecycle.births r st s i k = false) :
    ∀ c ∈ ((Sweep.apply r st s).fed.worlds i).node.cands, c.id = k →
      ∃ d ∈ (st.fed.worlds i).node.cands, reg d = reg c ∧ d.track.floor ≤ c.track.floor ∧
        d.track.latch ≤ c.track.latch := by
  intro c hc hk
  rcases sweep_step ha i hc with ⟨d, hd, h1, h2, h3⟩ | ⟨-, h2⟩
  · exact ⟨d, hd, h1, h2, (h3 (latch_on_ladder hx hi d hd)).1⟩
  · subst hk
    simp [Lifecycle.births, h2] at hb

/-- **The retained lifetime** (`DUR-27`, `SPN-38`). Over a stretch of the checked run in which no step births a
record under `k` at honest node `i`, from the state the stretch starts in, every record under `k` at its end
descends from one at its start with the same registration-owned fields (id, pair, base, the base's user-signature
hash, the rungs above it), whose release floor and rung latch it does not lower. A fresh registration after
pruning, or a rebirth, is a birth: it ends the lifetime, and its record starts at zero
(`Exhibits.Retained.fresh_resets`). -/
@[req "DUR-27"]
theorem lifetime_mono {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    {T₁ T₂ : Sweep.Trace} {st₀ : Sweep.State} {s₀ : Sweep.Step} (hT : T = T₂ ++ (st₀, s₀) :: T₁)
    (hb : ∀ y ∈ T₂ ++ [(st₀, s₀)], Lifecycle.births r y.1 y.2 i k = false) :
    ∀ c ∈ (st.fed.worlds i).node.cands, c.id = k →
      ∃ d ∈ (st₀.fed.worlds i).node.cands, reg d = reg c ∧ d.track.floor ≤ c.track.floor ∧
        d.track.latch ≤ c.track.latch := by
  induction hx generalizing T₂ with
  | init st h => cases T₂ <;> simp at hT
  | @next T st s ha hx' ih =>
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hT
      exact life_step hx' hi ha (hb (st, s) (by simp))
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      intro c hc hk
      obtain ⟨d, hd, h1, h2, h3⟩ := life_step hx' hi ha (hb _ (List.mem_cons_self ..)) c hc hk
      obtain ⟨e, he, g1, g2, g3⟩ :=
        ih hT (fun z hz => hb z (List.mem_cons_of_mem _ hz)) d hd (by rw [(reg_eq h1).1]; exact hk)
      exact ⟨e, he, g1.trans h1, Nat.le_trans g2 h2, Nat.le_trans g3 h3⟩

/-- A release that lists no rung leaves the release state as it was. -/
theorem release_quiet (cfg : Ladder.Cfg) (rd : Ladder.Read) (c : Cand) (tr : Track)
    (h : (Ladder.release cfg rd c tr).2 = []) : (Ladder.release cfg rd c tr).1 = tr := by
  revert h
  unfold Ladder.release
  split
  · intro _; rfl
  · unfold Ladder.after
    split
    · intro _; rfl
    · split
      · intro _; rfl
      · split
        · intro _; rfl
        · rename_i hne
          intro h
          exact absurd h (by simpa using hne)

/-- **A record's release state at one ladder pass** (`DUR-27`, `SPN-38`). At a ladder pass the check admits, each
record after it is one before it with the same registration-owned fields, whose release state either stays or, for
an Escape-role record that is not hot and is due and authorized, becomes the release state its own read and
release state compute, and then only when that release lists a rung. Each record reads its own entry
(`RungRelease.ladderAt_own`), so what the pass releases for another record moves nothing here. -/
@[req "DUR-27"]
theorem pass_track {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules) :
    ∀ c' ∈ ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands,
      ∃ c ∈ (st.fed.worlds i).node.cands, reg c = reg c' ∧ (c'.track = c.track ∨
        (c.isEscape = true ∧ c.hot = false ∧ due r env (st.fed.worlds i).node c = true ∧
          releaseAuthorized r (st.fed.worlds i).node c = true ∧
          (Ladder.release lc (RungRelease.readAt st T i c) c c.track).2 ≠ [] ∧
          c'.track = (Ladder.release lc (RungRelease.readAt st T i c) c c.track).1)) := by
  intro c' hc'
  rw [Federation.apply_of_actor r _ _ rfl i, if_pos rfl] at hc'
  simp only [step, ladderPass] at hc'
  split at hc'
  · exact ⟨c', hc', rfl, .inl rfl⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine ⟨c, hc, rfl, ?_⟩
    cases hl : ladderAt r env (st.fed.worlds i).node c with
    | none => exact .inl (by simp)
    | some p =>
      obtain ⟨tr, ms⟩ := p
      obtain ⟨h1, h2, h3, h4, hrel⟩ := RungRelease.ladderAt_own ha r hc hl
      simp only [Option.map_some, Option.getD_some]
      by_cases hm : ms = []
      · subst hm
        left
        have := release_quiet lc (RungRelease.readAt st T i c) c c.track (by rw [hrel])
        rw [hrel] at this
        exact this
      · exact .inr ⟨h1, h2, h3, h4, by rw [hrel]; exact hm, by rw [hrel]⟩

/-- **A pass that releases no rung keeps the release state** (`SPN-38`: "release nothing and advance no release
bookkeeping on this pass"). At an admitted ladder pass, a record whose own computed release lists no rung keeps its
latch and floor, whatever the pass releases for other records. -/
@[req "SPN-38"]
theorem quiet_keeps {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules) :
    ∀ c' ∈ ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands,
      ∃ c ∈ (st.fed.worlds i).node.cands, reg c = reg c' ∧
        ((Ladder.release lc (RungRelease.readAt st T i c) c c.track).2 = [] → c'.track = c.track) := by
  intro c' hc'
  obtain ⟨c, hc, h1, h2⟩ := pass_track ha r c' hc'
  refine ⟨c, hc, h1, fun hq => ?_⟩
  rcases h2 with h | ⟨-, -, -, -, hne, -⟩
  · exact h
  · exact absurd hq hne

/-! ## A compatible repeat -/

/-- **A repeat keeps the resident records** (`SPN-32`: "an already resident compatible pair is left exactly as is").
Under `Registration.preserve`, an acceptance, refused or not, of a pair whose spend is resident leaves every record's
registration-owned fields and release state as they were, the rung latch and release floor included, in order. -/
@[req "SPN-32"]
theorem repeat_keeps (r : Rules) (hr : r.registration = .preserve) (env : Env) (n : Node) (cid : Nat) (d : Bool)
    (E : Clocks.Wall) (sp es : Cand) (hres : n.cands.any (·.id == sp.id) = true) :
    (accept r env n cid d E sp es).cands.map (fun c => (reg c, c.track)) = n.cands.map (fun c => (reg c, c.track)) ∧
      (accept r env n cid d E sp es).id = n.id := by
  have hreg : register r n env sp es = n.cands := by simp [register, hr, hres]
  unfold accept
  split
  · simp
  · split
    · exact ⟨rfl, rfl⟩
    · refine ⟨?_, rfl⟩
      simp only [hreg]
      split
      · simp only [writeWindows, List.map_map]
        apply List.map_congr_left
        intro c _
        simp only [Function.comp, (withWindow_frame ..).1, (withWindow_frame ..).2]
      · rfl

/-- `VariantReceipt.kept` already holds only records whose commitment the node keeps. -/
theorem kept_filter (keys : List Nat) :
    ∀ (h : VariantReceipt.LHistory) (n : Node),
      (VariantReceipt.kept keys h n).filter (fun p => n.cands.any (·.id == p.1)) = VariantReceipt.kept keys h n
  | [], _ => rfl
  | a :: h, n => by simp [VariantReceipt.kept, List.filter_filter]

/-- **A repeat keeps the Held partial set** (`DUR-28`, `SPN-32`). Under `Registration.preserve`, node `i`'s
acceptance, refused or not, of a pair whose spend is resident leaves `VariantReceipt.held`, its own signatures and
the partials its store kept, as it was. -/
@[req "DUR-28"]
theorem repeat_held (keys : List Nat) (r : Rules) (hr : r.registration = .preserve) (i : Nat)
    (T : VariantReceipt.LTrace) (f : Federation.Fed) (env : Env) (cid : Nat) (d : Bool) (E : Clocks.Wall)
    (sp es : Cand) (lab : Option Nat) (hres : (f.worlds i).node.cands.any (·.id == sp.id) = true) :
    VariantReceipt.held keys i ((f, .process i env (.accept cid d E sp es), lab) :: T)
        (Federation.apply r f (.process i env (.accept cid d E sp es))) =
      VariantReceipt.held keys i T f := by
  obtain ⟨hm, hid⟩ := repeat_keeps r hr env (f.worlds i).node cid d E sp es hres
  have hw : (Federation.apply r f (.process i env (.accept cid d E sp es))).worlds i =
      { f.worlds i with node := accept r env (f.worlds i).node cid d E sp es } := by
    rw [Federation.apply_of_actor r _ _ rfl i, if_pos rfl]; rfl
  have hids : ∀ x, (accept r env (f.worlds i).node cid d E sp es).cands.any (·.id == x) =
      (f.worlds i).node.cands.any (·.id == x) := by
    intro x
    have hid' : (accept r env (f.worlds i).node cid d E sp es).cands.map (·.id) =
        (f.worlds i).node.cands.map (·.id) := by
      have := congrArg (List.map fun p => p.1.1) hm
      simpa [List.map_map, Function.comp_def, reg] using this
    have e : ∀ l : List Cand, l.any (·.id == x) = (l.map (·.id)).any (· == x) := by
      intro l; simp [List.any_map, Function.comp_def]
    rw [e, e, hid']
  have hlad : (accept r env (f.worlds i).node cid d E sp es).cands.map Cand.ladder =
      (f.worlds i).node.cands.map Cand.ladder := by
    have := congrArg (List.map fun p => (p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2)) hm
    simp only [List.map_map, Function.comp_def, reg] at this
    have e : ∀ l : List Cand, l.map Cand.ladder =
        (l.map fun c => (c.tx, c.baseSig, c.above)).map fun t => (⟨t.1, t.2.1⟩ : Rung) :: t.2.2 := by
      intro l; simp [List.map_map, Function.comp_def, Cand.ladder]
    rw [e, e, this]
  unfold VariantReceipt.held
  rw [hw]
  simp only [VariantReceipt.lproject, Federation.actor, if_true, VariantReceipt.kept, VariantReceipt.arrival,
    VariantReceipt.addNew, List.filter_nil, List.append_nil]
  congr 1
  · unfold RungIngress.ownSigs
    rw [hid]
    rw [← List.flatMap_map (f := Cand.ladder), ← List.flatMap_map (f := Cand.ladder) (l := (f.worlds i).node.cands), hlad]
  · congr 1
    simp only [hids]
    exact kept_filter keys _ _

/-! ## On the lifecycle run -/

/-- `Retained.latch_on_ladder` on the lifecycle run. -/
@[req "DUR-27"]
theorem life_latch_on_ladder {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace}
    {st : Lifecycle.State} (hx : Lifecycle.Execution cfg r honest T st) {i : Nat} (hi : i ∈ honest) :
    ∀ c ∈ (st.cs.sw.fed.worlds i).node.cands, c.track.latch < c.ladder.length :=
  latch_on_ladder (Lifecycle.to_ladder hx) hi

/-- **The partial inventory on the lifecycle run** (`DUR-21`, `DUR-27`). Every row names a signer whose key is in the
cumulative extracted set, or an honest signer that emitted it at a fire pass past the verdict over its candidate's
whole ladder, on the base's message (`LadderRelease.EmittedBase`), or at a ladder pass as a rung above the base its
candidate's own release listed (`RungRelease.EmittedRung`). The two are separate emissions: the fire pass's, gated by
the kernel's `released` bit, and the ladder pass's, over the cursor's interval; neither alternative reads the
other. -/
@[req "DUR-27"]
theorem inventory_provenance {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace}
    {st : Lifecycle.State} (hx : Lifecycle.Execution cfg r honest T st) {x : Exp}
    (hm : x ∈ st.cs.sw.fed.parts) :
    x.signer ∈ st.cs.sw.fed.extracted ∨
      (x.signer ∈ honest ∧ (LadderRelease.EmittedBase cfg.lc r (ClassAssembly.sweepT (Lifecycle.toL T)) x ∨
        RungRelease.EmittedRung cfg.lc r (ClassAssembly.sweepT (Lifecycle.toL T)) x)) :=
  LadderRelease.inventory_provenance (Lifecycle.to_ladder hx) hm

/-- **Every Escape submission is the selected rung of its lifetime** (`DUR-28`, `DUR-29`, `DUR-31`). Each Escape
entry of the submission history was sent by honest node `i` on a permit recorded at an earlier admitted assembly of
the same rung and txid by node `i`, where that rung was the finalization over the variant-bound possession at the
node's latch and passed the rung's check (`ClassAssembly.assembleOk`); no sweep step between the assembly and the
send birthed a record under the commitment at node `i`, so the send is in the lifetime the assembly was. No kernel
send adds an Escape entry (`Lifecycle.sentAt_not_escape`), so no inherited base path reaches the history. -/
@[req "DUR-28"]
theorem escape_sent_selected {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace}
    {st : Lifecycle.State} (hx : Lifecycle.Execution cfg r honest T st) {i : Nat} {tx : Tx}
    (h : (i, true, tx) ∈ st.subs) :
    i ∈ honest ∧ ∃ T₀ T₁ T₂ U st₀ st₁ env cid m lab h₁ g, T = T₂ ++ (st₀, .send i env cid m, lab) :: T₁ ∧
      T₁ = T₀ ++ (st₁, .assemble i cid m, h₁) :: U ∧
      ClassAssembly.assembleOk cfg st₁.cs (Lifecycle.toL U) i cid m = true ∧
      RungAssembly.rungAt (st₁.cs.sw.fed.worlds i).node cid m = some g ∧ g.tx.id = tx.id ∧
      ∀ q ∈ T₀, ∀ b, q.2.1 = .base b → Lifecycle.births r q.1.cs.sw b i cid = false := by
  obtain ⟨hi, T₁, T₂, st₀, env, cid, m, lab, hT, c, g, p, hc, hg, hgt, -, -, -, h1, h2, h3, h4, -, hp⟩ :=
    Lifecycle.submitted_origin hx h
  obtain ⟨U₁, U₂, st₁, h₁, hU, hok, -, -, ⟨g', hg', hg't⟩, hkeep⟩ := hp
  rw [h1, h2, h3] at hU hok hg'
  refine ⟨hi, U₂, T₁, T₂, U₁, st₀, st₁, env, cid, m, lab, h₁, g', hT, hU, hok, hg', ?_, ?_⟩
  · rw [hg't, h4, ← hgt]
  · intro q hq b hb
    have hk := hkeep q hq
    rw [hb] at hk
    simp only [Lifecycle.keeps, Bool.and_eq_true, Bool.not_eq_true'] at hk
    rw [← h1, ← h2]; exact hk.1.2

end BtcPolicy.Retained
