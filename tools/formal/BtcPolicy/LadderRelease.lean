import BtcPolicy.RungRelease
/-! `DUR-21`'s check over the whole ladder at the fire pass, on the composed sweep run. `BtcPolicy.RungRelease`
checks the ladder pass's release, but its fire pass carries `PreRelease.failing`, which judges an Escape by
its base alone: where the ladder's attempt fails and the base's passes, it releases a base partial that
`DUR-21` withholds ("Before ANY partial of a selected Escape is released, the node MUST establish that
Escape's admissibility ..., and MUST release nothing of it ... if any step fails") and that `DUR-27`'s "a
rung the node's own predicate refused MUST be released to nobody" covers when the base is that rung. This
module is the refinement beside it that closes that gap at the fire pass and nowhere else:
`LadderRelease.withheldAt` withholds an Escape-role candidate when its base's verdict fails, as
`PreRelease.failing` does, or when it retains rungs above its base (`Kernel.Cand.above`) and the ladder's
attempt at its own read and latch (`RungRelease.readAt`, `Kernel.Cand.track`) does not release a rung with
the base admissible there (`LadderRelease.baseOk`). The fire pass also carries `SPN-38`'s account of the base
(`LadderRelease.starvedAt`): a record not yet released with no rung affordable, or with its floor past rung 0, is
starved, and `Kernel.firePass` releases nothing of it (`Kernel.Env.starved`). A ladder pass carries
`RungRelease.ladderOk`, as on `RungRelease`'s run. The verdict and the account stay inputs of the kernel.

**The relation to the earlier refinements.** Over a history whose fire passes are taken where the acting
node's Escape-role candidates retain no rung, and carry the account `LadderRelease.starvedAt` computes
(`LadderRelease.AccountBound`), the two ladder-aware refinements are one (`LadderRelease.rung_iff`); without the
account, every execution here is one of `RungRelease`'s (`LadderRelease.to_rung`). Every refined execution here
withholds at least what `RungRelease`'s does (`LadderRelease.failing_sub`), so a base row a fire pass emits carries
`PreRelease.Emitted`'s rung-0 verdict and more (`LadderRelease.EmittedBase.pre`): fire-pass base rows keep their
rung-0 verdict. A base row a ladder pass emits carries the ladder's own listing of rung 0 instead
(`RungRelease.EmittedRung`): admissible at that pass's attempt under a releasing verdict, with ancestry validated
on the selected rung.

**What it establishes.** `LadderRelease.base_origin`: every row an honest fire pass adds to the inventory is a
candidate's, and for an Escape-role candidate the base's verdict released rung 0 and, when it retains rungs,
the ladder's verdict at its own read and latch released a rung with the base admissible at that attempt.
`LadderRelease.refused_base`: at an admitted fire pass, no Escape-role candidate sharing the commitment id of
an Escape whose ladder refuses its base emits anything. `LadderRelease.inventory_provenance`,
`LadderRelease.no_premature_exposure` and `LadderRelease.recovery_no_premature_exposure` are
`RungRelease`'s inventory results with the fire-pass alternative strengthened to `LadderRelease.EmittedBase`.

**Not modelled here.** The kernel's fire pass releases the base's partial and never a rung: the rungs above
the base are the ladder pass's, and a ladder pass whose release lists rung 0 releases the base when no fire
pass has (`Kernel.baseEffects`). The kernel's `released` bit makes the base once across both passes. -/

namespace BtcPolicy.LadderRelease
open BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Federation (Fed fanout outbox others mem_outbox node_id extracted_grows)

/-! ## The fire pass's check -/

/-- `DUR-21` and `DUR-27` for the base of an Escape over its ladder: at candidate `c`'s own read
(`RungRelease.readAt`) and latch, there is an observation, the ladder's verdict releases a rung, and the base
is admissible at that attempt. -/
@[req "DUR-21"]
def baseOk (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) (c : Cand) : Bool :=
  match (RungRelease.readAt st T i c).ob with
  | none => false
  | some b =>
    (Ladder.attempt lc.pre (RungRelease.readAt st T i c) b c c.track.latch).verdict.ok &&
      (Ladder.attempt lc.pre (RungRelease.readAt st T i c) b c c.track.latch).admAt 0

theorem baseOk_iff (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) (c : Cand) :
    baseOk lc st T i c = true ↔ ∃ b k, (RungRelease.readAt st T i c).ob = some b ∧
      Ladder.verdict lc.pre (RungRelease.readAt st T i c) c c.track.latch = .release k ∧
      (Ladder.attempt lc.pre (RungRelease.readAt st T i c) b c c.track.latch).admAt 0 = true := by
  unfold baseOk
  split
  · rename_i hb
    simp [hb]
  · rename_i b hb
    simp only [Ladder.verdict, hb, Bool.and_eq_true, Option.some.injEq]
    constructor
    · rintro ⟨hv, h0⟩
      revert hv
      cases (Ladder.attempt lc.pre (RungRelease.readAt st T i c) b c c.track.latch).verdict with
      | release k => exact fun _ => ⟨b, k, rfl, rfl, h0⟩
      | fail _ => simp [PreRelease.Verdict.ok]
    · rintro ⟨b', k, rfl, hv, h0⟩
      simp [hv, PreRelease.Verdict.ok, h0]

/-- Whether the fire pass withholds candidate `c`: an Escape-role candidate whose base's verdict fails, as
`PreRelease.failing` reads it, or that retains rungs above its base and whose ladder does not release a rung
with the base admissible (`LadderRelease.baseOk`). -/
@[req "DUR-21"]
def refuses (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) (c : Cand) : Bool :=
  c.isEscape &&
    (!(PreRelease.verdict lc.pre (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c).ok ||
      (!c.above.isEmpty && !baseOk lc st T i c))

/-- `DUR-21`'s verdict at node `i`'s fire pass over each Escape's whole ladder: the ids of the Escape-role
candidates it refuses (`LadderRelease.refuses`). -/
@[req "DUR-21"]
def withheldAt (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) : List Nat :=
  ((st.fed.worlds i).node.cands.filter (refuses lc st T i)).map (·.id)

/-- Every id the base's verdict withholds is withheld here. -/
@[req "DUR-21"]
theorem failing_sub (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) {k : Nat}
    (h : k ∈ PreRelease.failing lc.pre st T i) : k ∈ withheldAt lc st T i := by
  simp only [PreRelease.failing, withheldAt, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨c, ⟨hc, hp⟩, rfl⟩ := h
  refine ⟨c, ⟨hc, ?_⟩, rfl⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  simp [refuses, hp.1, hp.2]

/-- Where the acting node's Escape-role candidates retain no rung, the fire pass's verdict is
`PreRelease.failing`. -/
@[req "DUR-21"]
theorem withheldAt_bare (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat)
    (h : ∀ c ∈ (st.fed.worlds i).node.cands, c.isEscape = true → c.above = []) :
    withheldAt lc st T i = PreRelease.failing lc.pre st T i := by
  unfold withheldAt PreRelease.failing
  congr 1
  apply List.filter_congr
  intro c hc
  unfold refuses
  cases he : c.isEscape
  · rfl
  · simp [h c hc he]

/-- `SPN-38`'s account at node `i`'s fire pass, as the commitment ids of the records not yet released whose base
it does not list: no rung is affordable at the base's input count ("If `affordable_rungs = 0`, release nothing
and advance no release bookkeeping on this pass"), or the release floor is already past rung 0. Only records
not yet released are read, so a fire pass after the base is out is unaffected by the floor. -/
@[req "SPN-38"]
def starvedAt (lc : Ladder.Cfg) (st : State) (_T : Trace) (i : Nat) : List Nat :=
  ((st.fed.worlds i).node.cands.filter fun c => !c.released &&
      (Cursor.affordableRungs lc.quota c.tx.inputs.length == 0 || c.track.floor != 0)).map (·.id)

/-- An id is starved exactly when a resident record under it is not yet released and either has no rung
affordable or a floor past rung 0. -/
@[req "SPN-38"]
theorem starved_iff (lc : Ladder.Cfg) (st : State) (T : Trace) (i k : Nat) :
    k ∈ starvedAt lc st T i ↔ ∃ c ∈ (st.fed.worlds i).node.cands, c.id = k ∧ c.released = false ∧
      (Cursor.affordableRungs lc.quota c.tx.inputs.length = 0 ∨ c.track.floor ≠ 0) := by
  unfold starvedAt
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨c, ⟨hc, hr, hs⟩, rfl⟩
    exact ⟨c, hc, rfl, hr, hs⟩
  · rintro ⟨c, hc, rfl, hr, hs⟩
    exact ⟨c, ⟨hc, hr, hs⟩, rfl⟩

/-- A fire pass carries the verdict over the whole ladder and `SPN-38`'s account of the base
(`LadderRelease.starvedAt`), and a ladder pass the computed release. Every other step passes. -/
@[req "DUR-21"]
def releaseOk (lc : Ladder.Cfg) (st : State) (T : Trace) : Step → Bool
  | .fed (.process i env .firePass) =>
    env.withheld == withheldAt lc st T i && env.starved == starvedAt lc st T i
  | .fed (.process i env .ladderPass) => RungRelease.ladderOk lc st T i env
  | _ => true

/-- The sweep's admission and the release conjunct. -/
def admits (lc : Ladder.Cfg) (honest : List Nat) (st : State) (T : Trace) (s : Step) : Bool :=
  Sweep.admits lc.pre.sweep honest st T s && releaseOk lc st T s

/-- A reachable refined execution: `Sweep.Execution` whose fire passes carry the verdict over the whole
ladder and whose ladder passes carry the computed release. -/
inductive Execution (lc : Ladder.Cfg) (r : Rules) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Sweep.Fresh honest st) : Execution lc r honest [] st
  | next {T st} (s : Step) (ha : admits lc honest st T s = true) : Execution lc r honest T st →
      Execution lc r honest ((st, s) :: T) (Sweep.apply r st s)

/-! ## The relation to the earlier refinements -/

theorem to_sweep {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution lc r honest T st) : Sweep.Execution lc.pre.sweep r honest T st := by
  induction hx with
  | init st h => exact .init st h
  | next s ha _ ih =>
    simp only [admits, Bool.and_eq_true] at ha
    exact .next s ha.1 ih

/-- Each step of a trace carries the release conjunct at its own state and history. -/
def Checked (lc : Ladder.Cfg) : Trace → Prop
  | [] => True
  | (st, s) :: T => releaseOk lc st T s = true ∧ Checked lc T

/-- The refinement is exactly the release conjunct. -/
@[req "DUR-21"]
theorem execution_iff {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State} :
    Execution lc r honest T st ↔ Sweep.Execution lc.pre.sweep r honest T st ∧ Checked lc T := by
  constructor
  · intro hx
    induction hx with
    | init st h => exact ⟨.init st h, trivial⟩
    | next s ha _ ih =>
      simp only [admits, Bool.and_eq_true] at ha
      exact ⟨.next s ha.1 ih.1, ha.2, ih.2⟩
  · rintro ⟨hx, hc⟩
    induction hx with
    | init st h => exact .init st h
    | next s ha _ ih =>
      exact .next s (by simp [admits, ha, hc.1]) (ih hc.2)

/-- A ladder pass admitted here is admitted by `RungRelease`. -/
theorem admits_ladder {lc : Ladder.Cfg} {honest : List Nat} {st : State} {T : Trace} {i : Nat} {env : Env}
    (ha : admits lc honest st T (.fed (.process i env .ladderPass)) = true) :
    RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true := by
  simp only [admits, releaseOk, Bool.and_eq_true] at ha
  simp [RungRelease.admits, RungRelease.releaseOk, ha.1, ha.2]

/-- Each fire pass of a trace is taken where the acting node's Escape-role candidates retain no rung. -/
def Bare : Trace → Prop
  | [] => True
  | (st, s) :: T =>
    (∀ i env, s = .fed (.process i env .firePass) →
      ∀ c ∈ (st.fed.worlds i).node.cands, c.isEscape = true → c.above = []) ∧ Bare T

/-- Each fire pass of a trace carries `SPN-38`'s account of the base (`LadderRelease.starvedAt`) at its own
state and history. -/
def AccountBound (lc : Ladder.Cfg) : Trace → Prop
  | [] => True
  | (st, s) :: T =>
    (∀ i env, s = .fed (.process i env .firePass) → env.starved = starvedAt lc st T i) ∧ AccountBound lc T

theorem releaseOk_iff_bare {lc : Ladder.Cfg} {st : State} {T : Trace} {s : Step}
    (hb : ∀ i env, s = .fed (.process i env .firePass) →
      ∀ c ∈ (st.fed.worlds i).node.cands, c.isEscape = true → c.above = [])
    (hs : ∀ i env, s = .fed (.process i env .firePass) → env.starved = starvedAt lc st T i) :
    releaseOk lc st T s = RungRelease.releaseOk lc st T s := by
  cases s with
  | fed s =>
    cases s with
    | process i env e =>
      cases e with
      | firePass =>
        simp [releaseOk, RungRelease.releaseOk, withheldAt_bare lc st T i (hb i env rfl), hs i env rfl]
      | ladderPass => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- Over a history whose fire passes are taken where the acting node's Escape-role candidates retain no rung, a
refined execution here is a `RungRelease.Execution`: the account of the base only refuses more. -/
@[req "DUR-21"]
theorem to_rung {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hb : Bare T) (hx : Execution lc r honest T st) : RungRelease.Execution lc r honest T st := by
  revert hb
  induction hx with
  | init st h => exact fun _ => .init st h
  | @next T st s ha _ ih =>
    intro hb
    refine .next s ?_ (ih hb.2)
    simp only [admits, Bool.and_eq_true] at ha
    simp only [RungRelease.admits, Bool.and_eq_true]
    refine ⟨ha.1, ?_⟩
    have h2 := ha.2
    cases s with
    | fed s =>
      cases s with
      | process i env e =>
        cases e with
        | firePass =>
          simp only [releaseOk, Bool.and_eq_true, beq_iff_eq] at h2
          simp [RungRelease.releaseOk, h2.1, withheldAt_bare lc st T i (hb.1 i env rfl)]
        | ladderPass => exact h2
        | _ => rfl
      | _ => rfl
    | _ => rfl

/-- **The relation to `RungRelease`'s refinement.** Over a history whose fire passes are taken where the
acting node's Escape-role candidates retain no rung and carry `SPN-38`'s account of the base, a refined
execution here is exactly a `RungRelease.Execution`. -/
@[req "DUR-21"]
theorem rung_iff {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hb : Bare T) (hs : AccountBound lc T) :
    Execution lc r honest T st ↔ RungRelease.Execution lc r honest T st := by
  constructor
  · intro hx
    revert hb hs
    induction hx with
    | init st h => exact fun _ _ => .init st h
    | next s ha _ ih =>
      intro hb hs
      simp only [admits, Bool.and_eq_true, releaseOk_iff_bare hb.1 hs.1] at ha
      exact .next s (by simp [RungRelease.admits, ha.1, ha.2]) (ih hb.2 hs.2)
  · intro hx
    revert hb hs
    induction hx with
    | init st h => exact fun _ _ => .init st h
    | next s ha _ ih =>
      intro hb hs
      simp only [RungRelease.admits, Bool.and_eq_true, ← releaseOk_iff_bare hb.1 hs.1] at ha
      exact .next s (by simp [admits, ha.1, ha.2]) (ih hb.2 hs.2)

/-! ## The fire pass's rows -/

theorem fire_effects (r : Rules) (env : Env) (w : World) :
    (step r env w .firePass).2 = (firePass r env w.node).2 := rfl

/-- An admitted fire pass carries the verdict over the whole ladder and the account of the base. -/
theorem fire_env {lc : Ladder.Cfg} {honest : List Nat} {st : State} {T : Trace} {i : Nat} {env : Env}
    (ha : admits lc honest st T (.fed (.process i env .firePass)) = true) :
    env.withheld = withheldAt lc st T i ∧ env.starved = starvedAt lc st T i := by
  simp only [admits, Bool.and_eq_true] at ha
  simpa [releaseOk] using ha.2

/-- **`DUR-21` at the fire pass, over the whole ladder.** Every row an honest node's fire pass adds to the
partial inventory is the partial of a candidate that pass releases, over that candidate's transaction at the
row's input, under its commitment, by this node; and when that candidate is registered in the Escape role, its
base's verdict at that pass released rung 0, and when it also retains rungs above its base, the ladder's
verdict at its own read and latch released a rung, with an observation and the base admissible at that
attempt. Proved from the step and its admission, with no premise that the release was authorized. -/
@[req "DUR-21"]
theorem base_origin {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {i : Nat}
    {env : Env} (ha : admits lc honest st T (.fed (.process i env .firePass)) = true) {x : Exp}
    (hx : x ∈ fanout (st.fed.worlds i) (step r env (st.fed.worlds i) .firePass).2) :
    ∃ c ∈ (st.fed.worlds i).node.cands, x.signer = (st.fed.worlds i).node.id ∧ x.cid = c.id ∧
      x.msg = sighash c.tx x.input ∧ x.hot = c.hot ∧ env.withholds c = false ∧ c.released = false ∧
      due r env (st.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.fed.worlds i).node c = true ∧
      (c.isEscape = true →
        PreRelease.verdict lc.pre (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c = .release 0 ∧
        (c.above ≠ [] → baseOk lc st T i c = true)) := by
  have hw : env.withheld = withheldAt lc st T i := (fire_env ha).1
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hx
  obtain ⟨hsig, hey⟩ := mem_outbox hy
  rw [fire_effects] at hey
  obtain ⟨c, hc, hdue, hauth, hnw, hrel, heq⟩ := firePass_effect r env _ hey
  simp only [Effect.queuePartial.injEq] at heq
  obtain ⟨hm, hi0, hh, hcid⟩ := heq
  have hesc : c.isEscape = true →
      PreRelease.verdict lc.pre (authorizedAt st T i) (st.fed.worlds i).node (st.obs i) c = .release 0 ∧
        (c.above ≠ [] → baseOk lc st T i c = true) := by
    intro he
    have hnr : refuses lc st T i c = false := by
      cases hr : refuses lc st T i c
      · rfl
      · have hk : c.id ∈ withheldAt lc st T i :=
          List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hr⟩, rfl⟩
        rw [← hw] at hk
        simp [Env.withholds, he, hk] at hnw
    simp only [refuses, he, Bool.true_and, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      Bool.not_eq_eq_eq_not] at hnr
    obtain ⟨hv, hb⟩ := hnr
    refine ⟨(PreRelease.verdict_ok_iff ..).1 hv, fun hne => ?_⟩
    rcases hb with hb | hb
    · exact absurd (List.isEmpty_iff.1 (by simpa using hb)) hne
    · simpa using hb
  rcases List.mem_cons.1 hxy with rfl | ho
  · exact ⟨c, hc, hsig, hcid, by rw [hm, hi0], hh, hnw, hrel, hdue, hauth, hesc⟩
  · simp only [others] at ho
    split at ho
    · rename_i d hd
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 ho
      have hdm := List.find?_some hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hdm
      have htx : d.tx.id = c.tx.id := by
        have := hdm.2.trans hm
        simpa [sighash] using this
      refine ⟨c, hc, hsig, hcid, ?_, hh, hnw, hrel, hdue, hauth, hesc⟩
      simp [sighash, htx]
    · simp at ho

/-- **The gap closed: a refused ladder withholds its base.** At an admitted fire pass, for an Escape-role
candidate `c` that retains rungs above its base and whose ladder, at its own read and latch, does not release
a rung with the base admissible, every row the pass adds under `c`'s commitment is a candidate's that is not
registered in the Escape role: no Escape-role candidate under that commitment releases anything there. -/
@[req "DUR-21"]
theorem refused_base {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {i : Nat}
    {env : Env} (ha : admits lc honest st T (.fed (.process i env .firePass)) = true) {c : Cand}
    (hc : c ∈ (st.fed.worlds i).node.cands) (hesc : c.isEscape = true) (hr : c.above ≠ [])
    (hf : baseOk lc st T i c = false) {x : Exp}
    (hx : x ∈ fanout (st.fed.worlds i) (step r env (st.fed.worlds i) .firePass).2) (hcid : x.cid = c.id) :
    ∃ d ∈ (st.fed.worlds i).node.cands, d.isEscape = false ∧ x.cid = d.id ∧ x.msg = sighash d.tx x.input := by
  obtain ⟨d, hd, -, hdx, hmsg, -, hnw, -, -, -, -⟩ := base_origin ha hx
  refine ⟨d, hd, ?_, hdx, hmsg⟩
  cases hde : d.isEscape
  · rfl
  · exfalso
    have hw : env.withheld = withheldAt lc st T i := (fire_env ha).1
    have hrc : refuses lc st T i c = true := by
      simp [refuses, hesc, hr, hf]
    have hk : d.id ∈ withheldAt lc st T i :=
      List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hrc⟩, hcid.symm.trans hdx⟩
    rw [← hw] at hk
    simp [Env.withholds, hde, hk] at hnw

/-- No Escape's ladder blocks a fire pass: an honest node's fire pass carrying the verdict over the whole
ladder and the account of the base is admitted, whatever the environment's other fields. -/
@[req "DUR-21"]
theorem fire_available (lc : Ladder.Cfg) (honest : List Nat) (st : State) (T : Trace) {i : Nat}
    (hi : i ∈ honest) (env : Env) (hs : env.starved = starvedAt lc st T i) :
    admits lc honest st T (.fed (.process i { env with withheld := withheldAt lc st T i } .firePass)) =
      true := by
  simp [admits, Sweep.admits, Federation.admits, Federation.ownEvent, assemblyOk, releaseOk, hi, hs]

/-! ## The partial inventory -/

/-- Node `x.signer` emitted row `x` at a fire pass of the trace, `T₁` the history before it, from a
candidate under the row's commitment, over that candidate's transaction at the row's input, whose base's
verdict there released rung 0 when it is registered in the Escape role, and whose ladder released a rung with
the base admissible when it also retains rungs above its base. -/
def EmittedBase (lc : Ladder.Cfg) (r : Rules) (T : Trace) (x : Exp) : Prop :=
  ∃ T₁ T₂ st env, T = T₂ ++ (st, .fed (.process x.signer env .firePass)) :: T₁ ∧
    x ∈ fanout (st.fed.worlds x.signer) (step r env (st.fed.worlds x.signer) .firePass).2 ∧
    ∃ c ∈ (st.fed.worlds x.signer).node.cands, x.cid = c.id ∧ x.msg = sighash c.tx x.input ∧
      (c.isEscape = true →
        PreRelease.verdict lc.pre (authorizedAt st T₁ x.signer) (st.fed.worlds x.signer).node
          (st.obs x.signer) c = .release 0 ∧
        (c.above ≠ [] → baseOk lc st T₁ x.signer c = true))

theorem EmittedBase.cons {lc : Ladder.Cfg} {r : Rules} {T : Trace} {x : Exp} (y : State × Step)
    (h : EmittedBase lc r T x) : EmittedBase lc r (y :: T) x := by
  obtain ⟨T₁, T₂, st, env, rfl, rest⟩ := h
  exact ⟨T₁, y :: T₂, st, env, rfl, rest⟩

/-- A row emitted here carries `PreRelease.Emitted`'s rung-0 verdict. -/
@[req "DUR-21"]
theorem EmittedBase.pre {lc : Ladder.Cfg} {r : Rules} {T : Trace} {x : Exp} (h : EmittedBase lc r T x) :
    PreRelease.Emitted lc.pre r T x := by
  obtain ⟨T₁, T₂, st, env, hT, hx, c, hc, hcid, hmsg, hv⟩ := h
  exact ⟨T₁, T₂, st, env, hT, hx, c, hc, hcid, hmsg, fun he => (hv he).1⟩

/-- **The partial inventory of the ladder-aware run, with the fire pass checked over the whole ladder.** A
row names a signer whose key is in the cumulative extracted set, or an honest signer that emitted it at a fire
pass past the verdict over its candidate's whole ladder (`LadderRelease.EmittedBase`), or at a ladder pass as a
rung its candidate's own release listed (`RungRelease.EmittedRung`). -/
@[req "DUR-21"]
theorem inventory_provenance {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution lc r honest T st) {x : Exp} (hm : x ∈ st.fed.parts) :
    x.signer ∈ st.fed.extracted ∨
      (x.signer ∈ honest ∧ (EmittedBase lc r T x ∨ RungRelease.EmittedRung lc r T x)) := by
  induction hx with
  | init st h => rw [h.1.2.1] at hm; cases hm
  | @next T st s ha hx ih =>
    have lift (hm : x ∈ st.fed.parts) :
        x.signer ∈ (Sweep.apply r st s).fed.extracted ∨
          (x.signer ∈ honest ∧ (EmittedBase lc r ((st, s) :: T) x ∨
            RungRelease.EmittedRung lc r ((st, s) :: T) x)) := by
      rcases ih hm with h | ⟨hh, he | he⟩
      · refine .inl ?_
        cases s with
        | fed s => exact extracted_grows r _ s h
        | chain b => exact h
        | observe j b => exact h
      · exact .inr ⟨hh, .inl (he.cons _)⟩
      · exact .inr ⟨hh, .inr (he.cons _)⟩
    cases s with
    | chain b => exact lift hm
    | observe j b => exact lift hm
    | fed s =>
      have hfx := Sweep.fed_execution (to_sweep hx)
      cases s with
      | process i env e =>
        simp only [Sweep.apply, Federation.apply, List.mem_append] at hm
        rcases hm with hm | hm
        · exact lift hm
        · have hai := ha
          simp only [admits, Sweep.admits, Federation.admits, Bool.and_eq_true, List.contains_eq_mem,
            decide_eq_true_eq] at hai
          have hi : i ∈ honest := hai.1.1.1
          obtain ⟨y, hy, -⟩ := List.mem_flatMap.1 hm
          have hsig := (Federation.mem_fanout hm).1
          rw [node_id hfx hi] at hsig
          rcases PreRelease.queue_only_firePass (mem_outbox hy).2 with he | ⟨he, -⟩
          · subst he
            subst hsig
            obtain ⟨c, hc, -, hcid, hmsg, -, -, -, -, -, hv⟩ := base_origin ha hm
            exact .inr ⟨hi, .inl ⟨T, [], st, env, rfl, hm, c, hc, hcid, hmsg, hv⟩⟩
          · subst he
            subst hsig
            have hra := admits_ladder ha
            obtain ⟨c, hc, -, hcid, -, hesc, -, -, -, ho⟩ := RungRelease.rung_origin hra hm
            refine .inr ⟨hi, .inr ⟨T, [], st, env, rfl, hm, c, hc, hesc, hcid, ?_⟩⟩
            rcases ho with ⟨-, hmsg, h0⟩ | ho
            · exact .inl ⟨hmsg, h0⟩
            · exact .inr ho
      | forge y =>
        simp only [Sweep.apply, Federation.apply, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact lift hm
        · simp only [admits, Sweep.admits, Federation.admits, Bool.and_eq_true, List.contains_eq_mem,
            decide_eq_true_eq] at ha
          exact .inl (by simpa [Sweep.apply, Federation.apply] using ha.1.1)
      | deliver i env m => exact lift (by simpa [Sweep.apply, Federation.apply, Federation.advance] using hm)
      | deliverPartial i env y =>
        exact lift (by simpa [Sweep.apply, Federation.apply, Federation.advance] using hm)
      | unstaged i cid => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)
      | emit i cid => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)
      | inject m => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)
      | extract j => exact lift (by simpa [Sweep.apply, Federation.apply] using hm)

/-- No premature exposure, with the fire pass checked over the whole ladder: a row of the inventory whose
signer's key is not in the cumulative extracted set was emitted by that signer's honest node, at a fire pass
past the verdict over its candidate's whole ladder or at a ladder pass as a rung its candidate's own release
listed. -/
@[req "DUR-21"]
theorem no_premature_exposure {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution lc r honest T st) {x : Exp} (hm : x ∈ st.fed.parts)
    (hs : x.signer ∉ st.fed.extracted) :
    x.signer ∈ honest ∧ (EmittedBase lc r T x ∨ RungRelease.EmittedRung lc r T x) :=
  (inventory_provenance hx hm).resolve_left hs

/-- **No premature exposure on the composed run with custody, the fire pass checked over the whole ladder.**
On a composed run whose fire passes carry the verdict over each Escape's whole ladder and whose ladder passes
carry the computed release, every row of the partial inventory whose signer's key is not in the cumulative
extracted set was emitted by that signer's honest node at such a fire pass or as a released rung. -/
@[req "DUR-21"]
theorem recovery_no_premature_exposure {cfg : Recovery.Cfg} {lc : Ladder.Cfg} (hpc : lc.pre.sweep = cfg.sweep)
    {r : Rules} {honest : List Nat} {T : Recovery.Trace} {st : Recovery.St}
    (hx : Recovery.Execution cfg r honest T st) (hc : Checked lc (Recovery.sweepTrace T)) {x : Exp}
    (hm : x ∈ st.sw.fed.parts) (hs : x.signer ∉ st.sw.fed.extracted) :
    x.signer ∈ honest ∧ (EmittedBase lc r (Recovery.sweepTrace T) x ∨
      RungRelease.EmittedRung lc r (Recovery.sweepTrace T) x) := by
  have hsw := Settlement.to_sweep (Recovery.to_settlement hx)
  rw [← hpc] at hsw
  exact no_premature_exposure (execution_iff.2 ⟨hsw, hc⟩) hm hs

/-! ## Running a schedule -/

def legal (lc : Ladder.Cfg) (r : Rules) (honest : List Nat) : Trace → State → List Step → Bool
  | _, _, [] => true
  | T, st, s :: ss => admits lc honest st T s && legal lc r honest ((st, s) :: T) (Sweep.apply r st s) ss

theorem execution_of_legal {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution lc r honest T st) {ss : List Step} (hl : legal lc r honest T st ss = true) :
    Execution lc r honest (record r T st ss).1 (record r T st ss).2 := by
  induction ss generalizing T st with
  | nil => exact hx
  | cons s ss ih =>
    simp only [legal, Bool.and_eq_true] at hl
    exact ih (.next s hl.1 hx) hl.2

/-- A schedule with each fire pass's verdict over the whole ladder and each ladder pass's release written
from the state and history it is taken in. A schedule so filled may still be refused at any other step. -/
def fill (lc : Ladder.Cfg) (r : Rules) : Trace → State → List Step → List Step
  | _, _, [] => []
  | T, st, s :: ss =>
    let s' : Step := match s with
      | .fed (.process i env .firePass) =>
        .fed (.process i { env with withheld := withheldAt lc st T i, starved := starvedAt lc st T i }
          .firePass)
      | .fed (.process i env .ladderPass) =>
        .fed (.process i { env with ladder := RungRelease.listed lc st T i } .ladderPass)
      | s => s
    s' :: fill lc r ((st, s') :: T) (Sweep.apply r st s') ss

end BtcPolicy.LadderRelease
