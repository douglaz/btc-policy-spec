import BtcPolicy.Ladder
import BtcPolicy.Recovery
/-! `DUR-27`'s release of the rungs above the base, checked on the composed sweep run. `BtcPolicy.PreRelease`
refines the sweep run for the base: a fire pass carries `DUR-21`'s verdict, and a ladder pass is admitted only
when its `Kernel.Env.ladder` lists nothing. This module is the refinement beside it that admits a ladder pass
whose list is computed: `RungRelease.releaseOk` requires the ladder pass's `Kernel.Env.ladder` to be exactly
`RungRelease.listed`, which is, for each Escape-role candidate of the acting node, `Ladder.release` at that
node's read on the run (`Ladder.readOf`), with the rungs above the base the candidate itself retains
(`Kernel.Cand.above`) and its own release state (`Kernel.Cand.track`). A fire pass carries
`PreRelease.failing` as before, so the base keeps its rung-0 verdict. No list is supplied: the read is the
node's own authorized set, registry and latest observation in the state the pass is taken in, and the median
is the one that observation reports at the anchor of its tip (`RungRelease.medianOf`), so an absent reading
is `DUR-30`'s "no pressure".

**The relation to the base's refinement.** Over a history whose ladder passes list nothing, the two
refinements are one (`RungRelease.to_pre`, `RungRelease.pre_iff`), and `RungRelease.inventory_provenance_quiet`
is `PreRelease.inventory_provenance`'s conclusion. `PreRelease.inventory_provenance` and
`PreRelease.no_premature_exposure` are unchanged: they are the base's results, over the base's refinement.

**What it establishes.** `RungRelease.rung_origin`: every row an honest ladder pass adds to the partial
inventory is, for an Escape-role candidate that is not hot and is due and authorized, either its base, not yet
released, on the base's message, with rung 0 listed (`Kernel.baseEffects`), or a rung above its base that this
candidate retains, on that rung's message at the row's input; under its commitment, by this node, and listed in
`Ladder.release` at that candidate's own read and latch, so admissible at that pass's attempt and inside the
cursor's interval (`Ladder.release_mem`). `RungRelease.inventory_provenance`: every row of the
inventory names an extracted signer, or was emitted by its honest signer at a fire pass past the base's
verdict (`PreRelease.Emitted`), or at a ladder pass as a released rung, the base included
(`RungRelease.EmittedRung`);
`RungRelease.no_premature_exposure` drops the first alternative for a signer outside the cumulative extracted
set, and `RungRelease.recovery_no_premature_exposure` is the same on the composed run with custody.
`RungRelease.refused_rung`: no row a ladder pass adds under a candidate's commitment releases a rung index above
the base its own predicate refused there; a base row it adds has rung 0 listed.

**Identity.** The kernel's ladder pass reads, for each candidate, the first entry under its commitment id.
The check admits a listing ladder pass only where the acting node's Escape-role ids are distinct, so that
entry is the candidate's own; under `Kernel.Rules.registration = .preserve` every reachable node's ids are
distinct (`Kernel.ids_nodup`). A rung sharing the base's transaction identity is expanded by
`Federation.others` over the base's inputs; its rows stay on that identity's messages.

**Not modelled here.** Checked ingress still registers no rung (`Ingress.resident_no_rungs`), so the
reachable runs that release a rung register its candidate directly; a released rung's delivery to a peer's
store, its count toward `DUR-28`'s quorum, and its assembly and send are not on this run yet. -/

namespace BtcPolicy.RungRelease
open BtcPolicy.Kernel BtcPolicy.Sweep
open BtcPolicy.Federation (Fed fanout outbox others mem_outbox node_id extracted_grows)

/-! ## The computed list -/

/-- `DUR-30`'s median at an observed instant: the block at the anchor of its tip, as the backend reports
it; `none` when it reports none, which `DUR-30` reads as no pressure. -/
@[req "DUR-30"]
def medianOf (b : Backend) : Option Nat := b.medians.lookup (BumpTarget.anchor b.tip.height)

/-- The rungs above the base that node `n` retains under commitment id `k`, those of its first Escape-role
candidate with that id: `DUR-22`'s pass leaves out the outputs of every selected Escape's resident rungs. -/
@[req "DUR-22"]
def rungsOf (n : Node) (k : Nat) : List Tx :=
  ((n.cands.find? fun d => d.id == k && d.isEscape).map fun d => d.above.map Rung.tx).getD []

/-- The read node `i`'s ladder pass takes for candidate `c`, in state `st` after history `T`:
`Ladder.readOf` there, at the median of the node's latest observation, with the rungs each Escape of the
node's registry retains, and `c`'s own rungs under its id. -/
@[req "DUR-21"]
def readAt (st : State) (T : Trace) (i : Nat) (c : Cand) : Ladder.Read :=
  ({ Ladder.readOf st T i ((st.obs i).bind medianOf) with rungs := rungsOf (st.fed.worlds i).node }).own c.id
    (c.above.map Rung.tx)

/-- The entry for candidate `c`: an Escape-role candidate whose release at its own read and release state
releases some rung, with that release. -/
@[req "DUR-27"]
def entry (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) (c : Cand) :
    Option (Nat × Track × List Nat) :=
  if c.isEscape && !(Ladder.release lc (readAt st T i c) c c.track).2.isEmpty then
    some (c.id, Ladder.release lc (readAt st T i c) c c.track)
  else none

/-- `DUR-27`'s release at node `i`'s ladder pass, computed: one entry per Escape-role candidate that
releases a rung, in registry order. -/
@[req "DUR-27"]
def listed (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) : List (Nat × Track × List Nat) :=
  (st.fed.worlds i).node.cands.filterMap (entry lc st T i)

/-- The ladder pass's check: its list is the computed one, and a list that names a release is taken only
where the node's Escape-role ids are distinct. -/
@[req "DUR-27"]
def ladderOk (lc : Ladder.Cfg) (st : State) (T : Trace) (i : Nat) (env : Env) : Bool :=
  env.ladder == listed lc st T i &&
    (env.ladder.isEmpty || decide (PreRelease.escapeIds (st.fed.worlds i).node).Nodup)

/-- A fire pass carries the base's verdict, as in `PreRelease.releaseOk`, and a ladder pass the computed
release. Every other step passes. -/
@[req "DUR-21"]
def releaseOk (lc : Ladder.Cfg) (st : State) (T : Trace) : Step → Bool
  | .fed (.process i env .firePass) => env.withheld == PreRelease.failing lc.pre st T i
  | .fed (.process i env .ladderPass) => ladderOk lc st T i env
  | _ => true

/-- The sweep's admission and the release conjunct. -/
def admits (lc : Ladder.Cfg) (honest : List Nat) (st : State) (T : Trace) (s : Step) : Bool :=
  Sweep.admits lc.pre.sweep honest st T s && releaseOk lc st T s

/-- A reachable refined execution: `Sweep.Execution` whose fire passes carry the base's verdict and whose
ladder passes carry the computed release. -/
inductive Execution (lc : Ladder.Cfg) (r : Rules) (honest : List Nat) : Trace → State → Prop
  | init (st : State) (h : Sweep.Fresh honest st) : Execution lc r honest [] st
  | next {T st} (s : Step) (ha : admits lc honest st T s = true) : Execution lc r honest T st →
      Execution lc r honest ((st, s) :: T) (Sweep.apply r st s)

/-! ## The relation to the old abstractions -/

/-- Every refined execution is a sweep execution with the same trace and state. -/
@[req "DUR-27"]
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
@[req "DUR-27"]
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

theorem releaseOk_pre {lc : Ladder.Cfg} {st : State} {T : Trace} {s : Step}
    (hn : ∀ i env, s = .fed (.process i env .ladderPass) → env.ladder = [])
    (h : releaseOk lc st T s = true) : PreRelease.releaseOk lc.pre st T s = true := by
  cases s with
  | fed s =>
    cases s with
    | process i env e =>
      cases e with
      | firePass => simpa [releaseOk, PreRelease.releaseOk] using h
      | ladderPass => simp [PreRelease.releaseOk, hn i env rfl]
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem releaseOk_of_pre {lc : Ladder.Cfg} {st : State} {T : Trace} {s : Step}
    (hq : ∀ i env, s = .fed (.process i env .ladderPass) → listed lc st T i = [])
    (h : PreRelease.releaseOk lc.pre st T s = true) : releaseOk lc st T s = true := by
  cases s with
  | fed s =>
    cases s with
    | process i env e =>
      cases e with
      | firePass => simpa [releaseOk, PreRelease.releaseOk] using h
      | ladderPass =>
        have h0 : env.ladder = [] := by simpa [PreRelease.releaseOk] using h
        simp [releaseOk, ladderOk, h0, hq i env rfl]
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- A refined execution whose ladder passes list nothing is the base's refined execution. -/
@[req "DUR-21"]
theorem to_pre {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution lc r honest T st)
    (hn : ∀ p ∈ T, ∀ i env, p.2 = .fed (.process i env .ladderPass) → env.ladder = []) :
    PreRelease.Execution lc.pre r honest T st := by
  induction hx with
  | init st h => exact .init st h
  | next s ha _ ih =>
    simp only [admits, Bool.and_eq_true] at ha
    exact .next s (by
        simp only [PreRelease.admits, Bool.and_eq_true]
        exact ⟨ha.1, releaseOk_pre (hn _ List.mem_cons_self) ha.2⟩)
      (ih fun p hp => hn p (List.mem_cons_of_mem _ hp))

/-- Each ladder pass of a trace is taken where the computed release lists nothing. -/
def Quiet (lc : Ladder.Cfg) : Trace → Prop
  | [] => True
  | (st, s) :: T => (∀ i env, s = .fed (.process i env .ladderPass) → listed lc st T i = []) ∧ Quiet lc T

/-- **The relation to the base's refinement.** Over a history whose ladder passes are taken where the
computed release lists nothing, a refined execution is exactly a `PreRelease.Execution`. -/
@[req "DUR-21"]
theorem pre_iff {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hq : Quiet lc T) : Execution lc r honest T st ↔ PreRelease.Execution lc.pre r honest T st := by
  constructor
  · intro hx
    revert hq
    induction hx with
    | init st h => exact fun _ => .init st h
    | next s ha _ ih =>
      intro hq
      simp only [admits, Bool.and_eq_true] at ha
      refine .next s ?_ (ih hq.2)
      simp only [PreRelease.admits, Bool.and_eq_true]
      refine ⟨ha.1, releaseOk_pre (fun i env he => ?_) ha.2⟩
      subst he
      have h := ha.2
      simp only [releaseOk, ladderOk, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, hq.1 i env rfl]
  · intro hx
    revert hq
    induction hx with
    | init st h => exact fun _ => .init st h
    | next s ha _ ih =>
      intro hq
      simp only [PreRelease.admits, Bool.and_eq_true] at ha
      refine .next s ?_ (ih hq.2)
      simp only [admits, Bool.and_eq_true]
      exact ⟨ha.1, releaseOk_of_pre hq.1 ha.2⟩

/-! ## Rung origin -/

theorem ladder_effects (r : Rules) (env : Env) (w : World) :
    (step r env w .ladderPass).2 = (ladderPass r env w.node).2 := rfl

/-- A listing ladder pass the check admits is taken where the node's Escape-role ids are distinct. -/
theorem escape_nodup {lc : Ladder.Cfg} {honest : List Nat} {st : State} {T : Trace} {i : Nat} {env : Env}
    (ha : admits lc honest st T (.fed (.process i env .ladderPass)) = true) (hne : env.ladder ≠ []) :
    (PreRelease.escapeIds (st.fed.worlds i).node).Nodup := by
  simp only [admits, Bool.and_eq_true] at ha
  have hk := ha.2
  simp only [releaseOk, ladderOk, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff,
    decide_eq_true_eq] at hk
  exact hk.2.resolve_left hne

/-- The entry the kernel's ladder pass reads for a candidate it releases for is that candidate's own
computed release: an admitted ladder pass reads no other candidate's. -/
@[req "DUR-27"]
theorem ladderAt_own {lc : Ladder.Cfg} {honest : List Nat} {st : State} {T : Trace} {i : Nat} {env : Env}
    (ha : admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules) {c : Cand}
    (hc : c ∈ (st.fed.worlds i).node.cands) {tr : Track} {ms : List Nat}
    (hl : ladderAt r env (st.fed.worlds i).node c = some (tr, ms)) :
    c.isEscape = true ∧ c.hot = false ∧ due r env (st.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.fed.worlds i).node c = true ∧
      Ladder.release lc (readAt st T i c) c c.track = (tr, ms) := by
  have heq : env.ladder = listed lc st T i := by
    have hk := ha
    simp only [admits, Bool.and_eq_true] at hk
    have hk2 := hk.2
    simp only [releaseOk, ladderOk, Bool.and_eq_true, beq_iff_eq] at hk2
    exact hk2.1
  unfold ladderAt at hl
  split at hl
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    obtain ⟨⟨hesc, hhot⟩, hdue, hauth⟩ := hcond
    cases hf : env.ladder.find? (·.1 == c.id) with
    | none => simp [hf] at hl
    | some e =>
      simp only [hf, Option.map_some, Option.some.injEq] at hl
      have hmem := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      have hnd := escape_nodup ha (List.ne_nil_of_mem hmem)
      rw [heq] at hmem
      obtain ⟨d, hd, hde⟩ := List.mem_filterMap.1 hmem
      unfold entry at hde
      split at hde
      · rename_i hdc
        simp only [Option.some.injEq] at hde
        subst hde
        simp only [Bool.and_eq_true] at hdc
        simp only [beq_iff_eq] at hp
        have hdc' : d = c := Kernel.eq_of_mem_ids_nodup hnd (List.mem_filter.2 ⟨hd, hdc.1⟩)
          (List.mem_filter.2 ⟨hc, hesc⟩) hp
        subst hdc'
        exact ⟨hesc, hhot, hdue, hauth, hl⟩
      · simp at hde
  · simp at hl

/-- **`DUR-27` at the ladder pass's release boundary.** Every row an honest node's ladder pass adds to the
partial inventory is, for an Escape-role candidate of that node that is not hot and is due and authorized
(`DUR-10`), under the candidate's commitment, by this node, not hot, either the base's partial over the
candidate's own transaction at the row's input, where rung 0 is listed in `Ladder.release` at the candidate's
own read and release state and the candidate was not yet released (`Kernel.baseEffects`), or the partial of a
rung above its base that this candidate retains, on that rung's message at the row's input, and that rung is
listed there. Proved from the step and its admission, with no premise that the release was authorized. -/
@[req "DUR-27"]
theorem rung_origin {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {i : Nat}
    {env : Env} (ha : admits lc honest st T (.fed (.process i env .ladderPass)) = true) {x : Exp}
    (hx : x ∈ fanout (st.fed.worlds i) (step r env (st.fed.worlds i) .ladderPass).2) :
    ∃ c ∈ (st.fed.worlds i).node.cands, x.signer = (st.fed.worlds i).node.id ∧ x.cid = c.id ∧
      x.hot = false ∧ c.isEscape = true ∧ c.hot = false ∧ due r env (st.fed.worlds i).node c = true ∧
      releaseAuthorized r (st.fed.worlds i).node c = true ∧
      ((c.released = false ∧ x.msg = sighash c.tx x.input ∧
          0 ∈ (Ladder.release lc (readAt st T i c) c c.track).2) ∨
        ∃ m g, c.above[m]? = some g ∧ x.msg = sighash g.tx x.input ∧
          m + 1 ∈ (Ladder.release lc (readAt st T i c) c c.track).2) := by
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hx
  obtain ⟨hsig, hey⟩ := mem_outbox hy
  rw [ladder_effects] at hey
  obtain ⟨c, hc, tr, ms, hl, hb | ⟨m, g, k, hm, hg, -, heq⟩⟩ := ladderPass_effect r env _ hey
  · obtain ⟨h0, hcr, heq⟩ := hb
    obtain ⟨hesc, hhot, hdue, hauth, hrel⟩ := ladderAt_own ha r hc hl
    simp only [Effect.queuePartial.injEq] at heq
    obtain ⟨hmsg, hin, hh, hcid⟩ := heq
    have h0' : 0 ∈ (Ladder.release lc (readAt st T i c) c c.track).2 := by rw [hrel]; exact h0
    have hh' : y.hot = false := by rw [hh, hhot]
    rcases List.mem_cons.1 hxy with rfl | ho
    · exact ⟨c, hc, hsig, hcid, hh', hesc, hhot, hdue, hauth, .inl ⟨hcr, by rw [hmsg, hin], h0'⟩⟩
    · simp only [others] at ho
      split at ho
      · rename_i d hd
        obtain ⟨k', -, rfl⟩ := List.mem_map.1 ho
        have hdm := List.find?_some hd
        simp only [Bool.and_eq_true, beq_iff_eq] at hdm
        have htx : d.tx.id = c.tx.id := by
          have := congrArg Prod.fst (hdm.2.trans hmsg)
          simpa [sighash] using this
        exact ⟨c, hc, hsig, hcid, hh', hesc, hhot, hdue, hauth, .inl ⟨hcr, by simp [sighash, htx], h0'⟩⟩
      · simp at ho
  · simp only [Effect.queuePartial.injEq] at heq
    obtain ⟨hmsg, hin, hh, hcid⟩ := heq
    obtain ⟨hesc, hhot, hdue, hauth, hrel⟩ := ladderAt_own ha r hc hl
    have hm' : m + 1 ∈ (Ladder.release lc (readAt st T i c) c c.track).2 := by rw [hrel]; exact hm
    rcases List.mem_cons.1 hxy with rfl | ho
    · exact ⟨c, hc, hsig, hcid, hh, hesc, hhot, hdue, hauth, .inr ⟨m, g, hg, by rw [hmsg, hin], hm'⟩⟩
    · simp only [others] at ho
      split at ho
      · rename_i d hd
        obtain ⟨k', -, rfl⟩ := List.mem_map.1 ho
        have hdm := List.find?_some hd
        simp only [Bool.and_eq_true, beq_iff_eq] at hdm
        have htx : d.tx.id = g.tx.id := by
          have := congrArg Prod.fst (hdm.2.trans hmsg)
          simpa [sighash] using this
        exact ⟨c, hc, hsig, hcid, hh, hesc, hhot, hdue, hauth, .inr ⟨m, g, hg, by simp [sighash, htx], hm'⟩⟩
      · simp at ho

/-- A rung the ladder pass releases was authorized for it: the candidate's own read had an observation, its
verdict there released a rung at or above this one, and this rung was admissible at that attempt. -/
@[req "DUR-27"]
theorem rung_authorized {lc : Ladder.Cfg} {st : State} {T : Trace} {i : Nat} {c : Cand} {m : Nat}
    (h : m + 1 ∈ (Ladder.release lc (readAt st T i c) c c.track).2) :
    ∃ b k, st.obs i = some b ∧ Ladder.verdict lc.pre (readAt st T i c) c c.track.latch = .release k ∧
      m + 1 ≤ k ∧ (Ladder.attempt lc.pre (readAt st T i c) b c c.track.latch).admAt (m + 1) = true := by
  obtain ⟨b, k, _F, _U, _c, hb, hv, -, -, hU, hUk, hadm, -⟩ := Ladder.release_mem h
  exact ⟨b, k, hb, hv, by omega, hadm⟩

/-- **A refused rung is released to nobody.** At an admitted ladder pass, every row the pass adds under an
Escape-role candidate's commitment is the release of a rung index other than one above the base that
candidate's own predicate refuses at its read, however the cursor's interval lies: the base, over the
candidate's own transaction, with rung 0 listed in its release, or a rung above the base at another index.
Rungs are told apart by index: two rungs sharing a txid share their messages (`Kernel.sighash`), so this does
not separate them by message. -/
@[req "DUR-27"]
theorem refused_rung {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {st : State} {T : Trace} {i : Nat}
    {env : Env} (ha : admits lc honest st T (.fed (.process i env .ladderPass)) = true) {c : Cand}
    (hc : c ∈ (st.fed.worlds i).node.cands) (hesc : c.isEscape = true) {b : Backend} {m : Nat}
    (hb : (readAt st T i c).ob = some b)
    (hm : (Ladder.attempt lc.pre (readAt st T i c) b c c.track.latch).admAt (m + 1) = false) {x : Exp}
    (hx : x ∈ fanout (st.fed.worlds i) (step r env (st.fed.worlds i) .ladderPass).2) (hcid : x.cid = c.id) :
    (x.msg = sighash c.tx x.input ∧ 0 ∈ (Ladder.release lc (readAt st T i c) c c.track).2) ∨
      ∃ m' g', m' ≠ m ∧ c.above[m']? = some g' ∧ x.msg = sighash g'.tx x.input := by
  have hne : env.ladder ≠ [] := by
    intro h0
    have hz := ladderPass_nothing r env (st.fed.worlds i).node h0
    rw [ladder_effects, hz] at hx
    split at hx <;> simp [fanout, outbox] at hx
  have hnd := escape_nodup ha hne
  obtain ⟨d, hd, -, hdx, -, hdesc, -, -, -, hbase | ⟨m', g', hg', hmsg, hrel⟩⟩ := rung_origin ha hx
  · have hdc : d = c := Kernel.eq_of_mem_ids_nodup hnd (List.mem_filter.2 ⟨hd, hdesc⟩)
      (List.mem_filter.2 ⟨hc, hesc⟩) (hdx.symm.trans hcid)
    subst hdc
    exact .inl ⟨hbase.2.1, hbase.2.2⟩
  · have hdc : d = c := Kernel.eq_of_mem_ids_nodup hnd (List.mem_filter.2 ⟨hd, hdesc⟩)
      (List.mem_filter.2 ⟨hc, hesc⟩) (hdx.symm.trans hcid)
    subst hdc
    refine .inr ⟨m', g', fun he => ?_, hg', hmsg⟩
    subst he
    exact Ladder.refused_not_released hb hm hrel

/-- A ladder pass carrying the computed release is admitted wherever the acting node is honest and its
Escape-role ids are distinct: no candidate's release blocks a pass. -/
@[req "DUR-27"]
theorem ladder_available (lc : Ladder.Cfg) (honest : List Nat) (st : State) (T : Trace) {i : Nat}
    (hi : i ∈ honest) (hnd : (PreRelease.escapeIds (st.fed.worlds i).node).Nodup) (env : Env) :
    admits lc honest st T (.fed (.process i { env with ladder := listed lc st T i } .ladderPass)) = true := by
  simp [admits, Sweep.admits, Federation.admits, Federation.ownEvent, assemblyOk, releaseOk, ladderOk, hi, hnd]

/-! ## The partial inventory -/

/-- Node `x.signer` emitted row `x` at a ladder pass of the trace, `T₁` the history before it, for an
Escape-role candidate under the row's commitment, as a rung listed in `Ladder.release` at that candidate's own
read and release state there: the base, over the candidate's own transaction at the row's input
(`Kernel.baseEffects`), or a rung above the base, on that rung's message at the row's input. -/
def EmittedRung (lc : Ladder.Cfg) (r : Rules) (T : Trace) (x : Exp) : Prop :=
  ∃ T₁ T₂ st env, T = T₂ ++ (st, .fed (.process x.signer env .ladderPass)) :: T₁ ∧
    x ∈ fanout (st.fed.worlds x.signer) (step r env (st.fed.worlds x.signer) .ladderPass).2 ∧
    ∃ c ∈ (st.fed.worlds x.signer).node.cands, c.isEscape = true ∧ x.cid = c.id ∧
      ((x.msg = sighash c.tx x.input ∧ 0 ∈ (Ladder.release lc (readAt st T₁ x.signer c) c c.track).2) ∨
        ∃ m g, c.above[m]? = some g ∧ x.msg = sighash g.tx x.input ∧
          m + 1 ∈ (Ladder.release lc (readAt st T₁ x.signer c) c c.track).2)

theorem EmittedRung.cons {lc : Ladder.Cfg} {r : Rules} {T : Trace} {x : Exp} (y : State × Step)
    (h : EmittedRung lc r T x) : EmittedRung lc r (y :: T) x := by
  obtain ⟨T₁, T₂, st, env, rfl, rest⟩ := h
  exact ⟨T₁, y :: T₂, st, env, rfl, rest⟩

/-- **The partial inventory of the ladder-aware run, row by row.** A row names a signer whose key is in the
cumulative extracted set, or an honest signer that emitted it at a fire pass past the base's verdict
(`PreRelease.Emitted`), or at a ladder pass as a rung its candidate's own release listed
(`RungRelease.EmittedRung`). -/
@[req "DUR-21"]
theorem inventory_provenance {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution lc r honest T st) {x : Exp} (hm : x ∈ st.fed.parts) :
    x.signer ∈ st.fed.extracted ∨
      (x.signer ∈ honest ∧ (PreRelease.Emitted lc.pre r T x ∨ EmittedRung lc r T x)) := by
  induction hx with
  | init st h => rw [h.1.2.1] at hm; cases hm
  | @next T st s ha hx ih =>
    have lift (hm : x ∈ st.fed.parts) :
        x.signer ∈ (Sweep.apply r st s).fed.extracted ∨
          (x.signer ∈ honest ∧ (PreRelease.Emitted lc.pre r ((st, s) :: T) x ∨
            EmittedRung lc r ((st, s) :: T) x)) := by
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
            have hpa : PreRelease.admits lc.pre honest st T (.fed (.process i env .firePass)) = true := ha
            subst hsig
            obtain ⟨c, hc, -, hcid, hmsg, -, -, -, -, -, hv⟩ := PreRelease.release_origin hpa hm
            exact .inr ⟨hi, .inl ⟨T, [], st, env, rfl, hm, c, hc, hcid, hmsg, hv⟩⟩
          · subst he
            subst hsig
            obtain ⟨c, hc, -, hcid, -, hesc, -, -, -, ho⟩ := rung_origin ha hm
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

/-- No premature exposure on the ladder-aware run: a row of the inventory whose signer's key is not in the
cumulative extracted set was emitted by that signer's honest node, at a fire pass past the base's verdict
or at a ladder pass as a rung its candidate's own release listed. -/
@[req "DUR-21"]
theorem no_premature_exposure {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace} {st : State}
    (hx : Execution lc r honest T st) {x : Exp} (hm : x ∈ st.fed.parts)
    (hs : x.signer ∉ st.fed.extracted) :
    x.signer ∈ honest ∧ (PreRelease.Emitted lc.pre r T x ∨ EmittedRung lc r T x) :=
  (inventory_provenance hx hm).resolve_left hs

/-- Over a history whose ladder passes list nothing, the inventory's provenance is
`PreRelease.inventory_provenance`'s, with no rung alternative. -/
@[req "DUR-21"]
theorem inventory_provenance_quiet {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Trace}
    {st : State} (hx : Execution lc r honest T st)
    (hn : ∀ p ∈ T, ∀ i env, p.2 = .fed (.process i env .ladderPass) → env.ladder = []) {x : Exp}
    (hm : x ∈ st.fed.parts) :
    x.signer ∈ st.fed.extracted ∨ (x.signer ∈ honest ∧ PreRelease.Emitted lc.pre r T x) :=
  PreRelease.inventory_provenance (to_pre hx hn) hm

/-- **No premature exposure on the composed run, with the rungs.** On a composed run whose fire passes carry
the base's verdict and whose ladder passes carry the computed release, every row of the partial inventory
whose signer's key is not in the cumulative extracted set was emitted by that signer's honest node at a fire
pass past the base's verdict or at a ladder pass as a released rung. -/
@[req "DUR-21"]
theorem recovery_no_premature_exposure {cfg : Recovery.Cfg} {lc : Ladder.Cfg} (hpc : lc.pre.sweep = cfg.sweep)
    {r : Rules} {honest : List Nat} {T : Recovery.Trace} {st : Recovery.St}
    (hx : Recovery.Execution cfg r honest T st) (hc : Checked lc (Recovery.sweepTrace T)) {x : Exp}
    (hm : x ∈ st.sw.fed.parts) (hs : x.signer ∉ st.sw.fed.extracted) :
    x.signer ∈ honest ∧ (PreRelease.Emitted lc.pre r (Recovery.sweepTrace T) x ∨
      EmittedRung lc r (Recovery.sweepTrace T) x) := by
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

/-- A schedule with each fire pass's verdict and each ladder pass's release written from the state and
history it is taken in. A schedule so filled may still be refused at any other step. -/
def fill (lc : Ladder.Cfg) (r : Rules) : Trace → State → List Step → List Step
  | _, _, [] => []
  | T, st, s :: ss =>
    let s' : Step := match s with
      | .fed (.process i env .firePass) =>
        .fed (.process i { env with withheld := PreRelease.failing lc.pre st T i } .firePass)
      | .fed (.process i env .ladderPass) =>
        .fed (.process i { env with ladder := listed lc st T i } .ladderPass)
      | s => s
    s' :: fill lc r ((st, s') :: T) (Sweep.apply r st s') ss

/-- A Bool form of `RungRelease.Checked`, for decided runs. -/
def checks (lc : Ladder.Cfg) : Trace → Bool
  | [] => true
  | (st, s) :: T => releaseOk lc st T s && checks lc T

theorem checked_of_checks (lc : Ladder.Cfg) : ∀ {T : Trace}, checks lc T = true → Checked lc T
  | [], _ => trivial
  | (_, _) :: _, h => by
    simp only [checks, Bool.and_eq_true] at h
    exact ⟨h.1, checked_of_checks lc h.2⟩

end BtcPolicy.RungRelease
