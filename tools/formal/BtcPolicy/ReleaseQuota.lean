import BtcPolicy.Retained
/-! `SPN-38`'s quota accounting for the base and the rungs above it, read off the release the ladder pass computes
(`DUR-27`, `NCH-23`). `Ladder.release` runs the cursor per candidate and returns the release state after the
pass and the rungs it lists; this module keeps, beside them, the interval `[F, U]` the cursor computed, and
derives from it what `SPN-38` meters. No definition changes and no kernel event is added.

**The account of one pass.** `ReleaseQuota.account` is `Ladder.release`'s own computation, match for match
(`ReleaseQuota.account_release`), with the cursor's interval kept even when every rung of it is refused.
`ReleaseQuota.consumed` is the interval's rung count `U + 1 − F` when the pass released at least one rung and
`0` otherwise: "Only a pass that released at least one rung MUST set `release_floor = U + 1`", and "If
`affordable_rungs = 0`, release nothing and advance no release bookkeeping on this pass". A pass that releases
a rung starts at `F = max(release_floor, a)`, lists the admissible rungs of `[F, U]`, sets the latch to the
verdict's rung and the floor to `U + 1`, and consumes at most `affordable_rungs` slots, so at most `rung_budget`
messages per input count (`ReleaseQuota.account_released`), for either anchor of the cap. A pass that releases
nothing keeps the release state and consumes nothing (`ReleaseQuota.account_quiet`). Every listed rung lies at
or above the floor before the pass and below the floor after it (`ReleaseQuota.account_mem`). Nothing here is
supplied: the interval is the one `Cursor.pass` computes from the attempt.

**The pass on the run.** `ReleaseQuota.passAccount` is the account the kernel's ladder pass acts on for one
candidate: none under `Kernel.PoisonGate.asserted` on a poisoned node, none for a candidate the kernel's gate
(`Kernel.ladderAt`: Escape role, not hot, due and authorized) leaves out, and otherwise `ReleaseQuota.account`
at the candidate's own read and release state (`RungRelease.readAt`). At a ladder pass `RungRelease.admits`
admits, the acting node's registry after the step is its registry with each record's release state replaced by
its account's and its `released` bit set when the account lists rung 0, and the step's effects are each record's
`Kernel.baseEffects` and `Kernel.rungEffects` of its account's rungs (`ReleaseQuota.pass_account`). For an Escape-role record, the effects under its commitment are exactly its own
(`ReleaseQuota.pass_under`): a listing pass is admitted only where the node's Escape-role ids are distinct, and
an empty list lists nothing for any record. With every rung above the base spending as many inputs as the base,
`CHN-16`'s ordered inputs, their number is at most `consumed × inputs_per_variant`, which is within
`rung_budget`, and a slot taken by rung 0 queues at most the base's one row at the ladder pass
(`ReleaseQuota.pass_count`); a pass
that releases nothing for a record keeps its release state and queues nothing under its commitment
(`ReleaseQuota.pass_nothing`). The same holds at a ladder pass of `LadderRelease`'s run and of the lifecycle run
(`ReleaseQuota.pass_account_ladder`, `ReleaseQuota.pass_account_life`). For one record at one pass, its interval,
the rows queued under its commitment, the slots it consumes and the floor it leaves are stated together in
`ReleaseQuota.pass_quota`, and on the lifecycle run in `ReleaseQuota.pass_quota_life`.

**Across a lifetime.** Under `Kernel.Rules.registration = .preserve` every honest node's ids stay distinct on
the run (`ReleaseQuota.ids_nodup_run`). Over a stretch of `LadderRelease.Execution` with no birth under `k` at
honest node `i` (`Lifecycle.births`), a rung listed for the record under `k` at a ladder pass of the stretch is
below every rung listed for it at a later ladder pass of the stretch (`ReleaseQuota.no_relist`): "rungs already
queued … MUST NOT be re-queued merely to reconstruct the prefix". A delivered partial adds no inventory row and
moves no record's registration-owned fields or release state (`ReleaseQuota.redelivery_keeps`): a partial
delivered again is not a release.

**The base under the account.** `SPN-38`'s released prefix starts at the base, rung 0, and the base obeys the same
account. At `LadderRelease`'s fire pass the account is an input the check binds (`LadderRelease.starvedAt`): a record
not yet released with no rung affordable, or with its floor past rung 0, is starved, and the fire pass queues only
the base rows of records with a rung affordable and the floor at 0, whose inputs then fit one pass's `rung_budget`
(`ReleaseQuota.fire_quota`). A fire pass that releases a base sets that record's floor past rung 0, its `U + 1`
with `U = 0` ("Only a pass that released at least one rung MUST set `release_floor = U + 1`"), so a later ladder pass's
interval starts above the base and spends no slot on it (`Exhibits.ReleaseQuota.fire_floor`). A ladder pass whose
account lists rung 0 queues the base row when the record is not yet released and marks it released
(`ReleaseQuota.ladder_base`). With `affordable_rungs = 0` a node sends nothing for that
candidate at either pass, base included, and moves none of its bookkeeping (`ReleaseQuota.starved_silent`,
`ReleaseQuota.starved_silent_life`). `RungRelease`'s run binds no account at its fire pass, so there the base is
still released outside it (`Exhibits.ReleaseQuota.base_separate`). What holds the base to one row is the `released`
bit both passes read and set: under `Registration.preserve`, once any pass of an honest node queues a base row
under a commitment (`ReleaseQuota.baseOut`), no later pass of that node in the same lifetime queues one
(`ReleaseQuota.base_once_paths`, and `ReleaseQuota.base_once` for fire passes), and one pass queues at most one
(`ReleaseQuota.baseOut_length`).

**Not established here.** The shared per-peer quota (`NCH-15`) across candidates and across the base and the
rungs (`Exhibits.ReleaseQuota.shared_peer`); retransmission schedules (`NCH-8`); the bytes on the wire. -/

namespace BtcPolicy.ReleaseQuota
open BtcPolicy.Kernel

/-! ## The account of one pass -/

/-- What one pass computes for one candidate: the cursor's interval `[F, U]` when it computed one, the rungs it
lists, and the release state after it. -/
structure Account where
  interval : Option (Nat × Nat)
  rungs : List Nat
  track : Track
  deriving DecidableEq, Repr

/-- The account of a pass that computes no interval and moves nothing. -/
def quiet (tr : Track) : Account := ⟨none, [], tr⟩

/-- `Ladder.after` with the cursor's interval kept: nothing on a failed verdict or an empty interval; on a
verdict releasing `k`, the interval `[F, U]` `SPN-38`'s pass gives with the latch at `k`, its admissible rungs,
and, when one is listed, the latch at `k` and the floor past the interval. -/
@[req "SPN-38"]
def afterAccount (cfg : Ladder.Cfg) (a : Ladder.Attempt) (inputs : Nat) (tr : Track) : Account :=
  match a.verdict with
  | .fail _ => quiet tr
  | .release k =>
    match Cursor.pass cfg.anchor cfg.quota inputs (Ladder.cursorOf a tr k) with
    | (none, _) => quiet tr
    | (some (F, U), c') =>
      if (Ladder.relOf a F U).isEmpty then ⟨some (F, U), [], tr⟩
      else ⟨some (F, U), Ladder.relOf a F U, { latch := k, floor := c'.floor }⟩

/-- One node's pass for one Escape, as `Ladder.release` computes it, with the interval kept. -/
@[req "SPN-38"]
def account (cfg : Ladder.Cfg) (rd : Ladder.Read) (c : Cand) (tr : Track) : Account :=
  match rd.ob with
  | none => quiet tr
  | some b => afterAccount cfg (Ladder.attempt cfg.pre rd b c tr.latch) c.tx.inputs.length tr

/-- The slots a pass consumes: the interval's rung count when it released at least one rung, else `0`. -/
@[req "SPN-38"]
def consumed (x : Account) : Nat :=
  match x.interval with
  | some (F, U) => if x.rungs.isEmpty then 0 else U + 1 - F
  | none => 0

/-- **The account is `Ladder.release`.** Its rungs and its release state are the ones `Ladder.release`
returns, for every read, candidate and release state: the interval is the cursor's own, not an input. -/
@[req "SPN-38"]
theorem account_release (cfg : Ladder.Cfg) (rd : Ladder.Read) (c : Cand) (tr : Track) :
    (account cfg rd c tr).rungs = (Ladder.release cfg rd c tr).2 ∧
      (account cfg rd c tr).track = (Ladder.release cfg rd c tr).1 := by
  unfold account Ladder.release
  cases rd.ob with
  | none => exact ⟨rfl, rfl⟩
  | some b =>
    simp only
    unfold afterAccount Ladder.after
    cases (Ladder.attempt cfg.pre rd b c tr.latch).verdict with
    | fail _ => exact ⟨rfl, rfl⟩
    | release k =>
      simp only
      cases Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length
          (Ladder.cursorOf (Ladder.attempt cfg.pre rd b c tr.latch) tr k) with
      | mk o c' =>
        cases o with
        | none => exact ⟨rfl, rfl⟩
        | some p =>
          obtain ⟨F, U⟩ := p
          simp only
          split <;> exact ⟨rfl, rfl⟩

/-- The cursor's interval is at most `affordable_rungs` wide, under either anchor of the cap, and a pass that
gives one has a rung affordable. -/
@[req "SPN-38"]
theorem pass_width {anchor : Cursor.Anchor} {q i : Nat} {c c' : Cursor.Candidate} {F U : Nat}
    (h : Cursor.pass anchor q i c = (some (F, U), c')) :
    U + 1 - F ≤ Cursor.affordableRungs q i ∧ Cursor.affordableRungs q i ≠ 0 := by
  unfold Cursor.pass at h
  cases hq : Cursor.quotaRungCap anchor q i c.floor c.a c.last with
  | none => rw [hq] at h; simp at h
  | some cap =>
    rw [hq] at h
    simp only at h
    split at h
    · simp at h
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      unfold Cursor.quotaRungCap at hq
      generalize hA : Cursor.affordableRungs q i = aff at hq ⊢
      by_cases haff : aff = 0
      · simp [haff] at hq
      · simp only [haff, if_false, Option.some.injEq] at hq
        refine ⟨?_, haff⟩
        subst hq
        cases anchor <;> simp only <;> omega

/-- The cursor's interval costs at most `rung_budget` per input count: `(U + 1 − F) × inputs ≤ rung_budget`,
under either anchor. -/
@[req "SPN-38"]
theorem pass_budget {anchor : Cursor.Anchor} {q i : Nat} {c c' : Cursor.Candidate} {F U : Nat}
    (h : Cursor.pass anchor q i c = (some (F, U), c')) : (U + 1 - F) * i ≤ Cursor.rungBudget q :=
  Nat.le_trans (Nat.mul_le_mul_right _ (pass_width h).1) (Nat.div_mul_le_self (Cursor.rungBudget q) i)

theorem mem_relOf {a : Ladder.Attempt} {F U m : Nat} (h : m ∈ Ladder.relOf a F U) : F ≤ m ∧ m ≤ U := by
  have hr := List.mem_range'_1.1 (List.mem_filter.1 h).1
  omega

theorem relOf_length (a : Ladder.Attempt) (F U : Nat) : (Ladder.relOf a F U).length ≤ U + 1 - F := by
  unfold Ladder.relOf
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- **A pass that releases a rung** (`SPN-38`). It had an observation and a verdict releasing `k`; its interval
is `[F, U]` with `F = max(release_floor, a)`, `F ≤ U ≤ k`; its rungs are the admissible ones of the interval;
the latch becomes `k` and the floor `U + 1`; it consumes `U + 1 − F` slots, at most `affordable_rungs`, and
their messages at the base's input count fit `rung_budget`. -/
@[req "SPN-38"]
theorem account_released {cfg : Ladder.Cfg} {rd : Ladder.Read} {c : Cand} {tr : Track}
    (h : (account cfg rd c tr).rungs ≠ []) :
    ∃ b k F U, rd.ob = some b ∧ (Ladder.attempt cfg.pre rd b c tr.latch).verdict = .release k ∧
      (account cfg rd c tr).interval = some (F, U) ∧
      F = max tr.floor (Ladder.lowest (Ladder.attempt cfg.pre rd b c tr.latch)) ∧ F ≤ U ∧ U ≤ k ∧
      (account cfg rd c tr).rungs = Ladder.relOf (Ladder.attempt cfg.pre rd b c tr.latch) F U ∧
      (account cfg rd c tr).track = { latch := k, floor := U + 1 } ∧
      consumed (account cfg rd c tr) = U + 1 - F ∧
      consumed (account cfg rd c tr) ≤ Cursor.affordableRungs cfg.quota c.tx.inputs.length ∧
      consumed (account cfg rd c tr) * c.tx.inputs.length ≤ Cursor.rungBudget cfg.quota := by
  revert h
  unfold account
  cases hb : rd.ob with
  | none => intro h; exact absurd rfl h
  | some b =>
    simp only
    unfold afterAccount
    cases hv : (Ladder.attempt cfg.pre rd b c tr.latch).verdict with
    | fail _ => intro h; exact absurd rfl h
    | release k =>
      simp only
      cases hp : Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length
          (Ladder.cursorOf (Ladder.attempt cfg.pre rd b c tr.latch) tr k) with
      | mk o c' =>
        cases o with
        | none => intro h; exact absurd rfl h
        | some p =>
          obtain ⟨F, U⟩ := p
          simp only
          split
          · intro h; exact absurd rfl h
          · rename_i hne
            intro _
            have hc := Ladder.cursor_some hp
            have hw := pass_width hp
            have hbud := pass_budget hp
            simp only [Ladder.cursorOf] at hc
            have hne' : (Ladder.relOf (Ladder.attempt cfg.pre rd b c tr.latch) F U).isEmpty = false := by
              simpa using hne
            refine ⟨b, k, F, U, rfl, hv, rfl, hc.1, hc.2.1, hc.2.2.1, rfl, ?_, ?_, ?_, ?_⟩
            · rw [hc.2.2.2]
            · simp [consumed, hne']
            · simp only [consumed, hne']; exact hw.1
            · simp only [consumed, hne']; exact hbud

/-- **A pass that releases nothing** keeps the release state and consumes nothing: no bookkeeping moves. -/
@[req "SPN-38"]
theorem account_quiet {cfg : Ladder.Cfg} {rd : Ladder.Read} {c : Cand} {tr : Track}
    (h : (account cfg rd c tr).rungs = []) :
    (account cfg rd c tr).track = tr ∧ consumed (account cfg rd c tr) = 0 := by
  obtain ⟨hr, ht⟩ := account_release cfg rd c tr
  refine ⟨?_, ?_⟩
  · rw [ht]; exact Retained.release_quiet cfg rd c tr (by rw [← hr]; exact h)
  · unfold consumed
    split <;> simp [h]

/-- **The base of "no re-release"** (`SPN-38`). Every rung a pass lists lies at or above the release floor
before the pass and below the floor after it. -/
@[req "SPN-38"]
theorem account_mem {cfg : Ladder.Cfg} {rd : Ladder.Read} {c : Cand} {tr : Track} {m : Nat}
    (h : m ∈ (account cfg rd c tr).rungs) : tr.floor ≤ m ∧ m < (account cfg rd c tr).track.floor := by
  obtain ⟨b, k, F, U, -, -, -, hF, -, -, hr, ht, -⟩ := account_released (List.ne_nil_of_mem h)
  rw [hr] at h
  have := mem_relOf h
  rw [ht]
  dsimp only
  omega

/-- "If `affordable_rungs = 0`, release nothing and advance no release bookkeeping on this pass": with no rung
affordable at the base's input count, the account computes no interval and moves nothing, at every read. -/
@[req "SPN-38"]
theorem account_zero {cfg : Ladder.Cfg} {rd : Ladder.Read} {c : Cand} {tr : Track}
    (h : Cursor.affordableRungs cfg.quota c.tx.inputs.length = 0) : account cfg rd c tr = quiet tr := by
  unfold account
  cases rd.ob with
  | none => rfl
  | some b =>
    simp only
    unfold afterAccount
    cases (Ladder.attempt cfg.pre rd b c tr.latch).verdict with
    | fail _ => rfl
    | release k =>
      simp only
      have hp : Cursor.pass cfg.anchor cfg.quota c.tx.inputs.length
          (Ladder.cursorOf (Ladder.attempt cfg.pre rd b c tr.latch) tr k) =
          (none, Ladder.cursorOf (Ladder.attempt cfg.pre rd b c tr.latch) tr k) := by
        simp [Cursor.pass, Cursor.quotaRungCap, h]
      rw [hp]

/-! ## The rows a release queues -/

/-- Whether an effect is a partial queued under commitment `k`. -/
def under (k : Nat) : Effect → Bool
  | .queuePartial _ _ _ c => c == k
  | .broadcast _ => false

/-- `Kernel.rungEffects` queues nothing for index 0, the base: a listed base's row is `Kernel.baseEffects`'. -/
@[req "NCH-23"]
theorem rungEffects_base (c : Cand) (ms : List Nat) :
    rungEffects c ms = rungEffects c (ms.filter (· != 0)) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    cases m with
    | zero => simp only [rungEffects, List.flatMap_cons, List.nil_append] at ih ⊢; simpa using ih
    | succ m =>
      have e : ((m + 1) :: ms).filter (· != 0) = (m + 1) :: ms.filter (· != 0) := by simp
      rw [e]
      simp only [rungEffects, List.flatMap_cons] at ih ⊢
      rw [ih]

/-- `NCH-23`'s "one message per released rung per signed input", counted: with every rung above the base
spending `n` inputs, a release of `ms` queues at most `n` rows per listed rung above the base. -/
@[req "NCH-23"]
theorem rungEffects_length (c : Cand) (ms : List Nat) (n : Nat) (hin : ∀ g ∈ c.above, g.tx.inputs.length = n) :
    (rungEffects c ms).length ≤ (ms.filter (· != 0)).length * n := by
  induction ms with
  | nil => simp [rungEffects]
  | cons m ms ih =>
    have e : rungEffects c (m :: ms) = rungEffects c [m] ++ rungEffects c ms := by
      simp [rungEffects, List.flatMap_cons]
    rw [e, List.length_append]
    cases m with
    | zero =>
      have : rungEffects c [0] = [] := by simp [rungEffects]
      rw [this]
      simpa using ih
    | succ m =>
      have hf : ((m + 1) :: ms).filter (· != 0) = (m + 1) :: ms.filter (· != 0) := by simp
      rw [hf, List.length_cons, Nat.succ_mul]
      have h1 : (rungEffects c [m + 1]).length ≤ n := by
        cases hg : c.above[m]? with
        | none => simp [rungEffects, hg]
        | some g =>
          simp [rungEffects, hg, hin g (List.mem_of_getElem? hg)]
      omega

theorem rungEffects_under (c : Cand) (ms : List Nat) (k : Nat) :
    (rungEffects c ms).filter (under k) = if c.id = k then rungEffects c ms else [] := by
  split
  · rename_i h
    apply List.filter_eq_self.2
    intro e he
    obtain ⟨-, -, -, -, -, -, rfl⟩ := mem_rungEffects he
    simp [under, h]
  · rename_i h
    apply List.filter_eq_nil_iff.2
    intro e he
    obtain ⟨-, -, -, -, -, -, rfl⟩ := mem_rungEffects he
    simp [under, h]

theorem baseEffects_under (c : Cand) (ms : List Nat) (k : Nat) :
    (baseEffects c ms).filter (under k) = if c.id = k then baseEffects c ms else [] := by
  unfold baseEffects
  by_cases h : c.id = k <;> cases (ms.contains 0 && !c.released) <;> simp [under, h]

/-- The rows a release queues for one record, base and rungs above it, picked out under one commitment: the
record's own when the commitment is its, and none otherwise. -/
theorem effects_under (c : Cand) (ms : List Nat) (k : Nat) :
    (baseEffects c ms ++ rungEffects c ms).filter (under k) =
      if c.id = k then baseEffects c ms ++ rungEffects c ms else [] := by
  rw [List.filter_append, baseEffects_under, rungEffects_under]
  by_cases h : c.id = k <;> simp [h]

theorem filter_flatMap {α β : Type} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap fun a => (f a).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.filter_append, ih]

theorem flatMap_filter {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap fun a => if p a then f a else [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- Over records with distinct ids, the rows picked out under one record's id are that record's own. -/
theorem flatMap_own {β : Type} {E : List Cand} (hn : (E.map Cand.id).Nodup) {c : Cand} (hc : c ∈ E)
    (g : Cand → List β) : (E.flatMap fun d => if d.id = c.id then g d else []) = g c := by
  induction E with
  | nil => cases hc
  | cons d E ih =>
    obtain ⟨hnd, hns⟩ := List.nodup_cons.1 hn
    rw [List.flatMap_cons]
    by_cases hd : d.id = c.id
    · have hcE : c ∉ E := fun h => hnd (by rw [hd]; exact List.mem_map_of_mem h)
      have hdc : d = c := by
        rcases List.mem_cons.1 hc with h | h
        · exact h.symm
        · exact absurd h hcE
      subst hdc
      have hrest : (E.flatMap fun d' => if d'.id = d.id then g d' else []) = [] := by
        apply List.flatMap_eq_nil_iff.2
        intro x hx
        have : x.id ≠ d.id := fun he => hnd (he ▸ List.mem_map_of_mem hx)
        simp [this]
      simp [hrest]
    · have hcE : c ∈ E := by
        rcases List.mem_cons.1 hc with h | h
        · exact absurd (h ▸ rfl) hd
        · exact h
      simp [hd, ih hns hcE]

/-! ## The pass on the run -/

/-- The account the kernel's ladder pass at node `i` acts on for candidate `c`, in state `st` after history `T`
at step environment `env`: none under `Kernel.PoisonGate.asserted` on a poisoned node, none for a candidate the
kernel's gate (`Kernel.ladderAt`) leaves out, and otherwise the account at its own read and release state. -/
@[req "SPN-38"]
def passAccount (lc : Ladder.Cfg) (r : Rules) (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (env : Env)
    (c : Cand) : Account :=
  if r.poison == .asserted && (st.fed.worlds i).node.poisoned then quiet c.track
  else if c.isEscape && !c.hot &&
      (due r env (st.fed.worlds i).node c && releaseAuthorized r (st.fed.worlds i).node c) then
    account lc (RungRelease.readAt st T i c) c c.track
  else quiet c.track

theorem passAccount_cases (lc : Ladder.Cfg) (r : Rules) (st : Sweep.State) (T : Sweep.Trace) (i : Nat)
    (env : Env) (c : Cand) :
    passAccount lc r st T i env c = quiet c.track ∨
      passAccount lc r st T i env c = account lc (RungRelease.readAt st T i c) c c.track := by
  unfold passAccount
  split
  · exact .inl rfl
  · split
    · exact .inr rfl
    · exact .inl rfl

/-- The ladder pass's list is the computed one. -/
theorem ladder_eq {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) :
    env.ladder = RungRelease.listed lc st T i := by
  simp only [RungRelease.admits, Bool.and_eq_true] at ha
  have h := ha.2
  simp only [RungRelease.releaseOk, RungRelease.ladderOk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- What the kernel's ladder pass reads for a resident on a node not poisoned under the gate is that record's
account: its release state and its rungs. -/
theorem ladderAt_account {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands)
    (hp : (r.poison == .asserted && (st.fed.worlds i).node.poisoned) = false) :
    ((ladderAt r env (st.fed.worlds i).node c).map (·.1)).getD c.track = (passAccount lc r st T i env c).track ∧
      ((ladderAt r env (st.fed.worlds i).node c).map (·.2)).getD [] = (passAccount lc r st T i env c).rungs := by
  cases hl : ladderAt r env (st.fed.worlds i).node c with
  | some p =>
    obtain ⟨tr, ms⟩ := p
    obtain ⟨h1, h2, h3, h4, hrel⟩ := RungRelease.ladderAt_own ha r hc hl
    have hpa : passAccount lc r st T i env c = account lc (RungRelease.readAt st T i c) c c.track := by
      simp [passAccount, hp, h1, h2, h3, h4]
    obtain ⟨hr, ht⟩ := account_release lc (RungRelease.readAt st T i c) c c.track
    rw [hpa, hr, ht, hrel]
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [Option.map_none, Option.getD_none]
    by_cases hg : (c.isEscape && !c.hot &&
        (due r env (st.fed.worlds i).node c && releaseAuthorized r (st.fed.worlds i).node c)) = true
    · have hpa : passAccount lc r st T i env c = account lc (RungRelease.readAt st T i c) c c.track := by
        simp only [passAccount, hp, Bool.false_eq_true, if_false, hg, if_true]
      have hf : env.ladder.find? (·.1 == c.id) = none := by
        unfold ladderAt at hl
        rw [if_pos hg] at hl
        cases hf : env.ladder.find? (·.1 == c.id) with
        | none => rfl
        | some e => rw [hf] at hl; simp at hl
      have hq : (Ladder.release lc (RungRelease.readAt st T i c) c c.track).2 = [] := by
        cases hq : (Ladder.release lc (RungRelease.readAt st T i c) c c.track).2 with
        | nil => rfl
        | cons m ms =>
          exfalso
          have hesc : c.isEscape = true := by
            simp only [Bool.and_eq_true] at hg; exact hg.1.1
          have hen : RungRelease.entry lc st T i c =
              some (c.id, Ladder.release lc (RungRelease.readAt st T i c) c c.track) := by
            unfold RungRelease.entry
            rw [if_pos (by simp [hesc, hq])]
          have hmem : (c.id, Ladder.release lc (RungRelease.readAt st T i c) c c.track) ∈ env.ladder := by
            rw [ladder_eq ha]
            exact List.mem_filterMap.2 ⟨c, hc, hen⟩
          have := List.find?_eq_none.1 hf _ hmem
          simp at this
      have hr := (account_release lc (RungRelease.readAt st T i c) c c.track).1
      rw [hq] at hr
      have ht := (account_quiet hr).1
      rw [hpa, ht, hr]
      exact ⟨rfl, rfl⟩
    · have hpa : passAccount lc r st T i env c = quiet c.track := by
        simp only [passAccount, hp, Bool.false_eq_true, if_false]
        rw [if_neg hg]
      rw [hpa]
      exact ⟨rfl, rfl⟩

/-- **The ladder pass is its accounts** (`SPN-38`, `DUR-27`). At a ladder pass `RungRelease.admits` admits, the
acting node's registry after the step is its registry with each record's release state replaced by its account's
and its `released` bit set when its account lists rung 0, and the step's effects are, record by record, the base
row `Kernel.baseEffects` queues for its account's rungs and the rows `Kernel.rungEffects` queues for them. -/
@[req "SPN-38"]
theorem pass_account {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules) :
    ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands =
        (st.fed.worlds i).node.cands.map (fun c =>
          { c with track := (passAccount lc r st T i env c).track,
                   released := c.released || (passAccount lc r st T i env c).rungs.contains 0 }) ∧
      (step r env (st.fed.worlds i) .ladderPass).2 =
        (st.fed.worlds i).node.cands.flatMap (fun c => baseEffects c (passAccount lc r st T i env c).rungs ++
          rungEffects c (passAccount lc r st T i env c).rungs) := by
  rw [Federation.apply_of_actor r _ _ rfl i, if_pos rfl]
  simp only [step, ladderPass]
  by_cases hp : (r.poison == .asserted && (st.fed.worlds i).node.poisoned) = true
  · rw [if_pos hp]
    have hq : ∀ c, passAccount lc r st T i env c = quiet c.track := by
      intro c; simp [passAccount, hp]
    refine ⟨?_, ?_⟩
    · simp only [hq, quiet, List.contains_nil, Bool.or_false]
      conv => lhs; rw [← List.map_id (st.fed.worlds i).node.cands]
      exact List.map_congr_left fun c _ => rfl
    · simp [hq, quiet, rungEffects, baseEffects]
  · rw [if_neg hp]
    have hp' : (r.poison == .asserted && (st.fed.worlds i).node.poisoned) = false := by simpa using hp
    refine ⟨?_, ?_⟩
    · exact List.map_congr_left fun c hc => by
        rw [(ladderAt_account ha r hc hp').1, (ladderAt_account ha r hc hp').2]
    · exact flatMap_congr' fun c hc => by rw [(ladderAt_account ha r hc hp').2]

/-- With an empty list a ladder pass lists nothing for any record. -/
theorem pass_rungs_nil {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules)
    (h0 : env.ladder = []) : ∀ c ∈ (st.fed.worlds i).node.cands, (passAccount lc r st T i env c).rungs = [] := by
  intro c hc
  by_cases hp : (r.poison == .asserted && (st.fed.worlds i).node.poisoned) = true
  · simp [passAccount, hp, quiet]
  · have hp' : (r.poison == .asserted && (st.fed.worlds i).node.poisoned) = false := by simpa using hp
    have := (ladderAt_account ha r hc hp').2
    have hl : ladderAt r env (st.fed.worlds i).node c = none := by simp [ladderAt, h0]
    rw [hl] at this
    exact this.symm

/-- A record outside the Escape role is never released for. -/
theorem pass_not_escape (lc : Ladder.Cfg) (r : Rules) (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (env : Env)
    {c : Cand} (h : c.isEscape = false) : passAccount lc r st T i env c = quiet c.track := by
  simp [passAccount, h]

/-- **A record's own rows** (`SPN-38`, `NCH-23`). At an admitted ladder pass, the rows queued under an
Escape-role record's commitment are exactly the ones its own account's rungs queue: the base row when its
account lists rung 0 and it is not yet released, and the rows of its listed rungs above the base. -/
@[req "SPN-38"]
theorem pass_under {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands) (hesc : c.isEscape = true) :
    (step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id) =
      baseEffects c (passAccount lc r st T i env c).rungs ++ rungEffects c (passAccount lc r st T i env c).rungs := by
  rw [(pass_account ha r).2, filter_flatMap]
  simp only [effects_under]
  by_cases h0 : env.ladder = []
  · have hn := pass_rungs_nil ha r h0
    have e0 : baseEffects c [] ++ rungEffects c [] = [] := by simp [baseEffects, rungEffects]
    rw [hn c hc, e0]
    apply List.flatMap_eq_nil_iff.2
    intro d hd
    rw [hn d hd]
    simp [rungEffects, baseEffects]
  · have hnd := RungRelease.escape_nodup ha h0
    have e1 : ((st.fed.worlds i).node.cands.flatMap fun d =>
        if d.id = c.id then baseEffects d (passAccount lc r st T i env d).rungs ++
          rungEffects d (passAccount lc r st T i env d).rungs else []) =
        ((st.fed.worlds i).node.cands.filter (·.isEscape)).flatMap fun d =>
          if d.id = c.id then baseEffects d (passAccount lc r st T i env d).rungs ++
            rungEffects d (passAccount lc r st T i env d).rungs else [] := by
      rw [flatMap_filter]
      apply flatMap_congr'
      intro d _
      cases hd : d.isEscape
      · simp [pass_not_escape lc r st T i env hd, quiet, rungEffects, baseEffects]
      · simp
    rw [e1]
    exact flatMap_own hnd (List.mem_filter.2 ⟨hc, hesc⟩) _

/-- **The quota on the rows** (`SPN-38`, `NCH-23`). At an admitted ladder pass, for an Escape-role record whose
rungs above the base each spend as many inputs as its base (`CHN-16`'s ordered inputs, the premise `hin`), the
rows queued under its commitment number at most `consumed × inputs_per_variant`, which is within `rung_budget`;
when rung 0 is listed, its slot is consumed by at most one queued row, the base's, which `Federation.fanout`
expands to one row per input: the rungs above it account for one slot fewer. -/
@[req "SPN-38"]
theorem pass_count {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands) (hesc : c.isEscape = true)
    (hin : ∀ g ∈ c.above, g.tx.inputs.length = c.tx.inputs.length) :
    ((step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id)).length ≤
        consumed (passAccount lc r st T i env c) * c.tx.inputs.length ∧
      consumed (passAccount lc r st T i env c) * c.tx.inputs.length ≤ Cursor.rungBudget lc.quota ∧
      (0 ∈ (passAccount lc r st T i env c).rungs →
        ((step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id)).length ≤
          (consumed (passAccount lc r st T i env c) - 1) * c.tx.inputs.length + 1) := by
  rw [pass_under ha r hc hesc]
  have hl := rungEffects_length c (passAccount lc r st T i env c).rungs c.tx.inputs.length hin
  have hcases := passAccount_cases lc r st T i env c
  generalize passAccount lc r st T i env c = x at hl hcases ⊢
  rcases hcases with hq | hq
  · subst hq; simp [quiet, consumed, rungEffects, baseEffects]
  · by_cases h0 : x.rungs = []
    · have h0' := h0
      rw [hq] at h0'
      have hz : consumed x = 0 := by rw [hq]; exact (account_quiet h0').2
      simp [h0, hz, rungEffects, baseEffects]
    · have h0' := h0
      rw [hq] at h0'
      obtain ⟨b, k, F, U, -, -, -, -, hFU, -, hr, -, hcons, hcaff, hbud⟩ := account_released h0'
      rw [← hq] at hr hcons hcaff hbud
      have hlen : x.rungs.length ≤ consumed x := by rw [hcons, hr]; exact relOf_length _ _ _
      have hC1 : 1 ≤ consumed x := by rw [hcons]; omega
      have hn1 : 1 ≤ c.tx.inputs.length := by
        apply Nat.pos_of_ne_zero
        intro hz
        rw [hz] at hcaff
        simp only [Cursor.affordableRungs, Nat.div_zero] at hcaff
        omega
      rw [List.length_append]
      refine ⟨?_, hbud, ?_⟩
      · by_cases hz : 0 ∈ x.rungs
        · have hlt : (x.rungs.filter (· != 0)).length < x.rungs.length :=
            List.length_filter_lt_length_iff_exists.2 ⟨0, hz, by simp⟩
          have hm : (x.rungs.filter (· != 0)).length * c.tx.inputs.length ≤
              (consumed x - 1) * c.tx.inputs.length := Nat.mul_le_mul_right _ (by omega)
          have hsum : (consumed x - 1) * c.tx.inputs.length + c.tx.inputs.length =
              consumed x * c.tx.inputs.length := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hC1]
          have hb1 : (baseEffects c x.rungs).length ≤ 1 := by
            rw [baseEffects_eq]; split <;> simp
          omega
        · have hb0 : (baseEffects c x.rungs).length = 0 := by rw [baseEffects_eq]; simp [hz]
          have hm : (x.rungs.filter (· != 0)).length * c.tx.inputs.length ≤ consumed x * c.tx.inputs.length :=
            Nat.mul_le_mul_right _ (Nat.le_trans (List.length_filter_le _ _) hlen)
          omega
      · intro hz
        have hlt : (x.rungs.filter (· != 0)).length < x.rungs.length :=
          List.length_filter_lt_length_iff_exists.2 ⟨0, hz, by simp⟩
        have hm : (x.rungs.filter (· != 0)).length * c.tx.inputs.length ≤
            (consumed x - 1) * c.tx.inputs.length := Nat.mul_le_mul_right _ (by omega)
        have hb1 : (baseEffects c x.rungs).length ≤ 1 := by
          rw [baseEffects_eq]; split <;> simp
        omega

/-- **A pass that releases nothing for a record** (`SPN-38`) keeps its release state and queues nothing under
its commitment, whatever the pass releases for other records. -/
@[req "SPN-38"]
theorem pass_nothing {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands) (hesc : c.isEscape = true)
    (h0 : (passAccount lc r st T i env c).rungs = []) :
    (passAccount lc r st T i env c).track = c.track ∧
      (step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id) = [] := by
  refine ⟨?_, by rw [pass_under ha r hc hesc, h0]; simp [baseEffects, rungEffects]⟩
  rcases passAccount_cases lc r st T i env c with hq | hq
  · rw [hq]; rfl
  · rw [hq] at h0 ⊢; exact (account_quiet h0).1

/-- Every rung a pass lists for a record lies at or above its floor before the pass and below its floor after. -/
@[req "SPN-38"]
theorem pass_mem {lc : Ladder.Cfg} {r : Rules} {st : Sweep.State} {T : Sweep.Trace} {i : Nat} {env : Env}
    {c : Cand} {m : Nat} (h : m ∈ (passAccount lc r st T i env c).rungs) :
    c.track.floor ≤ m ∧ m < (passAccount lc r st T i env c).track.floor := by
  rcases passAccount_cases lc r st T i env c with hq | hq <;> rw [hq] at h ⊢
  · simp [quiet] at h
  · exact account_mem h

/-- With no rung affordable at a record's input count, its pass lists nothing and moves nothing. -/
@[req "SPN-38"]
theorem pass_zero (lc : Ladder.Cfg) (r : Rules) (st : Sweep.State) (T : Sweep.Trace) (i : Nat) (env : Env)
    {c : Cand} (h : Cursor.affordableRungs lc.quota c.tx.inputs.length = 0) :
    passAccount lc r st T i env c = quiet c.track := by
  rcases passAccount_cases lc r st T i env c with hq | hq
  · exact hq
  · rw [hq, account_zero h]

/-- `ReleaseQuota.pass_account` at a ladder pass of `LadderRelease`'s run. -/
@[req "SPN-38"]
theorem pass_account_ladder {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : LadderRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules) :
    ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands =
        (st.fed.worlds i).node.cands.map (fun c =>
          { c with track := (passAccount lc r st T i env c).track,
                   released := c.released || (passAccount lc r st T i env c).rungs.contains 0 }) ∧
      (step r env (st.fed.worlds i) .ladderPass).2 =
        (st.fed.worlds i).node.cands.flatMap (fun c => baseEffects c (passAccount lc r st T i env c).rungs ++
          rungEffects c (passAccount lc r st T i env c).rungs) :=
  pass_account (LadderRelease.admits_ladder ha) r

/-- A ladder pass of the lifecycle run is admitted by `LadderRelease` at its sweep state and history. -/
theorem life_admits {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {st : Lifecycle.State}
    {T : Lifecycle.Trace} {b : Sweep.Step} (ha : Lifecycle.admits cfg r honest st T (.base b) = true) :
    LadderRelease.admits cfg.lc honest st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) b = true := by
  have h := (Lifecycle.admits_base ha).1
  simp only [ClassAssembly.admits, Bool.and_eq_true] at h
  exact h.1

/-- `ReleaseQuota.pass_account` at a ladder pass of the lifecycle run. -/
@[req "SPN-38"]
theorem pass_account_life {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {st : Lifecycle.State}
    {T : Lifecycle.Trace} {i : Nat} {env : Env}
    (ha : Lifecycle.admits cfg r honest st T (.base (.fed (.process i env .ladderPass))) = true) :
    ((Federation.apply r st.cs.sw.fed (.process i env .ladderPass)).worlds i).node.cands =
        (st.cs.sw.fed.worlds i).node.cands.map (fun c =>
          { c with track := (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).track,
                   released := c.released ||
              (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs.contains 0 }) ∧
      (step r env (st.cs.sw.fed.worlds i) .ladderPass).2 =
        (st.cs.sw.fed.worlds i).node.cands.flatMap (fun c =>
          baseEffects c (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs ++
            rungEffects c (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs) :=
  pass_account_ladder (life_admits ha) r

/-- **One ladder pass for one record, whole** (`SPN-38`, `NCH-23`). At a ladder pass `RungRelease.admits` admits,
for an Escape-role record whose variants above the base spend as many inputs as its base (the premise `hin`):
when the pass lists rungs for it, its interval `[F, U]` is the computed one (`F = max(release_floor, a)`,
`F ≤ U ≤ k`, the rungs the admissible ones of the interval), the effects queued under its commitment are the base's
row when the rungs include 0 and the record is not yet released (`Kernel.baseEffects`), then the ones
`Kernel.rungEffects` queues for the rungs above the base, and number at most
`consumed × inputs_per_variant ≤ rung_budget`, with `consumed = U + 1 − F ≤ affordable_rungs`, and the record after
the step carries latch `k` and floor `U + 1`, and is marked released when the rungs include 0;
when the pass lists nothing, the record keeps its release state, consumes nothing and queues no row. -/
@[req "SPN-38"]
theorem pass_quota {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands) (hesc : c.isEscape = true)
    (hin : ∀ g ∈ c.above, g.tx.inputs.length = c.tx.inputs.length) :
    ((passAccount lc r st T i env c).rungs ≠ [] →
      ∃ b k F U, (RungRelease.readAt st T i c).ob = some b ∧
        (Ladder.attempt lc.pre (RungRelease.readAt st T i c) b c c.track.latch).verdict = .release k ∧
        (passAccount lc r st T i env c).interval = some (F, U) ∧
        F = max c.track.floor
          (Ladder.lowest (Ladder.attempt lc.pre (RungRelease.readAt st T i c) b c c.track.latch)) ∧
        F ≤ U ∧ U ≤ k ∧
        (passAccount lc r st T i env c).rungs =
          Ladder.relOf (Ladder.attempt lc.pre (RungRelease.readAt st T i c) b c c.track.latch) F U ∧
        (step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id) =
          baseEffects c (passAccount lc r st T i env c).rungs ++
            rungEffects c (passAccount lc r st T i env c).rungs ∧
        ((step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id)).length ≤
          consumed (passAccount lc r st T i env c) * c.tx.inputs.length ∧
        consumed (passAccount lc r st T i env c) * c.tx.inputs.length ≤ Cursor.rungBudget lc.quota ∧
        consumed (passAccount lc r st T i env c) = U + 1 - F ∧
        consumed (passAccount lc r st T i env c) ≤ Cursor.affordableRungs lc.quota c.tx.inputs.length ∧
        (passAccount lc r st T i env c).track = { latch := k, floor := U + 1 } ∧
        { c with track := { latch := k, floor := U + 1 },
                 released := c.released || (passAccount lc r st T i env c).rungs.contains 0 } ∈
          ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands) ∧
    ((passAccount lc r st T i env c).rungs = [] →
      (passAccount lc r st T i env c).track = c.track ∧ consumed (passAccount lc r st T i env c) = 0 ∧
        (step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id) = [] ∧
        c ∈ ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands) := by
  have hu := pass_under ha r hc hesc
  have hcnt := pass_count ha r hc hesc hin
  have hpost : { c with track := (passAccount lc r st T i env c).track,
                         released := c.released || (passAccount lc r st T i env c).rungs.contains 0 } ∈
      ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands := by
    rw [(pass_account ha r).1]
    exact List.mem_map.2 ⟨c, hc, rfl⟩
  refine ⟨fun hne => ?_, fun h0 => ?_⟩
  · have hq : passAccount lc r st T i env c = account lc (RungRelease.readAt st T i c) c c.track := by
      rcases passAccount_cases lc r st T i env c with hq | hq
      · exact absurd (by rw [hq]; rfl) hne
      · exact hq
    have hne' := hne
    rw [hq] at hne'
    obtain ⟨b, k, F, U, hb, hv, hI, hF, hFU, hUk, hr, ht, hc1, hc2, hc3⟩ := account_released hne'
    rw [← hq] at hI hr ht hc1 hc2 hc3
    rw [ht] at hpost
    exact ⟨b, k, F, U, hb, hv, hI, hF, hFU, hUk, hr, hu, hcnt.1, hcnt.2.1, hc1, hc2, ht, hpost⟩
  · obtain ⟨ht, hf⟩ := pass_nothing ha r hc hesc h0
    have hz : consumed (passAccount lc r st T i env c) = 0 := by
      rcases passAccount_cases lc r st T i env c with hq | hq
      · rw [hq]; rfl
      · rw [hq] at h0 ⊢; exact (account_quiet h0).2
    rw [ht, h0] at hpost
    simp only [List.contains_nil, Bool.or_false] at hpost
    exact ⟨ht, hz, hf, hpost⟩

/-- `ReleaseQuota.pass_quota` at a ladder pass of the lifecycle run. -/
@[req "SPN-38"]
theorem pass_quota_life {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {st : Lifecycle.State}
    {T : Lifecycle.Trace} {i : Nat} {env : Env}
    (ha : Lifecycle.admits cfg r honest st T (.base (.fed (.process i env .ladderPass))) = true)
    {c : Cand} (hc : c ∈ (st.cs.sw.fed.worlds i).node.cands) (hesc : c.isEscape = true)
    (hin : ∀ g ∈ c.above, g.tx.inputs.length = c.tx.inputs.length) :
    ((passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs ≠ [] →
      ∃ b k F U, (RungRelease.readAt st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i c).ob = some b ∧
        (Ladder.attempt cfg.lc.pre (RungRelease.readAt st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i c) b c
          c.track.latch).verdict = .release k ∧
        (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).interval = some (F, U) ∧
        F = max c.track.floor (Ladder.lowest (Ladder.attempt cfg.lc.pre
          (RungRelease.readAt st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i c) b c c.track.latch)) ∧
        F ≤ U ∧ U ≤ k ∧
        (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs =
          Ladder.relOf (Ladder.attempt cfg.lc.pre
            (RungRelease.readAt st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i c) b c c.track.latch) F U ∧
        (step r env (st.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id) =
          baseEffects c (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs ++
            rungEffects c (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs ∧
        ((step r env (st.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id)).length ≤
          consumed (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c) *
            c.tx.inputs.length ∧
        consumed (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c) *
          c.tx.inputs.length ≤ Cursor.rungBudget cfg.lc.quota ∧
        consumed (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c) = U + 1 - F ∧
        consumed (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c) ≤
          Cursor.affordableRungs cfg.lc.quota c.tx.inputs.length ∧
        (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).track =
          { latch := k, floor := U + 1 } ∧
        { c with track := { latch := k, floor := U + 1 },
                 released := c.released ||
                   (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs.contains 0 } ∈
          ((Federation.apply r st.cs.sw.fed (.process i env .ladderPass)).worlds i).node.cands) ∧
    ((passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).rungs = [] →
      (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c).track = c.track ∧
        consumed (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env c) = 0 ∧
        (step r env (st.cs.sw.fed.worlds i) .ladderPass).2.filter (under c.id) = [] ∧
        c ∈ ((Federation.apply r st.cs.sw.fed (.process i env .ladderPass)).worlds i).node.cands) :=
  pass_quota (LadderRelease.admits_ladder (life_admits ha)) r hc hesc hin

/-! ## Across a lifetime -/

/-- **Distinct ids on the run** (`SPN-32`). Under `Registration.preserve`, at every state of `LadderRelease`'s
run each honest node's resident ids are distinct: `Kernel.ids_nodup_step` at each of its own steps. -/
@[req "SPN-32"]
theorem ids_nodup_run {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hr : r.registration = .preserve) (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest) :
    ((st.fed.worlds i).node.cands.map Cand.id).Nodup := by
  induction hx with
  | init st h => rw [(h.1.2.2 i hi).2.2.2.1]; exact List.nodup_nil
  | next s ha _ ih =>
    cases s with
    | chain b => exact ih
    | observe j b => exact ih
    | fed fs =>
      show (((Federation.apply r _ fs).worlds i).node.cands.map Cand.id).Nodup
      cases hact : Federation.actor fs with
      | none => rw [Federation.apply_no_actor r _ fs hact i]; exact ih
      | some a =>
        obtain ⟨j, env, e⟩ := a
        rw [Federation.apply_of_actor r _ fs hact i]
        by_cases hij : i = j
        · rw [if_pos hij]; subst hij; exact Kernel.ids_nodup_step hr env _ e ih
        · rw [if_neg hij]; exact ih

/-- From a step of the run onward: the step was admitted at its own state and history, which the run reached,
and over the steps after it, none of which births a record under `k` at honest node `i`, every record under `k`
at the end descends from one right after the step with the same registration-owned fields and a floor no
higher. -/
theorem lifetime_after {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest) {k : Nat}
    {T₁ T₂ : Sweep.Trace} {st₁ : Sweep.State} {s₁ : Sweep.Step} (hT : T = T₂ ++ (st₁, s₁) :: T₁)
    (hb : ∀ y ∈ T₂, Lifecycle.births r y.1 y.2 i k = false) :
    LadderRelease.Execution lc r honest T₁ st₁ ∧ LadderRelease.admits lc honest st₁ T₁ s₁ = true ∧
      ∀ c ∈ (st.fed.worlds i).node.cands, c.id = k →
        ∃ d ∈ ((Sweep.apply r st₁ s₁).fed.worlds i).node.cands, Retained.reg d = Retained.reg c ∧
          d.track.floor ≤ c.track.floor := by
  induction hx generalizing T₂ with
  | init st h => cases T₂ <;> simp at hT
  | @next T st s ha hx' ih =>
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hT
      exact ⟨hx', ha, fun c hc _ => ⟨c, hc, rfl, Nat.le_refl _⟩⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      obtain ⟨hx₁, ha₁, hanc⟩ := ih hT (fun z hz => hb z (List.mem_cons_of_mem _ hz))
      refine ⟨hx₁, ha₁, fun c hc hk => ?_⟩
      obtain ⟨d, hd, h1, h2, -⟩ := Retained.life_step hx' hi ha (hb _ List.mem_cons_self) c hc hk
      obtain ⟨e, he, g1, g2⟩ := hanc d hd (by rw [(Retained.reg_eq h1).1]; exact hk)
      exact ⟨e, he, g1.trans h1, Nat.le_trans g2 h2⟩

/-- **No rung is listed twice in a lifetime** (`SPN-38`: "rungs already queued … MUST NOT be re-queued merely to
reconstruct the prefix"). On `LadderRelease`'s run under `Registration.preserve`, take a ladder pass of honest
node `i` and the steps after it, none of which births a record under `k` at `i`. A rung listed for the record
under `k` at that pass is below every rung the account at the state reached lists for a record under `k`, at
any environment: so at a ladder pass the run takes there, whose rows are that account's
(`ReleaseQuota.pass_account`), no rung listed at the earlier pass is listed again. -/
@[req "SPN-38"]
theorem no_relist {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hr : r.registration = .preserve) (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest)
    {k : Nat} {T₁ T₂ : Sweep.Trace} {st₁ : Sweep.State} {env₁ : Env}
    (hT : T = T₂ ++ (st₁, .fed (.process i env₁ .ladderPass)) :: T₁)
    (hb : ∀ y ∈ T₂, Lifecycle.births r y.1 y.2 i k = false)
    {c₁ : Cand} (hc₁ : c₁ ∈ (st₁.fed.worlds i).node.cands) (hk₁ : c₁.id = k) {m : Nat}
    (hm : m ∈ (passAccount lc r st₁ T₁ i env₁ c₁).rungs)
    {env₂ : Env} {c₂ : Cand} (hc₂ : c₂ ∈ (st.fed.worlds i).node.cands) (hk₂ : c₂.id = k) {m' : Nat}
    (hm' : m' ∈ (passAccount lc r st T i env₂ c₂).rungs) : m < m' := by
  obtain ⟨hx₁, ha₁, hanc⟩ := lifetime_after hx hi hT hb
  obtain ⟨d, hd, hreg, hfl⟩ := hanc c₂ hc₂ hk₂
  have hcands := (pass_account (LadderRelease.admits_ladder ha₁) r).1
  have hd' : d ∈ ((Federation.apply r st₁.fed (.process i env₁ .ladderPass)).worlds i).node.cands := hd
  rw [hcands] at hd'
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hd'
  have hid : c₀.id = c₁.id := by
    have := (Retained.reg_eq hreg).1
    simp only at this
    rw [this, hk₂, hk₁]
  have hc01 : c₀ = c₁ := Kernel.eq_of_mem_ids_nodup (ids_nodup_run hr hx₁ hi) hc₀ hc₁ hid
  subst hc01
  have h1 := (pass_mem hm).2
  have h2 := (pass_mem hm').1
  simp only at hfl
  omega

/-- `ReleaseQuota.no_relist` on the lifecycle run, through `Lifecycle.to_ladder`. -/
@[req "SPN-38"]
theorem life_no_relist {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace}
    {st : Lifecycle.State} (hr : r.registration = .preserve) (hx : Lifecycle.Execution cfg r honest T st)
    {i : Nat} (hi : i ∈ honest) {k : Nat} {T₁ T₂ : Sweep.Trace} {st₁ : Sweep.State} {env₁ : Env}
    (hT : ClassAssembly.sweepT (Lifecycle.toL T) = T₂ ++ (st₁, .fed (.process i env₁ .ladderPass)) :: T₁)
    (hb : ∀ y ∈ T₂, Lifecycle.births r y.1 y.2 i k = false)
    {c₁ : Cand} (hc₁ : c₁ ∈ (st₁.fed.worlds i).node.cands) (hk₁ : c₁.id = k) {m : Nat}
    (hm : m ∈ (passAccount cfg.lc r st₁ T₁ i env₁ c₁).rungs) {env₂ : Env}
    {c₂ : Cand} (hc₂ : c₂ ∈ (st.cs.sw.fed.worlds i).node.cands) (hk₂ : c₂.id = k) {m' : Nat}
    (hm' : m' ∈ (passAccount cfg.lc r st.cs.sw (ClassAssembly.sweepT (Lifecycle.toL T)) i env₂ c₂).rungs) :
    m < m' :=
  no_relist hr (Lifecycle.to_ladder hx) hi hT hb hc₁ hk₁ hm hc₂ hk₂ hm'

/-- **Redelivery is not a release** (`SPN-38`: "The cursor records that a rung has been queued for transport, not
that a peer received it"). A delivered partial adds no row to the partial inventory and leaves every record of
every node with its registration-owned fields and release state. -/
@[req "SPN-38"]
theorem redelivery_keeps (r : Rules) (st : Sweep.State) (i : Nat) (env : Env) (x : Exp) :
    (Sweep.apply r st (.fed (.deliverPartial i env x))).fed.parts = st.fed.parts ∧
      ∀ j, ((Sweep.apply r st (.fed (.deliverPartial i env x))).fed.worlds j).node.cands.map
          (fun c => (Retained.reg c, c.track)) =
        (st.fed.worlds j).node.cands.map (fun c => (Retained.reg c, c.track)) := by
  refine ⟨rfl, fun j => ?_⟩
  show ((Federation.apply r st.fed (.deliverPartial i env x)).worlds j).node.cands.map _ = _
  rw [Federation.apply_of_actor r _ _ rfl j]
  by_cases hji : j = i
  · rw [if_pos hji]
    subst hji
    simp only [step, receivePartial, List.map_map]
    apply List.map_congr_left
    intro c _
    simp only [Function.comp]
    split <;> rfl
  · rw [if_neg hji]

/-! ## The base held to one row -/

theorem withWindow_released (r : Rules) (sel : List (Nat × Bool)) (T : Clocks.Wall) (slack : Clocks.Secs)
    (c : Cand) : (withWindow r sel T slack c).released = c.released := by
  unfold withWindow; split <;> rfl

/-- **One kernel step and the `released` bit.** Each record after it is one before it with the same id whose
`released` bit it does not clear, or the step leaves more records under its id than before. -/
theorem step_released (r : Rules) (env : Env) (w : World) (e : Event) {c : Cand}
    (hc : c ∈ (step r env w e).1.node.cands) :
    (∃ d ∈ w.node.cands, d.id = c.id ∧ (d.released = true → c.released = true)) ∨
      w.node.cands.countP (·.id == c.id) < (step r env w e).1.node.cands.countP (·.id == c.id) := by
  have keep (h : c ∈ w.node.cands) : ∃ d ∈ w.node.cands, d.id = c.id ∧ (d.released = true → c.released = true) :=
    ⟨c, h, rfl, id⟩
  have frame (f : Cand → Cand) (hf : ∀ d, (f d).id = d.id ∧ (d.released = true → (f d).released = true))
      (h : c ∈ w.node.cands.map f) :
      ∃ d ∈ w.node.cands, d.id = c.id ∧ (d.released = true → c.released = true) := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    exact ⟨d, hd, (hf d).1.symm, (hf d).2⟩
  cases e with
  | accept cid dd E sp es =>
    revert hc
    simp only [step, accept]
    split
    · intro hc; exact .inl (keep (by simpa using hc))
    · split
      · intro hc; exact .inl (keep hc)
      · have born_case (f : Cand → Cand) (hf : ∀ d, (f d).id = d.id ∧ (f d).released = d.released)
            (hcm : c ∈ (register r w.node env sp es).map f) :
            (∃ d ∈ w.node.cands, d.id = c.id ∧ (d.released = true → c.released = true)) ∨
              w.node.cands.countP (·.id == c.id) <
                ((register r w.node env sp es).map f).countP (·.id == c.id) := by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hcm
          unfold register at hx ⊢
          split at hx
          · exact .inl ⟨x, hx, (hf x).1.symm, fun h => by rw [(hf x).2]; exact h⟩
          · rename_i hreg
            simp only [hreg]
            rcases List.mem_cons.1 hx with rfl | hx'
            · refine .inr ?_
              rw [(hf _).1]
              exact Retained.countP_lt (pre := [_, _]) (fun d => (hf d).1) (List.mem_cons_self ..)
            rcases List.mem_cons.1 hx' with rfl | hx''
            · refine .inr ?_
              rw [(hf _).1]
              exact Retained.countP_lt (pre := [_, _]) (fun d => (hf d).1)
                (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            · exact .inl ⟨x, hx'', (hf x).1.symm, fun h => by rw [(hf x).2]; exact h⟩
        split
        · intro hc
          exact born_case _ (fun d => ⟨withWindow_id .., withWindow_released ..⟩) hc
        · intro hc
          have hc' : c ∈ (register r w.node env sp es).map id := by simpa using hc
          rcases born_case id (fun d => ⟨rfl, rfl⟩) hc' with h | h
          · exact .inl h
          · right; simpa using h
  | receipt cid s =>
    refine .inl ?_
    simp only [step, receipt] at hc
    split at hc
    · exact keep hc
    · split at hc
      · exact keep hc
      · split at hc
        · simp only [holderDecision] at hc
          exact frame _ (fun d => ⟨by rw [withWindow_id], by rw [withWindow_released]; exact id⟩) hc
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
    · exact frame _ (fun d => by split <;> (try split) <;> first | exact ⟨rfl, fun _ => rfl⟩ | exact ⟨rfl, id⟩) hc
  | ladderPass =>
    refine .inl ?_
    simp only [step, ladderPass] at hc
    split at hc
    · exact keep hc
    · exact frame (fun d =>
          { d with track := ((ladderAt r env w.node d).map (·.1)).getD d.track,
                   released := d.released || (((ladderAt r env w.node d).map (·.2)).getD []).contains 0 })
        (fun d => ⟨rfl, fun h => by simp [h]⟩) hc
  | packageAccepted cid =>
    simp only [step, packageAccepted] at hc
    exact .inl (frame _ (fun d => by split <;> exact ⟨rfl, id⟩) hc)
  | send cid =>
    simp only [step, send] at hc
    split at hc
    · exact .inl (keep hc)
    · exact .inl (frame _ (fun d => by split <;> exact ⟨rfl, id⟩) hc)
  | settle tx =>
    refine .inl ?_
    simp only [step, settle] at hc
    split at hc
    · exact keep hc
    · exact frame _ (fun d => by split <;> (try split) <;> exact ⟨rfl, id⟩) hc
  | prune => exact .inl (keep (List.mem_filter.1 hc).1)
  | tick | panic | adversaryExposes _ _ _ _ => exact .inl (keep hc)
  | receivePartial m i s cid' =>
    exact .inl (frame _ (fun d => by split <;> exact ⟨rfl, id⟩) hc)
  | clawback x =>
    have hc' : c ∈ (clawback env w.node x).cands := by simpa [step] using hc
    rcases mem_clawback hc' with hc | ⟨rfl, hl, hn⟩
    · exact .inl (keep hc)
    · refine .inr ?_
      have e : (step r env w (.clawback x)).1.node.cands =
          ([clawbackBorn w.node.id w.node.combineSlack env x] ++ w.node.cands).map id := by
        simp only [step, clawback, hl, Bool.false_or, List.map_id, List.singleton_append]
        have : w.node.cands.any (·.id == x.id) = false := by
          simpa using fun a ha => hn a ha
        simp [this]
      rw [e]
      exact Retained.countP_lt (fun d => rfl) (List.mem_singleton_self _)

/-- One step of the run, at node `i`: each record after it is one before it with the same id whose `released`
bit it does not clear, or the step births a record under its id there. -/
theorem sweep_released (r : Rules) (st : Sweep.State) (s : Sweep.Step) (i : Nat) {c : Cand}
    (hc : c ∈ ((Sweep.apply r st s).fed.worlds i).node.cands) :
    (∃ d ∈ (st.fed.worlds i).node.cands, d.id = c.id ∧ (d.released = true → c.released = true)) ∨
      Lifecycle.births r st s i c.id = true := by
  cases s with
  | chain b => exact .inl ⟨c, hc, rfl, id⟩
  | observe j b => exact .inl ⟨c, hc, rfl, id⟩
  | fed fs =>
    have hc' : c ∈ ((Federation.apply r st.fed fs).worlds i).node.cands := hc
    cases hact : Federation.actor fs with
    | none =>
      rw [Federation.apply_no_actor r _ fs hact i] at hc'
      exact .inl ⟨c, hc', rfl, id⟩
    | some a =>
      obtain ⟨j, env, e⟩ := a
      have hw := Federation.apply_of_actor r st.fed fs hact i
      rw [hw] at hc'
      split at hc'
      · rename_i hij
        subst hij
        rcases step_released r env _ e hc' with h | h
        · exact .inl h
        · refine .inr ?_
          unfold Lifecycle.births
          apply decide_eq_true
          unfold Lifecycle.countAt
          simp only [Sweep.apply]
          rw [hw, if_pos rfl]
          exact h
      · exact .inl ⟨c, hc', rfl, id⟩

/-- Over the steps after a step of the run, none of which births a record under `k` at node `i`, every record
under `k` at the end descends from one under `k` right after the step whose `released` bit it does not clear. -/
theorem released_after {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hx : LadderRelease.Execution lc r honest T st) {i k : Nat} {T₁ T₂ : Sweep.Trace} {st₁ : Sweep.State}
    {s₁ : Sweep.Step} (hT : T = T₂ ++ (st₁, s₁) :: T₁) (hb : ∀ y ∈ T₂, Lifecycle.births r y.1 y.2 i k = false) :
    ∀ c ∈ (st.fed.worlds i).node.cands, c.id = k →
      ∃ d ∈ ((Sweep.apply r st₁ s₁).fed.worlds i).node.cands, d.id = k ∧ (d.released = true → c.released = true) := by
  induction hx generalizing T₂ with
  | init st h => cases T₂ <;> simp at hT
  | @next T st s ha hx' ih =>
    cases T₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hT
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hT
      exact fun c hc hk => ⟨c, hc, hk, id⟩
    | cons y T₂ =>
      simp only [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT⟩ := hT
      intro c hc hk
      rcases sweep_released r st s i hc with ⟨d, hd, h1, h2⟩ | h
      · obtain ⟨e, he, g1, g2⟩ :=
          ih hT (fun z hz => hb z (List.mem_cons_of_mem _ hz)) d hd (by rw [h1, hk])
        exact ⟨e, he, g1, fun h => h2 (g2 h)⟩
      · have := hb _ List.mem_cons_self
        simp only at this
        rw [hk] at h
        rw [h] at this
        cases this

/-- A fire pass that queues a row under commitment `k`, at a node whose ids are distinct, leaves the record under
`k` with its `released` bit set. -/
theorem firePass_marks {r : Rules} {env : Env} {n : Node} (hn : (n.cands.map Cand.id).Nodup) {eff : Effect}
    (he : eff ∈ (firePass r env n).2) {k : Nat} (hk : under k eff = true) :
    ∀ d ∈ (firePass r env n).1.cands, d.id = k → d.released = true := by
  obtain ⟨c, hc, hdue, hauth, hw, hs, -, rfl⟩ := firePass_effect_fed r env n he
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
    by_cases hr : d₀.released = true <;> simp [hdue, hauth, hw, hs, hr]

/-- **The base row at most once in a lifetime** (`SPN-36`'s `released`). On `LadderRelease`'s run under
`Registration.preserve`, once a fire pass of honest node `i` queues a row under commitment `k`, no fire pass of
`i` after it queues one, over every stretch of steps none of which births a record under `k` at `i`, at every
environment. The `released` bit, which a ladder pass listing rung 0 sets too, is what holds the base to one row
(`ReleaseQuota.base_once_paths` for both passes). -/
@[req "SPN-38"]
theorem base_once {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hr : r.registration = .preserve) (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest)
    {k : Nat} {T₁ T₂ : Sweep.Trace} {st₁ : Sweep.State} {env₁ : Env}
    (hT : T = T₂ ++ (st₁, .fed (.process i env₁ .firePass)) :: T₁)
    (hb : ∀ y ∈ T₂, Lifecycle.births r y.1 y.2 i k = false)
    (h₁ : (step r env₁ (st₁.fed.worlds i) .firePass).2.filter (under k) ≠ []) (env₂ : Env) :
    (step r env₂ (st.fed.worlds i) .firePass).2.filter (under k) = [] := by
  obtain ⟨hx₁, -, -⟩ := lifetime_after hx hi hT hb
  obtain ⟨eff, hm⟩ := List.exists_mem_of_ne_nil _ h₁
  obtain ⟨he, hu⟩ := List.mem_filter.1 hm
  have hmark := firePass_marks (ids_nodup_run hr hx₁ hi) he hu
  apply List.filter_eq_nil_iff.2
  intro eff₂ he₂ hu₂
  obtain ⟨c, hc, -, -, -, hrel, rfl⟩ := firePass_effect r env₂ _ he₂
  have hck : c.id = k := by simpa [under] using hu₂
  obtain ⟨d, hd, hdk, hdr⟩ := released_after hx hT hb c hc hck
  have hd' : d ∈ (firePass r env₁ (st₁.fed.worlds i).node).1.cands := by
    have h := hd
    change d ∈ ((Federation.apply r st₁.fed (.process i env₁ .firePass)).worlds i).node.cands at h
    rw [Federation.apply_of_actor r _ _ rfl i, if_pos rfl] at h
    exact h
  have := hdr (hmark d hd' hdk)
  rw [hrel] at this
  cases this

/-! ## The base under the account -/

/-- **The base under the account at the fire pass** (`SPN-38`). At a fire pass `LadderRelease.admits` admits,
every row the pass queues is the base row of a resident record not yet released, whose release floor is at
rung 0 and which has a rung affordable at its input count (`LadderRelease.starvedAt`); so its inputs fit one
pass's `rung_budget`, and the base's rows, one per input once fanned out, are within the budget `SPN-38` meters. -/
@[req "SPN-38"]
theorem fire_quota {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : LadderRelease.admits lc honest st T (.fed (.process i env .firePass)) = true) (r : Rules)
    {eff : Effect} (he : eff ∈ (step r env (st.fed.worlds i) .firePass).2) :
    ∃ c ∈ (st.fed.worlds i).node.cands, c.released = false ∧ c.track.floor = 0 ∧
      Cursor.affordableRungs lc.quota c.tx.inputs.length ≠ 0 ∧
      c.tx.inputs.length ≤ Cursor.rungBudget lc.quota ∧
      eff = .queuePartial (sighash c.tx 0) 0 c.hot c.id := by
  obtain ⟨c, hc, -, -, -, hs, hrel, rfl⟩ := firePass_effect_fed r env _ he
  have hst := (LadderRelease.fire_env ha).2
  have hnot : ¬ (Cursor.affordableRungs lc.quota c.tx.inputs.length = 0 ∨ c.track.floor ≠ 0) := by
    intro h
    have hm : c.id ∈ LadderRelease.starvedAt lc st T i :=
      (LadderRelease.starved_iff lc st T i c.id).2 ⟨c, hc, rfl, hrel, h⟩
    rw [← hst] at hm
    simp [Env.starves, hm] at hs
  have haff : Cursor.affordableRungs lc.quota c.tx.inputs.length ≠ 0 := fun h => hnot (.inl h)
  have hfl : c.track.floor = 0 := Decidable.of_not_not fun h => hnot (.inr h)
  refine ⟨c, hc, hrel, hfl, haff, ?_, rfl⟩
  apply Decidable.of_not_not
  intro hlt
  exact haff (Nat.div_eq_of_lt (by omega))

/-- **The base at the ladder pass** (`SPN-38`). At a ladder pass `RungRelease.admits` admits, for a resident
Escape-role record on a node whose ids are distinct: the rows under its commitment are its base row, exactly when its
account lists rung 0 and it is not yet released, followed by the rows of its listed rungs above the base; and the
record under its id after the pass is released exactly when it was or its account lists rung 0. -/
@[req "SPN-38"]
theorem ladder_base {lc : Ladder.Cfg} {honest : List Nat} {st : Sweep.State} {T : Sweep.Trace} {i : Nat}
    {env : Env} (ha : RungRelease.admits lc honest st T (.fed (.process i env .ladderPass)) = true) (r : Rules)
    (hn : ((st.fed.worlds i).node.cands.map Cand.id).Nodup) {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands)
    (hesc : c.isEscape = true) :
    (step r env (st.fed.worlds i) .ladderPass).2.filter (under c.id) =
        (if 0 ∈ (passAccount lc r st T i env c).rungs ∧ c.released = false then
          [.queuePartial (sighash c.tx 0) 0 c.hot c.id] else []) ++
          rungEffects c (passAccount lc r st T i env c).rungs ∧
      ∀ d ∈ ((Federation.apply r st.fed (.process i env .ladderPass)).worlds i).node.cands, d.id = c.id →
        (d.released = true ↔ c.released = true ∨ 0 ∈ (passAccount lc r st T i env c).rungs) := by
  refine ⟨by rw [pass_under ha r hc hesc, baseEffects_eq], fun d hd hdc => ?_⟩
  rw [(pass_account ha r).1] at hd
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hd
  have hcc : c' = c := Kernel.eq_of_mem_ids_nodup hn hc' hc hdc
  subst hcc
  simp

/-- **A starved node sends nothing for that candidate** (`SPN-38`: "If `affordable_rungs = 0`, release nothing and
advance no release bookkeeping on this pass"). On `LadderRelease`'s run under `Registration.preserve`, at an
admitted fire or ladder pass of honest node `i`, a resident record with no rung affordable at its input count gets
no row under its commitment, its base included, and the record under its id after the pass keeps its `released`
bit and its release state, latch and floor. -/
@[req "SPN-38"]
theorem starved_silent {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hr : r.registration = .preserve) (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest)
    {env : Env} {e : Event} (he : e = .firePass ∨ e = .ladderPass)
    (ha : LadderRelease.admits lc honest st T (.fed (.process i env e)) = true)
    {c : Cand} (hc : c ∈ (st.fed.worlds i).node.cands)
    (hz : Cursor.affordableRungs lc.quota c.tx.inputs.length = 0) :
    (step r env (st.fed.worlds i) e).2.filter (under c.id) = [] ∧
      ∀ d ∈ ((Federation.apply r st.fed (.process i env e)).worlds i).node.cands, d.id = c.id →
        d.released = c.released ∧ d.track = c.track := by
  have hn := ids_nodup_run hr hx hi
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
    have hq : passAccount lc r st T i env c = quiet c.track := pass_zero lc r st T i env hz
    refine ⟨?_, fun d hd hdc => ?_⟩
    · rw [(pass_account har r).2, filter_flatMap]
      simp only [effects_under]
      refine (flatMap_own hn hc _).trans ?_
      simp [hq, quiet, baseEffects, rungEffects]
    · rw [(pass_account har r).1] at hd
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hd
      have hcc : c' = c := Kernel.eq_of_mem_ids_nodup hn hc' hc hdc
      subst hcc
      simp [hq, quiet]

/-- `ReleaseQuota.starved_silent` on the lifecycle run, through `Lifecycle.to_ladder`. -/
@[req "SPN-38"]
theorem starved_silent_life {cfg : RungAssembly.Cfg} {r : Rules} {honest : List Nat} {T : Lifecycle.Trace}
    {st : Lifecycle.State} (hr : r.registration = .preserve) (hx : Lifecycle.Execution cfg r honest T st)
    {i : Nat} (hi : i ∈ honest) {env : Env} {e : Event} (he : e = .firePass ∨ e = .ladderPass)
    (ha : Lifecycle.admits cfg r honest st T (.base (.fed (.process i env e))) = true)
    {c : Cand} (hc : c ∈ (st.cs.sw.fed.worlds i).node.cands)
    (hz : Cursor.affordableRungs cfg.lc.quota c.tx.inputs.length = 0) :
    (step r env (st.cs.sw.fed.worlds i) e).2.filter (under c.id) = [] ∧
      ∀ d ∈ ((Federation.apply r st.cs.sw.fed (.process i env e)).worlds i).node.cands, d.id = c.id →
        d.released = c.released ∧ d.track = c.track := by
  exact starved_silent hr (Lifecycle.to_ladder hx) hi he (life_admits ha) hc hz

/-- The base rows a step of node `n` queues under commitment `k`: at a fire pass, its rows under `k`; at a ladder
pass, the base rows (`Kernel.baseEffects`) of the records under `k` at their listings; nothing at any other
event. -/
@[req "SPN-38"]
def baseOut (r : Rules) (env : Env) (n : Node) (k : Nat) : Event → List Effect
  | .firePass => (firePass r env n).2.filter (under k)
  | .ladderPass =>
    if r.poison == .asserted && n.poisoned then []
    else (n.cands.filter (·.id == k)).flatMap fun c => baseEffects c (((ladderAt r env n c).map (·.2)).getD [])
  | _ => []

/-- A base row of a step is one of its effects, under its commitment. -/
theorem baseOut_sub (r : Rules) (env : Env) (w : World) (k : Nat) (e : Event) {eff : Effect}
    (h : eff ∈ baseOut r env w.node k e) : eff ∈ (step r env w e).2 ∧ under k eff = true := by
  cases e with
  | firePass => exact List.mem_filter.1 h
  | ladderPass =>
    simp only [baseOut] at h
    split at h
    · simp at h
    · rename_i hp
      obtain ⟨c, hc, hb⟩ := List.mem_flatMap.1 h
      obtain ⟨hc, hck⟩ := List.mem_filter.1 hc
      refine ⟨?_, ?_⟩
      · show eff ∈ (ladderPass r env w.node).2
        unfold ladderPass
        rw [if_neg hp]
        exact List.mem_flatMap.2 ⟨c, hc, List.mem_append_left _ hb⟩
      · obtain ⟨-, -, rfl⟩ := mem_baseEffects hb
        simpa [under] using hck
  | _ => simp [baseOut] at h

/-- Every effect a step queues under commitment `k` is one of its base rows (`ReleaseQuota.baseOut`) or a row of a
rung above the base that a ladder pass lists for a record under `k`. -/
theorem baseOut_cover (r : Rules) (env : Env) (w : World) (k : Nat) (e : Event) {eff : Effect}
    (he : eff ∈ (step r env w e).2) (hu : under k eff = true) :
    eff ∈ baseOut r env w.node k e ∨
      ∃ c ∈ w.node.cands, c.id = k ∧ eff ∈ rungEffects c (((ladderAt r env w.node c).map (·.2)).getD []) := by
  cases e with
  | firePass => exact .inl (List.mem_filter.2 ⟨he, hu⟩)
  | ladderPass =>
    have he' : eff ∈ (ladderPass r env w.node).2 := he
    unfold ladderPass at he'
    split at he'
    · simp at he'
    · rename_i hp
      obtain ⟨c, hc, hm⟩ := List.mem_flatMap.1 he'
      rcases List.mem_append.1 hm with hb | hr
      · have hck : c.id = k := by
          obtain ⟨-, -, rfl⟩ := mem_baseEffects hb
          simpa [under] using hu
        refine .inl ?_
        simp only [baseOut, if_neg hp]
        exact List.mem_flatMap.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hck]⟩, hb⟩
      · have hck : c.id = k := by
          obtain ⟨_, _, _, -, -, -, rfl⟩ := mem_rungEffects hr
          simpa [under] using hu
        exact .inr ⟨c, hc, hck, hr⟩
  | send cid =>
    exfalso
    simp only [step, send] at he
    split at he
    · simp at he
    · split at he <;> simp at he <;> subst he <;> simp [under] at hu
  | _ => simp [step] at he

theorem filter_id_length {E : List Cand} (hn : (E.map Cand.id).Nodup) (k : Nat) :
    (E.filter (·.id == k)).length ≤ 1 := by
  induction E with
  | nil => simp
  | cons d E ih =>
    obtain ⟨hnd, hns⟩ := List.nodup_cons.1 hn
    by_cases hd : d.id = k
    · have h0 : E.filter (·.id == k) = [] := by
        apply List.filter_eq_nil_iff.2
        intro x hx hxk
        apply hnd
        have hxd : x.id = d.id := by simp only [beq_iff_eq] at hxk; rw [hxk, hd]
        rw [← hxd]
        exact List.mem_map_of_mem hx
      rw [List.filter_cons, if_pos (by simpa using hd), h0]
      simp
    · rw [List.filter_cons, if_neg (by simpa using hd)]
      exact ih hns

theorem firePass_effects (r : Rules) (env : Env) (n : Node) (hp : (r.poison == .asserted && n.poisoned) = false) :
    (firePass r env n).2 = (n.cands.filter fun c => due r env n c && releaseAuthorized r n c && !env.withholds c &&
      !env.starves c && !c.released).map fun c => Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id := by
  simp [firePass, hp]

/-- **One base row per record per pass.** On a node whose ids are distinct, a step queues at most one base row under
a commitment. -/
@[req "SPN-38"]
theorem baseOut_length (r : Rules) (env : Env) (n : Node) (hn : (n.cands.map Cand.id).Nodup) (k : Nat)
    (e : Event) : (baseOut r env n k e).length ≤ 1 := by
  cases e with
  | firePass =>
    show ((firePass r env n).2.filter (under k)).length ≤ 1
    by_cases hp : (r.poison == .asserted && n.poisoned) = true
    · simp [firePass, hp]
    · rw [firePass_effects r env n (by simpa using hp), List.filter_map, List.length_map]
      have hL : ((n.cands.filter fun c => due r env n c && releaseAuthorized r n c && !env.withholds c &&
          !env.starves c && !c.released).map Cand.id).Nodup :=
        List.Nodup.sublist ((List.filter_sublist (l := n.cands)).map Cand.id) hn
      have e : ∀ L : List Cand,
          L.filter (under k ∘ fun c => Effect.queuePartial (sighash c.tx 0) 0 c.hot c.id) = L.filter (·.id == k) := by
        intro L
        apply List.filter_congr
        intro c _
        simp [under]
      rw [e]
      exact filter_id_length hL k
  | ladderPass =>
    simp only [baseOut]
    split
    · simp
    · have h1 := filter_id_length hn k
      generalize n.cands.filter (·.id == k) = L at h1 ⊢
      match L, h1 with
      | [], _ => simp
      | [c], _ =>
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [baseEffects_eq]
        split <;> simp
      | _ :: _ :: _, h => simp at h
  | _ => simp [baseOut]

/-- A pass that queues a base row under `k`, at a node whose ids are distinct, leaves the record under `k` released:
the fire pass and the ladder pass set the one `released` bit they both read. -/
theorem baseOut_marks {r : Rules} {env : Env} {w : World} (hn : (w.node.cands.map Cand.id).Nodup) {k : Nat}
    {e : Event} (h : baseOut r env w.node k e ≠ []) :
    ∀ d ∈ (step r env w e).1.node.cands, d.id = k → d.released = true := by
  cases e with
  | firePass =>
    obtain ⟨eff, hm⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨he, hu⟩ := List.mem_filter.1 hm
    exact firePass_marks hn he hu
  | ladderPass =>
    simp only [baseOut] at h
    split at h
    · exact absurd rfl h
    · rename_i hp
      obtain ⟨eff, hm⟩ := List.exists_mem_of_ne_nil _ h
      obtain ⟨c, hc, hb⟩ := List.mem_flatMap.1 hm
      obtain ⟨hc, hck⟩ := List.mem_filter.1 hc
      obtain ⟨h0, -, -⟩ := mem_baseEffects hb
      intro d hd hdk
      change d ∈ (ladderPass r env w.node).1.cands at hd
      unfold ladderPass at hd
      rw [if_neg hp] at hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      have hid : d₀.id = c.id := by
        simp only [beq_iff_eq] at hck
        rw [hck]
        exact hdk
      rw [Kernel.eq_of_mem_ids_nodup hn hd₀ hc hid]
      simp [h0]
  | _ => exact (h (by simp [baseOut])).elim

/-- **The base at most once in a lifetime, by either path** (`SPN-36`'s `released`, `SPN-38`). On `LadderRelease`'s
run under `Registration.preserve`, once any pass of honest node `i`, fire or ladder, queues a base row under
commitment `k`, no pass of `i` after it, fire or ladder, at any environment, queues one, over every stretch of steps
none of which births a record under `k` at `i`. The `released` bit both passes read and set is what holds the base
to one row. -/
@[req "SPN-38"]
theorem base_once_paths {lc : Ladder.Cfg} {r : Rules} {honest : List Nat} {T : Sweep.Trace} {st : Sweep.State}
    (hr : r.registration = .preserve) (hx : LadderRelease.Execution lc r honest T st) {i : Nat} (hi : i ∈ honest)
    {k : Nat} {T₁ T₂ : Sweep.Trace} {st₁ : Sweep.State} {env₁ : Env} {e₁ : Event}
    (hT : T = T₂ ++ (st₁, .fed (.process i env₁ e₁)) :: T₁)
    (hb : ∀ y ∈ T₂, Lifecycle.births r y.1 y.2 i k = false)
    (h₁ : baseOut r env₁ (st₁.fed.worlds i).node k e₁ ≠ []) (env₂ : Env) (e₂ : Event) :
    baseOut r env₂ (st.fed.worlds i).node k e₂ = [] := by
  obtain ⟨hx₁, -, -⟩ := lifetime_after hx hi hT hb
  have hmark := baseOut_marks (ids_nodup_run hr hx₁ hi) h₁
  have hrel : ∀ c ∈ (st.fed.worlds i).node.cands, c.id = k → c.released = true := by
    intro c hc hck
    obtain ⟨d, hd, hdk, hdr⟩ := released_after hx hT hb c hc hck
    have hd' : d ∈ (step r env₁ (st₁.fed.worlds i) e₁).1.node.cands := by
      have h := hd
      change d ∈ ((Federation.apply r st₁.fed (.process i env₁ e₁)).worlds i).node.cands at h
      rw [Federation.apply_of_actor r _ _ rfl i, if_pos rfl] at h
      exact h
    exact hdr (hmark d hd' hdk)
  cases e₂ with
  | firePass =>
    show (firePass r env₂ (st.fed.worlds i).node).2.filter (under k) = []
    apply List.filter_eq_nil_iff.2
    intro eff he hu
    obtain ⟨c, hc, -, -, -, hc0, rfl⟩ := firePass_effect r env₂ _ he
    have hck : c.id = k := by simpa [under] using hu
    rw [hrel c hc hck] at hc0
    cases hc0
  | ladderPass =>
    simp only [baseOut]
    split
    · rfl
    · apply List.flatMap_eq_nil_iff.2
      intro c hc
      obtain ⟨hc, hck⟩ := List.mem_filter.1 hc
      have := hrel c hc (by simpa using hck)
      simp [baseEffects, this]
  | _ => simp [baseOut]

end BtcPolicy.ReleaseQuota
