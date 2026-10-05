import BtcPolicy.Req
/-! `DUR-13`'s deadline and `DUR-14`'s dynamic `T`: "On every hot spend accepted while armed,
`T ← max(min(T, its fire_at − epsilon_secs), now)`." The conformance item once asked that `T`
never grow (`F58`). The properties proved here are `T' ≤ max(T, now)` and `now ≤ T ⇒ T' ≤ T`.
When `now > T`, the update means act now, not grant more delay. `DUR-7` says "a dedicated deadline
driver attempts it on every 1-second tick with no backend I/O, one lock and one comparison
(`armed ∧ now ≥ T`)". `not_never_grows` retains the false theorem's counterexample. -/

namespace BtcPolicy.Deadline

/-- `DUR-14`'s update. `Nat` subtraction saturates; `fire_at − ε` below zero is the same "act now"
case as a past `T`. -/
@[req "DUR-14"]
def shrink (T fireAt eps now : Nat) : Nat := max (min T (fireAt - eps)) now

/-- `DUR-13`'s computation at the holder decision: `t_ceiling = first_seen + duress_delay_secs`,
pulled to `earliest_hot − epsilon_secs` if a hot candidate is pending, then `max(t_ceiling, now)`. -/
@[req "DUR-13"]
def initialT (firstSeen delay now : Nat) (earliestHot : Option Nat) (eps : Nat) : Nat :=
  let ceiling := firstSeen + delay
  let ceiling := match earliestHot with
    | none => ceiling
    | some fire => min ceiling (fire - eps)
  max ceiling now

/-- The unconditional bound on `shrink`, for every input. -/
@[req "DUR-14"]
theorem shrink_le_max (T fireAt eps now : Nat) : shrink T fireAt eps now ≤ max T now := by
  unfold shrink; omega

/-- The bound on `shrink` while `now ≤ T`: `T` never grows. -/
@[req "DUR-14"]
theorem shrink_le_of_now_le (T fireAt eps now : Nat) (h : now ≤ T) :
    shrink T fireAt eps now ≤ T := by
  unfold shrink; omega

/-- The theorem the conformance item used to ask for (`F58`), refuted: `T' ≤ T` fails on a late acceptance. -/
@[req "DUR-14"]
theorem not_never_grows : ¬ ∀ T fireAt eps now, shrink T fireAt eps now ≤ T := by
  intro h
  have := h 10 100 1 11
  simp [shrink] at this

/-- The late acceptance `F58` turns on, as one input: `T = 10`, `now = 11`; `T'` is `11`. -/
@[req "DUR-14"]
theorem late_acceptance_exhibit : shrink 10 100 1 11 = 11 := by decide

/-- `DUR-14`'s purpose: without the pull, "a post-arm hot spend with a nearer Hold expiry would
settle visibly under the normal PIN and be frozen under duress, leaking the armed state before
`T`" — so a hot spend whose `fire_at − epsilon_secs` is below `T` (`hf`) and not yet past (`hn`)
pulls `T` to exactly that instant; a `T` already past becomes `now` (`late_acceptance_exhibit`). -/
@[req "DUR-14"]
theorem pulls_before_fire (T fireAt eps now : Nat) (hf : fireAt - eps < T)
    (hn : now ≤ fireAt - eps) : shrink T fireAt eps now = fireAt - eps := by
  unfold shrink; omega

/-- `DUR-14` says "`duress_delay_secs` is therefore a **ceiling**, not a guarantee"; here is the
ceiling on `DUR-13`'s initial `T`: never above `max(first_seen + delay, now)`. -/
@[req "DUR-13"]
theorem initial_le_ceiling (firstSeen delay now : Nat) (eh : Option Nat) (eps : Nat) :
    initialT firstSeen delay now eh eps ≤ max (firstSeen + delay) now := by
  unfold initialT; cases eh <;> simp <;> omega

/-! ## The bound the concealment horizon rests on (`DUR-13`, `DUR-14`) -/

/-- `T` is at or before a candidate's fire time less `epsilon_secs`, or at the sample of the write
that set it — `DUR-13`'s clamp `max(t_ceiling, now)`, which its own listing annotates "a past T
fires now".
The second disjunct is why the bound is carried at a sample and not as a property of `T` alone. -/
@[req "DUR-14"]
def belowFire (T fireAt eps now : Nat) : Bool := T ≤ max (fireAt - eps) now

/-- A later sample only weakens it, which is what lets the invariant be carried at the step's own
sample instead of at the sample of the last `T` write. -/
@[req "DUR-14"]
theorem belowFire_weaken (T fireAt eps now now' : Nat) (h : belowFire T fireAt eps now = true)
    (hn : now ≤ now') : belowFire T fireAt eps now' = true := by
  simp only [belowFire, decide_eq_true_eq] at *; omega

/-- `DUR-13`'s deadline satisfies it for every hot candidate the scan covered: `earliest_hot` is a
minimum over their fire times, so a candidate at or after it is bounded too. -/
@[req "DUR-13"]
theorem initial_belowFire (firstSeen delay now earliest fireAt eps : Nat)
    (h : earliest ≤ fireAt) :
    belowFire (initialT firstSeen delay now (some earliest) eps) fireAt eps now = true := by
  simp only [belowFire, initialT, decide_eq_true_eq]; omega

/-- `DUR-14`'s shrink satisfies it for the spend that caused it. -/
@[req "DUR-14"]
theorem shrink_belowFire (T fireAt eps now : Nat) :
    belowFire (shrink T fireAt eps now) fireAt eps now = true := by
  simp only [belowFire, shrink, decide_eq_true_eq]; omega

/-- And it keeps it for every other hot candidate, given a sample no earlier than the one the
bound was carried at. Without that premise the lemma is false, which is the clock family `F60`
records: the new `T` is clamped up to `now`, and a `now` that stepped backward is below the
bound the old `T` respected. -/
@[req "DUR-14"]
theorem shrink_keeps_belowFire (T fireAt other eps now now' : Nat)
    (h : belowFire T other eps now = true) (hn : now ≤ now') :
    belowFire (shrink T fireAt eps now') other eps now' = true := by
  simp only [belowFire, shrink, decide_eq_true_eq] at *; omega

end BtcPolicy.Deadline
