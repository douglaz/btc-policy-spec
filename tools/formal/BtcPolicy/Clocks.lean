import BtcPolicy.Req
import BtcPolicy.Deadline
/-! `DOM-24`'s three node clocks and `SPN-46`'s chain clock as four types, plus `SPN-13`'s
high-water (`ADR-0023` decision 12). "Three clocks exist and MUST NOT be confused":
every conversion and comparison is a named operation below, carrying the clause that licenses
it, and there is no coercion between the types. The constructor and the field of each type are
private, so a raw sample cannot be minted into another clock outside this module: the term that
retires a Carrier from a `Wall` sample (`DEF-1`) is a type error, and CI compiles that term and
asserts the mismatch. What the types do NOT rule out is a wall-to-wall comparison that deletes a
Carrier, which confuses nothing; that is `Kernel.lean`'s retirement parameter and its exhibit.

`Mono` carries no generation index: a rebooted armed node is dead (`DUR-18`) and the HotClock is
process-lifetime (`NCH-41`), so one node has one HotClock; `SPN-14`'s "handler generations" are
`NCH-32`'s memo generations, not process generations. Two nodes' HotClocks share no origin; a
multi-node world would index `Mono` by node, and this kernel is one node. -/

namespace BtcPolicy.Clocks

/-- `DOM-24`: "unix seconds from the host clock; the authority for signed expiries". -/
structure Wall where private mk :: private s : Nat deriving DecidableEq, Repr
/-- `SPN-13`'s high-water: "the greatest expiry of every entry that accept pruned" — a
wall-domain value with its own type, so a raw sample cannot stand in for it. -/
structure HighWater where private mk :: private s : Nat deriving DecidableEq, Repr
/-- `DOM-24`: "`max(nonce-log high-water, wall)`; the rollback-guarded lower bound every
freshness decision uses". Its only constructor is `Effective.ofWall`. -/
structure Effective where private mk :: private s : Nat deriving DecidableEq, Repr
/-- `DOM-24`: "elapsed seconds since the channel was constructed, the HotClock; the authority
for the Hot-budget window and for Carrier residency". -/
structure Mono where private mk :: private s : Nat deriving DecidableEq, Repr
/-- `SPN-46`: BIP113 median-time-past, "chain state and not one of `DOM-24`'s three node
clocks"; it lives in a chain view, never in a node. -/
structure Mtp where private mk :: private s : Nat deriving DecidableEq, Repr

/-- A raw host reading. -/
def Wall.sample (n : Nat) : Wall := ⟨n⟩
def HighWater.sample (n : Nat) : HighWater := ⟨n⟩
/-- A HotClock reading. -/
def Mono.sample (n : Nat) : Mono := ⟨n⟩
def Mtp.sample (n : Nat) : Mtp := ⟨n⟩

/-- A duration in seconds is a bare `Nat`; it is never an instant. -/
abbrev Secs := Nat

/-- `SPN-13`: "`effective_now = max(high_water, raw_now)`". -/
@[req "SPN-13"]
def Effective.ofWall (w : Wall) (hw : HighWater) : Effective := ⟨max hw.s w.s⟩

/-- `NCH-33`: "`D = M + (E − W)` with `M` the monotonic HotClock sample taken before
authentication, `E` the signed expiry and `W` that decision's effective time, in checked
arithmetic that fails closed"; `SPN-14`: "with overflow failing closed as a window refusal". On
`Nat` the check that can fail is `E < W`: the refusal is `none`. -/
@[req "NCH-33"]
def Mono.deadline (m : Mono) (e : Wall) (w : Effective) : Option Mono :=
  if w.s ≤ e.s then some ⟨m.s + (e.s - w.s)⟩ else none

/-- `NCH-34`: "A new holder requires attempt time `< E`" — the effective sample against the
signed wall-domain expiry. -/
@[req "NCH-34"]
def Effective.before (w : Effective) (e : Wall) : Bool := w.s < e.s
/-- A window bound reached: `fire_at ≤ now` (`SPN-38`: "its fire window is open now"). -/
def Effective.atOrAfter (w : Effective) (e : Wall) : Bool := e.s ≤ w.s
/-- `SPN-41`: "The last authorized second is `now == expiry`". -/
def Effective.atOrBefore (w : Effective) (e : Wall) : Bool := w.s ≤ e.s
/-- `NCH-34`: "AND `mono_now < D`". The only comparison a Carrier deadline admits. -/
@[req "NCH-34"]
def Mono.before (m d : Mono) : Bool := m.s < d.s

/-- `DUR-7`'s deadline driver. `DUR-7` says it attempts Lockdown with "one lock and one comparison
(`armed ∧ max(ratchet, effective) ≥ T`)". The armed deadline is a wall-domain value (`DUR-13` builds it from its start, the seed lowered
to each duress-bit record's `first_seen`, and a candidate's `fire_at`) read against an effective-domain sample, so it is its own named operation and not
`NCH-34`'s. -/
@[req "DUR-7"]
def Effective.deadlineReached (w : Effective) (T : Wall) : Bool := T.s ≤ w.s

/-- `DUR-7`'s comparison and the opening of `SPN-38`'s "its fire window is open now" are one
operation on one pair of domains: the deadline driver's `≥ T` is the window-open test at
`fire_at = T`, which is what a selected Escape's window makes it (`DUR-20`). The two read it at
different samples: the driver at `max(ratchet, effective)`, the opening at effective time. -/
@[req "DUR-7"]
theorem Effective.atOrAfter_eq_deadlineReached (w : Effective) (e : Wall) :
    w.atOrAfter e = w.deadlineReached e := rfl

/-- The earlier of two effective samples: `DUR-13`'s minimum over its seed and the `first_seen` of
each record that contributes to its start. -/
def Effective.earlier (a b : Effective) : Effective := if a.s < b.s then a else b

/-- The earlier of two wall instants: `DUR-13`'s `min` over the pending hot candidates' fire
times. -/
def Wall.earlier (a b : Wall) : Wall := if a.s < b.s then a else b

/-- One effective sample no later than the next. `SPN-13`'s effective time is NOT monotone on
its own — the high-water "is advanced, on an accept only", so a corrected wall clock lowers it —
so a trace that never steps back is a premise, never a property of the type (`F60`). What is
never lowered is the time ratchet (`DUR-7`), a record of readings built from `Effective.latest`
below, and not a fourth clock. -/
def Effective.notAfter (a b : Effective) : Bool := a.s ≤ b.s

theorem Effective.notAfter_refl (a : Effective) : a.notAfter a = true := by
  simp [Effective.notAfter]

theorem Effective.notAfter_trans {a b c : Effective} (h1 : a.notAfter b = true)
    (h2 : b.notAfter c = true) : a.notAfter c = true := by
  simp only [Effective.notAfter, decide_eq_true_eq] at *; omega

/-! ## The time ratchet's arithmetic

`DUR-7`'s time ratchet is the greatest effective time a node has read at its advancing events.
It is a record of effective-time readings, so its type is `Effective`, and the two operations it
needs — the starting value and the later of two readings — are named here, beside the private
field they read. -/

/-- The ratchet's value before any advancing event: no reading yet. -/
def Effective.epoch : Effective := ⟨0⟩

/-- The later of two effective readings: `max(ratchet, effective)`. -/
def Effective.latest (a b : Effective) : Effective := ⟨max a.s b.s⟩

theorem Effective.notAfter_latest_left (a b : Effective) : a.notAfter (a.latest b) = true := by
  simp only [Effective.notAfter, Effective.latest, decide_eq_true_eq]; omega

theorem Effective.notAfter_latest_right (a b : Effective) : b.notAfter (a.latest b) = true := by
  simp only [Effective.notAfter, Effective.latest, decide_eq_true_eq]; omega

/-- `DUR-7`'s comparison at `max(ratchet, effective)` is false exactly when it is false at both. -/
theorem Effective.deadlineReached_latest {a b : Effective} {T : Wall}
    (h : (a.latest b).deadlineReached T = false) :
    a.deadlineReached T = false ∧ b.deadlineReached T = false := by
  simp only [Effective.deadlineReached, Effective.latest, decide_eq_false_iff_not, Nat.not_le] at *
  omega

/-- An instant at or after the ratchet is at or after every reading below it. -/
theorem Effective.atOrBefore_of_notAfter {a b : Effective} {e : Wall} (h : a.notAfter b = true)
    (hb : b.atOrBefore e = true) : a.atOrBefore e = true := by
  simp only [Effective.notAfter, Effective.atOrBefore, decide_eq_true_eq] at *; omega

/-- A sample already past an instant is past it at every later sample: the `SPN-41` half of what
a live invariant carried at one sample needs to be read at a later one. -/
theorem Effective.not_atOrBefore_weaken {a b : Effective} {e : Wall}
    (h : a.atOrBefore e = false) (hab : a.notAfter b = true) : b.atOrBefore e = false := by
  simp only [Effective.atOrBefore, Effective.notAfter, decide_eq_true_eq,
    decide_eq_false_iff_not, Nat.not_le] at *
  omega

/-- One HotClock sample no later than the next. `NCH-41`: "A suspend makes it lag real time,
which can only over-count residency — the safe direction"; that it never steps back within a
process is what the ledger's one-way release relies on. -/
def Mono.notAfter (a b : Mono) : Bool := a.s ≤ b.s

theorem Mono.notAfter_refl (a : Mono) : a.notAfter a = true := by simp [Mono.notAfter]

theorem Mono.notAfter_trans {a b c : Mono} (h1 : a.notAfter b = true) (h2 : b.notAfter c = true) :
    a.notAfter c = true := by
  simp only [Mono.notAfter, decide_eq_true_eq] at *; omega

/-- `SPN-38`'s HotClock check of a hot candidate's Hold, "`now_mono − reserved_at ≥ hold_secs`",
written without the subtraction: `reserved_at + hold ≤ now_mono`. Two `Mono` instants and one
duration, inclusive at equality. -/
def Mono.aged (start now : Mono) (hold : Secs) : Bool := start.s + hold ≤ now.s

/-- `DUR-20`'s window close, `T + combine_slack_secs`; `SPN-30`'s cap on a hot window,
`fire_at + combine_slack_secs`, is the same sum. -/
@[req "DUR-20"]
def Wall.plus (w : Wall) (d : Secs) : Wall := ⟨w.s + d⟩

/-- `DUR-13`'s deadline at the holder decision, over `Deadline.initialT`: `t_ceiling =
start + duress_delay_secs`, pulled to `earliest_hot − epsilon_secs` when a hot candidate is
pending, then `max(t_ceiling, now)`. The clause mixes domains on purpose — `start` and `now` are
effective times, `earliest_hot` is a candidate's wall-domain `fire_at` — so the conversion is
named here rather than left to a field read. -/
@[req "DUR-13"]
def Wall.initialDeadline (start : Effective) (delay : Secs) (now : Effective)
    (earliestHot : Option Wall) (eps : Secs) : Wall :=
  ⟨Deadline.initialT start.s delay now.s (earliestHot.map (·.s)) eps⟩

/-- `DUR-14`'s dynamic shrink, over `Deadline.shrink`: "On every hot spend accepted while armed,
`T ← max(min(T, its fire_at − epsilon_secs), now)`". -/
@[req "DUR-14"]
def Wall.shrinkDeadline (T fireAt : Wall) (eps : Secs) (now : Effective) : Wall :=
  ⟨Deadline.shrink T.s fireAt.s eps now.s⟩

/-- `POL-19`'s "`reserved_at ≥ now_mono − window_secs`", written without the saturating
subtraction: `now_mono ≤ reserved_at + window`. Two `Mono` instants and one duration. -/
def Mono.withinWindow (reservedAt now : Mono) (window : Secs) : Bool := now.s ≤ reservedAt.s + window
/-- `POL-19`'s "`wall_now ≤ expiry`": the RAW wall sample, as the clause says, not the effective
time every other lifetime comparison uses. -/
def Wall.atOrBefore (now expiry : Wall) : Bool := now.s ≤ expiry.s

/-- `POL-19`: "`live ⇔ reserved_at ≥ now_mono − window_secs ∨ wall_now ≤ expiry`, both boundaries
inclusive". Each disjunct compares within one clock; no conversion is needed to join them. -/
@[req "POL-19"]
def reservationLive (reservedAt nowMono : Mono) (window : Secs) (wallNow expiry : Wall) : Bool :=
  Mono.withinWindow reservedAt nowMono window || Wall.atOrBefore wallNow expiry

/-- `NCH-41`'s safe direction, as the lemma a one-way release rests on: a reservation inside the
trailing window at one sample is inside it at every earlier sample, so a sweep that ran before the
cut released nothing the cut still counts. The wall disjunct is not needed and `POL-17` is not
needed; saturating `Nat` subtraction is not in the statement, since `withinWindow` is written as
`now ≤ reserved_at + window`. -/
@[req "POL-19"]
theorem Mono.withinWindow_of_notAfter {reservedAt a b : Mono} {window : Secs}
    (hab : a.notAfter b = true) (hb : Mono.withinWindow reservedAt b window = true) :
    Mono.withinWindow reservedAt a window = true := by
  simp only [Mono.notAfter, Mono.withinWindow, decide_eq_true_eq] at *; omega

/-- Both boundaries inclusive: on the edge of each disjunct the reservation is live. -/
@[req "POL-19"]
theorem reservationLive_boundaries_inclusive (r : Nat) (w : Secs) (e : Nat) :
    reservationLive ⟨r⟩ ⟨r + w⟩ w ⟨e + 1⟩ ⟨e⟩ = true ∧
    reservationLive ⟨r⟩ ⟨r + w + 1⟩ w ⟨e⟩ ⟨e⟩ = true := by
  simp [reservationLive, Mono.withinWindow, Wall.atOrBefore]

/-- The conjunction `POL-19`'s rationale warns against loses a reservation whose wall expiry a
forward step has passed while its monotonic window is open. -/
@[req "POL-19"]
theorem reservationLive_and_is_wrong :
    ¬ ∀ (r w e : Nat), (Mono.withinWindow ⟨r⟩ ⟨r⟩ w && Wall.atOrBefore ⟨e + 1⟩ ⟨e⟩) =
      reservationLive ⟨r⟩ ⟨r⟩ w ⟨e + 1⟩ ⟨e⟩ := by
  intro h; have := h 0 0 0; simp [reservationLive, Mono.withinWindow, Wall.atOrBefore] at this

/-! ## The bound the concealment horizon rests on, in the wall domain -/

/-- `Deadline.belowFire` over the types: the overlay deadline is at or before a candidate's fire
time less `epsilon_secs`, or at the effective sample of the write that set it. The domains mix
exactly as `DUR-13`'s own computation mixes them, so the comparison is named here. -/
@[req "DUR-14"]
def Wall.belowFire (T fireAt : Wall) (eps : Secs) (now : Effective) : Bool :=
  Deadline.belowFire T.s fireAt.s eps now.s

@[req "DUR-14"]
theorem Wall.belowFire_weaken {T fireAt : Wall} {eps : Secs} {a b : Effective}
    (h : Wall.belowFire T fireAt eps a = true) (hab : a.notAfter b = true) :
    Wall.belowFire T fireAt eps b = true :=
  Deadline.belowFire_weaken _ _ _ _ _ h (by simpa [Effective.notAfter] using hab)

@[req "DUR-14"]
theorem Wall.belowFire_shrink (T fireAt : Wall) (eps : Secs) (now : Effective) :
    Wall.belowFire (Wall.shrinkDeadline T fireAt eps now) fireAt eps now = true :=
  Deadline.shrink_belowFire _ _ _ _

@[req "DUR-14"]
theorem Wall.belowFire_shrink_keeps {T fireAt other : Wall} {eps : Secs} {a b : Effective}
    (h : Wall.belowFire T other eps a = true) (hab : a.notAfter b = true) :
    Wall.belowFire (Wall.shrinkDeadline T fireAt eps b) other eps b = true :=
  Deadline.shrink_keeps_belowFire _ _ _ _ _ _ h (by simpa [Effective.notAfter] using hab)

/-- `DUR-14`'s shrink at a sample at or below the one the bound is carried at keeps the bound
there: `T' ≤ max(T, now) ≤ max(other − ε, carried)`. So a `T` write below the ratchet keeps every
bound carried at the ratchet. -/
@[req "DUR-14"]
theorem Wall.belowFire_shrink_keeps_below {T fireAt other : Wall} {eps : Secs} {now carried : Effective}
    (h : Wall.belowFire T other eps carried = true) (hn : now.notAfter carried = true) :
    Wall.belowFire (Wall.shrinkDeadline T fireAt eps now) other eps carried = true := by
  simp only [Wall.belowFire, Wall.shrinkDeadline, Deadline.belowFire, Deadline.shrink,
    Effective.notAfter, decide_eq_true_eq] at *
  omega

/-- `DUR-14`'s update never writes above `max(T, now)`. The bound is stated as its two disjuncts:
the written value is at or before the `T` it replaces, or at or before its own sample. `DUR-13`
names the same update at a holder decision on an armed node, "`DUR-14`'s own update", with the
computed value in place of the fire time. -/
@[req "DUR-13"]
theorem Wall.shrinkDeadline_le_max (T fireAt : Wall) (eps : Secs) (now : Effective) :
    Wall.atOrBefore (Wall.shrinkDeadline T fireAt eps now) T = true ∨
      now.deadlineReached (Wall.shrinkDeadline T fireAt eps now) = true := by
  simp only [Wall.atOrBefore, Effective.deadlineReached, Wall.shrinkDeadline, Deadline.shrink,
    decide_eq_true_eq]
  omega

/-- `DUR-13`'s clamp at a holder decision, `max(min(T, T_computed), now)`, keeps every bound the
computed value carries at a sample no earlier than the decision's: the clamp is at most
`max(T_computed, now)`, and the bound is monotone downward in `T`. -/
@[req "DUR-13"]
theorem Wall.belowFire_clamp {T computed fireAt : Wall} {eps : Secs} {now carried : Effective}
    (h : Wall.belowFire computed fireAt eps carried = true) (hn : now.notAfter carried = true) :
    Wall.belowFire (Wall.shrinkDeadline T computed 0 now) fireAt eps carried = true := by
  simp only [Wall.belowFire, Wall.shrinkDeadline, Deadline.belowFire, Deadline.shrink,
    Effective.notAfter, decide_eq_true_eq] at *
  omega

/-- `DUR-13`'s deadline bounds every hot candidate at or after `earliest_hot`. -/
@[req "DUR-13"]
theorem Wall.belowFire_initial {earliest fireAt : Wall} (start now : Effective) (delay eps : Secs)
    (h : Wall.atOrBefore earliest fireAt = true) :
    Wall.belowFire (Wall.initialDeadline start delay now (some earliest) eps) fireAt eps now
      = true :=
  Deadline.initial_belowFire _ _ _ _ _ _ (by simpa [Wall.atOrBefore] using h)

/-- What the bound buys: a sample strictly below `T` and no earlier than the one the bound is
carried at is strictly before the candidate's fire time, so `SPN-38`'s window conjunct is false
and the freeze decides nothing. -/
@[req "DUR-14"]
theorem Effective.not_atOrAfter_of_belowFire {T fireAt : Wall} {eps : Secs} {a b : Effective}
    (h : Wall.belowFire T fireAt eps a = true) (hab : a.notAfter b = true)
    (hlt : b.deadlineReached T = false) : b.atOrAfter fireAt = false := by
  simp only [Wall.belowFire, Deadline.belowFire, Effective.notAfter, Effective.deadlineReached,
    Effective.atOrAfter, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le] at *
  omega

/-- The same, with the bound carried at the time ratchet and the step's own sample anywhere:
`DUR-7`'s driver at `max(ratchet, effective)` strictly below `T` puts both readings below it, so a
bound `T ≤ max(fire_at − ε, ratchet)` leaves `T ≤ fire_at − ε`, and the effective sample, below
`T`, is before the fire time, whether or not that sample is below the ratchet. -/
@[req "DUR-14"]
theorem Effective.not_atOrAfter_of_belowFire_latest {T fireAt : Wall} {eps : Secs}
    {a b : Effective} (h : Wall.belowFire T fireAt eps a = true)
    (hlt : (a.latest b).deadlineReached T = false) : b.atOrAfter fireAt = false := by
  simp only [Wall.belowFire, Deadline.belowFire, Effective.latest, Effective.deadlineReached,
    Effective.atOrAfter, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le] at *
  omega

/-- `Wall.earlier` is at or before each of its arguments: the two halves `DUR-13`'s `min` over the
pending hot candidates needs. -/
theorem Wall.earlier_atOrBefore_left (a b : Wall) : Wall.atOrBefore (Wall.earlier a b) a = true := by
  simp only [Wall.earlier, Wall.atOrBefore, decide_eq_true_eq]; split <;> omega

theorem Wall.earlier_atOrBefore_right (a b : Wall) : Wall.atOrBefore (Wall.earlier a b) b = true := by
  simp only [Wall.earlier, Wall.atOrBefore, decide_eq_true_eq]; split <;> omega

theorem Wall.atOrBefore_trans {a b c : Wall} (h1 : Wall.atOrBefore a b = true)
    (h2 : Wall.atOrBefore b c = true) : Wall.atOrBefore a c = true := by
  simp only [Wall.atOrBefore, decide_eq_true_eq] at *; omega

theorem Wall.atOrBefore_refl (a : Wall) : Wall.atOrBefore a a = true := by
  simp [Wall.atOrBefore]

theorem Wall.atOrBefore_antisymm {a b : Wall} (h1 : Wall.atOrBefore a b = true)
    (h2 : Wall.atOrBefore b a = true) : a = b := by
  cases a; cases b; simp only [Wall.atOrBefore, decide_eq_true_eq, Wall.mk.injEq] at *; omega

/-! ## `T` across two runs, and the prune pass's reading of a window (`SPN-41`) -/

/-- A sample strictly before `T` has not passed a window that closes at or after `T`: `DUR-20`'s
`[T, T + combine_slack_secs]` is open at its close before `T`. -/
theorem Effective.atOrBefore_plus_of_not_reached {now : Effective} {T : Wall} (s : Secs)
    (h : now.deadlineReached T = false) : now.atOrBefore (T.plus s) = true := by
  simp only [Effective.deadlineReached, Effective.atOrBefore, Wall.plus, decide_eq_true_eq,
    decide_eq_false_iff_not, Nat.not_le] at *
  omega

/-- A sample strictly before `T` is strictly before every later deadline. -/
theorem Effective.not_reached_of_atOrBefore {now : Effective} {T T' : Wall}
    (h : now.deadlineReached T = false) (hle : Wall.atOrBefore T T' = true) :
    now.deadlineReached T' = false := by
  simp only [Effective.deadlineReached, Wall.atOrBefore, decide_eq_true_eq,
    decide_eq_false_iff_not, Nat.not_le] at *
  omega

/-- `DUR-14`'s shrink at a sample strictly before `T` never raises it. -/
theorem Wall.shrinkDeadline_le_of_not_reached (T fireAt : Wall) (eps : Secs) (now : Effective)
    (h : now.deadlineReached T = false) : Wall.atOrBefore (Wall.shrinkDeadline T fireAt eps now) T = true := by
  simp only [Effective.deadlineReached, Wall.atOrBefore, Wall.shrinkDeadline, Deadline.shrink,
    decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le] at *
  omega

/-- `DUR-13`'s clamp, `max(min(T, T_computed), now)`, is at or before the computed value, which is
itself at or after `now`. -/
theorem Wall.clamp_le_initial (T : Wall) (start now : Effective) (delay eps : Secs)
    (earliest : Option Wall) :
    Wall.atOrBefore (Wall.shrinkDeadline T (Wall.initialDeadline start delay now earliest eps) 0 now)
      (Wall.initialDeadline start delay now earliest eps) = true := by
  simp only [Wall.atOrBefore, Wall.shrinkDeadline, Wall.initialDeadline, Deadline.shrink,
    Deadline.initialT, decide_eq_true_eq]
  omega

/-- Two optional instants, both absent or both present and in order: what `DUR-13`'s
`earliest_hot` is in two runs whose hot candidates are the same and whose `T` is in order. -/
def Wall.optAtOrBefore : Option Wall → Option Wall → Bool
  | none, none => true
  | some a, some b => Wall.atOrBefore a b
  | _, _ => false

theorem Wall.earlier_mono {a b c d : Wall} (h1 : Wall.atOrBefore a b = true)
    (h2 : Wall.atOrBefore c d = true) :
    Wall.atOrBefore (Wall.earlier a c) (Wall.earlier b d) = true := by
  simp only [Wall.earlier, Wall.atOrBefore, decide_eq_true_eq] at *
  split <;> split <;> omega

/-- `DUR-13`'s computed deadline is monotone in `earliest_hot`. -/
theorem Wall.initialDeadline_mono (start now : Effective) (delay eps : Secs)
    {ea eb : Option Wall} (h : Wall.optAtOrBefore ea eb = true) :
    Wall.atOrBefore (Wall.initialDeadline start delay now ea eps)
      (Wall.initialDeadline start delay now eb eps) = true := by
  cases ea <;> cases eb <;>
    simp_all [Wall.optAtOrBefore, Wall.atOrBefore, Wall.initialDeadline, Deadline.initialT] <;> omega

/-- The earlier of two samples is at or before the first. -/
theorem Effective.earlier_notAfter_left (a b : Effective) : (a.earlier b).notAfter a = true := by
  simp only [Effective.earlier, Effective.notAfter, decide_eq_true_eq]; split <;> omega

/-- `DUR-13`'s computed deadline is monotone in its start and in `earliest_hot`. -/
theorem Wall.initialDeadline_mono_start {fa fb : Effective} (delay : Secs) (now : Effective)
    (eps : Secs) (hf : fa.notAfter fb = true) {ea eb : Option Wall}
    (h : Wall.optAtOrBefore ea eb = true) :
    Wall.atOrBefore (Wall.initialDeadline fa delay now ea eps)
      (Wall.initialDeadline fb delay now eb eps) = true := by
  simp only [Effective.notAfter, decide_eq_true_eq] at hf
  cases ea <;> cases eb <;>
    simp_all [Wall.optAtOrBefore, Wall.atOrBefore, Wall.initialDeadline, Deadline.initialT] <;> omega

/-! ## The released charge and the time ratchet (`POL-19`, `DUR-7`) -/

/-- A raw wall sample past an expiry puts the effective time past it too: `SPN-13`'s
`effective_now = max(high_water, raw_now)` is at or above the raw sample. -/
theorem Effective.ofWall_not_atOrBefore {w : Wall} (hw : HighWater) {e : Wall}
    (h : Wall.atOrBefore w e = false) : (Effective.ofWall w hw).atOrBefore e = false := by
  simp only [Wall.atOrBefore, Effective.atOrBefore, Effective.ofWall, decide_eq_false_iff_not,
    Nat.not_le] at *
  omega

end BtcPolicy.Clocks
