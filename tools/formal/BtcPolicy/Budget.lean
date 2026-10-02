import BtcPolicy.Req
import BtcPolicy.Shapes
import BtcPolicy.Formula
/-! `POL-20`'s admission coefficient and `ADR-0014`'s delayed-holder trace as data.

`POL-20`: "Its admitted outflow is at most `((n − c) / (t − c)) × cap` … For the production shape
`n = 2t − 1`, the coefficient at `c = 0` is `(2 − 1/t)`, below `2 × cap` in outflow, and the full
`c = t − 1` tolerance admits at most `t × cap` for that cohort."

These are the coefficient proofs, not the admission-accounting theorem: that `POL-18`/`POL-19`'s
reserve, refund and age-out transitions establish the counting premises for `POL-20`'s cohort is
`BtcPolicy.Ledger`'s. Likewise the trace below is the timeline as data — every row the arithmetic
gate checked — not a lifecycle exhibit showing each row reachable; the run that makes it reachable
is `BtcPolicy.Exhibits.HotLedger`, and it reads its instants from the `timeline` below rather than
restating them. -/

open Std

namespace BtcPolicy.Budget

/-- `POL-20`'s counting coefficient, in exact rationals: `(n − c) / (t − c)`. -/
@[req "POL-20"]
def coef (n t c : Nat) : Rat := ((n : Rat) - c) / ((t : Rat) - c)

/-- The figure `POL-20` states as the ceiling at `c = 0`: "below `2 × cap`". -/
@[req "POL-20"] def upperMultiple : Nat := 2
/-- The numerator of the `1/t` term in `(2 − 1/t)`: one, and the copies gate reads it back. -/
@[req "POL-20"] def c0Numerator : Nat := 1

/-! The three formulas `POL-20` writes, as the copies gate reads them, each rendered from an
expression (`BtcPolicy.Formula`) the theorem beside it proves evaluates to `coef` or to the
figure `POL-20` gives, so string and rule move together. -/
open Formula in
def coefExpr : Expr := .paren (.div (.paren (.sub (.var "n") (.var "c"))) (.paren (.sub (.var "t") (.var "c"))))
open Formula in
def c0Expr : Expr := .paren (.sub (.lit upperMultiple) (.divTight (.lit c0Numerator) (.var "t")))
open Formula in
def fullToleranceExpr : Expr := .mul (.var "t") (.var "cap")

@[req "POL-20"] def coefFormula : String := Formula.render coefExpr
@[req "POL-20"] def c0Formula : String := Formula.render c0Expr
@[req "POL-20"] def fullToleranceFormula : String := s!"`{Formula.render fullToleranceExpr}`"

@[req "POL-20"]
theorem formulas_render :
    coefFormula = "((n − c) / (t − c))" ∧ c0Formula = "(2 − 1/t)" ∧
    fullToleranceFormula = "`t × cap`" := by decide

/-- Per shape of `CHN-2`'s list — `Shapes.shapes`, not a second copy — the gate's loop: `c = 0` gives `2 − 1/t`, strictly below 2; `c = t − 1` gives `t`. -/
@[req "POL-20"]
theorem per_shape_decided :
    ∀ p ∈ Shapes.shapes,
      coef p.2 p.1 0 = upperMultiple - 1 / (p.1 : Rat) ∧
      coef p.2 p.1 0 < upperMultiple ∧
      coef p.2 p.1 (p.1 - 1) = (p.1 : Rat) := by
  decide +kernel

/-! The general form. `n = 2t − 1` is stated as `n + 1 = 2t` so no truncating `Nat` subtraction is
cast into `Rat`. -/

/-- For EVERY `t ≥ 1` and `n = 2t − 1`, the `c = 0` coefficient is `2 − 1/t`. -/
@[req "POL-20"]
theorem coef_c0 (n t : Nat) (ht : 1 ≤ t) (h : n + 1 = 2 * t) :
    coef n t 0 = upperMultiple - 1 / (t : Rat) := by
  unfold coef upperMultiple
  have hc : (n : Rat) + 1 = 2 * (t : Rat) := by exact_mod_cast h
  have ht' : (t : Rat) ≠ 0 := by
    have : (0 : Rat) < t := Rat.natCast_pos.mpr (by omega)
    exact Ne.symm (ne_of_lt this)
  simp
  grind

/-- `c = 0`: strictly below 2, for every `t ≥ 1`. -/
@[req "POL-20"]
theorem coef_c0_lt_two (n t : Nat) (ht : 1 ≤ t) (h : n + 1 = 2 * t) : coef n t 0 < upperMultiple := by
  rw [coef_c0 n t ht h]; unfold upperMultiple
  have : (0 : Rat) < 1 / (t : Rat) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr (Rat.natCast_pos.mpr (by omega))
  grind

/-- `c = t − 1`: the coefficient is `t`, for every `t ≥ 1`. -/
@[req "POL-20"]
theorem coef_full_tolerance (n t c : Nat) (h : n + 1 = 2 * t) (hc : c + 1 = t) :
    coef n t c = (t : Rat) := by
  unfold coef
  have h1 : (n : Rat) + 1 = 2 * (t : Rat) := by exact_mod_cast h
  have h2 : (c : Rat) + 1 = (t : Rat) := by exact_mod_cast hc
  grind

/-- The whole curve for `c < t`: `2 + (c − 1)/(t − c)`, rising from `2 − 1/t` to `t`. -/
@[req "POL-20"]
theorem coef_general (n t c : Nat) (h : n + 1 = 2 * t) (hct : c < t) :
    coef n t c = 2 + ((c : Rat) - 1) / ((t : Rat) - c) := by
  unfold coef
  have h1 : (n : Rat) + 1 = 2 * (t : Rat) := by exact_mod_cast h
  have hne : (t : Rat) - c ≠ 0 := by
    have : (c : Rat) < t := by exact_mod_cast hct
    grind
  grind

/-! ## The formulas evaluate to the definitions -/

/-- `((n − c) / (t − c))` IS `coef`. -/
@[req "POL-20"]
theorem coef_expr_agrees (n t c : Nat) :
    Formula.evalRat (fun s => if s = "n" then n else if s = "t" then t else if s = "c" then c else 0)
      coefExpr = coef n t c := by
  simp [Formula.evalRat, coefExpr, coef]

/-- `(2 − 1/t)` IS `coef` at `c = 0` for every admitted shape (`coef_c0`). -/
@[req "POL-20"]
theorem c0_expr_agrees (n t : Nat) (ht : 1 ≤ t) (h : n + 1 = 2 * t) :
    Formula.evalRat (fun s => if s = "t" then t else 0) c0Expr = coef n t 0 := by
  rw [coef_c0 n t ht h]; simp [Formula.evalRat, c0Expr, upperMultiple, c0Numerator]

/-- `t × cap` IS the full-tolerance bound: `coef` at `c = t − 1` times `cap`. -/
@[req "POL-20"]
theorem full_tolerance_expr_agrees (n t c cap : Nat) (h : n + 1 = 2 * t) (hc : c + 1 = t) :
    Formula.evalRat (fun s => if s = "t" then t else if s = "cap" then cap else 0)
      fullToleranceExpr = coef n t c * cap := by
  rw [coef_full_tolerance n t c h hc]; simp [Formula.evalRat, fullToleranceExpr]

/-! ## `ADR-0014`'s delayed-holder trace, as data

"take a 2-of-3 federation with no compromised node, cap `V`, `hot_window_secs =
max_commitment_age_secs = 120`, `hold_secs = 20`, `combine_slack_secs = 100`, and
`delivery_horizon_secs = 60`." The rows are the timeline; every row check the arithmetic gate ran
is a theorem here. What a lifecycle model would need that this does not carry: that `DUR-8`
withholds the first release until the holder decision, that the decision at 100 is admitted by
`DUR-6`, that the second acceptance at 121 passes `POL-16` because the first reservation is not
`live`, that pruning has not collected the first candidate, and that the completion at 141 is a
fresh exposure. -/

structure Params where
  t : Nat
  n : Nat
  window : Nat     -- hot_window_secs = max_commitment_age_secs
  hold : Nat       -- hold_secs
  slack : Nat      -- combine_slack_secs
  horizon : Nat    -- delivery_horizon_secs
  deriving Repr

@[req "POL-20"]
def params : Params := { t := 2, n := 3, window := 120, hold := 20, slack := 100, horizon := 60 }

structure Timeline where
  firstAccept : Nat
  firstExpiry : Nat
  firstHold : Nat
  firstComplete : Nat
  boundary : Nat
  secondAccept : Nat
  secondExpiry : Nat
  secondComplete : Nat
  deriving Repr

@[req "POL-20"]
def timeline : Timeline :=
  { firstAccept := 0, firstExpiry := 120, firstHold := 20, firstComplete := 100, boundary := 120,
    secondAccept := 121, secondExpiry := 241, secondComplete := 141 }

/-- The stated conclusion: the completion interval `[100, 220)`, its length, its content in
units of `V`, and the withdrawn coefficient `3/2`. -/
@[req "POL-20"] def intervalStart : Nat := 100
@[req "POL-20"] def intervalEnd : Nat := 220
@[req "POL-20"] def statedLength : Nat := 120
@[req "POL-20"] def statedTotalV : Nat := 2
@[req "POL-20"] def withdrawnNumerator : Nat := 3
@[req "POL-20"] def withdrawnDenominator : Nat := 2

/-- Every row the arithmetic gate checked, as one decided conjunction. -/
@[req "POL-20"]
theorem rows_hold :
    let p := params; let tl := timeline
    tl.firstAccept + p.window = tl.firstExpiry ∧
    tl.firstAccept + p.hold = tl.firstHold ∧
    p.horizon < p.window ∧                                            -- MAN-9 refuses equality
    p.hold + p.slack ≤ p.window ∧
    (tl.firstHold ≤ tl.firstComplete ∧
      tl.firstComplete < min tl.firstExpiry (tl.firstHold + p.slack)) ∧
    tl.firstAccept + p.window = tl.boundary ∧
    tl.secondAccept > max tl.boundary tl.firstExpiry ∧
    tl.secondAccept + p.window = tl.secondExpiry ∧
    tl.secondAccept + p.hold = tl.secondComplete ∧
    intervalEnd - intervalStart = statedLength ∧
    statedLength = p.window := by
  decide

/-- Completions inside `[start, stop)`, counted from the timeline. -/
def completedIn (start stop : Nat) (tl : Timeline) : Nat :=
  [tl.firstComplete, tl.secondComplete].countP fun w => start ≤ w && w < stop

@[req "POL-20"]
theorem outflow_two_V : completedIn intervalStart intervalEnd timeline = statedTotalV := by decide

/-- The withdrawn coefficient is `n/t = 3/2`, and the trace exceeds it. -/
@[req "POL-20"]
theorem exceeds_withdrawn_bound :
    ((params.n : Rat) / params.t) = (withdrawnNumerator : Rat) / withdrawnDenominator ∧
    (statedTotalV : Rat) > (withdrawnNumerator : Rat) / withdrawnDenominator := by
  decide +kernel

/-- `POL-19`'s liveness predicate, both boundaries inclusive, written without truncating
subtraction: `reserved_at ≥ now_mono − window ∨ wall_now ≤ expiry`. -/
@[req "POL-19"]
def live (reservedAt nowMono window wallNow expiry : Nat) : Bool :=
  reservedAt + window ≥ nowMono || wallNow ≤ expiry

/-- The two instants the trace turns on, under stable clocks: at 120 the first reservation is
"Still charged at equality"; at 121 it has aged out under BOTH clocks. -/
@[req "POL-19"]
theorem reservation_boundary :
    live timeline.firstAccept 120 params.window 120 timeline.firstExpiry = true ∧
    live timeline.firstAccept 121 params.window 121 timeline.firstExpiry = false := by
  decide

end BtcPolicy.Budget
