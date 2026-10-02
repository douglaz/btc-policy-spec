import BtcPolicy.Req
/-! A formula the copies gate reads out of a requirement is RENDERED from an expression, and the
expression is PROVED to evaluate to the definition it describes. That is what binds the string in
the Markdown to the rule the theorems are about: a change to either without the other is a red
theorem or a red copies gate, never a green pair of contradictions (`ADR-0023` decision 5).

`render` and `renderNat` write the expression as the requirements write it — `/` for the rational
division and, in `renderNat`, `÷` for the integer one, `−` for subtraction, `×` for multiplication,
`max(…, …)`, `min(…, …)`. `evalNat` gives the `Nat`
semantics the lifecycle formulas have (saturating subtraction, floor division); `evalRat` the
exact-rational semantics `POL-20`'s coefficient has. -/

open Std

namespace BtcPolicy.Formula

inductive Expr
  | var (name : String)
  | lit (n : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | divTight (a b : Expr)   -- rendered without spaces, as `POL-20` writes `1/t`
  | max (a b : Expr)
  | min (a b : Expr)
  | paren (a : Expr)
  deriving Repr

def render : Expr → String
  | .var s => s
  | .lit n => toString n
  | .add a b => s!"{render a} + {render b}"
  | .sub a b => s!"{render a} − {render b}"
  | .mul a b => s!"{render a} × {render b}"
  | .div a b => s!"{render a} / {render b}"
  | .divTight a b => s!"{render a}/{render b}"
  | .max a b => s!"max({render a}, {render b})"
  | .min a b => s!"min({render a}, {render b})"
  | .paren a => s!"({render a})"

/-- `÷` is how `SPN-38` writes integer division; `/` is how `POL-20` writes the rational one.
Rendering the same node two ways would let one string describe two semantics, so `Nat` formulas
render through this variant. -/
def renderNat : Expr → String
  | .div a b => s!"{renderNat a} ÷ {renderNat b}"
  | .add a b => s!"{renderNat a} + {renderNat b}"
  | .sub a b => s!"{renderNat a} − {renderNat b}"
  | .mul a b => s!"{renderNat a} × {renderNat b}"
  | .max a b => s!"max({renderNat a}, {renderNat b})"
  | .min a b => s!"min({renderNat a}, {renderNat b})"
  | .paren a => s!"({renderNat a})"
  | e => render e

def evalNat (env : String → Nat) : Expr → Nat
  | .var s => env s
  | .lit n => n
  | .add a b => evalNat env a + evalNat env b
  | .sub a b => evalNat env a - evalNat env b
  | .mul a b => evalNat env a * evalNat env b
  | .div a b => evalNat env a / evalNat env b
  | .divTight a b => evalNat env a / evalNat env b
  | .max a b => Max.max (evalNat env a) (evalNat env b)
  | .min a b => Min.min (evalNat env a) (evalNat env b)
  | .paren a => evalNat env a

def evalRat (env : String → Rat) : Expr → Rat
  | .var s => env s
  | .lit n => n
  | .add a b => evalRat env a + evalRat env b
  | .sub a b => evalRat env a - evalRat env b
  | .mul a b => evalRat env a * evalRat env b
  | .div a b => evalRat env a / evalRat env b
  | .divTight a b => evalRat env a / evalRat env b
  | .max a b => Max.max (evalRat env a) (evalRat env b)
  | .min a b => Min.min (evalRat env a) (evalRat env b)
  | .paren a => evalRat env a

end BtcPolicy.Formula
