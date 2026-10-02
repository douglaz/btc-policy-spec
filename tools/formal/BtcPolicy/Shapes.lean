import BtcPolicy.Req
/-! `CHN-2`'s federation shapes: "A production vault MUST have `t ≥ 2` and exactly `n = 2t − 1`,
for two reasons that only together give the constraint: any two subsets of size `t` intersect, so
no unfrozen signing quorum exists outside an armed set (`2t > n`), and `t` honest nodes remain
after every `t − 1` withholding minority (`n − (t − 1) ≥ t`). The permitted shapes are therefore
2-of-3, 3-of-5, 4-of-7, up to 8-of-15; `n ≤ 15`". -/

namespace BtcPolicy.Shapes

@[req "CHN-2"] def minT : Nat := 2
@[req "CHN-2"] def maxT : Nat := 8
@[req "CHN-2"] def nodeLimit : Nat := 15

/-- The shape rule's two figures, `n = 2t − 1`: the copies gate reads both back out of `CHN-2`. -/
@[req "CHN-2"] def coefficient : Nat := 2
@[req "CHN-2"] def offset : Nat := 1

/-- The shape rule, `n = 2t − 1`. -/
@[req "CHN-2"]
def nOf (t : Nat) : Nat := coefficient * t - offset

@[req "CHN-2"]
theorem nOf_eq (t : Nat) : nOf t = 2 * t - 1 := rfl

/-- The two reasons, as `Bool` predicates so `decide` elaborates without a separate instance. -/
@[req "CHN-2"]
def quorumsIntersect (t n : Nat) : Bool := 2 * t > n
@[req "CHN-2"]
def toleratesWithholding (t n : Nat) : Bool := n - (t - 1) ≥ t

/-- The published shapes, from `minT` to `maxT`. -/
@[req "CHN-2"]
def shapes : List (Nat × Nat) := (List.range' minT (maxT - minT + 1)).map fun t => (t, nOf t)

/-- The largest node count, `8-of-15`'s `15`. -/
@[req "CHN-2"] def maxN : Nat := nOf maxT

/-- The list is exactly the seven the requirement names. -/
@[req "CHN-2"]
theorem shapes_published :
    shapes = [(2, 3), (3, 5), (4, 7), (5, 9), (6, 11), (7, 13), (8, 15)] := by decide

/-- The maximum shape is `8-of-15`, it IS the node limit, and the next shape is over it: "up to
8-of-15; `n ≤ 15`" is one figure, derived, not two figures that agree today. -/
@[req "CHN-2"]
theorem max_shape : nOf maxT = 15 ∧ nOf maxT = nodeLimit ∧ nodeLimit < nOf (maxT + 1) := by decide

/-- Decided over the range the gate walked: every shape has both properties. -/
@[req "CHN-2"]
theorem shapes_decided :
    ∀ p ∈ shapes, quorumsIntersect p.1 p.2 = true ∧ toleratesWithholding p.1 p.2 = true := by
  decide

/-- For EVERY `t ≥ 1`, `n = 2t − 1` gives both properties; `t ≥ 2` is `CHN-2`'s floor, not what
the arithmetic needs. -/
@[req "CHN-2"]
theorem shape_general (t : Nat) (ht : 1 ≤ t) :
    quorumsIntersect t (nOf t) = true ∧ toleratesWithholding t (nOf t) = true := by
  unfold quorumsIntersect toleratesWithholding nOf coefficient offset; constructor <;> simp <;> omega

/-- Why "only together": `n = 2t − 1` is the LARGEST `n` with intersecting quorums and the
SMALLEST `n` tolerating a `t − 1` withholding minority, so the two constraints pin `n` exactly. -/
@[req "CHN-2"]
theorem shape_is_pinned (t n : Nat) (ht : 1 ≤ t) :
    (quorumsIntersect t n = true ∧ toleratesWithholding t n = true) ↔ n = nOf t := by
  unfold quorumsIntersect toleratesWithholding nOf coefficient offset; simp; omega

/-- Two `t`-subsets of `2t − 1` nodes share exactly one guaranteed member — never more — which is
why `DUR-8` says the holder count "cannot prove `t` honest nodes froze". -/
@[req "CHN-2"]
theorem intersection_is_one_node (t : Nat) (ht : 1 ≤ t) : 2 * t - nOf t = 1 := by
  unfold nOf coefficient offset; omega

end BtcPolicy.Shapes
