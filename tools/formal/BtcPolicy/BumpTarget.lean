import BtcPolicy.Req
/-! `DUR-30`'s bump target: "with `tip` the node's tip height, `anchor = tip − (tip mod 6)`; …
`target = ⌊median / 5⌋ × 5`, quantised **down**." The median itself is `WTC-2`'s algorithm and is
not here; its domain is the integer it returns. -/

namespace BtcPolicy.BumpTarget

@[req "DUR-30"] def anchorStep : Nat := 6
@[req "DUR-30"] def quantum : Nat := 5

@[req "DUR-30"]
def anchor (tip : Nat) : Nat := tip - tip % anchorStep

@[req "DUR-30"]
def target (median : Nat) : Nat := median / quantum * quantum

/-- For EVERY median, `⌊median/5⌋ × 5 ≤ median < ⌊median/5⌋ × 5 + 5`. The gate sampled five. -/
@[req "DUR-30"]
theorem floor_interval (median : Nat) :
    target median ≤ median ∧ median < target median + quantum := by
  unfold target quantum; omega

/-- The gate's five sample points, so the finite check is reproduced as well. -/
@[req "DUR-30"]
theorem floor_interval_samples :
    ∀ m ∈ [0, quantum - 1, quantum, quantum + 1, quantum * 4 + 3],
      target m ≤ m ∧ m < target m + quantum := by decide

/-- "quantised **down**": the target is a multiple of five. -/
@[req "DUR-30"]
theorem target_is_quantised (median : Nat) : target median % quantum = 0 := by
  unfold target quantum; omega

/-- The anchor is a multiple of six at or below the tip, within five blocks of it. -/
@[req "DUR-30"]
theorem anchor_props (tip : Nat) :
    anchor tip % anchorStep = 0 ∧ anchor tip ≤ tip ∧ tip < anchor tip + anchorStep := by
  unfold anchor anchorStep; omega

/-- `DUR-30`'s own caveats, executable: tips straddling a multiple of six anchor apart (5 and 6
→ 0 and 6), and medians straddling a step quantise apart (4 and 5 → 0 and 5). The reducers
"narrow the split without closing it". -/
@[req "DUR-30"]
theorem straddle_exhibits :
    anchor 5 = 0 ∧ anchor 6 = 6 ∧ target 4 = 0 ∧ target 5 = 5 := by decide

/-- What the reducers do buy: tips within one six-block bucket anchor identically. -/
@[req "DUR-30"]
theorem same_bucket_same_anchor (tip k : Nat) (hk : k < anchorStep - tip % anchorStep) :
    anchor (tip + k) = anchor tip := by
  unfold anchor anchorStep at *; omega

end BtcPolicy.BumpTarget
