import BtcPolicy.Req
/-! `NCH-12`'s freshness window, the one number `WIR-16` copies and `NCH-13`'s prune offset is
defined equal to: "An envelope is
**fresh** iff `timestamp ∈ [now − 300, now + 60]`". -/

namespace BtcPolicy.Freshness

/-- The window's two bounds. -/
@[req "NCH-12"] def past : Nat := 300
@[req "NCH-12"] def future : Nat := 60

/-- The width the gate printed: 360 seconds. -/
@[req "NCH-12"]
theorem width : past + future = 360 := by decide

/-- `NCH-13` prunes "seen nonces whose recorded timestamp is below `now − 300`": the prune offset
is the window's past bound, so a nonce is forgotten exactly when its envelope could no longer be
fresh. -/
@[req "NCH-13"] def pruneOffset : Nat := past

@[req "NCH-13"]
theorem prune_matches_window : pruneOffset = past := rfl

end BtcPolicy.Freshness
