import BtcPolicy.Req
/-! `MAN-16`'s preimage widths: "a 63-bit-wide value whose top bit is pinned — 62 bits of entropy,
a 2⁶² search space — presented as exactly 16 hex characters (8 bytes)." Four derivations from one
operand. Counting `2^62` admissible values is arithmetic; calling that *entropy* also assumes the
sampling is uniform, which width alone does not give. -/

namespace BtcPolicy.Preimage

@[req "MAN-16"] def width : Nat := 63

/-- A pinned top bit leaves `width − 1` free bits. -/
@[req "MAN-16"]
def entropyBits (w : Nat) : Nat := w - 1

/-- Bytes needed for `w` bits, `⌈w / 8⌉`. -/
@[req "MAN-16"]
def bytesFor (w : Nat) : Nat := (w + 7) / 8

/-- Two hex characters per byte. -/
@[req "MAN-16"]
def hexChars (w : Nat) : Nat := 2 * bytesFor w

@[req "MAN-16"] def publishedEntropy : Nat := 62
@[req "MAN-16"] def publishedBytes : Nat := 8
@[req "MAN-16"] def publishedHex : Nat := 16

@[req "MAN-16"]
theorem widths_derived :
    entropyBits width = publishedEntropy ∧ bytesFor width = publishedBytes ∧
    hexChars width = publishedHex := by decide

/-- The search-space exponent is the entropy, for every width with a pinned bit. -/
@[req "MAN-16"]
theorem exponent_is_entropy (w : Nat) (h : 1 ≤ w) : 2 ^ entropyBits w * 2 = 2 ^ w := by
  unfold entropyBits
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp [Nat.pow_succ]

end BtcPolicy.Preimage
