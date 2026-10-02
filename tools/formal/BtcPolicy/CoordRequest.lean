import BtcPolicy.Encode
/-! `WIR-21`'s coordinator-request preimage: "the tag byte then the fields", built with `WIR-18`'s
moves, and the message the coordinator signs is the tagged hash of `wallet_id ‖ preimage` "with
the 32-byte `wallet_id` prepended and never transmitted". The three classes are one inductive,
so the tag byte is the constructor and "a Refresh signature over identical fields never verifies
as a Clawback" (`WIR-31`) is the first byte differing. `coord_sig` has no field here: "`coord_sig`
is excluded from its own preimage" by construction. The hash itself is `check_vectors.py`'s. -/

namespace BtcPolicy.CoordRequest
open BtcPolicy.Encode

/-- The three request classes with the fields `WIR-21` frames. Base64 texts are their bytes. -/
inductive Request
  | spend (spend escape : Bytes) (rungs : List Bytes) (pin nonce : Bytes) (expiry policyVersion : Nat)
  | refresh (refresh nonce : Bytes) (expiry policyVersion : Nat)
  | clawback (clawback nonce : Bytes) (expiry policyVersion : Nat)
  deriving DecidableEq, Repr

/-- `WIR-21`, line by line. The rungs are `WIR-18`'s `list`: "The rung count is written even
when zero". -/
@[req "WIR-21"]
def encode : Request → Bytes
  | .spend s e rungs pin nonce expiry pv =>
    u8 0x01 ++ var s ++ var e ++ list rungs ++ var pin ++ var nonce ++ u64 expiry ++ u32 pv
  | .refresh r nonce expiry pv => u8 0x02 ++ var r ++ var nonce ++ u64 expiry ++ u32 pv
  | .clawback c nonce expiry pv => u8 0x03 ++ var c ++ var nonce ++ u64 expiry ++ u32 pv

/-- What is hashed: "`wallet_id ‖ preimage`". -/
@[req "WIR-21"]
def message (walletId : Bytes) (r : Request) : Bytes := fixed walletId ++ encode r

def readTail (bs : Bytes) : Option (Nat × Nat) := do
  let (expiry, bs) ← readLE 8 bs
  let (pv, bs) ← readLE 4 bs
  match bs with
  | [] => pure (expiry, pv)
  | _ => none

/-- The decoder, on the tag byte; consumes the whole string or refuses. -/
@[req "WIR-21"]
def decode : Bytes → Option Request
  | 0x01 :: bs => do
    let (s, bs) ← readVar bs
    let (e, bs) ← readVar bs
    let (rungs, bs) ← readList bs
    let (pin, bs) ← readVar bs
    let (nonce, bs) ← readVar bs
    let (expiry, pv) ← readTail bs
    pure (.spend s e rungs pin nonce expiry pv)
  | 0x02 :: bs => do
    let (r, bs) ← readVar bs
    let (nonce, bs) ← readVar bs
    let (expiry, pv) ← readTail bs
    pure (.refresh r nonce expiry pv)
  | 0x03 :: bs => do
    let (c, bs) ← readVar bs
    let (nonce, bs) ← readVar bs
    let (expiry, pv) ← readTail bs
    pure (.clawback c nonce expiry pv)
  | _ => none

/-- The admitted domain: every `var` below `2^32` bytes, the integers in their widths. -/
abbrev WF : Request → Prop
  | .spend s e rungs pin nonce expiry pv =>
    s.length < 256 ^ 4 ∧ e.length < 256 ^ 4 ∧ rungs.length < 256 ^ 4 ∧
    (∀ b ∈ rungs, b.length < 256 ^ 4) ∧ pin.length < 256 ^ 4 ∧ nonce.length < 256 ^ 4 ∧
    expiry < 256 ^ 8 ∧ pv < 256 ^ 4
  | .refresh r nonce expiry pv =>
    r.length < 256 ^ 4 ∧ nonce.length < 256 ^ 4 ∧ expiry < 256 ^ 8 ∧ pv < 256 ^ 4
  | .clawback c nonce expiry pv =>
    c.length < 256 ^ 4 ∧ nonce.length < 256 ^ 4 ∧ expiry < 256 ^ 8 ∧ pv < 256 ^ 4

theorem readLE_le_nil (n v : Nat) (h : v < 256 ^ n) : readLE n (le n v) = some (v, []) := by
  simpa using readLE_le n v h []

theorem readTail_enc (expiry pv : Nat) (he : expiry < 256 ^ 8) (hp : pv < 256 ^ 4) :
    readTail (u64 expiry ++ u32 pv) = some (expiry, pv) := by
  simp [readTail, u64, u32, readLE_le 8 _ he, readLE_le_nil 4 _ hp]

/-- On the admitted domain the preimage reads back exactly. -/
@[req "WIR-21"]
theorem decode_encode (r : Request) (h : WF r) : decode (encode r) = some r := by
  cases r with
  | spend s e rungs pin nonce expiry pv =>
    obtain ⟨hs, he, hk, hr, hpin, hn, hx, hp⟩ := h
    simp [decode, encode, u8, List.append_assoc, readVar_var _ hs, readVar_var _ he,
      readList_list rungs hk hr, readVar_var _ hpin, readVar_var _ hn, readTail_enc _ _ hx hp]
  | refresh r nonce expiry pv =>
    obtain ⟨hr, hn, hx, hp⟩ := h
    simp [decode, encode, u8, List.append_assoc, readVar_var _ hr, readVar_var _ hn,
      readTail_enc _ _ hx hp]
  | clawback c nonce expiry pv =>
    obtain ⟨hc, hn, hx, hp⟩ := h
    simp [decode, encode, u8, List.append_assoc, readVar_var _ hc, readVar_var _ hn,
      readTail_enc _ _ hx hp]

/-- Two well-formed requests with one preimage are one request — across classes too, since the
tag byte is part of the preimage. -/
@[req "WIR-21"]
theorem encode_injective (a b : Request) (ha : WF a) (hb : WF b) (h : encode a = encode b) :
    a = b := by
  have := decode_encode a ha
  rw [h, decode_encode b hb] at this
  exact (Option.some.inj this).symm

/-- `WIR-21`: "The rung count is written even when zero" — a Spend with no rungs carries the four
zero bytes of the count between `escape` and `pin`. -/
@[req "WIR-21"]
theorem rung_count_written_when_zero (s e pin nonce : Bytes) (expiry pv : Nat) :
    encode (.spend s e [] pin nonce expiry pv) =
      u8 0x01 ++ var s ++ var e ++ [0, 0, 0, 0] ++ var pin ++ var nonce ++ u64 expiry ++ u32 pv := by
  simp [encode, list, le]

/-- `WIR-31`: "the tag byte is the first preimage byte, so a Refresh signature over identical
fields never verifies as a Clawback": the two preimages differ at byte 0. -/
@[req "WIR-31"]
theorem refresh_ne_clawback (r nonce : Bytes) (expiry pv : Nat) :
    encode (.refresh r nonce expiry pv) ≠ encode (.clawback r nonce expiry pv) := by
  intro h
  have := congrArg List.head? h
  simp [encode, u8] at this

/-- The preimage length: one tag byte, four plus the bytes per `var`, four per count, twelve for
the tail. -/
@[req "WIR-21"]
theorem encode_length_refresh (r nonce : Bytes) (expiry pv : Nat) :
    (encode (.refresh r nonce expiry pv)).length = 21 + r.length + nonce.length := by
  simp [encode, u8, u64, u32, var_length, le_length]; omega

/-! ## `WIR-31`'s three vectors, under `wallet_id = 0x11 × 32` -/

def walletId : Bytes := List.replicate 32 0x11

/-- `spend = "cHNidP8BSPEND"`, `escape = "cHNidP8BESCAPE"`, no rungs, `pin = "246802"`,
`nonce = "nonce-vector"`, `expiry = 1752500000`, `policy_version = 1`. -/
def spendVector : Request :=
  .spend [0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x53, 0x50, 0x45, 0x4e, 0x44]
         [0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x45, 0x53, 0x43, 0x41, 0x50, 0x45]
         [] [0x32, 0x34, 0x36, 0x38, 0x30, 0x32]
         [0x6e, 0x6f, 0x6e, 0x63, 0x65, 0x2d, 0x76, 0x65, 0x63, 0x74, 0x6f, 0x72]
         1752500000 1

/-- `refresh = "cHNidP8BREFRESH"`, `nonce = "r-1"`, same expiry and version. -/
def refreshVector : Request :=
  .refresh [0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x52, 0x45, 0x46, 0x52, 0x45, 0x53, 0x48]
           [0x72, 0x2d, 0x31] 1752500000 1

/-- `clawback = "cHNidP8BCLAWBACK"`, `nonce = "c-1"`, same expiry and version. -/
def clawbackVector : Request :=
  .clawback [0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x43, 0x4c, 0x41, 0x57, 0x42, 0x41, 0x43, 0x4b]
            [0x63, 0x2d, 0x31] 1752500000 1

/-- The published hashed messages, wallet id first. -/
def spendPreimage : Bytes :=
  [ 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x01, 0x0d, 0x00, 0x00, 0x00, 0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x53, 0x50, 0x45, 0x4e, 0x44, 0x0e, 0x00, 0x00, 0x00, 0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x45, 0x53,
    0x43, 0x41, 0x50, 0x45, 0x00, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x32, 0x34, 0x36, 0x38, 0x30, 0x32, 0x0c, 0x00, 0x00, 0x00, 0x6e, 0x6f, 0x6e, 0x63, 0x65, 0x2d, 0x76, 0x65, 0x63, 0x74,
    0x6f, 0x72, 0x20, 0x07, 0x75, 0x68, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00 ]

def refreshPreimage : Bytes :=
  [ 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x02, 0x0f, 0x00, 0x00, 0x00, 0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x52, 0x45, 0x46, 0x52, 0x45, 0x53, 0x48, 0x03, 0x00, 0x00, 0x00, 0x72, 0x2d, 0x31, 0x20, 0x07, 0x75, 0x68, 0x00,
    0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00 ]

def clawbackPreimage : Bytes :=
  [ 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x03, 0x10, 0x00, 0x00, 0x00, 0x63, 0x48, 0x4e, 0x69, 0x64, 0x50, 0x38, 0x42, 0x43, 0x4c, 0x41, 0x57, 0x42, 0x41, 0x43, 0x4b, 0x03, 0x00, 0x00, 0x00, 0x63, 0x2d, 0x31, 0x20, 0x07, 0x75, 0x68,
    0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00 ]

set_option maxRecDepth 10000 in
/-- Each vector's fields frame to the published message, and the preimage after the wallet id
decodes back to the fields. -/
@[req "WIR-31"]
theorem vectors_reproduce :
    message walletId spendVector = spendPreimage ∧
    message walletId refreshVector = refreshPreimage ∧
    message walletId clawbackVector = clawbackPreimage ∧
    decode (spendPreimage.drop 32) = some spendVector ∧
    decode (refreshPreimage.drop 32) = some refreshVector ∧
    decode (clawbackPreimage.drop 32) = some clawbackVector := by
  decide +kernel

end BtcPolicy.CoordRequest
