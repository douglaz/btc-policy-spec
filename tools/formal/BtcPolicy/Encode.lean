import BtcPolicy.Req
/-! The two byte encoders: `WIR-18`'s five little-endian moves,
which every signed or hashed byte string except the commitment is built with, and `CHN-25`'s
commitment encoding, "the ONE big-endian encoding in the system". A byte is a `Nat` below 256; a
byte string is a `List Nat`. Each encoder has a decoder that consumes exactly what the encoder
wrote, and the properties are the decoder's: `decode (encode x) = some x` on the well-formed
domain, so `encode` is injective there and every published length follows from the widths.

Framing stops at the digest: `CHN-26`'s SHA-256 and `WIR-19`'s tagged hash are not here
(decision 3, and the bead: no SHA-256 in Lean); `check_vectors.py` hashes what these encoders
frame. What `CHN-24`'s "Two distinct transactions MUST never share a commitment" rests on is
therefore two things: `encode_injective` below, and a named collision assumption on `CHN-26`'s
hash over the admitted domain. -/

namespace BtcPolicy.Encode

abbrev Bytes := List Nat

/-! ## Fixed-width integers, both byte orders -/

/-- `n` bytes of `v`, most significant first: `CHN-25`'s "every integer big-endian". -/
@[req "CHN-25"]
def be : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, v => be n (v / 256) ++ [v % 256]

/-- `n` bytes of `v`, least significant first: `WIR-18`'s "little-endian throughout". -/
@[req "WIR-18"]
def le : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, v => v % 256 :: le n (v / 256)

theorem be_length (n v : Nat) : (be n v).length = n := by
  induction n generalizing v with
  | zero => simp [be]
  | succ n ih => simp [be, ih]

theorem le_length (n v : Nat) : (le n v).length = n := by
  induction n generalizing v with
  | zero => simp [le]
  | succ n ih => simp [le, ih]

def beVal (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

def leVal : Bytes → Nat
  | [] => 0
  | b :: bs => b + 256 * leVal bs

theorem beVal_append_single (l : Bytes) (b : Nat) : beVal (l ++ [b]) = beVal l * 256 + b := by
  simp [beVal, List.foldl_append]

theorem beVal_be (n v : Nat) (h : v < 256 ^ n) : beVal (be n v) = v := by
  induction n generalizing v with
  | zero => simp [be, beVal]; omega
  | succ n ih =>
    rw [Nat.pow_succ] at h
    simp only [be, beVal_append_single, ih (v / 256) (by omega)]
    omega

theorem leVal_le (n v : Nat) (h : v < 256 ^ n) : leVal (le n v) = v := by
  induction n generalizing v with
  | zero => simp [le, leVal]; omega
  | succ n ih =>
    rw [Nat.pow_succ] at h
    simp only [le, leVal, ih (v / 256) (by omega)]
    omega

/-- The two byte orders differ on every multi-byte value that is not a palindrome; one value
suffices to keep the encoders apart (`CHN-25`: "do not carry either convention into the other"). -/
@[req "CHN-25"]
theorem be_ne_le : be 4 1 ≠ le 4 1 := by decide

/-! ## Reading back -/

def takeN : Nat → Bytes → Option (Bytes × Bytes)
  | 0, bs => some ([], bs)
  | _ + 1, [] => none
  | n + 1, b :: bs => (takeN n bs).map fun (h, t) => (b :: h, t)

theorem takeN_append (l rest : Bytes) : takeN l.length (l ++ rest) = some (l, rest) := by
  induction l with
  | nil => simp [takeN]
  | cons b l ih => simp [takeN, ih]

theorem takeN_append' {n : Nat} {l : Bytes} (h : l.length = n) (rest : Bytes) :
    takeN n (l ++ rest) = some (l, rest) := by
  subst h; exact takeN_append l rest

def readBE (n : Nat) (bs : Bytes) : Option (Nat × Bytes) :=
  (takeN n bs).map fun (h, t) => (beVal h, t)

def readLE (n : Nat) (bs : Bytes) : Option (Nat × Bytes) :=
  (takeN n bs).map fun (h, t) => (leVal h, t)

theorem readBE_be (n v : Nat) (h : v < 256 ^ n) (rest : Bytes) :
    readBE n (be n v ++ rest) = some (v, rest) := by
  simp [readBE, takeN_append' (be_length n v) rest, beVal_be n v h]

theorem readBE_be_nil (n v : Nat) (h : v < 256 ^ n) : readBE n (be n v) = some (v, []) := by
  simpa using readBE_be n v h []

theorem readLE_le (n v : Nat) (h : v < 256 ^ n) (rest : Bytes) :
    readLE n (le n v ++ rest) = some (v, rest) := by
  simp [readLE, takeN_append' (le_length n v) rest, leVal_le n v h]

/-- `k` items in a row, each read by `p`. -/
def readN {α : Type} (p : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
    let (x, bs) ← p bs
    let (xs, bs) ← readN p k bs
    pure (x :: xs, bs)

theorem readN_enc {α : Type} (p : Bytes → Option (α × Bytes)) (enc : α → Bytes) (xs : List α)
    (h : ∀ x ∈ xs, ∀ r, p (enc x ++ r) = some (x, r)) (rest : Bytes) :
    readN p xs.length (xs.flatMap enc ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => simp [readN]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp [readN, List.flatMap_cons, List.append_assoc, hx, ih']

/-! ## `WIR-18`: the five moves -/

/-- "the bytes, no prefix — 32-byte ids, 33-byte compressed points". -/
@[req "WIR-18"] def fixed (b : Bytes) : Bytes := b
/-- "one byte". -/
@[req "WIR-18"] def u8 (v : Nat) : Bytes := [v]
@[req "WIR-18"] def u16 (v : Nat) : Bytes := le 2 v
@[req "WIR-18"] def u32 (v : Nat) : Bytes := le 4 v
@[req "WIR-18"] def u64 (v : Nat) : Bytes := le 8 v
/-- "`u32` little-endian length prefix, then the bytes". -/
@[req "WIR-18"] def var (b : Bytes) : Bytes := le 4 b.length ++ b
/-- "`u32` little-endian count, then each item as `var`". -/
@[req "WIR-18"] def list (items : List Bytes) : Bytes := le 4 items.length ++ items.flatMap var

def readVar (bs : Bytes) : Option (Bytes × Bytes) := do
  let (n, bs) ← readLE 4 bs
  takeN n bs

def readList (bs : Bytes) : Option (List Bytes × Bytes) := do
  let (k, bs) ← readLE 4 bs
  readN readVar k bs

/-- "Every variable-length field is length-prefixed, so no concatenation ambiguity exists": a
`var` reads back exactly, whatever follows it. -/
@[req "WIR-18"]
theorem readVar_var (b : Bytes) (h : b.length < 256 ^ 4) (rest : Bytes) :
    readVar (var b ++ rest) = some (b, rest) := by
  simp [readVar, var, List.append_assoc, readLE_le 4 b.length h, takeN_append]

@[req "WIR-18"]
theorem readList_list (items : List Bytes) (hk : items.length < 256 ^ 4)
    (h : ∀ b ∈ items, b.length < 256 ^ 4) (rest : Bytes) :
    readList (list items ++ rest) = some (items, rest) := by
  simp [readList, list, List.append_assoc, readLE_le 4 items.length hk,
    readN_enc readVar var items (fun b hb r => readVar_var b (h b hb) r)]

@[req "WIR-18"]
theorem var_length (b : Bytes) : (var b).length = 4 + b.length := by simp [var, le_length]

/-! ## `CHN-25`: the commitment -/

/-- One input, as `CHN-24` binds it: "every input's txid, vout and `nSequence` in transaction
order". `txid` is the 32 bytes in INTERNAL order, what the encoding writes raw. -/
structure Input where
  txid : Bytes
  vout : Nat
  sequence : Nat
  deriving DecidableEq, Repr

/-- One output: "every output's scriptPubKey and amount in transaction order". -/
structure Output where
  script : Bytes
  amount : Nat
  deriving DecidableEq, Repr

/-- The fields `CHN-24` binds, and nothing else: no signature, no nonce, no request field but
the expiry. `version` is the 32-bit pattern `CHN-25` writes ("i32 two's complement"): a
negative `nVersion` is its two's complement here. -/
structure Commitment where
  walletId : Bytes
  version : Nat
  lockTime : Nat
  inputs : List Input
  outputs : List Output
  fee : Nat
  expiry : Nat
  policyVersion : Nat
  deriving DecidableEq, Repr

/-- The admitted domain: every fixed field its width, every integer in its range. -/
abbrev Input.WF (i : Input) : Prop := i.txid.length = 32 ∧ i.vout < 256 ^ 4 ∧ i.sequence < 256 ^ 4
abbrev Output.WF (o : Output) : Prop := o.script.length < 256 ^ 4 ∧ o.amount < 256 ^ 8
abbrev Commitment.WF (c : Commitment) : Prop :=
  c.walletId.length = 32 ∧ c.version < 256 ^ 4 ∧ c.lockTime < 256 ^ 4 ∧
  c.inputs.length < 256 ^ 4 ∧ (∀ i ∈ c.inputs, i.WF) ∧
  c.outputs.length < 256 ^ 4 ∧ (∀ o ∈ c.outputs, o.WF) ∧
  c.fee < 256 ^ 8 ∧ c.expiry < 256 ^ 8 ∧ c.policyVersion < 256 ^ 4

@[req "CHN-25"]
def encInput (i : Input) : Bytes := i.txid ++ be 4 i.vout ++ be 4 i.sequence

@[req "CHN-25"]
def encOutput (o : Output) : Bytes := be 4 o.script.length ++ o.script ++ be 8 o.amount

/-- `CHN-25`'s layout, field by field, every integer big-endian. -/
@[req "CHN-25"]
def encode (c : Commitment) : Bytes :=
  c.walletId ++ be 4 c.version ++ be 4 c.lockTime ++
  be 4 c.inputs.length ++ c.inputs.flatMap encInput ++
  be 4 c.outputs.length ++ c.outputs.flatMap encOutput ++
  be 8 c.fee ++ be 8 c.expiry ++ be 4 c.policyVersion

def decInput (bs : Bytes) : Option (Input × Bytes) := do
  let (txid, bs) ← takeN 32 bs
  let (vout, bs) ← readBE 4 bs
  let (sequence, bs) ← readBE 4 bs
  pure ({ txid, vout, sequence }, bs)

def decOutput (bs : Bytes) : Option (Output × Bytes) := do
  let (n, bs) ← readBE 4 bs
  let (script, bs) ← takeN n bs
  let (amount, bs) ← readBE 8 bs
  pure ({ script, amount }, bs)

/-- The decoder: consumes the whole string or refuses. -/
@[req "CHN-25"]
def decode (bs : Bytes) : Option Commitment := do
  let (walletId, bs) ← takeN 32 bs
  let (version, bs) ← readBE 4 bs
  let (lockTime, bs) ← readBE 4 bs
  let (ni, bs) ← readBE 4 bs
  let (inputs, bs) ← readN decInput ni bs
  let (no, bs) ← readBE 4 bs
  let (outputs, bs) ← readN decOutput no bs
  let (fee, bs) ← readBE 8 bs
  let (expiry, bs) ← readBE 8 bs
  let (policyVersion, bs) ← readBE 4 bs
  match bs with
  | [] => pure { walletId, version, lockTime, inputs, outputs, fee, expiry, policyVersion }
  | _ => none

theorem decInput_enc (i : Input) (h : i.WF) (rest : Bytes) :
    decInput (encInput i ++ rest) = some (i, rest) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [decInput, encInput, List.append_assoc, takeN_append' h1, readBE_be 4 _ h2, readBE_be 4 _ h3]

theorem decOutput_enc (o : Output) (h : o.WF) (rest : Bytes) :
    decOutput (encOutput o ++ rest) = some (o, rest) := by
  obtain ⟨h1, h2⟩ := h
  simp [decOutput, encOutput, List.append_assoc, readBE_be 4 _ h1, takeN_append, readBE_be 8 _ h2]

/-- On the admitted domain the encoding reads back exactly. -/
@[req "CHN-25"]
theorem decode_encode (c : Commitment) (h : c.WF) : decode (encode c) = some c := by
  obtain ⟨hw, hv, hl, hni, hi, hno, ho, hf, he, hp⟩ := h
  simp [decode, encode, List.append_assoc, takeN_append' hw, readBE_be 4 _ hv, readBE_be 4 _ hl,
    readBE_be 4 _ hni, readN_enc decInput encInput c.inputs (fun i hi' r => decInput_enc i (hi i hi') r),
    readBE_be 4 _ hno, readN_enc decOutput encOutput c.outputs (fun o ho' r => decOutput_enc o (ho o ho') r),
    readBE_be 8 _ hf, readBE_be 8 _ he, readBE_be_nil 4 _ hp]

/-- `CHN-24`: "Two distinct transactions MUST never share a commitment" — the half the encoding
carries: two well-formed commitments with one encoding are one commitment. The other half, that
two encodings have two `commitment_id`s, is `CHN-26`'s hash and a collision assumption named
there, not a theorem here. -/
@[req "CHN-24"]
theorem encode_injective (a b : Commitment) (ha : a.WF) (hb : b.WF) (h : encode a = encode b) :
    a = b := by
  have := decode_encode a ha
  rw [h, decode_encode b hb] at this
  exact (Option.some.inj this).symm

theorem flatMap_length_const {α : Type} (f : α → Bytes) (k : Nat) (xs : List α)
    (h : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = k * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      h x (by simp), ih (fun y hy => h y (by simp [hy])), Nat.mul_succ]
    omega

/-- The published widths add up: 68 fixed bytes, 40 per input, 12 plus the script per output. -/
@[req "CHN-25"]
theorem encode_length (c : Commitment) (h : c.WF) :
    (encode c).length =
      68 + 40 * c.inputs.length + (c.outputs.map fun o => 12 + o.script.length).sum := by
  obtain ⟨hw, -, -, -, hi, -, -, -, -, -⟩ := h
  have hin : (c.inputs.flatMap encInput).length = 40 * c.inputs.length :=
    flatMap_length_const encInput 40 c.inputs fun i hi' => by
      simp [encInput, be_length, (hi i hi').1]
  have hout : ∀ os : List Output,
      (os.flatMap encOutput).length = (os.map fun o => 12 + o.script.length).sum := by
    intro os
    induction os with
    | nil => simp
    | cons o os ih => simp [List.flatMap_cons, encOutput, be_length, ih]; omega
  simp [encode, be_length, hw, hin, hout]
  omega

/-- What the commitment does NOT bind (`CHN-24`'s list is exhaustive; the review of `F32` asked
for it stated): a request carries signatures and a nonce beside its commitment, and none of them
reaches the encoding. Two requests with one commitment have one encoding, whatever their
signatures. -/
structure Request where
  commitment : Commitment
  nonce : Bytes
  coordSig : Bytes
  partials : List Bytes

@[req "CHN-24"]
theorem encode_ignores_signatures (r r' : Request) (h : r.commitment = r'.commitment) :
    encode r.commitment = encode r'.commitment := by rw [h]

/-! ## The published vector (`tools/protocol-vectors.json`, `commitment`) -/

/-- The vector's fields. The JSON txid is in display order; `Input.txid` is internal order, so
it is reversed here, as `CHN-25` says ("INTERNAL byte order (not display order)"). -/
def vector : Commitment :=
  { walletId := [0x6c, 0x67, 0x56, 0x67, 0xd4, 0x8f, 0x3d, 0x90, 0x25, 0x46, 0x3d, 0x26, 0xb0, 0x8c,
                 0xc5, 0x34, 0xbc, 0x53, 0x6b, 0xf3, 0xd6, 0x43, 0x1f, 0x95, 0x14, 0xbd, 0xb3, 0x6a,
                 0xfc, 0xad, 0x75, 0x7e],
    version := 2, lockTime := 0,
    inputs := [{ txid := [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
                          0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
                          0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f].reverse,
                 vout := 1, sequence := 4294967295 }],
    outputs := [{ script := [0x00, 0x14, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
                             0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11],
                  amount := 99000 }],
    fee := 1000, expiry := 1752500000, policyVersion := 1 }

/-- The published preimage, 142 bytes. -/
def vectorPreimage : Bytes :=
  [ 0x6c, 0x67, 0x56, 0x67, 0xd4, 0x8f, 0x3d, 0x90, 0x25, 0x46, 0x3d, 0x26, 0xb0, 0x8c, 0xc5, 0x34, 0xbc, 0x53, 0x6b, 0xf3, 0xd6, 0x43, 0x1f, 0x95, 0x14, 0xbd, 0xb3, 0x6a, 0xfc, 0xad, 0x75, 0x7e,
    0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x1f, 0x1e, 0x1d, 0x1c, 0x1b, 0x1a, 0x19, 0x18, 0x17, 0x16, 0x15, 0x14, 0x13, 0x12, 0x11, 0x10, 0x0f, 0x0e, 0x0d, 0x0c,
    0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14, 0x11, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x82, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x03, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x68, 0x75, 0x07, 0x20, 0x00, 0x00, 0x00, 0x01 ]

set_option maxRecDepth 10000 in
/-- The fields encode to the published bytes, and the bytes decode to the fields. -/
@[req "CHN-25"]
theorem vector_reproduces : encode vector = vectorPreimage ∧ decode vectorPreimage = some vector := by
  decide +kernel

set_option maxRecDepth 10000 in
@[req "CHN-25"]
theorem vector_length : vectorPreimage.length = 142 ∧ vector.WF := by decide +kernel

end BtcPolicy.Encode
