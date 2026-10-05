import BtcPolicy.Encode
/-! `CHN-34`'s maximum finalized vsize from serialization: the
witness script of `CHN-1`'s template and `CHN-9`'s maximum witness are CONSTRUCTED as bytes and
measured, and the published constants — the script's `34 × n + 152`, `W_N = 73 × t + 34 × n +
232`, the 71-byte DER ceiling, the vsize formula — are theorems about those lengths, not
restated numbers. `F51` and `F56` are why: a table checked against a formula agrees with a
framing error rather than catching it, and a dropped row passed unnoticed. The two library
accessors `CHN-34` warns against, `W_N − 1` and `W_N + 4`, are both refuted as values of the
serialized witness's weight; in the earlier formula form `W_N − 1` reproduces the vsize and
`W_N + 4` overstates it. -/

namespace BtcPolicy.Witness
open BtcPolicy.Encode

/-- Bitcoin's CompactSize, the tiers this set's sizes reach. -/
def compactSize (n : Nat) : Bytes :=
  if n < 253 then [n] else if n < 65536 then 0xfd :: le 2 n else 0xfe :: le 4 n

theorem compactSize_small {n : Nat} (h : n < 253) : compactSize n = [n] := by simp [compactSize, h]
theorem compactSize_mid {n : Nat} (h1 : 253 ≤ n) (h2 : n < 65536) : compactSize n = 0xfd :: le 2 n := by
  simp [compactSize, h2]; omega

/-- A script data push with the one-byte length opcode: what a 33-byte key and a 3-byte lock
need (`OP_PUSHBYTES_1` to `_75`). -/
def push (payload : Bytes) : Bytes := payload.length :: payload

theorem push_length (p : Bytes) : (push p).length = p.length + 1 := by simp [push]

/-- The length of a minimal script number below `2^31`: little-endian bytes and a padding byte
when the top bit would read as a sign. -/
def scriptNumLen (n : Nat) : Nat :=
  if n = 0 then 0 else if n < 0x80 then 1 else if n < 0x8000 then 2 else if n < 0x800000 then 3 else 4

/-- `CHN-34`: the script length is "invariant across every sealed `recovery_timelock`, since bit 22
set keeps the `older` push at three bytes (`CHN-4`)" — for every lock in `CHN-4`'s field,
`2^22 ≤ lock ≤ 0x40FFFF`, the operand is exactly three bytes. -/
@[req "CHN-4"]
theorem lock_operand_is_three_bytes (lock : Nat) (h1 : 2 ^ 22 ≤ lock) (h2 : lock ≤ 0x40FFFF) :
    scriptNumLen lock = 3 := by
  unfold scriptNumLen
  split; · omega
  split; · omega
  split; · omega
  split
  · rfl
  · omega

/-- `CHN-1`'s template as script bytes: `OP_IF <user> OP_CHECKSIGVERIFY <t> <nodes…> <n>
OP_CHECKMULTISIG OP_ELSE <lock> OP_CHECKSEQUENCEVERIFY OP_VERIFY OP_2 <rec…> OP_3
OP_CHECKMULTISIG OP_ENDIF`. The lock is its three little-endian bytes, which
`lock_operand_is_three_bytes` licenses on every admitted lock. -/
@[req "CHN-1"]
def witnessScript (user : Bytes) (t : Nat) (nodes : List Bytes) (lock : Nat) (rec : List Bytes) : Bytes :=
  [0x63] ++ push user ++ [0xad, 0x50 + t] ++ nodes.flatMap push ++ [0x50 + nodes.length, 0xae] ++
  [0x67] ++ push (le 3 lock) ++ [0xb2, 0x69, 0x52] ++ rec.flatMap push ++ [0x53, 0xae, 0x68]

/-- `CHN-34`: "the witness script is `34 × n + 152` bytes", for every `n`, from the bytes. -/
@[req "CHN-34"]
theorem witnessScript_length (user : Bytes) (t : Nat) (nodes : List Bytes) (lock : Nat) (rec : List Bytes)
    (hu : user.length = 33) (hn : ∀ k ∈ nodes, k.length = 33) (hr : rec.length = 3)
    (hrk : ∀ k ∈ rec, k.length = 33) :
    (witnessScript user t nodes lock rec).length = 34 * nodes.length + 152 := by
  have h1 := flatMap_length_const push 34 nodes fun k hk => by simp [push, hn k hk]
  have h2 := flatMap_length_const push 34 rec fun k hk => by simp [push, hrk k hk]
  simp [witnessScript, push, le_length, hu, h1, h2, hr]
  omega

/-- The secp256k1 group order `q` (`MAN-17`). -/
def order : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- `CHN-34`'s DER ceiling, constructed: `R` at 33 bytes with its padding byte (the top bit of
`q − 1` is set), `S` at 32 bytes at `WIR-6`'s low-S cap `⌊q / 2⌋`, "whose leading byte is
`0x7f`, so a 32-byte `S` never needs padding". -/
@[req "CHN-34"]
def maxDer : Bytes := [0x30, 69, 0x02, 33, 0x00] ++ be 32 (order - 1) ++ [0x02, 32] ++ be 32 (order / 2)

/-- "`2 + (2 + 33) + (2 + 32) = 71` is the DER ceiling", and the low-S leading byte is `0x7f`. -/
@[req "CHN-34"]
theorem maxDer_length : maxDer.length = 71 ∧ (be 32 (order / 2)).head? = some 0x7f ∧
    (be 32 (order - 1)).head? = some 0xff := by decide

/-- A signature stack item: the DER bytes plus one `SIGHASH_ALL` byte, 72 bytes. -/
@[req "CHN-34"]
def maxSig : Bytes := maxDer ++ [0x01]

/-- `CHN-9`: "the `CHECKMULTISIG` dummy, `t` federation signatures in descriptor order, the user
signature, the branch selector, and the witness script" — `t + 4` items, the selector "a single
`0x01` byte for the Normal (`OP_IF`) branch". -/
@[req "CHN-9"]
def maxStack (t : Nat) (script : Bytes) : List Bytes :=
  [] :: List.replicate t maxSig ++ [maxSig, [0x01], script]

/-- The serialized witness "including its witness stack-count prefix": the count, then each item
behind its CompactSize length. -/
@[req "CHN-34"]
def serializeWitness (stack : List Bytes) : Bytes :=
  compactSize stack.length ++ stack.flatMap fun item => compactSize item.length ++ item

def maxWitness (t : Nat) (script : Bytes) : Bytes := serializeWitness (maxStack t script)

/-- `CHN-34`: "`W_N = 73 × t + 34 × n + 232` weight units". -/
@[req "CHN-34"]
def W (t n : Nat) : Nat := 73 * t + 34 * n + 232

/-- `W_N` from the bytes: for every shape with `3 ≤ n ≤ 15` (`CHN-2`), the maximum witness over a
script of the template's length measures exactly `73 × t + 34 × n + 232`. The `+ 232` is the
dummy's prefix, the count byte, the user signature's 73, the selector's 2, the script's 3-byte
prefix and its 152. -/
@[req "CHN-34"]
theorem maxWitness_length (t n : Nat) (script : Bytes) (hs : script.length = 34 * n + 152)
    (hn : 3 ≤ n) (hn' : n ≤ 15) (ht : t ≤ 15) :
    (maxWitness t script).length = W t n := by
  have hsig : maxSig.length = 72 := by simp [maxSig, maxDer_length.1]
  have hcount : compactSize (t + 4) = [t + 4] := compactSize_small (by omega)
  have hscript : compactSize (34 * n + 152) = 0xfd :: le 2 (34 * n + 152) :=
    compactSize_mid (by omega) (by omega)
  simp [maxWitness, serializeWitness, maxStack, W, hcount, hscript, hsig, hs, le_length,
    compactSize_small]
  omega

/-! ## The transaction: `B`, the maximum, and the actual -/

structure Tx where
  version : Nat
  lockTime : Nat
  inputs : List Input
  outputs : List Output
  deriving DecidableEq, Repr

/-- `CHN-34`'s `B`: "the byte length of the transaction's legacy serialization — no segwit
marker, no flag, no per-input witness stack-count, with every `scriptSig` empty and its length
prefix present". -/
@[req "CHN-34"]
def legacy (tx : Tx) : Bytes :=
  le 4 tx.version ++ compactSize tx.inputs.length ++
  tx.inputs.flatMap (fun i => i.txid ++ le 4 i.vout ++ [0] ++ le 4 i.sequence) ++
  compactSize tx.outputs.length ++
  tx.outputs.flatMap (fun o => le 8 o.amount ++ compactSize o.script.length ++ o.script) ++
  le 4 tx.lockTime

/-- "`weight = 4 × B`", plus the segwit marker and flag this rule restores, plus one maximum
witness per input. -/
@[req "CHN-34"]
def maxWeight (B inputs t n : Nat) : Nat := 4 * B + 2 + inputs * W t n

/-- `CHN-34`: `maximum_finalized_vsize = ⌊(4 × B + 2 + input_count × W_N + 3) / 4⌋`. -/
@[req "CHN-34"]
def maxVsize (B inputs t n : Nat) : Nat := (maxWeight B inputs t n + 3) / 4

/-- What a finalized transaction weighs: the same base, marker and flag, and its actual
witnesses. -/
def finalizedVsize (B : Nat) (witnesses : List Nat) : Nat := (4 * B + 2 + witnesses.sum + 3) / 4

theorem sum_le_of_each_le (l : List Nat) (bound : Nat) (h : ∀ x ∈ l, x ≤ bound) :
    l.sum ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have := ih fun y hy => h y (by simp [hy])
    have hx := h x (by simp)
    simp [List.sum_cons, Nat.succ_mul]; omega

/-- The maximum is a maximum: a finalized transaction whose every witness is at most `W_N` has at
most the published vsize. -/
@[req "CHN-34"]
theorem finalized_le_max (B t n : Nat) (witnesses : List Nat) (h : ∀ w ∈ witnesses, w ≤ W t n) :
    finalizedVsize B witnesses ≤ maxVsize B witnesses.length t n := by
  unfold finalizedVsize maxVsize maxWeight
  have := sum_le_of_each_le witnesses (W t n) h
  exact Nat.div_le_div_right (by omega)

/-! ## The accessors `CHN-34` refuses by name -/

/-- The earlier revision's form, "`⌊(weight + 2 + (max_satisfaction_weight + 1) × input_count +
3) / 4⌋`", over one input. -/
@[req "CHN-34"]
def earlierForm (B msw : Nat) : Nat := (4 * B + 2 + (msw + 1) + 3) / 4

/-- "That form is arithmetically identical to the one above, but only when
`max_satisfaction_weight` means `W_N − 1`" — the current accessor. -/
@[req "CHN-34"]
theorem earlier_form_with_current_accessor (B t n : Nat) :
    earlierForm B (W t n - 1) = maxVsize B 1 t n := by
  unfold earlierForm maxVsize maxWeight W; omega

/-- With the deprecated accessor, "a value five weight units larger", the form overstates the
vsize by at least one on every transaction. -/
@[req "CHN-34"]
theorem earlier_form_with_deprecated_accessor (B t n : Nat) :
    maxVsize B 1 t n < earlierForm B (W t n + 4) := by
  unfold earlierForm maxVsize maxWeight W; omega

/-- Neither accessor's value is the serialized witness's weight, on any shape. -/
@[req "CHN-34"]
theorem accessors_are_not_the_weight (t n : Nat) (script : Bytes) (hs : script.length = 34 * n + 152)
    (hn : 3 ≤ n) (hn' : n ≤ 15) (ht : t ≤ 15) :
    (maxWitness t script).length ≠ W t n - 1 ∧ (maxWitness t script).length ≠ W t n + 4 := by
  rw [maxWitness_length t n script hs hn hn' ht]; unfold W; omega

/-! ## The published vectors (`tools/protocol-vectors.json`, `witness_weight`) -/

def jsonUser : Bytes := [0x03, 0xa0, 0x43, 0x4d, 0x9e, 0x47, 0xf3, 0xc8, 0x62, 0x35, 0x47, 0x7c, 0x7b, 0x1a, 0xe6, 0xae, 0x5d, 0x34, 0x42, 0xd4, 0x9b, 0x19, 0x43, 0xc2, 0xb7, 0x52, 0xa6, 0x8e, 0x2a, 0x47, 0xe2, 0x47, 0xc7]
def jsonNodes : List Bytes := [[0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98], [0x02, 0xc6, 0x04, 0x7f, 0x94, 0x41, 0xed, 0x7d, 0x6d, 0x30, 0x45, 0x40, 0x6e, 0x95, 0xc0, 0x7c, 0xd8, 0x5c, 0x77, 0x8e, 0x4b, 0x8c, 0xef, 0x3c, 0xa7, 0xab, 0xac, 0x09, 0xb9, 0x5c, 0x70, 0x9e, 0xe5], [0x02, 0xf9, 0x30, 0x8a, 0x01, 0x92, 0x58, 0xc3, 0x10, 0x49, 0x34, 0x4f, 0x85, 0xf8, 0x9d, 0x52, 0x29, 0xb5, 0x31, 0xc8, 0x45, 0x83, 0x6f, 0x99, 0xb0, 0x86, 0x01, 0xf1, 0x13, 0xbc, 0xe0, 0x36, 0xf9]]
def jsonRec : List Bytes := [[0x03, 0x77, 0x4a, 0xe7, 0xf8, 0x58, 0xa9, 0x41, 0x1e, 0x5e, 0xf4, 0x24, 0x6b, 0x70, 0xc6, 0x5a, 0xac, 0x56, 0x49, 0x98, 0x0b, 0xe5, 0xc1, 0x78, 0x91, 0xbb, 0xec, 0x17, 0x89, 0x5d, 0xa0, 0x08, 0xcb], [0x03, 0xd0, 0x11, 0x15, 0xd5, 0x48, 0xe7, 0x56, 0x1b, 0x15, 0xc3, 0x8f, 0x00, 0x4d, 0x73, 0x46, 0x33, 0x68, 0x7c, 0xf4, 0x41, 0x96, 0x20, 0x09, 0x5b, 0xc5, 0xb0, 0xf4, 0x70, 0x70, 0xaf, 0xe8, 0x5a], [0x03, 0xf2, 0x87, 0x73, 0xc2, 0xd9, 0x75, 0x28, 0x8b, 0xc7, 0xd1, 0xd2, 0x05, 0xc3, 0x74, 0x86, 0x51, 0xb0, 0x75, 0xfb, 0xc6, 0x61, 0x0e, 0x58, 0xcd, 0xde, 0xed, 0xdf, 0x8f, 0x19, 0x40, 0x5a, 0xa8]]

/-- The published script, 254 bytes. -/
def jsonScript : Bytes :=
  [
    0x63, 0x21, 0x03, 0xa0, 0x43, 0x4d, 0x9e, 0x47, 0xf3, 0xc8, 0x62, 0x35, 0x47, 0x7c, 0x7b, 0x1a, 0xe6, 0xae, 0x5d, 0x34, 0x42, 0xd4, 0x9b, 0x19, 0x43, 0xc2, 0xb7, 0x52, 0xa6, 0x8e, 0x2a, 0x47,
    0xe2, 0x47, 0xc7, 0xad, 0x52, 0x21, 0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59,
    0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98, 0x21, 0x02, 0xc6, 0x04, 0x7f, 0x94, 0x41, 0xed, 0x7d, 0x6d, 0x30, 0x45, 0x40, 0x6e, 0x95, 0xc0, 0x7c, 0xd8, 0x5c, 0x77, 0x8e, 0x4b, 0x8c, 0xef, 0x3c,
    0xa7, 0xab, 0xac, 0x09, 0xb9, 0x5c, 0x70, 0x9e, 0xe5, 0x21, 0x02, 0xf9, 0x30, 0x8a, 0x01, 0x92, 0x58, 0xc3, 0x10, 0x49, 0x34, 0x4f, 0x85, 0xf8, 0x9d, 0x52, 0x29, 0xb5, 0x31, 0xc8, 0x45, 0x83,
    0x6f, 0x99, 0xb0, 0x86, 0x01, 0xf1, 0x13, 0xbc, 0xe0, 0x36, 0xf9, 0x53, 0xae, 0x67, 0x03, 0xa7, 0x76, 0x40, 0xb2, 0x69, 0x52, 0x21, 0x03, 0x77, 0x4a, 0xe7, 0xf8, 0x58, 0xa9, 0x41, 0x1e, 0x5e,
    0xf4, 0x24, 0x6b, 0x70, 0xc6, 0x5a, 0xac, 0x56, 0x49, 0x98, 0x0b, 0xe5, 0xc1, 0x78, 0x91, 0xbb, 0xec, 0x17, 0x89, 0x5d, 0xa0, 0x08, 0xcb, 0x21, 0x03, 0xd0, 0x11, 0x15, 0xd5, 0x48, 0xe7, 0x56,
    0x1b, 0x15, 0xc3, 0x8f, 0x00, 0x4d, 0x73, 0x46, 0x33, 0x68, 0x7c, 0xf4, 0x41, 0x96, 0x20, 0x09, 0x5b, 0xc5, 0xb0, 0xf4, 0x70, 0x70, 0xaf, 0xe8, 0x5a, 0x21, 0x03, 0xf2, 0x87, 0x73, 0xc2, 0xd9,
    0x75, 0x28, 0x8b, 0xc7, 0xd1, 0xd2, 0x05, 0xc3, 0x74, 0x86, 0x51, 0xb0, 0x75, 0xfb, 0xc6, 0x61, 0x0e, 0x58, 0xcd, 0xde, 0xed, 0xdf, 0x8f, 0x19, 0x40, 0x5a, 0xa8, 0x53, 0xae, 0x68
  ]

set_option maxRecDepth 20000 in
/-- The template over the vector's keys is the published script byte for byte, and its maximum
witness measures the published 480 weight units over `CHN-9`'s six items. -/
@[req "CHN-34"]
theorem json_vector_reproduces :
    witnessScript jsonUser 2 jsonNodes 4224679 jsonRec = jsonScript ∧
    jsonScript.length = 254 ∧
    (maxStack 2 jsonScript).length = 6 ∧
    maxSig.length = 72 ∧
    (maxWitness 2 jsonScript).length = 480 := by
  decide +kernel

/-- `CHN-2`'s seven shapes, `n = 2t − 1`, `t = 2 … 8`: `(t, n, script bytes, W_N)`. -/
def shapeRows : List (Nat × Nat × Nat × Nat) := [(2, 3, 254, 480), (3, 5, 322, 621), (4, 7, 390, 762), (5, 9, 458, 903), (6, 11, 526, 1044), (7, 13, 594, 1185), (8, 15, 662, 1326)]

def dummyKey : Bytes := List.replicate 33 0x02

set_option maxRecDepth 20000 in
/-- Every published row is measured from a synthetic vault of that shape: the script and the
maximum witness serialized and counted, at the default lock and at both ends of `CHN-4`'s field.
The table covers exactly `CHN-2`'s thresholds (`F56`). -/
@[req "CHN-34"]
theorem shape_table_measured :
    (shapeRows.map fun r => r.1) = [2, 3, 4, 5, 6, 7, 8] ∧
    ∀ r ∈ shapeRows, r.2.1 = 2 * r.1 - 1 ∧
      ∀ lock ∈ [4224679, 2 ^ 22 + 1, 0x40FFFF],
        (witnessScript dummyKey r.1 (List.replicate r.2.1 dummyKey) lock (List.replicate 3 dummyKey)).length = r.2.2.1 ∧
        (maxWitness r.1 (witnessScript dummyKey r.1 (List.replicate r.2.1 dummyKey) lock (List.replicate 3 dummyKey))).length = r.2.2.2 ∧
        r.2.2.2 = W r.1 r.2.1 := by
  decide +kernel

/-- The worked transaction: one vault input, one P2WPKH output, version 2, sequence
`0xfffffffd`, 99 000 000 sat out. -/
def workedTx : Tx :=
  { version := 2, lockTime := 0,
    inputs := [{ txid := List.replicate 32 0, vout := 0, sequence := 0xfffffffd }],
    outputs := [{ script := 0x00 :: 0x14 :: List.replicate 20 0, amount := 99000000 }] }

def unsignedSerialization : Bytes :=
  [
    0x02, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xfd, 0xff, 0xff, 0xff, 0x01, 0xc0, 0x9e, 0xe6, 0x05, 0x00, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
  ]

set_option maxRecDepth 20000 in
/-- The legacy serialization is the published 82 bytes, and the published maximum weight and
vsize follow: `4 × 82 + 2 + 480 = 810`, `⌊813 / 4⌋ = 203`. -/
@[req "CHN-34"]
theorem worked_transaction_reproduces :
    legacy workedTx = unsignedSerialization ∧ unsignedSerialization.length = 82 ∧
    maxWeight 82 1 2 3 = 810 ∧ maxVsize 82 1 2 3 = 203 ∧
    earlierForm 82 (W 2 3 + 4) = 203 + 1 := by
  decide +kernel

end BtcPolicy.Witness
