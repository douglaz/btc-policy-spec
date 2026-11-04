import BtcPolicy.Encode
/-! `NCH-11`'s channel envelope preimage: the envelope's fields in table order, each in the
"preimage form" column's `WIR-18` move. The sender's channel key signs its tagged hash under
`btc-policy/channel-envelope/v0`; the tag and the hash are `check_vectors.py`'s, as for every other
preimage here, and `channel_sig` is "not in the preimage".

**What it gives.** `Envelope.preimage_length`: the preimage's length is a fixed width plus the
lengths of `msg_type` and the payload, whatever the sender and recipient ids, the nonce's sixteen
bytes and the timestamp. Both message types are equally long (`Envelope.msgType_length`), so two
envelopes' preimages have one length exactly when their payloads do. `Envelope.vector_reproduces`
rebuilds `WIR-29`'s published preimage from its fields.

**What it does not give.** The envelope on the wire is a JSON object (`NCH-11`), padded by
`NCH-22`, and its payload is base64 over JSON (`NCH-21`, `NCH-23`). Neither JSON nor base64 has an
encoder here, so no length of a body on the wire is derived, and the payload is an input. `NCH-11`
says the nonce is "16 bytes from the operating system's random source, fresh per transport
attempt", and a partial's payload carries an ECDSA `partial_sig` (`NCH-23`): one length is not one
string of bytes, and neither random draw has a model or a coupling here. -/

namespace BtcPolicy.Envelope
open BtcPolicy.Encode

/-- `NCH-11`'s members but `channel_sig`, as the preimage takes them: `payload` is the base64 text's
ASCII bytes "un-decoded", and `nonce` is the raw bytes. -/
structure Envelope where
  msgType : Bytes
  version : Nat
  walletId : Bytes
  manifestHash : Bytes
  sender : Nat
  recipient : Nat
  payload : Bytes
  nonce : Bytes
  timestamp : Nat
  deriving DecidableEq, Repr

/-- `NCH-11`'s table, row by row: `var`, `u32`, 32 raw bytes twice, `u16` twice, `var` over the
payload's text, `var` over the nonce's raw bytes, and `u64`. -/
@[req "NCH-11"]
def preimage (e : Envelope) : Bytes :=
  var e.msgType ++ u32 e.version ++ fixed e.walletId ++ fixed e.manifestHash ++ u16 e.sender ++
    u16 e.recipient ++ var e.payload ++ var e.nonce ++ u64 e.timestamp

/-- `NCH-20`'s two message types, as ASCII: `"partial"` and `"request"`. -/
def partialType : Bytes := [0x70, 0x61, 0x72, 0x74, 0x69, 0x61, 0x6c]
def requestType : Bytes := [0x72, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74]

@[req "NCH-20"]
theorem msgType_length : partialType.length = 7 ∧ requestType.length = 7 := by decide

/-- **The widths add up.** Every field but `msg_type` and the payload has a fixed width: an id is
written in its two bytes whatever its value, and so are the version and the timestamp in theirs. -/
@[req "NCH-11"]
theorem preimage_length (e : Envelope) (hw : e.walletId.length = 32)
    (hm : e.manifestHash.length = 32) (hn : e.nonce.length = 16) :
    (preimage e).length = 108 + e.msgType.length + e.payload.length := by
  simp only [preimage, var, u32, u16, u64, fixed, List.length_append, le_length, hw, hm, hn]
  omega

/-! ## The published vector (`WIR-29`) -/

/-- `WIR-29`'s fields: `msg_type = "partial"`, `protocol_version = 4`, `wallet_id = 0x22 × 32`,
`manifest_hash = 0x33 × 32`, sender 1, recipient 2, the payload text `cGFydGlhbA==`, nonce
`0x44 × 16`, timestamp `1752000000`. -/
def vector : Envelope :=
  { msgType := partialType, version := 4, walletId := List.replicate 32 0x22,
    manifestHash := List.replicate 32 0x33, sender := 1, recipient := 2,
    payload := [0x63, 0x47, 0x46, 0x79, 0x64, 0x47, 0x6c, 0x68, 0x62, 0x41, 0x3d, 0x3d],
    nonce := List.replicate 16 0x44, timestamp := 1752000000 }

/-- The published preimage, 127 bytes. -/
def vectorPreimage : Bytes :=
  [ 0x07, 0x00, 0x00, 0x00, 0x70, 0x61, 0x72, 0x74, 0x69, 0x61, 0x6c, 0x04, 0x00, 0x00, 0x00, 0x22,
    0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
    0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x33,
    0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
    0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x01,
    0x00, 0x02, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x63, 0x47, 0x46, 0x79, 0x64, 0x47, 0x6c, 0x68, 0x62,
    0x41, 0x3d, 0x3d, 0x10, 0x00, 0x00, 0x00, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
    0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x00, 0x66, 0x6d, 0x68, 0x00, 0x00, 0x00, 0x00 ]

/-- The fields frame to the published bytes, at the length `preimage_length` gives. -/
@[req "WIR-29"]
theorem vector_reproduces : preimage vector = vectorPreimage ∧ vectorPreimage.length = 127 := by
  decide +kernel

end BtcPolicy.Envelope
