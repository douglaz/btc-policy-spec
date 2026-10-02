# 08 — Wire contract

Everything here is normative and byte-exact. Where a shape disagrees with prose elsewhere, this
document wins and the disagreement is a defect to record. The vectors at the end are executed
by `tools/check_vectors.py` on every push: each block's digest is recomputed from its published
preimage, so an encoder in any language that reproduces these blocks interoperates with the
reference, and one that does not is a different protocol.

## JSON conventions

**WIR-1** Every nonempty HTTP body is JSON; empty routing-error responses follow `API-2`.
The profile is I-JSON with bounded numbers: a JSON body MUST be
valid UTF-8, every JSON number MUST be an integer within ±(2⁵³ − 1) with no exponent or
fraction — satoshi amounts, unix timestamps, counts, versions, node ids — and a parser that
silently rounds a large number is a money bug. Unix timestamps are integer seconds. There are
no floats anywhere on the wire.

A JSON example in this set fixes decoded member names, types and values. Its insignificant
whitespace is NOT normative, and no requirement may depend on a RESPONSE's raw bytes: a receiver
classifies on the HTTP status and the decoded members (`NCH-17`, `API-16`). Object-member order is
likewise not normative on a response; on a request it follows `API-10`, which states "Field order
on the wire is as listed; a receiver MUST accept any order" — a sender's convention that no
receiver may rely on. Explicit fixed string values stay exact. This freedom is scoped to
serialisation and takes nothing from the PIN-uniform response-byte requirements within one
implementation (`DUR-1`, `API-20`, `API-21`), which compare one node against itself. The one
place JSON bytes are load-bearing is a length the sender must predict rather than a body a
receiver must match: `NCH-10`'s envelope-bound preflight and `NCH-21`'s padding target, whose
serialisation `NCH-21` owns.

**WIR-2** Identifiers are strings of lowercase hex: `wallet_id`, `manifest_hash`,
`commitment_id`, `user_sig_hash` and `txid` are 64 characters (32 bytes); `signing_pubkey`,
`channel_pubkey` and `coordinator_auth_pubkey` are 66 characters (a 33-byte compressed point,
first byte `02` or `03`); a channel `nonce` is 32 characters (16 bytes); a coordinator `nonce`
is 1–64 BYTES of any encoding. A `txid` on the wire is in DISPLAY order (reversed from internal
byte order); inside a commitment preimage it is internal order (`CHN-25`). A coordinator nonce's
1–64-byte bound is over the UTF-8 bytes of the JSON string, which are also the bytes `WIR-21`
writes as `var(nonce)`; "any encoding" means the coordinator chooses what those bytes spell, not
that they are decoded before measuring. A channel `nonce` is the opposite: it is 32 hex
characters on the wire and its preimage carries the 16 DECODED bytes (`NCH-11`, `WIR-29`).

**WIR-3** Every JSON example in this set is a test input, not an illustration: it parses under
`WIR-1` with real-shaped values, and a `...` placeholder inside an object is prohibited. An
implementation SHOULD load these fixtures directly into its decoder tests.

**WIR-4** A node MUST ignore unknown members in a request body it decodes and MUST NOT emit
members beyond those specified; a client MUST ignore unknown members in a response. The channel
envelope is the exception: every member of `NCH-11` is required and none may be added, because
the signature covers the fields positionally and an unsigned extra member is a smuggling
channel.

**WIR-5** A PSBT on the wire is its BIP174 binary serialisation encoded as standard padded
base64, as one JSON string. A node decodes it after trimming surrounding whitespace. In every
signed preimage a PSBT is bound as its exact base64 ASCII, un-decoded, so both sides commit to
the identical string without a re-serialisation round trip.

**WIR-6** A signature on the wire — `coord_sig`, `channel_sig`, `channel_endorsement`,
`partial_sig` — is strict-DER secp256k1 ECDSA as lowercase hex, at most 144 characters. A
receiver MUST decode hex then DER and MUST refuse anything else.
All protocol ECDSA signers MUST emit low-S signatures, where `1 ≤ S ≤ floor(q / 2)` and `q`
is the secp256k1 group order. Receivers MUST reject high-S signatures, without normalizing
them into accepted signatures before verification, replay matching or signature hashing.
This acceptance profile also applies to the DER portion of PSBT user and federation signatures.
High-S uses the existing invalid-signature outcome for its boundary: `COORD_AUTH_INVALID` /
`coord_sig`, `BAD_CHANNEL_SIG`, `BAD_PARTIAL_SIG`, `USER_SIG_INVALID`, or fatal endorsement
validation failure. The distinction between verification and normalization is also documented
by the [libsecp256k1 signature API](https://github.com/bitcoin-core/secp256k1/blob/master/include/secp256k1.h).

## Request and response fixtures

**WIR-7** The tagged request body of `API-9`, all three variants. The PSBT strings below are
complete BIP174 v0 containers with an unsigned transaction and empty input/output maps.
They exercise structural decoding; they carry no user signatures or prevout evidence and therefore
are not policy-accepted requests. Nothing is elided.

```json
{"spend": {"spend": "cHNidP8BAFICAAAAAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAAAAAAD/////AQDh9QUAAAAAFgAUAgICAgICAgICAgICAgICAgICAgIAAAAAAAAA", "escape": "cHNidP8BAFICAAAAAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAAAAAAD/////AQDh9QUAAAAAFgAUAwMDAwMDAwMDAwMDAwMDAwMDAwMAAAAAAAAA", "pin": "246802", "nonce": "9f1c2b3a4d5e6f708192a3b4c5d6e7f80112233445566778899aabbccddeeff0", "expiry": 1757460000, "policy_version": 1, "coord_sig": "3045022100b7f9e3d1c2a4f6e8d0b2a4c6e8f0a2c4e6f8a0b2c4d6e8f0a2b4c6d8e0f2a4c602203c1e5f7a9b0d2e4f6a8c0e2f4b6d8a0c2e4f6a8b0d2e4f6a8c0e2f4a6b8d0e2f"}}
```

```json
{"refresh": {"refresh": "cHNidP8BAF4CAAAAAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAAAAAAD/////AQDh9QUAAAAAIgAgpPH8j3LzZDPkhIYtdI4WyzC+FZwGNYU3IacLIn5Cc1EAAAAAAAAA", "nonce": "1a2b3c4d5e6f708192a3b4c5d6e7f8091a2b3c4d5e6f708192a3b4c5d6e7f809", "expiry": 1757460000, "policy_version": 1, "coord_sig": "304402207d3e5f1a9c0b2d4e6f8a0c2e4f6b8d0a2c4e6f8a0b2d4e6f8a0c2e4f6a8b0d2e02204f6a8c0e2f4b6d8a0c2e4f6a8b0d2e4f6a8c0e2f4a6b8d0e2f4a6c8e0f2a4b6d"}}
```

```json
{"clawback": {"clawback": "cHNidP8BAFICAAAAAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAAAAAAD/////AQDh9QUAAAAAFgAUEREREREREREREREREREREREREREAAAAAAAAA", "nonce": "1a2b3c4d5e6f708192a3b4c5d6e7f8091a2b3c4d5e6f708192a3b4c5d6e7f809", "expiry": 1757460000, "policy_version": 1, "coord_sig": "304402207d3e5f1a9c0b2d4e6f8a0c2e4f6b8d0a2c4e6f8a0b2d4e6f8a0c2e4f6a8b0d2e02204f6a8c0e2f4b6d8a0c2e4f6a8b0d2e4f6a8c0e2f4b6d8a0c2e4f6a8b0d2e4f6a"}}
```

A Spend with a ladder adds `"escape_bumps": ["<base64>", "<base64>"]` between `escape` and
`pin`; an empty ladder is omitted, so a ladderless body is byte-identical to the pre-ladder
format. The claw-back body is the refresh body with its one key renamed (`API-24`); its PSBT
pays a `wpkh` script, standing for the escape descriptor's index-0 script (`CHN-35`).

**WIR-8** The two response bodies of `API-12`:

```json
{"accepted": {"commitment_id": "c6b4a2e0f8d6c4b2a0e8f6d4c2b0a8e6f4d2c0b8a6e4f2d0c8b6a4e2f0d8c6b4", "first_seen": 1757456400, "remaining_secs": 86400}}
```

```json
{"refusal": {"code": "HOT_VELOCITY_EXCEEDED", "check": "hot_budget_velocity", "detail": "hot outflow 40000000 sat would put this node's 172800-second rolling hot outflow at 120000000 sat, past the Hot budget of 100000000 sat"}}
```

**WIR-9** The generic error-body shape (`API-3`), followed by the `/events`, `/healthz` and
`/pending` bodies. Routing-error responses are owned by `API-2`; tagged channel replies by `NCH-17`.

```json
{"error": "request body is too large"}
```

```json
{"alerts": [{"kind": "UNRECOGNIZED_SPEND", "spend_txid": "7a1e5c3d9b8f6e4d2c0a1b3d5f7e9c8b6a4d2e0f1c3b5a7d9e8f6c4b2a0d1e3f", "outpoint": "925d90816847313b28865b47847603635729eef69e36b654526385a69d36aa7f:1", "script": "0020a3f1c9e7b5d3f1a9c7e5b3d1f9a7c5e3b1d9f7a5c3e1b9d7f5a3c1e9b7d5f3a1"}, {"kind": "CHANNEL_FRESHNESS_REJECT", "peer_node_id": 3, "reject_count": 12, "skew_secs": -412}], "cursor": 17}
```

```json
{"serving": true, "locked_down": true, "last_deadline_tick": 1757456400, "generation_claimed": true}
```

```json
{"pending": ["1e2f3a4b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0f1a2b3c4d5e6f7a8b9c0d1e2f", "c6b4a2e0f8d6c4b2a0e8f6d4c2b0a8e6f4d2c0b8a6e4f2d0c8b6a4e2f0d8c6b4"]}
```

**WIR-10** Independent structural fixtures for the channel envelope (`NCH-11`) and partial
payload (`NCH-23`). The envelope reuses the hash-vector fields of `WIR-29`; its `payload_b64`
decodes to the ASCII text `partial`, not the JSON object below. It is not a valid end-to-end
channel request: the decoded payload fails the partial JSON decoder. The signature is also a
shape placeholder. The separate partial object fixes its decoder's field names and types.

```json
{"msg_type": "partial", "protocol_version": 4, "wallet_id": "2222222222222222222222222222222222222222222222222222222222222222", "manifest_hash": "3333333333333333333333333333333333333333333333333333333333333333", "sender_node_id": 1, "recipient_node_id": 2, "payload_b64": "cGFydGlhbA==", "nonce": "44444444444444444444444444444444", "timestamp": 1752000000, "channel_sig": "3044022012a4b6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a20220a6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a2b4c6d8"}
```

```json
{"commitment_id": "c6b4a2e0f8d6c4b2a0e8f6d4c2b0a8e6f4d2c0b8a6e4f2d0c8b6a4e2f0d8c6b4", "wallet_id": "2222222222222222222222222222222222222222222222222222222222222222", "txid": "7a1e5c3d9b8f6e4d2c0a1b3d5f7e9c8b6a4d2e0f1c3b5a7d9e8f6c4b2a0d1e3f", "input": 0, "signer_node_id": 1, "sighash_type": 1, "spend_purpose": "spend", "user_sig_hash": "23a1d6d547854d3b3729083060a4f454fd21ab87a3b1784ffd541bd076cba457", "partial_sig": "3044022012a4b6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a20220a6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a2b4c6d8"}
```

**WIR-11** The four channel replies of `NCH-17`, as decoded JSON values. Their member names and
values are exact; their insignificant whitespace is not. `NCH-17` requires a client to classify on
the HTTP status and the decoded `status` member, never on the response bytes.

```json
{"status": "ACCEPTED"}
```

```json
{"status": "REJECTED", "reason": "STALE_TIMESTAMP"}
```

```json
{"status": "UNKNOWN_CANDIDATE"}
```

```json
{"status": "RATE_LIMITED", "retry_after_secs": 30}
```

## Ceremony artifact fixtures

**WIR-12** `manifest.json` (`MAN-5`), for the two-node membership of `WIR-27`'s vector:

```json
{"wallet_id": "2222222222222222222222222222222222222222222222222222222222222222", "vault_descriptor": "wsh(or_i(and_v(v:pk(031913e5eeec873b214dd4ee297115d67591d044e081c202f513db049810188b9c),multi(2,02531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337,031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f,03b8039cfb1e7998e2bcc12b50abffbbadffe815486af0b82c118d0f62e35863ed)),and_v(v:older(4224679),multi(2,03c6e0d5cd979a9e0fbb4220e7bcdee8e2607ee1641efc519e02ecf126530f6303,028a25b84d7e5b30f466f44063bea9f590f52cca8299cced623db5a2573748d81e,03ed2bed77edb656ac3860859b2378dd5eba700309ad9b4c6d1fca4515f8b91301))))#6rzn6n8d", "manifest_hash": "694d9b8a7bc153db0ecf099c916065788cc5b3cbeef932588079ca715131b5a4", "coordinator_auth_pubkey": "038a3ba5c99568d26602f4cf8038371da3c86057a96eb1b6a8de1b4f1be723c236", "protocol_version": 4, "t": 2, "n": 3, "recovery_timelock": 4224679, "policy_version": 1, "max_msg_bytes": 1048576, "hot_max_per_tx": 286331153, "hot_max_per_window": 572662306, "hot_window_secs": 858993459, "hot_allowlist": ["wpkh(hot)"], "escape_descriptor": "wpkh(escape)", "max_derivation_index": 5, "escape_feerate_floor": 1, "escape_coverage_pct": 95, "escape_bump_max_fee_pct": 0, "network": "bitcoin", "refresh_min_interval_secs": 2592000, "refresh_max_feerate": 100, "nodes": [{"node_id": 0, "signing_pubkey": "031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f", "channel_pubkey": "024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766", "transport_endpoints": ["127.0.0.1:9000"], "channel_endorsement": "3044022012a4b6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a20220a6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a2b4c6d8"}, {"node_id": 1, "signing_pubkey": "02531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337", "channel_pubkey": "03462779ad4aad39514614751a71085f2f10e1c7a593e4e030efb5b8721ce55b0b", "transport_endpoints": ["127.0.0.1:9001"], "channel_endorsement": "3044022012a4b6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a20220a6c8e0f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a2b4c6d8"}]}
```

**This fixture fixes field names and types; it is not a loadable manifest.** Precisely what does
and does not hold, so an implementer's decoder tests assert the right things:

- every key in `vault_descriptor` is a distinct on-curve compressed point, its Normal-branch keys
  are in `CHN-7` canonical order, and its BIP380 checksum verifies (`MAN-39`), so the string
  parses and `CHN-8` admits it;
- `wallet_id` is the placeholder `0x22 × 32` shared with `WIR-27`, **not** the SHA-256 of this
  descriptor, so `CHN-6` does not hold over this file;
- `nodes` carries the two-member membership of `WIR-27`'s encoder vector, which is why
  `manifest_hash` reproduces from these fields; it is neither `n` nor a legal federation shape
  (`CHN-2` requires `n = 2t − 1`), and its `node_id` assignment is `WIR-27`'s two-member one, not
  a position in canonical order over this descriptor's three node keys;
- `channel_endorsement` values are shape-valid DER placeholders, not signatures over `MAN-6`.

A node handed this file would be refused at `MAN-11`. The end-to-end artifact whose descriptor,
checksum, `wallet_id`, canonical node order and manifest digest all reproduce together is the
`descriptor_manifest` object of `WIR-34`, which the gate executes. `hot_allowlist` is the
allowlist minus the escape descriptor and its members are canonicalised strings (`MAN-2`).

**WIR-13** `node-public.json` (`MAN-25`) and a key bundle (`MAN-26`):

```json
{"signing_pubkey": "031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f", "channel_pubkey": "024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766", "node_key_salt": "0f1e2d3c4b5a69788796a5b4c3d2e1f0", "node_key_ops": 4, "node_key_mem_kib": 262144, "endpoints": ["127.0.0.1:9000"]}
```

```json
{"role": "escape", "descriptor": "wpkh([7c1a2b3d]tpubD9B2uSXfMA5WjnUHQ12QD8joJPQYmnZBULNcx7KD8gSDGhQiGJyvvAYLUKkMz2ZiB61EmvWfrdZntfTAyxFkFtphnf9sEAeLtLerypGCvte/*)", "master_fingerprint": "7c1a2b3d"}
```

**WIR-14** The ceremony input of `MAN-27`:

```json
{"threshold": 3, "node_bundles": ["dev0/node-public.json", "dev1/node-public.json", "dev2/node-public.json", "dev3/node-public.json", "dev4/node-public.json"], "user_bundle": "user.json", "recovery_bundles": ["rec-a.json", "rec-b.json", "rec-c.json"], "escape_bundle": "escape.json", "hot_descriptor": "wpkh([1a2b3c4d]tpubD8THQQqNN2prHGuUY7SvJNtYhe4tpvS4ugBTMhnatHWJxod8MVTnPqnAX7xvFZdzKUkzxXLxVbNqgTj2TnmL8uiXi7DBnt8FNqtxzeYmeaR/*)", "policy": {"max_derivation_index": 1000, "hold_secs": 86400, "duress_delay_secs": 43200, "epsilon_secs": 60, "combine_slack_secs": 3600, "delivery_horizon_secs": 60, "max_commitment_age_secs": 172800, "policy_version": 1, "escape_feerate_floor": 20, "escape_coverage_pct": 95, "escape_bump_max_fee_pct": 0, "network": "signet", "hot_max_per_tx": 50000000, "hot_max_per_window": 100000000, "hot_window_secs": 172800, "max_msg_bytes": 1048576}, "pin_normal_hash": "$argon2id$v=19$m=65536,t=3,p=1$YnRjcG9saWN5LW5vcm1hbA$Z2xhc3NlcyBhcmUgbm90IGEgcGFzc3dvcmQgaGFzaCB4eHg", "pin_duress_hash": "$argon2id$v=19$m=65536,t=3,p=1$YnRjcG9saWN5LWR1cmVzcw$bm90IGEgcGFzc3dvcmQgaGFzaCBlaXRoZXIgeHh4eHh4", "chain_backend_rpc_addr": "127.0.0.1:38332", "chain_backend_auth": "dmF1bHQ6czNjcjN0"}
```

**WIR-15** A node configuration (`MAN-7`, `MAN-8`), as the ceremony emits it, top-level keys in
this order:

```toml
listen_port = 9000
node_key_salt = "0f1e2d3c4b5a69788796a5b4c3d2e1f0"
node_key_ops = 4
node_key_mem_kib = 262144
descriptor = "wsh(...)#checksum"
allowlist = ["wpkh([1a2b3c4d]tpub.../*)", "wpkh([7c1a2b3d]tpub.../*)"]
escape_descriptor = "wpkh([7c1a2b3d]tpub.../*)"
max_derivation_index = 1000
hold_secs = 86400
duress_delay_secs = 43200
epsilon_secs = 60
combine_slack_secs = 3600
delivery_horizon_secs = 60
hot_max_per_tx = 50000000
hot_max_per_window = 100000000
hot_window_secs = 172800
max_commitment_age_secs = 172800
refresh_min_interval_secs = 2592000
refresh_max_feerate = 100
policy_version = 1
protocol_version = 4
escape_feerate_floor = 20
escape_coverage_pct = 95
escape_bump_max_fee_pct = 0
network = "signet"
pin_normal_hash = "$argon2id$v=19$m=65536,t=3,p=1$...$..."
pin_duress_hash = "$argon2id$v=19$m=65536,t=3,p=1$...$..."
coordinator_auth_pubkey = "038a3ba5c99568d26602f4cf8038371da3c86057a96eb1b6a8de1b4f1be723c236"

[chain_backend]
rpc_addr = "127.0.0.1:38332"
auth = "dmF1bHQ6czNjcjN0"

[channel]
node_id = 0
expected_manifest_hash = "694d9b8a7bc153db0ecf099c916065788cc5b3cbeef932588079ca715131b5a4"
max_msg_bytes = 1048576

[[channel.nodes]]
node_id = 0
signing_pubkey = "031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f"
channel_pubkey = "024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766"
channel_endorsement = "3044..."
endpoints = ["127.0.0.1:9000"]
```

(TOML is not checked by the fixture gate; the elisions above are in TOML only.)

## Lengths and limits

**WIR-16** The wire bounds, in one place:

| quantity | bound |
|---|---|
| `/sign` body | 1 048 576 bytes |
| `/channel` body | `max_msg_bytes`, default 1 048 576, sealed |
| channel response read | `max_response_bytes`, default 65 536 |
| coordinator nonce | 1–64 bytes |
| channel nonce | exactly 16 bytes |
| PIN | at most 64 bytes; empty is refused |
| DER signature | at most 72 bytes, 144 hex |
| escape ladder | at most 3 rungs |
| node preimage | exactly 8 bytes, 16 hex |
| node key salt | exactly 16 bytes, 32 hex |
| Argon2 parameters | `m ≤ 262 144` KiB, `t ≤ 10`, `p ≤ 16`, salt ≥ 8 bytes |
| freshness window | `[now − 300, now + 60]` seconds |
| per-peer quota | 600 per 60 seconds, default |
| coordinator nonce log | 4 096 live entries |
| Hot-budget ledger | 4 096 reservations |
| candidate registry | 1 024 candidates, 64 MiB, defaults |
| alert queue | 1 024 events |

**WIR-17** Padding (`NCH-21`, `NCH-22`) fixes one length for every protocol-valid request
payload — independent of PIN length — and one length for every envelope independent of
signature length. Padding bytes are ASCII spaces after the JSON; a decoder MUST accept trailing
whitespace.

## Canonical encodings

**WIR-18** Every signed or hashed byte string except the commitment (`CHN-25`) is built with one
encoder of five moves, **little-endian** throughout:

| move | encoding |
|---|---|
| `fixed(bytes)` | the bytes, no prefix — 32-byte ids, 33-byte compressed points |
| `u8(v)` | one byte |
| `u16(v)` / `u32(v)` / `u64(v)` | little-endian, 2 / 4 / 8 bytes |
| `var(bytes)` | `u32` little-endian length prefix, then the bytes |
| `list(items)` | `u32` little-endian count, then each item as `var` |

Every variable-length field is length-prefixed, so no concatenation ambiguity exists.

**WIR-19** Every digest is the BIP340-style tagged hash
`tagged_hash(tag, msg) = SHA256(SHA256(tag) ‖ SHA256(tag) ‖ msg)`, with `tag` the ASCII tag
string without a trailing NUL. An implementation that skips the doubled tag hash is a different
protocol that happens to interoperate until it does not.

**WIR-20** The domain tags:

| domain | tag |
|---|---|
| channel key derivation | `btc-policy/channel-key/v0` |
| manifest | `btc-policy/manifest/v0` |
| channel endorsement | `btc-policy/channel-endorsement/v0` |
| channel envelope | `btc-policy/channel-envelope/v0` |
| user-signature hash | `btc-policy/user-sig-hash/v0` |
| coordinator request | `btc-policy/coord-request/v0` |
| Carrier identity | `btc-policy/vault-node/arm-carrier/v0` |
| Carrier signature tag | `btc-policy/vault-node/arm-signature/v0` |
| outer-stale claim | `btc-policy/outer-stale-claim/v0` |

The `/v0` separates domains, not revisions; the manifest schema revision is `protocol_version`
inside the manifest preimage (`MAN-3`), and retagging would invalidate every digest for no gain.

**WIR-21** The **coordinator request** preimage is the tag byte then the fields, and the digest
the coordinator signs is `tagged_hash("btc-policy/coord-request/v0", wallet_id ‖ preimage)`
with the 32-byte `wallet_id` prepended and **never transmitted** — each side supplies its own
vault's, so a signature is valid at exactly one vault (`CHN-28`):

```
Spend   : 0x01 ‖ var(spend base64) ‖ var(escape base64) ‖ u32(rung count) ‖ var(rung base64)…
          ‖ var(pin) ‖ var(nonce) ‖ u64(expiry) ‖ u32(policy_version)
Refresh : 0x02 ‖ var(refresh base64) ‖ var(nonce) ‖ u64(expiry) ‖ u32(policy_version)
Clawback: 0x03 ‖ var(clawback base64) ‖ var(nonce) ‖ u64(expiry) ‖ u32(policy_version)
```

The rung count is written even when zero. `coord_sig` is excluded from its own preimage. The
buffer holds the plaintext PIN and MUST be allocated at full size before any field is written and
zeroized after.

**WIR-22** The **manifest** preimage is `MAN-2`. The **endorsement** preimage is `MAN-6`. The
**envelope** preimage is `NCH-11`'s fields in table order. The **channel key** is `NCH-4`.

**WIR-23** The **user-signature hash** preimage is, for each input in order, `var(DER user
signature)` followed by `u8(sighash type)` — `0x01` for `SIGHASH_ALL` — concatenated; the digest
is under `btc-policy/user-sig-hash/v0` (`CHN-29`).

**WIR-24** The **commitment** is the one big-endian encoding (`CHN-25`), and its id is a plain
untagged SHA-256 (`CHN-26`). Do not apply `WIR-18`'s encoder or `WIR-19`'s hash to it.

## Vectors

**WIR-25** Every block below is executed by `tools/check_vectors.py`: `digest` MUST equal the
tagged hash of `preimage` under `tag`. An independent implementation reproduces every digest
from the field descriptions alone; if it cannot, one of the two is wrong, and the vector, not
the prose, is normative. The reference implementation pins the same values in its own tests.

**WIR-26** Vector 1 — channel key. The message is a node signing secret of all `0x11` bytes; the
digest, read as a big-endian scalar, is its channel secret.

```vector
tag = "btc-policy/channel-key/v0"
preimage =
1111111111111111111111111111111111111111111111111111111111111111
digest = 39d6dee9b0db353e509ef6daa3885eccb21dc01b4b471369b98cd6f3253f20c7
```

**WIR-27** Vector 2 — manifest. `wallet_id = 0x22 × 32`, `protocol_version = 4`, the
coordinator pubkey shown, `max_msg_bytes = 1048576`, hot budget
`(0x11111111, 0x22222222, 0x33333333)`, allowlist `["wpkh(hot)"]`, escape `"wpkh(escape)"`,
`max_derivation_index = 5`, `escape_feerate_floor = 1`, `escape_coverage_pct = 95`,
`escape_bump_max_fee_pct = 0`, `network = bitcoin`, two nodes at `127.0.0.1:9000` and
`127.0.0.1:9001`. Field boundaries are shown as line breaks; the preimage is one contiguous
byte string.

```vector
tag = "btc-policy/manifest/v0"
preimage =
2222222222222222222222222222222222222222222222222222222222222222   # wallet_id
04000000                                                            # protocol_version
038a3ba5c99568d26602f4cf8038371da3c86057a96eb1b6a8de1b4f1be723c236 # coordinator_auth_pubkey
0000100000000000                                                    # max_msg_bytes
1111111100000000 2222222200000000 3333333300000000                  # hot budget triple
01000000 09000000 77706b6828686f7429                                # hot_allowlist: 1 × "wpkh(hot)"
0c000000 77706b682865736361706529                                   # escape_descriptor
05000000                                                            # max_derivation_index
0100000000000000                                                    # escape_feerate_floor
5f                                                                  # escape_coverage_pct
00                                                                  # escape_bump_max_fee_pct
01                                                                  # network = bitcoin
01000000                                                            # policy_version
008d270000000000                                                    # refresh_min_interval_secs
6400000000000000                                                    # refresh_max_feerate
02000000                                                            # node count
0000 031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f
     024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766
     01000000 0e000000 3132372e302e302e313a39303030
0100 02531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337
     03462779ad4aad39514614751a71085f2f10e1c7a593e4e030efb5b8721ce55b0b
     01000000 0e000000 3132372e302e302e313a39303031
digest = 694d9b8a7bc153db0ecf099c916065788cc5b3cbeef932588079ca715131b5a4
```

The same membership sealed to signet (network byte `02`) and to regtest (`03`) — two more values
than one vector needs, deliberately: one vector cannot distinguish an encoder that writes the
sealed network from one that writes a constant.

```vector
tag = "btc-policy/manifest/v0"
preimage =
222222222222222222222222222222222222222222222222222222222222222204000000
038a3ba5c99568d26602f4cf8038371da3c86057a96eb1b6a8de1b4f1be723c236
0000100000000000111111110000000022222222000000003333333300000000
010000000900000077706b6828686f74290c00000077706b682865736361706529
0500000001000000000000005f00
02                                                                  # network = signet
01000000                                                            # policy_version
008d270000000000 6400000000000000                                   # refresh bounds
02000000
0000031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f
024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766
010000000e0000003132372e302e302e313a39303030
010002531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337
03462779ad4aad39514614751a71085f2f10e1c7a593e4e030efb5b8721ce55b0b
010000000e0000003132372e302e302e313a39303031
digest = a4afcb8d1566b3cc6421181ea773b99bdd7b0f50da7360718f3ac5840642ef9c
```

```vector
tag = "btc-policy/manifest/v0"
preimage =
222222222222222222222222222222222222222222222222222222222222222204000000
038a3ba5c99568d26602f4cf8038371da3c86057a96eb1b6a8de1b4f1be723c236
0000100000000000111111110000000022222222000000003333333300000000
010000000900000077706b6828686f74290c00000077706b682865736361706529
0500000001000000000000005f00
03                                                                  # network = regtest
01000000                                                            # policy_version
008d270000000000 6400000000000000                                   # refresh bounds
02000000
0000031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f
024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766
010000000e0000003132372e302e302e313a39303030
010002531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337
03462779ad4aad39514614751a71085f2f10e1c7a593e4e030efb5b8721ce55b0b
010000000e0000003132372e302e302e313a39303031
digest = e1a588770e90684d7b40459ff693481b46784055b02e4c799e1688755c96ab65
```

The network codes are written by hand — `1`, `2`, `3` — and are NOT a library enum's ordinal;
a dependency that inserted a new network between two existing ones would otherwise silently
renumber every sealed vault. Appending that byte is why `protocol_version` reached `2`;
appending `policy_version` and then the two refresh bounds after it is why the current
revision is `4` (`MAN-3`).

**WIR-28** Vector 3 — channel endorsement. `wallet_id = 0x22 × 32`, `manifest_hash = 0x33 ×
32`, `node_id = 1`, the channel pubkey shown, `protocol_version = 4`, one endpoint
`127.0.0.1:9001`.

```vector
tag = "btc-policy/channel-endorsement/v0"
preimage =
2222222222222222222222222222222222222222222222222222222222222222   # wallet_id
3333333333333333333333333333333333333333333333333333333333333333   # manifest_hash
0100                                                                # node_id
03462779ad4aad39514614751a71085f2f10e1c7a593e4e030efb5b8721ce55b0b # channel_pubkey
04000000                                                            # protocol_version
01000000 0e000000 3132372e302e302e313a39303031                      # endpoints
digest = a34b7ae77451a667d585788a81f6c44bd09f80210b23bae73d7bf5148759462e
```

**WIR-29** Vector 4 — channel envelope. `msg_type = "partial"`, `protocol_version = 4`,
`wallet_id = 0x22 × 32`, `manifest_hash = 0x33 × 32`, sender 1, recipient 2, payload the base64
text `cGFydGlhbA==`, nonce `0x44 × 16`, timestamp `1752000000`.

```vector
tag = "btc-policy/channel-envelope/v0"
preimage =
07000000 7061727469616c                                             # msg_type
04000000                                                            # protocol_version
2222222222222222222222222222222222222222222222222222222222222222   # wallet_id
3333333333333333333333333333333333333333333333333333333333333333   # manifest_hash
0100 0200                                                           # sender, recipient
0c000000 6347467964476c6862413d3d                                   # payload_b64 as text
10000000 44444444444444444444444444444444                           # nonce
00666d6800000000                                                    # timestamp
digest = 5b877eee8b49475aac5c2540d6ac3f292aacb831908f80ded20c9825944d35b8
```

**WIR-30** Vector 5 — user-signature hash. One input whose DER signature is the eight bytes
`30 06 02 01 01 02 01 01`, sighash type 1.

```vector
tag = "btc-policy/user-sig-hash/v0"
preimage =
08000000 3006020101020101   # var(DER)
01                          # sighash type
digest = 23a1d6d547854d3b3729083060a4f454fd21ab87a3b1784ffd541bd076cba457
```

**WIR-31** Vector 6 — coordinator request, under `wallet_id = 0x11 × 32`. The hashed message is
the wallet id followed by the request preimage of `WIR-21`. Spend: `spend = "cHNidP8BSPEND"`,
`escape = "cHNidP8BESCAPE"`, no rungs, `pin = "246802"`, `nonce = "nonce-vector"`, `expiry =
1752500000`, `policy_version = 1`. Refresh: `refresh = "cHNidP8BREFRESH"`, `nonce = "r-1"`,
same expiry and version. Clawback: `clawback = "cHNidP8BCLAWBACK"`, `nonce = "c-1"`, same
expiry and version; the tag byte is the first preimage byte, so a Refresh signature over
identical fields never verifies as a Clawback.

```vector
tag = "btc-policy/coord-request/v0"
preimage =
1111111111111111111111111111111111111111111111111111111111111111   # wallet_id, never transmitted
01                                                                  # Spend tag
0d000000 63484e69645038425350454e44                                 # spend
0e000000 63484e6964503842455343415045                               # escape
00000000                                                            # rung count
06000000 323436383032                                               # pin
0c000000 6e6f6e63652d766563746f72                                   # nonce
2007756800000000                                                    # expiry
01000000                                                            # policy_version
digest = 36ed7e2ef3a2dc1a0ad7ae76b2471d25c9be09c97e69e7c5ed82a2eca2c76cdc
```

```vector
tag = "btc-policy/coord-request/v0"
preimage =
1111111111111111111111111111111111111111111111111111111111111111   # wallet_id
02                                                                  # Refresh tag
0f000000 63484e696450384252454652455348                             # refresh
03000000 722d31                                                     # nonce
2007756800000000                                                    # expiry
01000000                                                            # policy_version
digest = 28a372480bde07d363f57bd59d3603c5a4c18ea6e69b553f19470f3402579eb9
```

```vector
tag = "btc-policy/coord-request/v0"
preimage =
1111111111111111111111111111111111111111111111111111111111111111   # wallet_id
03                                                                  # Clawback tag
10000000 63484e6964503842434c41574241434b                           # clawback
03000000 632d31                                                     # nonce
2007756800000000                                                    # expiry
01000000                                                            # policy_version
digest = 1229c1bc4498ef862a36962ff6c906049182d2ac9742cfd038b44657545cbc8b
```

**WIR-32** To verify: `python3 tools/check_vectors.py` here; in the reference repository,
`cargo test -p vault-node --lib vector_is_frozen` and
`cargo test -p vault-proto coord_request_vector_is_frozen`. A reimplementation SHOULD pin the
same blocks in its own tests, and a vector that changes is a new protocol revision.

**WIR-33** The `node_key` object in [the executable protocol vectors](tools/protocol-vectors.json)
is the complete node-key derivation vector. It publishes the raw preimage and salt, configured
costs, expected signing secret and compressed public key, and expected derived channel secret
and public key. These are public test secrets, never keys for a funded vault. Its Argon2id
invocation is `MAN-17`; the channel derivation is `NCH-4`. An independent implementation MUST
reproduce every expected output. `tools/check_vectors.py` computes them with independent
Argon2id and secp256k1 libraries pinned by `flake.nix`.

**WIR-34** The `descriptor_manifest` object in [the executable protocol vectors](tools/protocol-vectors.json)
fixes equivalent descriptor spellings, their exact canonical strings, a complete manifest
preimage and its tagged digest. Within each descriptor group, every `inputs` spelling MUST
render to `canonical` under `MAN-39`. The final group is the escape descriptor; the preceding
groups are the hot allowlist. Reordering that allowlist, adding duplicate entries or adding
the escape descriptor MUST leave the published preimage and digest unchanged. The manifest
uses real public keys, extended keys and a checksummed vault descriptor; it is a hash vector,
not an endorsed ceremony artifact. The gate reconstructs all manifest bytes from the fields
and checks the vault descriptor's checksum and `wallet_id`. Its descriptor parser deliberately
covers only the `wpkh` key-origin and multipath cases in these fixtures; it does not certify
the rest of the grammar or the Miniscript alias rules.

**WIR-35** The `commitment` object in [the executable protocol vectors](tools/protocol-vectors.json)
publishes the transaction fields, the complete big-endian preimage and its single-SHA256
commitment id. Input `txid` strings in the fields are in display order; serialization reverses
them. Every field MUST reproduce the preimage and the digest under `CHN-25` and `CHN-26`.
The asymmetric txid bytes distinguish display order from internal order, and the gate compares
the reconstructed preimage as well as its hash. Double-SHA256 is not this protocol's
commitment hash.

**WIR-36** The `witness_weight` object in [the executable protocol vectors](tools/protocol-vectors.json)
is the maximum-satisfaction-size vector for `CHN-34`. It publishes the vault descriptor, the
serialized witness script and its length, the maximum DER signature and stack-item sizes, the
witness item count, `W_N`, a worked unsigned transaction with its legacy byte length and the
maximum weight and vsize that follow, and the `W_N` of every production shape from 2-of-3 to
8-of-15, and the gate MUST refuse a table that lacks, duplicates or adds a shape, and MUST
measure each shape at both ends of `CHN-4`'s field as well as at the default lock, so that
`CHN-34`'s invariance claim is executed rather than trusted. `tools/check_vectors.py` MUST derive each published length by **serializing** the script
and a maximum-length witness from the descriptor's own keys and measuring the bytes, never by
re-evaluating `CHN-34`'s formula: a gate that restated the formula would agree with a framing
error rather than catch it. An independent implementation MUST reproduce every published length.
