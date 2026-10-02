# 07 — The node HTTP API

The five routes a vault node serves, their bodies, status codes and limits, and the closed set
of refusal codes. JSON conventions and byte encodings are `08-wire-contract.md`; the channel
protocol behind `/channel` is `06-node-channel.md`; what each gate decides is
`04-spend-lifecycle.md`.

## Transport

**API-1** A node MUST bind `127.0.0.1:<listen_port>` only, with one port for every route, no
TLS, and no authentication header on any route: authentication is the coordinator signature in
the body of `/sign` and the envelope signature in the body of `/channel`. `listen_port` is
mandatory configuration and MUST NOT be 0. This is the rollout stage-1 transport; from stage 2
the listener is reachable over the routable authenticated transport of `OPS-51` and the
coordinator ingress of `OPS-50`, which wrap these routes without changing them.

**API-2** A node MUST serve exactly these routes:

| method | path | when |
|---|---|---|
| `POST` | `/sign` | always |
| `GET` | `/events` | always |
| `GET` | `/healthz` | always |
| `GET` | `/pending` | always |
| `POST` | `/channel` | when the node has a `[channel]` configuration, which every production node has (`MAN-8`) |

An unknown path answers 404 and a wrong method on a known path answers 405, both with an empty
body. A node MUST refuse to serve at all without channel configuration and MUST claim its
process generation (`STO-4`) after binding and before accepting its first connection.

**API-3** A node MUST require no request header, MUST ignore `Content-Type`, and MUST emit
`Content-Type: application/json` on every response it produces. Every nonempty transport-error body has the one
shape `{"error": "<detail>"}` except `/channel`'s tagged bodies (`NCH-17`). Unknown members in
a request body MUST be ignored.

**API-4** `/sign` MUST refuse a body larger than 1 048 576 bytes with HTTP 413 before decoding
it, and MUST read the body through a zeroizing buffer since it carries the PIN. The handler
deadline is 10 seconds plus the largest entry of the PIN attempt budget's backoff schedule
(`MAN-23`); on expiry the node answers HTTP 408 but MUST NOT abort the job, which keeps running,
commits its verdict to the replay log and drains its outbox, so a resubmission is idempotent.

`/sign` is a **bulkhead** with a fixed concurrency of **2**, a hardcoded constant — not
configuration, not manifest-sealed, not adaptive, because an adaptive bound hands the flood
author influence over it. Admission is a non-blocking try-acquire that runs AFTER the size check
and after the body is parsed and its buffer wiped, and BEFORE the job is spawned; on saturation
the request is shed immediately with HTTP 429 and the one fixed body
`{"error":"sign capacity exhausted"}`, never queued. The decision depends on nothing but permit
availability, so the shed response is byte-identical across PIN classes even though the PIN has
by then been read; a shed request consumes no nonce, does no memory-hard work, evicts, stages
and relays nothing. The permit is moved into the detached job, not held by the handler, so it
survives the handler deadline: a request answered 408 holds its permit until its job finishes,
and a disconnecting client cannot release it early (`API-22` fixes the same ownership for
`/pending`). A refresh consumes a permit on the same counter. The bulkhead is per-surface: a
request relayed through `/channel` runs the same ingress work under `NCH-19`'s permit, so no
node-wide memory-hard bound follows from this, and it bounds nothing about the delay to
Lockdown (`DUR-15`). The value is 2 because permits above 1 buy no memory-hard throughput — a
single work lock serialises it — while the handler's own contract invites exactly one overlap:
an honest coordinator's idempotent resubmit after a 408 races its still-running predecessor.

**API-5** `/sign` MUST answer HTTP 400 with an error body for: a body that cannot be read; a
body that does not decode as the tagged request; a `spend`, `escape`, `escape_bumps` entry,
`refresh` or `clawback` that is not a decodable base64 PSBT. Everything decodable that is refused is a policy
outcome at HTTP 200 (`API-12`); a refusal is never a transport error.

**API-6** `/sign` MUST answer HTTP 400 when the request, once wrapped in a channel envelope,
would exceed the federation-uniform `max_msg_bytes` (`NCH-10`), with the detail naming the bound.
The check runs after the nonce is consumed (`SPN-8`).

**API-7** `/sign` answers HTTP 500 for an internal encoding failure or a panicked job; a panic
also forces the fail-closed Lockdown of `DUR-9` where a critical lock is poisoned.

**API-8** `/channel` is bounded by `max_msg_bytes` with the channel's own tagged 400 for
oversize, a 5-second body read under a pre-authentication concurrency permit
(`NCH-19`), and has no handler deadline of its own.

## `POST /sign`

**API-9** The body is an **externally tagged** union: an object with a single member whose KEY is
the variant name, `"spend"`, `"refresh"` or `"clawback"`, and whose value is the request object. The decoder
fixtures are in `WIR-7`, [08 — Wire contract](08-wire-contract.md).

**API-10** A `SpendRequest` has these members. Field order on the wire is as listed; a receiver
MUST accept any order.

| member | JSON type | required | meaning |
|---|---|---|---|
| `spend` | string | yes | base64 PSBT of the user-signed spend; surrounding whitespace tolerated |
| `escape` | string | yes | base64 PSBT of the user-signed mandatory Escape |
| `escape_bumps` | array of string | no; omitted when empty | base64 PSBTs of the fee ladder, ascending; at most 3 |
| `pin` | string | no; missing reads as empty and is refused | the plaintext PIN, at most 64 bytes |
| `nonce` | string | no; missing reads as empty and is refused | 1–64 bytes, any encoding; single-use per logical request |
| `expiry` | integer | no; missing reads as 0 and is refused | unix seconds |
| `policy_version` | integer | no; missing reads as 0 | bound into the signature; must equal the node's own (`API-15`) |
| `coord_sig` | string | no; missing reads as empty and is refused | lowercase hex DER ECDSA over `WIR-21` |

A body without `spend` or `escape` does not decode (HTTP 400): the Escape is mandatory by
schema, so a hostile coordinator cannot strip it.

**API-11** A `RefreshRequest` has `refresh` (required, base64 PSBT of the user-signed
self-spend), `nonce`, `expiry`, `policy_version` and `coord_sig` with the same semantics, and no
`pin`, `escape` or `escape_bumps`. A `ClawbackRequest` has the identical shape with `clawback`
(required, base64 PSBT of the user-signed sweep to the escape wallet, `CHN-35`) in place of
`refresh` (`API-24`).

**API-12** A decodable request answers HTTP 200 with one of two externally tagged bodies:

```json
{"accepted": {"commitment_id": "c6b4a2e0f8d6c4b2a0e8f6d4c2b0a8e6f4d2c0b8a6e4f2d0c8b6a4e2f0d8c6b4", "first_seen": 1757456400, "remaining_secs": 86400}}
```

```json
{"refusal": {"code": "DEST_NOT_ALLOWED", "check": "destination_allowlist", "detail": "output 0 pays non-allowlisted scriptPubKey 0014d3f1a9c7e5b3d1f9a7c5e3b1d9f7a5c3e1b9d7"}}
```

`commitment_id` is `CHN-26`; `first_seen` is the node's ingress time; `remaining_secs` is the
seconds from `first_seen` to the fire time, fixed at first acceptance and replayed verbatim,
zero for every refresh and claw-back (`SPN-34`). There is no variant carrying a
signature or a PSBT, and a body of the retired `{"signed_psbt": …}` shape MUST NOT decode.

**API-13** The refusal `code` is one of exactly these strings and no other:

| code | produced when |
|---|---|
| `WRONG_DESCRIPTOR` | never; declared for completeness |
| `UNKNOWN_INPUT` | an input is not the vault's (`POL-9`), or a mempool-spent input fails `WTC-25`'s replacement test (`SPN-43`, `SPN-50`) |
| `DEST_NOT_ALLOWED` | an output pays outside the allowlist (`POL-10`) |
| `CHANGE_NOT_DERIVABLE` | an output labelled change does not derive from the vault (`POL-10`) |
| `FEE_EXCEEDS_CAP` | fee above 10% of inputs (`POL-12`) |
| `BAD_SIGHASH` | the user signature is not `SIGHASH_ALL` (`CHN-12`) |
| `USER_SIG_INVALID` | the user signature is missing or does not verify (`CHN-12`) |
| `COMMITMENT_EXPIRED` | expiry outside the freshness window (`SPN-10`, `SPN-17`) |
| `PSBT_INCONSISTENT` | structural, class, ladder, prevout, signing or registration inconsistency |
| `BAD_PIN` | wrong PIN, or any PIN on a locked-out node (`SPN-18`) |
| `FRAUD_SUSPECTED` | Lockdown (`DUR-7`) |
| `COORD_AUTH_INVALID` | coordinator signature or nonce length (`SPN-7`, `SPN-5`) |
| `NONCE_REPLAYED` | nonce already seen (`SPN-14`) |
| `COORD_NONCE_CAPACITY` | nonce log full (`SPN-11`) |
| `CANDIDATE_CAPACITY` | candidate registry cannot admit the request's candidate group (`SPN-32`, `SPN-48`, `SPN-51`) |
| `EXPIRY_TOO_SHORT` | delivery horizon (`SPN-9`) or Hold plus slack (`SPN-30`) |
| `REFRESH_TOO_SOON` | `SPN-46` |
| `REFRESH_FEE_EXCEEDS_CAP` | `SPN-47` |
| `REFRESH_SUBORDINATED` | `SPN-45` |
| `HOT_BUDGET_EXCEEDED` | per-transaction cap (`POL-11`) |
| `HOT_VELOCITY_EXCEEDED` | rolling window or ledger capacity (`POL-16`) |

**API-14** The `check` member names the gate: `psbt_consistency`, `input_ownership`,
`destination_allowlist`, `verified_change`, `hot_budget`, `fee_cap`, `transaction_class`,
`user_signature`, `prevout_ground_truth`, `signing`,
`candidate_registration`, `candidate_identity`, `candidate_registry_capacity`,
`commitment_expiry`, `delivery_horizon`, `pin`, `pin_attempt_budget`, `lockdown`,
`coord_sig`, `policy_version`, `coord_nonce`, `coord_nonce_capacity`, `hot_budget_velocity`,
`refresh_min_interval`, `refresh_fee_cap`, `refresh_subordination`, plus `escape:` prefixed
twins of every check the Escape can reach — `escape:user_signature`,
`escape:prevout_ground_truth`, `escape:psbt_consistency`, `escape:input_ownership`,
`escape:verified_change`, `escape:destination_allowlist`, `escape:fee_cap`,
`escape:hot_budget`, `escape:transaction_class`, `escape:bump_ladder`. `detail` is free text a
client MUST NOT parse.

**API-15** The request's `policy_version` is bound into the coordinator signature so it cannot
be tampered with. A node MUST bake its OWN configured `policy_version` into the commitment
(`CHN-24`), never the request's, and one combined verifier MUST first verify the coordinator
signature and then require the request's `policy_version` to equal the node's, at all five
entries: a direct Spend, a direct Refresh and a direct Clawback answer `PSBT_INCONSISTENT` with the locally
authored check `policy_version`; a fresh relay receipt stays silent to the peer and creates no
receipt state; an outer-stale receipt stays stale and creates no state. The mismatch is judged
BEFORE the nonce log records anything and before any PIN, Carrier, claim, intent, holder,
candidate or preflight mutation, and before the coordinator request memo; envelope replay
nonces, peer high-water and quota consumption stay outside that invariant (`SPN-5` gate 4). The node's own value is manifest-sealed (`MAN-2`), so every
honest node holds the same one, the commitment ids agree, and the mismatch refusal is a
federation-uniform policy refusal under `SPN-19`; a node whose value differs from the
federation's never reaches serving (`MAN-11`).

**API-16** A coordinator delivering one request to a federation SHOULD serialise it once, offer
byte-identical bytes to each endpoint in order under a per-endpoint deadline, parse only
`commitment_id`, `first_seen`, `remaining_secs` and `code` from the reply, and stop on an
`accepted` whose `commitment_id` equals its own precomputed id or on a `NONCE_REPLAYED` that
follows a possible earlier delivery. A reply's `check` and `detail` MUST NOT be reflected into
anything the coordinator retains, since a hostile node could echo the PIN into them. The full
delivery contract — the absolute aggregate deadline, the sticky possibly-delivered state, and
what a `NotSent` outcome does and does not authorize — is `OPR-48`–`OPR-51`.

## `GET /events`

**API-17** `/events` takes one query parameter, `since=<u64>`, and answers
`{"alerts": [...], "cursor": <u64>}` at HTTP 200. The reference parser reads the query string
as an exact `since=<integer>` prefix and treats anything else — no query, an unparsable value,
another parameter first or after — as `since=0`; an implementation MUST accept at least the
exact form and MUST treat an unparsable `since` as 0.

**API-18** The queue assigns sequence numbers from 1; a response carries every retained event
with `seq > since` and `cursor = the highest sequence number the queue has ever assigned` — not
one less, and not the highest sequence still retained — so a fresh node answers
`cursor: 0` and the cursor advances even when nothing new is returned. A client that always
passes back the returned cursor never re-fetches and never misses within the queue's capacity
of 1 024 events, beyond which the oldest are dropped (`WTC-20`). Each event is one of, with no
wrapper key and discriminated by `kind`:

```json
{"kind": "RECOVERY_PATH_SPEND", "spend_txid": "7a1e5c3d9b8f6e4d2c0a1b3d5f7e9c8b6a4d2e0f1c3b5a7d9e8f6c4b2a0d1e3f", "outpoint": "925d90816847313b28865b47847603635729eef69e36b654526385a69d36aa7f:1", "script": "0020a3f1c9e7b5d3f1a9c7e5b3d1f9a7c5e3b1d9f7a5c3e1b9d7f5a3c1e9b7d5f3a1"}
```

```json
{"kind": "CHANNEL_FRESHNESS_REJECT", "peer_node_id": 3, "reject_count": 12, "skew_secs": 412}
```

`kind` is `RECOVERY_PATH_SPEND`, `UNRECOGNIZED_SPEND` or `CHANNEL_FRESHNESS_REJECT`
(`WTC-17`, `NCH-16`). `/events` carries nothing about pending or armed state, reads only the
alert queue's own lock, and never waits on the sign lock.

## `GET /healthz`

**API-19** `/healthz` answers, at HTTP 200, exactly:

```json
{"serving": true, "locked_down": false, "last_deadline_tick": 1757456400, "generation_claimed": true, "vault_wallet_serving": true}
```

`serving` is the constant `true`; `locked_down` is the Lockdown latch; `last_deadline_tick` is
`null` before the deadline driver's first pass and thereafter a unix second bucketed down to a
multiple of 10, published by the deadline driver alone and never regressing — it attests that
the deadline driver's own thread is alive and has not stopped itself on poison, and NOT that
the async runtime is scheduling, because that thread is independent of the runtime
(`STO-13`); `generation_claimed` is whether this process wrote the one-shot generation marker
(`STO-4`); `vault_wallet_serving` is whether the watch-only descriptor wallet is serving the
vault-unspent cache, `false` while the node has fallen back to the full UTXO-set scan
(`WTC-6`), fed from the fallback counter the cache refresher already keeps. The handler reads
four atomics, takes no lock, and answers while every other lock is held.

**API-20** Every `/healthz` field MUST be pin-uniform and MUST be byte-identical between an
armed pre-`T` node and an idle one. There is deliberately no arm state, candidate count, `T`,
fire deadline or per-commitment field, and no timing derived from the completion-scheduled
release pass; a stale heartbeat beside `locked_down: true` is the signal of a poison-bricked
node (`DUR-9`). Adding a field requires the `DUR-1` test: if a pre-`T` duress carrier could
change it, it does not belong here. `vault_wallet_serving` passes that test because the cache
refresher reads no PIN, duress or arm state, and the byte-identity assertion of `CNF-41` covers
it.

## `GET /pending`

**API-21** `/pending` answers, at HTTP 200, `{"pending": ["<commitment_id>", …]}` — the
**sorted** lowercase-hex commitment ids of live hot-class spends this node has accepted and not
yet seen settle. Liveness follows `SPN-42`: "The pending log MUST retain an unsettled entry while
`expiry ≥ now`, including equality, and prune it when `expiry < now`." Sorting is mandatory
because an unsorted projection leaks its container's iteration order, which differs per process
and would break the armed-versus-idle twin comparison `API-20` and `CNF-41` require. It is NOT a
claim of cross-implementation byte identity: equal pending sets MUST decode to equal arrays, but
two implementations MAY serialise them with different insignificant whitespace. Nothing in this
set depends on response bytes matching ACROSS nodes; `DUR-1`'s SILENCE compares one node's bytes
across the two PIN classes, and a per-implementation serialisation constant is PIN-independent.
Refreshes and claw-backs are never listed. Nothing else is present: no expiry, fire time, `T`, arm
state, txid, PSBT, amount, destination, fee, signature material or timestamp.

**API-22** `/pending` serves one snapshot at a time. A concurrent request is shed immediately
with HTTP 429 `{"error":"pending query already in progress"}` (never queued), the permit is held
by the detached snapshot job so a disconnecting poller cannot release it, and a poisoned sign
lock answers HTTP 500 rather than an empty list a poller could read as "nothing pending". A
locked-down node answers this route exactly like any other node. The route waits on the sign
lock, which is the one read surface that does, and `SEC-20` owns the timing channel that
creates.

## `POST /channel`

**API-23** `/channel` is the peer transport of `06-node-channel.md`. Its body is the envelope of
`NCH-11`, its replies are `NCH-17`, and its bounds are `API-8`. A node that is locked down with
a poisoned critical lock answers HTTP 500 `{"error":"channel task failed unexpectedly"}` before
parsing, as does a panicked job.

**API-24** A `ClawbackRequest` is the third `/sign` variant (`API-9`), keyed `clawback`, with
`API-11`'s shape: `clawback` (required, base64 PSBT of the user-signed sweep to the escape
wallet), `nonce`, `expiry`, `policy_version` and `coord_sig`, and no `pin`, `escape` or
`escape_bumps`. It is handled by `SPN-50`, answered by `API-12`'s two bodies, and has no
refusal codes of its own (`API-13`): `BAD_PIN`, `HOT_VELOCITY_EXCEEDED` and the three
`REFRESH_*` codes are unreachable on it, `HOT_BUDGET_EXCEEDED` is reachable only on a malformed
request carrying hot-allowlist outputs, because `POL-6`'s evaluation precedes classification
(`SPN-26`), and every other code is reachable exactly as on a spend. The decoder fixture is in
`WIR-7`.
