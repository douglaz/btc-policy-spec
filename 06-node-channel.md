# 06 — The node channel

The authenticated node-to-node transport over which nodes relay coordinator requests, exchange
partial signatures, and count holder receipts. It carries signatures and assembly only — never
policy, never a verdict, never a claim any node acts on without re-deriving it. The Carrier —
the exact request body a node processes and relays — and the clock rules that govern its
residency are specified here because they are properties of the channel's receipt path.

## Purpose and boundary

**NCH-1** Every node MUST expose one channel endpoint to its peers and MUST accept on it exactly
the two message types of `NCH-20`. The channel carries: verbatim relays of coordinator-signed
requests, per-input partial signatures for a named candidate, and — implicitly, by a relay's
arrival — holder receipts. It MUST NOT carry policy decisions, shared counters, verdict caches,
or any gossip; each node still evaluates every request against its own policy and its own
chain view.

**NCH-2** Transport is HTTP POST to `http://<endpoint>/channel` at each peer's manifest-pinned
endpoints (`MAN-4`). A sending node MUST disable ambient proxies and MUST refuse to follow any
redirect: a 3xx is a misbehaving peer, never a hop, because a redirect could exfiltrate a
partial. The response read MUST be bounded by `max_response_bytes` (default 65 536). At
rollout stage 1 every endpoint is `127.0.0.1:<port>` and the ceremony refuses anything else;
from stage 2 the transport is routable and authenticated (`OPS-51`), and which mechanism —
onion addresses derived from node key material, or mTLS — is `F37`.

**NCH-3** **The signing-oracle prohibition.** A peer assertion or partial MUST NEVER authorize
a new signature. A relayed coordinator-authenticated request may enter the shared ingress
pipeline (`SPN-2`); a node signs only after it has itself received and accepted the full
user-authorized request. A peer's "I validated", "I froze", "broadcast now", or a partial signature carries no
authority; a partial is stored only after this node verifies it against its own recomputed
sighash. There is no legitimate nonce-exchange phase in this protocol.

## Identity

**NCH-4** Each node's **channel key** MUST be derived at startup from its federation signing key
and never persisted: the scalar is the tagged hash `btc-policy/channel-key/v0` over the 32-byte
signing secret, interpreted big-endian; if that is zero or not below the curve order the node
appends a one-byte counter starting at 0 to the message and retries. Its public half is the
compressed encoding. Like the signing key it dies with the process.

**NCH-5** A peer's channel public key is trusted because the manifest carries it with an
**endorsement** — a signature by that peer's Bitcoin signing key over `MAN-6`'s domain-separated
bytes — which every node verifies for every member at startup (`MAN-11`). The wire carries no
endorsement and no challenge-response handshake: possession of the channel key is proven per
message by the envelope signature.

**NCH-6** A node's channel key MUST differ from the coordinator auth key, compared as curve
points so that an uncompressed spelling cannot hide reuse (`MAN-10`).

## Sending

**NCH-7** To deliver one message a node MUST try the peer's endpoints in manifest order for one
logical attempt, building a **fresh envelope — fresh nonce, fresh timestamp, fresh signature —
for every endpoint attempt**, because reusing one would self-reject as a replay at an alternate
endpoint. Before each endpoint it re-reads the clock and stops if past the message deadline; each
send's timeout is `min(per_send_deadline_secs, remaining + 1)`.

**NCH-8** Retry MUST follow this schedule: an `ACCEPTED` reply ends the message; a `REJECTED`
reply ends it immediately with no retry (a rejection is permanent); a `RATE_LIMITED` reply waits
the advertised `retry_after_secs` without advancing the backoff; an `UNKNOWN_CANDIDATE` reply or
a transport error waits the next backoff step and advances it. The backoff steps are `1, 2, 5,
10, 30` seconds, the last repeating; every wait is at least one second and at most the time
left before the deadline plus one. The wall clock is re-read after every attempt and a message
past its deadline is given up. The schedule is a constant, not a ceremony knob.

**NCH-9** Fan-out MUST use one sending task per peer, with messages to one peer sent in order
so that a base rung wins the recipient's quota before its bumps.

## Size and freshness

**NCH-10** The envelope body is bounded by `max_msg_bytes`, a federation-uniform manifest-sealed
value (default 1 048 576). A larger body MUST be refused as a tagged `REJECTED` /
`OVERSIZED_BODY` — an HTTP 400 with the channel's own body, deliberately not a 413 — and a
sending node MUST preflight the worst case (all-zero identity fields, maximum node ids, maximum
timestamp, 144-character signature) before acknowledging any request it could not relay
(`SPN-8`).

**NCH-11** The **envelope** is a JSON object with exactly these members, all required:

| member | JSON | encoding | preimage form |
|---|---|---|---|
| `msg_type` | string | `"partial"` or `"request"` | `var` |
| `protocol_version` | number | `4` | `u32` |
| `wallet_id` | string | 64 lowercase hex | 32 raw bytes |
| `manifest_hash` | string | 64 lowercase hex | 32 raw bytes |
| `sender_node_id` | number | u16 | `u16` |
| `recipient_node_id` | number | u16 | `u16` |
| `payload_b64` | string | standard padded base64 | `var` over the base64 ASCII, un-decoded |
| `nonce` | string | 32 lowercase hex, 16 random bytes | `var(hex_decode(nonce))` — the 16 RAW bytes, not the 32 hex characters |
| `timestamp` | number | unix seconds | `u64` |
| `channel_sig` | string | lowercase hex DER ECDSA | not in the preimage |

The signature is ECDSA by the sender's channel key over the tagged hash
`btc-policy/channel-envelope/v0` of the fields in table order with `WIR-18`'s encoder;
`WIR-29` publishes the vector. The nonce is 16 bytes from the operating system's random source,
fresh per transport attempt.

**NCH-12** An envelope is **fresh** iff `timestamp ∈ [now − 300, now + 60]`, where `now` is the
receiver's freshness high-water (`NCH-13`). The window is a constant, never configuration.

**NCH-13** The receiver's ingress guard MUST run as one critical section in this order:

1. `high_water ← max(high_water, raw_now)`; `now ← high_water` (the freshness high-water is
   forward-only and never lowered);
2. freshness against `now`; on failure charge the quota, then answer `RATE_LIMITED` if the quota
   is exhausted, else stale;
3. prune seen nonces whose recorded timestamp is below `now − 300` — keyed by the envelope's own
   timestamp, so a future-stamped nonce lives until `now` catches up;
4. replay: `(sender_node_id, nonce)` already seen ⇒ charge the quota, then `REPLAYED_NONCE`;
5. charge the quota BEFORE inserting the nonce, so a rate-limited flood cannot grow the cache;
6. insert `(sender, nonce) → timestamp`.

A quota-refused or stale envelope consumes no nonce. *A high-water latched forward by a clock
excursion is `F3`.*

**NCH-14** A `request` envelope that fails freshness MUST NOT be rejected outright. After
authentication and quota charging it MAY be bounded-decoded solely to recognise an exact
resident Spend Carrier; only that case continues into `NCH-36`'s receipt-only path, and every
other stale outcome — any other message type, a Refresh or a Clawback, malformed or unknown content — answers
`STALE_TIMESTAMP`. Every stale outcome calls the same freshness diagnostic and consumes no
nonce.

**NCH-15** Each peer has a rolling quota of `per_peer_quota_per_min` (default 600) envelopes per
60-second window, keyed by the **authenticated** sender and charged on every authenticated
envelope including stale and replayed ones — forged traffic cannot charge a peer because the
guard runs after signature verification. Over quota answers `RATE_LIMITED` with
`retry_after_secs = max(oldest_charge + 60 − now, 1)`. The quota is per node, not sealed, and
has no fairness: enough simultaneous Carriers can consume freed entries until their bounds end,
and no one-window delivery bound is claimed.

**NCH-16** Every stale envelope MUST increment a monotonic per-peer reject count and publish a
`CHANNEL_FRESHNESS_REJECT` event (`API-18`) carrying `peer_node_id`, `reject_count` and
`skew_secs = timestamp − now`. Publication is keyed on the ingress high-water: a lower
concurrent observation is dropped; an equal high-water updates the retained entry in place at
its existing sequence and never resurrects a cap-evicted one; only a strictly higher high-water
appends. A latched-high-water outage therefore publishes at most once per peer, and unrelated
on-chain watchtower evidence is never displaced by diagnostics. The event is published after
the guard lock is released.

## Replies

**NCH-17** The reply is one of four fixed `(status, body)` pairs, and a client MUST classify on
both:

| reply | HTTP | body |
|---|---|---|
| accepted | 200 | `{"status":"ACCEPTED"}` |
| rejected | 400 | `{"status":"REJECTED","reason":"<CODE>"}` |
| unknown candidate | 409 | `{"status":"UNKNOWN_CANDIDATE"}` |
| rate limited | 429 | `{"status":"RATE_LIMITED","retry_after_secs":<n>}` |

Any other pairing is a transport anomaly and is retried as one. A missing `retry_after_secs`
reads as 1.

A client MUST classify a reply on its HTTP status and its **decoded** `status` member, never by
comparing the response bytes: insignificant JSON whitespace and object-member order are not
normative anywhere in this set, so a reply from a compact serialiser and one from a spaced
serialiser are the same reply. `WIR-11` publishes these four bodies as decoded JSON values for
that reason. A byte-comparing client would read every reply from an implementation that spaces
its JSON differently as a transport anomaly and retry it until the message deadline (`NCH-8`),
which silently ends partial-signature delivery between two conforming implementations.

**NCH-18** The rejection reasons, their wire strings, and what produces each:

| reason | produced by |
|---|---|
| `MALFORMED_JSON` | envelope not JSON; `wallet_id`/`manifest_hash` not 32-byte hex; `nonce` not 16-byte hex; `channel_sig` not hex |
| `OVERSIZED_BODY` | body larger than `max_msg_bytes` |
| `BAD_PROTOCOL_VERSION` | `protocol_version ≠ 4` |
| `WRONG_WALLET` | `wallet_id` is not this vault's |
| `WRONG_MANIFEST` | `manifest_hash` is not this vault's |
| `WRONG_RECIPIENT` | `recipient_node_id` is not this node |
| `UNKNOWN_SENDER` | sender is this node, or not a member |
| `BAD_CHANNEL_SIG` | signature not DER, or does not verify against the sender's channel key |
| `STALE_TIMESTAMP` | outside the freshness window and not the `NCH-14` exception |
| `REPLAYED_NONCE` | `(sender, nonce)` already seen |
| `MALFORMED_PAYLOAD` | base64 fails; a `request` that is not a tagged request; a partial whose fields do not parse |
| `UNKNOWN_MSG_TYPE` | `msg_type` is neither `partial` nor `request` |
| `PAYLOAD_WALLET_MISMATCH` | a partial's `wallet_id` differs from the envelope's |
| `SIGNER_MISMATCH` | a partial's `signer_node_id` differs from the sender, or is not a member |
| `WRONG_SIGHASH_TYPE` | a partial's `sighash_type ≠ 1` |
| `WRONG_TXID` | a partial's `txid` matches no rung of the named candidate |
| `WRONG_USER_SIG_HASH` | a partial's `user_sig_hash` differs from the variant's |
| `WRONG_INPUT` | a partial's `input` is out of range |
| `BAD_PARTIAL_SIG` | not DER, or does not verify against the recomputed sighash and the signer's key |

After the pre-authentication concurrency, read and size bounds (`NCH-19`, `NCH-10`), envelope
validation MUST run in this order: structural decoding (`MALFORMED_JSON`), protocol version,
wallet, manifest, recipient, sender membership, channel signature. Each failure uses its table
reason. Only an authenticated envelope enters the freshness, replay and quota guard (`NCH-13`,
with the receipt exception in `NCH-14`). Dispatch is owned by `NCH-20`; partial validation order,
including the `UNKNOWN_CANDIDATE` branches, by `NCH-24`.

**NCH-19** Before authentication the receiver MUST bound concurrency at
`max_concurrent_channel_requests` (default 64), answering `RATE_LIMITED{1}` when saturated with
the permit moved into the processing job so a disconnecting sender cannot release it early, and
MUST bound the body read at 5 seconds, answering `RATE_LIMITED{1}` on timeout. A node that is
locked down with a poisoned critical lock answers HTTP 500 before parsing (`API-23`).

## Message types

**NCH-20** There are exactly two message types, `request` and `partial`. Dispatch happens
AFTER the quota is charged and the nonce consumed.

**NCH-21** A `request` payload is the padded JSON of the tagged request (`API-9`). The relaying
node MUST pad every request to one fixed length so that PIN length is not observable: serialise
the request with `pin`, `nonce` and `coord_sig` cleared to obtain the shape length, add a fixed
budget — `6 × (64 + 64) + 144` bytes for a Spend, `6 × 64 + 144` for a Refresh and for a
Clawback, which has a Refresh's shape (`API-24`) — and pad the
real serialisation with trailing ASCII spaces to that target. The payload buffer MUST be
allocated at its final size before the PIN is copied into it, so a secret-bearing buffer never
reallocates.

**NCH-22** The serialised envelope MUST likewise be padded with trailing spaces to
`len + (144 − channel_sig length)`, hiding the DER signature's variable length.

**NCH-23** A `partial` payload is a JSON object:

| member | type | meaning |
|---|---|---|
| `commitment_id` | string | the candidate (`CHN-26`) |
| `wallet_id` | string, 64 hex | must equal the envelope's |
| `txid` | string, display-order txid | selects the rung within the candidate |
| `input` | u32 | input index |
| `signer_node_id` | u16 | must equal the envelope's sender |
| `sighash_type` | u32 | must be 1 |
| `spend_purpose` | string | `"spend"` or `"escape"`; a hint the receiver ignores |
| `user_sig_hash` | string, 64 hex | `CHN-29` |
| `partial_sig` | string | lowercase hex DER ECDSA |

The sender is a node whose candidate fired; it sends one message per released rung per signed
input to every peer, with deadline = the candidate's window deadline.

**NCH-24** On a `partial` the receiver MUST, in order: check wallet equality, signer equals
sender, sighash type; then under the store lock: the candidate exists, else `UNKNOWN_CANDIDATE`;
it is not expired (`expiry < now`, except the delayed-slot exemption of `SPN-41`), else evict it,
refund its unexposed reservation, and answer `UNKNOWN_CANDIDATE`; the rung is found by txid; the
user-signature hash matches; the input and signer are in range; the signature verifies against
this node's own recomputed sighash for that rung and input and the signer's descriptor key
(`CHN-11`); then store it.

**NCH-25** The store holds at most one partial per `(rung, input, signer)`. A duplicate is an
idempotent `ACCEPTED` and never displaces the first. Storing inserts the signature into this
node's canonical PSBT for that rung; a node MUST NOT merge a peer's PSBT wholesale.

**NCH-26** `UNKNOWN_CANDIDATE` is retriable: the peer may not have registered the candidate yet,
or has already pruned it. It is never an error the sender treats as permanent.

**NCH-27** A `request` payload is handed to the ingress pipeline (`SPN-2`) after channel
authentication. The receiver MUST re-run every gate itself. Every decodable outcome — including
`NONCE_REPLAYED`, which is the common case for a request this node already processed — answers
`ACCEPTED`; an undecodable payload answers `MALFORMED_PAYLOAD`. The relay carries the
coordinator's bytes verbatim, PIN included, which is why its contents are pin-dependent by
construction and only its presence and length are uniform.

**NCH-28** The relay is loop-free by nonce consumption (`SPN-35`); a node MUST NOT relay a
request whose nonce it did not consume.

**NCH-29** After the ingress pipeline the channel path MUST resolve the Carrier memo for the
nonce and, on an exact match, count the sender as a holder (`DUR-5`). The receipt outcomes:

| lookup result | reply | meaning |
|---|---|---|
| exact resident Carrier | `ACCEPTED` after confirming | the sender is counted |
| vacant, or a skipped (settled) memo | `ACCEPTED` | nothing to count |
| owner in flight, or staged but not yet propagated | `RATE_LIMITED{1}` | the ruling is not done; retry shortly |
| clock-refused (`NCH-36`) | `RATE_LIMITED{30}` | actionable, but this wall sample is past `E` |
| a different valid signature on the same body | at most one memory-hard derivation per `(nonce, sender)`, then as above; KDF busy ⇒ `RATE_LIMITED{1}` | `NCH-39` |

`RATE_LIMITED{1}` for an in-flight owner MUST be answered before any memory-hard reservation and
without recording the sender: answering `ACCEPTED` there would silently lose holder evidence
(`DEF-1`).

## The Carrier

**NCH-30** The **Carrier** is the exact coordinator-authenticated Spend request body that a node
processes and relays. Its identity is the body; the coordinator signature authenticates it but
is not its identity, so several valid signatures MAY represent one Carrier. One resident Carrier
owns one coordinator nonce and one slot in the ordinary nonce log; exact retries and alternate
signatures resolve to it; a different body cannot create an overlapping generation while that
nonce's tombstone lives.

**NCH-31** The **Carrier identity** of a Spend MUST be the tagged hash
`btc-policy/vault-node/arm-carrier/v0` over a memory-hard stretch of the request's authentication
digest (`WIR-21`), which commits to the plaintext PIN; the stretch is Argon2id with the stronger
version and the element-wise maximum of the two enrolled PIN slots' parameters, a 32-byte
output, and a fresh per-boot random 32-byte salt (`MAN-22`). A Refresh's identity is the same
tag over the digest directly, with no stretch, because it carries no PIN, and a Clawback's
identity is formed the same way (`SPN-51`). A node MUST NOT retain
any fast digest, MAC, full signature or request body that would let later process-memory capture
cheaply test the plaintext PIN.

**NCH-32** A node keeps, under the store lock, an **arm intent** per Carrier (`DUR-4`) and a
**Carrier memo** per coordinator nonce holding the signature tag, expiry and deadline and one of
two outcomes: *in flight* — the owner is still ruling — or *derived* — naming the Carrier and the
senders whose alternate signatures have been resolved. A memo generation is `(signature_tag,
expiry, deadline)`; the signature tag is the tagged hash `btc-policy/vault-node/arm-signature/v0`
over the canonical DER of the verified coordinator signature, so hex-case aliases share one key.

**NCH-33** **Acceptance fixes lifetime once.** At the atomic nonce-acceptance transition for a
channel-mode Spend (`SPN-14`) the node MUST compute `D = M + (E − W)` with `M` the monotonic
HotClock sample taken before authentication, `E` the signed expiry and `W` that decision's
effective time, in checked arithmetic that fails closed. `D` lives on the nonce entry until it
lapses and is copied into the memo and the intent. Nothing later — wall-clock changes, retries,
relays, alternate signatures, Carrier retirement, unrelated accepted requests — may move `D`. A
wall clock already wrong at acceptance can make `D` too early or too late and is an accepted
residual (`SEC-45`).

**NCH-34** `E` is the signed, federation-facing **attempt-authority** bound; `D` ends
node-local logical residency and actionability. A new holder requires attempt time `< E` AND
`mono_now < D`. Physical records MAY remain at or after `D` while an owner is ruling, but confer
no holder authority.

**NCH-35** **Wall readings are attempt signals, not retirement authority.** Raw wall time, the
effective time, the fire sweep, handler re-reads, nonce pruning, and confirmation resampling MAY
refuse the current attempt but MUST NOT retire, replace or extend an active or
confirmation-pending Carrier while `mono_now < D`. At or past `D` the outcome is terminal,
opaque and non-mutating.

**NCH-36** At the memo lookup, the post-derivation lookup, and the final confirmation, an
authenticated, quota-admitted, **exact** receipt whose wall sample is at or past `E` MUST answer
the fixed `RATE_LIMITED{30}` — mutating no nonce, capacity, holder, gate, commit, arm, candidate,
eviction or lifetime state — while: the resident nonce and signed expiry match, `mono_now < D`,
the generation is active, ruling or staged, the holder decision is uncommitted, and the sender
is not already counted. One second is reserved for the short owner-in-flight and KDF-busy
states. Retries end at `E` or `D`, whichever ends actionability first. Every recovery claim
for a clock-refused exact receipt carries the premise of the outer-stale path (`NCH-37`):
recovery is possible only while the coordinator-nonce high-water is below `E`, because
the in-window path reads the same `effective_now` (`SPN-12`) and an unrelated later-expiry
entry can latch it past a live Carrier (`F4`); retries are bounded by `E` and `D`, never
unbounded.

**NCH-37** **The outer-stale receipt exception** (`NCH-14`) MUST: verify the coordinator
signature and the nonce length; check propagatability; under the sign lock refuse if locked
down; read `D` for the exact `(nonce, expiry)` and only if the nonce high-water is still below
`E`; classify the Carrier without mutation; if an unseen alternate signature must be resolved,
reserve the single node-wide memory-hard slot, claim the derivation by writing a claim tag
`btc-policy/outer-stale-claim/v0` over the signature tag into the memo, run the derivation
outside every lock, and revalidate after reacquisition. The final decision briefly serialises
sign lock then store lock so it cannot observe the acceptance-to-claim gap. Outcomes map to
`STALE_TIMESTAMP` (terminal), `RATE_LIMITED{30}` (actionable), or `RATE_LIMITED{1}`
(derivation pending). The exception never enters ordinary ingress, reads the PIN, or does
signing, candidate or outbox work.

**NCH-38** A receiver's wall-clock correction MUST NOT lower the freshness high-water. A stale
sender recovers only when elapsed real time brings its timestamps back inside the 300-second
window before `E` and `D`; a larger excursion can make the authenticated channel unavailable for
unbounded real time (`F3`). `E`, `D`, capacity, the Hot budget and Recovery bound the retained
state and the loss consequence, not the outage duration.

**NCH-39** **Alternate signatures.** Strict-DER low-S ECDSA still lets a hostile coordinator sign
one body many ways. An exact, already-verified signature tag is a KDF-free fast path. One
previously unseen valid signature MAY cause at most ONE non-blocking memory-hard derivation per
`(nonce, sender)` and resident generation — including from the outer-stale path; a busy slot
consumes no allowance and is retryable; a matching result records only the safe signature tag; a
mismatch spends the allowance; a third unfamiliar signature is terminal while the exact resolved
signature stays usable. Alternate resolution allocates no nonce or Carrier state and never
restarts `D`. Cross-nonce work is bounded by the 4 096 live memos and the one-active,
zero-queued memory-hard slot.

**NCH-40** **Retirement is atomic and closed.** The intent and the memo retire together under the
store lock ONLY on: (1) a non-staged terminal owner exit, including a panic unwind, where the
retire runs poison-tolerantly because it runs during unwinding; (2) completion of the full
pin-uniform holder decision (`DUR-5`), not an intermediate committed write; (3) `mono_now ≥ D`
once no owner is ruling, executed by any store prune driver — the fire tick, ingress, or refresh
— using HotClock time and never its caller's wall value; (4) process death. Capacity pressure,
HTTP disconnect or timeout, a staged refusal, a receipt, a replay, an alternate signature, and
every raw or effective wall value are NEVER retirement authority. There is no cross-lock
release: `D` lapses. The nonce tombstone keeps `D` and remains a capacity entry until both wall
expiry and `D` have ended; ordinary nonce pruning removes it only then. An in-flight memo whose
generation matches is removed by its owner's guard on exit; a derived memo never is, except by
retirement. Candidate expiry is independent of all of this.

**NCH-41** The clock of `NCH-33`–`NCH-40` is the **HotClock**: seconds elapsed since the channel
was built, monotonic, never wall time, process-lifetime, pinnable only under test. A suspend
makes it lag real time, which can only over-count residency — the safe direction.

**NCH-42** **The claim is guarded across unwinding.** Both alternate-signature paths — the
ordinary one and the outer-stale one of `NCH-37` — write a per-`(nonce, sender)` pending
marker BEFORE the memory-hard derivation. One exact-ownership guard MUST own that marker,
bound to the nonce, the sender, the memoized Carrier, the memo generation and the exact pending
tag; it is armed only after a successful vacant claim and disarmed once the derivation has
recorded an exact resolution or a mismatch-spent allowance. On an abnormal exit between claim
and resolution the guard removes ONLY the same still-pending value from the same generation,
poison-tolerantly. It MUST NEVER clear a newer generation, a completed holder decision or
resolution, or a deliberately spent mismatch, and MUST NOT clear merely because a terminal
result was returned: Lockdown, a missing `D`, `D` lapse, generation replacement and completed
state are monotonic terminal authority (`NCH-40`). A stranded marker would make the outer-stale
path retry until `E` or `D` and fail, and the ordinary path later answer `Accepted` without
counting the sender as a holder — the silent loss of holder evidence of `DEF-1`. The span is
unreachable for as long as nothing request-controlled can fail inside it — the KDF parameters,
salt and output shape are fixed and an allocation failure aborts rather than unwinds — and the
guard exists for the moment a fallible operation enters it.
