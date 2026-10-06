# 04 — Spend lifecycle

What a node does with a request from the moment its bytes arrive until the transaction is on
the chain: the ingress pipeline and its gate order, the coordinator nonce log, candidates and
the Hold, release and combine, refresh, and the pending projection. The duress overlay that
rides on this lifecycle is `05-duress-and-lockdown.md`; the channel that carries the messages is
`06-node-channel.md`.

## Model B

**SPN-1** The federation MUST assemble and broadcast every spend itself. A node signs its
partial at ingress, keeps it until the candidate's authorized fire event, releases it to peers
over the channel, and whichever node first holds `t` valid partials on every input combines and
broadcasts through its own chain backend. The coordinator relays and pulls; it never holds a
finalizable transaction.

**SPN-2** There MUST be exactly one ingress implementation. A request relayed by a peer over the
channel (`NCH-31`) enters the same pipeline as one delivered by the coordinator, runs the same
gates in the same order, and differs only in that the channel path additionally counts the
sender as a holder of the Carrier (`DUR-5`).

**SPN-3** Ingress MUST be **pin-independent in every observable**. On every request that passes
the pre-PIN admission gates, normal or duress, the node performs the identical operations in the
identical order — authenticate, validate both transactions, sign both partials, write a
same-shaped schedule record, stage for propagation — and answers with the same response shape.
The PIN decides only the contents of one internal selector bit. Doing the duress work
asynchronously after the response does not satisfy this: the work itself must be identical.

**SPN-4** Refusals before the nonce-consumption boundary in the ingress table (`SPN-5`)
MUST consume no nonce, perform no memory-hard work, evict nothing, and relay nothing, so that a
node at an admission ceiling behaves identically to every request regardless of what it carries.
Later refusals follow that table's nonce and propagation columns even when they read no PIN.

## The ingress pipeline

**SPN-5** A node MUST process a SpendRequest through the following gates in this order,
returning at the first failure. Three columns matter beyond the refusal: whether the gate
**consumed the nonce**, whether a failure **propagates** the request to peers, and whether it
**stages** — counts this node as a holder of the Carrier (`DUR-5`). Staging implies
propagating.

<!-- formal: BtcPolicy.Render.spn5Gates -->
| # | Gate | On failure | nonce | propagates | stages |
|---|---|---|---|---|---|
| 1 | body ≤ 1 MiB | HTTP 413 | `no` | `no` | `no` |
| 2 | JSON decodes to a tagged request | HTTP 400 | `no` | `no` | `no` |
| 3 | not locked down (before and again under the lock) | `FRAUD_SUSPECTED` / `lockdown` | `no` | `no` | `no` |
| 4 | coordinator signature verifies, then the request's `policy_version` equals the node's (`API-15`) | `COORD_AUTH_INVALID` / `coord_sig`; `PSBT_INCONSISTENT` / `policy_version` | `no` | `no` | `no` |
| 5 | nonce length 1..=64 bytes | `COORD_AUTH_INVALID` / `coord_nonce` | `no` | `no` | `no` |
| 6 | expiry inside the freshness window (`SPN-10`) | `COMMITMENT_EXPIRED` / `commitment_expiry` | `no` | `no` | `no` |
| 7 | nonce not replayed | `NONCE_REPLAYED` / `coord_nonce` | `no` | `no` | `no` |
| 8 | nonce log below capacity | `COORD_NONCE_CAPACITY` / `coord_nonce_capacity` | `no` | `no` | `no` |
| — | **nonce consumed**; `D` fixed for a channel-mode spend (`NCH-33`) | | `yes` |  |  |
| 9 | request fits the channel envelope bound | HTTP 400 | `consumed` | `no` | `no` |
| 10 | `expiry ≥ now + delivery_horizon_secs` | `EXPIRY_TOO_SHORT` / `delivery_horizon` | `consumed` | `yes` | `no` |
| — | lock released; PIN evaluation and carrier derivation (`SPN-16`) | |  |  |  |
| 11 | not locked down | `FRAUD_SUSPECTED` | `consumed` | `no` | `no` |
| 12 | arm hook records intent (`DUR-4`) — never fails | |  |  |  |
| 13 | the three clock predicates, re-decided (`SPN-17`) | `COMMITMENT_EXPIRED` ×2, `EXPIRY_TOO_SHORT` | `consumed` | `yes` | `yes` |
| 14 | PIN attempt budget (`SPN-18`) | `BAD_PIN` / `pin` or `pin_attempt_budget` | `consumed` | `yes` | `yes` |
| — | lock released; chain preflight (`SPN-21`) | |  |  |  |
| 15 | not locked down | `FRAUD_SUSPECTED` | `consumed` | `no` | `no` |
| 16 | the three clock predicates, re-decided after the preflight | as 13 | `consumed` | `yes` | `yes` |
| 17 | spend and Escape PSBTs decode | HTTP 400 | `consumed` | `no` | `no` |
| 18 | ladder has at most 3 rungs, then each rung decodes | `PSBT_INCONSISTENT` / `escape:bump_ladder`; HTTP 400 | `consumed` | `no` | `no` |
| 19 | idempotent replay of an earlier ACCEPTED verdict (`SPN-23`) | returns it, re-stages |  | `yes` | `yes` |
| 20 | idempotent replay of an earlier REFUSED verdict | returns it |  | `no` | `no` |
| 21 | prevout fetch succeeded (node-local backend failure) | the fail-closed refusal | `consumed` | `yes` | `yes` |
| 22 | verify the spend (`SPN-26`) | policy codes | `consumed` | only `HOT_BUDGET_EXCEEDED` | `same` |
| 23 | classify; hot-class only; not mixed (`CHN-30`, `CHN-32`) | `PSBT_INCONSISTENT` / `transaction_class` | `consumed` | `no` | `no` |
| 24 | hot velocity reservation (hot only, `POL-16`) | `HOT_VELOCITY_EXCEEDED` | `consumed` | `yes` | `yes` |
| 25 | verify the Escape and every rung (`SPN-27`) | policy codes with `escape:` | `consumed` | `no` | `no` |
| 26 | withdrawn with `CHN-33` (`ADR-0022`); the row is kept so later gate numbers stand | — | — | — | — |
| 27 | hot: `expiry ≥ fire_at + combine_slack_secs` (`SPN-30`) | `EXPIRY_TOO_SHORT` / `commitment_expiry` | `consumed` | `yes` | `yes` |
| 28 | sign spend, Escape and every rung (`SPN-32`) | `PSBT_INCONSISTENT` / `signing` | `consumed` | `no` | `no` |
| 29 | stage the Carrier; register the pair atomically | `PSBT_INCONSISTENT` / `candidate_identity`, `CANDIDATE_CAPACITY` | `consumed` | `yes` | `yes` |
| 30 | record authorized txids, the Hold, the verdict; respond `Accepted` | |  |  |  |
<!-- /formal -->

**SPN-6** Lockdown MUST be checked before the lock, under the ingress hold, under the commit
hold, and after the preflight. A locked-down node answers every spend and every refresh
`FRAUD_SUSPECTED` with check `lockdown` and the fixed detail `funds quarantined by policy`
(`DUR-7`), and a `FRAUD_SUSPECTED` refusal MUST NOT stage.

**SPN-7** Coordinator authentication MUST verify a strict-DER ECDSA signature, decoded from
lowercase hex, over the tagged digest of `WIR-21` against the pinned `coordinator_auth_pubkey`.
The three failures are distinguishable in `detail` (not hex, not DER, does not verify) but share
one code and check. The signature profile is `WIR-6`; high-S takes the does-not-verify outcome.
Freshness state MUST be mutated only after the signature verifies, so an
unauthenticated flood cannot move the nonce log.

**SPN-8** A body larger than 1 MiB MUST be refused HTTP 413 before decoding; a body that does
not decode as the tagged union, a PSBT that does not decode, and a request that would not fit
the federation-uniform channel envelope MUST be refused HTTP 400 (`API-5`, `API-6`). The last of
these is checked after the nonce is consumed so that a request this node cannot relay is never
acknowledged and never relayed by a peer that could.

**SPN-9** A request MUST satisfy `expiry ≥ now + delivery_horizon_secs`, so that a Carrier this
node admits can still reach and be processed by every peer before it lapses. The horizon is
per-node, not sealed (`MAN-7`); the check is skipped only in the channel-less test build. **At
gate 10** the refusal propagates but does not stage: the arm hook has not yet run, so that
refusal signs no partial and creates no local intent, and this node counts itself in no holder
set. The same predicate is re-decided at gates 13 and 16, after the arm hook; `SPN-17` owns
those and states: "Each failure propagates and stages, since the node has by then recorded an
intent." Neither path signs a partial. Propagating without a local intent is not the same as
supplying no holder evidence: a peer that receives this node's relay still counts it under
`DUR-5`, which states that a relay "proves the peer received and processed the Carrier, not that
it froze or signed".

## The coordinator nonce log

**SPN-10** Every request MUST be coordinator-signed and fresh. Freshness is decided against two
readings: `expiry > effective_now` where `effective_now` is `SPN-13`'s rollback-guarded value,
and `expiry ≤ raw_now + max_commitment_age_secs` against the RAW wall clock, so that rollback
protection cannot widen the horizon a hostile coordinator may claim. Equality on the lower
bound is stale; on the upper bound it passes.

**SPN-11** The nonce log MUST hold, for every accepted nonce, its signed wall expiry and — for a
channel-mode spend only — its monotonic Carrier deadline `D` (`NCH-33`); refreshes, claw-backs
and channel-less spends carry no `D`. An entry is **live** while `expiry > effective_now` OR
`mono_now < D`; a deadline-bearing entry with no monotonic sample is live (fail closed). The log
is bounded at **4 096** live entries and nonces of **1 to 64 bytes** of any encoding; the
operator program draws 32 random bytes and sends them as 64 lowercase hex characters
(`OPR-47`).

**SPN-12** One nonce log MUST serve Spend, Refresh and Clawback alike, with one shared non-decreasing
high-water mark. Refresh entries are wall-only, so an accepted transition that prunes a Refresh
whose expiry exceeds a live Carrier's signed expiry advances the high-water past that Carrier;
`F4` records the consequence and the repair is open.

**SPN-13** `effective_now = max(high_water, raw_now)`. The high-water is advanced, on an accept
only, to the greatest expiry of every entry that accept pruned. It is the tombstone: a backward
clock step can never revive a pruned nonce, because the nonce it would revive has an expiry at
or below the high-water. A forward excursion passes straight through, which is why Carrier
residency has its own clock (`NCH-35`).

**SPN-14** On a request the log MUST decide in this order — length, window, replay, capacity —
so that an expired entry is pruned before its nonce is judged replayed, and a live entry is
judged replayed before capacity is consulted. Capacity **refuses; it never evicts.** A refused
request MUST mutate nothing: no entry, no high-water. On accept, and only then, the log prunes
under both clocks, computes `D = mono_now + (expiry − effective_now)` with overflow failing
closed as a window refusal, and inserts. On a channel node a nonce shared by two handler
generations is admissible only once both its wall expiry and its `D` have lapsed.

**SPN-15** The nonce is single-use per **logical** request. Endpoint failover within one
delivery re-offers the identical signed bytes including the nonce; a new logical retry draws a
fresh nonce and re-signs. Idempotency is keyed on the commitment (`SPN-23`), not the nonce, so a
retried request that was already accepted answers from the replay log after `NONCE_REPLAYED`
would otherwise have refused it — the coordinator treats `NONCE_REPLAYED` after a possible
earlier delivery as "already delivered".

## PIN evaluation

**SPN-16** After the ingress hold releases, and before any further lock is taken, the node MUST
evaluate BOTH enrolled Argon2id digests unconditionally, in the fixed order normal then duress,
and select the verdict in constant time: `0` wrong, `1` normal, `2` duress, with a double match
failing closed to duress (`MAN-21` fixes the parameters). A PIN that is empty or longer than 64
bytes is forced to WRONG **after** both evaluations, never before. In the same lock-free window
the node derives the Carrier identity (`NCH-31`), which is memory-hard for a Spend. Roughly 600
milliseconds of work therefore sits outside the lock a waiting Lockdown contends for (`DUR-15`).

**SPN-17** Under the commit hold the node MUST re-decide the three clock predicates on the commit
clock — `expiry > effective_now`, `expiry ≤ raw_now + max_commitment_age_secs`, and the delivery
horizon — because the PIN window has no bound. Each failure propagates and stages, since the
node has by then recorded an intent.

**SPN-18** The PIN attempt budget (`MAN-23`) MUST be charged under the commit hold, AFTER the arm
hook, so that a locked-out node still records a valid duress intent. Only a WRONG verdict
consumes budget. A wrong PIN is refused `BAD_PIN` / `pin`; any PIN on a locked-out node is
refused `BAD_PIN` / `pin_attempt_budget` with a fixed detail — a correct PIN while locked out
gets the same bytes, so lockout is not a PIN oracle. The backoff sleep the budget prescribes is
taken after every lock is released.

**SPN-19** The propagation rule is: **node-local refusals propagate; federation-uniform policy
refusals do not**. A clock, horizon, budget or backend refusal is something this node alone
decided, and the carrier must still reach `t` peers; a policy refusal would be refused by every
honest node, and propagating it would fan a theft out to the honest set and let a locally
refused intent become a one-node arm. `HOT_BUDGET_EXCEEDED` is the one deliberate exception on
the staging side, because an over-cap coerced spend must still freeze the federation; it is
correspondingly excluded from the replay log (`SPN-24`).

## Locks and the chain preflight

**SPN-20** The handler MUST hold the sign lock in three separate critical sections — the ingress
hold, the commit hold, and the registration hold — with the memory-hard PIN and Carrier work in
the window between the first two and the chain preflight in the window between the last two.
Nothing memory-hard and no chain I/O may run under the lock: `enter_lockdown` needs the same
lock, and the lock is unfair.

**SPN-21** The chain preflight MUST fetch every prevout of the spend and of the Escape in exactly
two batched backend calls (the ladder reuses the Escape's, having the same inputs), under the
backend timeout, outside every lock. A fetch failure is node-local; when converted to a refusal,
it propagates and stages so a peer with a working backend still processes the carrier. The I/O
runs before the registration hold and its clock rechecks. Only the conversion of a fetch error
into a refusal MUST run after the accepted and refused replay lookups, as ordered
in the ingress table. A still-fresh cached acceptance therefore wins over the fetch-error
result; a retry does not skip the I/O or the post-I/O freshness gates. If the preflight consumes
its remaining lifetime or delivery margin, the retry is refused and staged at the clock gate
even though an earlier request was accepted.

**SPN-22** The ladder MUST be bounded before its rungs are decoded: more than 3 rungs is
`PSBT_INCONSISTENT` / `escape:bump_ladder`.

## Commitments and idempotency

**SPN-23** After all preceding admission, PIN and post-preflight clock gates pass, the node MUST
compute the spend's and the Escape's commitments (`CHN-24`) and answer idempotently: a request
whose acceptance key — the spend commitment and bytes, the Escape commitment and bytes, and every
rung — matches an earlier `Accepted` returns that verdict
verbatim, re-applies its schedule, records its own intent (`DUR-4`), and re-stages; a spend whose commitment AND exact
base64-decoded PSBT bytes match an earlier recorded spend-evaluation refusal returns that refusal,
including its `API-25` fault member verbatim, and does NOT stage. Changed PSBT bytes MUST undergo
fresh evaluation even if the commitment is unchanged. Refusal matching excludes the PIN and coordinator nonce. **Idempotency before cache**
for the PIN: because the arm hook runs at gate 12, a duress resubmission of a previously
normal-accepted commitment under a fresh nonce still records a duress intent before the cached
verdict is returned. Conversely, a resubmission whose pair is named by a duress intent or its
retained nonce tombstone arms at its own holder decision (`DUR-5`: "`arm` set to the **pair
duress bit**"), including a normal-PIN resubmission. Recording the new intent and accepting the
replay do not themselves arm.

**SPN-24** The replay log MUST record `Accepted` and the spend-evaluation policy refusals
(`UNKNOWN_INPUT`, `DEST_NOT_ALLOWED`, `CHANGE_NOT_DERIVABLE`, `FEE_EXCEEDS_CAP`,
`PSBT_INCONSISTENT` from evaluation, `USER_SIG_INVALID`, `BAD_SIGHASH`) and MUST NOT record
`HOT_BUDGET_EXCEEDED`, `HOT_VELOCITY_EXCEEDED`, `EXPIRY_TOO_SHORT`, `COMMITMENT_EXPIRED`, the
refresh codes, `BAD_PIN`, `COORD_*`, `NONCE_REPLAYED`, capacity refusals or `FRAUD_SUSPECTED`:
those depend on state or time and must be re-decided. Cached refusals MUST retain the exact
spend PSBT binding for the matching rule in `SPN-23`: signature and derivation metadata are
validation inputs even though they are absent from the commitment. Escape and ladder refusals
MUST NOT populate the spend-refusal entry. A cacheable refusal MUST be recorded with its
`API-25` fault member verbatim for replay. Cache eligibility is decided by the originating check,
never just the code: confirmed-prevout and replacement-test refusals MUST NOT be cached as pure
policy refusals merely because their codes overlap. Log entries expire with their commitment.

## Validation

**SPN-25** For every input whose prevout the backend reports as **confirmed**, the node MUST
require the PSBT's `witness_utxo` script and value to equal the chain's; a difference is
`PSBT_INCONSISTENT` / `prevout_ground_truth`. A prevout the backend reports absent or
unconfirmed is tolerated here — it is the vault-authorized-unconfirmed case, and its
admissibility is decided at fire time (`DUR-22`). The fault-list rule is `API-25`'s
"Confirmed prevout script/value mismatches" row; absent and unconfirmed prevouts do not enter it.

**SPN-26** Verifying the spend MUST run, in order: the user signature on every input
(`CHN-12`); the prevout comparison (`SPN-25`); policy evaluation (`POL-6`). Then classification
(`CHN-30`), the refresh-shaped refusal (`CHN-32`), and for a hot spend the velocity reservation
(`POL-16`).

**SPN-27** Verifying the Escape MUST run the same three steps on the Escape with every refusal's
check prefixed `escape:`, then require escape-class. Gate 25 MUST check `CHN-15`'s
"every input's `nSequence` to `0xfffffffd`" on the base even when the ladder is empty, and on
every rung; any other sequence value refuses as `escape:bump_ladder`. It MUST apply the ladder
rules of `CHN-14`–`CHN-16` to every rung with refusals `escape:bump_ladder`, then verify each rung
as an Escape against the Escape's own prevouts. An Escape whose evaluation refuses stages nothing.
Diagnostics follow `API-25`: "No later check or other transaction may contribute" and
"Fee-bump rungs MUST NOT carry a fault list"; the base Escape uses `tx = escape`.

**SPN-28** Classification MUST be recorded with the candidate: the class decides the fire time
(`SPN-30`), the freeze (`DUR-11`), and whether the pending log records it.

In the formal kernel, `Kernel.Cand.hot` represents that recorded class and `accept` takes it as
given. Kernel safety proves a fact about the recorded Boolean; it does not bind the independently
supplied `Kernel.Tx.outflow` to real outputs. A candidate with `hot = false` and positive outflow
is outside the classification-to-value interpretation of these theorems.

**SPN-29** The velocity reservation MUST be placed before signing and re-validated under the
registration hold. If registration refuses, only a reservation placed by this request MUST be
unwound in the same step. A reservation placed by an earlier acceptance of the same commitment
MUST remain unchanged by that refusal (`POL-18`).

## The Hold and the fire window

**SPN-30** A hot-class spend's fire time is `ingress_now + hold_secs`. Its fire window is
`[fire_at, min(expiry, fire_at + combine_slack_secs)]`, both
ends inclusive. A hot spend MUST satisfy `expiry ≥ fire_at + combine_slack_secs`, equality
passing, or it is refused `EXPIRY_TOO_SHORT` / `commitment_expiry`. Every accepted hot-class
spend MUST be recorded in the **pending log** as `commitment_id → expiry`; this record is the
Hold timer, what refresh subordination reads, and what `/pending` projects. Refreshes and
claw-backs are never pending.

**SPN-31** Before its chain preflight begins, a spend MUST claim an **in-flight marker** that
refresh subordination consults alongside the pending log (`SPN-45`), released on every exit
including a panic unwind. Without it a refresh could register during the preflight window and
consume an input the mandatory Escape needs.

## Signing and registration

**SPN-32** The node MUST sign the spend, the Escape and every rung at ingress, pin-independently,
with `SIGHASH_ALL` (`CHN-11`), and MUST transmit none of those partials in the response or to
any peer at this point. It then stages the Carrier — pushes the request to the outbox and counts
itself as a holder — and registers the spend and Escape as one **pair** in the candidate registry
atomically: a candidate that cannot be BUILT from its accepted spec is `PSBT_INCONSISTENT` /
`candidate_registration`; a conflicting resident commitment is `PSBT_INCONSISTENT` /
`candidate_identity`; a registry that cannot admit both members within `max_active_candidates` and
`max_candidate_store_bytes` is `CANDIDATE_CAPACITY` / `candidate_registry_capacity`; an already
resident compatible pair is left exactly as is. Subject to these checks, registration MUST admit
both distinct ids together when both are absent, or retain both residents when they are
compatible **as this pair**. Each
resident MUST have the requested role (spend or Escape), the request's other id recorded as its
sibling, and the same transaction, hot classification and expiry. The resident Escape MUST also
have the same **ordered rung txids**, including the empty list. Compare neither PSBT bytes nor
held partials, the rung latch, release floor or `released_through`: valid changed PSBT bytes
preserving the transactions remain compatible after fresh evaluation.

Equal member ids, exactly one resident id, crossed members of different pairs, swapped roles,
an unpaired resident claw-back under either id, or any immutable mismatch MUST refuse the whole
registration as `PSBT_INCONSISTENT` / `candidate_identity`, leaving every resident untouched.
Registration MUST NOT reset terminality, release state, held partials, quorum or any other resident
lifecycle state. This preservation applies to registration itself. An accepted replay follows
`SPN-23`: "re-applies its schedule, records its own intent (`DUR-4`), and re-stages". The schedule path remains:
`DUR-14` says "On every hot spend accepted while armed, `T ← max(min(T, its fire_at −
epsilon_secs), now)`". `DUR-20` says "every hot acceptance and every holder decision MUST visit
every selected entry and write its window … under BOTH PINs and whether or not `T` actually moved".
Staging on registration refusal remains governed by `SPN-5`, row 29 (Staging: "yes").

No live candidate is ever evicted for capacity:
the whole reservation — current bytes plus the maximum partial-signature growth over every rung,
input and member — is charged at registration.

**SPN-33** On acceptance the node MUST add the spend's, the Escape's and every rung's txid to its
**vault-authorized set**, which the watchtower recognises (`WTC-18`) and which qualifies
unconfirmed parents at fire time (`DUR-22`). When any transaction settles — seen in the mempool
or confirmed, including a confirmed armed Escape — the node MUST remove from the pending log the
settled id, its paired sibling, and every other resident hot candidate that shares an input with
it, and mark the input-conflicting candidates **terminal**: removal from the pending log is not
removal from the registry, and a terminal candidate stays resident under `SPN-41`'s pruning and
is never due (`SPN-38`), so a hot spend a claw-back has defeated is not finalized at its Hold
expiry even if the claw-back is later evicted. Reservation refunds follow `POL-18`: "invalidated by a
conflicting confirmation while unexposed." Mempool-only settlement MUST NOT refund a reservation;
the ledger retains its original reservation time, expiry and exposure state independently of
candidate residency. An unexposed retained charge may be refunded after its signed expiry
strictly passes or after a conflicting confirmation; an exposed charge ages under `POL-19`.
Candidate terminality or registry removal alone MUST NOT refund this charge. The escape sweep
is the implicit cancel of a pending spend; there is no cancel
message, and there MUST NOT be one (`DUR-16`).

**SPN-34** The response to an accepted spend is `Accepted { commitment_id, first_seen,
remaining_secs }` with `first_seen` the ingress time and `remaining_secs = fire_at − first_seen`
— zero for a refresh and a claw-back — fixed at first acceptance and replayed verbatim
thereafter. It carries
no signature and no PSBT (`API-12`).

**SPN-35** After the handler returns, the node MUST drain its outbox: one relay of the verbatim
request to every peer, with deadline = the request's `expiry` (`NCH-31`). The relay is
loop-free by construction: the nonce was consumed on first processing, so a copy that comes
back is `NONCE_REPLAYED` and is not relayed again; a fan-out ends after one round at
`n × (n − 1)` messages.

## Candidates

**SPN-36** A **candidate** is one exact commitment, born fully signed and fully withheld, with:
its role (spend or escape), whether it is hot, its paired sibling's id, whether its holder quorum
has been reached, its base signing variant and up to 3 rung variants each holding the canonical
PSBT, the recomputed sighashes, the user-signature hash and the partials received per `(input,
signer)`, a monotone rung latch and release floor, its expiry, its fire window if any, and the
`released`, `released_through` and `broadcast` flags. A rung's variant strips every partial that
is not the user's or this node's before it is stored.

**SPN-37** A SpendRequest's pair is registered **closed**: `holder_quorum_reached = false`,
opened only by the holder decision of a Carrier naming it, with `DUR-5`'s local acceptance authority
("only for a Carrier this node accepted, or replayed as accepted"). A refresh is born open. The Escape
member of a pair is registered with **no** fire window; its window `[T, T + combine_slack_secs]`
is installed by the arm commit and is deliberately not capped by the commitment expiry.

**SPN-38** A candidate is **due** iff it is not broadcast, is not terminal (`SPN-33`), is not
a frozen hot candidate (`DUR-11`), its slot is active — its quorum is reached and, for an Escape, `sweep_active` holds
AND the entry's own duress bit is set (`DUR-10`) — and its fire window is open now. The two
Escape conjuncts MUST be read unconditionally and combined in constant time, never as an early
return: before `T` the window conjunct is false on every node, so the bits decide nothing, and a
branch on them would be work a normal-PIN node does not do. The release gate (`DUR-8`) is the sole egress
for a partial and MUST release the **prefix** of rungs from the release floor through the
authorized rung `min(latch, quota_rung_cap)`. Over a common ladder with compatible user-signature
hashes, this permits nodes whose readings differ by one step to converge on a rung signed by
`t` nodes, given enough successful passes and partial delivery within their fire windows. Compute
`rung_budget = max(saturating_sub(per_peer_quota_per_min, 2), 1)` and
`affordable_rungs = rung_budget ÷ inputs_per_variant`, where division is integer floor,
`inputs_per_variant > 0`, and `saturating_sub(a, b) = max(a − b, 0)`.
If `affordable_rungs = 0`, release nothing and advance no release bookkeeping on this pass.

`release_floor` is the candidate's **next-unscheduled-rung cursor**, per candidate and monotone.
It MUST be initialised to `0` at registration (`SPN-32`). Let `a` be the lowest rung this node's
own pre-release predicate currently admits (`DUR-21`; `a = 0` for a candidate with no ladder) and
`F = max(release_floor, a)`. A pass releases the interval `[F, U]` where
`quota_rung_cap = min(last_rung_index, F + affordable_rungs − 1)`, computed without overflow, and
`U = min(latch, quota_rung_cap)`. If `F > U` the pass MUST release nothing and leave the cursor
unchanged. The cap MUST be anchored on `F` and never on `release_floor`: with the cursor still at
an inadmissible low rung, a cap measured from the cursor can fall below `F` on every pass, and the
candidate then never releases anything at all. This is a per-candidate batch bound; peer admission
remains subject to the shared quota (`NCH-15`). The release time MUST be sampled after the guard
is acquired. Only a pass that released at least one rung MUST set `release_floor = U + 1`;
`last_rung_index + 1` denotes exhaustion. The cursor records that a rung has been queued for
transport, not that a peer received it: rungs already queued keep their own retry schedules
(`NCH-8`) and MUST NOT be re-queued merely to reconstruct the prefix, since `NCH-15` charges a
duplicate envelope even though `NCH-25` makes a duplicate partial an idempotent `ACCEPTED`.
Over a common ladder, `a` does not move over the candidate's life: `DUR-25` requires
"Admissibility before release MUST be evaluated at each rung's **maximum** finalized
vsize" and coverage bounds only the top of the admissible interval.
With that common-ladder premise, every honest node's cumulative prefix begins at the same rung.
Partial exchange also requires compatible user-signature hashes: `NCH-24` requires that "the
rung is found by txid" and "the user-signature hash matches". Local cursor progress establishes
neither ladder agreement nor delivery; the per-node split and admissible-base fallback are
specified in `DUR-28`.

Boundary examples, rendered from `BtcPolicy.Render.spn38Table` (`none` means no release). The
last column is the cap the withdrawn cursor anchor would give, so the rows whose two caps differ
are the ones that distinguish the anchors: `a > 0` is necessary for them to differ and not
sufficient, and `BtcPolicy.Cursor.a_gt_zero_is_not_sufficient` names a row with `a > 0` whose
caps agree, because the budget from the cursor reaches past `a` (`F51`).

<!-- formal: BtcPolicy.Render.spn38Table -->
| peer quota | inputs per variant | release floor | lowest admissible | last rung index | quota rung cap | cap if anchored on the cursor (`F51`) |
|---|---|---|---|---|---|---|
| 0 | 1 | 0 | 0 | 3 | 0 | 0 |
| 1 | 1 | 0 | 0 | 3 | 0 | 0 |
| 2 | 2 | 0 | 0 | 3 | none | none |
| 3 | 2 | 0 | 0 | 3 | none | none |
| 600 | 598 | 0 | 0 | 3 | 0 | 0 |
| 600 | 599 | 0 | 0 | 3 | none | none |
| 600 | 1 | 2 | 0 | 3 | 3 | 3 |
| 3 | 1 | 0 | 1 | 3 | 1 | 0 |
| 3 | 1 | 0 | 3 | 3 | 3 | 0 |
| 600 | 1 | 0 | 2 | 3 | 3 | 3 |
<!-- /formal -->

**SPN-39** On every fire pass, for each due candidate, the node MUST: settle it if the network
already shows it (in mempool or confirmed) rather than re-sending; otherwise finalize on a clone
at the highest rung at or below the latch that carries at least `t` distinct valid partials on
every input, walking downward; assemble the package (`WTC-24`); test it for mempool acceptance;
re-check the slot, the freeze and the window under the store lock as the linearization point
between arming and sending; then broadcast. Redundant broadcast of identical bytes is the
designed steady state; a duplicate-rejection whose transaction is now visible is treated as
settled.

`BtcPolicy.Exhibits.ReleaseKernel.no_hot_broadcast_while_armed_with_current` instantiates the
general armed-send theorem at the current rules, discharging the send-time re-authorization
premise. The general claim lives at `DUR-11`, with the recorded-class boundary at `SPN-28`.

**SPN-41** The registry MUST prune every candidate whose `expiry < now` on each pass, EXCEPT a
non-broadcast Escape whose fire window has not closed and its paired spend — the exemption is
granted to the normal PIN's inert slot too, so probing `CANDIDATE_CAPACITY` before `T` reveals
nothing — and MUST remove every selected Escape and its pair when the armed window closes
regardless of their own expiries. The last authorized second is `now == expiry`; `expiry < now`
is expired at lookup as well as at prune.

**SPN-42** The pending log MUST retain an unsettled entry while `expiry ≥ now`, including
equality, and prune it when `expiry < now`. Before expiry, an id is removed only on a public
network settlement event (`SPN-33`), never by a PIN-dependent path. Expiry pruning is identical
under both PINs.

## Refresh

**SPN-43** A refresh MUST arrive only as a RefreshRequest, pin-less, and fires at ingress. The
handler runs: Lockdown checks; coordinator authentication, nonce length, freshness, replay and
capacity as `SPN-5` gates 4–8 (a Refresh records no `D` but still samples the monotonic clock);
propagatability; then, outside the lock, one batched prevout fetch and — for EVERY input,
looked up by the txid of its creating transaction and never by the prevout read's confirmed
flag — the confirming block of that transaction and its median-time-past, and the tip's
(`WTC-2`'s two mempool-independent rows), because `SPN-46` compares those and `SPN-20` forbids
chain I/O under the lock. The prevout read includes the mempool, so an outpoint a resident
replacement candidate already spends reads ABSENT there while its creating transaction is
confirmed; that is the replacement case, and the node MUST apply `WTC-25`'s test at ingress —
the resident is a vault-authorized refresh over exactly these ordered outpoints — or refuse
`UNKNOWN_INPUT` / `replacement_inputs` (`API-14`). The list is owned by `API-25`'s
"Inputs failing the replacement test" row, with `tx = refresh`. Then,
under the lock again, Lockdown, the two expiry predicates, decode, idempotent replay, pruning,
verification, class, subordination, interval (a comparison of the values already fetched),
feerate, signing, registration, and the response.

A refresh has no gate table of its own, so `SPN-19`'s classes are assigned here rather than left
to be inferred. `SPN-19` states the rule: "**node-local refusals propagate; federation-uniform
policy refusals do not**". `REFRESH_SUBORDINATED` is node-local — decided from this node's own
pending log and in-flight marker, which no peer shares (`DOM-7`) — and therefore propagates, so a
peer that has no spend pending can still accept the refresh. `REFRESH_TOO_SOON` and
`REFRESH_FEE_EXCEEDS_CAP` do NOT propagate: both are federation-uniform policy refusals, the first
read from the chain every honest node shares (`SPN-46`, `WTC-1`) and the second from a
manifest-sealed ceiling (`MAN-2`), so every honest node at the same tip refuses the same
transaction, exactly like `FEE_EXCEEDS_CAP` on a spend. Two honest nodes whose tips differ by a
block CAN split on a coin whose age crosses the interval in that block; that is harmless, and not
a reason to propagate: the nodes that accept it relay it to every peer (`SPN-35`), so the lagging
node still receives it from them; the refusal is never replay-logged (`SPN-24`) so a resubmission
under a fresh nonce is re-decided once the node's tip advances; and the lagging node
alerts `UNRECOGNIZED_SPEND` when the refresh confirms (`WTC-18`), the same false positive every
node-local refusal produces. No refresh refusal ever **stages**:
staging counts this node as a holder of a Carrier (`DUR-5`), and a refresh records no arm intent
(`SPN-49`).

**SPN-44** A refresh MUST verify like a spend (`SPN-26`) and classify as refresh-class; any other
class is `PSBT_INCONSISTENT` / `transaction_class`, and `CHN-30` is where a transaction that
mints vault coins is refused. A refresh MUST have at most **24** inputs, refused
`PSBT_INCONSISTENT` / `transaction_class` above that: `SPN-47` bounds the fee by
`refresh_max_feerate × vsize`, and a vsize the composer chooses is a bound the attacker chooses —
anyone can deposit dust to the vault script, wait one interval, and refresh that dust beside one
large vault coin, paying for a standardness-sized transaction from the large coin; at the
`WIR-14` ceiling that is roughly ten million satoshis per vault coin per interval against the
twenty thousand a one-in-one-out refresh burns. With the input count capped the per-coin bound is
`refresh_max_feerate × vsize(24-in, 24-out)`, a number an Operator can read. The constant
matches `WTC-24`'s ancestor limit; a vault with more coins refreshes in batches. Every input's
`nSequence` MUST be `0xfffffffd` (`CHN-18`), refused `PSBT_INCONSISTENT` / `transaction_class`
otherwise, so that every refresh signals BIP125 and a later higher-fee refresh of the same coins
can replace it in the mempool — BIP125 is a property the RESIDENT must carry, which is why the
rule is unconditional rather than a rule for replacements only.

**SPN-45** A refresh MUST be refused `REFRESH_SUBORDINATED` / `refresh_subordination` while ANY
spend is pending on this node — the pending log has any live entry, or a spend's in-flight
marker (`SPN-31`) is held. The rule is deliberately **coarse**, not input-overlap: the armed
Escape sweeps most of the vault while the triggering spend touches a subset, so an overlap rule
would let a refresh spend an Escape input and invalidate the sweep. Both halves of the predicate
MUST produce byte-identical refusals. The refusal is retriable and is not recorded.

**SPN-46** A refresh MUST be refused `REFRESH_TOO_SOON` / `refresh_min_interval` unless EVERY
input's coin is at least `refresh_min_interval_secs` old **by the chain's own clock**: with
`confirming` the block in which the input's creating transaction confirmed on the active chain,
`tip` the node's current tip, and `MTP` BIP113 median-time-past,

```
MTP(tip) − MTP(confirming) ≥ refresh_min_interval_secs
```

with equality passing. `confirming` is found from the input's creating transaction by txid
(`WTC-2`), NEVER from the prevout read's confirmed flag: that read includes the mempool, and an
outpoint a resident replacement already spends reads absent there while its creating transaction
is confirmed, which would refuse the bump path `WTC-25` exists to keep open and would make this
verdict depend on this node's mempool. An input whose creating transaction is not confirmed on
the active chain has no age and MUST be refused the same way — its recovery timer (`CHN-4`) has
not started
either, so refreshing it resets nothing. The rule reads nothing about WHAT created the coin: a
deposit, change from a hot spend, and the output of an earlier refresh are all refused while
younger than the interval, and all admissible once older. `API-25` owns the fault list for
"Too-young or unconfirmed refresh inputs", with `tx = refresh`.

This is a fact of consensus, read identically by every honest node from the same tip (`WTC-1`),
and that is what makes the bound hold: a coin can be refreshed at most once per interval, at most
`refresh_max_feerate × vsize` is burned each time (`SPN-47`), and no arrangement of which nodes
co-sign can change either, because there is no per-node record to route around. **A node keeps
no refresh log.** The earlier design's private log of accepted refreshes is withdrawn; `ADR-0019`
records why, and `F52` the two defects it had. A refresh that is signed but never confirms leaves
no trace on the chain, so a replacement of it over the same inputs at a higher fee is admissible
on every node for as long as the coins stay old enough, `WTC-25` walks its ancestry over the
resident as a replacement, and `CHN-18`'s `0xfffffffd` lets the mempool accept it — that is the
bump path, end to end, and refresh needs no ladder for it. The MTP is chain state and not one of `DOM-24`'s three node clocks; nodes whose
tips differ by a block differ by minutes on an interval of days, the tolerance `DUR-30` already
accepts. A backend that cannot answer fails closed (`WTC-1`), the dependency every input's
preflight already carries (`SPN-21`).

**SPN-47** A refresh MUST be refused `REFRESH_FEE_EXCEEDS_CAP` / `refresh_fee_cap` when
`fee > refresh_max_feerate × vsize` in arithmetic that cannot overflow, with `fee = Σ
witness_utxo − Σ outputs` and `vsize` the refresh transaction's **maximum finalized vsize**
(`CHN-34`). Equality passes. It is the finalized size and never the unsigned one: a refresh is a
Normal-path spend, so it carries `t + 1` signatures by the time it is broadcast, and at the
worked shape of `WIR-36` the unsigned transaction measures 82 vB against a finalized 203. Bounding
an absolute fee by the unsigned size would make the sealed feerate bite two and a half times
harder than it reads, forcing every refresh to underpay the rate its operator chose. A refresh is
not subject to the Hold and has no PIN, which is why it needs these two bounds in place of them
(`ADR-0006`). The cap is an absolute sealed `sat/vB`, and that supersedes the form `ADR-0012`'s
refresh section first proposed — "a small multiple of the node's fee estimate". A multiple of a
per-node backend estimate diverges between honest nodes by construction, the disease `DUR-30`
spends its whole requirement fighting on the sweep path, and it cannot be audited at seal time;
`ADR-0012`'s historical instruction does not override this requirement (`README`, *The decisions
this specification is built on*).

**SPN-48** A refresh is registered as ONE candidate — not hot, not duress, born open — with fire
window `[now, min(expiry, now + combine_slack_secs)]`, no Escape, no hot reservation, and a
Carrier identity derived from its coordinator request digest without the memory-hard step
(`NCH-31`). Its txid enters the authorized set and it is relayed to peers like a spend. Its
response is `Accepted` with `remaining_secs = 0`.

**SPN-49** A refresh MUST NOT touch the PIN attempt budget, MUST NOT record a duress intent, and
MUST NOT change the Armed overlay. There is no duress-versus-normal decision on a refresh, so it
cannot be used as a duress probe.

## The claw-back path

**SPN-50** A claw-back MUST arrive only as a ClawbackRequest, pin-less, and fires at ingress
(`ADR-0022`). Its handler is `SPN-43`'s with the refresh-only steps removed: Lockdown checks;
coordinator authentication, nonce length, freshness, replay and capacity as `SPN-5` gates 4–8
(a claw-back, like a Refresh, records no `D` but samples the monotonic clock); propagatability;
the in-flight marker of `SPN-31`, claimed exactly as a spend claims it, so that `SPN-45` holds
a refresh off the claw-back's inputs for the length of its preflight; outside the lock, one
batched prevout fetch, with `SPN-25`'s tolerance of an absent or unconfirmed prevout; under
the lock, Lockdown, the two expiry predicates, decode, idempotent replay, pruning, verification
as a spend (`SPN-26`, whose `POL-6` pass is the claw-back's only fee bound, `POL-12`), class —
escape-class per `CHN-35`, with its no-change, `nSequence` and `nLockTime` rules, refused
`PSBT_INCONSISTENT` / `transaction_class` otherwise — signing, registration, and the response.
It carries NONE of refresh's four guards, and each omission is deliberate: not `SPN-45`'s
subordination, because a claw-back exists to spend a pending spend's inputs before that spend
fires (`OPS-19`), and one that spends the armed Escape's inputs pays the same wallet, so it is
the sweep firing early; not `SPN-46`'s interval, because a coin that leaves the vault cannot be
swept again; not `SPN-47`'s sealed feerate cap, because the burn is one-shot under `POL-12`
once `CHN-35` forbids change, and an emergency sweep may need to outbid a thief; not `SPN-44`'s
input cap, because a percentage cap leaves the attacker no vsize lever. An outpoint a resident
claw-back already spends reads absent from the mempool-inclusive prevout read; the node MUST
apply `WTC-25`'s test — the resident is a vault-authorized claw-back over exactly these ordered
outpoints — or refuse `UNKNOWN_INPUT` / `replacement_inputs` (`API-14`), with the fault list
owned by `API-25`'s "Inputs failing the replacement test" row and `tx = clawback`.
`SPN-24` states: "confirmed-prevout and replacement-test refusals MUST NOT be cached as pure
policy refusals merely because their codes overlap"; this test depends on this node's mempool.
Every refusal a claw-back can receive is federation-uniform or node-local exactly as the same refusal is on a spend (`SPN-19`); none stages, since a claw-back records no
arm intent.

**SPN-51** A claw-back is registered, relayed and answered exactly as a refresh is (`SPN-48`):
one candidate, not hot, not duress, born open, fire window `[now, min(expiry, now +
combine_slack_secs)]`, no Escape, no hot reservation, a Carrier identity that is `NCH-31`'s
tag over the request digest with no stretch, as a Refresh's is, its txid in the vault-authorized set, relayed to peers
like a spend, answered `Accepted` with `remaining_secs = 0`. `SPN-49` applies to it word for
word: no PIN attempt budget, no duress intent, no change to the Armed overlay, so it cannot be a
duress probe. An armed node signs a claw-back exactly as an idle one does, because `DUR-11`
freezes hot-class candidates only (`DUR-36`); a locked-down node refuses it with everything
else (`DUR-7`).
