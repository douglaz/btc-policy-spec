# 14 — Known defects in the reference implementation

Every entry is a defect found by review of the reference implementation and, where marked
*verified*, reproduced against it. Each is written as a prohibition so a reimplementation can be
checked against it, and each names the requirement that now owns the rule. The reference
project's tracking record (`btc-policy-<id>`) is cited so the two ledgers can be joined; the
reference code is named by crate and function, never by line.

Identifiers are stable and cited from the other documents; they are grouped by theme but not
renumbered.

## Clocks and Carrier state

### DEF-1 — A passive peer receipt could erase the node's own arm intent — *verified*

The Carrier memo lookup pruned intents against the RAW wall clock, driven by an untrusted peer
receipt. A transient forward excursion — an NTP step, a VM restore, an RTC fault — past a live
Carrier's signed expiry deleted this node's own arm intent and memo; the sender's next receipt
resolved to vacant and was answered `ACCEPTED`, so it never retried, and the node could be left
unarmed beside `t − 1` compromised peers holding a coerced partial. The class is theft, reached
from an environmental fault rather than a hostile coordinator.

**Prohibition** — a wall reading MUST NOT retire, replace or extend Carrier state (`NCH-35`);
residency MUST be fixed at acceptance from a monotonic clock (`NCH-33`); an in-flight owner MUST
answer `RATE_LIMITED{1}` without recording the sender, never `ACCEPTED` (`NCH-29`); an exact
actionable receipt whose wall sample is past `E` MUST get the fixed 30-second retry
(`NCH-36`).

*Reference: `btc-policy-q6v`, `btc-policy-sxt` and children; `vault-node`
`channel::carrier_memo_lookup`, `channel::confirm_carrier`, `replay::NonceLog`.*

### DEF-2 — The freshness diagnostic could evict on-chain evidence

Every stale envelope from one latched-forward peer appended a new event to the alert queue,
contending for the queue's capacity and evicting unrelated watchtower alerts.

**Prohibition** — freshness diagnostics MUST coalesce per peer on the ingress high-water and
never resurrect an evicted entry (`NCH-16`).

*Reference: `btc-policy-qzo`; `vault-node` `watchtower::AlertQueue::record_freshness_reject`.*

## Locks and Lockdown

### DEF-3 — Both memory-hard PIN evaluations ran under the sign lock — *verified*

Roughly 600 milliseconds of Argon2 and carrier derivation per request sat inside the critical
section that `enter_lockdown` needs. The delay to Lockdown remains unbounded (`F13`); this
shortened each individual hold and closed a silent receipt-loss window on the way.

**Prohibition** — no memory-hard work and no chain I/O under the sign lock (`SPN-20`).

*Reference: `btc-policy-9zs`; `vault-node` `handle_sign_after_lock`.*

### DEF-4 — The release gate was fail-closed under a poisoned lock by accident

A panic while holding the sign lock poisoned it; a uniform "lock poisoned" expectation then
bricked arming, Lockdown and the fire path at once. A poisoned node released nothing only
because the fire pass happened to acquire the sign lock before its release loop — a property
asserted nowhere and one refactor from fail-open.

**Prohibition** — a poisoned critical lock MUST force Lockdown through a lock-free path and
MUST release nothing, and both MUST be asserted by tests that poison the lock (`DUR-9`, `STO-10`).

*Reference: `btc-policy-9y5.2`; `vault-node` `force_lockdown_fail_closed`,
`fire_tick_with_lockdown_net`.*

### DEF-5 — A confirmed armed Escape left the hot candidates it defeated in `/pending`

The confirmed-escape settlement branch removed only its paired candidate and never ran the
input-overlap invalidation scan, so defeated candidates stayed visible until expiry, kept their
Hot-budget reservations, and contradicted `/pending`'s settlement semantics.

**Prohibition** — every settlement, including a confirmed armed Escape, MUST apply `SPN-33`'s
pending-log removal and terminalization to every hot candidate sharing an input with it, and
refunds follow `SPN-33`'s rule alone: "Mempool-only settlement MUST NOT refund a reservation";
a conflicting confirmation refunds an unexposed one (`POL-18`, `DUR-33`).

*Reference: `btc-policy-6nq`; `vault-node` `channel::PartialStore::invalidate_hot_conflicts`.*

## The chain

### DEF-6 — The chain loop was reorg-blind

The watchtower cursor was a bare monotonic height that never rewound, so a recovery-path or
unrecognised spend re-landing below it after a reorg was silently missed; an armed Escape left
unconfirmed after its combine window was never re-broadcast; scans began at genesis on every
pass; and policy evaluated `witness_utxo` without chain verification.

**Prohibition** — the cursor MUST hold block-hash anchors and rewind on mismatch (`WTC-13`); a
scan MUST prove the chain it scanned (`WTC-12`); the armed Escape MUST re-broadcast within its
window (`DUR-31`); confirmed prevouts MUST be cross-checked against the chain before evaluation
(`SPN-25`).

*Reference: `btc-policy-9y5.3`; `vault-node` `watchtower::scan_pass`, `chain::spends_of`.*

### DEF-7 — A refresh could race a spend's out-of-lock chain preflight

Refresh subordination required the spend to be registered, and during its out-of-lock preflight
it was not, so a concurrent refresh could register as immediately fireable and consume an input
the mandatory Escape needed — funds to Recovery, not theft, but honest-reachable.

**Prohibition** — a spend MUST claim an in-flight marker before its preflight, released on
every exit, and subordination MUST consult it (`SPN-31`, `SPN-45`).

*Reference: `btc-policy-f91`; `vault-node` `enter_spend_preflight`.*

### DEF-8 — The coordinator's HTTP client read responses without bound

A fixed connect timeout, a per-read inactivity timeout and an unbounded read-to-close let a
manifest-pinned peer or a local backend drip forever or exhaust coordinator memory.

**Prohibition** — one monotonic deadline created before connect and spent across connect,
writes, the whole response and the terminal end of stream; a cap on the entire raw response in
one zeroizing allocation that never grows; strict framing at end of stream; a `NotSent`
outcome reachable only before connect. Reissue of a signed request is authorized only when
EVERY endpoint was `NotSent`; a single endpoint's `NotSent` authorizes nothing, and any
post-write status, `400` and `413` included, is possible delivery (`WTC-29`, `API-16`,
`OPR-49`, `OPR-51`).

*Reference: `btc-policy-http-bounded-ingress-response-qhe`; `vault-cli` `http::Policy`.*

### DEF-9 — The startup UTXO warm was a full set scan — *measured*

About ten seconds per scan against signet's 72-million-output set, serialised process-wide by
Bitcoin Core, so five nodes sharing one backend queued behind each other past a readiness
deadline; every restart and every periodic refresh repeated it.

**Prohibition** — the steady state MUST be served by a node-owned watch-only descriptor wallet
with the full scan as cold-start and repair fallback (`WTC-6`); the fire path MUST never scan
(`WTC-5`).

*Reference: `btc-policy-hn8`, `btc-policy-nvr`; `vault-node`
`chain::refresh_vault_unspent_cache_mode`.*

### DEF-10 — The fee-ladder residency check pulled the whole mempool per rung per tick

With no rung resident, a four-rung ladder parsed the entire mempool up to four times per
one-second tick, worst under the congestion that makes the combine window tightest.

**Prohibition** — mempool residency of a ladder MUST be read from one snapshot (`WTC-2`,
"first resident of these"). *The ancestry walk still issues one full mempool read per input
parent — `btc-policy-zzv`.*

*Reference: `btc-policy-nvr`; `vault-node` `chain::mempool_resident`.*

## Silence

### DEF-11 — The wall-clock silence gate was noise-dominated — *measured*

Two CI runs of identical code measured the normal-versus-duress ingress skew at 224 ms one way
and 680 ms the other, against a 199 ms one-Argon2 target effect. A gate whose noise exceeds its
detection threshold can neither fail honestly nor pass meaningfully.

**Prohibition** — silence MUST be gated deterministically: identical ordered handler
operations, identical pin-masked state projections, identical evaluation counts, across every
request shape including a locked-out node (`DUR-1`, `CNF-40`); wall-clock skew MAY be measured
and MUST be reported as advisory (`SEC-47`).

*Reference: `btc-policy-c9r`; `vault-node` `ingress_trace`.*

### DEF-12 — The channel confirmation marker keyed on the arm bit

A harness-only marker fired on holder confirmation only when the confirmation ARMED, which is
present under duress and absent under normal — a duress oracle hanging off an ordinary log.

**Prohibition** — every artifact derived from a holder confirmation MUST key on pin-uniform
state, never on the arm bit; `committed` and `armed` MUST be separate values and production MUST
consume only the first (`DUR-5`).

*Reference: 2026-07-22 holistic audit; `vault-node` `channel::CarrierConfirmation`.*

### DEF-13 — The coordinator-auth-key thief was invisible during the Hold

A thief holding the user key, the PIN and the coordinator auth key could feed one node directly
and let propagation arm the federation, and no surface the user watched showed the pending
spend; `/events` carried only on-chain alerts.

**Prohibition** — every node MUST project its accepted-but-unsettled hot candidates on a
pin-uniform read surface (`API-21`).

*Reference: `btc-policy-k0t`; `vault-node` `Node::pending_projection`.*

## The harness and the gate

### DEF-14 — The class check was misdocumented as an unconditional bypass

Three sites asserted that a misclassified 99%-to-hot spend "completes instantly" under the
duress PIN. The mechanism was right and the magnitude wrong: the per-transaction Hot cap is
class-independent and arming takes no class, so the bound is drain-at-the-cap for the duress
window, then Lockdown.

**Prohibition** — a security claim MUST be stated at its true strength (`CHN-31`, `POL-11`), and
a figure MUST live in exactly one document.

*Reference: `btc-policy-yh7`, `btc-policy-nia`; `ADR-0017`.*

### DEF-15 — The adversarial harness is blind to a mixed-class spend — *measured*

With the mixed hot-plus-escape arm of classification made to return escape-class, every
harness scenario and all three demos stayed green while four unit tests went red, because no
harness spend has more than one destination class.

**Prohibition** — a conformance suite MUST construct a mixed-class spend end to end and assert
its refusal under BOTH PINs, and MUST be shown to go red, naming that scenario, when the
mixed arm is faulted again (`CNF-22`); a green scorecard is evidence about the properties its
scenarios construct and nothing else. Any statement of what the fault reaches carries its
precondition — stolen hot keys — or it overstates (`CHN-31`).

*Reference: `btc-policy-u98`; `vault-cli` `attack`.*

### DEF-16 — The launch gate ran red for dozens of consecutive runs and nobody noticed — *verified*

About half died at startup with zero steps; the rest executed the full gate and failed. Work was
merged throughout on the assumption a push-triggered gate was watching.

**Prohibition** — a gate MUST be shown able to fail on a deliberately introduced regression,
and the demonstration MUST be repeated in CI rather than remembered (`CNF-3`, `AGENTS.md`).

*Reference: `btc-policy-9yf`, `btc-policy-nia`.*

## The ceremony

### DEF-17 — The manifest preimage was documented two fields short — *verified*

The ADR's canonical field list omitted the two fire-time selector fields and both `u32` counts
while instructing reimplementers to work from it. Following it yields `WRONG_MANIFEST` at
startup. The preimage `hot_allowlist` was also documented in two places as the full allowlist
when it is the allowlist minus the escape descriptor.

**Prohibition** — the preimage has one normative home (`MAN-2`), it is executable
(`tools/check_vectors.py`), and every other mention cites it (`F14`).

*Reference: `btc-policy-0ip`.*

### DEF-18 — A node key was once written to the config at rest

The first provisioning wrote `node_seckey` into the node's configuration file. A disk image, a
provider console or rescue mode would have yielded the key.

**Prohibition** — no signing key at rest; the configuration carries only public derivation
parameters and the key is derived at start from a preimage the machine does not hold
(`MAN-15`, `MAN-17`).

*Reference: `btc-policy-9y5.5`.*

### DEF-19 — The ceremony directory's parent namespace was substitutable — *measured*

The staging root and the sealed set were owner-only, but the directory that contained them was
created at the operator's umask, so a local group member could replace the staging root
mid-ceremony or the sealed set afterwards; `independence.txt` is read back from that namespace
verbatim.

**Prohibition** — the ceremony MUST validate the parent namespace and refuse a shared one
(`MAN-40`); tightening the mode on the create call is not a fix, because creation succeeds
silently on an existing directory.

*Reference: `btc-policy-b8z`.*

## Ordering and preflight

### DEF-20 — The chain preflight ran under the sign lock

Under-lock chain I/O delayed Lockdown at `T` by the backend's timeout.

**Prohibition** — the preflight runs between the commit hold and the registration hold, outside
every lock (`SPN-20`, `SPN-21`).

*Reference: `btc-policy-9y5.3` round 2; `vault-node` `prefetch_spend_escape_prevouts`.*

### DEF-21 — The wallet birthday could be imported from another branch

A reorg landing between the cold scan and the wallet import could import a birthday proven on an
abandoned fork, leaving an output permanently unwatched and inflating apparent coverage.

**Prohibition** — the import MUST be bracketed by re-proving the settled block, and the walk
above it MUST end at the scan anchor (`WTC-7`).

*Reference: `btc-policy-hn8` review; `vault-node` `chain::import_vault_descriptors`.*
