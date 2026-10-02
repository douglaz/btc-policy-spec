# 11 — State and persistence

What a node holds, where, and what survives what. The short version: nothing survives. Every
mutable state that bears on safety is RAM-only, a reboot leaves a bare machine, and a rebooted
node never rejoins its vault. The two exceptions — a process-generation marker and the Lockdown
latch — live as extended attributes on a tmpfs inode and have exactly the RAM disk's
durability. This is the model this set specifies; `OPS-62` is the procedure by which the
alternative could replace it, and `F8` the open question.

## Reboot-death

**STO-1** The ENTIRE node deployment MUST run from volatile storage — the operating system as
provisioned, the binary, the configuration and all runtime state — so that a reboot leaves a
bare machine with no key, no configuration, no attempt budget, no Lockdown latch, no schedule,
and no way to ask for a preimage. A node therefore starts exactly once in its life (`MAN-36`).
A dead node never rejoins: reprovisioning with the same key and manifest is the resurrection
`ADR-0007` rejects, and a new key is not in the immutable manifest. Restoring capacity means
rotating to a successor vault.

**STO-2** Reboot-death is load-bearing for five separate security states, each of which would
otherwise need to be durable, monotonic and rollback-resistant before a restart could be
supported: the Lockdown latch; the duress arm state and its `T`; the PIN attempt budget; the
Hot-budget velocity window; and the process-generation and channel-replay state. A design that
persists any one of them without the others reopens a theft or brute-force path (`F9`).

**STO-3** At startup a node MUST verify that the filesystem holding its configuration and key
inode is tmpfs or ramfs, and MUST refuse to start otherwise unless an explicit
allow-durable-storage override is set, in which case it MUST print one warning; a failure to
read the filesystem type is treated as non-volatile. The check reads the filesystem of the
already-open configuration descriptor, which is held for the process lifetime so that symlinks
and hardlinks resolve to one inode. *(This is an assumption enforced by a warning, not by the
platform — `SEC-44`.)*

## The two extended attributes

**STO-4** A node MUST record two lifecycle markers as user extended attributes on the
configuration inode, with names in the `btc-policy` namespace and version-suffixed:

- the **process-generation marker**, written with create-only semantics at the serving
  boundary — after the listener is bound, before the first connection is accepted — so that a
  transient bind failure cannot permanently brick the key while no request can arm the node
  before the marker exists. A second process on the same inode fails the create and MUST refuse
  to start: a signing key whose RAM-only armed and candidate state may have died MUST NOT be
  reloaded. The marker records only "this key generation has run", never whether duress
  occurred;
- the **Lockdown latch**, created EMPTY with create-only semantics at load — proving the
  filesystem can take the later write, with a concurrent first start re-reading the winner's
  value — and written non-empty by the Lockdown transition, then synced, BEFORE the in-RAM latch
  is set, so a crash after the write restarts locked. Absent means fresh; present-and-empty
  means writable and not locked; present-and-non-empty means locked, and is adopted at load. A
  persistence failure never prevents the in-RAM latch.

The filesystem MUST support user extended attributes; on Linux that is tmpfs from kernel 6.6,
and a node MUST refuse to start on one that does not, rather than run unable to lock down.

**STO-5** Both attributes have the config inode's durability and vanish with it on
reboot-death, which is strictly stronger than any persisted lockdown. There is no durable
lockdown flag on disk, no `/unseal`, and no reset.

## What each store holds

**STO-6** Under the **sign lock** (`DOM-20`): the replay log with matching keys owned by `SPN-23`, pruned at
commitment expiry; the coordinator nonce log with its high-water and Carrier deadlines
(`SPN-11`); the pending log of hot-class Holds (`SPN-30`); the PIN attempt budget (`MAN-23`);
the in-flight spend marker (`SPN-31`). There is no refresh log: a coin's refresh age is read from
the chain (`SPN-46`, `ADR-0019`). The lock is a plain mutex with no fairness; `SPN-20` and
`DUR-15` state what that costs.

**STO-7** Under the **channel store lock** (`DOM-21`): the candidate registry (`SPN-36`), bounded
by `max_active_candidates` and `max_candidate_store_bytes` with the whole growth reserved at
registration; the Armed overlay (`DUR-10`); the arm intents and Carrier memos (`NCH-32`); the
Hot-budget ledger of at most 4 096 reservations (`POL-16`); and the ingress guards — the
freshness high-water, the seen envelope nonces keyed `(sender, nonce)` and retained by their own
timestamps for 300 seconds, and the per-peer quota deques (`NCH-13`).

**STO-8** Independently of both locks, and never taken by `/healthz`: the alert queue
(`WTC-20`); the vault-authorized txid set (`SPN-33`); the vault-unspent cache and its anchor
(`WTC-5`); the watchtower cursor, owned by its driver task (`WTC-13`); the Lockdown latch, the
deadline heartbeat, the generation flag and the wallet-serving flag as atomics (`API-19`).

**STO-9** Lock order MUST be sign lock, then store lock, wherever both are held; the fire pass's
release loop holds the sign lock across nested store acquisitions and that ordering is
safety-critical (`DUR-9`) and MUST be moved intact, never restructured. The boundary between
the synchronous core and the async shell is two rules, not one: (1) a lock that is not
await-aware MUST NOT be held across an await — in a language whose lock guards are not
sendable across await points the compiler enforces this, except for the runtime's root future;
(2) such a lock MUST NOT be acquired on an async runtime worker at all — no language enforces
this, so every driver pass, the `/events` alert-queue read and the outbox propagation reached
from `/sign` and `/channel` run their lock touches inside dedicated blocking sections. One
named exception: the startup vault-unspent warm (`STO-14`) locks on the root future for a
multi-second scan, harmless only because it runs before the listener binds, and it MUST NOT be
extended past the serving boundary. An implementation SHOULD carry a debug-only assertion that
rule (2) holds, via a thread-local marker set by every blocking-pool spawn, because no runtime
API distinguishes a worker from a pool thread. The state locks MUST NOT be replaced with
await-aware locks, which would delete the compile-time tripwire for rule (1), and the chain RPC
stays synchronous. Whether the Lockdown latch's extended-attribute write on the post-await
poison path counts as a violation is `F47`.

**STO-10** Every lock a critical section holds MUST be poison-aware: a panic inside one poisons
it, the poison is read as a flag without acquiring, and the node then forces the Lockdown latch
through `DUR-9`'s lock-free path and stops its driver passes. The one deliberate exception is
the Carrier retirement that runs during unwinding (`NCH-40`), which tolerates poison because a
double panic would abort the process and leave the node dead but unlatched.

## Secrets in memory

**STO-11** The PIN, the coordinator-request preimage that contains it, the node preimage, the
signing and channel secrets, the Carrier KDF output and matrix, the padded request payload, and
every request body buffer MUST be zeroized on drop, MUST be redacted from any debug rendering,
and MUST never appear in a log line, trace, metric, crash dump, alert, replay entry or disk
write. Buffers that carry a secret MUST be allocated at their final size before the secret is
copied in, so no reallocation leaves a copy behind. The reference implementation asserts the
no-reallocation property in debug builds.

**STO-12** No fast digest, MAC, full signature or retained request body MAY exist that would let
later process-memory capture cheaply test the plaintext PIN (`NCH-31`). The Carrier identity
is memory-hard for that reason.

## Drivers

**STO-13** A node MUST run these background loops, all of which die with the process:

| loop | cadence | reads the backend | resets its ticker from pass completion |
|---|---|---|---|
| Lockdown deadline driver (`DUR-7`) | 1 s, absolute, first tick immediate | never | no — never reset |
| fire pass (`SPN-39`, `DUR-21`) | 1 s | yes | yes |
| watchtower scan (`WTC-17`) | 10 s, first pass immediate | yes | yes |
| vault-unspent cache refresh (`WTC-6`) | 10 s | yes | yes |

The **Lockdown deadline driver MUST run on a dedicated operating-system thread** that is not
part of the async runtime or its blocking pool, so the deadline tick shares no worker with the
arm-dependent fire pass; a failure to start that thread MUST be fatal before the node serves,
because a node serving with no deadline driver is the worst available silent failure. The move
delivers isolation, not latency: it does not make Lockdown at `T` a bounded-delay claim
(`DUR-15`). The driver publishes the heartbeat BEFORE reading the overlay, returns without
publishing once the node is both locked down and poisoned, and keeps a clock seam so a test
can drive it deterministically and terminate it — an armed node and an idle node MUST publish
the same heartbeat bucket on the same tick (`API-20`). The fire pass stays on the runtime, its
lock touches inside blocking sections. Each backend-reading pass runs on a blocking thread with
a panic net that forces fail-closed Lockdown if a critical lock is poisoned.

**STO-14** Before the drivers start the node MAY warm the vault-unspent cache synchronously with
a cold scan, logging and continuing on failure. This is safe only because reboot-death
guarantees a fresh process holds no armed schedule that the warm could delay.

## What is deliberately not persisted

**STO-15** Not persisted, and MUST NOT be: the replay log (idempotency and audit for the
process lifetime only; a restarted node forgets in-flight commitments, which is acceptable
because the log provides idempotency and not signature security); partial signatures; the
escape transaction bytes; the Armed overlay; the watchtower cursor; the attempt budget; the
Hot-budget ledger; the channel nonce cache. A restart resets the Hold on any pending spend to
"never seen", which is the failing-safe direction; it also loses this node's holder receipts
and its vote in any pending arm, which is why a rebooted node is counted dead and not degraded.
