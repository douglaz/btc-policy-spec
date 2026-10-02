# 10 — Watchtower and chain backend

What a node requires of its Bitcoin backend, how it keeps its view of the vault's coins, how it
detects reorgs, how it reads the one fee signal the sweep uses, and the watchtower every node
runs against its own chain. Every requirement here is per node: nodes share no chain oracle, and
that independence is part of the security claim.

## The backend contract

**WTC-1** Each node MUST run against its OWN chain backend and MUST fail closed when it cannot
read the chain. Every honest node reaches the same verdict from the same chain state (`OVR-9`),
which is only possible because every fact a node acts on comes from consensus, never from its
mempool's opinion or a peer's.

**WTC-2** The backend MUST provide these operations, each with the stated contract. The
reference backend is Bitcoin Core over JSON-RPC and the table names the calls it uses; another
backend interoperates if it provides the same contract.

| operation | contract | reference RPC |
|---|---|---|
| broadcast | push a fully signed transaction; malformed input is an error, never a panic | `sendrawtransaction` |
| tip height | the active chain's height | `getblockcount` |
| block hash at height | the ACTIVE chain's hash, or none if no block occupies it (Core error −8 ⇒ none) | `getblockhash` |
| block median feerate | the **weight-weighted** 50th-percentile feerate of that block in sat/vB, by the algorithm below, or none (Core −8 ⇒ none) | `getblockstats` `feerate_percentiles[2]` |
| spends of scripts in a height range | every spend of the watched scripts, with witness and prevout, plus the proven `(height, hash)` chain (`WTC-12`) | `getblockhash` + `getblock` verbosity 3 |
| prevout | an unspent output INCLUDING this node's mempool, with a confirmed flag; batched | `gettxout` with `include_mempool = true` |
| vault unspent | confirmed vault outputs plus unconfirmed outputs whose parent is vault-authorized (`WTC-10`) | cache + `gettxout` + `getrawmempool` |
| mempool transaction | raw bytes iff resident in this node's mempool; batched "first resident of these" from one snapshot | `getrawmempool`, `getrawtransaction` |
| transaction confirmed | in the active chain (Core −5 ⇒ false) | `getrawtransaction` verbose |
| package acceptance | mempool-acceptance test of a package | `testmempoolaccept` |
| confirming block of a transaction | the ACTIVE chain's `(height, hash)` in which the transaction confirmed, or none if unconfirmed or not on the active chain | `getrawtransaction` verbose (`blockhash`) + `getblockheader` (active check) |
| block median-time-past | the BIP113 median-time-past of the active block at a hash, or none if not active; what `SPN-46` reads for both the tip and a coin's confirming block | `getblockheader` `mediantime` |

The **block median feerate** MUST be computed by exactly this algorithm, because "the
50th-percentile feerate" alone names three different functions of the same block — a
transaction-count median, a weight-weighted median, and a median over `⌊fee / vsize⌋` scores —
whose answers on a block of many small high-feerate payments beside a few large consolidations
differ by orders of magnitude, far past the five-unit quantisation `DUR-30` applies afterwards.
Two honest nodes on backends that disagree here select different rungs. Over the **non-coinbase**
transactions of the block:

1. score each transaction `⌊fee_sat × 4 / weight_wu⌋`, integer division, where `weight_wu` is its
   BIP141 weight — never `⌊fee / vsize⌋`, which rounds the divisor up first and therefore reads
   **lower** or equal (fee 503 over weight 401 scores 5 here and 4 that way);
2. let `total_weight` be the sum of those same transactions' weights — the coinbase is excluded
   from the denominator as well as from the population;
3. sort by score ascending and accumulate weight in that order;
4. the median is the score of the first transaction at which `2 × cumulative_weight ≥
   total_weight`; no interpolation between neighbouring scores;
5. an empty population — a coinbase-only block — is `0`, which `DUR-30` reads as no pressure.

A backend other than Bitcoin Core interoperates only if it reproduces these five steps; the
reference RPC column names where Core implements them, and the column is a pointer, not the
contract.

**WTC-3** At startup, before any bind and before the generation claim, a node MUST verify in this
order: the sealed network is supported; the backend's reported chain equals the sealed
`network`, and on signet its `signet_challenge` equals the default public signet's
(case-insensitively; a custom signet, a missing challenge, or a challenge on a non-signet chain
is refused); the backend is not in initial block download; the transaction index is present and
synced; and the backend's incremental relay fee is at most 1 000 sat/kvB. Chain identity comes
FIRST because a backend caught up on the wrong chain answers every later query completely and
wrongly. Known residuals: two regtest instances are indistinguishable, a fork truthfully
reporting `main` passes, and the check runs once. With the other backend checks a node MUST
probe whether the backend has a usable wallet RPC — wallet support compiled in, not
`-disablewallet`, a writable wallet directory — and print one loud warning at boot when it does
not, since the fallback of `WTC-6` is complete and verdict-identical but roughly ten seconds
per scan, serialised process-wide by the backend; the state is also published on `/healthz`
(`API-19`). The probe warns and does not refuse: a slow node is a live node.

**WTC-4** Every backend call MUST be bounded by a timeout (60 seconds; 600 for wallet build)
and MUST be made outside every node lock (`SPN-20`).

## The vault's coins

**WTC-5** A node MUST maintain a **vault-unspent cache** of the confirmed outputs paying the vault
script, anchored to the `(height, hash)` it was computed at, and MUST serve every fire-time read
from that cache: the coverage denominator (`DUR-22`) MUST refuse rather than scan the UTXO set
on the combine path, and MUST refuse if the cache's anchor is not the current tip.

**WTC-6** The cache MUST be served, in order of preference, by: a node-owned **watch-only
descriptor wallet** read with one unspent listing and a since-block reconciliation, discarded
unless the tip captured before the listing is still the tip when the reconciliation ends, and
re-proving after the read that a completion marker's anchor is still active (`WTC-8`); a
bounded delta walk of at most 32 blocks from a cached anchor whose block is still active; or a
cold **full UTXO-set scan** for the vault script, published to the cache BEFORE the slow wallet
build that may follow it on a background thread. Measured on signet the cold scan costs about
ten seconds against 72 million outputs and Bitcoin Core serialises it process-wide, which is why
it is the fallback and not the steady state (`DEF-9`). The delta walk covers every height above
the cache's anchor through the lesser of the tip captured when the walk starts and 32 blocks
above that anchor. A walk that covers less is discarded whole, as is one that fails any proof
(`WTC-12`), and the refresh falls through to the cold scan. A walk that completes becomes the
cache even where it ends below the tip, and any later delta walk starts from that cache; a cache
whose anchor is not the current tip is refused at fire time (`WTC-5`). While the repair latch is
set or a build or repair attempt is in progress, `WTC-9` restricts this order.

**WTC-7** The wallet MUST be created with private keys disabled, blank, descriptor-based, not
loaded on startup, named from a hash of the node's identity and the watched script set, and
imported with the same `raw(<script>)` descriptors the cold scan uses. Let the **scan anchor**
A be the block the cold scan read at, and the **settled block** S the block the **settled
depth** — 10 blocks — below it, or genesis when A's height is below the settled depth. The cold
scan and a walk of the blocks above S proven to end at A itself (`WTC-12`) form one result, and
a walk that fails refuses the import. The import's **birthday** is the lowest height among S
and the blocks that created every output the scan found live or the walk found spent, so the
import covers every output a reorg that leaves S active can make live; a backend that takes a
birthday as a time MUST start its rescan no later than that height's block. The import MUST be
bracketed by re-proving S is still active, before the descriptors are imported and again before
the marker is (`WTC-8`); if it moved, the import is refused rather than importing a birthday
from another branch, which would leave an output permanently unwatched and inflate apparent
coverage. A repair never starts later than the wallet already covers: when its birthday is not
below the lowest birthday a held marker carries, it imports only a new marker, and otherwise it
re-imports the descriptors from its own birthday.

**WTC-8** A **completion marker** — an inert `raw(OP_RETURN …)` descriptor carrying the owner
hash, the anchor height and hash of the import's settled block, and the import's birthday
(`WTC-7`) — MUST be imported once the descriptors are, and the wallet is usable only when it
holds every vault descriptor, only markers otherwise, and at least one marker whose anchor is
still active. Any such marker vouches for the wallet, because a repair never starts later than
the wallet already covers and so never narrows what an earlier marker's import covered. A
wallet with private keys enabled is refused.

**WTC-9** If the wallet holds a completion marker and none it holds has an anchor on the active
chain the node MUST latch a repair, keep the wallet out of use until a cold scan and re-import have
rebuilt it, and re-prove after every read that a marker's anchor is still active, so a reorg deep
enough to unseat the last of them discards the result instead of installing an understated
denominator; a shallower reorg landing during a read is caught by the read's own tip bracket
(`WTC-6`), and one landing between reads is already reflected in the next read, since the backend's
wallet follows the active chain. From the latch setting until a cold scan has replaced the cache,
every refresh with no attempt in progress starts a repair attempt from a cold scan, whatever cache
it holds, the scan replacing the cache before the re-import begins (`WTC-6`); thereafter, while the
latch holds, the cache is advanced by delta walks or their cold-scan fallback (`WTC-6`), and a
wallet read never replaces it. At most one attempt, whether a repair or a first build, is in
progress at a time. An attempt ends however it stops, whether or not its re-import began — a cold
scan or wallet call that fails or overruns its `WTC-4` timeout ends it as a failure — and one that
ends without rebuilding the wallet leaves any latch set; the next attempt starts only from a cold
scan `WTC-6` itself reaches with none in progress, and starts no scan of its own. A wallet holding
no completion marker is not latched, `WTC-8` already keeping it out of use: its first build, and any
retry after a failed one, starts the same way, from a cold scan `WTC-6` reaches with no attempt in
progress. A failed build or repair is therefore not retried while delta walks succeed; the cache
does not depend on the wallet.

**WTC-10** The **vault unspent** read the sweep uses MUST take one consistent snapshot: capture
the mempool txid set and its sequence number; read confirmed candidates from the cache at the
current tip; re-validate each with a batched prevout read keeping only watched, confirmed
outputs; add every output paying a watched script from mempool transactions in the authorized
set whose prevout is unconfirmed; then require the tip and the mempool sequence to be unchanged,
retrying once and failing closed otherwise. Unconfirmed external deposits are excluded by
construction.

## Reorgs

**WTC-11** A node MUST detect a reorg at every point where it binds a result to a chain: a
block hash at a height that no longer matches; a header height accepted only if that block is
still active at it; a delta walk whose block's `previousblockhash` is not the cached parent; a
wallet that holds completion markers none of whose anchors is still active (`WTC-8`).

**WTC-12** A scan of a height range MUST prove the chain it scanned with three checks, any
failure discarding the whole result: the first block's `previousblockhash` equals the cursor's
expected parent (closing a fork below the range that rebuilt taller); each later block's
`previousblockhash` equals the previous scanned hash (breaking a mixed-fork straddle); and after
the loop the hash at the last height still equals the last scanned hash (closing a scan that ran
entirely on an abandoned fork, including one that returned to the captured tip). Coinbase inputs
are skipped; every other input MUST carry a prevout, and a missing one is an error, never a
silent negative.

**WTC-13** The watchtower **cursor** MUST hold the `(height, hash)` anchors of the top of its
scanned range — at most 101, contiguous — and its next height, in RAM only; a process restart
scans from genesis. Before each pass the cursor MUST be reconciled: one hash read at the newest
anchor detects any in-window reorg; on mismatch the cursor walks newest to oldest for the
highest still-active anchor, drops everything above it, and re-scans from there with a loud
message; if no anchor matches — a reorg deeper than 100 blocks — it clears and re-scans from
genesis rather than wedging or silently advancing.

**WTC-14** A pass whose tip is below the newest anchor MUST return without advancing; a pass
whose captured tip's hash is no longer the active hash at that height when the scan ends MUST
discard its candidate cursor — a block arriving on top during the scan is not such a change,
and is the next pass's range; a pass that errors keeps the unadvanced cursor so the same range
is retried and no block is skipped; a pass that panics, anywhere in it and the tip comparison
included, resets the cursor to genesis. The alert queue's dedup makes every redundant re-scan
harmless.

## The fee signal

**WTC-15** The only fee reading the federation acts on is `DUR-30`'s bump target: the
50th-percentile feerate of the block at `tip − (tip mod 6)`, as the backend reports it for that
block's transactions excluding the coinbase, quantised down to a multiple of 5 sat/vB. A node
MUST NOT read its mempool minimum fee, a fee estimator, or arrival order for any decision the
federation must agree on. An error or absent reading means no pressure.

**WTC-16** The coordinator's composer (`CHN-20`) MAY use a fee estimator for the RATE it
composes at, because composition is the coordinator's and the user signs the result; the
reference uses the larger of the backend's conservative six-block estimate and the mempool's
minimum and incremental-relay floors, in sat/vB rounded up. That rate never enters a node
decision.

## Watchtower

**WTC-17** Every node MUST scan its own chain every 10 seconds, first pass immediate, for every
spend of the vault's script, and classify each spend with this precedence: a witness whose
branch selector is the empty push (`CHN-9`) is a `RECOVERY_PATH_SPEND`, even if the txid is in
the authorized set; otherwise a txid NOT in the node's vault-authorized set is an
`UNRECOGNIZED_SPEND`; otherwise no alert. The recovery exit is never swallowed, because stolen
recovery keys are otherwise silent and that detection is the watchtower's most important job.

**WTC-18** Recognition is by **validation and acceptance**, never by co-signing and never by
evaluation. Only `t` of `n` nodes sign a legitimate spend, so "I did not sign it" false-alarms on
`n − t` honest nodes; and a spend a node REFUSED was evaluated, so "I evaluated it" would let an
attacker fanning a theft to honest nodes suppress its own alert. The authorized set is the txids
of every spend, Escape, rung, refresh and claw-back this node accepted (`SPN-33`). A legitimate spend is
accepted by all `n` and alerts nowhere; a theft the honest nodes refuse is in nobody's set and
alerts everywhere.

**WTC-19** Recovery-branch identification MUST read the witness, not the script: both branches
share one scriptPubKey. A witness with fewer than two elements reads as non-recovery, which is
the safe default because it still alerts as unrecognised when unauthorized.

**WTC-20** The **alert queue** is RAM-only, capped at 1 024 events with the oldest evicted first,
sequence-numbered from 1, and served by `API-17`. Watchtower alerts are deduplicated on
`spend_txid:outpoint`: a re-scan of a retained spend never re-enqueues, and an evicted entry's
key is released so a later scan may re-alert it. Freshness diagnostics are keyed per peer and
coalesced by `NCH-16`. An alert carries `kind`, `spend_txid`, `outpoint` as `txid:vout`, and
`script` as lowercase hex.

**WTC-21** The watchtower MUST snapshot the authorized set and release its lock BEFORE the slow
chain read, so a concurrent ingress is never blocked on chain I/O, and MUST take the alert lock
only after the scan has been proven (`WTC-12`).

**WTC-22** Alert delivery is coordinator-pull (`ADR-0002`); nodes never push. The operator
program's consumption of the queue is `OPR-60`. Watchtower duty continues during Lockdown.

## Packages and broadcast

**WTC-23** A package for acceptance testing MUST be the candidate transaction alone: its
unconfirmed ancestors are already in this node's mempool and Bitcoin Core's package policy
rejects a package that re-lists present ancestry, while a singleton acceptance test still
evaluates the candidate against its full in-mempool ancestor set.

**WTC-24** Before assembling, a node MUST validate the candidate's ancestry: for a candidate,
every prevout MUST exist (unknown or spent is an error), and an unconfirmed parent MUST be
resident in the mempool AND in the vault-authorized set — an unconfirmed external deposit is
excluded because its parent can be replaced out from under the spend; for a candidate that
replaces a mempool-resident vault-authorized transaction (`WTC-25`) — a higher rung over a
resident rung, a refresh over a resident refresh, or a claw-back over a resident claw-back — a
parent absent from the mempool is
confirmed, and the resident's own inputs are read as unspent for the replacement. Diamond ancestry is
deduplicated, and more than 24 distinct ancestors is an error, one below Bitcoin Core's default
ancestor limit. Every parent MUST be resolved against ONE mempool snapshot — a batched
membership read — and never by one full mempool query per parent: with a resident rung every
one-second fire tick re-runs this validation, so an escape sweeping `K` coins would otherwise
pay `K` full mempool pulls per tick, worst under exactly the congestion that makes the combine
window tightest, and `N` successive snapshots are also less coherent than one. A parent absent
from the snapshot still means confirmed.

**WTC-25** A replacement — a higher rung over a resident lower rung, a refresh over a resident
refresh of the same coins, or a claw-back over a resident claw-back of the same coins
(`CHN-35`) — MUST spend exactly the same ordered outpoints as the
resident transaction, and its ancestry MUST be walked over the resident transaction with inputs
treated as spent, because a prevout read including the mempool hides what the resident already
spends. The resident MUST be in this node's vault-authorized set (`WTC-18`); a resident the node
never accepted is not something it replaces. Without this clause a refresh could never be
fee-bumped: its first attempt, resident, would make its own inputs read as spent on every node.

**WTC-26** Package acceptance MUST require every entry allowed, tolerating exactly one rejection
reason — `txn-already-in-mempool` — because a vault-authorized unconfirmed parent already present
is what the package needs. Any other rejection is a verdict the sweep treats as inadmissible for
this pass (`DUR-32`).

**WTC-27** Broadcast MUST deserialise locally first, so malformed bytes are a clean error, then
send the canonical serialisation. Idempotency is not the backend's: the fire path recognises an
already-broadcast or already-mined candidate through the mempool-resident and confirmed reads
before it sends (`SPN-39`).

## The composer's view of the chain

**WTC-28** The coordinator's inventory of spendable coins is every confirmed, mature (at least
100 confirmations for a coinbase), mempool-unspent output paying the vault script at one
consistent tip, in canonical outpoint order. A scanned coin absent from the UTXO set at the same
tip MUST refuse the WHOLE inventory as unavailable — never silently omit it, never diagnose it as
"wait for confirmation" — because composing over the remainder produces an under-covered Escape
and a coin mempool-spent by a prior vault spend is the common case. `OPR-39` keeps composition
confirmed-only in this revision; composing over vault-authorized unconfirmed value is `F2`. Up
to three attempts are made; only observed
tip movement makes an attempt retryable.

**WTC-29** The composer MUST bound what it retains: the projected size of retained full parent
transactions at most 64 MiB, refused before allocation; each composed shape's maximum finalized
vsize at most 100 000 vB. The coordinator's HTTP client for the backend MUST create one monotonic
deadline before connecting (60 seconds; 600 for the full scan), cap the entire raw response
(16 MiB), frame strictly at end of stream, and hold the response in one zeroizing allocation
that never grows (`DEF-8`). That cap bounds the wire, not the heap a decoded reply costs
(`F1`).

**WTC-30** The composer MUST verify the backend's chain identity exactly as a node does
(`WTC-3`) before it reads anything, refuse during initial block download, and read the backend's
authentication cookie per call from an owner-only file with the credential appearing in no
diagnostic.
