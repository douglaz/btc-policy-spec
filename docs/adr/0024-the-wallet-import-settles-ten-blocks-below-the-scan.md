# The wallet import settles ten blocks below the scan

Status: accepted 2026-09-29. Specification-repository decision, closing the reorg questions
`bps-8s0.11.13` collected. Settled by the Operator over four consultation rounds on
2026-09-27..29, with a Bitcoin Core regtest run as the evidence for what a real wallet does across
a reorg. Amends `WTC-6`, `WTC-7`, `WTC-8`, `WTC-9`, `WTC-11` and `WTC-14`, and records the
divergence the reference implementation now carries. Extended on 2026-10-02 by decisions 9 to 11,
each put to a four-adviser consultation and settled by the specification owner; they amend `WTC-6`,
`WTC-9` and `WTC-11` again and close `bps-8s0.11.22`, `bps-8s0.11.23` and `bps-8s0.11.24`.

`DEF-9` made the watch-only descriptor wallet the steady state and the cold full UTXO-set scan the
cold-start and repair fallback. `WTC-7` then had to say what the wallet is imported from, and it
said: a birthday equal to the block time of the oldest live vault output the cold scan found,
bracketed by re-proving the cold scan's own anchor. Three things were wrong with that, and a
fourth sentence elsewhere was ambiguous enough that two readers implemented it two ways.

**The birthday was computed from live outputs only.** An output the scan found *spent* contributed
nothing, so a reorg that reversed the spend resurrected an output created below that import's
birthday. On its own that was not yet an understated denominator: the marker anchored at the scan
anchor, a reorg that reverses a spend at or below it replaces the anchor's block too, and
a wallet left with no active marker was out of use until a repair's cold scan, which finds the
output live, had rebuilt it. The harm needed the third defect below as well. In a wallet an older
marker kept in use, whose floor a later repair had raised, the resurrected output sat below the
floor; the wallet — scanning only from its birthday up — never saw it, and coverage (`DUR-22`)
divided by an understated denominator. That is `DEF-21`'s failure mode reached by a different
route: not a birthday from an abandoned fork, but a birthday from the *right* fork that the next
reorg made too high.

**The anchor was the scan tip, so every shallow reorg was a repair.** A cold scan reads at the tip.
Anchoring the completion marker there means a reorg that orphans the scan's own tip block unseats
it, and a wallet holding no older marker whose anchor is still active then latches a repair — one
cold scan, about ten seconds against signet's 72-million-output set and serialised process-wide by
Core, per attempt. On a chain that reorgs a block a day such a wallet is in repair a noticeable
fraction of the time, for a reorg that changed nothing the wallet cares about.

**A repair could start later than the wallet already covered.** A repair scans at the current tip,
so its birthday is at least as high as the tip's own settled point. If it replaced the descriptors'
timestamp and nothing kept the old one, the wallet's floor rose. Every output between the old floor
and the new one was then unwatched, permanently.

**And `WTC-14`'s tip test had two readings.** "A pass whose captured tip hash changes during the
scan MUST discard its candidate cursor" can mean *the hash at the captured height changed* or *the
chain tip is no longer the captured tip*. The second reading discards a pass any time a block
arrives on top while the loop runs — which is every pass of a `WTC-13` genesis re-scan on mainnet,
so the cursor can never finish one. The reference implementation took the first reading. The formal
model took the second: at the base commit of this amendment its pass compared the tip hash read
after the loop against the captured one.

## Decision

**1. The settled depth is 10 blocks, and it is a cost setting, not a finality assumption.** Let the
scan anchor `A` be the block the cold scan read at and the settled block `S` the block 10 below it,
or genesis on a shorter chain. A reorg no deeper than 10 leaves that import's completion marker in
force and costs no repair; a deeper one can unseat it, and a repair latches only when no held
marker's anchor is still active (`WTC-9`). Ten is chosen against the repair's cost, not against any
claim about when Bitcoin is final: shallower means more repairs, deeper means a wider window the
birthday has to cover. It is held to its declaration —
`BtcPolicy.VaultUnspent.settledDepth` — by the copies gate.

This is **not** `WTC-13`'s cursor window. `WTC-13`: "if no anchor matches — a reorg deeper than 100
blocks — it clears and re-scans from genesis rather than wedging or silently advancing." That window
bounds how far the watchtower cursor can rewind before it gives up and re-scans the whole chain; it
is about *finding spends* and it costs a re-scan. The settled depth bounds how far a reorg can reach
before a *wallet import* stops vouching for itself; it is about *counting coins* and it costs a cold
scan and a re-import. Two windows, two costs, two numbers, and they move independently.

**2. The cold scan and a walk of `(S, A]` are one result.** The scan yields what is live at `A`; a
`WTC-12`-proven walk of the blocks above `S`, ending at `A` itself, yields the spends inside the
settled depth with the heights of the blocks that created the outputs they spent. A walk that fails
any of `WTC-12`'s checks refuses the import; there is no half-import.

**3. The birthday is the lowest height among `S` and every one of those creating blocks.** That is
exactly the set of outputs a reorg which leaves `S` active can make live again: an output created
below `S` and spent inside the settled depth is the one case the old rule missed, and the walk is
what finds it. Where the backend takes a birthday as a time rather than a height, it must start its
rescan no later than that height's block.

**4. The completion marker carries `S` and the import's birthday, and any held marker vouches for
the wallet.** `WTC-8` already required a marker whose anchor was active; the marker now anchors at
`S` instead of at the scan tip, and carries the birthday of the import that left it. **Any** held
marker whose anchor is active satisfies `WTC-8`'s marker clause — "at least one marker whose anchor
is still active" — which is one of the conditions `WTC-8` sets for the wallet to be usable, not the
whole of them. `WTC-9` latches a repair only when no held marker's anchor is active. `WTC-9`: "a shallower reorg landing during a read is caught by the read's own tip
bracket" — `WTC-6`'s read is discarded unless the tip captured before the listing is still the tip
when the reconciliation ends, so a reorg mid-read is caught there and needs no latch.

Trusting any marker is sound only because of decision 5.

**5. A repair never starts later than the wallet already covers.** `WTC-7`: "A repair never starts
later than the wallet already covers". When a repair's birthday is not below the lowest birthday a
held marker carries, it imports **only** a new marker and leaves the descriptors alone; otherwise it
re-imports the descriptors from its own birthday. So the floor the wallet scans from never rises,
and an older marker can be trusted without knowing which import left it.

**6. The import is bracketed at two points: before the descriptors and again before the marker.**
Re-proving `S` once left a window between the two writes in which a deep reorg could land. The
marker written after it is not a coverage hole: `WTC-8` lets a marker vouch only while its anchor
is active, and one anchored at an unseated `S` vouches for nothing. It is an import that reports
completion without having completed — a repair would count the wallet rebuilt, and clear its latch
(`WTC-9`), on a marker that was already dead when it was written. Both writes are now bracketed,
and a failure at either refuses the import whole, so an import leaves a marker whose settled block
was active when it was written or leaves none. `DEF-21`'s prohibition is restated against the
settled block rather than the scan anchor.

**7. `WTC-14`'s tip test compares the active hash at the captured tip's height.** `WTC-14`: "a block
arriving on top during the scan is not such a change, and is the next pass's range". A pass that is
overtaken keeps its candidate cursor; a pass whose captured height was *replaced* discards it. And a
pass that panics — "anywhere in it and the tip comparison included" — still resets the cursor to
genesis, which is the clause the ambiguity was hiding behind.

**8. `WTC-6`'s delta walk commits wherever it completes.** `WTC-6`: "A walk that completes
becomes the cache even where it ends below the tip, and any later delta walk starts from that
cache". A walk is complete only when it covers every height through the lesser of the tip captured
when it starts and 32 blocks above its anchor; one that covers less, or fails any proof, is
discarded whole and the refresh falls through to the cold scan. The range is therefore fixed when
the walk starts, and a complete walk ends below that tip in one case only: the cache was more than
32 blocks behind it. Throwing that proven walk away to run a cold scan instead pays the expensive
source for the cheap source's success, where committing it lets each refresh
carry the cache 32 blocks further. The partial cache is still refused at fire time, by `WTC-5`,
because its anchor is not the current tip.
(Rationale corrected 2026-10-01: it had rested on a tip that moved while the walk ran, which the
full-range rule makes beside the point — a block arriving during the walk is outside the range the
walk was given and is the next refresh's.)

**9. The repair latch is for a wallet that was built, and a failed attempt starts no scan of its
own (2026-10-02).** `WTC-9`: "If the wallet holds a completion marker and none it holds has an
anchor on the active chain the node MUST latch a repair". Read without its first clause the
condition held, with nothing to check, of a wallet that holds no marker — the wallet before its
first build, and the one a first build that failed leaves — so a first build ran as a repair.
`WTC-9` now says otherwise: "A wallet holding no completion marker is not latched, `WTC-8` already
keeping it out of use". `BtcPolicy.VaultUnspent.unbuilt_wallet_never_latches` is the rule in the
model.

Under the latch, the node scans of its own until one cold scan has replaced the cache, and no
further. `WTC-9`: "From the latch setting until a cold scan has replaced the cache, every refresh
with no attempt in progress starts a repair attempt from a cold scan, whatever cache it holds".
The rule is a state, not a count: worded as the first refresh after the latch sets, it let a
refresh that followed a first scan which failed to publish walk on from the cache held before the
latch, which a wallet read may have left, and a consultation found it. After that scan the cache
is advanced without the wallet, and `WTC-9`: "the next attempt starts only from a cold scan
`WTC-6` itself reaches with none in progress, and starts no scan of its own". A wallet holding no
marker has its first build, and every retry of it, started the same way. The owner took the
consequence with the rule, and `WTC-9` states it: "A failed build or repair is therefore not
retried while delta walks succeed; the cache does not depend on the wallet."
`BtcPolicy.VaultUnspent.latched_unscanned_serves_cold`,
`BtcPolicy.VaultUnspent.failed_attempt_starts_no_scan`,
`BtcPolicy.VaultUnspent.attempt_starts_only_at_cold_scan` and
`BtcPolicy.Exhibits.VaultUnspentCache.failed_attempt_not_retried_while_walks_succeed` are the four
halves.

**10. A delta walk's end is held to the chain after the walk and to no other (2026-10-02).**
`WTC-12`: "after the loop the hash at the last height still equals the last scanned hash". The
model had also asked that the walk's last block be active on the view captured when the walk
starts, a test no sentence of `WTC-6` states. It is withdrawn. Against the chain as it is after
the walk, `WTC-12`'s check is the rule; the further test only discards a walk read correctly on a
branch the chain moved to between the capture and the read; and a cache the walk leaves anywhere
but the tip is refused at fire time already — `WTC-5`: "MUST refuse if the cache's anchor is not
the current tip". `BtcPolicy.VaultUnspent.delta_commits_walk_on_any_branch` is the rule and
`BtcPolicy.Exhibits.VaultUnspentCache.off_branch_walk_committed` the case.

**11. That a block hash commits to its ancestry is a premise the model states, not something its
state records (2026-10-02).** The re-import is tied to its attempt's cold scan by comparing scan
results, which pins the scan's tip and what was live there
(`BtcPolicy.VaultUnspent.rebuild_is_of_the_attempts_scan`). The rebuild reads the settled block
off the view it is given, and a view in the model is a map from heights to hashes in which nothing
makes a tip fix the blocks beneath it. `BtcPolicy.Chain.Ancestry` is the premise on a pair of
views — each view's tip active in it, and two views that share an active block agreeing at every
height at or below it — taken as a hypothesis where a theorem needs it and never as an axiom.
Under it `BtcPolicy.VaultUnspent.rebuild_reads_the_attempts_settled_block` proves the two settled
blocks equal, and `BtcPolicy.VaultUnspent.mismatched_scan_view_excluded_by_ancestry` keeps the
review's probe as the pair of views the premise excludes. No conforming node is affected either
way: a real hash chain has no such pair.

## The regtest evidence

Bitcoin Core 31.1 (`/Satoshi:31.1.0/`), 2026-09-27, on a private regtest datadir. Four watch-only
descriptor wallets — `raw(<script>)` descriptor, private keys disabled, blank, descriptor-based, not
loaded on startup — were built at an **empty** vault, so every coin the run created arrived after
the build. They differ in what happens to them afterwards: one is kept loaded and never re-imported;
one is never re-imported but unloaded across a Core restart; one is re-imported on the second branch
with a later timestamp **and** marker descriptors; one is re-imported the same way with **no**
markers.

The sequence: a coin confirms on branch X; the first build's anchor block is invalidated, taking the
chain to branch Y; a second coin confirms on Y; two of the wallets are re-imported with a timestamp
taken on Y; Core is stopped and restarted with those wallets unloaded; the chain is returned to X;
the unloaded wallets are reloaded.

What it showed:

- **Core's wallet follows a reorg away and back, for every variant, across a restart.** All four
  wallets listed the Y coin while on Y and the X coin again after the return to X. Nothing in the
  run needed the specification to say anything about re-scanning a wallet after a reorg.
- **A re-import does replace a descriptor's timestamp.** The two re-imported wallets carried the
  later, Y-side timestamp on their vault descriptor afterwards. So a repair that re-imports
  descriptors can raise a per-descriptor floor, which is what decision 5 forbids.
- **The wallet-wide birthtime did not move past a transaction Core had already seen.** Core retains
  wallet transactions across a reorg, and the wallet with markers kept the low birthtime the markers
  carried. In the wallet with no markers the re-import moved the *descriptor's* timestamp to the Y
  value, but its *wallet-wide* birthtime stayed at the build time it was created with, below the X
  coin's own time; back on X that birthtime became the X coin's own time and no higher.

**What the run does not cover**, and the reason decision 5 is a rule rather than an observation: a
coin in a block the wallet never processed, older than a later re-import's timestamp, in a wallet
with no earlier marker keeping the birthtime low. Core had already seen every coin in the run, so
its retention hid the case. The amended `WTC-7` closes it by construction — a repair never starts
later than the wallet already covers — rather than by relying on a backend behaviour the run did not
exercise.

## Alternatives rejected

**Anchor the marker at the scan tip.** The reference implementation's reading, and the smaller
change: no settled depth, no walk of `(S, A]`, and no settled-block floor under the birthday. That
is not the absence of every floor; the word does three jobs here. The scan-anchor floor stays:
`BtcPolicy.VaultUnspent.scanTipBirthday` still takes the birthday down to the lowest of the scan
anchor's height and the creating heights of everything the scan found live, and
`BtcPolicy.VaultUnspent.scanTip_birthday_le_anchor` proves that the marker such an import leaves
carries a birthday at or below its anchor's height. Decision 5's repair floor is the third, and the
guard parameter that isolates this alternative flips the marker anchor alone. Decision 5 is a rule
and not a parameter — `BtcPolicy.VaultUnspent.applyImport` and `BtcPolicy.VaultUnspent.markerOnly`
are unconditional, and the guard parameters are the ones Consequences names — so it stays in
force under either value. The alternative weighed here is that isolated flip, not what the reference
implementation historically carried, which Consequences records under *The reference implementation
diverges and must move in its own repository*.

Rejected on the repair cost. A cold scan reads at the tip, so the marker it leaves is unseated by the
very next block that gets orphaned. In a wallet holding only that marker — what a fresh import and a
cold start leave — no held marker's anchor is then active, which is the case `WTC-9` latches on.
`WTC-9`: "If the wallet holds a completion marker and none it holds has an anchor on the active
chain the node MUST latch a repair, keep the wallet out of use until a cold scan and re-import have
rebuilt it". So the
wallet goes out of use for one cold scan and one re-import, however shallow the reorg was, where the
settled block's marker would have stood through it. That wallet is
`BtcPolicy.VaultUnspent.scanTipWallet`, one marker at the scan anchor `(12, 112)`, and
`BtcPolicy.VaultUnspent.markerAnchor_repairs_with_scanTip` proves of it, against the reorg to `C`,
that the scan anchor is no longer active, that `BtcPolicy.VaultUnspent.usable` is `false` and that
`BtcPolicy.VaultUnspent.observe` is `true` — the wallet out of use and the repair latched. That is
the difference the model's guard-parameter twin turns on; the flip is red in `Exhibits.lean`.

A wallet holding a marker whose anchor the reorg leaves active is the other case, and it is
reachable: an earlier import at a lower scan tip leaves such a marker whenever the reorg does not
reach down to its anchor, `BtcPolicy.VaultUnspent.observe` then latches nothing, and that import's
own birthday already covers what the reorg resurrected. The surviving anchor is what spares the
wallet — not the marker's age, and not how many markers it holds; an earlier marker whose anchor
the reorg does reach is unseated with the rest, and a wallet can hold two and have neither left
standing. Decision 4 above is the whole of the rule. So the cost is what a wallet holding no
surviving marker pays — every wallet at its first import, and every node coming up cold — and that
is ground enough to reject the alternative.

What it does **not** do, while a held marker's anchor is still standing, is leave an output
unwatched. Under this reading a marker's birthday is at most its anchor's height, so an output
created below what the wallet already covers and made live again by a reorg was live at the import
of any marker that reorg leaves standing — an import whose own birthday was therefore floored at or
below that output's creating height. `BtcPolicy.VaultUnspent.scanTip_active_marker_watches_everything`
carries that half, under its own hypotheses — among them that the wallet still holds such a marker,
and the chain assumption recorded two paragraphs below. Decision 5 is what puts the wallet's floor at
the lowest birthday a held marker carries, so strip decision 5 and a later repair can raise the floor
above the output, which is the third defect this amendment corrects rather than anything the anchor
decides.

The other half is the reorg that unseats every held marker, and it is not a hole either, though it
is not free. There the wallet is out of use and the repair runs — the case
`BtcPolicy.VaultUnspent.markerAnchor_repairs_with_scanTip` proves, above — and
`BtcPolicy.VaultUnspent.scanTipWallet`'s own birthday does leave the resurrected output uncovered
in the meantime. What closes it is the repair's own cold scan: the scan reads at the new tip, where
that output is live, so `BtcPolicy.VaultUnspent.scanTipBirthday` takes the re-import's birthday
down to the lower of the scan anchor's height and the lowest creating height
`BtcPolicy.VaultUnspent.liveCreator` finds — at or below the output's own creating height. So the
repair is a closure and not merely a cost, and the output is uncovered only until it completes.
Both of those are reasoned from the definitions, and unlike the standing-marker half above neither
is exhibited. That the output is uncovered in the meantime is not, because no declaration reads
`BtcPolicy.VaultUnspent.unwatched` on that wallet. That the repair closes it is not, because no
exhibit evaluates `BtcPolicy.VaultUnspent.repair` at the withdrawn anchor on that wallet:
`BtcPolicy.VaultUnspent.cleared_only_by_rebuild` does hold of a repair under either anchor, but it
says which marker the rebuilt wallet holds, not what that wallet then watches.

That there is no third case rests on an assumption about the chain the model does not itself enforce.
A view is an arbitrary map from heights to hashes and `BtcPolicy.Chain.Anchor.active` tests a single
height, so nothing in the model stops a view from keeping a marker's anchor hash while changing a
block below it; the theorem therefore takes agreement at every height at or below the anchor as a
hypothesis rather than deriving it. Bitcoin is what makes that hypothesis hold — a reorg that
replaces a block at some height replaces every block above it — and it is recorded here as a
dependence on the chain rather than as something the anchor test proves.

**Trust only the newest marker.** The formal model's reading before the amendment, and the
conservative-sounding one: if a repair might narrow what the wallet covers, believe only the last
import. Rejected twice over. The regtest run refutes it as a necessity — Core's wallet followed the
reorg away and back for every variant, so nothing forced the narrow reading — and it is not
recoverable from a real wallet anyway, because import order is not stored: the descriptor list a
node reads back carries no sequence, so "the newest marker" is not a thing a node can identify.
Decision 5 makes the question moot: no import narrows what an earlier one covered.

**Run a full scan whenever the cache is more than 32 blocks behind.** Simpler than a partial delta
commit: if the walk cannot reach the tip, cold-scan. Rejected because a node behind by more than
the delta window would pay the cold scan on every pass, which is exactly the shape `DEF-9`
records. Committing the partial walk lets later refreshes continue the job, at most 32 blocks each,
for the price of block reads.

**Import nothing into an empty vault.** Considered for the case the cold scan finds no live output:
with no output there is no oldest output and, under the old rule, no birthday. Rejected because it
contradicts `DEF-9`'s prohibition — "the steady state MUST be served by a node-owned watch-only
descriptor wallet with the full scan as cold-start and repair fallback (`WTC-6`)" — which requires a
usable wallet at the steady state whether or not the vault currently holds a coin, and because the
amended birthday has a floor of its own, `S`, so an empty vault imports from the settled block and
is usable immediately. The regtest run built all four wallets at an empty vault for this reason.

**Retry a failed attempt from the scan it kept.** Considered for decision 9 on 2026-10-02: hold the
failed attempt's cold scan and run the re-import again from it, so that a retry costs no scan and
does not wait for one. Not chosen: the owner took the rule under which a failed attempt starts
nothing of its own and the next attempt begins at a cold scan the cache needs anyway.

**Scope the latch, but go on retrying a built wallet's repair on every refresh.** Considered for
decision 9: leave the unbuilt wallet unlatched and keep the rule of 2026-10-01 for a wallet that
holds a marker, each refresh that finds the latch set and no attempt in progress cold-scanning and
starting one. It is what the reference implementation does. Not chosen: where the re-import cannot
succeed it is a cold scan on every refresh, the shape `DEF-9` records as "every restart and every
periodic refresh repeated it", and the cache does not need the wallet to be served. The model keeps
it as the retry trigger's `everyRefresh`.

**Record the settled block in the attempt's state.** Considered for decision 11: have the state
carry what the rebuild reads from the scan view — the settled block, or the view itself — and
refuse a re-import that offers another. Not chosen: it changes the state and the trace format to
exclude a pair of views no chain of blocks can produce, where a stated premise excludes the same
pair and changes neither.

**Keep the served-chain tie as a new rule of `WTC-6`.** Considered for decision 10: give the test
the model was making a sentence of its own and a conformance row. Not chosen, for the reasons
decision 10 gives; the model keeps it as the chain tie's `tied`.

## Consequences

**The reference implementation diverges and must move in its own repository.** `btc-policy-rust`,
crate `vault-node`, module `chain`, carries the design this ADR amends:
`chain::import_vault_descriptors` anchors the completion marker at the scan tip, brackets the import
once rather than twice, and computes the birthday from the live outputs the cold scan found, with no
walk of the settled depth and no birthday field on the marker;
and `chain::refresh_vault_unspent_cache_mode` returns a delta walk's error instead of falling
through to the cold scan, so a walk that keeps failing from a still-active anchor leaves the cache
below the tip indefinitely. It already commits a partial walk, which decision 8 adopts. It refuses
the cache as a delta base on every pass while a repair is pending with no attempt running, which
`WTC-9` stated from 2026-10-01 and since decision 9 no longer does: there the reference now
diverges, retrying a failed repair of a built wallet with a cold scan on every pass. On the other
two points of 2026-10-02 it already agrees: it latches only a wallet that holds an anchor and does
not retry an unseeded wallet's build each pass, and `chain::advance_confirmed_scan` captures a
height when its walk starts, not a block, so it makes no served-chain tie.
`WTC-14`'s tip test is not on that list: the reference's watchtower pass already compares the active
hash at the captured height, which is the reading decision 7 adopts, and the formal model is what
moved — it compared the chain tip read after the loop. Nothing that implements the specified system
belongs in this repository, so this paragraph is the whole of what this repository does about the
divergence; the work is tracked in `btc-policy-rust`.

**The tip-test change is the one with a liveness consequence.** Under the withdrawn reading a
`WTC-13` genesis re-scan on mainnet never completes, because a block arrives on top of every pass
long enough to matter. That is a wedge, not a slowdown, and it is why the tip test is a guard
parameter with a trace under each value rather than a wording fix.

**Three guard parameters, three negative controls.** `VaultUnspent.lean` owns the marker anchor
(`settled`, twin `scanTip`) and the delta commit (`partialWalk`, twin `tipOnly`); `Watchtower.lean`
owns the tip test (`capturedHeight`, twin `chainTip`). Each holds its trace under each value, every
theorem over `current` is in `Exhibits.lean`, and `.github/workflows/gates.yml` breaks each one on
purpose and asserts the exact set of theorems that goes red.

**The catch-up rules of 2026-10-01 are guard parameters as well, and decisions 9 and 10 moved
two of them.** The amendment that completed decision 8 and gave `WTC-9` its repair attempt brought
three rules, and `VaultUnspent.lean` owned a parameter for each: the walk range (`whole`, twin
`asRead`, under which a walk that passes its proofs is complete wherever it stops), the latched
base, and the chain tie. The walk range stands. The chain tie's value as it stands is now `untied`
and its twin `tied` (decision 10). The latched base is taken into the retry trigger, which
decision 9 brought: `neededScan` as it stands, with two twins — `everyRefresh`, the rule of
2026-10-01, which was the latched base's `coldScan`, and `noFirstScan`, the reading that rule had
withdrawn, which was its `cache` — because all three answer one question, what a latched refresh
with no attempt in progress walks from, and a second parameter would have carried values the
first overrides. Decision 9 also brought the latch scope (`scoped`, twin `vacuous`, under which a
wallet holding no marker is latched), which `BtcPolicy.VaultUnspent.observe` reads. The delta
commit, the walk range, the retry trigger and the chain tie reach the model as one record, whose
value as it stands is `BtcPolicy.VaultUnspent.currentRules`; each parameter has its twins' traces
beside it and a negative control per twin in the workflow.

**The delta walk is measured by its own tip.** `WTC-6`: "the lesser of the tip captured when the
walk starts and 32 blocks above that anchor". The model read that tip from the view a refresh
captures before the wallet read, so a block landing during the read — which the read's bracket
rightly discards — made the walk that followed overrun a range one block too short, and the model
cold-scanned where a node walks. `BtcPolicy.VaultUnspent.serve` now takes the walk's view as its
own argument, and `BtcPolicy.Exhibits.VaultUnspentCache.block_during_wallet_read_is_walked` is the
case.

**An attempt has a lifecycle, and the re-import is held to its cold scan.** `WTC-9`: "At most one
attempt, whether a repair or a first build, is in progress at a time." The model's state holds the
cold scan the attempt in progress started from (`BtcPolicy.VaultUnspent.State`), a refresh that
finds one in progress starts no other (`BtcPolicy.VaultUnspent.attempt_in_progress_not_restarted`),
and the re-import clears the latch only when the scan it is given is that one
(`BtcPolicy.VaultUnspent.cleared_only_by_rebuild`,
`BtcPolicy.VaultUnspent.rebuild_is_of_the_attempts_scan`). An attempt that stops without
rebuilding — the re-import refused, or a failure before it, `BtcPolicy.VaultUnspent.endAsFailure` —
leaves the latch set and nothing in progress (`BtcPolicy.VaultUnspent.failed_attempt_keeps_latch`).
As amended on 2026-10-01 the next refresh then started another attempt from a cold scan of its
own, and the model, reading the latch condition as holding of a wallet with no marker, ran a first
build under the latch, so one that kept failing cost a cold scan on every refresh; that question
was tracked as `bps-8s0.11.22`. Decision 9 settles both: the state also holds whether a cold scan
has replaced the cache since the latch set, a wallet holding no marker is not latched, and the next
attempt starts only where a refresh serves a cold scan with none in progress
(`BtcPolicy.VaultUnspent.cold_scan_starts_attempt`). The state's new field moved the trace format
to version 4, which `ADR-0023` records.

**Spentness is now in the formal model.** The model's ledger carries the outputs a block creates
*and* the ones it spends, each spend with the height of the block that created the output — without
which the amended birthday cannot be stated at all. The cold scan yields what is live
(`BtcPolicy.VaultUnspent.live`, over `BtcPolicy.VaultUnspent.spentUpTo`) rather than everything
confirmed. What is still opaque is `WTC-10`'s prevout re-validation, the predicate that drops an
output the delta walk carried and a later block spent.

**`CNF-89` and `CNF-91` grew rows and `DEF-21`'s prohibition moved.** The conformance checklist now
asks for the block that arrives on top, the panic that resets the cursor, the two-point bracket, the
repair that never starts later, and the read's own tip bracket. `DEF-21` now prohibits an import
bracketed against anything but the settled block. Decision 9 moved `CNF-91` again: it asks for the
cold scan a latched refresh makes until one has been published, for the failed attempt that costs
no scan of its own, and for the wallet holding no marker that is not latched.
