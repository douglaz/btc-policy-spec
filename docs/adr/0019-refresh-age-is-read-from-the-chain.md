# Refresh age is a fact of the chain, not a node's own record

Status: accepted 2026-09-12. Specification-repository decision, closing `F52`. Proposed by the
Operator during review; the reference implementation still carries the design this withdraws and
has not been changed.

The refresh interval exists because a refresh is the one Normal-path spend with no PIN and no
Hold, so `ADR-0006` gave it two guards of its own: a minimum interval between refreshes of a coin,
and a fee cap. `SPN-46` enforced the interval from a **refresh log** — each node's private record
of the outpoints consumed and produced by the refreshes *that node* accepted, with the time.

That log was the only policy check in the set that read a node's own notebook instead of the
chain. `WTC-1` states the rule the rest of the set follows: "every fact a node acts on comes from
consensus, never from its mempool's opinion or a peer's." `DUR-30` goes to unusual lengths — a
six-block anchor, a five-unit quantisation, a ban on mempool readings — precisely so that every
node derives the fee signal from the same chain state. The refresh log was the outlier, and it
failed in exactly the way an outlier from that rule would be expected to.

## What the log got wrong

**It did not bound burn.** Because each node saw only the refreshes it accepted, one compromised
signer could rotate which honest node co-signed, and no honest node ever saw two consecutive
links of the chain. On 2-of-3, after seeding a one-link divergence through `SPN-45`:

| day | refresh | signed by | outcome |
|---|---|---|---|
| 3 | `X→Y` | A, M | quorum |
| 5 | `Y→Z` | B, M | quorum — B's log holds nothing about `Y` |
| 7 | `Z→W` | A, M | quorum — A's log holds nothing about `Z` |

Seven confirmed refreshes in fifteen days against a thirty-day interval, indefinitely. `SPN-46`'s
own sentence — the log "is what bounds chained-refresh burn" — was false against an adversary the
threat model admits (`SEC-2` A5, `c < t`). Sealing the interval into the manifest (`ADR-0018`)
could not touch this: sealing makes nodes share a *number*, and this was nodes holding different
*histories*.

**It could not be fee-bumped.** The log latched on acceptance and nothing un-accepted, so a
refresh signed at too low a feerate blocked every replacement of itself and every child spending
its output, for the rest of the interval. Refresh has no ladder. The composer had one attempt per
coin per month.

Two proposals were on the table before the Operator's: accept the burn as a residual, since the
attack is slow (one confirmation per link), loud (every link trips `WTC-17`'s
`UNRECOGNIZED_SPEND` on the honest node it bypassed), capped (`SPN-47`), and worthless to an
attacker who cannot extract; or make each node refuse any coin descending from a transaction it
had not itself approved. The first left a false bound standing under a narrower sentence. The
second would have turned one transient backend failure — which `SPN-21` converts to a refusal by
design — into a node permanently refusing every descendant of that transaction, on a node that
`STO-1` forbids restarting.

## Decision

**1. A coin's refresh age is read from the chain.** A refresh input is admissible under the
interval iff `MTP(tip) − MTP(confirming) ≥ refresh_min_interval_secs`, where `confirming` is the
block in which the input's creating transaction confirmed on the active chain, `tip` is the
node's current tip, and `MTP` is BIP113 median-time-past. Every honest node reading the same tip
computes the same answer, and nodes whose tips differ by a block differ by minutes on an interval
of days — the tolerance `DUR-30` already accepts.

**2. An unconfirmed input is refused.** It has no confirming block and so no age. This is not a
limitation: a coin's recovery timer (`CHN-4`) has not started until it confirms either, so
refreshing it resets nothing. `F2`'s composer already builds over confirmed coins only.

**3. Any coin younger than the interval is refused, whatever created it.** Deposit, change from
a hot spend, output of an earlier refresh — the rule does not classify the parent. "A coin must be
at least the interval old to be refreshed" is what the Operator means, and it needs no
transaction-class judgement of anything but the refresh itself.

**4. A node keeps no refresh log.** The state is deleted from `DOM-20` and `STO-6`. There is
nothing to route around and nothing to prune.

## Consequences

**Both halves of `F52` close.** The alternation stops at its second link on every honest node,
because the first link's output is younger than the interval on the chain they all read. A
refresh that never confirms leaves no chain trace, so its replacement over the same inputs is
admissible everywhere; `WTC-25` walks its ancestry over the resident as a replacement and
`CHN-18` gives it BIP125 signalling, so it also assembles and enters the mempool. That is the
bump path, and it needs no ladder. (The first draft of this ADR stopped at "admissible"; a
reviewer traced the fire pass and found `WTC-24` reading the resident's inputs as spent. The
second draft fixed the fire pass and left ingress reading the age off the same mempool-inclusive
prevout flag, which refused the replacement one step earlier; the age is now read by txid from
the creating transaction's confirming block, mempool-independent.) The per-coin bound is only a
bound if the attacker cannot choose the coin count or the transaction size: no transaction of any
class may carry more vault-derived outputs than inputs (`CHN-30`), and a refresh may carry at
most 24 inputs (`SPN-44`), which closes the padding path where deposited dust is refreshed
beside one large coin to pay for a standardness-sized transaction. The bound is then
`refresh_max_feerate × vsize(24-in, 24-out)` per vault coin per interval.

**The bound `ADR-0006` asked for now holds.** At most one confirmed refresh per coin per
interval, at most `refresh_max_feerate × vsize` burned by each (`SPN-47`), enforced identically on
every honest node, with no arrangement of co-signers able to change it.

**`REFRESH_TOO_SOON` stops propagating.** It is now a federation-uniform policy refusal under
`SPN-19` — every honest node would refuse the same transaction — joining `REFRESH_FEE_EXCEEDS_CAP`.
Only `REFRESH_SUBORDINATED` remains node-local, because the pending log is the one per-node input
the refresh path has left.

**The reference implementation now diverges from the set.** It carries the refresh log this ADR
withdraws. That is tracked in its own repository (`OVR-17`), not as a finding here; `F52` is
CLOSED.

**Reorg behaviour is the same as every other spend's.** A confirming block that is reorged out
returns the coin to unconfirmed; a refresh already signed against it is the ordinary reorg
residual, not a new one. The tip-binding rules of `WTC-11` apply to this read as to every other.

**A backend that cannot answer fails closed** (`WTC-1`). The refresh path already depended on
the backend for every input's prevout (`SPN-21`); this adds a confirming-block read, not a new
dependency.

## Alternatives rejected

**Accept the burn as a residual and narrow the sentence.** The severity analysis was correct —
slow, loud, capped, and profitless to an attacker who cannot extract — and it was still the
weaker choice, because it left a guard in the set that did not guard, documented as such. A
control that must be read with a footnote explaining that it does not hold is a control the
next reader will trust anyway.

**Lineage-aware enforcement from the node's own approvals** — refuse any coin descending from a
transaction this node did not accept. It kills the chain at step two and the node already holds
the data. Rejected because the same rule fires on innocent failures: `SPN-21` turns a transient
backend fault into a refusal, and under this rule that node would then refuse every descendant
of the affected transaction forever, on a host `STO-1` forbids restarting. One network blip
during one legitimate spend would permanently cost a 3-of-5 vault a third of its margin.

**Keep the log and add the chain check as belt-and-braces.** Rejected: the log is what created
both defects, and a second predicate that can only refuse cannot repair a first one that refuses
wrongly. The bump lockout would remain.

**Measure age by wall clock against the confirming block's time.** Rejected: the wall clock is
per node (`DOM-24`), which reintroduces divergent verdicts on identical bytes, and it is
adjustable in ways `SPN-13` spends a whole requirement guarding against. Chain-to-chain is
deterministic.

**Measure age in blocks rather than seconds.** Cleaner arithmetic, and rejected only because the
sealed value is `refresh_min_interval_secs`, already in the revision-4 preimage in seconds, and
the vault's other coin-age timer (`CHN-4`) is a time-based lock. Two age rules in two units would
be a trap. Block-height age would be a legitimate revision-5 change if MTP ever proves awkward.
