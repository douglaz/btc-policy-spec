# Every confirmed duress Escape is selected; the sweep does not pick one

Status: accepted 2026-09-12. Specification-repository decision; the reference implementation
still carries the single-selector design this withdraws and has not been changed.

A duress SpendRequest carries an Escape: a user-signed sweep of the vault to the escape wallet.
When `t` nodes hold the Carrier the federation arms (`DUR-5`), and at `T` the Escape is combined
and broadcast (`DUR-19`–`DUR-31`). That firing is the entire purpose of the duress path — it is
what moves the coins beyond the coercer's reach in hours rather than the one hundred and eighty
days Recovery takes.

`DUR-10` had each node select **one** Escape to fire: "first-live-wins over confirmed duress
intents", where *first* meant first to reach its holder decision **at this node**. Carriers reach
different nodes in different orders, so with several distinct duress Carriers in flight — a
frightened user retrying after a timeout, or a post-wrench coordinator re-submitting with the PIN
it holds — honest nodes could split their selections. On 3-of-5, a 2/2/1 split leaves no Escape
with `t` partials. Nothing fires. Lockdown lands regardless (`DUR-2`), so the coins are frozen and
exit through Recovery: denial, never theft, and inside `SEC-21`'s "Censoring or selectively
delivering requests can suppress the sweep". This historical split selected different Escapes;
it was not a split of one Escape's ladder. But
it defeats the mechanism that exists for exactly the moment a scared person hits retry.

A deterministic tiebreak does not close it. "Every node fires the lowest commitment id" assumes
every node has *seen* that id; the confirmed sets differ by delivery timing, not only the choice
within them.

## Decision

**1. The Armed overlay holds a set of selected Escapes, not one.** `DUR-10` owns the insertion:
"Every holder decision whose intent names a pair adds that pair's Escape id". Nothing is ever
chosen over anything else; nothing is ever displaced.

**2. Each selected Escape is gated, laddered, latched, finalized and re-authorized
independently.** `DUR-20` through `DUR-31` apply per Escape: its own fire window, its own
admissibility pass, its own rung selection and latch, its own quorum. A node releases its partial
on every selected Escape whose own gates pass.

**3. The collection is pin-uniform, and release is gated per entry.** Amended 2026-10-03 to
follow the inheritance decision recorded in `ADR-0023`: `DUR-10` inserts "the pair duress bit"
and requires "BOTH `sweep_active` AND that entry's own duress bit". Its unbound and refused cases
are owned there. The former description of every normal-PIN insertion as a clear bit is
withdrawn; `DUR-5` owns inheritance at that holder decision. The first draft's separate defect
is retained: gating on `sweep_active` alone made an unrelated normal pair's Escape fireable
when another Carrier armed. A reviewer caught it.

**4. `T` is unchanged.** `DUR-13` already handles several duress intents: a later arm may only
shrink `T`. One deadline, many Escapes.

## Why releasing on several Escapes grants nothing

Three facts from the set, none new:

- **Every Escape pays the escape wallet.** `CHN-14`: "An Escape MUST spend only vault outputs and
  MUST pay every destination output to the escape descriptor." There is no other destination an
  Escape can have.
- **At most one of a node's selection can confirm.** `DUR-24` requires every admissible Escape
  to deliver at least `escape_coverage_pct` of the vault's protected value, and `MAN-9` refuses a
  coverage of fifty or below at load. Two input-disjoint sets cannot each hold more than half of
  a value no smaller than their combined inputs — `DUR-22`'s floor — so any two admissible
  Escapes a node had selected when it first released overlap on inputs and conflict. Releasing
  partials on three does not sweep three times. The guarantee is per node: an Escape selected
  after that release, or one that a different subset of nodes selected, can confirm beside the
  first (`F59`), each paying the escape descriptor at a fee the coverage caps. (The lower bound is why the
  argument holds for every sealable value and not only the default of 95; a reviewer found the
  gap.) **Historical exception, withdrawn by ADR-0022:** the former escape-class pair credited
  its residual with the confirmed sibling's coverage, so input-disjoint residuals crediting one
  sibling could both confirm. That exception and its window question (`F55`) went with the pair;
  ADR-0022 records "Every SpendRequest is now exactly a hot spend plus its Escape". There is no
  current sibling credit.
- **Choosing which one confirms is a power the attacker already has.** `SEC-21` lists what a
  post-wrench coordinator can do: "censor, selectively deliver". This can favour an already
  user-signed Escape with a costlier ladder; it does not guarantee confirmation. Selecting among
  distinct Escapes through request delivery is separate from removing rungs of one Escape.
  `SEC-21` bounds the latter: "Stripping uniformly or differently per node only downgrades the
  `T`-time sweep, at worst to the base when that base is admissible." The fee bound remains
  `DUR-24`'s "`(100 − escape_coverage_pct)%` of protected value".

A partial is bound to its own commitment by the sighash (`CHN-11`), so a partial on one Escape
cannot be applied to another. `t − 1` compromised nodes holding partials on several Escapes can
complete at most one of those an honest node had selected at its first release; where honest
nodes selected different Escapes, two can complete (`F59`), each to the escape wallet, at a fee
the sealed coverage caps per sweep.

## Consequences

**The 2/2/1 split fires.** Every node that confirmed Escape 1 releases on it; if `t` did, it
completes. Set divergence between nodes stops mattering, because no node's release depends on
what another node selected.

**A stale Escape may fail coverage and may also deny other Escapes.** `DUR-22` owns the shared
denominator and the accepted denial: "an absent or inflated prevout a selected Escape names is
counted too" and "can only raise this denominator against real Escapes: denial inside `SEC-21`".
This is `SEC-21`'s "Censoring or selectively delivering requests can suppress the sweep",
including "a request whose selected Escape inflates the coverage denominator"; it is not a
power granted by stripping rungs. The former claim that the others are unaffected is withdrawn.

**Settlement strands input-conflicting selected Escapes.** `DUR-21` owns the interaction:
"what its mempool residency does to this one's prevouts, which `WTC-24` reads as spent".
The first draft wrongly invoked hot-candidate invalidation here. The shared-input argument also
needed correction: the former denominator restored only the Escape under evaluation and shrank
as another became resident, letting a disjoint Escape cover the remainder (`F54`). `DUR-22` now
counts "every distinct input outpoint of EVERY selected Escape counted once at its
`witness_utxo` value whatever the read says of it". Its argument owns the per-node scope:
"over the Escapes it had selected when it first released". The former description of the
denominator as the vault as armed on every pass was corrected in `F59`; the current floor and
late-selection and cross-node exceptions remain at `DUR-22`.

**The sweep path's prose is per-Escape throughout.** Twenty sentences in `DUR-20`–`DUR-31`
written for *the* Escape now read for *each selected* Escape. The mechanics of each sentence are
unchanged; only the quantifier moved.

**The reference implementation now diverges from the set.** It selects one Escape. That is
tracked in its own repository (`OVR-17`), not as a finding here.

## Alternatives rejected

**Leave it as the accepted residual it already was.** It was bounded — Lockdown holds, funds
route to Recovery, nothing is stolen — and it was documented. Rejected because the trigger is not
an attack; it is a retry, which is the expected behaviour of the person the duress path exists to
protect, and because the fix grants an attacker nothing beyond `SEC-21`'s "censor, selectively
deliver" power.

**A deterministic tiebreak** — lowest commitment id, earliest `first_seen`, any total order over
each node's confirmed set. Rejected because the sets differ, not only the order within them. A
node cannot select an Escape it never saw, and a rule that assumes it can produces the same split
with a different label.

**Converge the sets first** — gossip confirmed Escape ids between nodes before selecting.
Rejected on `NCH-1` and `NCH-3`: the channel carries signatures and assembly and never policy, and
a peer's "I confirmed this Escape" is exactly the kind of assertion no node may act on. It would
also add a round trip on the path whose latency `DUR-15` already declines to bound.

**Let the coordinator name the Escape to fire.** Rejected on `DOM-2`: the coordinator is hostile
from the wrench, and this is the moment after it.
