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
exit through Recovery: denial, never theft, and inside the residual `SEC-21` already grants. But
it defeats the mechanism that exists for exactly the moment a scared person hits retry.

A deterministic tiebreak does not close it. "Every node fires the lowest commitment id" assumes
every node has *seen* that id; the confirmed sets differ by delivery timing, not only the choice
within them.

## Decision

**1. The Armed overlay holds a set of selected Escapes, not one.** At every holder decision the
node adds the intent's Escape commitment id to `selected_escapes`. Nothing is ever chosen over
anything else; nothing is ever displaced.

**2. Each selected Escape is gated, laddered, latched, finalized and re-authorized
independently.** `DUR-20` through `DUR-31` apply per Escape: its own fire window, its own
admissibility pass, its own rung selection and latch, its own quorum. A node releases its partial
on every selected Escape whose own gates pass.

**3. The collection is pin-uniform, and release is gated per entry.** A normal-PIN holder
decision adds the Escape to the same set with the intent's duress bit clear, exactly as `DUR-17`
already writes an inert delayed slot under the normal PIN. The scan, the insertion and the window
refresh are identical under both PINs. Release requires `sweep_active` AND the entry's own bit —
not `sweep_active` alone, which is one flag for the whole node and would otherwise make a
normal-PIN pair's Escape fireable the moment some other Carrier armed. (The first draft of this
ADR gated on `sweep_active` alone; a reviewer caught it.)

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
  gap.) The exception is an escape-class pair's residual, whose coverage is credited from its
  confirmed sibling (`DUR-22`): two residuals crediting one confirmed sibling can be
  input-disjoint and both confirm. The review of the merge found this; it grants nothing,
  because each pays only the escape descriptor and each residual's fee is capped at ingress
  (`POL-12`) and by its own coverage (`DUR-24`). Whether that residual is meant to fire at all
  under the default window is `F55`.
- **Choosing which one confirms is a power the attacker already has.** `SEC-21` lists what a
  post-wrench coordinator can do: "swap an escape-class spend/residual pair, and thereby suppress
  or downgrade the `T`-time sweep or choose which already-user-signed leg releases immediately."
  Picking the Escape with the costliest ladder is that power, and the ladder's fee is bounded at
  `100 − escape_coverage_pct` percent of protected value by the same coverage rule that bounds it
  today.

A partial is bound to its own commitment by the sighash (`CHN-11`), so a partial on one Escape
cannot be applied to another. `t − 1` compromised nodes holding partials on several Escapes can
complete at most one of those an honest node had selected at its first release; where honest
nodes selected different Escapes, two can complete (`F59`), each to the escape wallet, at a fee
the sealed coverage caps per sweep.

## Consequences

**The 2/2/1 split fires.** Every node that confirmed Escape 1 releases on it; if `t` did, it
completes. Set divergence between nodes stops mattering, because no node's release depends on
what another node selected.

**An Escape composed over a stale UTXO set fails its own coverage and is not released.** Each
Escape's admissibility is decided at fire time against the current protected value (`DUR-22`,
`DUR-24`); one that no longer covers is simply inadmissible, and the others are unaffected.

**Settlement of any selected Escape strands the rest, and nothing needs to clear them.** A
confirmed rung of one Escape spends inputs every other selected Escape shares, so each other
Escape fails `DUR-21`'s predicate on every later pass — no later than `WTC-24`, often at coverage
first — releases nothing, and is pruned with its pair at window close (`SPN-41`). `SPN-33`'s
input-conflict invalidation names hot candidates only and does not reach Escapes; the first draft
of this ADR claimed it did. The "shares inputs" premise itself needed a second correction:
`DUR-22` restored only the Escape under evaluation, so once one Escape was resident the
denominator shrank and a disjoint Escape over the leftover coins covered the smaller vault and
passed — two Escapes both confirming, at every coverage. `DUR-22` now restores every selected
Escape's inputs, so the denominator is the vault as armed on every pass and the shared-coin
argument holds. Raising `MAN-9`'s coverage floor did not buy this on its own; a reviewer traced
the moving denominator after that fix landed.

**The sweep path's prose is per-Escape throughout.** Twenty sentences in `DUR-20`–`DUR-31`
written for *the* Escape now read for *each selected* Escape. The mechanics of each sentence are
unchanged; only the quantifier moved.

**The reference implementation now diverges from the set.** It selects one Escape. That is
tracked in its own repository (`OVR-17`), not as a finding here.

## Alternatives rejected

**Leave it as the accepted residual it already was.** It was bounded — Lockdown holds, funds
route to Recovery, nothing is stolen — and it was documented. Rejected because the trigger is not
an attack; it is a retry, which is the expected behaviour of the person the duress path exists to
protect, and because the fix grants an attacker nothing beyond what `SEC-21` already concedes.

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
