# The refresh bounds are sealed; the PIN attempt budget is not

Status: accepted 2026-09-12. Specification-repository decision, closing `F15`. Reviewed by three
independent reviewers; the reference implementation was read as
evidence and was not changed.

`MAN-7` named three values as node configuration that the ceremony never writes:
`refresh_min_interval_secs`, `refresh_max_feerate`, and the `pin_attempt_budget` table. Every
provisioned node therefore ran on defaults, and none of the three appeared in `MAN-2`'s manifest
preimage, so nothing detected a node whose copy differed.

The finding that recorded this treated the three as one question. They are not. It conflated two
independent axes — whether a value is **sealed** (in the preimage, so a mismatch fails startup)
and whether the ceremony **asks** for it — across three values that share only the accident of
being defaulted.

## The question that had to be asked first

"Should this be sealed?" is unanswerable on its own, because *sealed* names a mechanism rather
than a property. The property is whether the federation must agree, and the set had no word for
it: **federation-uniform** appeared in six places across four documents, carried `SPN-19`'s entire
propagation rule, and was defined nowhere. `CONTEXT.md` now defines it, and the test is whether
any request the coordinator could compose reaches quorum across the divergence.

That test is narrow on purpose. `policy_version` passes it — differing values give differing
`commitment_id`s, so no request whatsoever combines across the split, which is why revision 3
sealed it. `delivery_horizon_secs` fails it, and `SPN-9` says so outright: "The horizon is
per-node, not sealed (`MAN-7`)"; one node refuses `EXPIRY_TOO_SHORT`, the refusal propagates, and
a longer expiry satisfies everybody.

**Both refresh bounds fail the test too.** A node that refuses `REFRESH_FEE_EXCEEDS_CAP`
propagates, the accepting nodes still reach `t`, and a cheaper transaction passes everywhere. So
sealing them is not forced by necessity. It is a policy choice, and this ADR is the record of
making it.

## Decision

**1. Both refresh bounds are sealed into `MAN-2`, as manifest schema revision 4.** They are
shared security policy, not host preference. `ADR-0006`'s own correction block is the reason:
the refresh class is "pin-less AND has no Hold — so neither guard applies to it. The refresh class
therefore needs its own bounds: a **minimum refresh interval** and a **tight refresh-specific fee
cap**." The two are named together as the replacement for two missing guards, and every other burn
bound in the set is already sealed — `POL-17` for the Hot-budget triple, `MAN-13` for the ladder
ceiling. Leaving these two out made them the only security bounds `MAN-7` marked unsealed.

**2. `pin_attempt_budget` stays node-local, and is not sealed.** It guards the two PIN digests,
which `MAN-7` already leaves unsealed, so the guard belongs in the same trust domain as the thing
it guards. `MAN-23` makes it RAM-only and node-lifetime, and `SPN-18` makes lockout produce denial
only — never an unfrozen signing quorum. Uniformity would actively hurt: every peer re-runs the
attempt gate on a relayed request (`NCH-27`), so a uniform budget locks all `n` nodes out on the
same wrong attempt, where divergent budgets stagger it.

**3. The ceremony MUST ask for every value it seals, and SHOULD ask for this one too** (`MAN-27`).
This is the half of `F15` that survives independent of sealing. A value the Operator never chose
is still frozen for the vault's life by `OPS-1`, and the refresh bounds in particular price a burn
ceiling only the Operator can size.

**4. This is revision 4, not an amendment to revision 3.** `WIR-32` states "a vector that changes
is a new protocol revision", and neither it nor `OPS-29` nor `MAN-3` offers an exemption for
unfunded vaults or recent commits. Revision 3 had been published three commits earlier under
identical conditions; amending it in place would contradict the choice the set had just made, and
would let two byte layouts share one version number in any reimplementation that pinned it.
`MAN-3` additionally records that no vault was ever sealed below revision 4, so an implementation
refuses revisions 1–3 outright rather than inferring a compatibility burden from `OPS-31` that
nothing can ever call in.

## Consequences

`REFRESH_FEE_EXCEEDS_CAP` stops propagating. With the ceiling sealed, every honest node refuses
the same transaction, which makes it a federation-uniform policy refusal under `SPN-19` — the same
class as `FEE_EXCEEDS_CAP` on a spend. As decided, `REFRESH_TOO_SOON` did not move, and the
reason was the whole distinction this ADR turns on: what made that one node-local was the
per-node **log**, not the per-node **number**, and sealing a value does not make a history
uniform. `ADR-0019` then withdrew the log the same day; with age read from the chain, that
refusal is federation-uniform too, and `SPN-43` now classes it so.

`MAN-9` gains a refusal for `refresh_max_feerate = 0`, which would otherwise refuse every refresh
of even one satoshi and silently strand the vault toward its recovery timelock. That is the defect
class `POL-17` already refuses for a zero hot cap.

Five published digests moved — three manifest variants, the endorsement, the envelope — plus the
end-to-end manifest fixture and the two config fixtures.

**Sealing alone did not deliver the bound `ADR-0006` asked for.** As this was decided, `SPN-46`
still enforced the interval from a per-node log of accepted refreshes, so with one compromised
signer a chain of refreshes could alternate which honest node co-signed and no honest node ever
saw two consecutive links. Sealing cannot reach that: it makes nodes share a number, and that was
nodes holding different histories. `ADR-0019`, decided the same day, withdrew the log and reads a
coin's age from the chain instead; with both decisions in force the bound holds.

## Alternatives rejected

**Leave both unsealed, to preserve operator tunability.** The premise is false. `OPS-1` states
"Once a vault is sealed, nothing an Operator can do reconfigures it", and `MAN-36` starts a node
exactly once in its life, so an unsealed value is exactly as frozen as a sealed one. What being
unsealed bought was not adjustability but unreadability: a refresh needs `t` signatures, so the
operative ceiling was whichever value the `t`-th most permissive node happened to hold, and a
coordinator retrying downward could burn each node's acceptance latch without ever reaching `t`.
The related appeal to "a per-host operator preference" has no referent either — there is one
Operator, and `finalize` writes every node's configuration from one ceremony state.

**Seal the fee cap but not the interval**, on the grounds that each node keeps its own refresh log
so nodes already diverge from their own history. This was the author's position and it does not
survive: `POL-17` seals `hot_window_secs` even though `POL-16`'s reservation ledger is equally per
node. The same argument would unseal that one. The asymmetry was unprincipled.

**Justify sealing from `OVR-9`** — "Every honest node MUST reach the same verdict, and select the
same fee-bump rung, from the same chain state." Proposed by one reviewer and rejected: it proves
far too much. `SPN-9` makes the delivery horizon per-node by design, and `hold_secs`,
`max_commitment_age_secs` and `delivery_horizon_secs` all produce divergent verdicts on identical
bytes, with `SPN-19` existing precisely to absorb that. An argument that would forbid those is not
an argument for sealing these.

**A relative cap — a small multiple of each node's own fee estimate**, as `ADR-0012`'s refresh
section originally specified. Rejected, and `SPN-47`'s absolute sealed `sat/vB` stands: a multiple
of a per-node backend estimate diverges by construction, which is the disease `DUR-30` spends its
whole requirement fighting on the sweep path, and a bound nobody can evaluate at seal time is not
a bound an Operator can size. `F53` records that this supersession was never written down.

**Defer the whole question until `F52` is fixed**, on the grounds that sealing a bound that does
not bind is decoration. Rejected on sequencing, not on merit: the two are independent, sealing
closes a real exception at the cost of one mechanical pass while a revision was already being cut,
and `F52`'s repair is a change to `SPN-46`'s predicate that deserves its own round with the threat
model open rather than a rider on a versioning commit.
