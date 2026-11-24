# F48 node admission: owner decided

**Owner decided, 2026-11-24; normative amendment pending.** The owner forbids
`non_witness_utxo` in node `/sign` PSBTs, answering “yes” with the reason “I don't see why it's
hard to refuse a syntatically invalid request”, and answered “follow rec” on keeping the
existing decode step 17. This withdraws the prior option-1 standing-rule pick. F48 remains
open pending the rule and its formal correspondence; this research record changes neither.

## Decided format/decode form

Presence becomes invalid node-request format, even for an otherwise decodable PSBT with a
consistent parent. Absence passes this format check, subject to all other checks. This differs
from the historical late policy check below and from `ParentRule.refuse`, which requires
parents and refuses absence. The model's `refuse | ignore | verify` has no refuse-presence
reading; its `wireOk` condition is `(rule != .refuse || carried)`. Formal correspondence
remains open, and no theorem for the new format rule is claimed.

### Placement and effects

[SPN-5](../../04-spend-lifecycle.md#the-ingress-pipeline) says “through the following gates in
this order, returning at the first failure”. Its gate 17 is “spend and Escape PSBTs decode”;
gate 18 is “ladder has at most 3 rungs, then each rung decodes”. The format amendment belongs
at those existing decode steps, preserving the rung bound before rung decoding. Both decode
failures have “HTTP 400”, nonce “`consumed`”, propagates “`no`”, stages “`no`”.
[SPN-8](../../04-spend-lifecycle.md) says “a PSBT that does not decode” is “refused HTTP 400”.
No new pre-PIN check or reordering is selected.

Not every submitted request reaches decode. SPN-5 puts “**nonce consumed**” after gate 8,
then “PIN evaluation and carrier derivation (`SPN-16`)”, gate 12 “arm hook records intent
(`DUR-4`) — never fails”, gate 13 “the three clock predicates, re-decided (`SPN-17`)”, gate 14
“PIN attempt budget (`SPN-18`)”, “chain preflight (`SPN-21`)”, and gate 16 “the three clock
predicates, re-decided after the preflight” before gate 17. Its earlier failure rows retain
their effects, including clock/budget rows with propagation and staging “`yes`”.
[SPN-4](../../04-spend-lifecycle.md) says refusals before the nonce boundary “MUST consume no
nonce, perform no memory-hard work, evict nothing, and relay nothing”. Those paths stay intact.

[API-5](../../07-node-api.md) currently requires “HTTP 400 with an error body” for a field
“that is not a decodable base64 PSBT”, but also says “Everything decodable that is refused is
a policy outcome at HTTP 200 (`API-12`); a refusal is never a transport error”. The later
amendment must explicitly change that contract for this forbidden node-request field,
including otherwise decodable parent-bearing PSBTs, and retain an error body. No new error
detail or body shape is chosen here. This is an identified amendment, not an assertion that
the current API already says it. [SPN-24](../../04-spend-lifecycle.md) records
“`PSBT_INCONSISTENT` from evaluation” and says “Cache eligibility is decided by the originating
check, never just the code”. Decode-format failure is not spend evaluation and must not gain
a replay-log entry from that inventory; “Escape and ladder refusals MUST NOT populate the
spend-refusal entry”.

### Replay and relay

[SPN-23](../../04-spend-lifecycle.md#commitments-and-idempotency) begins “After all preceding
admission, PIN and post-preflight clock gates pass”. SPN-5 places accepted/refused replay at
gates 19/20, after decode. Thus a same-nonce copy can fail at gate 7, “nonce not replayed”,
before decode; a fresh-nonce copy matching a retained key must still reach and pass decode
before replay. Under the amended format, a retained parent-bearing copy fails there rather
than returning its old verdict. Parent-free copies that pass the preceding gates retain
SPN-23's “first `Accepted` on this node verbatim” and refusal “including its `API-25` fault
member verbatim”. No parent-free-history invariant or unconditional replay override is assumed.
The historical replay objection below concerns the late-check proposal; it does not override
this preceding-gate condition or block the decided decode placement.

[NCH-21](../../06-node-channel.md) calls the payload “the padded JSON of the tagged request”;
[SPN-35](../../04-spend-lifecycle.md) requires “one relay of the verbatim request to every peer”.
An honest relay therefore does not strip parents. Earlier propagating failures can still
carry an arbitrary authenticated client's parent-bearing request; peers may fail earlier too.
The honest originating program instead follows [OPR-46](../../17-operator-program.md):
“Every `non_witness_utxo` is stripped from the WIRE PSBTs after verification”. The decision
establishes no general parent-free relay or storage invariant.

### PIN argument and excluded observations

The argument covers only the decode outcome for the same request PSBT bytes when either
enrolled PIN reaches this step: forbidden presence depends on those bytes, not the PIN.
[SPN-16](../../04-spend-lifecycle.md#pin-evaluation) already requires “evaluate BOTH enrolled
Argon2id digests unconditionally, in the fixed order normal then duress” and “select the verdict
in constant time”. The same PIN work has therefore already occurred under either PIN; today's
undecodable PSBTs already follow this post-PIN failure path. A non-stripping client reaching
decode loses a nonce and a PIN attempt's work before learning it is malformed. This does not
mean every attempt consumes budget: [SPN-18](../../04-spend-lifecycle.md) says “Only a WRONG
verdict consumes budget”.

Byte lengths, timing and the intent already recorded by the arm hook are excluded from that
argument. Error-body length equality with today's undecodable case is unestablished because
diagnostics are unchosen; there is no byte-length result. Detecting forbidden presence differs
from detecting an undecodable PSBT, so parsing work can differ; neither timing equality nor a
measured timing difference is established. For intent, [DUR-4](../../05-duress-and-lockdown.md)
requires a “same-shaped **arm intent** for every SpendRequest under either PIN, keyed by the
Carrier identity”, and says “an intent refused before then names no pair”. Both decode-failure
classes occur after the hook and before SPN-23 computes commitment ids: no new hook placement
or pair binding is introduced, but different request bodies have different Carrier identities
([NCH-30](../../06-node-channel.md): “Its identity is the body”). Intent-content equality is
not claimed. The actual compatibility change is that formerly decodable parent-bearing input
now takes the malformed-request path. No pre-allocation saving, complete SILENCE theorem or
runtime result follows.

### Later normative work

The amendment must update SPN-5's gate-17 Spend/Escape and gate-18 rung decode definitions,
SPN-8's malformed-PSBT scope, and API-5's HTTP-400/error-body versus decodable-HTTP-200 boundary
for forbidden `non_witness_utxo`, while preserving earlier refusal effects and SPN-24's
originating-check cache distinction. Other `/sign` variants need the same format rule at
their own existing decode steps, not Spend gate numbers: [SPN-43](../../04-spend-lifecycle.md)
calls Refresh “pin-less” and orders “decode, idempotent replay, pruning, verification”;
[SPN-50](../../04-spend-lifecycle.md) calls Clawback “pin-less” and likewise orders “decode,
idempotent replay, pruning, verification”. No PIN work is added to either variant.
SPN-23's preceding-gate condition, NCH-21/SPN-35's verbatim relay, OPR-46's originating
stripping and CHN-22's signer-side “full previous transaction” stay intact, as does SPN-25's
backend comparison “to equal the chain's”. Requirements, ADRs and Lean are untouched here.
Diagnostics, parser mechanics and formal correspondence remain unperformed; any further
untouched-clause conflict **needs an owner decision**, and that part must stop.

## Historical analysis and proposals — superseded by the owner decision

Everything below records the earlier assessment, recommendations and proposals, not current
authority. Its pending-choice language, late-check replay objection and final question are
historical; the decided format/decode form above governs the next amendment.

Sources: [baseline](milestone-3-baseline.md),
[triage](milestone-3-triage.md), [F48](../../16-open-findings.md#findings): “The node-side rule —
refuse, ignore, or verify when present — is unstated”.

| Signer verification | Operator verification and stripping | Node admission | Downstream retention/wire output |
| --- | --- | --- | --- |
| [CHN-22/23](../../02-onchain-contract.md): “full previous transaction”; “hashes to the input's txid with an in-bounds vout”; mandatory witness script/value agreement; “SIGHASH_ALL”; “build every sighash before signing any”; “no partially signed group”. Preserve group shape. | [OPR-24/45](../../17-operator-program.md): “all against the full previous transaction”; preserve map counts, empty scriptSig/witness, duplicate-outpoint, sealed-script, checked-sum checks; verify display and ordered txids: “equal those previewed”. | [SPN-26/27](../../04-spend-lifecycle.md): “the user signature on every input”; “the prevout comparison”; “policy evaluation”, in order. Preserve classification, pair/ladder/transaction shape checks. | [ADR-0012](../adr/0012-model-b-spend-and-duress-architecture.md#architecture-full-model-b): coordinator “never combines partial signatures, finalizes, or broadcasts”; nodes do. |
| Amounts/scripts: CHN-22, “agree exactly with the selected parent output”. | Verified canonical witness supplies wire amounts/scripts. | Backend authority: [SPN-25](../../04-spend-lifecycle.md), “require the PSBT's `witness_utxo` script and value to equal the chain's”. | Preserve [CHN-24–26](../../02-onchain-contract.md#the-commitment), “the exact-transaction binding”. |
| Full-parent PSBTs through validation/signing. | OPR-45: “every full-parent PSBT and the preview storage are then dropped”; OPR-46: “Every `non_witness_utxo` is stripped from the WIRE PSBTs after verification”; “canonical `witness_utxo` is retained”. | Both accept-absence options admit stripped input. | Relay: NCH-21's “padded JSON of the tagged request”; replay: SPN-23's “exact base64-decoded PSBT bytes”. Optional-parent candidate retention pending. |

Common: checks/backend authority above. “Pass” concerns parents only.
Proposed **ignore** boundary: bounded PSBT/typed-parent decoding; ignore correspondence, never
accept malformed opaque bytes.

| Input / consequence | Accept absence, verify supplied (recommended) | Accept absence, ignore supplied | Require full parents, verify supplied | Refuse-when-present, accept absence |
| --- | --- | --- | --- | --- |
| Absent | Pass | Pass | Refuse | Pass |
| Present-consistent | Pass | Pass | Pass | Refuse |
| Present-malformed encoding | Decode error | Decode error | Decode error | Decode error |
| Present-inconsistent | Refuse | Pass parent check | Refuse | Refuse for presence |
| Changed rule / cost / unknown | SPN-25 conditional checks; parsing/hash/comparison work; sublimit/retention pending | SPN-25 non-authority rule; syntax work; syntax/retention details pending | Presence requirement; transport/retention cost; wire redesign unresolved | New presence refusal; typed parsing remains; accepted parent retention avoided; replay scope pending |

Require-present's proposed “refuse absence” conflicts with OPR-46's quoted stripping: **needs an
owner decision**. [§9](proof-boundaries.md#9-fast-exit-feasibility):
`Feasibility.refuse_refuses_composed`, assuming `composeEvery lim txid s = .ok q`,
concludes `s.bounded lim .refuse q = false`.
`Exhibits.Feasibility.f48_moves_the_verdict`, at fixed `largeVault`/`lim`: stripped requests bounded
under ignore/verify; every request fails `nodeOk` under require-present.
Abstract 400-byte inputs establish no production capacity.

Recommended: bounded valid parent decoding, hash equals input txid, vout in range, selected
output equals mandatory `witness_utxo`. Retain SPN-25's “`PSBT_INCONSISTENT` / `prevout_ground_truth`”
for backend mismatch. Parent bytes neither replace backend authority nor prove
network identity. Preserve SPN-25's “absent or unconfirmed is tolerated here”; supplied parents
never promote those reports to confirmed. Independent sealed-network validation distinguishes
network mismatch from fetch failure/absent/unconfirmed reports; mapping pending.

[SPN-21](../../04-spend-lifecycle.md): “exactly two batched backend calls”, “under the backend
timeout, outside every lock”; ladder reuses Escape inputs. Fetch after PIN budget, before registration/clock rechecks;
conversion to refusal comes “after the accepted and refused replay lookups”. Preserve accepted
re-staging and refused replay without staging ([SPN-23](../../04-spend-lifecycle.md): “returns
that refusal”, “does NOT stage”). Without replay, fetch failure is node-local, fail-closed,
“propagates and stages”; no universal confirmed-only gate.

Allocation: [API-4](../../07-node-api.md), “body larger than
1 048 576 bytes” before decoding; base64 PSBT decoding; [OPR-35](../../17-operator-program.md),
“at most 64 MiB” aggregate retained-parent projection and “maximum finalized vsize at most
100 000 vB”; [NCH-10/19](../../06-node-channel.md), envelope `max_msg_bytes` “default 1 048 576”,
bounded concurrency/read; [SPN-32](../../04-spend-lifecycle.md), “current bytes plus the maximum partial-signature growth”
charged against candidate-store limits. Coordinator projection grants no node
allowance. Proposed parsing requires checked aggregate accounting before
retention/allocation; additional numeric sublimits pending. Preserve OPR-46's “Before the
PIN a worst-case request shell” and “actual request is rechecked before ingress”. Stripping saves
node-wire parent payload, not signer/coordinator acquisition/retention or finalized vsize.

Smallest follow-up: SPN-25 rule plus ordering/error/observation owners.
Unadopted proposals: typed-parent decoding at SPN-5's PSBT-decode gate (HTTP 400,
consumed nonce, no relay/stage); SPN-26/27 `parent_consistency` (Escape-prefixed)
after signatures, before confirmed comparison; semantic failures use HTTP 200,
`PSBT_INCONSISTENT`, reason-specific details, consumed nonce, no relay/stage, uncached.
[API-5](../../07-node-api.md): “not a decodable base64 PSBT” means HTTP 400;
“Everything decodable that is refused is a policy outcome at HTTP 200”. Finalize names/details
with API-13. Preserve first refusal and [API-25](../../07-node-api.md):
“Eligibility is exactly this inventory”; new parent failures omit fault lists, not silently extend it.
Preserve SPN-3's “pin-independent in every observable”: compare codes/details, fault lists, byte
lengths, work/timing under both PINs, including NCH-21 padding. [SEC-10](../../12-security-requirements.md):
“scope of SILENCE” must be stated; [receipt-only evidence](milestone-3-baseline.md) certifies no
ingress bytes/timing property here.

Option 4, **refuse-when-present**, would reject a request carrying any full previous transaction
and accept absence, subject to other checks. Option 3 is the opposite:
**require-full-parents/refuse-when-absent**, represented by `ParentRule.refuse` in
[the model discussion](proof-boundaries.md#9-fast-exit-feasibility). That three-valued model has
no reading for option 4, and no theorem proves its new refusal or parse behavior.
`refuse_refuses_composed` concerns option 3 only; it is not an option-4 obstruction.

Against verify-supplied, presence refusal can avoid parent hashing and correspondence checks;
against ignore-supplied it adds refusal without removing such checks. After typed PSBT decoding,
neither comparison promises parsing, checked-framing or allocation savings: that work has happened.
Successful parent-free candidates need no parent retention, but rejected requests occupy ingress
buffers and decoded objects until disposal. Earlier clock/PIN failures can retain and relay
parent-bearing requests. Refusal establishes no general parent-free storage or wire invariant.

[API-4](../../07-node-api.md)'s “before decoding” body cap remains. A future bounded scanner
might avoid constructing typed parent objects by checking lengths and skipping bounded values,
but only under a justified decode/error-order contract preserving [API-5](../../07-node-api.md):
“not a decodable base64 PSBT” means HTTP 400; “Everything decodable that is refused is a policy
outcome at HTTP 200”. Stopping at a parent key cannot establish later bytes' decodability;
malformed data must not become a presence refusal. No parser is written here.

For fresh evaluation, propose appending presence to POL-7's consistency checks after “any input
without a `witness_utxo`”, preserving its preceding emptiness/map-count order.
[SPN-26](../../04-spend-lifecycle.md)'s “the user signature on every input” and “the prevout
comparison” would precede it; POL-6's “return the first failure” would still govern. The proposed
decodable refusal would follow nonce consumption, answer HTTP 200 without relay/stage, and use
`PSBT_INCONSISTENT` with a proposed `parent_presence` check, subject to
[API-13](../../07-node-api.md)'s “structural, class, ladder, prevout, signing or registration
inconsistency” ownership. [SPN-27](../../04-spend-lifecycle.md)'s “every refusal's check prefixed
`escape:`” would cover Escape/rungs when their verification is reached.

[SPN-24](../../04-spend-lifecycle.md) says “Cache eligibility is decided by the originating
check, never just the code”. A proposed primary spend-evaluation consistency refusal would join
its “`PSBT_INCONSISTENT` from evaluation” inventory; “Escape and ladder refusals MUST NOT populate
the spend-refusal entry”. An earlier presence gate would need explicit cache ownership, not
inherit eligibility from that code. [API-25](../../07-node-api.md)'s “Eligibility is exactly
this inventory” means the new check omits `faults`; existing eligible checks still win when first.

The late proposal cannot promise rejection of every parent-bearing replay.
[SPN-23](../../04-spend-lifecycle.md) says a retained matching acceptance key “returns the
commitment's first `Accepted` on this node verbatim”; SPN-24 says “retain every acceptance key
under which it was accepted until that commitment's expiry”. Rejecting all such requests before
replay conflicts with that obligation. It **needs an owner decision**; that amendment stops here,
pending an explicit admitted-history invariant excluding parent-bearing retained keys or an
owner-approved rule change. Neither is adopted.

The specified originating program differs from arbitrary authenticated clients.
[OPR-43/46](../../17-operator-program.md) order “strip signed wire parents → worst-case preflight
→ PIN” and require “Every `non_witness_utxo` is stripped”. Refresh delivery uses
“`RefreshAuthorization  = { refresh }`”; [OPR-69](../../17-operator-program.md) uses
“`OPR-43`'s order with the PIN step absent” for Clawback. Their stripped requests pass this
parent check. A non-stripping client's decodable fresh request would instead be refused when
the check is reached, a compatibility loss relative to verify-supplied and ignore-supplied.

Honest relay need not reach that check: [SPN-5](../../04-spend-lifecycle.md)'s clock and PIN
failure rows say “`yes`” for propagation before PSBT decoding. [SPN-35](../../04-spend-lifecycle.md)
requires “one relay of the verbatim request”; a peer's copy can similarly fail earlier or reach
presence refusal. Nodes cannot strip authenticated bytes: [WIR-5/21](../../08-wire-contract.md)
bind “exact base64 ASCII” and the request preimage, while [NCH-30](../../06-node-channel.md)
says “Its identity is the body”.

[SPN-43/50](../../04-spend-lifecycle.md) place “decode, idempotent replay, pruning, verification”
in that order; extending verification would preserve earlier failures and replay.
[SPN-25](../../04-spend-lifecycle.md)'s confirmed comparison and “absent or unconfirmed is
tolerated here” remain; [CHN-22](../../02-onchain-contract.md)'s signer-side “full previous
transaction” remains stronger. [ADR-0013](../adr/0013-concrete-protocol-schemas.md) names wire
and lifecycle owners and says authentication “does not stop the coordinator itself from editing
and re-signing it”. No cited ADR decision or theorem conflicts merely because option 4 is
unmodeled. The replay conflict above is conditional and actual.

Option 1 remains recommended: option 4 sacrifices client compatibility without demonstrated
typed-decoder savings. Any future refusal must preserve [SPN-3](../../04-spend-lifecycle.md)'s
“pin-independent in every observable” work and responses; no SILENCE proof for new parsing,
bytes or timing is implied. No policy is adopted.

Later acceptance cases: stripped, matching, malformed, wrong txid, vout out of range, witness
mismatch, backend mismatch, backend absent/unconfirmed, fetch failure, network mismatch.
Update record/F48 disposition afterward; no extra review prerequisite.
Separate estimate requires scoping parser bounds, retention and diagnostics.

The signer checks full parents before signing. The coordinator verifies the result, strips parents
and sends. Each node checks signatures and consults its backend. Choose one option:

1. **Accept absence; verify supplied parents (recommended).**
2. Accept absence; ignore supplied parents beyond syntax validation.
3. Require full parents; reject absence, requiring a stripping-rule decision.
4. Refuse-when-present; accept absence, subject to other checks and the replay limitation above.

Reliance: CHN-22/23, CHN-24–26, OPR-24/35/45/46, SPN-3/5/21/23/25–27,
API-4/5/6/13/25, NCH-10/19/21, POL-6/7;
[ADR-0012](../adr/0012-model-b-spend-and-duress-architecture.md#transactions-and-exact-byte-identity),
“User signs first” and “Nodes validate the escape; they do NOT build it”;
[ADR-0013](../adr/0013-concrete-protocol-schemas.md), “It does not define a second protocol contract”.
Which node-admission option do you choose?
