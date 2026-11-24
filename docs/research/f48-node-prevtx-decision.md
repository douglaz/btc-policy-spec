# F48 node admission: decision pending

Analysis complete; **needs an owner decision**. F48 open; no policy/implementation adopted.
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
