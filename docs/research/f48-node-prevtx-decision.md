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

| Input / consequence | Accept absence, verify supplied (recommended) | Accept absence, ignore supplied | Require full parents, verify supplied |
| --- | --- | --- | --- |
| Absent | Pass | Pass | Refuse |
| Present-consistent | Pass | Pass | Pass |
| Present-malformed encoding | Decode error | Decode error | Decode error |
| Present-inconsistent | Refuse | Pass parent check | Refuse |
| Changed rule / cost / unknown | SPN-25 conditional checks; parsing/hash/comparison work; sublimit/retention pending | SPN-25 non-authority rule; syntax work; syntax/retention details pending | Presence requirement; transport/retention cost; wire redesign unresolved |

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

Later acceptance cases: stripped, matching, malformed, wrong txid, vout out of range, witness
mismatch, backend mismatch, backend absent/unconfirmed, fetch failure, network mismatch.
Update record/F48 disposition afterward; no extra review prerequisite.
Separate estimate requires scoping parser bounds, retention and diagnostics.

The signer checks full parents before signing. The coordinator verifies the result, strips parents
and sends. Each node checks signatures and consults its backend. Choose one option:

1. **Accept absence; verify supplied parents (recommended).**
2. Accept absence; ignore supplied parents beyond syntax validation.
3. Require full parents; reject absence, requiring a stripping-rule decision.

Reliance: CHN-22/23, CHN-24–26, OPR-24/35/45/46, SPN-3/5/21/23/25–27,
API-4/5/6/13/25, NCH-10/19/21, POL-6/7;
[ADR-0012](../adr/0012-model-b-spend-and-duress-architecture.md#transactions-and-exact-byte-identity),
“User signs first” and “Nodes validate the escape; they do NOT build it”;
[ADR-0013](../adr/0013-concrete-protocol-schemas.md), “It does not define a second protocol contract”.
Which node-admission option do you choose?
