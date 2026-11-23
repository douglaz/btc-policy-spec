# Milestone 3 baseline

Pinned baseline and local `origin/main`: `8b123b35ce3ae69f793f99f72781db15f902683a`.
This is a source-reading card. No fresh validation, build, proof check, gate, linter or test was run.

**Proved under stated premises.** The [current composed-domain table](proof-boundaries.md#the-current-composed-domain)
reads `Lifecycle.Execution`; the expiry-aware extension is `ReceiptLifecycle.Execution`
([section 30](proof-boundaries.md#30-the-expiry-aware-receipt-on-the-lifecycle-run)). On that extension,
`ReceiptLifecycle.no_send_until_birth` takes `Registration.preserve`, an honest receiver and no birth under the
evicted id there: eviction leaves no admitted send under it until a birth.

The repaired base obeys release accounting on `LadderRelease`, the lifecycle run and the expiry-aware extension
([sections 26](proof-boundaries.md#26-the-release-quota-at-each-pass) and
[32](proof-boundaries.md#32-the-release-quota-on-the-expiry-aware-lifecycle-run)).
`ReceiptQuota.starved_silent_layer` takes a run, an honest node, `Registration.preserve`, an admitted fire or
ladder pass, a resident candidate and zero affordable rungs: neither pass queues its base or other rows.
`ReceiptQuota.pass_quota_layer` takes an admitted ladder pass, a resident Escape-role record and equal input counts
above the base. `ReceiptQuota.base_once_layer` takes a run, an honest node, `Registration.preserve` and no birth
under the id after the first base release.
This is per-candidate accounting, not a shared peer-rate bound: `Exhibits.ReceiptQuota.no_shared_limit` remains.

Receipt-only SILENCE: `LifecycleSilence.xvfed_silence` compares `LifecycleSilence.XVObs` under one labelled schedule,
samples included, starting `VariantSilence.VCoupled` and both `FedSilence.FInv`, with marker `committed`, traversal
`always`, dynamics `dynamic`, registration `preserve`, and close/driver time `ratchet`. It stops at the concealment
horizon; the lifecycle's rung, assembly, send and chain steps remain outside
([section 31 and its assumption ledger](proof-boundaries.md#31-silence-over-the-receipt-step-on-one-domain)).

`ReceiptPossession.possession_window` takes `ReceiptLifecycle.Fresh`, `Registration.preserve`, distinct contributor
keys, an honest receiver key outside them, threshold `t ≤ S.length + 1`, nonempty transaction inputs, admitted and
ready passes, pass/delivery service windows, delivery chain views, matching envelope labels and receiver retention.
Its endpoint is Held quorum in slots, not seconds; no submission or inclusion follows
([section 33](proof-boundaries.md#33-possession-on-the-expiry-aware-lifecycle-run)).

Exposed-authority counterexamples remain: `Exhibits.EarlierRelease.linked_preserves_prior_quorum`,
`Exhibits.EarlierRelease.deleted_candidate_retains_authority` and `Exhibits.EarlierRelease.exposure_without_possession`
([retained counterexamples](proof-boundaries.md#counterexamples-that-must-stay-counterexamples)).

**Specified but unproved here.** Shared peer quotas, retry scheduling, whole-lifecycle SILENCE, serialized bytes and
timing remain outside these results; see [the second milestone's residuals](proof-boundaries.md#the-second-milestones-review).

**Formal-model inputs or external assumptions.** Backend truth, observations, feerates and package verdicts are inputs;
authenticated senders/signers and cryptographic binding are not derived from bytes. Feasibility wire-size inputs are
assumptions, not deployment measurements ([current domain](proof-boundaries.md#the-current-composed-domain),
[section 9](proof-boundaries.md#9-fast-exit-feasibility)).

**Open policy choice.** The [selected findings and task reconciliation](milestone-3-triage.md) adopt no policy.
Next question, F48: at node ingress, must a missing full previous transaction be refused, ignored as a field, or
verified when present, while preserving the user-signer contract and the post-signing stripped wire—or does an
explicit amendment need an owner decision?
