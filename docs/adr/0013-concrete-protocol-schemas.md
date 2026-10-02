# Concrete protocol schemas (requests, commitment, classes, manifest, config)

Status: accepted 2026-07-15; implementation instructions superseded by the numbered
requirements on 2026-09-09. This record preserves the decisions and rejected alternatives
behind the schemas. It does not define a second protocol contract. Current requirement owners
are listed in each section; the byte encodings and fixtures live in
[08 — Wire contract](../../08-wire-contract.md).

Companion: [ADR-0012](0012-model-b-spend-and-duress-architecture.md), the Model-B design record.

## 1. Vault descriptor template

Current owners: `CHN-1`–`CHN-8` in [02 — On-chain contract](../../02-onchain-contract.md).

The decision was to use one fixed vault template. A general policy compiler at setup was
rejected because selecting an equivalent script independently can change witness construction,
branch recognition, and vault identity. The earlier policy sketch using `thresh` was not the
concrete descriptor and must not be used to construct one.

Ranged vault keys were also rejected: the node-key ceremony creates one signing key per node,
and the reference node loaded concrete public keys for its witness script. A setup that
accepted a ranged vault could seal a descriptor its nodes could not load. Destination wallets
have a different purpose; their address derivation is governed by `POL-4`–`POL-5`.

The federation-shape argument has its home in `CHN-2`; it is not restated here.

## 2. Tagged request schema

Current owners: `WIR-4`–`WIR-7`, `WIR-21` in
[08 — Wire contract](../../08-wire-contract.md), and the request lifecycle in
[04 — Spend lifecycle](../../04-spend-lifecycle.md).

Separate Spend and Refresh variants removed the ambiguity of a PIN-bearing request that was
actually a self-spend. Mandatory Escape material closed escape stripping; the optional ladder
later made fee adaptation possible without granting the nodes additional signing authority.
The rejected earlier request shape lacked coordinator authentication and freshness fields.

The coordinator-authentication domain includes vault identity to prevent a request signed with
a reused coordinator key being accepted across vaults. A signature protects against a relay
altering the request; it does not stop the coordinator itself from editing and re-signing it.
The ladder-stripping consequence is recorded in [ADR-0016](0016-the-escape-fee-ladder-is-sealed-and-opt-in.md).

## 3. Transaction-class predicate

Current owners: `CHN-30`–`CHN-33` in [02 — On-chain contract](../../02-onchain-contract.md),
with policy evaluation in [03 — Policy checks](../../03-policy-checks.md).

Classifying from a coordinator label was rejected because class controls the release path.
Treating a mixed Hot/Escape payment as an Escape would allow a small escape output to disguise
a Hot payment. The predicate and its rationale belong to the current owners above, including
how they distinguish destination outputs from vault change.

## 4. Per-vault manifest

Current owners: `MAN-1`–`MAN-6` in
[09 — Manifest, configuration, and the ceremony](../../09-manifest-config-ceremony.md).
The manifest preimage field list has one home, `MAN-2`; its worked vector is `WIR-27`.

The ceremony was chosen as the trust bootstrap. No external signing authority is introduced:
the witnessed setup establishes the manifest anchor that subsequent node and coordinator
identity checks use. Endpoints are included in that trust relationship to prevent later
redirection of a peer.

Including endorsements in the hash they sign, or including a config hash when the config
already contains the manifest hash, was rejected because either creates a circular definition.
Missing manifest anchors were rejected because a federation whose configs all omitted the
anchor could appear internally consistent without any evidence of ceremony agreement.

The manifest seals classification inputs alongside the Hot-budget parameters: agreement on a
number is insufficient if nodes disagree about which outputs consume it. The budget argument
belongs to [ADR-0014](0014-hot-spend-bound.md) and its normative owner `POL-20`.

## 5. Policy config schema

Current owners: `MAN-7`–`MAN-14` and `MAN-16`–`MAN-19` in
[09 — Manifest, configuration, and the ceremony](../../09-manifest-config-ceremony.md).

A config containing the signing secret was rejected in favor of public derivation parameters
and a preimage supplied only during initial startup. This fits the one-shot lifecycle decision
in [ADR-0007](0007-node-death-on-reboot.md); it does not create a restart or key-recovery path.

Explicit required fields distinguish an omitted setting from a later opaque hash mismatch.
Unknown-field rejection also makes stale config recipes visible, which is why this ADR no
longer carries a second TOML schema.

## 6. Precise numeric definitions

Current owners: `DUR-22`–`DUR-30` in [05 — Duress and Lockdown](../../05-duress-and-lockdown.md),
`SPN-46`–`SPN-47` in [04 — Spend lifecycle](../../04-spend-lifecycle.md), and the configuration
bounds in [09 — Manifest, configuration, and the ceremony](../../09-manifest-config-ceremony.md).

Measuring escape coverage by input value was rejected because it could count value lost to
fees as delivered recovery value. A node-local mempool fee signal was rejected because differing
readings could cause honest nodes to select incompatible rungs. The current coverage and
fee-selection arguments, including accepted residuals, belong to the owners above.

Refresh received separate rate and fee controls because a self-spend that bypasses the Hold
would otherwise provide a repeated fee-burning path. Defaults and formulas are kept in their
owning requirements rather than copied into this record.

## 7. Attempt budget and coordinator auth-key lifecycle

Current owners: `MAN-21`–`MAN-23` in
[09 — Manifest, configuration, and the ceremony](../../09-manifest-config-ceremony.md),
`STO-1`–`STO-4` in [11 — State and persistence](../../11-state-and-persistence.md), and `OPS-9`
in [13 — Operations and rollout](../../13-operations-and-rollout.md).

Transient PIN lockout and terminal Lockdown were kept distinct because they answer different
conditions. The PIN budget's lifetime follows the node-lifecycle decision; a restart design
would require a separate durability decision rather than merely restoring the key.

Coordinator-key loss and rotation were made ceremony concerns because the coordinator's public
key is part of the vault's trust anchor. The current operational procedure belongs to `OPS-9`.

## Open findings

The extraction's current unresolved work is indexed in
[16 — Open findings](../../16-open-findings.md). The earlier V0 task list is historical and
is not an alternative list of current implementation obligations.
