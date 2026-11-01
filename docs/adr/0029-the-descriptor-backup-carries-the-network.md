# The descriptor backup carries the network

Status: accepted 2026-11-01. Specification-repository decision by the specification owner.
Closes `F67`.

## Decision

Record the network next to the full vault descriptor in the descriptor backup (`OPS-23`).
Its machine-readable artifact is `descriptor-backup.json`, emitted by `assemble` (`MAN-29`)
and regenerated from verified state by `finalize` as `backup/descriptor-backup.json`
(`MAN-33`). The no-manifest readers consume that single file (`OPR-74`).
Without a manifest, balance, maturity reporting and recovery take their expected network from
that backup and check backend chain identity before other chain reads (`OPR-74`, `WTC-3`).
A missing or unsupported network is refused; a backend identity mismatch fails visibly before
recovery signing or broadcast. The accepted values remain `MAN-14`'s.

The backup remains one artifact. Requiring a manifest was rejected: recovery must work when
only the promiscuous descriptor backup and a chain view survive (`OPR-74`). Inferring the
network from the descriptor cannot supply this metadata: `MAN-14` states that network
"changes no key derivation and no scriptPubKey". Thus an incorrect backup value cannot
redirect the intended chain's coins to another chain. The identity check compares the backend
to the backup; it does not independently authenticate the backup value. A wrong value paired
with a backend reporting that same value is not a detectable identity mismatch. `WTC-3`'s
existing chain-identity residuals still apply. Independent evidence failures remain governed
by `OPR-82`; no unconditional detection of a mislabeled backup is claimed.

Landed at `OPS-23`, `OPS-26`, `MAN-29`, `MAN-33`, `OPR-12`, `OPR-62`, `OPR-74`,
`CNF-125`, `CNF-126` and `CONTEXT.md`.
