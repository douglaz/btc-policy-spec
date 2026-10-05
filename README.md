# btc-policy — specification set

A language-neutral specification for a self-hosted Bitcoin **soft vault**: a user key plus a
`t`-of-`n` federation of policy-enforcing signer nodes, with a timelocked recovery path, a silent
duress response, and a node-to-node channel that assembles and broadcasts every spend. It runs on
today's consensus rules — standard P2WSH Miniscript, no covenants.

This directory contains **specifications only**, with one carve-out: `tools/` holds the gates that
check the specifications, and `.github/workflows/` runs them. Nothing that implements the specified
system belongs here. The set was extracted on 2026-09-09 from a Rust reference implementation
(`btc-policy-rust`) and then extended past it; it is written to stay ahead of every implementation.
It does not record what any implementation has or has not built — that is tracked in each
implementation's own repository (`OVR-17`). Where an implementation and this set disagree, one
of them is wrong, and `16-open-findings.md` is where an unresolved design question lives.

## Gates

`flake.nix` pins the toolchain the gates need — Lean 4.30.0 for the formal layer and the Python
with the vector gate's two libraries — so the one command is:

```sh
nix develop --command bash tools/check-all.sh
```

It runs the gates listed below, and CI runs the same script on every push. A missing toolchain is
a red gate, not a skipped one.

| Gate | What it refuses |
|---|---|
| `tools/check_formal.sh` | A formalized clause whose proof does not hold. Runs first; the gates below that read what it writes are named in `check-all.sh`. `tools/formal/` carries formalized clauses as Lean definitions tagged `@[req]` with the identifier each formalizes, their properties as theorems over every input, and the historical defects as executable exhibits (`ADR-0023`); the requirement index `lake exe gate` emits, one line per tagged declaration, is the list of what is carried. `lake build` refuses a theorem that no longer proves; `lake exe gate` refuses, for every constant of every project module, tagged or not, `Explore` included, a dependency on any axiom beyond `propext`, `Classical.choice` and `Quot.sound` — so a `sorry` and a `native_decide` are red anywhere — and an `axiom` written or minted; it refuses a tagged declaration inside `Explore`, a tag that is not an identifier or that names a `CNF` item, and an empty index; `leanchecker --fresh` replays every declaration through the kernel; the wrapper refuses a module the build never imports (reachability read through `lean --deps`), a Lean file outside `BtcPolicy/` and the four roots, an executable root that is not one import and one `main`, a `CNF` identifier anywhere in the tree, and an `implemented_by`, `extern` or `csimp` attribute; `lake exe render` and `lake exe values` write the marked regions and emitted values the last two gates read. *`sorry` is why the axiom check exists: `lake build` stays green over one, which is `DEF-16`'s green check with a `.lean` suffix.* |
| `tools/check_ids.py` | A duplicate identifier, a citation to an id nothing defines, a gap in a namespace's sequence, an id far above its neighbours, a reference to an ADR that does not exist, a `@[req]` tag naming an id nothing defines |
| `tools/check_fixtures.py` | A JSON example that does not parse, carries a `...` placeholder, repeats an object member, exceeds the integer bound, or carries a malformed identifier, compressed pubkey, or BIP174 PSBT structure. Parses every descriptor-bearing field: a BIP380 checksum that does not verify, a key that is not 66 lowercase hex or not a point on secp256k1, and Normal-branch keys out of canonical node order. Also structurally checks every Mermaid diagram |
| `tools/check_obligations.py` | A duty assigned to another requirement's subject — "`X` MUST write `y`" — where `X`'s own text names none of the machinery |
| `tools/check_coverage.py` | A fall in the number of requirements exercised by at least one conformance item, against a recorded baseline |
| `tools/check_citations.py` | A quoted attribution to a requirement that does not contain the quote — verb (`` `X` says "…" ``), possessive (`` `X`'s rule that "…" `` or `` `X`'s "…" ``) or colon (`` `X`: "…" ``) form, with straight or curly quotation marks, each quote held to the attribution it follows — and any NEW unquoted "`X` says …" against a recorded baseline, in root Markdown, `docs/adr/*.md`, or a Lean docstring under `tools/formal/`, where a docstring nesting a `/- -/` block comment is refused rather than read past, and a quotation whose nested straight quotes cut it into spans the gate reads outer to outer and finds whole in the body — write the inner quotes curly; and a backticked `BtcPolicy.*` name that the requirement index does not carry — a renamed declaration's dangling citation. Requirement bodies come from root Markdown; ADRs are attribution sources, never alternative quotation evidence. Explicitly cited root documents retain their existing quotation exception |
| `tools/check_vectors.py` | A published byte vector whose framing or digest does not reproduce, or a key-derivation, descriptor-normalization, commitment or witness-weight fixture whose fields do not produce its expected bytes. The witness-weight check SERIALIZES the script and a maximum-length witness and measures them, so it catches a framing error rather than agreeing with one. Sources: `08-wire-contract.md` and `tools/protocol-vectors.json` |
| `tools/check_copies.py` | A figure inline in a requirement — `CHN-4`'s `older(4224679)`, `POL-20`'s `(2 − 1/t)`, `SPN-38`'s cap formula — or restated anywhere else in the set, another requirement, a conformance item, an ADR, this README, that differs from the value its declaration emits (`ADR-0023` decision 5); and a restatement that stops matching, by a hit-count ratchet. Reads every operand out of the owning sentence with the regexes the arithmetic gate used and fails closed on unrecognised wording. *A theorem over Lean-side constants reads nothing of the document; this is what keeps the document bound to the rule the theorem proves.* It replaces `tools/check_arithmetic.py` (2026-09-09 to 2026-09-16), whose derivations are now theorems and whose two tables are now regions |
| `tools/check_regions.py` | A marked region — the lines between `<!-- formal: BtcPolicy.Render.… -->` and `<!-- /formal -->` — that is not what its declaration emits (`ADR-0023`): `SPN-38`'s boundary table and `ADR-0014`'s timeline, compared line for line, and `--write` regenerates them; `SPN-5`'s gate table, whose three decided columns are compared cell by cell as a `match` region. Also refuses a region naming a declaration the index does not carry, one sitting in a requirement other than the one its declaration is tagged with or in an ADR other than its `home`, and an emitted region no document renders |

The workflow also breaks a document deliberately on every run and asserts each gate that can be
broken rejects it. The reference implementation's launch gate once ran red for dozens of
consecutive runs before anyone noticed (`DEF-16`, `OPS-67`); a green check that asserts nothing
is worse than no check.

## How to read this

| Document | Contents |
|---|---|
| `executive-summary.md` | **Start here if you are new.** One self-contained orientation: what the vault is, the decisions everything follows from, why silence is the design's centrepiece, what is hard, and what has and has not been validated |
| `00-overview.md` | Problem statement, design goals, system context, non-goals |
| `01-domain-model.md` | Entities, roles, keys, transaction classes, the state each node holds |
| `02-onchain-contract.md` | The descriptor template, the recovery timelock, sighash rules, the commitment, transaction classes |
| `03-policy-checks.md` | The pure per-node PSBT checks and the Hot budget, in evaluation order, with every refusal |
| `04-spend-lifecycle.md` | Ingress, the coordinator nonce log, candidates, the Hold, release and combine, refresh, the pending projection |
| `05-duress-and-lockdown.md` | The two-track duress state machine: arm, confirm, freeze, `T`, Lockdown, the best-effort sweep and its fee ladder |
| `06-node-channel.md` | Identity, envelopes, freshness, quotas, message types, the Carrier and its clock authority |
| `07-node-api.md` | The node's HTTP surface: `/sign`, `/channel`, `/events`, `/healthz`, `/pending` |
| `08-wire-contract.md` | JSON bodies, canonical byte encodings, tagged hashes, and the frozen vectors the gate executes |
| `09-manifest-config-ceremony.md` | The manifest and its preimage, node configuration, key derivation, and the setup ceremony |
| `10-watchtower-and-chain.md` | The chain backend contract, the watchtower, reorg handling, fee signals |
| `11-state-and-persistence.md` | What a node holds, where, and what survives what: RAM-only state and reboot-death |
| `12-security-requirements.md` | The threat model, the load-bearing invariants, and the residual risks, as requirements |
| `13-operations-and-rollout.md` | The runbook, the rollout ladder and its gates, deployment (transport, hosts, images), migration, key custody, the freeze, the review, the alpha, dependency policy |
| `14-known-defects.md` | Defects found in the reference implementation, as prohibitions |
| `15-conformance-checklist.md` | What a reimplementation must demonstrate before it holds funds |
| `16-open-findings.md` | **Read this before building.** The design questions that are still open, who decides each, and the three questions a builder must ask first |
| `17-operator-program.md` | The coordinator-side program: the sealed-artifact substrate, the user-signer seam, the composer, and every command with its delivery and watch semantics |
| `CONTEXT.md` | Glossary. Which word means what, and which words are banned |
| `docs/adr/` | The decisions, and what was rejected to reach them |

Read `00`, `01`, `05` and `06` first. `05` is the heart of the design — the two-track duress
machine and its treatment of silence is what distinguishes this from a policy co-signer, and it is
the part an implementation is most likely to get wrong by adding one innocent field.

## The decisions this specification is built on

They live in `docs/adr/`, and each records what was rejected. `0001`–`0017` are numbered as the
reference project numbered them; the first eleven are short decision records from July 2026, and
`0012` consolidates and supersedes earlier design decisions and is the one to read for their
rationale. From `0018` the numbering continues here, for decisions this specification set made on
its own. The numbered
requirements own the current implementation contract; ADRs preserve decisions and rejected
alternatives. An imported ADR's historical implementation instructions do not override those
requirements. For wire-shape precedence, see the introduction to `08-wire-contract.md`.

| ADR | Decision |
|---|---|
| `0001` | Vault nodes are the watchtower; recognition is by validation, not co-signing (revised by `0012`) |
| `0002` | Alerts are pulled by the coordinator, never pushed |
| `0003` | The key-independence matrix; escape ⊥ user is load-bearing for the entire duress guarantee |
| `0004` | The Hold: an off-chain unvault period; the escape sweep is the implicit cancel (signing shape revised by `0012`) |
| `0005` | Nodes are sealed after setup: no admin path, no reset, no upgrade in place |
| `0006` | The 10% fee cap is a bug guard, not a security control (refresh excepted) |
| `0007` | A rebooted node is a dead node; everything runs from tmpfs |
| `0008` | Duress PINs and Lockdown (mechanism consolidated into `0012`) |
| `0009` | No correlation class may reach quorum (waived for rollout stages 2–5 by `0015`) |
| `0010` | The coordinator is a relay; nodes assemble and broadcast (consolidated into `0012`) |
| `0011` | The node-to-node channel carries signatures and assembly, never policy |
| `0012` | **Model B**: node-assembled spends, the two-track duress machine, Carrier clock authority, the accepted residuals and their design rationale |
| `0013` | Schema decisions and links to the current owners: descriptor template, requests, transaction classes, manifest, config, refresh bounds, the PIN budget |
| `0014` | The Hot budget: a per-transaction cap and a rolling-window velocity cap, manifest-sealed |
| `0015` | Rollout funding caps, and a test-only waiver of `0009` for stages 2–5 |
| `0016` | The escape fee ladder is sealed per vault and opt-in, default zero |
| `0017` | One external human review, at rollout stage 9, gating the lift of the dust caps |
| `0018` | The refresh bounds are sealed at schema revision 4; the PIN attempt budget is not |
| `0019` | Refresh age is read from the chain by median-time-past; a node keeps no refresh log |
| `0020` | Every confirmed duress Escape is selected and gated on its own; the sweep never picks one |
| `0021` | The compromise-and-loss matrix (`SEC-54`): five outcome words, and the cases the set does not defend |
| `0022` | The escape class is pin-less: the claw-back is one request, no vault change, and the two-leg shape goes |
| `0023` | A formalized clause lives in Lean under `tools/formal/`, the Markdown renders it, and a proof is never conformance; the copies gate compares every inline figure to what the declaration emits |

**Read `ADR-0012` before `05-duress-and-lockdown.md`**, and read its "Accepted residuals" section
before treating any silence or theft claim as settled.

## How much to trust this

Every requirement here wears the same costume — a MUST, a stable identifier, a conformance item.
**The confidence behind them is not uniform, and the formatting hides that.**

- **The node protocol (`02`–`12`) was extracted from a running implementation** exercised on
  every push by unit, property and decoder-robustness suites, a live-regtest adversarial harness
  and a bitcoind-backed leg, and one honest spend on a public chain. Those documents have the
  most evidence behind them.
- **The operator program (`17`) and the deployment half of `13` are written ahead of any
  implementation**, from decisions recorded in the reference project's tracker. They are
  decisions, not observations; an implementer will find gaps and should file them as findings.
- **Any harness can be blind to a fault it does not construct** (`DEF-15`). Read a green
  scorecard as evidence about the properties its scenarios construct, not about the ones they
  do not.
- **The least-reviewed documents are identifiable.** `14`, `15` and `17` were written once, on
  2026-09-09, and have not yet been read against a second implementation. Weight accordingly.

**A green conformance checklist certifies the requirements that are written down.** It says
nothing about what is missing, and what is missing is by construction whatever nobody has noticed
yet. `F14` records how the reference project's own documents drifted, and the gates above exist
because reading did not catch it.

## Requirement conventions

Requirements use RFC 2119 keywords: **MUST**, **MUST NOT**, **SHOULD**, **SHOULD NOT**, **MAY**.
Each is tagged with a stable identifier so it can be cited in code review, tests, and issue
trackers:

| Prefix | Domain |
|---|---|
| `OVR-n` | Overview and scope |
| `DOM-n` | Domain model |
| `CHN-n` | On-chain contract: descriptor, timelock, sighash, commitment, classes |
| `POL-n` | Policy checks and the Hot budget |
| `SPN-n` | Spend lifecycle: ingress, nonces, candidates, Hold, release, refresh |
| `DUR-n` | Duress, arming, Lockdown, the sweep |
| `NCH-n` | The node channel and the Carrier |
| `API-n` | The node HTTP API |
| `WIR-n` | Wire contract, encodings, vectors |
| `MAN-n` | Manifest, configuration, key derivation, ceremony |
| `WTC-n` | Watchtower and chain backend |
| `STO-n` | State and persistence |
| `SEC-n` | Security requirements and residuals |
| `OPS-n` | Operations, rollout, custody, dependencies |
| `DEF-n` | Defect prohibitions |
| `CNF-n` | Conformance checklist items |
| `OPR-n` | The operator program |

Findings in `16-open-findings.md` are `F1`… and are not requirements. Their numbers are
append-only too; a finding that closes is listed as withdrawn there, never renumbered.

### Identifiers are append-only. Text is not.

An identifier is never reused and never renumbered. This costs nothing and is what makes a citation
durable across seventeen documents, commit messages and future tests.

Withdrawn wording is retained only where a trap sits behind it — something that looked correct,
was nearly built, and broke. Withdrawn wording that merely records a fact that changed is deleted
outright. The reference project kept every correction inline with a dated tag, and its documents
became hard to read for exactly that reason. Decisions and retained arguments have their owners
in `docs/adr/` and the requirements; the history they replaced lives in non-normative
`docs/archive/`, whose README lists what it holds, and which no gate reads. Finding identifiers remain in the withdrawn
list in `16-open-findings.md`.

**Deleting the text is not reusing the number.** The gap in the sequence is the tombstone. A
deleted identifier goes in the index below so an old citation still resolves, and
`tools/check_ids.py` reads that index.

### A decision gets its identifier when it is accepted, not when it is written

When a decision is accepted, name the identifier that will carry it — the requirement it amends,
or the next free number in the right namespace. An accepted decision with no identifier has nothing
to search for, and the gates cannot help.

### Cite the code by identifier, never by line

The reference implementation is named by crate, module and function — `vault-node`,
`channel::confirm_carrier` — never by `file.rs:NNN`. Line numbers in the reference project's own
documents went stale within days of being written.

### Withdrawn identifiers

Deleted from the documents. Never reused. Listed so an older citation still resolves.

| Identifier | Was | Why it went |
|---|---|---|
| `SEC-52` | "One honest signet spend is the extent of real-chain evidence" | Implementation status, which this set no longer records (`OVR-17`); `SEC-51` states the rule |
| `CHN-33` | "An escape-class spend's mandatory Escape MUST be a distinct transaction with an input set disjoint from the spend's" | The escape-class spend and its residual went with `ADR-0022`; the claw-back is `CHN-35` |
| `SPN-40` | "An escape-class spend completes at its ingress time under either PIN" | `ADR-0022`; the claw-back path is `SPN-50` |
| `DUR-17` | "An escape-class spend completes immediately under either PIN, and under duress the node ADDITIONALLY schedules the residual sweep" | `ADR-0022`; the armed node's treatment of a claw-back is `DUR-36` |
| `OPR-26` | "A signer MUST approve every otherwise-valid escape-class pair" | `ADR-0022`; the one Spend shape and the Clawback arm are `OPR-25` |
| `OPR-70` | "A post-wrench coordinator can swap the two escape-class positions" | `ADR-0022`; there is no pair to swap, and `SEC-21` lists the remaining powers |
| `OPR-71` | "The ordinary Spend consolidates the vault to exactly one change coin, so after that spend confirms `escape` is structurally unavailable" | `ADR-0022`; a claw-back sweeps one coin (`CHN-35`) |

## Language and runtime

Nothing in this specification assumes a particular language, HTTP framework, JSON library or
async model. The reference implementation is Rust with a Tokio/axum node and a synchronous
coordinator; none of that is required. Interoperability depends on the contracts indexed above,
including the wire encodings, HTTP schemas, descriptor template, descriptor canonicalization
and key derivation. Their owners are `02-onchain-contract.md`, `07-node-api.md`,
`08-wire-contract.md` and `09-manifest-config-ceremony.md`; the evidence belongs in
`15-conformance-checklist.md`.

Two runtime properties are load-bearing and hard to reproduce casually: every node's mutable state
is RAM-only and dies with the process (`11-state-and-persistence.md`), and the memory-hard KDF for
PINs and node keys is Argon2id with the parameters the manifest and config fix
(`09-manifest-config-ceremony.md`). An implementation that persists what this set says must not
persist, or that evaluates one Argon2 where this set says two, is not a weaker implementation; it
is a different system with the duress guarantee removed.

## Status

These documents describe a target system. Which parts of it a given implementation reaches is
recorded in that implementation's repository, not here (`OVR-17`); what remains undecided in
the design is `16-open-findings.md`. No external human has reviewed the design (`F18`).
