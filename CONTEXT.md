# btc-policy

A self-hosted Bitcoin soft vault. The **Operator** holds a user key and runs a `t`-of-`n`
**federation** of policy-enforcing signer **nodes**; a **coordinator** composes and relays
spends; a second, distinct **duress PIN** silently sweeps the vault to an independent escape
wallet and locks the federation down.

This file is a glossary. It contains no design decisions — those live in `docs/adr/` — and no
requirements — those live in the numbered specification documents. Each entry names the
requirement that owns the rule the word stands for.

## Language

### People and machines

**Operator**:
The human who runs a vault: funds it, authorizes spends, watches alerts, drives Recovery
(`DOM-1`). Distinct from the user key they hold and from the coordinator, which is a program.
_Avoid_: user (when the human is meant), admin (a sealed host has no admin), owner

**Coordinator**:
The program that operates the user key, composes transactions, signs requests with the
coordinator auth key, relays them to every node, and pulls alerts. Trusted until the wrench,
untrusted after (`DOM-2`, `DOM-3`). Never assembles, finalizes, or broadcasts.
_Avoid_: server, orchestrator, wallet app, assembler

**Vault node**:
A daemon holding exactly one federation key and one policy engine; validates every request
independently, signs at ingress, performs watchtower duty (`DOM-5`–`DOM-7`).
_Avoid_: signer (alone), server, peer

**Federation**:
The `n = 2t − 1` vault nodes collectively (`DOM-8`). Policy-isolated, not network-isolated.
_Avoid_: cluster, cosigners

**Quorum**:
Any `t` of the `n` nodes. Every quorum has run the policy checks by construction.
_Avoid_: majority, threshold (as a noun for the group)

**Node id**:
A node's zero-based position in canonical node order — lexicographic over the full key
expression (`CHN-7`). A total bijection from the descriptor, never a table or a label.
_Avoid_: node name, node index (alone), peer id

**Sealed host**:
A node host with no SSH, no administrative path, no reset, no reconfiguration, no upgrade in
place; a reboot kills the node (`ADR-0005`, `STO-1`).
_Avoid_: hardened host (weaker), locked-down (that is Lockdown)

### The vault and its keys

**Vault**:
One wallet with two spend paths defined by one descriptor (`CHN-1`); identified by
`wallet_id` (`CHN-6`).
_Avoid_: wallet (alone), safe, cold storage

**Normal path**:
The branch needing the user key plus a quorum of node signatures; every spend through it is
policy-checked.
_Avoid_: primary path, spend branch

**Recovery path**:
The branch needing 2-of-3 recovery keys after the relative timelock (`CHN-4`, `CHN-10`). The
fallback exit: loss, inheritance, a stuck vault, and the only exit after Lockdown (`OPS-26`).
_Avoid_: emergency path, backup path

**User key**:
The Operator's own key, mandatory on every Normal-path spend; hardware in production, software
in every current driver (`SEC-43`).
_Avoid_: owner key, master key

**Recovery keyset**:
The 2-of-3 cold keys of the Recovery path; distributed socially, doubles as inheritance
(`DOM-12`).
_Avoid_: recovery wallet, cold keys (alone)

**Escape wallet**:
An offline wallet, preferably multisig with single-sig accepted, allowlisted at setup, whose
only job is receiving sweeps (`DOM-11`). Keys independent of every other role — load-bearing, not
hygiene.
_Avoid_: cold wallet (alone), backup wallet, panic wallet

**Escape-wallet cosigner**:
One key participant in the escape descriptor, identified in the ceremony bundle (`MAN-26`) and
checked individually (`MAN-28`). This term includes the sole participant of a single-sig escape.
_Avoid_: federation node, node quorum

**Hot wallet**:
The Operator's day-to-day wallet; an allowlisted destination and the declared risk budget
(`DOM-14`).
_Avoid_: spending wallet, mobile wallet

**Coordinator auth key**:
The key that signs every request; its public half is pinned in the manifest (`SPN-7`,
`MAN-2`). Loss bricks the Normal path (`SEC-36`).
_Avoid_: coordinator key (ambiguous with the channel key), API key

**Channel key**:
A node's per-process key, derived from its signing key, that signs every channel envelope
(`NCH-4`); endorsed in the manifest by the signing key (`MAN-6`).
_Avoid_: transport key, session key

**Preimage**:
The 63-bit operator-held value from which a node derives its signing key at start, printed
once on paper and destroyed after sealing (`MAN-16`, `MAN-36`).
_Avoid_: seed, passphrase, node password

### Policy words — always qualify

**Spending policy**:
The on-chain rules in the descriptor, enforced by consensus; a fixed hand-written template
(`CHN-1`), never compiled at runtime.
_Avoid_: script (alone), contract, compiled

**Policy checks**:
The off-chain PSBT checks every node runs before signing (`03-policy-checks.md`).
_Avoid_: rules, validation (alone)

**Policy config**:
The per-node TOML file (`MAN-7`). Written once, immutable forever.
_Avoid_: settings, policy file, unqualified "policy"

**Manifest**:
The immutable per-vault record, hash-pinned, distributed to every node (`MAN-1`, `MAN-2`).
The root of channel and coordinator trust. Any change is a new vault.
_Avoid_: config (that is Policy config), registry, membership file

**Federation-uniform**:
A value whose divergence leaves NO request the coordinator could compose that reaches quorum
across it (`MAN-2`). A value that merely makes some nodes refuse a given request is node-local
admission, because a different request still passes — divergent `delivery_horizon_secs` is
answered by a longer expiry, divergent `policy_version` by nothing at all. Sealing is one
enforcement of uniformity, never a synonym for it, and a value may be sealed as shared policy
without being uniform by necessity.
_Avoid_: sealed (that is the mechanism), shared, global, consistent, agreed

**Allowlist**:
The sealed set of permitted destination wallets — descriptors with a bounded index, never
fixed addresses (`POL-10`). Contains at least the hot and escape wallets.
_Avoid_: whitelist, address list

**Hot budget**:
The sealed per-transaction cap and rolling admission ledger for hot-class spends.
`POL-20` states: "The Hot budget provides an **acceptance-time admission bound**, not a rolling
completion-loss bound."
_Avoid_: spend limit, rate limit (that is the PIN budget)

**Ceremony**:
The one-time setup that produces a vault and ends with its hosts sealed (`MAN-24`–`MAN-38`).
Every question is asked exactly once, of the Operator.
_Avoid_: setup (when the sealed event is meant), provisioning, onboarding

### Transactions

**Transaction class**:
Hot, escape or refresh, derived by each node from the spend's outputs (`CHN-30`). Mixed is
refused.
_Avoid_: destination type, output kind, spend purpose (the non-authoritative hint)

**Escape**:
The mandatory second transaction in every SpendRequest: a user-signed sweep of the vault to the
escape wallet, carried whether or not anything is wrong (`DOM-18`, `CHN-14`).
_Avoid_: panic tx, sweep (alone), escape wallet (that is where it pays)

**Escape fee ladder**:
The optional pre-signed set of higher-fee variants of the Escape, at most three rungs
(`CHN-16`, `CHN-17`); the base Escape is rung 0.
_Avoid_: fee estimation, RBF policy, panic fee

**Rung**:
One indexed variant in a ladder, separately user-signed over its own bytes.
_Avoid_: bump (alone), replacement, retry

**Bump target**:
The consensus-observable feerate the sweep aims at: the median of the block at `tip − (tip mod
6)`, quantised down to 5 sat/vB (`DUR-30`).
_Avoid_: fee estimate, mempool fee

**Refresh**:
A pin-less Normal-path self-spend that resets a coin's recovery timelock; subordinate to pending
spends (`SPN-43`–`SPN-49`).
_Avoid_: rollover, renewal

**Rotate**:
The incident response: sweep everything to the escape wallet, then fund a successor vault
(`OPS-30`).
_Avoid_: key rotation (alone), migration

**Commitment**:
The exact-transaction binding a node evaluates and signs against (`CHN-24`–`CHN-26`); its id
keys the replay log and every partial message.
_Avoid_: authorization, intent, summary

**Descriptor backup**:
The full vault descriptor, backed up promiscuously (`OPS-23`). Without it even valid recovery
keys cannot locate the coins.
_Avoid_: wallet backup, seed backup

### The spend in flight

**Candidate**:
One signed-but-withheld commitment in a node's registry — spend, Escape, refresh or claw-back
— with its fire window, rungs, partials and flags (`SPN-36`).
_Avoid_: job, pending transaction (that is Pending spend), entry

**Pending spend**:
A hot-class candidate a node has accepted and signed, waiting out its Hold, listed on `/pending`
(`SPN-30`, `API-21`). Cancelled implicitly by any confirmed conflicting spend.
_Avoid_: queued transaction, unconfirmed spend

**Hold**:
The node-driven waiting period between a hot spend's acceptance and its combine and broadcast
(`SPN-30`). Off-chain; delays combine, not signing. Not the Carrier deadline; not the Recovery
timelock.
_Avoid_: delay, timelock (for this), cooldown

**Fire window**:
`[fire_at, deadline]`, the interval in which a candidate may release, combine and broadcast
(`SPN-30`, `DUR-20`).
_Avoid_: hold window, combine window (that is `combine_slack_secs`)

**Release gate**:
The sole egress for a partial signature (`DUR-8`); a SpendRequest pair is "opened only by the
holder decision of a Carrier naming it" (`SPN-37`), "only for a Carrier this node accepted, or
replayed as accepted" (`DUR-5`), and release requires that the node is not armed against that
candidate.
_Avoid_: signing gate, fire gate

**Partial**:
One node's `SIGHASH_ALL` signature on one input of one rung, exchanged over the channel
(`NCH-23`).
_Avoid_: signature share, vote

**Held partial**:
A valid Partial present in one node's resident Candidate — its own withheld signature, held
from registration because `SPN-36` says a candidate is "born fully signed and fully withheld",
or a peer's Partial its store accepted (`NCH-24`, `NCH-25`). It is what a node finalizes from
(`SPN-39`, `DUR-28`).
Node-local and mortal: pruning the Candidate destroys it, while the Exposed authority the same
Partials created survives. It says what this node has, never where else the signature exists.
_Avoid_: local exposure, exposed authority, received partial (this node's own is in the set),
signature cache

**Exposed authority**:
What a released Partial leaves behind: the fact, keyed by `(sighash message, input, signer)`,
that a signature for one message exists outside its node (`ADR-0023` decision 9). It outlives
everything node-local — candidate pruning, settlement, the reservation's refund and its age-out
(`POL-20`) — and two commitments over one transaction share it, because `CHN-24` binds an expiry
the sighash does not. The `exposed` bit a reservation carries (`POL-18`, `SPN-33`) is its
per-candidate projection, not the thing itself.
_Avoid_: exposure (bare — say exposed authority, or the node's exposed bit, and say which),
leaked signature, compromised partial

**Carrier**:
The exact coordinator-authenticated Spend request body a node processes and relays; its
identity is the body, not the signature (`NCH-30`). A peer's relay of it is evidence the peer
received and processed it, not that it froze or signed.
_Avoid_: carrier id, acknowledgement, partial

**Holder**:
A node counted as holding a Carrier: itself once staged, plus each peer whose relay it received
(`DUR-5`).
_Avoid_: confirmer, acker, voter

**Arm intent**:
The same-shaped per-Carrier record every SpendRequest writes at ingress under either PIN
(`DUR-4`); separate Carriers over one pair retain separate intents. The holder decision acts
on the Pair duress bit (`DUR-5`) and the earliest pair ingress sample (`DUR-13`); an unbound
intent retains its own bit and time. Retirement leaves metadata on the nonce tombstone with
"no holder authority" (`NCH-40`).
_Avoid_: arm, schedule, duress flag

**Pair duress bit**:
The holder decision's bit (`DUR-5`): "the OR of this intent's duress bit and those of every
resident intent and retained nonce tombstone" naming the same spend commitment, under both
PINs. Read at the holder decision for arm, sweep authorization, selection and freeze; never a
write to the resident candidate. An unbound intent uses its own bit.
_Avoid_: sticky candidate bit, node duress bit, PIN of the pair

**Carrier deadline `D`**:
The monotonic instant, fixed once at nonce acceptance, at which a Carrier's residency ends
(`NCH-33`). Signed expiry `E` bounds attempts; `D` bounds residency.
_Avoid_: expiry (that is `E`), timeout, stopwatch

**HotClock**:
A node's monotonic clock — elapsed seconds since the channel was built — the only clock that
may retire Carrier state or age the Hot-budget window (`NCH-41`, `POL-22`).
_Avoid_: system clock, wall clock

**Effective time**:
`max(nonce-log high-water, wall)`, the rollback-guarded lower bound freshness uses
(`SPN-13`).
_Avoid_: now (unqualified), current time

### Duress

**Duress PIN**:
The second enrolled PIN; submitting it records an intent (`DUR-4`). A holder decision acts
on the Pair duress bit (`DUR-5`), including through a later Carrier naming that pair, to freeze
hot completion, schedule Lockdown and authorize the best-effort sweep (`05-duress-and-lockdown.md`).
Externally identical to the normal PIN.
_Avoid_: panic code, secondary PIN

**Pin-independent ingress**:
The rule that every admitted request does identical observable work under either PIN
(`SPN-3`, `DUR-1`).
_Avoid_: constant-time path, duress branch (there is none)

**Armed**:
The node state after a holder decision with `arm = true` (`DUR-5`, `DUR-10`), including a
normal-PIN Carrier inheriting a pair's mark: hot completion frozen, `T` set, any bound Escape
selected. Never exposed on any surface.
_Avoid_: triggered, alerted, panic mode

**`T`**:
The deadline at which an armed node enters Lockdown and the sweep fires (`DUR-13`). A ceiling
bounded by `duress_delay_secs`, pulled earlier by any pending hot spend.
_Avoid_: timer, countdown, trigger time

**Lockdown**:
The terminal state in which a node refuses all signing (`FRAUD_SUSPECTED`) for its lifetime,
with no reset; the only exit is Recovery (`DUR-7`).
_Avoid_: freeze (alone), pause, quarantine (the cover story's word, not ours)

**Sweep**:
The best-effort firing of the Escape at `T` (`DUR-19`–`DUR-33`). May fail; safety never depends
on it.
_Avoid_: escape (that is the transaction), claw-back (that is the pin-less request)

**Protected value**:
The coverage denominator a selected Escape is measured against on one pass: the vault as this
node reads it then, with every selected Escape's inputs always counted (`DUR-22`). Per pass and
per node; never stored, never a snapshot.
_Avoid_: vault balance, armed balance, snapshot, the denominator (unscoped)

**Claw-back**:
A pin-less request that pays the escape wallet — instant, born open, and able to defeat a
pending spend by spending its inputs (`CHN-35`, `SPN-50`, `OPS-15`). Refresh's sibling, not a
spend; on the wire, `clawback`.
_Avoid_: cancel, veto, sweep (that is the Escape firing at `T`), escape (that is the transaction), escape-class spend

**SILENCE**:
The invariant that a duress ceremony is indistinguishable from a normal one across every
observable a node emits, against a coordinator that turns hostile at the wrench (`DUR-1`,
`SEC-10`). It assumes no node ran a compromised release while the current PINs were in use.
_Avoid_: stealth, privacy, indistinguishability (unscoped)

### Monitoring

**Watchtower**:
The duty every node performs against its own chain: alert on any Recovery-path spend and on any
vault spend it never validated and accepted (`WTC-17`, `WTC-18`).
_Avoid_: monitor (alone), watchtower service, co-sign check

**Alert**:
An event a node queues for the coordinator to pull from `/events`: a watchtower hit, or a
channel freshness diagnostic (`WTC-20`, `API-18`). A refusal is not an alert.
_Avoid_: notification, log line

**Watchtower cursor**:
The `(height, hash)` anchors of the top of a node's scanned chain range and its next height,
held in RAM and reconciled against the active chain before every pass (`WTC-13`, `WTC-14`). Not
the release cursor.
_Avoid_: cursor (bare), scan height, chain pointer

**Release cursor**:
Where a candidate's fire pass releases from: the release floor and the interval of rungs a pass
releases up to the latch (`SPN-38`). Not the watchtower cursor.
_Avoid_: cursor (bare), ladder position

**Cache anchor**:
The `(height, hash)` a node's vault-unspent cache was computed at; a fire-time read is refused
unless it is the current tip (`WTC-5`).
_Avoid_: anchor (bare)

**Scan anchor**:
The block a cold full UTXO-set scan read at (`WTC-7`).
_Avoid_: anchor (bare), scan tip

**Settled depth**:
How far below the scan anchor a wallet import treats the chain as settled: a reorg no deeper
leaves that import's completion marker in force, and a deeper one can unseat it; a repair latches
only when no held marker's anchor is still active (`WTC-7`, `WTC-9`). A cost setting, not a
finality assumption.
_Avoid_: confirmation depth, finality depth, reorg limit

**Settled block**:
The block the settled depth below the scan anchor, or genesis on a shorter chain. The import is
re-proved against it, and a completion marker's anchor is it (`WTC-7`, `WTC-8`).
_Avoid_: anchor (bare), checkpoint

**Birthday**:
The lowest block height a wallet import covers: the settled block, or lower where an output the
scan found live or the walk found spent was created lower (`WTC-7`). A repair never raises it.
_Avoid_: start date, wallet creation time, rescan timestamp

**Completion marker**:
An inert descriptor a wallet import leaves behind, carrying the owner hash, its settled block and
its birthday. A held marker whose settled block is still active is one of the conditions `WTC-8`
sets for the wallet to be usable, not the whole of them, and any such marker serves, whichever
import left it.
_Avoid_: checkpoint, note, wallet anchor

**Refusal**:
A node's structured decision not to sign, with a code and a check (`API-13`). A policy
outcome, never a transport error.
_Avoid_: rejection (that is the channel's word), error

### Rollout

**Core-proven**:
The milestone at rollout stage 1: full test matrix green, the Path suite driven on signet, and
the freeze (`OPS-37`). It means the protocol works — not that the system is deployable and not
that anyone outside has read it.
_Avoid_: v0 done, production-ready, launch-ready, audited

**Freeze**:
Stopping churn in a named artifact set so later stages build on something stable. Discipline,
not assurance (`OPS-45`).
_Avoid_: review, sign-off, audit, approval

**External review**:
The one independent human security review, at stage 9, gating the lift of the dust caps
(`OPS-45`, `SEC-40`). Automated panels do not count.
_Avoid_: review #1 / #2, panel, audit (unless a paid audit is meant)

**Production-ready**:
A later milestone: safe to hold meaningful savings. No earlier than stage 9.
_Avoid_: core-proven, v0 done

**Stage**:
One rung of the rollout ladder (`OPS-37`); complete when its Path suite has run against both
its vaults.
_Avoid_: phase, milestone, step

**Path suite**:
The behaviours a stage must exercise: honest hot spend, refresh, theft refusal, claw-back, and —
destructively — duress arm through Lockdown, then Recovery (`OPS-38`).
_Avoid_: test suite, smoke test

**Survivor vault** / **Sacrificial vault**:
The stage vault that exercises only non-destructive paths and stays running, and the one driven
to its terminal end (`OPS-38`).
_Avoid_: main vault, test vault, throwaway vault

**Soft vault**:
This design's honest trust boundary: `t` compromised nodes plus the user key equals theft
(`SEC-32`).
_Avoid_: covenant vault, trustless vault

**Outcome** — **Nothing** / **Bounded** / **Denial** / **Theft** / **Loss**:
The five words `SEC-54`'s compromise-and-loss matrix allows for what an attacker or a key loss
achieves. Nothing: no valid request exists. Bounded: hot spends inside the allowlist and budget,
clawed back inside the Hold. Denial: the coins reach the escape wallet or Recovery, under the
Operator's keys, later than wanted. Theft: coins reach a wallet the attacker controls. Loss:
coins reach a wallet nobody can spend.
_Avoid_: compromise (unqualified), breach, exploit, "funds at risk"

**Custody drill**:
A restore of every key role performed from backups alone with the primaries set aside, plus
the failure-domain check and a reachability check of each recovery holder (`OPS-61`). The whole
defence for escape-key loss and recovery-key loss (`SEC-54`).
_Avoid_: backup test, key audit, recovery drill (that is `OPS-27`, opening the Recovery door)

### The formal layer

**Specification gate**:
A command in `tools/` that refuses an inconsistent or invalid specification artifact and is run
by `tools/check-all.sh`. Bare *gate* means this in `README.md`, `AGENTS.md` and `tools/`; in a
requirement it is qualified, because the set also uses *gate* for a runtime refusal — the
**release gate** (`DUR-8`), the ingress gates of `SPN-5` — and those are requirements, not checks.

**Formal model**:
The formal layer's explicit state, inputs and transition rules, about which a property is proved.
Bare *model* is `ADR-0012`'s Model A, Model B and Model R, or the threat model; the formal layer's
is *the formal model*, or a named compound — *the release-gate model*, *the ledger model*. Say
*model state* and *model invariant*; a bare *invariant* is one of `SEC-8`–`SEC-15`.
_Avoid_: model (bare), reference model (reads as the reference implementation), oracle (two
meanings already, neither the formal layer's: a surface that leaks a secret — `NCH-3`, the PIN
oracle — and, per `OPR-81`, an implementation-diverse tool that checks an artifact, `MAN-37`; a
Lean evaluator a signer imports is not an independent oracle for itself)

**Exhibit**:
A concrete input or trace the formal layer executes that exhibits a property or its failure —
ADR-0014's delayed-holder trace, one usable rung above the cursor. A negative exhibit, or
counterexample, is a retained trap made executable; a positive exhibit is an admitted input, and
a formal model without one for each kind it admits is incomplete, because a rule that refuses
everything satisfies every prohibition. **Trace** stays the ordinary word for the sequence kind;
a trace is an exhibit once the formal layer executes it.
_Avoid_: witness (that is the segwit witness, `CHN-9`), test vector (that is `WIR`'s frozen bytes)

**Guard parameter**:
A field of a formal model's rule structure whose `current` value is the requirement as it stands
and whose other values are the requirement as it stood — `SPN-38`'s anchor on `F` or on the
cursor, `DUR-22`'s restoration of every selected Escape or of one. The module holds the refused
and admitted twins over one trace, and CI flips `current` and requires the named theorem red.
_Avoid_: guard (bare — `NCH-13`'s ingress guard, `POL-12`'s bug guard and `DUR-9`'s lock guard are
requirements), flag, feature switch

**Negative control**:
A deliberate break of one thing a specification gate guards, on a scratch copy, with the run
failing unless that gate goes red for that reason. One per gate that can be broken;
`.github/workflows/gates.yml` holds the list.
_Avoid_: control (bare — `OPR-78`'s ceremony controls are a requirement), mutation test (that is
what an implementation runs)

**Rendered region**:
The lines between `<!-- formal: BtcPolicy.… -->` and `<!-- /formal -->` in a requirement — or in
the ADR a declaration names as its home, where a requirement keeps its worked figures — which are
what the named declaration emits. Compared line for line (*render*) or on the tokens the
declaration determines (*match*); drift is a red gate.
_Avoid_: generated section, snippet

**Emitted value**:
A scalar or formula string a tagged declaration emits so the copies gate can compare it to the
figure inline in the owning sentence and in every copy of it — `CHN-4`'s `4224679` in `CHN-1`,
`CHN-8` and `CHN-10`. The Lean constant cannot read the Markdown; the gate reads both.
_Avoid_: constant (says nothing about the comparison), magic number

**Observer projection**:
What a formal model says a party outside the node can see of one step — the response bytes, the
pulled surfaces, the peer effects and the ordered work `DUR-1` lists — as a function of the state
and the step, with everything else omitted on purpose. SILENCE is a statement about two runs'
projections, so what the projection omits is what the statement does not cover, and the omission
is named where the projection is defined (`BtcPolicy.Silence`).
_Avoid_: view, observable (bare — an observable is one field of a projection), trace (that is the
sequence), API surface

**Concealment horizon**:
The point up to which a SILENCE statement holds: on each step, the state ENTERING it is unarmed
or its effective sample is strictly below that state's current `T` (`DUR-7`, `DUR-13`, `DUR-14`).
It is a guard on a step and not an instant, it may be zero (`DUR-14`: a matured Hold "collapses
the window to now"), and it is sticky by the quantification over the prefix rather than by any
property of the clock, which is not monotone (`F60`).
_Avoid_: window (that is `combine_slack_secs`' and the fire window's word), deadline (that is
`T`), cutoff

**Requirement index**:
The list `lake exe gate` emits, one line per tagged declaration, of which identifier each
formalizes. The only map between the formal layer and the documents. Always qualified: bare
*index* is `max_derivation_index` or a node's position.
_Avoid_: index (bare), manifest (that is the vault's), map

**Assumption**:
A named hypothesis a theorem takes as a parameter because its truth is not the theorem's to
establish — a chain backend's coherence, a cryptographic binding on the admitted domain, delivery
that is not partitionable per link, descriptor membership before it is derived. A theorem's
signature shows what it assumes; a formal model that omits something says so. In a Lean
signature the same thing is a *hypothesis*, `(hP : 0 < P)`.
_Avoid_: axiom (the formal layer declares none; the three logical axioms Lean supplies are not
assumptions and the gate's list does not enumerate these), residual (that is `SEC`'s word for an
accepted risk, which an assumption may name but is not)

**Property**:
A proposition about a definition or a trace, proved as a **theorem** under its stated assumptions
— by a hand proof, by `omega` or `grind` over every input, or by `decide` over a stated finite
bound, which is a theorem like any other. Neither is evidence about a running implementation;
that is a conformance item, and a proposition in an FFI type is not a runtime capability.
_Avoid_: guarantee, claim, requirement (a property is what a requirement's rule implies, never
the requirement), verified (against what?), complete (over which state space?)

## Flagged ambiguities

- **"witness"** — the segwit witness, always; the formal layer's concrete input is an
  **exhibit**.
- **"model"** — Model A/B/R and the threat model; the formal layer's is the **formal model**.
- **"policy"** alone — three meanings; always say spending policy, policy checks, or policy
  config.
- **"expiry"** — the signed request field `E`, never the Carrier deadline `D` and never a
  candidate's fire window deadline.
- **"host"** — key GENERATION is per device and always was; the RUNTIME is co-located at
  rollout stage 1 and on independent hosts from stage 2 (`OPS-51`). Say which.
- **"unconditional"** of Lockdown — about the decision, never the latency (`DUR-15`).
- **"silence"** — always scoped (`SEC-10`); it is not a claim against a compromised node.
- **"rejected"** — the channel's word for a permanent envelope-level refusal; a policy outcome is
  a **refusal**.
- **"confirmed"** — a chain fact about a transaction; a Carrier is **committed**, never
  confirmed.
- **"exposed"** — of AUTHORITY, the world-level record keyed by signer and sighash message; of a
  RESERVATION, the node-local bit `POL-18` reads off its own candidate. One transaction can have
  the first without the second (`F63`). Say which.
- **"sealed"** — of a HOST, the locked-down machine with no way back in (`ADR-0005`); of a
  VALUE, bound into the manifest preimage so a mismatch fails startup (`MAN-2`). Say which. A
  sealed value is one ENFORCEMENT of **federation-uniform**, never a synonym for it: asking
  "should this be sealed?" before "must every node agree on it?" is how `policy_version` stayed
  unsealed while the protocol required it to be uniform.

## Banned words

**cosigner** for a federation node (use only for an escape-wallet participant), **trustless**, **covenant** (out of scope), **audited**,
**production-ready** before stage 9, **cancel** (there is no cancel operation), **duress
response** (the retired toggle; duress is one mechanism), **unseal** (rejected),
**restart** of a node (there is none), **sign-log** (never built).
