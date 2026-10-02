# 13 — Operations and rollout

What an Operator does with a sealed vault, what the runbook tells them in an incident, the
ten-stage ladder from five daemons on one machine to a public alpha, what an upgrade or a
rotation costs, who holds which key, and the dependency policy. Requirements here are on the
Operator and on the operator program; node behaviour is cited, never restated.

## The one thing to know first

**OPS-1** Once a vault is sealed, nothing an Operator can do reconfigures it. There is no
reset, no upgrade in place, no key rotation, and no way out of Lockdown but the Recovery path.
Every remedy below is one of: wait, sweep to the escape wallet, or rotate to a successor vault.

## Routine

**OPS-2** The Operator MUST poll every node — not a quorum, never through the coordinator alone —
on `/healthz` for liveness and the Lockdown latch, on `/pending` to diff accepted candidates
against what they authorized, and on `/events` for watchtower alerts, keeping the returned
cursor per node. A node that stops answering is presumed dead and counted against the
federation budget (`OPS-5`). The operator program's `status` command is that poll (`OPR-52`).

**OPS-3** A `RECOVERY_PATH_SPEND` alert means recovery keys are being used. If the Operator did
not do it, the keys are stolen: race every remaining coin to the escape wallet through the
Normal path immediately, then rotate. The real defence was refresh discipline; a refreshed coin
was never exposed.

**OPS-4** An `UNRECOGNIZED_SPEND` alert means a vault coin moved without this node accepting the
spend. With `n − t` honest nodes legitimately not signing each spend this still fires only for a
spend some node REFUSED or never saw (`WTC-18`); treat it as an incident, not noise.

**OPS-5** At one dead node, plan a rotation; at two, rotate urgently: three alive on 3-of-5 is a
bare quorum with zero margin, and one more loss strands the Normal path. Node death is
permanent for that vault (`STO-1`).

**OPS-6** Refresh every coin before its recovery timelock matures, at a cadence expressed as a
fraction of the vault's own timelock — the operator program nags at 2/3 and 5/6 of it, day 120
and day 150 on the 180-day default (`OPR-63`) — and before a mandatory safety margin on any
funded vault. Maturity is per coin from its confirmation, so it moves with deposits and
refreshes; the operator program reports the earliest maturity across the unspent set
(`OPR-62`), never one vault-level date, and "earliest maturity for coins confirmed now" is the
ceremony's projection for a new deposit (`OPR-78`), not a reading of existing coins. The
operator program computes and enforces it (`OPR-62`); a reviewer named its absence the
likeliest cause of real loss.

## Reading a refusal

**OPS-7** A refusal is a policy outcome with a code and a check (`API-13`, `API-14`). The ones an
Operator will meet: `DEST_NOT_ALLOWED` — the destination is not on the sealed allowlist, and it
never will be; `HOT_BUDGET_EXCEEDED` / `HOT_VELOCITY_EXCEEDED` — the spend exceeds the sealed
cap or the rolling window; `BAD_PIN` — with check `pin_attempt_budget`, the node is locked out
after too many wrong PINs and will answer the same to a correct one until the lockout expires;
`COMMITMENT_EXPIRED` — the request's expiry is outside the node's window, usually a clock
problem; `REFRESH_SUBORDINATED` — a spend is pending; retry after it settles;
`FRAUD_SUSPECTED` — the node is locked down (`OPS-10`). For sizing the Hot budget, `POL-20`
states: "This formula MUST NOT be presented as a bound on funds completing or lost in an
arbitrary rolling window". The cap is not a promised maximum loss over that window.

## The coordinator's lifecycle

**OPS-8** The coordinator host MUST be a dedicated, single-purpose, minimal machine with no
other tenants — not the daily-driver laptop — and the binary on it MUST be reproducibly built
and verified from outside the host (`SEC-42`, `OPS-47`). Its controls are `OPS-54`. It is not a
node host: the two are different machines with different threat models, and the operator
program MUST NOT be installed on a node image (`OPS-50`). The user key MUST be hardware-backed
in production (`SEC-43`).

**OPS-9** Losing the coordinator auth secret with no backup bricks the Normal path (`SEC-36`).
It is backed up by the ceremony separately from the descriptor (`MAN-33`) and MUST be stored
apart from it. Losing the coordinator's DATA is not the same event: a coordinator is rebuilt
from the descriptor backup and the auth secret, with no funds at risk.

## Lockdown

**OPS-10** A locked-down federation answers `FRAUD_SUSPECTED` to every spend, refresh and claw-back and
reports `locked_down: true` on `/healthz`. It cannot be unlocked. The coins exit only through
the Recovery path after the timelock (`OPS-26`). Verify Lockdown by reading `/healthz` on every
node — NEVER by submitting a spend or a refresh, because on a node that is not locked down a
refresh can release and reset the recovery timelock the procedure depends on.

## Incidents

### The user was coerced

**OPS-11** **Cut power to the coordinator host first**, then reason. The deciding state — whether
the duress Carrier reached `t` nodes — is not chain-visible, and the coordinator in the
attacker's hands is the one machine that can still mint validly signed requests (`DUR-15`). The
power switch is the one action the Operator has after a wrench; it is narrower than it sounds,
because it stops new requests and does not undo any that were delivered.

**OPS-12** Nothing below is safe to run while the Operator may still be captive. The "once safe"
gate is a coercion gate, not an urgency wording, and MUST NOT be replaced by one: the procedure
generates the successor vault's keys and PINs, and a captive Operator running it hands them
over.

**OPS-13** Once safe, read `/healthz` on every node. If every reachable node reports
`locked_down: true`, the safety track held: no hot spend can release, the sweep either moved the
coins to the escape wallet or left them frozen, and the only exit is Recovery. If any node does
NOT report it, the Carrier may not have reached `t`, nothing armed there, and a coerced hot
spend can still finalize at its Hold expiry: `hold_secs` has no positive lower bound, so this
branch IS time-critical — race the coins to the escape wallet with a claw-back (`OPS-15`) if a
quorum of not-locked-down nodes will still sign one.

**OPS-14** Do not send anything through the possibly hostile relay, including a migration spend.
A request the attacker's coordinator relays is one it can censor, delay or downgrade
(`SEC-21`). Stand up a fresh coordinator from the descriptor backup and the auth secret on a
clean host first.

**OPS-15** The claw-back is a pin-less ClawbackRequest (`SPN-50`, `CHN-35`): it fires at
ingress on armed and idle nodes alike (`DUR-36`), sweeps the named coins to the escape wallet,
and defeats any pending hot spend by spending its inputs (`SPN-33`). Beyond the user key and
the credential every request needs, it needs `t` nodes that are not locked down and nothing
else — no PIN, no second transaction, no minimum coin count; a vault consolidated to one coin
claws back that coin. The operator program's command is
`clawback` (`OPR-67`).

**OPS-16** After a successful sweep the coins sit in a single-key escape wallet. That is an
incident destination, not a resting place: fund a successor vault from it at leisure
(`OPS-36`), and do not serialise the successor behind straggler maturity — stragglers left in
the locked vault reach Recovery on their own clock (`OPS-26`) while the swept funds move now.

**OPS-17** A mis-entered duress PIN is a real duress event and finishes the vault (`ADR-0005`).
Enrol the two PINs deliberately distinct.

**OPS-18** *This procedure was rewritten seven consecutive times by automated review, each round
introducing a new defect. It has not been read by a human security reviewer and MUST be, before
it is relied on (`F21`, `SEC-40`).*

### An unauthorized spend is pending

**OPS-19** A commitment id on `/pending` that the Operator did not authorize means the user key
and the normal PIN are in someone else's hands (A3), or the coordinator auth key too (A7). Before
its Hold expires, claw it back (`OPS-15`); the Hold exists to give
this window. Then rotate: the user key is compromised and the allowlist cannot be changed.

### The coordinator auth key is lost

**OPS-20** Restore it from the backup. If there is no backup, the Normal path is bricked and the
coins exit through Recovery after the timelock (`SEC-36`); stop refreshing so the coins mature.

### A node will not boot

**OPS-21** Read the error. The common ones: the derived key is not in the descriptor — wrong
preimage or wrong config for this host (`MAN-18`); the computed manifest hash differs from the
sealed one — a sealed value in this config disagrees with the federation (`MAN-11`); the
backend is on the wrong chain or a custom signet (`WTC-3`); the filesystem is not tmpfs
(`STO-3`); the filesystem does not support extended attributes (`STO-4`). None of these is
repaired on a sealed host; a node that will not boot before sealing is reprovisioned, and one
that dies after sealing is dead (`OPS-5`).

### Fewer than `t` nodes are serving

**OPS-22** The Normal path is unavailable. If the loss is temporary, wait. If it is permanent,
the coins exit through Recovery after the timelock; stop refreshing.

## Backups

**OPS-23** The descriptor backup MUST be promiscuous — paper, every node, the coordinator,
beside each recovery key. Without it even valid recovery keys cannot locate the coins. It is
public data.

**OPS-24** The sealed backup set (`MAN-33`) MUST be moved off the coordinator to storage the
Operator controls. The coordinator auth secret MUST be stored separately from the descriptor.

**OPS-25** A backup that has never been restored from is a hypothesis. The recovery drill
(`OPS-27`) restores from cold artifacts alone; the node-lifecycle drill (`OPS-63`) restores a
node; the custody drill (`OPS-61`) restores key material from backups alone. They are different
backups with different failure modes and MUST NOT be merged into one harness.

## Recovery

**OPS-26** The Recovery path spends with 2 of the 3 recovery keys after each coin's relative
timelock matures (`CHN-4`, `CHN-10`): no user key, no node quorum, no coordinator, no PIN. It
needs only the descriptor and the recovery keys, and it is the only exit from Lockdown, from
the loss of the user key, from the loss of the federation, and for inheritance. A Recovery
spend is visible on-chain as such (`SEC-41`) and every surviving node alerts on it.

**OPS-27** A Recovery rehearsal MUST be driven from cold artifacts alone — descriptor,
manifest, recovery keys, no live federation — and MUST demonstrate that a spend before maturity
is refused by the network as non-final, that one recovery key does not satisfy the branch, and
that two do after the median-time-past crosses the lock. On regtest the drill runs against
mocked time; on a public chain a vault sealed with the production timelock takes 180 days to
rehearse, which is why a Sacrificial vault seals a short one (`OPR-78`). There is NO hard
floor on the timelock: the choice is the Operator's (`OPR-78`). A Survivor or production vault
SHOULD keep the default; on mainnet a below-default timelock requires the typed confirmation
`OPR-78` specifies, because unit confusion is the actual failure mode. That control is for
mistakes, not tampering (`MAN-37`).

## Upgrade and rotation

**OPS-28** There are three categories of change and one cost:

| category | covers | cost |
|---|---|---|
| software upgrade | new node or coordinator binaries | a new vault; there is no upgrade in place on a sealed host |
| sealed-parameter change | anything in `MAN-2`'s preimage — `wallet_id` and `protocol_version` are its first fields — plus what `wallet_id` binds transitively: the descriptor, `t`, `n` and the recovery timelock | a new vault; re-run the ceremony and move the coins |
| key rotation | any federation, user, escape, recovery, or coordinator auth key | a new vault |

The mechanical test for the second category: does the value feed the manifest preimage? Then
it is sealed. One relation escapes that test — the extended-key flavour of the hot and escape
descriptors against the sealed network — and is refused independently at assemble, finalize and
node load (`POL-8`).

**OPS-29** A revision of the manifest schema is a new `protocol_version` (`MAN-3`), a new
manifest, and a new vault. A sealed host keeps computing its own revision's bytes with the
binary it was sealed with; there is no migration.

**OPS-30** **Rotation** is: sweep everything to the escape wallet through the Normal path (a
claw-back, `OPS-15`), run a fresh ceremony, and fund the successor from the escape wallet. A
rotation is the routine response to a patch, a dead node, a compromised key, a forgotten PIN
(`SEC-54` rows L4 and L5: the PIN digests are sealed and there is no reset), a recovery key
known lost or a recovery holder unreachable at the drill (`SEC-54` row L7: two of three is the
bare quorum `OPS-5` describes for two dead nodes), or any sealed value the Operator wants
changed. The operator program's `rotate` command drives it (`OPR-66`) through the migration
tooling of `OPS-59`. The order depends on the trigger: a rotation triggered by **duress or a
compromise signal** sweeps FIRST and builds the successor after, because the swept funds must
not wait on anything (`OPS-16`); a rotation triggered by a **patch, a dead node, a planned key
change, a forgotten PIN or a lost recovery key** verifies the successor FIRST (`OPS-59` step 1)
and sweeps only once a valid successor exists, because a sweep into a single-key escape wallet
with no successor to fund is an incident, not a rotation; a lost key accompanied by a
compromise signal sweeps first.

**OPS-31** A vault sealed under an older manifest revision is NOT operable by a newer
coordinator on the live path: the operator program authorizes only against the current
revision (`OPR-11`), and a sealed host cannot be taught a newer one. Recovery from its cold
artifacts MUST keep working regardless of revision (`OPR-12`, `OPR-77`): a cold path that
rejects an older manifest turns "Recovery is their only exit" into "they have no exit".

**OPS-32** Nothing provisioned under the rollout waiver (`OPS-40`) crosses stage 6 — not the
topology, not the secrets, and not the coordinator host: operator preimages, node keys,
escape-wallet keys, recovery keys, the coordinator auth key and the coordinator host itself
were all inside one provider's console reach. Fresh key material and a fresh coordinator host
at stage 6, no exceptions, checked by the migration tooling's key-freshness assertion
(`OPS-59`).

## Key custody

**OPS-33** An Operator MUST have a written custody plan naming who holds each key of `DOM-10`,
and MUST run — against the real assignment, recording the result — a failure-domain check
that no single event — one house fire, one hostile relative, one subpoena, one raid — reaches
**2 of the 3 recovery keys**, or the coordinator auth key together with the escape wallet key,
or the user together with the escape wallet key or its backup — the last being the reach of a
coercer holding the user (`OPS-60`, `SEC-54` row 10).
Two recovery keys alone spend after maturity (`OPS-26`); a check that also requires the user
key passes on an assignment that is already fatal. The Operator MUST drill restoring each
backup (`OPS-61`). The recovery keyset doubles as inheritance, so its holders are chosen for
that too.

**OPS-34** The two vaults of a rollout stage MUST NOT share recovery keys, because the
Sacrificial vault's ceremony deliberately exposes and uses them.

**OPS-35** Once a node is up and sealed, destroy its paper preimage (`MAN-36`).

## Funding

**OPS-36** Funding a vault is sending to an address derived from the sealed descriptor by the
operator program's `receive` command (`OPR-56`). Before the first deposit the Operator MUST
re-derive the address with the implementation-diverse oracle of `OPR-57` — "independent"
means a different encoder, not merely a different binary — and MUST retire a stage vault's
deposit addresses with the stage (`OPS-42`, `OPR-59`).

## The rollout ladder

**OPS-37** Deployment MUST climb a ten-stage ladder that varies four axes — host distribution,
host hardening, network, and value at risk — as a test matrix with a funding policy, not as one
axis at a time. Value moves LAST: reaching a mainnet rung is not authorization to move meaningful
savings.

| stage | hosts | hardening | network | notes |
|---|---|---|---|---|
| 1 | one machine | open | signet | first Path suite on signet; the protocol-core **freeze** |
| 2 | five machines, one provider | open | signet | first real transport; loopback assumptions die; waived |
| 3 | five machines, one provider | open | **mainnet** | first real funds, dust-capped; waived; requires coordinator hardening and the fire-path mempool fix |
| 4 | five machines, one provider | **sealed** | signet | first sealed hosts; begin measuring attrition; waived |
| 5 | five machines, one provider | sealed | **mainnet** | dust-capped; waived; gated on the lifecycle decision (`F8`) |
| 6 | many providers | open | signet | provider diversity; `SEC-28` enforced from here |
| 7 | many providers | sealed | signet | attrition under diversity |
| 8 | many providers | sealed | mainnet | run it for a while, capped; the Survivor vault is the subject |
| 9 | many providers | sealed | mainnet | full Path suite on the real configuration; hardware signing required; **freeze, then THE external review, then the caps lift** |
| 10 | — | — | — | public alpha |

**OPS-38** A stage is complete when its Path suite has run against both of its vaults, never
when its code merely compiles. Every stage runs two vaults because two paths are terminal: the
**Survivor** exercises an honest hot spend, a refresh, a theft refusal (allowlist and cap), and a
claw-back, then stays funded and running; the **Sacrificial** is driven through a duress arm to
`T`, unconditional Lockdown and a best-effort sweep, then to Recovery from cold artifacts.

**OPS-39** The Sacrificial drill MUST verify Lockdown and the sweep **independently**: Lockdown
at `T` regardless of the sweep's outcome (`FRAUD_SUSPECTED` on every node, `locked_down: true`
on every `/healthz`), and the sweep on its own terms. A drill asserting "sweep, then Lockdown"
would pass a build in which Lockdown had become conditional on the sweep — the exact theft class
`DUR-2` rules out. Recovery then runs against a FRESH deposit made to the locked-down vault,
which is the more valuable drill (a straggler deposit to a vault that can no longer sign is a
real incident) and not against a deliberately failed sweep.

**OPS-40** Stages 2–5 run under an explicit, time-limited, test-only waiver of `SEC-28`
(`ADR-0015`): a federation provisioned under it is a laboratory, never a custody deployment,
whatever network it runs on. The waiver expires at stage 6. The deployment tool's test-mode
bypass (`OPS-52`) MUST be compiled out of stage-6 and alpha binaries and shipped, where needed
before stage 6, as a separately built and visibly tainted artifact; that is verified by
confirming the bypass symbol is ABSENT from the stage-6 artifact, never by asking the binary
to refuse — a runtime "which stage am I" check is operator-controlled and therefore no control
at all. Evidence produced under the waiver MUST be machine-readably tainted as non-promotable,
and it is the bypass that writes the taint marker into every artifact the run emits, because
the bypass is the one component that knows a run is waived.

**OPS-41** Every mainnet rung MUST be capped at dust, and the cap MUST be a number with an
observer before the rung is funded: an aggregate across every live stage vault, watched by an
independent machine on a separate account outside both the provider's and the coordinator's
trust domain — during stages 2–5 one provider reaches all five consoles, so a watchtower alert
from those nodes is not sufficient. Breach handling is mandatory and immediate: abort or
descend the stage and retire the vault. The cap is a loss budget, not a security invariant;
Bitcoin cannot refuse a deposit.

**OPS-42** Stage deposit addresses MUST be retired with the stage; a stale address is a
permissionless path to re-fund a vault whose waiver has expired.

**OPS-43** Stages 3 and 5 accept unrepresentative fee data: at true dust, fees dominate and the
ladder, ancestor pressure and relay evidence do not represent production. Representative fee
behaviour is acquired at stage 8. Anyone proposing to raise a waived stage's cap for better fee
data is proposing to void `ADR-0015`, not to tune it; if the cap is raised on a waived stage the
ladder MUST be reordered to reach diversity first.

**OPS-44** Sealing does not make one provider safe (`SEC-28`). Stage 4 exists for
MEASUREMENT, not only hardening: it records how long five sealed nodes actually survive
untouched, what killed them, and the true wall-clock and ceremony cost of one
migration-to-patch performed for real — expecting attrition dominated by provider maintenance,
since a live-migrated or rebooted VM is a dead node under `ADR-0007` — and hands that data to
the lifecycle decision (`OPS-62`) in a form that can decide it. Stage-4 data alone decides
that question, BEFORE stage 5 puts mainnet funds behind either answer; stage 7 continues the
measurement under diversity and is not an input to a decision that is already closed.

**OPS-45** There is ONE external human review, at stage 9, and the order is freeze, then review,
then the caps lift (`ADR-0017`). It reads the stage-9 artifact — hardware signing included — and
not the stage-1 freeze. Stage 1 keeps the freeze: stopping churn in interfaces, threat model,
ceremony, runbooks, vectors, dependency policy, rotation policy and the reproducible release,
which is discipline and not assurance. Correlated automated review is not a substitute
(`SEC-40`).

## Dependencies and the build

**OPS-46** Every dependency MUST beat writing it. Each library is code in the signing key's
address space and a supply-chain entry point, and the bar rises with blast radius: the pure
policy core has exactly two dependencies (consensus types and descriptors) and MUST NOT gain one
without a recorded decision; the wire crate takes serialisation and zeroisation only; the node
and the coordinator justify each addition case by case, and only for what is genuinely hard —
consensus encoding, Argon2, constant-time comparison, async I/O. Concrete rules: no dependency
for convenience (write the hundred lines); pin what matters, with any source-control dependency
at a full commit hash; default features off for large crates; a dependency that reaches the
network, the filesystem or the clock is a design decision, not a packaging one. The HTTP client
used for peer sends and the backend MUST disable proxies and refuse redirects at every call site
that can carry a partial signature. An implementation in another language inherits the rule,
not the list.

**OPS-47** A release MUST be reproducible — an independent rebuild of a named commit on a
DIFFERENT machine yields byte-identical binaries, and the release documentation names which
machine that is (a CI runner or a second developer box), because a hash produced by the same
box proves nothing — signed with a key whose holder and verification path are stated, and its
dependency graph MUST be gated in CI by a vulnerability audit that is proven live by
deliberately pinning a known-vulnerable version and watching the gate go red. The pipeline is
supply-chain provenance: it closes the poisoned-build and tampered-dependency vectors of
`SEC-42` and addresses neither malware resident on a correctly built coordinator nor a wrench
that begins mid-spend; its one extra benefit is detection, by re-hashing an installed binary
from OUTSIDE the host.

**OPS-48** An implementation's dependency-inventory recipe MUST have this shape: assert the committed lockfiles are current BEFORE entering the build
environment, run the dependency listing with the lockfile pinned so drift fails instead of
regenerating, and check the exit status of every stage rather than the plausibility of the
output. A recipe that can silently document a dependency graph the repository does not commit
is the one thing an inventory exists to prevent.

**OPS-49** Test-only dependencies MUST NOT reach a released binary, and a reviewer SHOULD
re-derive the inventory rather than trust a table: that the policy core still has exactly two
dependencies and no I/O, that every consensus- and crypto-critical crate is pinned, that the
process draws secrets from the operating system's random source and never from a general
random library.

## Deployment: transport, hosts, images

**OPS-50** From rollout stage 2 the deployment MUST provide a **confidential, authenticated
coordinator ingress** from the coordinator host to at least one manifest-selected node API. It
MUST be confidential because a spend request carries the plaintext PIN; it MUST authenticate
the selected node and endpoint; and it MUST preserve the exact-request ordered failover of
`API-16` — byte-identical request offered to each endpoint in manifest order under the
per-endpoint deadline. No live operator command runs on a node host, and the operator program
MUST NOT be installed on a node image: it would co-locate the user key, the PIN and the
coordinator credential with a node signer. Verification: a request POSTed to exactly ONE
ingress reaches the non-ingress nodes, is independently validated there and reaches
node-side combine and broadcast; suppressing only the request-carrier propagation while
leaving partial-signature transport intact MUST make that path fail.

**OPS-51** From stage 2 node-to-node transport MUST be routable and authenticated, with the
manifest-pinned endpoints (`MAN-4`) and the channel-key endorsements (`NCH-5`) doing the
authentication; clearnet dynamic-IP topologies are unsupported by design. The mechanism —
onion addresses derived from node key material, or mTLS — is `F37`. Before the nodes are
reachable the deployment MUST record, for each of `/pending`, `/healthz` and `/events`, exactly
one of **public**, **firewalled to the coordinator** or **authenticated**, re-ranking `SEC-20`
for real links (`F38`); "firewalled to the coordinator" is compatible with `OPS-2`'s
poll-every-node only if the ingress reaches every node. The per-link partition attack accepted
on loopback (`DUR-15`) MUST be re-analysed for real links and not inherited (`F39`).

**OPS-52** A deployment tool MUST enforce correlation diversity (`SEC-28`) at deploy time, so
that a misprovisioned federation FAILS rather than silently collapsing to one class, reasoning
about provider AND provider account, not merely distinct machines, because sealing does not
remove provider administration. Its test-mode bypass MUST: never be a default; record its use
in the stage's artifacts; be unavailable from stage 6 (`OPS-40`); and write the machine-readable
non-promotable marker into every artifact of a waived run. A federation MUST publish an honest,
attested statement of the diversity actually achieved — provider, region, operating system,
operator — and no compliance claim dates from before stage 6. Verification: five separate
hosts complete an honest spend, a claw-back and a duress arm to Lockdown; a co-located
federation is REFUSED at deploy time unless the recorded bypass is set.

**OPS-53** The **sealed node image** MUST contain the node binary and its declared runtime
dependencies and nothing that constitutes an administrative path: no SSH, no remote
administration, no reset, no reconfiguration, no upgrade in place, no post-seal package
manager or network install path, no operator program, and no embedded user key, coordinator
secret or PIN. Its only surfaces are the node API and its chain backend. Configuration and key
material live on tmpfs (`STO-1`); the preimage is entered exactly once on standard input before
the host is sealed (`MAN-36`), then the paper is destroyed (`OPS-35`). The image build MUST be
reproducible (`OPS-47`): two independent builds produce identical artifacts, because after
sealing there is no way to inspect the running host. The reviewed binary's hash and version
MUST be bound into the stage's release evidence, and a stage readiness check FAILS if the
artifact present is not the reviewed one. The image deliverable MUST enumerate in writing every
capability that survives on the host after sealing and why a coercer cannot use it, and MUST
state plainly that patching a node costs a full vault rotation and a dead node has no remedy.
How an image reaches a host that has no SSH, and its format, is `F40`.

**OPS-54** The **coordinator host** MUST NOT have remote administration of any kind, ambient
network egress beyond what the relay needs, other tenants, or provider-console sessions for
the node hosts (`SEC-29`). It MUST have verified or measured boot, strict network allowlists,
process sandboxing, minimal installed software, frequent clean re-image and a stated update
story. Acceptance criteria MUST test those runtime-targeted controls; disk encryption MUST NOT
be presented as one, being of little use against live resident malware, which is the threat
this host is against. It owns the operator program's reproducible install slot and its
declared interactive secret surfaces, with no argv or log persistence of secrets (`OPR-3`) and
no ad hoc install path. The deliverable MUST state what an attacker who owns this host still
gets — the plaintext PIN and so duress nullification, plus the user key while it is software,
bounded by the allowlist and the Hot budget — and MUST NOT be written up as closing `SEC-42`:
this host reduces the probability of resident malware and removes no capability, and nothing
addresses a wrench that begins mid-spend while the normal PIN is in RAM. Hardware signing
(`OPR-31`) does not block this host; it gates only stage 9.

## The ladder's gates, caps and evidence

**OPS-55** No rung MAY be climbed with an unmet gate:

| stage | gated on |
|---|---|
| 1 | the freeze (`OPS-64`) alone; external review is at stage 9, not here (`ADR-0017`) |
| 2 | stage 1, plus the independent runtime and transport (`OPS-50`, `OPS-51`); it holds no funds, so coordinator hardening and caps do not gate it |
| 3 | stage 2, plus the coordinator host (`OPS-54`), written funding caps (`OPS-41`, `OPS-56`) and the single-snapshot ancestry read (`WTC-24`) |
| 4 | stage 3, plus the sealed image (`OPS-53`), migration tooling (`OPS-59`) and the wallet-fallback field on `/healthz` (`API-19`) |
| 5 | the lifecycle decision closed (`OPS-62`), the lifecycle drill (`OPS-63`), and the durable-state work if the decision requires it |
| 6–8 | stage 5, plus alert consumption (`OPR-60`) and refresh-maturity monitoring (`OPR-62`) |
| 9 | stages 6–8, the freeze, the custody policy (`OPS-60`) and hardware signing (`OPR-31`) |
| 10 | stage 9 remediated (`OPS-68`) and the alpha's contents decided (`OPS-70`) |

**OPS-56** The dust-cap FIGURE of `OPS-41` is an owner decision: an implementer or tool MUST
propose a number and STOP, marking it as awaiting ratification, because an automated drain
that picks it is inventing custody policy. A cap is not set until a number is ratified AND its
observer exists, since an unobserved cap is undetectable when breached. Every stage MUST have
written **abort criteria** — what result stops the stage rather than being noted and climbed
past — and **descent rules** — what failure demotes the ladder a rung, a stage-8 attrition
event for instance returning to stage 7; a ladder that only defines climbing will be climbed.
The stage-8 **attrition abort threshold** MUST be stated as a live-node count before the run
starts, not during it: a 3-of-5 Survivor at three live nodes has zero margin.

**OPS-57** Completion evidence for stages 2–5 MUST additionally record that the bypass was
engaged deliberately, that without it the enforcement refuses this exact topology, and that
the artifacts are machine-readably tainted. Stage 3's Path evidence MUST execute the
release-identified operator program from the coordinator host's reproducible build against
the authenticated ingress, with no ad hoc install.

**OPS-58** Stage-vault custody MUST be stated before a stage is funded: who holds the 2-of-3
recovery keys for each vault, on the per-vault timelock policy of `OPS-27` and the no-shared
recovery keys rule of `OPS-34`. Which stages use REAL third-party recovery holders and which
use test keys MUST be decided and recorded (`F41`): with test keys throughout, Recovery from
cold artifacts is never once exercised under the real custody arrangement before the alpha,
and the drill proves the code path rather than the human arrangement it depends on.

## Migration tooling

**OPS-59** A migration MUST be driven by tooling that performs, in order: (1) create and VERIFY
a successor vault — a fresh ceremony whose output is checked against the predecessor's, REFUSING
a shorter timelock, a smaller federation, or a reused key; (2) move the funds by a claw-back
through the Normal path — never the recovery branch, never a path that
needs the duress subsystem; (3) retire the predecessor — deposit addresses dead (`OPR-59`),
burned secrets recorded, reuse of the old descriptor detectable; (4) assert that no key in the
successor appeared in the predecessor, which is what makes `OPS-32` checkable; (5) write an
audit record of what moved, when, from which vault to which, sufficient to reconstruct the
event without the Operator's memory. Before relying on the sweep the tool MUST verify the
predecessor can still compose a claw-back (`OPR-68`). Migration is
also the response to a compromise signal, so it MUST work when the predecessor is degraded,
stating the minimum live-node count it needs — the protocol floor is `t` not-locked-down nodes,
below which Recovery is the only exit (`OPS-22`). Verification: a full migration on regtest
from a five-node vault with one deliberately dead node; the successor check refuses a shorter
timelock and a reused key; the audit record reconstructs the event unaided.

## Custody policy and drills

**OPS-60** The custody plan of `OPS-33` MUST cover all nine key roles — the `n` node keys, the
user key, the coordinator auth key, the escape-wallet key and the 2-of-3 recovery keys held by
third parties — and MUST name a backup and an independence check for the **escape-wallet key**:
after a duress sweep every coin's safety reduces to that one wallet's custody, and if the
escape key is attacker-held then duress IS theft (`ADR-0003`). The escape-wallet key and its
backup MUST be held where a coercer holding the user cannot reach them within the sweep's
window: `OPS-33`'s check states that no single event may reach "the user together with the
escape wallet key or its backup", and a plan that places either in the user's home or on the
coordinator host fails it; the ceremony births the key on its own device
(`MAN-24`, `MAN-26`) and checks its independence (`MAN-28`), and where it lives afterwards is
this plan's to state and the set's to require, not to verify (`SEC-54`). It MUST state which compromise
signal forces which rotation (`OPS-30`), a procedure for hardware-key loss once hardware signing
lands, and a recovery-holder availability drill on a stated cadence (`F42`) that contacts each
holder and confirms they still hold the key and can use it; an inheritance key nobody has
touched in three years is a guess. The plan defines the drills; the physical instantiation —
which hardware, which safe — is the owner's.

**OPS-61** The custody drill MUST be a restore actually performed from backups alone with the
primary artifacts set aside, including the coordinator auth key (`SEC-36`), with the
failure-domain check of `OPS-33` run and recorded and each recovery holder confirmed reachable
within the stated cadence. It restores KEY MATERIAL and the human arrangements; it does not
restore a node (`OPS-63`).

## Node lifecycle

**OPS-62** The node lifecycle MUST be settled by an ADR choosing exactly one of: **(a)**
immutable one-shot nodes — every binary or configuration change is a migration, the preimage
is destroyed after first start, no supported restart; this is what `STO-1` specifies and is the
default, since the sealed image IS the one-shot model; or **(b)** recoverable hardware-backed
nodes — the signing key in hardware, restart supported, Lockdown a durable monotonic latch.
The decision takes stage-4 data (`OPS-44`) and nothing else, and the ADR MUST explicitly
supersede or amend every document it contradicts, because the failure mode being closed is
documents disagreeing. If and only if (b) wins, the five RAM-only states of `STO-2` MUST each
become durable, monotonic and rollback-resistant, and the watchtower MUST catch up over the
downtime window, BEFORE restart is supported; if (a) wins, that requirement is recorded as
not applicable with the reason.

**OPS-63** A destructive node-lifecycle drill MUST be performed: (1) reboot a node and confirm
it is dead exactly as `ADR-0007` claims; (2) restore from backup onto a fresh machine;
(3) lose quorum and recover; (4) migrate a vault end to end (`OPS-59`); (5) drive the 2-of-3
recovery branch from cold artifacts alone (`OPS-27`). It MUST record what actually happened,
including what broke — a drill that only reports success was not really run — and MUST be
reproducible by someone who did not design it. Afterwards every operational document MUST
point at the chosen model and no procedure may remain that a sealed node cannot perform.

## The freeze and its evidence

**OPS-64** A freeze applies to ONE named commit and its artifact set MUST contain exactly: the
full test matrix run against that commit with the toolchain, binary hashes, effective
configuration and harness artifacts recorded, including the property-based and
decoder-robustness suites; a FRESH public-chain spend against those exact binaries,
regenerating the spend record (`OPS-65`) at that commit; and the commit hash with an explicit
statement that the matrix and the record describe THAT commit and not the head of the branch.
A freeze MUST NOT be taken against a commit lacking the stage-1 code set — the operator
program's live commands (`OPR-42`, `OPR-67`, `OPR-72`), the configurable timelock (`OPR-78`),
the fee-ladder composer (`OPR-40`), the reproducible pipeline (`OPS-47`) — because a freeze
with no blockers closes today against a commit that silently stops describing the code.

**OPS-65** A public-chain spend record MUST state: the network, explicitly the default global
signet or mainnet and never a custom signet; txid, confirming block hash, height and time;
size, vsize, fee and effective feerate; every input with value; every output with address,
value and role; the witness item count and the branch it proves (seven items is the normal
branch: the `CHECKMULTISIG` dummy, `t` federation signatures, the user signature, the branch
selector and the witness script); the descriptor with checksum and the vault address; the
policy in force — threshold, Hold in seconds and that it elapsed on real wall-clock, combine
slack, commitment TTL and max age, Hot budget, escape floor and coverage, the refresh interval
and fee cap, the recovery timelock, policy version, max
derivation index; and the environment — commit, compiler and build tool versions, backend
version with `txindex=1`, the hash of each binary, the chain tip at the run. It MUST state its
own scope and staleness: which build profile the hashes describe, what it does NOT claim
(duress, claw-back, reorg and refusal behaviour on that chain), and that it describes one
commit and does not travel forward. It MUST demonstrate five properties: `n` separate node
processes each with its own keygen-born key against a live backend; the coordinator relayed
to exactly ONE node and that node propagated it, each peer re-running its gates; a real
non-zero Hold elapsed; the federation combined and broadcast — zero broadcast calls from the
operator program; confirmation in a real block under real relay policy.

**OPS-66** The Path suite (`OPS-38`) MUST be re-runnable: invocable, returning pass or fail,
parameterised by network and by which vault — the Survivor's four non-destructive paths or the
Sacrificial pair — and MUST NOT be a sequence of hand-driven commands recorded in a log,
because eight later rungs each say "full Path suite on both vaults" and without this the
phrase means something different every time.

**OPS-67** The launch gate MUST run on every push with a manual re-run trigger; on the default
branch its concurrency group MUST be commit-specific and in-flight runs MUST NOT be cancelled,
so every permanent commit keeps its own record; third-party actions MUST be pinned to commit
hashes. Steps MUST NOT carry an unconditional-run flag: the first failing step skips the rest,
the scorecard says per section which ran, log-teeing steps run under a shell that propagates a
pipeline's failure, and record assembly tolerates missing logs so a FAILED run still produces
diagnostics. It MUST retain as artifacts the lockfiles, the resolved toolchain and backend
versions, the source of the adversarial harness and every gated demo, the hash of each
executed binary, a per-step exit-code file and every log; an upload that finds no files MUST
fail. The gate's build profile is DEBUG deliberately — debug assertions and overflow checks
turn a wrapping amount bug into a panic — so a green run MUST NOT be read as evidence about a
release artifact; that gap belongs to the freeze and the reproducible pipeline. The reference
project's gate ran red for 48 consecutive runs before anyone looked (`SEC-51`).

## The stage-9 review and the alpha

**OPS-68** The stage-9 review's scope MUST include: a human security reviewer reading the
coercion procedure (`OPS-11`–`OPS-17`) end to end and signing off, with its round-by-round
defect history as the brief; a DRY RUN of that procedure by someone who did not write it, on
signet against a deliberately partial sweep, reporting where they got stuck — the only check
in the project that tests executability by a person lacking the author's context; silence end
to end, since the harness reports wall-clock timing as advisory only; and correlated-reviewer
blind spots, the project having a recorded instance of two reviewers asserting the same wrong
claim. Findings MUST be remediated and re-tested before stage 10, budgeting for the fact that
a material finding means a new binary, hence a rotation and a fresh soak. The hardware
signer's first appearance at stage 9 — the PSBT hand-off, the device-display boundary and the
escape co-sign — is a material configuration change the stage-8 soak did not exercise, and
the Path suite MUST be expected to find things there.

**OPS-69** The coercion procedure MUST NOT be closed by an automated review pass. It closes when
every step names a real operator command (`17-operator-program.md`) and the section agrees
with `ADR-0016` as checked at review time. The root cause of its history — prose describing
operations that did not exist has no implementation to be checked against — is why each
careful rewrite produced a new plausible-but-wrong instruction, and the eight defects those
rewrites produced are the prohibitions `OPS-10`–`OPS-17` now carry.

**OPS-70** The public alpha MUST be built from the STAGE-9 frozen artifact — the one the review
read, hardware signing included — through the reproducible pipeline, with signed artifacts and
published hashes that an independent party rebuilds byte-identically. It MUST carry, in the
artifact and not only a README: a warning stating what is unproven, the funding guidance, and
that the review was scoped to a specific commit; remediation evidence with a recorded
disposition per finding, re-tested against the shipped commit; and an honest statement of the
residuals that survive into it, `SEC-42` among them, because an alpha that does not say the
pre-wrench coordinator compromise is accepted rather than closed is misrepresenting itself.
An incident and disclosure path MUST exist before users arrive. What the alpha contains, its
support commitment and its warning text are owner decisions (`F43`). Non-goals: lifting the
caps beyond the ladder, any custody-grade promise, onboarding beyond alpha scope.

**OPS-71** A **Fault suite** SHOULD exist beside the Path suite, on deterministic regtest with
scripted backend faults, and is explicitly future hardening that gates no stage: kill one node
then two — mid-Hold, at `T`, after partial release, after Lockdown — and asymmetric partitions;
clock skew, rollback and forward jumps against Hold expiry, `T`, request expiry and channel
freshness; reorgs of hot spends, refreshes, escapes and recovery spends including below the
settled block of every completion marker the wallet holds; the whole escape ladder under fee
escalation, eviction and backend disagreement; coordinator crash and restart between fan-out, acceptance, polling and
retry; cold-artifact restore, coordinator-key loss, migration, recovery with fewer than `t`
live nodes; a deposit or refresh confirming during a Hold followed by a reorg; degraded
quorum — spend from four of five, and two of five refusing everything with Recovery the only
exit; coordinator restore onto a fresh machine; a stuck broadcast hot spend under a fee spike,
which has no bump path; and that alerts actually surface. Live reorg testing on a public chain
is not worth chasing, being unschedulable.

**OPS-72** A merged implementation change is never a rollout authorization. Closing the
tracker for a feature — the sealed network byte, the ingress cookie cap, any of the commands
above — authorizes nothing; only a stage's completion evidence (`OPS-38`) climbs the ladder.
