# 12 — Security requirements

Normative. The threat model, the load-bearing invariants, and the residual risks, each stated
as a requirement or as an explicitly accepted residual. This document cites the rule that
implements each property rather than restating it; where a sentence here and one in the owning
document disagree, the owning document is right and the disagreement is a defect to record.

## What is protected

**SEC-1** The protected asset is the coins, and the protected property is: **a spend happens only
when the user genuinely wants it, and a spend the user does not want can be stopped before it
settles — including when the user is being physically coerced.** Secondary assets are the node
signing keys, the two PIN digests, the coordinator auth key, the escape and recovery keys, and
the node preimages.

## Adversaries

**SEC-2** The design MUST hold against each adversary below to the stated extent, and an
implementation MUST NOT claim more:

| # | adversary | holds | the design's answer |
|---|---|---|---|
| A1 | remote attacker or malware on the coordinator, pre-wrench | the relay, network position | a trust failure, not an adversary the design defeats: it can read the normal PIN and nullify duress (`SEC-42`); node validation still bounds what it can authorize, and it holds no federation key |
| A2 | thief with the user key | the key, no PIN | cannot produce a valid request (`SPN-18`); the allowlist and Hot budget bound anything that does pass |
| A3 | thief with the user key and the normal PIN | both | bounded, not prevented: allowlist, per-transaction cap, velocity window (`POL-16`–`POL-20`), and the Hold gives the user a window to claw back (`OPS-15`) |
| A4 | coercion — the wrench | the user, and everything they know | the duress PIN: a ceremony identical to the attacker, silently arming a sweep at `T` and locking the federation down (`05`) |
| A5 | `c < t` compromised nodes | up to `t − 1` keys | cannot reach quorum; cannot release a coerced partial; the Hot bound is stated for `c < t` (`POL-20`); silence is NOT claimed against them (`SEC-10`) |
| A6 | `≥ t` compromised nodes plus the user key | a quorum and the key | **out of scope — this breaks the vault.** The threshold is the boundary |
| A7 | coordinator-auth-key thief | user key, PIN, and the auth key | can feed one node directly and let propagation arm the federation; bounded by allowlist, Hot budget and Hold; visible on every node's `/pending` (`API-21`) |
| A8 | chain-level adversary | miners, mempool, fee market | cannot steal; can delay: fee spikes, censorship and reorgs are met by the ladder, re-broadcast and reorg handling, and every failure degrades to frozen funds and Recovery |
| A9 | supply chain | a dependency or the build | bounded by a small dependency set and a written policy (`OPS-46`); weakly defended (`SEC-46`) |

## The compromise-and-loss matrix

**SEC-54** `SEC-2` names adversaries by what they hold. This matrix names the outcome for every
combination of what the attacker holds and what the Operator still holds, so that a decision
about any path — a new pin-less class, a changed sweep rule — is made against the cells it
moves rather than against a story. The secrets are `DOM-10`'s: the **user key** `U`, the
**coordinator credential** `C`, a **node quorum** `N` (`t` node keys) or fewer `n<t`, **two
recovery keys** `R`, the **escape wallet key** `E`, the **normal PIN** `P` and the **duress
PIN** `D`. "Attacker" is anyone acting against the Operator's wishes, the coercer included; the
coordinator host pre-wrench (`SEC-42`, `SEC-43`) holds `C`, reads `P` when it is entered, and
holds `U` while the user key is software.

Outcomes are exactly five words. **Nothing**: no valid request exists. **Bounded**: hot spends
inside the allowlist and Hot budget, clawed back inside the Hold. **Denial**: the coins reach the
escape wallet or Recovery, under the Operator's keys, later than wanted. **Theft**: coins reach
a wallet the attacker controls. **Loss**: coins reach a wallet nobody can spend. An Operator
loss row is the exit that remains.

The combination rule: a cell's outcome is the worse of its attacker row and its loss row,
ordered Nothing < Denial < Bounded < Theft < Loss, except where a row below names the
combination, and undefined where the loss removes the attacker row's own defence — a lost `C`
removes row 2's request entirely (Nothing, then Recovery); a lost `E` removes Bounded's
claw-back, so a row-2 thief drains `hot_max_per_window` per window until Recovery matures; a
lost `U` removes row 14's refresh, so every coin matures into the attacker's hands. The seven
cells decided on 2026-09-14 are recorded in `ADR-0021`.

| # | attacker holds | Operator still holds | outcome today | where it is enforced | status |
|---|---|---|---|---|---|
| 1 | `U` | everything | Nothing | `SPN-18`: no PIN, no valid request | settled (`A2`) |
| 2 | `U` `P` | `D` `E` `C` `N` `R` | Bounded; the Operator claws back without a PIN (`CHN-35`) | `POL-16`–`POL-20`, `OPS-15`, `OPS-19` | settled (`A3`) |
| 3 | `U` `P` `C` | `D` `E` `N` `R` | Bounded; the request reaches nodes directly and is visible on every `/pending` | `API-21`, `OPS-19` | settled (`A7`) |
| 4 | `U` `D` (or `U` `P` `D`) | `E` `N` `R` | Denial: the sweep pays the escape wallet the Operator holds | `DUR-2`, `CHN-14` | settled |
| 5 | `U` + any PIN + `E` | `N` `R` | **Theft**: a claw-back or a duress sweep pays the attacker's escape wallet | `OPS-60`, `ADR-0003` | settled: `E` custody is the whole defence |
| 6 | `U` `C` `E`, no PIN | `P` `D` `N` `R` | **Theft**: a claw-back needs no PIN (`SPN-50`) | `CHN-35`, `SPN-50` | decided 2026-09-14: accepted (`ADR-0021`, `ADR-0022`). This attacker has already defeated `OPS-60`'s custody rule for `E`, and no PIN defends against them, since the duress PIN pays the same wallet |
| 7 | `C` alone, or `C` + `n<t` | `U` `P` `D` `E` `R` | Nothing: no user signature | `CHN-11`, `SPN-5` | settled |
| 8 | coordinator host pre-wrench (`C`, reads `P`, `U` while software) | `D` `E` `R` | Bounded theft: hot spends up to the budget, and duress is nullified by PIN substitution | `SEC-42`, `SEC-43`, `ADR-0015` | settled, conditional theft |
| 9 | the wrench: the user, `U` `P` `D` `C` | `E` out of the coercer's reach, `N` `R` | Denial: duress sweeps to the escape wallet at `T`, Lockdown follows | `05`, `SEC-8` | settled (`A4`) |
| 10 | the wrench reaching `E` too | `N` `R` | **Theft**, at `T` or immediately by claw-back; against this coercer duress buys nothing and the set claims nothing | `OPS-60`, `ADR-0003` | decided 2026-09-14: `OPS-60` requires the escape-wallet key and its backup to be held out of a coercer's reach, and `OPS-33`'s failure-domain check names that reach; the set requires it and cannot verify it |
| 11 | `n<t` node keys, with or without `U` `P` | the rest | Nothing beyond row 2's Bounded; no quorum, no coerced partial; silence not claimed | `POL-20`, `SEC-10` | settled (`A5`) |
| 12 | `N` (a quorum) without `U` | `U` `P` `D` `E` `R` | Nothing: the Normal path needs the user signature | `CHN-1`, `CHN-11` | settled |
| 13 | `N` `U` | — | out of scope: the threshold is the boundary | `SEC-2` | settled (`A6`) |
| 14 | `R` (two recovery keys) | everything else | **Theft of every coin whose timelock has matured**; only refresh keeps a coin young, and Lockdown ends refresh. After Lockdown the recovery holders are the sole custody of every straggler the sweep left in the vault, for the whole timelock, with only `OPS-3`'s alert against them | `SEC-35`, `OPS-26`, `OPS-33` | decided 2026-09-14: settled as is. Refresh cadence, `OPS-33`'s failure-domain rule and the alert are the defence; no stronger custody rule, because the holders must stay reachable for `OPS-60`'s drill, and a custody plan is judged against the post-Lockdown sentence, not against "a backstop" |
| 15 | miners, mempool, fee market | everything | Denial: delay, then Recovery | `SEC-38`, `A8` | settled |
| L1 | — | lost `U` | Recovery after each coin matures | `OPS-26` | settled |
| L2 | — | lost `C` and its backup | Normal path bricked; Recovery | `SEC-36`, `OPS-20` | settled |
| L3 | — | lost the node quorum (more than `n − t` nodes dead) | Recovery | `DUR-18`, `OPS-26` | settled |
| L4 | — | forgot `P` | cannot spend; claw back, then rotate with new PINs | `OPS-15`, `OPS-30` | decided 2026-09-14: the claw-back needs no PIN (`ADR-0022`), so the remedy is same-day and needs neither the duress PIN nor the recovery holders |
| L5 | — | forgot `D`, or both PINs | no duress path until rotated; claw back, then rotate with new PINs | `OPS-15`, `OPS-30` | decided 2026-09-14: same remedy as L4, which was the strongest reason for the pin-less claw-back (`ADR-0022`) |
| L6 | — | lost `E` and its backup, and a sweep fires | **Loss**: the coins sit in a wallet nobody can spend, and no node can tell a live escape wallet from a dead one | `OPS-60`, `OPS-61` | decided 2026-09-14: the custody drill is the whole defence; the protocol adds nothing, since a proof of possession at seal time says nothing about a backup a year later |
| L7 | — | lost two of the three `R` | no Recovery; vault coins stranded after any freeze or Lockdown are permanently lost, while coins a sweep or claw-back reached under a retained `E` stay spendable | `OPS-33`, `OPS-26`, `OPS-30` | decided 2026-09-14: the custody drill is the defence, and one lost recovery key is a rotation trigger (`OPS-30`) while the Normal path still works, as a dead node is (`OPS-5`) |
| L8 | — | lost the descriptor backup | Recovery cannot be composed; the coins are unspendable once the federation is gone | `OPS-23` | settled: the backup is promiscuous by design |

Row 6 is the cell the pin-less claw-back moved (`ADR-0022`), and the reason the decision was
made here: before it, every coin that left the vault for anywhere but the vault itself needed a
PIN, the one factor that lives only in a human's head behind `MAN-23`'s attempt budget. Rows L4
and L5 are what the move bought.

## Trust boundaries

**SEC-3** **User to coordinator.** The coordinator is trusted before the wrench and hostile from
it (`DOM-2`). Its signature proves only "this vault's coordinator authored this request", never
that the request is legitimate. It MUST NOT persist the PIN (`DOM-4`), MUST hold it in RAM only,
and MUST never log it anywhere; the day a request is logged "for debugging", PIN substitution
comes back.

**SEC-4** **Coordinator to node** is the hard boundary. Every node re-runs every gate in
`SPN-5`'s order and never signs because it was told to (`NCH-3`).

**SEC-5** **Node to node.** A peer is transport. Authority is cryptographic, rooted in the sealed
manifest: envelope signatures by endorsed channel keys (`NCH-5`, `NCH-11`), partials verified
against recomputed sighashes (`NCH-24`).

**SEC-6** **Node to chain.** Each node runs its own backend and is its own watchtower; a node
that cannot read the chain fails closed (`WTC-1`).

**SEC-7** **The ceremony** is trusted (`MAN-37`). "Trusted until the wrench" describes the
operating coordinator, not the setup tool.

## Load-bearing invariants

Each is enforced by code, not convention; each is what a reviewer should try hardest to break.

**SEC-8** **SILENCE** (`DUR-1`). Across every observable a node emits, a duress ceremony is
identical to a normal one. Break it and the wrench attacker learns the duress PIN was used and
escalates. This is the invariant most easily lost to an innocuous new field or endpoint.

**SEC-9** **Signer/partial coupling and the release gate** (`DUR-8`). A partial is finalizable
authority the moment `t − 1` compromised peers hold it, so every fire-time check runs before
release and the gate is the sole egress. Break it and a `t − 1` set combines a transaction the
honest node refused.

**SEC-10** The **scope of SILENCE** MUST be stated wherever it is claimed: silence against a
coordinator that turns hostile at the wrench, across response bytes, timing class, `/events`,
`/healthz`, `/pending` and peer effects. It is not a claim that no adversary can learn the PIN
class: a compromised node sees the PIN in plaintext, and a coordinator compromised before the
wrench reads and substitutes it. End-to-end timing has no hard gate (`SEC-47`).

**SEC-11** **Unconditional Lockdown at `T`** (`DUR-7`), as a decision and never as a latency
(`DUR-15`). Break it and duress becomes survivable for the attacker.

**SEC-12** **Determinism across the honest set** (`OVR-9`, `POL-1`, `DUR-30`). Break it and
partials cover different transactions, no rung reaches `t`, and the Escape fails when needed.

**SEC-13** **Escape-key independence** (`DOM-11`, `MAN-28`). Break it and the sweep and the claw-back become
theft: the coercer controls the destination.

**SEC-14** **Policy purity** (`POL-1`). Break it and refusals stop being deterministic.

**SEC-15** **Fail closed** (`OVR-10`, `DUR-9`, `STO-10`). Every unknown, error or degraded state
refuses or locks down; funds route to Recovery rather than moving.

## Surfaces

**SEC-16** `/sign` is the main gate and its order is `SPN-5`. The nonce is consumed atomically
under the sign lock; the memory-hard work and the chain I/O are deliberately outside it, so
neither lengthens the section a waiting Lockdown contends for — but the acquisition delay itself
remains unbounded (`DUR-15`).

**SEC-17** `/channel` is manifest-pinned, endorsed, quota'd and size-bounded (`06`). The
diagnostic it publishes to `/events` MUST be pin-independent (`NCH-16`).

**SEC-18** `/events` carries on-chain watchtower alerts and one channel diagnostic, and nothing
about pending or armed state (`API-18`).

**SEC-19** `/healthz` is four atomic loads and MUST stay free of duress-dependent content
(`API-20`). The residual is co-residency latency, which reflects what else the host is doing
and is equally present on every surface and on the TCP accept.

**SEC-20** `/pending` lists sorted opaque ids only (`API-21`). Its bytes are asserted identical
across normal and duress and across armed-pre-`T` and idle twins. It is the one read surface
that waits on the sign lock, and it is NOT structurally isolated from arm-dependent work: the
release pass holds the same lock. What keeps its timing pin-uniform is dynamic `T` (`DUR-14`),
which keeps the pre-`T` due set empty on armed and idle nodes alike; if that ever stopped
holding this would need re-analysis. A separate, weaker residual: the route is unauthenticated,
so any network observer can poll it and infer that a request was being processed, including
one that was refused — a spend-activity timing channel, not a duress oracle.

**SEC-21** A post-wrench coordinator's power is exactly: censor, selectively deliver, strip
ladder rungs and re-sign, and submit a claw-back, which pays only the escape wallet (`CHN-35`:
"paying EVERY output to the escape descriptor"). Censoring or selectively delivering requests
can suppress the sweep or influence which selected Escape confirms, including by delivering a
request whose selected Escape inflates the coverage denominator (`DUR-22`: "an absent or inflated
prevout a selected Escape names is counted too"). Stripping uniformly or differently per node
only downgrades the `T`-time sweep, at worst to the base when that base is admissible. This
bound assumes a common base with matching user-signature material and enough successful fire
passes, quotas and partial delivery; it promises neither confirmation nor success under arbitrary
delivery failure (`DUR-28`: "This fallback requires enough successful fire passes, quotas and
partial delivery within the fire windows").
It cannot redirect funds, cause arbitrary bytes to be broadcast, create a new
attacker-authorized spend, or steal. A pre-wrench-compromised one can substitute the PIN
(`SEC-42`).

**SEC-22** The chain backend requires a synced transaction index and the sealed chain's identity
before any other check (`WTC-3`). The ceremony is the highest-consequence surface (`MAN-24`–
`MAN-38`). The node configuration and preimage are the at-rest surface: the key is derived at
start from a preimage the machine does not hold (`MAN-15`).

## The PIN

**SEC-23** Both enrolled digests MUST be evaluated on every request and the verdict selected in
constant time (`SPN-16`); a short-circuit would cost a duress PIN one extra Argon2 evaluation,
measurable by the coordinator-controlling attacker and averageable over replays. A byte-compare
alone is not sufficient.

**SEC-24** A valid duress PIN is a matching compare: it MUST never consume the attempt budget and
MUST arm regardless of lockout (`MAN-23`, `DUR-4`). The budget rate-limits wrong PINs only, so
flooding wrong PINs produces denial and never an unfrozen quorum.

**SEC-25** The PIN is plaintext to the nodes — Direction 3 of `ADR-0012`, accepted permanently.
A device-bound coordinator-opaque token would need hardware beyond PSBT signing; a two-key
device-visible scheme closes substitution but sacrifices the hostage window. Direction 3 stands
on two reasons: silence protects the person, and the residual is honestly bounded. The
allowlist constrains WHERE coins go, never WHO controls the destination; that is what makes the
Hot budget enforceable, and it is a narrower property than "stops theft".

**SEC-26** Higher-entropy PINs are defence in depth, not load-bearing: the one-compromised-node
duress trigger is closed by coordinator request signing (`SPN-7`), and duress detection by a
compromised node is already accepted.

## Deployment

**SEC-27** Every federation node MUST run on its own host, with its own backend, on genuinely
independent infrastructure. A deployment in which one host holds more than `t − 1` signing keys
is not a `t`-of-`n` deployment whatever the descriptor says: the first thing an attacker
should do is take that host, and `OPS-52` is what makes that misprovisioning fail at deploy
time.

**SEC-28** No correlation class — provider account, network block, physical location,
household, operator — MAY host `t` nodes (`ADR-0009`). From rollout stage 6 a deployment tool
MUST refuse such a topology; stages 2–5 run under `ADR-0015`'s test-only waiver with capped
funds, and any claim of compliance dates from stage 6. Sealing does not substitute for
diversity: a VPS is never sealed against its provider's console and rescue mode.

**SEC-29** The coordinator host MUST NOT itself become a correlation class: provider-console
sessions for the node hosts must not all live, logged in, on the machine that drives the vault
and sits beside the user under duress.

**SEC-30** Provider-account hygiene — strong second factor, no provider session on the
coordinator host — is part of the security perimeter of every sealed node (`ADR-0005`).

**SEC-31** A `/unseal` endpoint, a durable never-cleared Lockdown flag, and any location holding
`t` preimages are each individually rejected (`ADR-0007`); they are the reasons node
resurrection cannot be safely revived, not a roadmap.

## Residuals — accepted, and named

Every residual below is accepted deliberately. An implementation MUST NOT claim to have closed
one without the change that closes it being recorded against the finding.

**SEC-32** **`t` compromised nodes plus the user key is unrecoverable** (A6). The mitigation is
operational — `SEC-28` — not cryptographic.

**SEC-33** **Censorship** (`DUR-34`). A hot spend pending before the wrench can finalize at its
Hold expiry when the duress Carrier is kept from `t` nodes. User-authored and user-destined, so
attacker funds only with stolen hot keys. `POL-20` states: "The Hot budget provides an
**acceptance-time admission bound**, not a rolling completion-loss bound." A window of
completions can include admissions from different windows; the counterexample belongs to
`ADR-0014` and the conformance case is `CNF-58`.

**SEC-34** **The hostile-at-wrench crippled Escape.** The coordinator can compose a compliant
but crippled Escape; the coverage threshold and feerate floor bound it, and it can still strand
up to `100 − escape_coverage_pct` percent of the vault in Recovery limbo. Denial, not theft.

**SEC-35** **Post-Lockdown stragglers versus stolen recovery keys.** After Lockdown the Normal
path is dead and refresh is impossible, so straggler coins sit exposed to a recovery-key holder
for the timelock's duration with only an alert in opposition. Recovery-key custody is the sole
protection in that window.

**SEC-36** **Coordinator auth-key loss bricks the Normal path.** The pubkey is pinned in the
immutable manifest; rotation is a new vault, and the ceremony backs the key up separately for
that reason (`MAN-29`).

**SEC-37** **A matured pending spend collapses the hostage window** (`DUR-14`). `duress_delay_secs`
is a ceiling.

**SEC-38** **A sustained fee spike above what the ladder can pay** leaves the Escape unconfirmed
and the coins frozen for Recovery. It interacts badly with the 10% fee cap on small vaults.

**SEC-39** **A pre-positioned vault-authorized replacement of an Escape's unconfirmed parent**,
signed before the wrench and broadcast after it under full-RBF, removes the Escape's chained
input; the outcome matches accepted total censorship — funds safe, Lockdown, no theft.

**SEC-40** **No external human has reviewed this system** (`ADR-0017`, `F18`). One review, at
rollout stage 9, gates the lift of the dust caps; three capped mainnet rungs run before it with
the cap as the mitigation. Correlated automated review panels — including the reference
project's own — are not a substitute, and this set must not be read as evidence that a review
has happened.

**SEC-41** **The Recovery path is the only exit from Lockdown, and it is not private.** A
Recovery spend is branch-identifiable on-chain by construction (`CHN-9`).

**SEC-42** **A coordinator compromised BEFORE the wrench nullifies duress.** Persistent malware,
a poisoned build, a tampered dependency, or a wrench that begins mid-spend while the normal PIN
is in RAM: any of these reads the normal PIN and substitutes it, so the Escape never arms, no
node locks down, and — because every observable is pin-uniform by design — the user sees exactly
what a working duress path would show. This is **conditional theft**, not mere nullification:
the coerced hot spend completes after the Hold, and an attacker who also holds the hot keys owns
it. The mitigations map vector by vector: reproducible builds close the poisoned-build and
tampered-dependency vectors (`OPS-47`); a hardened dedicated coordinator host reduces the
probability of resident malware without removing the capability; **nothing** addresses the
mid-spend wrench. The residual is likelihood-reduced but unclosed, and it would remain unclosed
if both mitigations shipped. The remaining controls are the Hot budget and velocity window,
the Hold, the allowlist, and hardware user signing; they do not justify a rolling loss budget
(`POL-20`: "No replacement rolling completion-loss formula is specified."). The only true
prevention is a device-bound PIN, which is hardware-gated and unplanned.

**SEC-43** **The user key is software in every current driver**, on the coordinator host, which
merges A3 with `SEC-42`: an attacker who owns that host skips the wrench and signs. Hardware
signing is deliberately deferred past the dust-capped rollout rungs and MUST gate the lift of
the caps (`ADR-0015`, `OPS-37`).

**SEC-44** **Reboot-death is an assumption enforced by a warning** (`STO-3`). The node warns on a
non-volatile filesystem and proceeds only under an explicit override; in that state the model's
premise does not hold.

**SEC-45** **A wall clock already wrong at Carrier acceptance** makes `D` too early or too late
(`NCH-33`). Later excursions cannot delete or extend Carrier state, but no local stopwatch can
prove the admission sample was true. The ordinary outcome is denial; composed with `t − 1`
compromised nodes and stolen hot keys it is the same conditional theft as censorship, with the
admission/completion distinction recorded in `SEC-33`.
Closing it needs external time authority and is not part of this revision.

**SEC-46** **Supply chain is defended by a written policy and a build discipline**, not by
cryptographic provenance a user can check on the chain. `OPS-46` and `OPS-47` are the whole
defence; an implementation that has not met `OPS-47` is defended by policy alone.

**SEC-47** **End-to-end timing has no hard gate** (`F22`). The deterministic replacement compares
response bytes, ordered handler operations and pin-masked state projections across eight request
shapes, ending at handler return; post-handler fan-out and arbitrary CPU cost are exercised by
live scenarios with no pass/fail on timing. SILENCE remains normative; this is the evidence
boundary.

**SEC-48** **The delay before Lockdown at `T` has no finite bound** (`DUR-15`, `F13`).

**SEC-49** **The freshness high-water can blackhole an honest peer for unbounded real time**
(`NCH-38`, `F3`), and an unrelated Refresh can advance the coordinator-nonce high-water past a
live Carrier (`SPN-12`, `F4`).

**SEC-50** **The full UTXO-set scan remains the fallback** (`WTC-6`): on a node whose backend
cannot serve the descriptor wallet, every refresh pays it, and Bitcoin Core serialises it
process-wide. It is availability, not theft, and its mainnet cost is an implementation's to
measure before it relies on the fallback.

**SEC-51** **Real-chain evidence is an implementation property.** Which paths an implementation
has exercised on a public chain, and which only on regtest, is recorded by that implementation;
this set claims none of it.

## What a reviewer should attack first

**SEC-53** In order of damage if wrong: SILENCE — diff every observable between the two PIN
classes, hunting a length-preserving difference; the release gate — any path where a partial
leaves before every fire-time check, or any second egress; determinism — two honest nodes that
could disagree on a verdict or a rung from the same chain state, especially across
manifest-pinned fields; Lockdown unconditionality — a failure that skips it, since delay is
already known and unbounded; the ceremony — a way to seal a vault whose manifest, descriptor,
keys or coordinator secret disagree, or an independence violation past `MAN-28`; fail-closed-ness
— an error path that moves coins or admits a spend.
