# 16 — Open findings

What a builder must know before building: the design questions this set has not settled, who
settles each, and the three questions to ask first. Findings are numbered `F1`… in the order
they were carried into this set; the number is stable and never reused, and a finding that
closes moves to the withdrawn list at the end rather than disappearing. Each names the
reference project's tracking record (`btc-policy-<id>`) where one exists, so the ledgers can be
joined.

This document records **design** state only. Whether a given implementation has built a given
requirement is not a finding and is tracked in that implementation's repository (`OVR-17`).

**Status words.** *OPEN* — a design question with no decided answer; an implementer inherits it
and MUST NOT write a MUST for it. *OWNER DECISION* — open, and the answer is the vault owner's
to give, not an implementer's: propose and stop. *CONTINGENT* — open only if another finding
resolves a particular way. *CLOSED* — a correction already made to this set itself; its identifier
moves to the withdrawn list below and its narrative to the non-normative `docs/archive/`.

## The three questions a builder must ask first

1. **Is the deployment shape the one the security claims assume?** Every requirement in this set
   is written for `n = 2t − 1` nodes on independent hosts with authenticated transport (`CHN-2`,
   `NCH-1`, `SEC-28`); rollout stage 1 runs on one host with loopback endpoints and stages 2–5
   under an explicit waiver (`OPS-40`). The transport that makes the claim true from stage 2 is
   specified (`OPS-50`–`OPS-52`) except for its mechanism (`F37`). Build the transport or state
   that you have not.
2. **Which node lifecycle are you building?** This set specifies immutable one-shot nodes
   (`STO-1`–`STO-4`); the alternative and the procedure for choosing it are `OPS-62` and `F8`.
   If you build the other, five RAM-only security states must become durable first (`F9`).
3. **What does the operator program leave undecided?** `17-operator-program.md` specifies every
   command. Two questions inside it are still open — what happens when the alert channel is
   down and whether the recovery-key alert needs a coordinator-independent path (`F45`), and the
   numeric safety margin (`F46`) — and the input topology that keeps the fast exits composable
   (`F1`).

## Findings

**F1. OPEN — toxic inputs and one-UTXO consolidation can disable the fast exits.**
(`btc-policy-yw4`.) A confirmed external deposit can pay the vault script from a consensus-valid
very large parent, or fragment the vault into enough confirmed outputs, without any vault
authorization; because every signer PSBT input carries its full previous transaction (`CHN-22`)
and the node bounds request and envelope size (`API-4`, `NCH-10`), a large or fragmented deposit
makes the normal Spend and its Escape uncomposable. (The consolidation half of this finding —
the one-change Spend leaving no disjoint residual for the claw-back — closed with `ADR-0022`: a
claw-back sweeps one coin as readily as many, `CHN-35`.) Funds remain under vault and Recovery
authority; what is lost is the fast exit. Candidates: deterministic bounded input selection, two vault-change outputs, another
reserve topology, or a revised full-prevtx proof carrier. Whatever is chosen MUST never omit
value in a way that fails `DUR-22`'s coverage, never trust `witness_utxo` or script equality in
place of prevout authority, keep `SIGHASH_ALL` and all-validation-before-signature, stay inside
the size bounds of `OPR-35`, re-derive the change-outpoint watch anchor atomically with any change-output edit, and
distinguish an unsupported toxic fragment from insufficient funds.

**F2. OPEN — composition over vault-authorized unconfirmed value has no chosen mechanism.**
(`btc-policy-w2b`.) `DUR-22` requires the Escape to cover confirmed plus vault-authorized
unconfirmed value, and `OPR-39` composes over confirmed coins only, refusing loudly when a coin
is mempool-spent. A second Spend therefore cannot be composed for as long as a prior vault
spend is mempool resident, which has no protocol time bound and is not cured by eviction. The
candidate primitive set — Bitcoin Core's `gettxspendingprevout` plus qualified raw-transaction
reads plus a bounded ancestry walk — is not frozen; downloading an unbounded mempool and a
generic wallet escape hatch are ruled out; the node's coverage denominator MUST NOT be weakened
to close this.

**F3. OPEN — a forward freshness high-water can blackhole a peer for unbounded real time.**
(`btc-policy-r1g`.) The channel ingress guard advances its high-water to `max(high_water,
raw_now)` and never lowers it (`NCH-13`, `NCH-38`). A receiver clock that jumps forward past the
300-second tolerance and is then corrected leaves every honest envelope stale until real time
catches the latch. The consequence is bounded (`NCH-38`); the outage is not. The two named
directions, neither chosen and either only after its replay and state-oracle consequences are
proved: bounded high-water decay, or an exact authenticated-message exception. The bar for a
fix: corrected traffic makes progress within a stated finite bound without accepting a captured
or replayed envelope, without bypassing quota, without consuming a nonce on refusal, and
without a PIN-dependent observable.

**F4. OPEN — an unrelated Refresh can advance the coordinator-nonce high-water past a live
Carrier.** (`btc-policy-i3p`.) The nonce log shares one non-decreasing high-water across Spend
and Refresh entries (`SPN-12`); a transient forward excursion can prune a Refresh whose expiry
is later than a live Carrier's `E`, latching the high-water there, so the Carrier's receipts
read as wall-expired until `E` or `D` ends. `NCH-36` and `NCH-37` state the premise every
recovery claim must carry. Options: split the high-water per entry class; sample raw wall time
for the receipt path; or keep the shared authority and the stated bound. Any fix preserves
rollback protection for forgotten nonces (`SPN-13`), capacity accounting, accepted-`D`
immutability and PIN-uniform work, and MUST NOT lower the channel high-water, which is `F3`'s.

**F8. OPEN — the node lifecycle decision waits on stage-4 attrition data.** (`btc-policy-nju`.)
`OPS-62` is the procedure: one ADR choosing immutable one-shot nodes — the specified default —
or recoverable hardware-backed nodes, from stage-4 measurements alone, superseding every
document it contradicts.

**F9. CONTINGENT — five RAM-only security states would need durability before restart.**
(`btc-policy-juq`.) If `F8` resolves to recoverable nodes, the states of `STO-2` plus watchtower
catch-up must become durable, monotonic and rollback-resistant before restart is supported;
each alone reopens a theft or brute-force path if missed.

**F13. OPEN — the delay before Lockdown at `T` has no finite bound.** (`btc-policy-1y2`,
`btc-policy-wqd`; `SEC-11`, `DUR-15`.) The transition is unconditional as a decision, but it
needs the one sign lock, that lock is unfair, admission control sheds rather than bounds
successive work, and a post-wrench coordinator can mint requests indefinitely. What bounds the
consequence is the release gate (`DUR-8`). No mechanism that would bound the delay is on the
table; the finding exists so nobody claims one by accident.

**F14. OPEN — per-rule authority is a mechanism nobody has yet seen fail.** (`btc-policy-0ip`.)
The reference project counted twelve "same claim, two places, one updated" defects across
twenty review passes; its preimage field list existed in eight places and one correction pass
fixed three files and missed further copies inside two of them. This set is the structural
answer — one requirement per rule, an executable preimage, a citation gate — chosen over
generation from code and over a drift-detecting grep. The residual: the mechanism MUST be
shown to catch a planted contradiction in each of the three historically drifted rules
(`CNF-113`); until it has, it is not known to work.

**F18. OPEN — no external human review has read this system.** (`ADR-0017`, `SEC-40`,
`OPS-68`.) One review, at rollout stage 9, gating the lift of the dust caps; everything up to
three capped mainnet rungs runs with no outside eyes, deliberately. Correlated automated
review is not a substitute.

**F21. OPEN — the coercion procedure needs a human security reviewer and a stranger's dry run.**
(`btc-policy-tv3`; `OPS-18`, `OPS-68`, `OPS-69`.) The section was rewritten repeatedly by
automated review, each round finding a defect the previous fix introduced, several
safety-relevant. It is not to be closed by another automated pass.

**F22. OPEN — end-to-end SILENCE timing has no hard gate.** (`SEC-10`; `btc-policy-c9r`.) The
wall-clock skew between normal and duress ingress is reported as advisory because CI variance
exceeded the effect the gate was meant to detect; the deterministic replacement (`CNF-40`) ends
at handler return and covers neither post-handler fan-out nor arbitrary CPU cost.

**F34. OWNER DECISION — the dust-cap figure.** (`btc-policy-cod`; `OPS-41`, `OPS-56`.) No number
exists anywhere. Constraints: dust-level minimum, aggregate across every live stage vault, an
independent observer before funding, and raising it on a waived stage voids `ADR-0015`.

**F35. OWNER DECISION — per-stage abort criteria, descent rules, and the stage-8 attrition
threshold.** (`btc-policy-cod`; `OPS-56`.) Entirely unwritten; the one worked example is a
stage-8 attrition event returning the ladder to stage 7. The threshold is a live-node count to
be fixed before the run; three live nodes on 3-of-5 is zero margin.

**F36. OWNER DECISION — which second machine verifies the reproducible build, and who holds
the release signing key.** (`btc-policy-oy3`; `OPS-47`.) A CI runner or a second developer box;
and a named key holder with a stated distribution path for the public half. "A signature
nobody can check is decoration."

**F37. OPEN — the authenticated transport mechanism.** (`btc-policy-imb`; `OPS-51`, `MAN-4`,
`NCH-2`.) Onion addresses derived deterministically from node key material, or mTLS; either way
endpoints stay manifest-pinned and endorsed, and clearnet dynamic-IP topologies are unsupported.
Nobody has chosen, and the selection is currently homeless between the runtime work and the
hardening it excludes.

**F38. OPEN — the read-surface perimeter on real links.** (`OPS-51`, `SEC-20`.) For each of
`/pending`, `/healthz` and `/events`: public, firewalled to the coordinator, or authenticated;
recorded at stage 2 before the nodes are reachable. `/pending` is a spend-activity timing oracle
for any peer holding no keys, ranked when nodes were unreachable on loopback. "Firewalled to
the coordinator" and `OPS-2`'s poll-every-node are compatible only if the ingress reaches all
`n`.

**F39. OPEN — the per-link partition attack on real links.** (`DUR-15`, `OPS-51`.) Arming one
node while an unfrozen quorum remains was accepted with every link on one box; on real links it
is live attack surface. Re-accept with a written argument, add a mechanism, or change the
release-gate analysis; none is preferred in the record.

**F40. OPEN — how a sealed image reaches a host that has no SSH, and its format.**
(`btc-policy-nwd`; `OPS-53`.) The image's contents and prohibitions are specified; the delivery
mechanism, the image type, and how a provider console is used at provisioning time without
becoming an administrative path are not.

**F41. OWNER DECISION — which rollout stages use real third-party recovery holders.**
(`OPS-58`.) Real holders throughout, test keys throughout, or real from a named stage. With
test keys throughout, Recovery from cold artifacts is never exercised under the real custody
arrangement before the alpha.

**F42. OWNER DECISION — the recovery-holder availability drill cadence.** (`btc-policy-34m`;
`OPS-60`.) A stated cadence with no value; the only reasoning on record is that three years
untouched is a guess.

**F43. OWNER DECISION — what the public alpha ships.** (`btc-policy-f6y`; `OPS-70`.) Contents,
support commitment and warning text.

**F45. OPEN — alert delivery when the channel is down, and whether the recovery-key alert needs
a coordinator-independent path.** (`btc-policy-2oz`; `OPR-60`, `OPR-61`.) Coordinator-pull
suppression is accepted for the wrench case; the reasoning does not extend to
`RECOVERY_PATH_SPEND`, which fires when nothing else is wrong. If an independent path is
wanted it is a design question to raise, not to implement silently; and what the program does
when its notification channel is down must be stated.

**F46. OWNER DECISION — the numeric refresh safety margin.** (`btc-policy-msj`; `OPS-6`,
`OPR-63`.) Decided only that it is a fraction of the vault's own timelock, never a day count.

**F47. OPEN — the Lockdown latch write on a runtime worker.** (`btc-policy-wqd`; `STO-9`,
`STO-4`.) The extended-attribute write plus sync on the post-await poison path runs on a runtime
worker: blocking I/O, not a lock, on the poison path only. Accept explicitly as a documented
exception, or move it with the rest.

**F48. OPEN — whether a node accepts a `/sign` PSBT whose inputs carry no full previous
transaction.** (`CHN-22`, `OPR-46`, `SPN-25`.) The signer requires `non_witness_utxo`, the wire
strips it after signing, and the node takes prevout truth from its backend. The node-side rule —
refuse, ignore, or verify when present — is unstated, and it matters for `F1`'s size bounds.

**F49. OPEN — how a finalize retry proves a stale staging directory is orphaned.**
(`btc-policy-sq7`; `MAN-32`, `OPR-80`.) A process id in the name is not proof, because ids are
reused; the reference discloses the residue and tells the operator to inspect it. The
mechanism — a token, a lock file, or the chosen equivalent — is open; treating pid existence
alone as proof is ruled out.

**F60. OPEN — a backward clock correction after arming reopens a pre-`T` SILENCE leak.**
(Specification repository, found 2026-09-19 while stating the SILENCE
relation; three independent readers on one brief
against `e74d9ff`, each building the same trace independently.) `DUR-13` computes `T =
max(t_ceiling, now)` at the holder decision, clamping a matured deadline to the current sample;
`DUR-13` annotates the clamp "a past T fires now". The sample is the effective time `max(high_water,
raw_now)` (`SPN-13`), and the high-water "is advanced, on an accept only". So with no
intervening accept, a wall clock corrected backward after the arm lowers the effective sample
below the `T` that arm just wrote, and a fire pass in that gap sees a hot candidate whose fire
window is open and whose `T` has not been reached: under the normal PIN it queues a partial,
under duress `DUR-11`'s freeze holds it. That is a PIN-dependent observable strictly before `T`,
which `DUR-1` forbids.

The trace: ingress at 40, `duress_delay_secs` 200, a hot candidate with `fire_at` 90,
`epsilon_secs` 5, a holder decision sampling 100, so `T = max(min(240, 85), 100) = 100`. The
wall is then corrected to 95 with no accept between, so the effective sample is 95: the window
at 90 is open, 95 is below `T`, and the two PINs diverge. The relation in `ADR-0023` decision 14
therefore carries a non-decreasing-sample hypothesis on its prefix, so a reader of the theorem
sees this gap in its signature; the trace is retained as a negative exhibit beside `F3`, `F4`
and `F13`, and `BtcPolicy.Exhibits.TwoRun.f60_backward_step_leaks` runs it: all three steps
inside the horizon, the third pair unequal, a hot partial queued at 95 under the ordinary PIN
and `DUR-11`'s freeze holding it under duress. It refutes no theorem here: the trace fails
`silence`'s non-decreasing-sample premise, the wall stepping back where the HotClock does not.

Two directions, neither chosen, and either only after its replay and observable consequences
are proved: advance the high-water to `T` at the holder decision, which is pin-uniform work
(`DUR-5`) but amends `SPN-13`'s accept-only rule and interacts with `F3` and `F4`; or refuse a
fire pass any sample below the last `T` write, a guard local to the driver that leaves
`SPN-13` alone. The bar for a fix: no PIN-dependent observable before `T`, no nonce consumed on
refusal, no new capacity or replay oracle, and `DUR-14`'s ceiling semantics preserved.

**F62. OPEN — a released Hot reservation can be resurrected by a backward wall step, putting a
ledger above the cap.** (Specification repository, found 2026-09-20 by the same panel.)
`POL-19` states liveness as a predicate: "`live ⇔ reserved_at ≥ now_mono − window_secs ∨
wall_now ≤ expiry`, both boundaries inclusive". The row that predicate reads outlives the
candidate, because `SPN-33` says "the ledger retains its original reservation time, expiry and
exposure state independently of candidate residency". Evaluated afresh at each admission, a
charge whose two disjuncts were both false, and whose budget a node has therefore already
reclaimed, becomes live again when a backward wall step puts `wall_now` back at or below
`expiry`. The live sum can then stand above `hot_max_per_window` with no rule broken.

The direction is conservative — a larger live sum admits fewer spends, never more — so this is
not an over-admission path. What it costs is the invariant: `POL-20`'s "each ledger holds at
most `cap`" is then false at some reachable states, and the accounting bridge in `ADR-0023`
decision 14 cannot discharge it as an induction over the transitions. The model takes age-out as a one-way release, which
makes the invariant true and diverges from the predicate exactly when a wall step goes
backward, the family `F60` records.

Two directions, neither chosen: state `POL-19`'s release as one-way, so a reclaimed charge is
never re-created and the predicate is the condition for releasing rather than a membership test
re-run; or keep the predicate and weaken `POL-20`'s hypothesis to the live sum at each counted
acceptance, which is what `POL-16` actually checks. The bar for a fix: the counting hypothesis
provable by induction, no reachable state that admits more than `POL-16` would have admitted on
a monotone clock, and no PIN-dependent observable (`POL-21`).

**F63. OPEN — the Hot budget's accounting unit is the commitment, and one transaction can hold
two of them.** (Specification repository, found 2026-09-20 while reviewing the Hot ledger landed
that day; three independent readers on one brief
against `42473ef`, each building the same trace independently.) `CHN-27` says "A changed
transaction or expiry gets a fresh commitment and evaluation", and `POL-18` places a reservation
"idempotently per commitment". So a coordinator that re-quotes one transaction with a later
expiry — which `SPN-10`'s `expiry ≤ raw_now + max_commitment_age_secs` ceiling eventually forces,
since `NCH-35` forbids extending an active Carrier — is charged twice for one `hot_outflow` that
`POL-11` computes from the outputs alone. Under `POL-17`'s "equality meaning one maximal spend may
consume the whole window" a maximal spend therefore cannot be re-quoted inside its window at all.

This is what `POL-18` specifies, not a departure from it, and the panel divided on whether it is a
defect: two readers called the double charge the defect, the third that it is presently specified
conservative accounting and that changing it is a separate protocol decision. What all three
agreed is that the accounting unit is nowhere stated: `POL-16` meters "every hot-class spend it
ACCEPTS", `POL-18` makes the reservation per commitment, and `ADR-0023` decision 9 keys the
exposure that decides refunds per `(sighash message, input, signer)` at world level. Three units
for one quantity.

`ADR-0014` records the over-count as deliberate, but every case it names is a CONFLICTING
replacement: "an RBF fee-bump or a re-issued spend of the same vault UTXO is a fresh commitment …
and takes its own full reservation", carried by "Two conflicting txs can never both confirm, so
`k` bumps over-count `k`×". A re-quoted expiry is one transaction, which cannot confirm twice, so
that argument does not reach it; the sentence's two halves want separating.

The refund reads the same unit and inherits the gap. `POL-18` releases a reservation only where
the candidate is terminal "without ever having released its partial", which is false at the
transaction level once its twin has released. The reachable trace, over the landed model, which
`BtcPolicy.Exhibits.HotLedger.f63_twins_end_charging_nothing` runs: the released twin's row ages
out first, and the expiry sweep then refunds the unexposed twin, leaving the node charging
nothing for a transaction its own signature still finalizes
(`BtcPolicy.Exhibits.HotLedger.f63_exposure_outlives_the_charges`). **`POL-20` is not
violated** — its cohort already excludes a refunded reservation, and the residual is the one it
states, "Already exposed signatures also remain valid after their reservations age out" — and the
same trace with a single commitment ends in the same place, so the refund reaches no state that
age-out alone would not.

Two directions, neither chosen. Meter the exact transaction once: one row keyed by the txid
`SPN-33` already adds to the vault-authorized set (`WTC-18`: "The authorized set is the txids of
every spend, Escape, rung, refresh and claw-back this node accepted"), its amount `hot_outflow`,
its exposure the OR over the commitments that name it, refunded when unexposed and every such
commitment has expired — replay stays commitment-keyed, and a fee-bump still takes its own charge
because it is a different txid. Or keep the commitment as the unit and say so where the meter is
defined, splitting `ADR-0014`'s sentence so the re-issued-same-transaction case is named and
priced separately from the RBF case. The bar for a fix: nothing netted across distinct
transactions (`ADR-0014`), the outpoint set still not a lookup key (`CHN-27`), the bridge's
`hcap` still provable by induction, and a re-quote's admission verdict independent of the PIN
(`POL-21`).

| Defect | Owner and verification |
|---|---|
| The accounting unit is stated three ways: `POL-16` meters a spend, `POL-18` reserves per commitment, `ADR-0023` decision 9 keys exposure per world-level signer | `POL-16`, `POL-18`; `BtcPolicy.Ledger` |
| `ADR-0014`'s non-netting argument covers conflicting replacements and is applied to a re-quote of one transaction, which cannot confirm twice | `ADR-0014` |
| `POL-18`'s refund premise — "without ever having released its partial" — is read per candidate where the authority is per transaction | `POL-18`, `SPN-33`; `BtcPolicy.Ledger.sweep_refunds_only_unexposed_and_expired`, `BtcPolicy.Exhibits.HotLedger.f63_twins_end_charging_nothing` |

**F64. OPEN — a later holder decision rewrites `T` on an armed node, and can grow it.**
(Specification repository, found 2026-09-20 while stating the SILENCE
relation.) `DUR-5` requires a normal holder decision to perform "the identical scan, overlay
write, applicable set insertion and window refresh as its duress twin with the same local
acceptance and pair-binding outcome", so the overlay deadline is written under both PINs at
every commit. The 2026-10-02 inheritance amendment makes `DUR-13` use "the earliest `first_seen`
among this intent, every resident intent and every retained nonce tombstone (`NCH-40`) naming
the same spend commitment, under **both** PINs". Its bound on a rewrite remains "When already
armed, a later arm MAY only shrink `T`" — a later *arm*. A later NORMAL commit for another,
unmarked pair on an armed node is neither exempted from the write nor bounded by the shrink
rule. If that pair's earliest `first_seen` is later, it writes a larger `T` whenever no pending
hot candidate pulls the ceiling down:
`BtcPolicy.Exhibits.TwoRun.later_commit_grows_T` runs it, arming at `T = 250` and reaching
`T = 800` on the next ordinary commit. `DUR-15` already records who can produce the requests that
do it — "a post-wrench coordinator holding the auth key can mint validly signed requests
indefinitely" — so the hostage window is extensible by an adversary that never learns the PIN
class. `SEC-11` names "**Unconditional Lockdown at `T`** (`DUR-7`), as a decision and never as a
latency", which is about the decision and says nothing about `T` moving.

Two directions, neither chosen: bound the write to the shrink under both PINs — `min` of the new
value and the current one, computed unconditionally so the work stays pin-uniform, which changes
the specified value on an unarmed node, where `T` is meaningless until an arm; or state that the
rewrite is the rule and bound the ceiling another way. The bar for a fix: pin-uniform work
(`DUR-1`), `DUR-13`'s `first_seen` provenance kept, no PIN-dependent branch on `armed`, and
`DUR-14`'s ceiling semantics preserved.

Beside it, and not a defect: the leak `DUR-14`'s rationale describes — "a post-arm hot spend with
a nearer Hold expiry would settle visibly under the normal PIN and be frozen under duress" — has
no trace in this model, because a candidate is due only with its quorum (`SPN-38`) and the only
opening rule is `SPN-37`'s "opened only by the holder decision of a Carrier naming it"; that
decision recomputes `T` over the pending hot candidates (`DUR-13`). `DUR-14` is what holds between that acceptance and that decision, and the
formal invariant needs it there: `BtcPolicy.Exhibits.TwoRun.static_bound_fails_with_withdrawn` is
the bound failing at a reachable state under the static value, not a partial leaving.

## Withdrawn findings

Never reused. Listed so an older citation still resolves.

| Finding | Was | Why it went |
|---|---|---|
| `F5` | The federation is not independent and the transport is loopback | Implementation status; the design is `OPS-50`–`OPS-52` and the open mechanism is `F37` |
| `F6` | The harness was blind to a mixed hot-plus-escape spend | Implementation status; the prohibition is `DEF-15` and the item is `CNF-22` |
| `F7` | One harness scenario was load-sensitive | Implementation status; the rules are `CNF-4` and `CNF-112` |
| `F10` | The operator program was incomplete | Implementation status; the program is `17-operator-program.md` |
| `F11` | Alerts reached no human and maturity was unmonitored | Implementation status; `OPR-60`–`OPR-64` |
| `F12` | The recovery timelock was frozen at 180 days | Decided: per-vault with no hard floor, `CHN-4`, `OPR-78` |
| `F16` | `n ≤ 15` was not machine-checked | Decided: enforced by the template parser, `CHN-2` |
| `F17` | The ceremony's parent namespace was substitutable | Decided: validated and refused, `MAN-40` |
| `F19` | The two most severe residuals were mitigated by documents, not code | Implementation status; the mitigations are `OPS-47`, `OPS-54`, `OPR-31` and the residual stays `SEC-42` |
| `F20` | Supply chain was defended by policy, not tooling | Implementation status; `OPS-47` |
| `F23`–`F31` | Defects closed in the reference implementation | Implementation history; each is a prohibition in `14-known-defects.md` |
| `F15` | the refresh bounds are sealed; the PIN attempt budget is node-local by decision. | Corrected at `ADR-0018`, `MAN-2`, `MAN-27`; [archived narrative](docs/archive/closed-findings.md) |
| `F32` | incompatible rules and ineffective checks: admission accounting read as a completion-loss guarantee, an expiry predicate that selected live entries, and a gate that checked copied constants. | Corrected at `POL-20`, `ADR-0014`, `SPN-42`, `CHN-20`, `MAN-17`, `MAN-39`, `CHN-25`, `SPN-21`, `SPN-23`, `ADR-0013`; [archived narrative](docs/archive/closed-findings.md) |
| `F33` | conflicting implementer contracts across replay, settlement, the release cursor, signing groups and response rules. | Corrected at `SPN-23`, `SPN-24`, `SPN-33`, `SPN-38`, `CHN-22`, `CHN-23`, `WIR-6`, `NCH-24`, `API-3`, `WIR-1`; [archived narrative](docs/archive/closed-findings.md) |
| `F44` | whether the residual of an escape-class pair gets a fee ladder. | Corrected at `ADR-0022`, `CHN-35`; [archived narrative](docs/archive/closed-findings.md) |
| `F50` | values that existed only as a library's behaviour, with no bytes or rule of their own. | Corrected at `CHN-34`, `SPN-38`, `SPN-9`, `API-21`, `WIR-11`, `MAN-2`, `NCH-11`, `WTC-2`, `DUR-10`, `ADR-0020`; [archived narrative](docs/archive/closed-findings.md) |
| `F51` | `SPN-38`'s cap anchored on the cursor, so a candidate whose lowest admissible rung sat above the cursor released nothing, forever; and two interop splits. | Corrected at `SPN-38`, `SPN-47`, `CHN-34`, `DUR-30`, `MAN-2`, `WIR-1`; [archived narrative](docs/archive/closed-findings.md) |
| `F52` | the refresh interval is read from the chain, not from a node's own log. | Corrected at `SPN-46`, `ADR-0019`, `BtcPolicy.RefreshAge.alternation`; [archived narrative](docs/archive/closed-findings.md) |
| `F53` | the refresh fee cap changed from relative to absolute with no record. | Corrected at `SPN-47`, `ADR-0018`; [archived narrative](docs/archive/closed-findings.md) |
| `F54` | defects in `ADR-0019` and `ADR-0020`, among them a refresh bump that could not fire, an unbounded refresh fan-out, and an Escape fireable once any other Carrier armed. | Corrected at `WTC-25`, `SPN-43`, `SPN-44`, `CHN-30`, `DUR-10`, `DUR-20`, `DUR-22`; [archived narrative](docs/archive/closed-findings.md) |
| `F55` | whether the duress claw-back residual is meant to fire at all. | Corrected at `ADR-0022`, `CHN-35`, `SPN-50`; [archived narrative](docs/archive/closed-findings.md) |
| `F56` | the operator program described rules that `ADR-0018` to `ADR-0020` had replaced. | Corrected at `CHN-1`, `CHN-4`, `OPR-15`, `OPR-33`, `OPR-51`, `OPR-65`, `DUR-22`, `MAN-35`; [archived narrative](docs/archive/closed-findings.md) |
| `F57` | the claw-back's one-shot burn argument was false, since with change the burn repeats every block, and the escape-class retirement was incomplete. | Corrected at `CHN-35`, `SPN-50`, `SPN-33`, `NCH-21`, `API-24`, `SEC-54`; [archived narrative](docs/archive/closed-findings.md) |
| `F58` | `CNF-47` asked for a theorem `DUR-14` does not hold. | Corrected at `DUR-14`, `BtcPolicy.Deadline.shrink_le_max`, `BtcPolicy.Deadline.shrink_le_of_now_le`; [archived narrative](docs/archive/closed-findings.md) |
| `F59` | `DUR-22` claimed one denominator fixed across every pass; the load-bearing property is a floor, and the single-sweep guarantee is per node. | Corrected at `DUR-22`, `SEC-21`, `ADR-0020`, `BtcPolicy.Coverage`; [archived narrative](docs/archive/closed-findings.md) |
| `F61` | `POL-20`'s cohort was stated over one interval the federation does not have, and `DOM-24` gave the HotClock a different origin from its two owners. | Corrected at `POL-20`, `DOM-24`, `BtcPolicy.Ledger.bridge`; [archived narrative](docs/archive/closed-findings.md) |
| `F65` | a receipt named no sender, so a duplicate relay counted twice, and the package test read world-level availability, so a node could assemble from partials it never received; both corrected. The exposure key names no recipient, and that half is deliberate. | Corrected at `BtcPolicy.Kernel.receipt`, `BtcPolicy.Kernel.exposedQuorum`, `BtcPolicy.Kernel.packageAccepted`; [archived narrative](docs/archive/closed-findings.md) |
