# Coercion procedure: human-review preparation

This packet prepares [F18 and F21](../../16-open-findings.md), without closing
either. F21 says “the coercion procedure needs a human security reviewer and
a stranger's dry run”. These are distinct future activities: expert review
assesses security and premises; someone who did not write the procedure tests
executability without its author's context. Nothing is sent, nobody is
contacted or recruited, no drill runs, and no stage or cap changes.

## Threat model and fictional timeline

Assume a coordinator turning hostile at the wrench and an attacker controlling
the physical scene but no node. Preserve [SEC-10](../../12-security-requirements.md)'s
release-history premise, “no node has run a compromised release while the current
PINs were in use”, and digest premise, “the adversary holds no copy of either
PIN digest and that neither PIN is enrolled in another vault, in either role”.
Prior PIN records or earlier coordinator compromise invalidate this knowledge
boundary. Attacker observables include response bytes and timing, events,
health, pending state, peer effects, visible human actions and eventual chain
activity. The [logical pre-horizon receipt-step comparison](silence-observation-inventory.md#:~:text=The%20common%20labelled)
stops on the first inadmissible step, rejected request shape, or acting node
outside `Silence.preHorizon` in either run. An armed node is inside only while
the listed ratchet driver sample is strictly below its current `T`; unarmed
states are inside. The stop remains sticky after backward samples. This proves
neither equality of the human's observable actions nor safety through captivity
or after the stop.

The following timeline is explicitly fictional, with no elapsed-time guarantee.
At scene A, coercion occurs; [OPS-11](../../13-operations-and-rollout.md) says
“Cut power to the coordinator host first”. That stops new requests, not already
delivered ones. At scene B the Operator may still be captive; OPS-12 says
“Nothing below is safe to run while the Operator may still be captive”. No
successor setup, Recovery operation or further command is proposed in captivity.

At scene C, only once safe, OPS-13 says “read `/healthz` on every node”.
Distinguish unreachable nodes from affirmative reports. OPS-14 requires
“Stand up a fresh coordinator from the descriptor backup and the auth secret
on a clean host first” and “Do not send anything through the possibly hostile
relay”. Apply that boundary to further requests, including migration.

If reachable nodes report Lockdown, OPS-13 says “the sweep either moved the
coins to the escape wallet or left them frozen”. If any does not, its warning
is “a coerced hot spend can still finalize once it is due”; the claw-back
depends on a quorum still able to sign. OPS-15 calls it “a pin-less
ClawbackRequest” and requires “`t` nodes that are not locked down”. Failed or
lost quorum therefore prevents assuming a fresh claw-back succeeds. No
invented recovery command fills that gap.

## Future signet dry run and judgment

Propose a deliberately partial-sweep signet scenario, after expert safety
review, recording where a stranger gets stuck. Track swept outputs separately
from stragglers and failed submissions. OPS-16 says “do not serialise the
successor behind straggler maturity”. Check usable escape-wallet authority and
backups before treating swept funds as accessible. For remaining coins,
[OPS-26](../../13-operations-and-rollout.md) specifies “2 of the 3 recovery
keys after each coin's relative timelock matures”; its exclusivity is only for
coins “no already-signed payment, in-flight Escape or claw-back, user-signed
refresh, or other permitted Normal-path spend can still move”. [SEC-41](../../12-security-requirements.md)
adds “it is not private”. OPS-17 warns “A mis-entered duress PIN is a real
duress event and finishes the vault”.

Future human questions are whether the safe-state gate is understandable,
unreachable nodes and lost quorum are handled without false certainty, and
partial sweep, escape custody and per-coin Recovery checks are executable.
These questions adopt no policy. OPS-18 says the procedure “has not been read
by a human security reviewer and MUST be, before it is relied on”.

## Stage-9 evidence still needed

[ADR-0017](../adr/0017-one-external-review-at-stage-9.md) orders “FREEZE, then
REVIEW, then CAPS LIFT”. Prepare the frozen artifact identity, matching runbook,
operator program and configuration, and round-by-round defect history with
introduced defects and their dispositions. OPS-68 requires that history “as
the brief”, the partial-sweep dry-run report, end-to-end silence review and
correlated-reviewer blind spots; hardware-signer boundaries also need evidence.
Its findings “MUST be remediated and re-tested before stage 10”. OPS-69 requires
“every step names a real operator command” and agreement with
[ADR-0016](../adr/0016-the-escape-fee-ladder-is-sealed-and-opt-in.md) “as checked
at review time”. Those checks, sign-off and frozen-artifact evidence remain
future work; this preparation supplies none of them.
