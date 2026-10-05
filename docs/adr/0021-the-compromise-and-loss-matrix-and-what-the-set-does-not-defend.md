# The compromise-and-loss matrix, and what the set does not defend

Status: accepted 2026-09-14; escape custody amended 2026-10-05. Specification-repository
decision. The decisions below record the matrix's custody and loss cases. The amendment changes
no node request or vault-input signing rule.

The original adversary list classified attackers by what they held. The missing axis was what
the Operator still held, which became decisive when considering a pin-less escape class.
`SEC-54` now names "the outcome for every combination of what the attacker holds and what the
Operator still holds". It is the owner of the outcome vocabulary and combination rule, and the
place a future path change is judged. A proposal that cannot name the cells it moves is not
ready.

## Decisions

**1. Control of the escape destination makes pin-less claw-back theft (row 6).** The accepted
attacker holds the user key, coordinator credential and escape signing authority, but no PIN.
Before the pin-less claw-back, the PIN was the additional factor on this exit. Removing that
factor is accepted because this attacker has already defeated escape custody; a duress PIN
would pay the same destination. `SEC-54` row 6 records "**Theft**: a claw-back needs no PIN".
Rows L4 and L5 are what this tradeoff buys.

**2. Escape custody must keep a signing threshold beyond a coercer's reach (row 10).** The
original decision assumed a single escape key; the accepted 2026-10-05 amendment applies the
same boundary to the supplied wallet's threshold. `OPS-60` states: "The escape keys and their
backups MUST be held so that a coercer holding the user cannot reach a signing threshold within
the sweep's window." `OPS-33`: "the user together with a signing threshold of escape
keys" and `OPS-33`: "Reach includes usable backups of those keys". Placing a reachable threshold
in the user's home or on the coordinator host fails that check. Reaching just one key of a
multisig wallet need not reach its threshold. The ceremony checks public evidence, while the
custody plan states where devices and backups live. The set cannot see a house.

**3. Recovery custody keeps its existing defence (row 14).** After Lockdown, refresh stops and
the recovery holders have sole custody of stragglers for the timelock. `SEC-54` row 14 records
"the recovery holders are the sole custody of every straggler the sweep left in the vault".
A stronger rule requiring recovery holders beyond a coercer's reach was rejected because they
must stay reachable for the availability drill. This escape-wallet amendment does not change
that decision.

**4 and 5. A forgotten PIN is a rotation trigger (rows L4, L5).** Pin-less claw-back gives a
same-day remedy needing neither PIN nor the recovery holders. The non-compromise order is
`OPS-30`'s: "verifies the successor FIRST" and "sweeps only once a valid successor exists".
The reason belongs there too: "a sweep into the escape wallet with no successor to fund is an
incident, not a rotation". A compromise signal takes that requirement's other order, preserved
in the later decision below.

**6 and 7. Destination-key loss is a custody-drill concern (rows L6, L7).** `SEC-54` row L6
now names "lost more than `m − k` escape keys, including all their usable backups". Loss of a
single key was the original single-sig case, not a rule that every multisig key loss destroys
spending authority. A sweep to an unspendable destination is Loss; nodes cannot distinguish it
from a live destination with the same script. Proof of possession at seal time was rejected:
it proves a key existed then, not that a backup survives a year later. The recovery-key
rotation trigger is unchanged: `OPS-30` names "a recovery key known lost or a recovery holder
unreachable at the drill". Rotation while the Normal path still works preserves the remaining
exit; the custody drill supplies the operational evidence.

## Decision 2026-10-05: multisig escape preferred, single-sig accepted

`DOM-11` owns the recommendation: "The escape wallet SHOULD be multisig; single-sig is
accepted." Its per-key rule is "Each escape key MUST be generated independently on a device
that holds no other vault role." The independence rationale stays
in `ADR-0003`; multisig does not turn fingerprint comparison into proof of separate seeds or
devices. `MAN-28` states: "The evidence MUST NOT claim seed independence or physical device
separation".

The accepted construction boundary is `MAN-26`: "The Operator MAY construct this bundle using
their own multisig tooling" and "The ceremony adds no multisig construction command". Its
bundle inventory requires "exactly one entry for every distinct key expression in the descriptor",
with fixtures in `WIR-13`. The all-key precondition is also `MAN-26`'s: "Every descriptor key MUST be a ranged
extended public key with origin." This narrows ceremony inputs without replacing `MAN-39`'s
grammar. The per-cosigner checks and their evidence have one home, `MAN-28`; the implementation
acceptance cases live in `CNF-78` and `CNF-79`.

Threshold notation is owned by `SEC-54`: "`E` means access to at least `k` of its `m` keys",
and "Single-sig is the accepted `k = m = 1` case". The interpretation applies to all rows using
`E`, including theft rows 5, 6 and 10, the retained destination in row L7, and the loss exception
in the combination rule. No additional escape spending policy is chosen here. `OPS-60` owns
threshold custody; `CNF-131` requires its implementation evidence. Specification gates do not
establish that any implementation has performed those checks or drills.

## Consequences and alternatives rejected

The original decision cleared the pin-less escape class for design; `ADR-0022` records that
subsequent change. The multisig amendment changes destination custody, not the request shape.
`CHN-35` still requires "paying EVERY output to the escape descriptor". Receiving there needs
no escape-cosigner signature on vault inputs; those inputs retain the vault's own spending
policy. The witness-size rule remains `CHN-34`'s: "`B` is the byte length of the transaction's
**legacy** serialization"; actual destination script bytes are already included.

Extending only the adversary list was rejected: the loss cases need the second axis. A full
cross product of secrets was rejected as unreadable; the matrix names the cases that differ
and owns the combination rule. Turning escape custody into a ceremony check was rejected:
`MAN-28`'s "device separation is unverifiable" applies even to a passed public-key comparison.
A green check cannot establish geography. Requiring multisig or adding multisig construction
and signing tooling is outside the accepted amendment.

## Decision 2026-10-05: compromised releases and predecessor data

Accepted: `SEC-10` owns the "release-history premise", that "no node has run a compromised
release while the current PINs were in use". The scope references are `OVR-13`, `DOM-2` and
`DUR-1`; `SEC-54` records the additional case as "silence is not claimed for PINs entered while
that release ran". A later coercer can read an encoding left on an otherwise honest
coordinator without controlling a node at coercion, compromising the coordinator earlier, or
communicating with the party that introduced the compromised release. This boundary concerns
the lifetime of the current PINs, not just the software running at coercion.

Rejected: close this channel by restricting which node-chosen values the operator program
persists. `OPR-8` says "only the closed refusal code is retained", but that closed code is still
node-chosen, as are the selection of events reported and their timing. Constraining field
contents therefore cannot close the channel. This is the rejection argument's home; it does
not change what an honest node emits. Reproducible builds and release signatures do not prove
that the reproduced and signed source lacks a backdoor.

The operational response is `OPS-30`: "Disclosure of a compromised node release is a
**compromise signal**", and that rotation "sweeps FIRST and builds the successor after".
Its successor recommendation is deliberately advisory: "the Operator SHOULD enroll successor
PINs such that neither new PIN verifies against either predecessor digest", including role
swaps, and "Enrollment tooling does not check this recommendation". The limits are also
`OPS-30`'s: "the rotation does not require the old PINs" and "This recommendation does not
apply to routine rotations".

`OPR-66` owns retirement "once the program's own chain view shows every predecessor coin named
by the sweep as spent": "MUST delete everything the program persisted from the predecessor's
nodes" and "MUST stop polling the predecessor's nodes". Its boundary is "not backups or
notifications already delivered", and "Retirement MUST preserve the locally held artifacts
and signing access" for the later-coin claw-back path. This reduces retained node-supplied
history; it does not restore SILENCE for exposed PINs. The runtime acceptance items are
`CNF-122` and `CNF-130`; their presence is no claim of runtime conformance.

The existing formal relations describe honest transitions. The admission criteria are `ADR-0025`'s:
"It ranges over executions" and "It is about this set's own rules". Absence of malicious
software is an external premise, not a new theorem about those transitions. The scope
documentation is amended without changing the relations or their honest-run properties. `F66`'s unchanged narrative is [archived](../archive/closed-findings.md);
its formerly unchosen alternatives are resolved by this decision.
