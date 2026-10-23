# The compromise-and-loss matrix, and what the set does not defend

Status: accepted 2026-09-14; escape custody amended 2026-10-05 and 2026-10-06. Specification-repository
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

**2. Escape custody follows the supplied descriptor (row 10).** The single-key assumption of
the original decision and the universal threshold assumption of the 2026-10-05 amendment are
superseded by the descriptor-choice decision below. `OPS-60` states: "The escape keys and their
backups MUST be held so that a coercer holding the user cannot reach any such spending key set
within the sweep's window."
`OPS-33`: "the user together with any escape spending key set" and "Reach includes usable backups
of those keys". The ceremony checks public evidence, while the custody plan states where
devices and backups live. The set cannot see a house.

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
now names "lost `E`, nobody else retains `E`, and a sweep fires". Loss of a
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

## Decision 2026-10-06: the descriptor is the Operator's choice

The Operator settled the ambiguity between the admitted grammar and the threshold-only custody
wording. `MAN-26` owns admission: "Subject to these bundle preconditions and all other ceremony
validation requirements, including `MAN-27`, `POL-8` and all of `MAN-28`, the ceremony MUST
accept any escape descriptor in the public grammar". Its boundary is
"it MUST NOT require a single numeric threshold, classify the spending policy, or add a
policy-eligibility test". Narrowing the grammar to threshold wallets was rejected; supplying
the wallet's spending policy remains the Operator's choice.

`SEC-54` owns the interpretation for every matrix row and its combination rule: "`E` means
spending authority under the supplied escape descriptor". It scopes the arithmetic: "The
numeric threshold formulas apply only to a `k`-of-`m` escape wallet" and "For other descriptor
policies, the set makes no threshold-based coercion, custody or loss claim." In particular,
"if the attacker retains `E`, a sweep is Theft even when the Operator has lost `E`".

`OPS-60` owns the custody duty: "The Operator MUST identify the key sets that can spend under
the supplied descriptor" and "The ceremony does not calculate these sets." `CNF-78` covers
admission and `CNF-131` covers restoration and custody evidence. Specification gates do not
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
`OPS-30` once said "the Operator SHOULD enroll successor PINs such that neither new PIN verifies
against either predecessor digest", including role swaps. `OPS-30` once said "This recommendation
does not apply to routine rotations". That recommendation was deliberately advisory; the decision of
2026-10-21 on new PINs below makes it a duty for every rotation. `OPS-30` says "the rotation does
not require the old PINs".

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

## Decision 2026-10-21: PIN-digest copies

Accepted: `OPS-35` requires every copy of either PIN digest off the node hosts to be destroyed
before funding, and `SEC-10` owns the "digest premise", that the adversary holds no copy of either
PIN digest. The scope references are `OVR-13`, `DOM-2` and `DUR-1`; the `SEC-54` preamble records
that silence is not claimed against a holder of a copy. A copy is an offline test: its holder can
test whether a PIN it holds is the one enrolled in that digest's role, and whoever holds the
coordinator at the wrench sees every PIN the user enters. This decision narrows the current
application of `ADR-0012`'s unnumbered "Silence model A" threat-model bullet: silence is not claimed
against a holder of a copy of either PIN digest, even one "who has compromised **no node**".
`ADR-0012` remains unchanged as the historical design record.

Rejected: narrowing the claim in text alone, which leaves the copies on the coordinator, where
whoever holds it at the wrench can test every PIN the user enters; and moving the copies to storage
the Operator controls, which can be within reach of a coercer who holds the user.

## Decision 2026-10-21: a copied node key and records of the PINs

Accepted: `DUR-1`'s silence claim covers a holder of a copy of fewer than `t` node keys that runs no
node, when the adversary also holds no record of either PIN from any source. `DUR-1` owns the
condition; `OVR-13` and `SEC-54` row 11 cite it, and `SEC-10` names a holder of such a record among
those who can learn the PIN class. Two PINs are enrolled, so a record of either one, from any
source, lets its holder compare it with the PIN offered at the wrench; a key copy is one source,
since a spend request carries the plaintext PIN and the transport mechanism is not chosen (`F37`).
This decision narrows the current application of `ADR-0012`'s unnumbered "Silence model A"
threat-model bullet a second time: silence is not claimed against an adversary holding a record of
the duress PIN, even one "who has compromised **no node**". A record of the normal PIN narrows
nothing there, since `ADR-0012`'s Coordinator bullet already says a coordinator compromised at the
wrench "never learns the normal pin". `ADR-0012` remains unchanged as the historical design record.

Rejected: narrowing `DUR-1` and `OVR-13` to row 11's earlier "silence not claimed" for a holder of
fewer than `t` node keys; and a condition naming the normal PIN alone, which leaves the claim
covering a holder of a duress-PIN record that can compare it the same way.

## Decision 2026-10-21: the fund outcome of row 16

Accepted: `SEC-54` row 16's coercer, who holds coordinator history carrying an encoding left by a
compromised node release "without earlier control of the coordinator or present control of a node",
reaches at worst Bounded theft, as in row 8, at the wrench, holding the user, `U` `P` `D` `C`, with
`E` out of its reach: where that history gives it the normal PIN, it substitutes that PIN. Other
holdings follow the applicable attacker and loss rows. This is a conditional-theft case that
`SEC-42`, whose histories are those of "A coordinator compromised BEFORE the wrench", does not
count. The row's silence sentence, "silence is not claimed for PINs entered while that release ran",
and the decision of 2026-10-05 are unchanged.

Rejected: a row of its own for this coercer, which would name one combination of holdings in two
rows.

## Decision 2026-10-21: new PINs

Accepted: every rotation needs new PINs. `OPS-30` says "the Operator MUST enroll successor PINs such
that neither new PIN verifies against either predecessor digest", including role swaps, and neither
enrolled in any other vault; `OPS-34` says a rollout stage's two vaults "MUST NOT share either PIN,
in either role, with each other or with any other vault". Both are Operator duties that enrollment
tooling does not check. This changes the decision of
2026-10-05 on compromised releases and predecessor data, whose recommendation was deliberately
advisory and did not apply to routine rotations. Where a PIN is also enrolled in another vault,
whoever holds that vault's coordinator auth key can test it against that vault's running nodes
without coins (`SEC-10`), and `OPR-66` says "Retirement MUST preserve the locally held artifacts and
signing access", so the coordinator keeps a predecessor's key after the sweep, and no rule stops the
predecessor's nodes. `SEC-10`'s "digest premise" now includes that neither PIN is enrolled in
another vault. This decision narrows the current application of `ADR-0012`'s unnumbered "Silence
model A" threat-model bullet a third time: silence is not claimed where either PIN is enrolled in
another vault, against any adversary, even one "who has compromised **no node**". `ADR-0012`
remains unchanged as the historical design record.

Rejected: a recommendation that lets the Operator reuse a PIN, which leaves silence unclaimed against
the coordinator itself while the other vault's nodes run; and allowing reuse once the other
vault's nodes are stopped or its coordinator auth key deleted, which conflicts with `OPR-66`'s
retention and `OPS-15`'s claw-back route.

## Decision 2026-10-23: new PINs for every vault

Accepted: no two of an Operator's vaults share a PIN, whatever made them. `OPS-73` says "An
Operator's vaults MUST NOT share either PIN, in either role, with one another, regardless of
enrollment order, rotation, rollout stage or retirement" and "Enrollment tooling does not check this
duty". This extends the decision of 2026-10-21 on new PINs, which reached a rotation's successor and
a rollout stage's vaults, to every pair of an Operator's vaults, because the test does not depend on
how either vault was made: `SEC-10` says "whoever holds that vault's coordinator auth key, a
coordinator serving both vaults included, can test the PIN against that vault's running nodes
without coins". That decision, its narrowing of `ADR-0012` included, is unchanged.

Rejected: leaving such a pair to the Operator's choice with its cost stated, which leaves silence
unclaimed against the coordinator itself while the other vault's nodes run, the reason the decision
of 2026-10-21 on new PINs gave for rejecting a recommendation that allows reuse.
