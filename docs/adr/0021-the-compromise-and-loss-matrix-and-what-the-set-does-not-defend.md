# The compromise-and-loss matrix, and what the set does not defend

Status: accepted 2026-09-14. Specification-repository decision; the Operator decided every cell
in one session, and the reference implementation is unaffected because no cell changes a node
rule. Records `SEC-54` and the seven decisions inside it.

`SEC-2` named nine adversaries by what they hold. It answered "what can this attacker do" and
never "what can the Operator still do when they have also lost something", and it had no cell
for the case that started this: a proposal to make the escape class pin-less, like refresh. The
right question for that proposal is not "is it safer" but "which cell does it move", and there
was no table to point at. `SEC-54` is that table: every combination of what the attacker holds
and what the Operator still holds, with one of five outcome words per cell — Nothing, Bounded,
Denial, Theft, Loss — and the requirement that enforces it.

Sixteen cells were already settled by the set as written. Seven were not, and are decided here.

## Decisions

**1. An attacker with the user key, the coordinator credential and the escape-wallet key, but no
PIN, is accepted as Theft once the escape class is pin-less (row 6).** Today every coin that
leaves the vault for anywhere but the vault itself needs a PIN, and the PIN is the one factor
that lives only in a human's head behind `MAN-23`'s attempt budget. A pin-less escape class
removes that factor from this one path. Accepted because this attacker has already defeated the
custody rule for the escape-wallet key (decision 2), and no PIN defends against them anyway: the
duress PIN pays the same wallet. What the removal buys is decisions 4 and 5.

**2. The escape-wallet key MUST be held out of a coercer's reach, and the set requires it without
verifying it (row 10).** Every duress protection ends at the escape wallet. `ADR-0003` made the
key independent of every other role and `OPS-60` made its backup a custody-plan item, but no
sentence said the obvious thing: against a coercer who reaches that key, duress buys nothing.
`OPS-60` now requires the key and its backup to be held where a coercer holding the user cannot
reach them within the sweep's window, and a plan that puts either in the user's home or on the
coordinator host fails `OPS-33`'s failure-domain check. The ceremony's part is unchanged — it
births the key on its own device (`MAN-24`, `MAN-26`) and checks its independence (`MAN-28`).
Where the device lives afterwards is the custody plan's to state and the set's to require, not
to verify. The set cannot see a house.

**3. Two recovery keys in an attacker's hands stay defended by refresh cadence, the
failure-domain rule and the alert, with no stronger custody rule (row 14).** The row now states
the consequence that was implicit: after Lockdown the Normal path is dead, refresh stops, and
the recovery holders are the sole custody of every straggler the sweep left behind for the whole
timelock. A custody plan is judged against that sentence. A stronger rule — holders beyond a
coercer's reach, as for the escape key — was rejected because the holders must stay reachable
for the availability drill, and a rule the drill contradicts is a rule nobody follows.

**4 and 5. A forgotten PIN is a rotation trigger, and its remedy is a rotation whose sweep is a
claw-back (rows L4, L5).** The PIN digests are sealed; there is no reset. The order is
`OPS-30`'s for a non-compromise trigger — successor first, then the sweep into it — because a
forgotten PIN is not an emergency and a sweep into a single-key wallet with no successor is an
incident. With the escape class pin-less (`ADR-0022`), both cases have one same-day remedy that
needs neither PIN nor the recovery holders. That is the strongest reason for the pin-less
class, stronger than anything in row 6.

**6 and 7. A lost escape key or a lost recovery key is defended by the custody drill alone, and
one lost recovery key is a rotation trigger (rows L6, L7).** A sweep into a lost escape wallet is
Loss, and no node can refuse it: a live wallet and a dead one are the same script. A proof of
possession at seal time was considered and rejected; it proves the key existed at the ceremony
and nothing about a backup a year later. `OPS-30` now lists a lost recovery key, or a holder
unreachable at the drill, as a successor-first rotation trigger, since two of three is the bare
quorum `OPS-5` describes for two dead nodes, and the rotation happens while the Normal path
still works.

## Consequences

The pin-less escape class is cleared to be designed. Its ADR will cite row 6 as the cell it
moves and rows L4 and L5 as the cells it repairs, and will retire the two-leg escape-class shape
(`CHN-33`), the residual, `F44` and `F55`.

`SEC-54` is the place a future path change is judged. A proposal that cannot name the cells it
moves is not ready.

Two new glossary entries: the five outcome words, and the custody drill as distinct from the
recovery drill.

## Alternatives rejected

**Extend `SEC-2` with more adversary rows** instead of a matrix. Rejected: `SEC-2` has one axis,
and every cell decided here needed the second one — what the Operator still holds. Row 6's
attacker is `A7` plus the escape key; L4 is no attacker at all.

**A full cross product of the seven secrets on both axes.** Rejected as unreadable: 2^14 cells,
of which fewer than thirty differ. The matrix names the rows that differ and states the
combination rule — the worse of the attacker row and the loss row — for the rest.

**Make the escape-wallet custody rule a ceremony check.** Rejected: the ceremony can prove
independence of keys and nothing about geography. A check that passes on a key generated in the
user's living room would be a false assurance with a green tick.
