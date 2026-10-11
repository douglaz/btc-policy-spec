# `SPN-41`'s removal runs on an armed node only, and the pending log keeps its entry

Status: accepted 2026-10-11. Specification-repository decision by the specification owner, taken
after a four-reader design review (reviewers A–D) that chose it unanimously.

`SPN-41` required the registry to remove every selected Escape and its pair when the armed window
closed, regardless of their own expiries, and did not say whether that ran on a node that is not
armed. `DUR-20` writes the selected windows under both PINs, so an unarmed node holds selected
entries with installed windows too, under `DUR-10`'s "An entry whose duress bit remains clear
therefore sits in the set present and never released". The formal layer modelled the exemption
and not the removal.

## Decisions

**1. The removal runs only on a node whose `active` bit is set.** `SPN-41` says "On a node whose
`active` bit (`DUR-10`) is set, the registry MUST remove every selected Escape, its entry's duress
bit set or clear, together with its pair". The bound is effective time strictly past `T +
combine_slack_secs`; at equality the window is still open. The close is read at effective time:
`DUR-7` says "No other comparison reads the ratchet". `active` is the bit `DUR-7`'s driver reads,
and `sweep_active` has the same one writer, under `DUR-10`'s "a single overlay flag set for the
whole node by a holder decision with `arm = true`".

**2. A conjunct of the keep test, never a branch.** `SPN-41` says "The removal MUST be a
constant-time conjunct of each candidate's keep test on the pass, never a branch on `active` around
it". The conjunct is false on every node until the close, which is at or after `T`, so it changes
nothing inside the concealment horizon.

**3. The registry only; the pending log is a record of its own.** `SPN-42` says "Before expiry, an
id is removed only on a public network settlement event (`SPN-33`), never by a PIN-dependent path",
with no `T` scope, so the removal leaves the spend's entry. A log read off the registry would lose
it, so the formal layer keeps the log as its own record, and its entry carries what the settlement
removal reads: `DUR-33` says "A confirmed armed Escape MUST clear from the pending log the
candidates it defeated — its paired spend and every hot candidate sharing an input". The common sweep outcome is exactly that
settlement, minutes after a prune pass has collected the pair.

Landed at `SPN-41`, `SPN-33`, `ADR-0023` decision 12, `CNF-35` and `CNF-140`. Formal:
`BtcPolicy.Kernel.prune`, `BtcPolicy.Kernel.pending`, `BtcPolicy.Kernel.logRegistration`,
`BtcPolicy.Kernel.PendingEntry.clearedBy`, `BtcPolicy.Kernel.prune_keeps_pending` and
`BtcPolicy.Silence.removal_false_preHorizon`; `Silence.silence` and `Silence.silence_initial` keep
their hypothesis lists. Exhibits:
`BtcPolicy.Exhibits.TwoRun.unarmed_spend_fires_past_close`,
`BtcPolicy.Exhibits.TwoRun.armed_removal_keeps_pending` and
`BtcPolicy.Exhibits.TwoRun.settlement_clears_removed_pending`.

## Considered options

**The removal on every node.** This is a liveness question, not a SILENCE one. An ordinary spend's
own holder decision writes `T` near `first_seen + duress_delay_secs`, so its pair's window closes
before its `fire_at` whenever `duress_delay_secs + combine_slack_secs < hold_secs`. That holds for
any Hold over a minute with the defaults. A prune pass in between removes the pair, and the spend
never fires. Three reviewers built that trace;
`BtcPolicy.Exhibits.TwoRun.unarmed_spend_fires_past_close` is the spend surviving it, and the
workflow plants this option and asserts that exhibit red.

**Keying on the entry's own duress bit.** An armed node can hold a selected entry whose bit is
clear: a pair committed under an ordinary PIN, before or after the arm. Keyed on that bit, the
removal would leave such a pair, whose Escape is never released, to linger on an armed node until
its expiry, for nothing.

**A branch on `active` around the pass.** A branch would make the pass visit candidates on one run
only before `T`, against `DUR-1`'s "lock counts, allocation counts, candidate visits and store-lock
hold time".

**Keeping `/pending` a projection of the registry.** The removal would then take the spend's
entry with its candidate, before its expiry and by a PIN-dependent path, which `SPN-42` forbids.
It is the withdrawn value of the guard parameter `Rules.pendingSource`.
`BtcPolicy.Kernel.PendingCases.removal_drops_pending_with_projection` and
`BtcPolicy.Kernel.PendingCases.removal_keeps_pending_with_record` hold the trace under each value,
`BtcPolicy.Exhibits.TwoRun.removal_drops_pending_with_withdrawn` runs it on the armed exhibits'
trace, and the workflow flips
to it and asserts `BtcPolicy.Exhibits.TwoRun.armed_removal_keeps_pending` and
`BtcPolicy.Exhibits.TwoRun.settlement_clears_removed_pending` red.

## Consequences

A selected pair whose window has closed is collected only on an armed node, past its `T`, where
`DUR-7` decides Lockdown. On every other node it stays until its own expiry. The pending log
lists a spend until its expiry or a settlement of it, its sibling or an input-conflicting
transaction, whether or not the registry still holds the candidate.
