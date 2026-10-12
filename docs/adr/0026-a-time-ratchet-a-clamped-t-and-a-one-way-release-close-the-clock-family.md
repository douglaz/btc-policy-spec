# A time ratchet, a clamped `T`, a one-way release and a HotClock Hold close the clock family

Status: accepted 2026-10-09. Specification-repository decision by the specification owner, taken
after four-reader design reviews (reviewers A–D). Each decision names the requirements its edits
landed in. The clock family of the title is `F60`, `F62`, `F64` and the forward wall step that
shortened a hot spend's Hold, each set out below; this record closes all four, and `F68` stays
open.

`F60` and `F62` shared one cause: a node's clocks do not agree, and a rule that read one of them
at the wrong moment either leaked the PIN class before `T` or let an invariant the set claims go
false. `F60`: a wall clock stepped back after a holder decision put the effective sample below the
`T` that decision wrote, or back inside a hot window the node had already passed, and a fire pass
there queued a partial under the ordinary PIN that `DUR-11`'s freeze held under duress. `F62`: the
Hot ledger's liveness predicate, re-run at every admission over rows that outlive their
candidates, revived a released charge after a backward wall step and put a ledger above its cap.
`F64` had a cause of its own, on clocks that agree: a later holder decision on an armed node wrote
the computed `T`, which could grow it. A forward wall step had a cost of its own: it reached a hot spend's `fire_at` early, shortening its
Hold in real time. The decisions below repair each at the point where it entered. Each rule has
one home in the requirements; this record owns the choice among the options and why the others
lost.

## Decisions

**1. The time ratchet, and its readers.** `DUR-7` says the ratchet is "the greatest effective time this
node has read at a holder decision (`DUR-5`), a refused Carrier's included, or at a hot
acceptance, a repeat `SPN-23` accepts included, under both PINs", and says "Nothing else moves it
— not a fire pass, a prune, a tick of this driver or of the store prune driver, nor a refused
request of any kind — and it is never lowered". This decision gave the ratchet two readers, the
driver and a hot window's close. `DUR-7` says "Its readers are exactly three: this driver's
comparison, the close of a hot candidate's fire window (`SPN-38`) and the seed of a holder
decision's start (`DUR-13`)." The third came later, with the repair of `F68`'s ordinary-record
route at `DUR-13`, and reads no ingress sample.
`DUR-7` says "No other comparison reads the ratchet", and says its driver compares
"`armed ∧ max(ratchet, effective) ≥ T`". `SPN-38` says "For a hot candidate, its fire window's opening, `fire_at ≤
now`, is read at effective time and its close at `max(ratchet, effective)`, the time ratchet of
`DUR-7`; every other candidate's fire window, opening and close, is read at effective time."

The advancing events are public and identical under both PINs. An advance keyed on writes of `T`
would not be: `DUR-20` says "`DUR-14` shrinks only on an armed node and a traversal that ran only
there would be work a normal-PIN twin does not do (`DUR-1`)", and an advance on that write would be
the same asymmetry in node state. The ratchet is a reading, not a clock: `DOM-24` says "The time
ratchet records effective-time readings and is not a fourth clock".

The opening of a hot window and every other read but that later seed stay on effective time, each
for its own reason (see the options below). Landed at `DUR-7`, `SPN-38`, `SPN-39`, `DOM-24` and `CNF-152`. Formal:
`BtcPolicy.Kernel.advanceRatchet`, `BtcPolicy.Kernel.closeSample` and
`BtcPolicy.Kernel.ratchet_never_lowered`; `BtcPolicy.Silence.silence` takes no premise on the
samples. Exhibits under `BtcPolicy.Exhibits.TwoRun`:
`BtcPolicy.Exhibits.TwoRun.f60_backward_step_leaks` and
`BtcPolicy.Exhibits.TwoRun.f60_clamp_silent_with_current` (the clamp route);
`BtcPolicy.Exhibits.TwoRun.f60_expiry_route_leaks` and
`BtcPolicy.Exhibits.TwoRun.f60_expiry_route_silent_with_current` (the expiry-filter route);
`BtcPolicy.Exhibits.TwoRun.f60_send_route_leaks` and
`BtcPolicy.Exhibits.TwoRun.f60_send_route_silent_with_current` (the send);
`BtcPolicy.Exhibits.TwoRun.f60_ratcheted_close_alone_leaks` and
`BtcPolicy.Exhibits.TwoRun.f60_ratcheted_driver_alone_leaks` (each reader alone leaves a route
open); `BtcPolicy.Exhibits.TwoRun.ratchet_moves_only_at_its_events`;
`BtcPolicy.Exhibits.TwoRun.other_windows_close_on_effective_time`,
`BtcPolicy.Exhibits.TwoRun.hot_opening_on_effective_time` and
`BtcPolicy.Exhibits.TwoRun.clamp_reads_effective_below_ratchet`.

**2. `SPN-30`'s cap is in the kernel.** `SPN-30` says "Its fire window is `[fire_at, min(expiry,
fire_at + combine_slack_secs)]`", and the kernel's window reads that close
(`BtcPolicy.Kernel.windowOpen`, `BtcPolicy.Exhibits.TwoRun.hot_window_closes_at_cap`).

**3. The never-fires residual is stated, not refused.** After a forward wall excursion that
contained a holder decision or a hot acceptance and was then corrected, a hot spend can be accepted
whose close is already below the ratchet. `SPN-30` says "it is accepted, charged (`POL-16`) and
listed in `/pending` but never fires, and no refusal is added for it". Its charge leaves the
ledger by `POL-18`'s refund or `POL-19`'s release, as any charge does. The residual is denial: the
operator must request the spend again. Landed at `SPN-30`;
`BtcPolicy.Exhibits.TwoRun.never_fires_with_current` runs it and `BtcPolicy.Exhibits.TwoRun.never_fires_never_due` shows it due at no sample.

**4. `F64`'s clamp on the arm bit as it stood before the decision.** `DUR-13` says a holder
decision on a node armed before it "MUST write `T ← max(min(T, T_computed), now)`", so that "no
later holder decision extends the hostage window, and one landing after `T` writes `now`"; on a node
not armed before it, a holder decision "writes `T ← T_computed`, which may be larger than the `T`
it replaces". The selection is pin-uniform because its selector is the arm bit as it stood before
the event: `DUR-13` says "The selection between the two writes MUST be
constant-time on the arm bit as it stood before the decision", and `DUR-14` says of its own update
"The selection between the two MUST be constant-time on the arm bit as it stood before the
acceptance." Why the clamp and not a plain `min` is in the options below. `DUR-20` says every
hot acceptance and every holder decision "MUST visit every selected entry and write its window at
the `T` that event writes", and `ADR-0020` point 4 quotes the bound.
Landed at `DUR-13`, `DUR-14`, `DUR-20`, `CNF-47` and `ADR-0020` point 4. Formal:
`BtcPolicy.Kernel.writtenDeadline` and `BtcPolicy.Kernel.holderDecision_bounds_T`; exhibits
`BtcPolicy.Exhibits.TwoRun.later_commit_keeps_T`, `BtcPolicy.Exhibits.TwoRun.later_arm_keeps_T`,
`BtcPolicy.Exhibits.TwoRun.chained_commit_keeps_T`,
`BtcPolicy.Exhibits.TwoRun.first_arm_writes_computed`,
`BtcPolicy.Exhibits.TwoRun.late_decision_writes_now` and
`BtcPolicy.Exhibits.TwoRun.f64_commits_grow_T_with_withdrawn`, which runs `F64`'s growth from 250
to 445 to 635 on the armed run; and, for `DUR-14`'s bound,
`BtcPolicy.Exhibits.TwoRun.static_bound_fails_with_withdrawn`.

**5. `F62`: a one-way release at an accepted admission, and a refund on collection.** `POL-19`
says "a reservation is released when both disjuncts are false, it is released for good, and it is
never re-created, whatever a later wall sample reads". And `POL-19` says "The release is evaluated
only at `POL-16`'s admission check of a hot request — never at a tick, a fire pass or a prune
pass — and persists only with the acceptance that check admits; a refused request releases
nothing (`POL-16`)." `POL-19` says why the released charge's candidate stays shut: "So that
expiry is strictly below the ratchet", and the candidate the reservation charged "is never due
again while its expiry is unchanged"
(`BtcPolicy.Ledger.released_below_ratchet`,
`BtcPolicy.Ledger.released_never_due`). `POL-16` says
"`SPN-14`’s “A refused request MUST mutate nothing” extends to this ledger". The refund waits for
collection: `POL-18` says "a reservation is refundable exactly when it is unexposed, its signed
expiry has strictly passed on the wall sample `POL-19`'s expiry disjunct reads, and its candidate
is no longer resident". `POL-20` is unchanged, and `POL-20`'s "each ledger holds at most `cap`" now
holds by induction (`BtcPolicy.Ledger.liveSum_le_cap`); the refund reaches only collected candidates
(`BtcPolicy.Ledger.prune_refunds_only_collected`). `SPN-41`'s exemption, which can keep a spend
resident past its expiry, is modelled in `BtcPolicy.Kernel.prune` and
`BtcPolicy.Kernel.exemptEscape`. Landed at `POL-19`, `POL-16`, `SPN-29` and `POL-18`, and cited
by `POL-21`, `SPN-30`, `SPN-33`, `SPN-41`, `NCH-24`, `DUR-33`, `DEF-5`, `CNF-30`,
`CNF-38` and `CNF-68`. Exhibits under `BtcPolicy.Exhibits.HotLedger`:
`BtcPolicy.Exhibits.HotLedger.uncharged_fire_closed_with_current`,
`BtcPolicy.Exhibits.HotLedger.refused_admission_closed_with_current`,
`BtcPolicy.Exhibits.HotLedger.refund_exemption_closed_with_current`,
`BtcPolicy.Exhibits.HotLedger.release_at_admission_shuts_window` and
`BtcPolicy.Exhibits.HotLedger.frozen_charge_refunded_at_collecting_prune`; and
`BtcPolicy.Exhibits.TwoRun.silence_needs_unarmed`, which shows the SILENCE invariant needs
`NodeInv`'s `unarmed` clause: the exemption reads an Escape's window, which each run closes at its
own `T`.

**6. The HotClock Hold check, and its cost.** `SPN-38` says "A hot candidate is due only when,
also, its Hold has matured on the HotClock (`POL-22`): `now_mono − reserved_at ≥ hold_secs`,
equality passing". Its anchor is `POL-18`'s reservation time, and `POL-18` says "a retry keeps
the original reservation time"; and it only restricts: `SPN-38` says it "does not move the
window's opening". It is pin-uniform: `SPN-38` says "it reads only the hot bit and HotClock
samples, so it is read alike under both PINs". A forward wall step therefore no longer shortens a
Hold; the wall-domain `fire_at` and the HotClock age must both be reached. The cost is `NCH-41`'s, and `NCH-41` says "So
a suspend, or a forward wall step, longer than `combine_slack_secs` before the HotClock Hold
matures closes the window first, and the spend does not fire while the wall stays ahead", and "In
every case it is denial, never theft". The same forward step still brings `T` earlier through
`DUR-7`'s comparison; the check leaves that unchanged. `SPN-34` says of the rendered countdown "For
a hot spend it is a lower bound on the time until the spend can fire, not that time". Landed at
`SPN-38`, `SPN-39`, `SPN-34`, `NCH-41`, `POL-22`, `DOM-24`, `SPN-13`, `CHN-31` and `CNF-152`.
Formal: `BtcPolicy.Kernel.holdMatured`; exhibits under `BtcPolicy.Exhibits.HotClockHold`:
`BtcPolicy.Exhibits.HotClockHold.forward_step_waits_for_hold`,
`BtcPolicy.Exhibits.HotClockHold.beyond_slack_fires_with_withdrawn_only`,
`BtcPolicy.Exhibits.HotClockHold.beyond_slack_never_due`,
`BtcPolicy.Exhibits.HotClockHold.hold_counts_from_acceptance`,
`BtcPolicy.Exhibits.HotClockHold.replay_keeps_reservation_time`,
`BtcPolicy.Exhibits.HotClockHold.corrected_wall_reopens_window` and
`BtcPolicy.Exhibits.HotClockHold.armed_escape_not_gated`.

## Considered options

**Advance the shared `SPN-13` high-water on every sample.** Every freshness decision reads
effective time (`DOM-24`), so a high-water advanced by every sample would carry `F3`'s blackhole
from peer receipts to request freshness: after one forward excursion, an honest request
whose signed expiry the excursion had passed would be refused until real time caught up.

**Take as a premise that wall time never steps back.** The set already defends backward steps:
`SPN-13` says "a backward clock step can never revive a pruned nonce", and `CNF-28` and `CNF-72`
exercise it. A premise would assume away a fault the rest of the set handles, and it would not
cover the expiry-filter route either. `DUR-13`: "`earliest_hot = min{ fire_at : candidate is hot,
not broadcast, expiry ≥ now }`". So a hot candidate already expired but resident at an arming
decision does not pull `T` in, and a backward step to a sample inside its window reopens it below
`T`: a window `[80, 120]` left out of the scan by an arm at 130, which writes `T = 272`, is open to
a fire pass at 85 (`BtcPolicy.Exhibits.TwoRun.f60_expiry_route_leaks`).

**Put the Hold and `T` on the HotClock alone.** The window's close and `DUR-13`'s expiry filter
read the signed wall expiry, which no local duration can replace, so a candidate already expired
at an arming decision still drops out of the scan, and a backward wall step still reopens its
window. The HotClock check is a conjunct
beside the window (decision 6), not a replacement for it.

**Read the opening of a hot window at the ratchet.** It would make the wall-domain `fire_at`
meaningless after a correction. With the ratchet at 150, a spend accepted at 100 with `fire_at`
120 would have passed its opening before it was accepted, and wherever the HotClock check passes
it would be due at 101.
`BtcPolicy.Exhibits.TwoRun.hot_opening_on_effective_time` runs that trace on a node whose HotClock
check passes at every sample, so the opening alone decides, and shows the spend not due at 101 and
due at 120 as the rules stand.

**Read every other clock reading at the ratchet.** Ingress read at the ratchet would move
`first_seen` later, stretching `T`, and `D` earlier. An Escape close read at the ratchet kills the
sweep: with the ratchet at 400 and `T` at 260, the Escape's window `[T, T + combine_slack_secs]`,
here `[260, 300]`, is shut at the ratchet, while a wall stepped back to 265 finds it open and due
(`BtcPolicy.Exhibits.TwoRun.other_windows_close_on_effective_time`). Refresh and claw-back windows
read at the ratchet would only lose spends. So `first_seen`, `D`, `DUR-13`'s outer floor and clamp,
`DUR-14`'s update, the prune pass (`SPN-41`, `SPN-42`), `/pending` (`API-21`) and `DUR-20`'s Escape
windows stay on effective time. `DUR-13`'s start, the repair of `F68`'s ordinary-record route, is
seeded at `max(ratchet, now)`: the seed reads no ingress sample, so the stretch above does not
reach it, and `DUR-13` says the start is "the seed `max(ratchet, now)`, read at `DUR-7`'s time
ratchet, lowered to the `first_seen` of each record naming the same spend commitment whose own
duress bit is set".

**Advance the ratchet at a refused hot request, or at every hot request.** A refused request could
then carry an excursion into the ratchet and end valid hot windows without reserving any budget.
`DUR-7` says "nor a refused request of any kind".

**Refuse a never-fires spend at acceptance.** It needs a new refusal whose predicate has a `now`
operand, `max(ratchet, effective) ≤ min(expiry, fire_at + combine_slack_secs)`, which `SPN-30`'s
acceptance inequality does not have; it makes the ingress check a further reader of the ratchet,
against `DUR-7`'s "No other comparison reads the ratchet"; `F60` does not need it; and the residual
it would remove is denial only (decision 3).

**A plain `min` for `T`, `T ← min(T, T_computed)`.** A holder decision can land after `T` and
before Lockdown takes effect, since `DUR-15` says "The DELAY before Lockdown lands has no finite
bound and this set claims none". A plain `min` would then keep the past `T` and re-window every
selected Escape at a window already closed. A commit at 305 against `T = 250` writes 305 and
re-windows the Escapes at `[305, 345]` under the clamp; under `min` it would leave `[250, 290]`,
shut (`BtcPolicy.Exhibits.TwoRun.late_decision_writes_now` runs the clamp's half).

**An unconditional `min`, on unarmed nodes too.** The `T` an unarmed node holds is stale, 0 at
start or whatever ordinary traffic last wrote, so the first arm would inherit a past `T` and fire
at once. `BtcPolicy.Exhibits.TwoRun.first_arm_writes_computed` runs the first arm, committed at 610
after ordinary traffic left 260: the clamp's selector, the arm bit as it stood before the
decision, writes the computed 800, where a `min` with the stale value would write `min(260, 800)
= 260`, already past at 610.

**Cap `T` at the first arm's ceiling.** It needs extra state, and it can grow a `T` that a hot
spend pulled below the cap.

**Freeze `T` once armed, except under `DUR-14`.** When it was weighed, `F68`'s after-arm route was
a resubmission whose holder decision started at an old ordinary record; the freeze closed that
route and not the first arm. `DUR-13`'s duress-bit start now closes that route under every option,
and the freeze closes neither route `F68` still records. It also reopens the stretch `DUR-13`
exists to prevent: two duress Carriers naming different spend commitments, ingressed at 10 and 50
and committed in reverse, give 210, or 250 under the freeze (`F68` records the figures).

**Keep `POL-19`'s predicate as a membership test re-run at every admission, and weaken `POL-20`
to the live sum at each counted acceptance.** `POL-20`'s bound would stop being an induction over
the transitions; rows dead on both disjuncts would need a retention rule, since `POL-16` says "The
reservation ledger is bounded at 4 096 entries"; and the refund while the
candidate is resident would still need its own repair.

**Release at every step, keep a release at a refused admission, or refund at expiry.** Releasing
at every step and refunding at expiry are the withdrawn values of the ledger's guard parameters,
and each lets a charged candidate fire with no row after a backward step, beside a second spend of
the whole cap: `BtcPolicy.Exhibits.HotLedger.uncharged_fire_with_withdrawn` (a tick released the
charge) and `BtcPolicy.Exhibits.HotLedger.refund_exemption_with_withdrawn` (the prune pass
refunded a resident spend). A release kept at a refused admission is a mutation the workflow plants
on the current release point: it falsifies
`BtcPolicy.Ledger.retained_outside_prune_and_admission`, and
`BtcPolicy.Exhibits.HotLedger.refused_admission_closed_with_current` is the trace as the rules
stand, whose refused request, refused by the kernel or by the budget, keeps no release. Effective
time alone at the release cannot keep the revived window shut; the ratchet the admitted acceptance advances does
(`BtcPolicy.Ledger.released_never_due`).

## Consequences

`BtcPolicy.Silence.silence` holds for every trace of samples, backward steps included, with the
driver and a hot window's close at `max(ratchet, effective)`; `ADR-0023` decision 14 records what it carries instead of a
sample premise.

A backward wall step after a holder decision or a hot acceptance can neither un-reach a `T` at or
below that event's effective time while that `T` is unchanged nor reopen a hot window whose close
is below it. A forward step followed by a correction can leave a hot spend that never fires
(decision 3), and a forward step or a suspend longer than `combine_slack_secs` before the HotClock
Hold matures can deny a spend (decision 6). Both are denial, never theft, and both mean the
operator requests the spend again.

`POL-20`'s invariant is an induction over the ledger's transitions, and a released charge stays
released whatever the wall later reads.

`F68`, a coercer timing Lockdown by resubmitting an old commitment, lies outside the family
and stays open. It was found while reviewing `F64`'s directions and is reachable with the clamp in
place; its directions are its own.
