# Only duress-bit records start `T`, and only hot spends still in play cap it

Status: accepted 2026-10-12. Specification-repository decision by the specification owner, taken
after a four-reader design review (reviewers A–D) over four rounds. Each decision names the
requirements its edits landed in. It closes `F68`, which `ADR-0026` left open. Decision 5 was taken
the same day, after a second four-reader design review (reviewers A–D) of a defect that review of
bead `bps-pxp.2`'s commits, which landed decisions 2–4, found before they were published; no
finding was opened for it.

`F68`: a coercer holding the coordinator could choose when Lockdown became due, and so learn the
PIN class at the scene. That is the adversary of `DUR-1`'s "Silence is claimed against an adversary
holding the coordinator and the physical scene but no node". The route was an old spend commitment
presented again, and `SPN-23` says "a duress resubmission of a previously normal-accepted
commitment under a fresh nonce still records a duress intent before the cached verdict is
returned". `CHN-32` says "A SpendRequest whose spend is any class other than hot MUST be refused",
so every old commitment is a hot spend, and one problem had three routes: an old ordinary record
starting the countdown, a replay of an old hot spend after the arm, and an old hot spend whose
window shut unfired capping the first arm. Bead `bps-pxp.1` fixed the first and bead `bps-pxp.2`
the other two. This record holds the decisions of both.

## Decisions

**1. Only duress-bit records start the countdown, seeded at `max(ratchet, now)`.** `DUR-13` says
the start is "the seed `max(ratchet, now)`, read at `DUR-7`'s time ratchet, lowered to the
`first_seen` of each record naming the same spend commitment whose own duress bit is set". Every
record is read under both PINs, and a record's own bit masks only its contribution. `DUR-13` says
"An unbound intent reads only its own record", so a wrong-PIN Carrier staged before any spend
commitment is computed starts at the seed. An old ordinary record therefore no longer lowers the
start. On a node armed before it an ordinary decision still writes `DUR-13`'s clamp, and `DUR-13`
says "one landing after `T` writes `now`"; `CNF-47` says a fresh-nonce resubmission of an old
ordinary commitment, accepted and refused, and an unbound wrong-PIN intent decided more than
`duress_delay_secs` after its ingress each leave `T` unchanged "when its decision lands inside the
concealment horizon, with no hot spend in `DUR-13`'s hot domain whose `fire_at − epsilon_secs` lies
below `T`, and no record naming its spend commitment whose own duress bit is set has a `first_seen`
earlier than `T − duress_delay_secs`". `DUR-13`'s outer floor and its clamp
(`ADR-0026` decision 4) stay on effective time: a floor at the ratchet would write no earlier
deadline and would move a selected Escape's window later (`ADR-0026`'s Escape-close example). Landed at `DUR-13`, `DUR-7`, `SPN-41`, `DOM-24`, `CNF-47`, `CNF-152`,
`CONTEXT.md`, `ADR-0023`, `ADR-0026` and `ADR-0027`. Formal: `BtcPolicy.Kernel.decisionStart`,
`BtcPolicy.Kernel.seedSample`, `BtcPolicy.Kernel.decisionStart_le`, the guard parameters
`BtcPolicy.Kernel.IngressTime` and `BtcPolicy.Kernel.Rules.startSeed`; exhibits
`BtcPolicy.Exhibits.Inheritance.duress_only_ingress`,
`BtcPolicy.Exhibits.TwoRun.f68_resubmission_keeps_T`,
`BtcPolicy.Exhibits.TwoRun.late_ordinary_decision_keeps_T`,
`BtcPolicy.Exhibits.Inheritance.backward_step_keeps_duress_start` and
`BtcPolicy.Exhibits.Inheritance.backward_step_keeps_armed_T`.

**2. Only hot spends still in play cap `T`.** `DUR-13`'s `earliest_hot` ranges over its hot
domain, `DUR-13`'s "candidate is hot, not broadcast, fire window not closed at max(ratchet, now)".
Whether a window has closed is `SPN-38`'s close, so the domain reads the ratchet through the
comparison `DUR-7` already lists, and "not closed" includes a candidate before its `fire_at`.
`DUR-14` applies its update to the candidate an acceptance leaves registered: `DUR-14` says "a
repeat reads the resident's `fire_at` and whether the resident is in the domain, never the
request's", because `SPN-32` says "an already resident compatible pair is left exactly as is". A
candidate outside the domain leaves `T` as it is, and `DUR-20`'s traversal still runs on every hot
acceptance. So a replay after the arm of an old hot spend this node has broadcast holds `T`
(`BtcPolicy.Exhibits.TwoRun.replay_keeps_T_through_resident`): the duress pair, requested at 490
with `fire_at` 800 and committed at 500, arms at `max(min(490 + 200, 800 − 5), 500) = 690`, and the
replay at 505 leaves 690, where the request's own `fire_at` of 480 would write `max(min(690, 480 −
5), 505) = 505`, `now`. And a first arm with a hot spend whose window shut unfired writes `start +
duress_delay_secs` on the exhibit's trace
(`BtcPolicy.Exhibits.TwoRun.shut_unfired_spend_keeps_first_arm`): `sU` has
`fire_at` 100, its window `[100, 140]` closed at the arm, and an expiry of 900; the duress pair,
requested at 500 with `fire_at` 800 and committed at 510, writes `max(min(500 + 200, 800 − 5), 510)
= 700`, where the withdrawn scan, which reads `sU`'s expiry, writes `max(min(500 + 200, 100 − 5),
510) = 510`, `now`. Landed at `DUR-13`, `DUR-14`, `DUR-7`, `SPN-23`, `SPN-30`, `SPN-32`, `CNF-47`,
`CNF-152`, `CONTEXT.md`, `executive-summary.md`, `ADR-0012`, `ADR-0017` and `ADR-0026`. Formal:
two guard parameters, one per choice: `BtcPolicy.Kernel.HotDomain`, which candidates are in the
domain, whose withdrawn value is the earlier scan, every hot unbroadcast candidate whose expiry has
not passed; and `BtcPolicy.Kernel.AcceptRead`, which candidate the acceptance update reads, whose
withdrawn value is the request's own `fire_at` with no domain test. `BtcPolicy.Kernel.inHotDomain`,
`BtcPolicy.Kernel.earliestHotFire`, `BtcPolicy.Kernel.shrinkTarget`,
`BtcPolicy.Kernel.shrunkDeadline`, `BtcPolicy.Kernel.HotDomainCases.shut_window_under_each_domain`
and `BtcPolicy.Kernel.HotDomainCases.replay_under_each_read`. `BtcPolicy.Silence.silence` and
`BtcPolicy.Silence.silence_initial` prove under every value of both fields, the two mixed
combinations included, with no premise on either field.
Exhibits: `BtcPolicy.Exhibits.TwoRun.backward_step_keeps_window_shut`,
`BtcPolicy.Exhibits.TwoRun.arm_past_close_not_capped`,
`BtcPolicy.Exhibits.TwoRun.arm_at_close_is_capped`,
`BtcPolicy.Exhibits.TwoRun.arm_before_fire_at_is_capped`,
`BtcPolicy.Exhibits.TwoRun.live_replay_caps_T` and
`BtcPolicy.Exhibits.TwoRun.settled_spend_in_window_caps_arm`.

**3. `SEC-37` stays an accepted residual, restated, with a floor beside it.** A hot spend settled
(`SPN-33`) or made terminal by a claw-back while its window is still open stays in the domain:
`DUR-13` says "A settled or terminal hot candidate whose window has not closed stays in it". It
caps `T` at the value it had while live, and a coercer who can time it settled can time it live,
so leaving it out would close no route a coercer has.
`SEC-37` says "A hot spend accepted before the first duress-PIN ingress, not broadcast, whose fire
window has not closed at the arm caps `T` at its `fire_at − epsilon_secs`, or at `now` when `now`
is later, whether or not it can still fire", and gives the floor this decision buys: "once armed,
`T` stays at or above `F + min(duress_delay_secs, hold_secs − epsilon_secs)`". Landed at `SEC-37`
and `MAN-29`. Exhibits: `BtcPolicy.Exhibits.TwoRun.floor_holds_on_ordinary_routes`, both arms of the
`min`, and `BtcPolicy.Exhibits.TwoRun.settled_spend_in_window_caps_arm`.

**4. `F68` is withdrawn.** Its identifier moves to the withdrawn list of `16-open-findings.md` and
its narrative to `docs/archive/closed-findings.md`.

**5. A selected entry acts only on the candidate registered in the Escape role.** `CHN-24` says a
commitment is "the exact-transaction binding a node evaluates, signs, records and keys its replay
log by", and no role is among the fields it binds, so a transaction has one id whether it is
presented as a spend or as an Escape. A request refused after `SPN-23` computes its commitments
and before gate 25 verifies its Escape can name a resident hot spend's exact transaction as its
Escape. In `SPN-5`'s table three refusals do so and stage: gate 21's failed prevout fetch, gate
22's `HOT_BUDGET_EXCEEDED` and gate 24's `HOT_VELOCITY_EXCEEDED`. `DUR-10` says "A refused intent
with computed ids MUST perform the same insertion", so the hot spend's id entered
`selected_escapes`, and every use of an entry applied to any candidate carrying its id. Gate 29 is
not such a route: gate 25 precedes it, and `SPN-27` says the Escape's verification runs "with
every refusal's check prefixed `escape:`, then require escape-class". Reviewers A, B and D reproduced the two harms on the kernel.

The floor fell. After the arm at 510 with `T = 700` on
`BtcPolicy.Exhibits.TwoRun.floorTrace`'s first eleven steps, a gate-24 refusal at 520 named `fU`,
an old hot spend released and never broadcast whose window `[310, 350]` had closed. Its holder
decision at 525 rewrote `fU`'s window to `[700, 740]`, which put `fU` back in the hot domain, and
two later unbound decisions walked `T` down to 695 and then 690, below `SEC-37`'s floor of 700.
That falsified `DUR-13`'s "A hot candidate whose window shut unfired, or that this node has
broadcast, caps no `T`".

A payment stopped. Under the normal PIN a gate-24 refusal at 520 named `fD`, the hot spend of the
pair requested at 500 with `fire_at` 800. Its holder decision at 525 moved `fD`'s window to `[725,
765]` and gated `fD`'s release on the entry's clear bit, so `fD` was not released at 800. That is
against `DUR-16`'s "there MUST be no cancel operation for a pending spend".

The decision: insertion is unchanged, and `DUR-10` says "Every use of an entry acts only on the
candidate registered in the Escape role with that entry's id". `DUR-20`'s window write, `DUR-10`'s
release gate and the hot domain of `DUR-13` and `DUR-14` apply an entry to that candidate alone. A
spend's `fire_at` is always `SPN-30`'s. The test reads the role registration records (`SPN-32`,
`SPN-36`), which is the same under both PINs. Landed at `DUR-10`, `DUR-20`, `DUR-13`, `SEC-37`,
`CNF-44` and `ADR-0023`. Formal: the guard parameter `BtcPolicy.Kernel.EntryTarget` and its role test
`BtcPolicy.Kernel.entryActs`, which `BtcPolicy.Kernel.withWindow` and
`BtcPolicy.Kernel.releaseAuthorized` read. Only the withdrawn value gives
`BtcPolicy.Kernel.inHotDomain` its selected disjunct and `BtcPolicy.Kernel.unarmedDeadline` its
selected fire time. The owning-module trace is
`BtcPolicy.Kernel.EntryTargetCases.crossed_refusal_under_each_target`. The projection
`BtcPolicy.Silence.pubCand` takes the rule, and `BtcPolicy.Silence.NodeInv` gains the clause that
no candidate in the Escape role is hot. `BtcPolicy.Silence.silence` and
`BtcPolicy.Silence.silence_initial` prove under both values, with the rule threaded into the
coupling and the invariant and no premise on the field. Exhibits:
`BtcPolicy.Exhibits.TwoRun.floor_holds_on_crossed_refusal`,
`BtcPolicy.Exhibits.TwoRun.crossed_refusal_spend_releases_at_fire` and
`BtcPolicy.Exhibits.TwoRun.reused_id_spend_keeps_floor_and_releases`. The last one's route, a
pruned selected Escape's id registered again as a hot spend, is the kernel's alone, whose ids are
abstract: `CHN-24` says "Two distinct transactions MUST never share a commitment".

## Considered options

**Seed the start at `now`.** After a backward wall step it writes a `T` already due. A duress
pair accepted at wall 1000, which moves the ratchet there, and decided at 100 writes `100 + 200 =
300`, due at once under `DUR-7`'s driver, where the seed at the ratchet writes `1000 + 200 = 1200`
(`BtcPolicy.Kernel.SeedCases.effective_seed_due_at_once`).

**Fall back to `max(now, latest first_seen naming the pair)`.** It fails the next ordinary decision
on another pair after that step: armed at 1001 with `T = 1200`, an ordinary pair accepted at 100
and decided at 110 starts at 110, and the clamp writes `max(min(1200, 110 + 200), 110) = 310`,
due at once (`BtcPolicy.Kernel.SeedCases.pair_latest_fallback_due_at_once`).

**Keep the earliest record of either PIN, as decided on 2026-10-02.** Bead `bps-8s0.26` recorded
the objection to a duress-only start: "Taking the earliest of the duress intents only would make
`T` depend on the PIN". Its real content is `BtcPolicy.Silence.NodeInv`'s `unarmed` clause, an
armed run's `T` at or below a pin-uniform bound, and the masked start keeps it: the start read with
the bits is at or before the start read with every bit clear
(`BtcPolicy.Kernel.decisionStart_le`), which is the seed (`BtcPolicy.Kernel.decisionStart_clear`). The written `T` already
differed between the runs since `F64`, whose clamp writes the computed value on an unarmed node
and its minimum with `T` on an armed one.

**Release pre-duress hot spends on an armed node.** `DUR-8` says "a hot partial is released only
when the node is NOT armed", which `BtcPolicy.Kernel.Inv` and
`BtcPolicy.Kernel.hot_release_provenance` carry. Releasing them would also release a spend coerced
earlier under the real PIN, and would take inputs from under the sweep.

**Postpone every waiting hot spend at each holder decision, under both PINs.** It buys a floor of
the full delay, but no payment would then fire within `duress_delay_secs + epsilon_secs` of any
commit, a wrong-PIN Carrier would become a veto any PIN-less caller can cast, and a backward step
would still leave a gap.

**Retain `T` on a repeat acceptance alone.** It is a subset of decision 2 and misses the first arm,
which reads no repeat.

**Freeze `T` once armed, except under `DUR-14`.** It misses the first arm, and it reopens the
stretch `DUR-13` exists to prevent: `DUR-13` says each `first_seen` is the ingress time "so that
slow or selective delivery cannot stretch the hostage window". Two duress Carriers naming different spend commitments, ingressed at 10 and 50 with
`duress_delay_secs` 200 and committed in reverse: the first decision writes `50 + 200 = 250`, and
the second lowers it to `10 + 200 = 210`, which the freeze forbids.

**Accept `F68`, and state the collapse beside `SEC-37`.** The coercer could then make Lockdown due
at once through any old hot spend, one this node broadcast long ago or one whose window shut long
ago, where `SEC-37` bounds the residual to a hot spend accepted before the first duress-PIN ingress
whose window has not closed at the arm.

**Leave settled and terminal hot spends out of the domain.** Decision 3 gives why it lost.

**G: insert only an id that a resident candidate in the Escape role carries.** This was reviewer A's
proposal, and decision 5 rejects it. A refused duress Carrier can name an Escape that is not yet
resident and is registered later beside a different spend. G drops that mark, and the later
decision does not recover it, because `DUR-5` says the pair duress bit ORs the records "naming the
same **spend commitment**". G also reverses `BtcPolicy.Exhibits.TwoRun.refused_repeat_selects_before_residency`.
In the kernel, whose ids are abstract, a pruned selected Escape's id registered again as a hot
spend breaks G too: `T` reads 510 against a floor of 700, unless a guard that exists only in the
kernel stands in for `CHN-24`.

**R: bind the role into the commitment.** It works, but it changes every published commitment
vector and the wire, for a property the stored role already gives.

**E: leave selected entries out of the hot domain, and change nothing else.** The window write
still lands, so the candidate re-enters the domain through its rewritten window, and the payment
still stops.

## Consequences

`SEC-37` is the residual, as restated, and its floor holds absent a backward wall step. The
backward-step residual stays where `DUR-13` states it: "The seed does not reach a duress intent
ingressed after a backward wall step: its `first_seen` is the rolled-back sample, so its own
decision can write a `T` already due under `DUR-7`'s comparison." Bead `bps-pxp.1` stated that
residual under its *Formal* section and left it unfixed; the owner has not ruled on it. One question is recorded and not answered: if a coercer can cause a backward
step of a node's wall clock, that residual is a route by which they time Lockdown. No finding is
opened for it.

`DUR-13` says "A hot candidate whose window shut unfired, or that this node has broadcast, caps no
`T`, and a backward wall step does not bring a shut window back, since the close reads at or above
the ratchet". The never-fires spend of `SPN-30` caps no `T` either.

A refused request whose computed Escape id is a resident hot spend's moves neither that spend's
window nor its release (decision 5). Under the normal PIN the spend fires at its `SPN-30`
`fire_at`, and a hot spend whose window shut unfired stays outside the hot domain through such a
refusal, so `SEC-37`'s floor holds on that route too. The inserted id stays in `selected_escapes`.
It acts only on a candidate later registered in the Escape role under that id.
