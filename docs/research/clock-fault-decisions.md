# Clock-fault decisions: F3, F4, F13

These records propose no policy and close no finding. The owners remain
[F3, F4 and F13](../../16-open-findings.md). F48 remains unanswered; this draft
does not start its follow-on work or amend earlier records.

## F3: channel freshness after a forward excursion

At wall time 1000 and monotonic time 0, accept a Spend with `E = 1200` and
`D = 200`, assuming its age horizon permits acceptance. At monotonic time 10,
an authenticated envelope encounters raw time 10000. The ingress guard latches
10000. Correct the wall to 1001; honest envelopes stamped 1001 now fail
[NCH-12](../../06-node-channel.md): “timestamp ∈ [now − 300, now + 60]”.
[NCH-13](../../06-node-channel.md) specifies “the freshness high-water is
forward-only and never lowered”. Ordinary channel admission therefore stays
unavailable until sender stamps reach 9700, after this Spend's authority and
residency have ended. Arbitrarily larger excursions give arbitrarily longer
outages, even with continuous delivery.

Correction alone does not recover admission.
[NCH-38](../../06-node-channel.md) says “a larger excursion can make the
authenticated channel unavailable for unbounded real time”. Positively, with
a smaller latch of 1400, corrected stamps can reach 1100 before `E` and `D`,
provided time and delivery progress and quota admits the envelope. This is
conditional recovery, not a universal deadline.
[`BtcPolicy.Progress.f3_blackhole`](../../tools/formal/BtcPolicy/Progress.lean)
has delivery at every slot; the positive receipt theorem additionally needs
`BtcPolicy.Progress.envelopeFits`. The model omits quota and the outer-stale
path's answers, so its counterexample does not describe those answers.

The existing exception matters. [NCH-14](../../06-node-channel.md) permits
bounded decoding “solely to recognise an exact resident Spend Carrier”.
[NCH-36](../../06-node-channel.md) limits the authenticated, quota-admitted
case to “the resident nonce and signed expiry match, `mono_now < D`,
the generation is active, ruling or staged, the holder decision is uncommitted,
and the sender is not already counted”. [NCH-37](../../06-node-channel.md)
adds “verify the coordinator signature and the nonce length; check
propagatability; under the sign lock refuse if locked down” and “only if the
nonce high-water is still below `E`”. For alternate signatures it requires
“reserve the single node-wide memory-hard slot” and “revalidate after
reacquisition”. Its fixed outcomes are
“`STALE_TIMESTAMP` (terminal), `RATE_LIMITED{30}` (actionable), or
`RATE_LIMITED{1}` (derivation pending)”. These bounded receipt-only answers
consume no nonce and do no PIN, signing, candidate or outbox work. They do not
restore ordinary admission. [NCH-36](../../06-node-channel.md) says “retries
are bounded by `E` and `D`, never unbounded”.

Classification: requires a protocol decision. F3 names bounded high-water decay
and an exact authenticated-message exception as unchosen directions. Recommend
first choosing the progress guarantee, then deciding whether the existing
exception suffices for that scope. Lowering the latch now conflicts with
NCH-38: “A receiver's wall-clock correction MUST NOT lower the freshness
high-water”. That amendment needs an owner decision and stops here. Any broader
exception or decay needs separate approved design and replay/captured-message,
quota, nonmutation and PIN-independent observation evidence. Existing unbounded
behavior is not a newly accepted residual; no choice is approved.

## F4: a pruned Refresh poisons attempt authority

Assume sufficient capacity and an age horizon admitting these expiries. At
raw time 100, monotonic time 0, accept a Spend with `E = 200`, `D = 100`, and
a distinct Refresh expiring at 240. At monotonic time 10, raw time jumps to
241. An accepted fresh request expiring at 242 actually prunes the Refresh;
the shared nonce high-water advances to 240. Correct raw time to 110 at
monotonic time 11. The Carrier remains resident because `11 < D`, but its
`E = 200` is below the latch. This small excursion need not defeat channel
freshness: a stamp of 110 is within 300 of 241.

The accepting transition is essential. [SPN-13](../../04-spend-lifecycle.md)
says “The high-water is advanced, on an accept only, to the greatest expiry of
every entry that accept pruned”. A refused request cannot produce this trace:
[SPN-14](../../04-spend-lifecycle.md) says “A refused request MUST mutate
nothing: no entry, no high-water”. Capacity “refuses; it never evicts”.
[NCH-34](../../06-node-channel.md) distinguishes “attempt time `< E` AND
`mono_now < D`”. Residency cannot supply missing attempt authority, and the
outer-stale exception cannot bypass its high-water-below-`E` premise.

[`BtcPolicy.Progress.f4_no_arming`](../../tools/formal/BtcPolicy/Progress.lean)
takes a resident Carrier whose `E` is at or below the nonce latch; even relays
at every slot do not arm from it. `D` ends residency, not the refusal. A
positive case instead needs nonce high-water below `E`, a window-valid current
attempt, remaining `D`, and the receipt path's authentication, quota and state
conditions. `BtcPolicy.Progress.window_open_below_latch` addresses the window;
`BtcPolicy.Progress.armed_within` additionally requires bounded service and
`BtcPolicy.Progress.deciding`. Neither proves deployment latency.

This Carrier failure differs from the general log outage. When
`raw_now + max_commitment_age_secs ≤ high_water`, no expiry satisfies both
window bounds. `BtcPolicy.Progress.f4_every_request_refused` captures that
condition; `BtcPolicy.Progress.f4_log_outage` makes it arbitrarily long using
two excursions. The latter requires an expiry signed against the excursion,
by a hostile coordinator or one sharing it. The concrete Carrier failure
above needs only the previously accepted Refresh, not that signing premise.

Classification: requires a protocol decision. F4's existing options are
per-class high-waters, raw-time receipt sampling, or keeping shared authority
with its stated limits. Recommend retaining the current rule pending the
scope choice, without presenting its outage as newly accepted. Splitting
conflicts with [SPN-12](../../04-spend-lifecycle.md): “one shared non-decreasing
high-water mark”; raw-only acceptance conflicts with SPN-10's “expiry >
effective_now”. Each affected amendment needs an owner decision and stops.
Future design must preserve forgotten-nonce rollback protection, capacity,
refusal nonmutation and PIN-uniform work. [NCH-33](../../06-node-channel.md)
requires “checked arithmetic that fails closed” and “Nothing later” may move
accepted `D`; changing receipt authority cannot silently extend it. No option
is approved.

## F13: Lockdown needs service and an enabled comparison

An armed node approaches `T` with its ratchet below `T`. After wall time
passes `T`, successive signed requests obtain the sign lock while the deadline
driver never does. The coordinator can keep issuing requests. The driver may
instead first obtain service at any chosen later slot `N`; eventual fairness
allows arbitrarily large `N`. [DUR-15](../../05-duress-and-lockdown.md) states
“The DELAY before Lockdown lands has no finite bound and this set claims
none”. Its warning is precise: “A semaphore bounds simultaneous jobs, not
successive ones”.

Classification: requires a stronger service premise for any finite delay
claim. Recommend preserving the current decision/latency distinction until
that premise is approved. [SEC-11](../../12-security-requirements.md) says
“as a decision and never as a latency”. The existing alternatives are leaving
latency unbounded, claiming eventual progress with stable enabling, or
requiring bounded service with enabling. No scheduling mechanism is selected.

Positively,
[`BtcPolicy.Progress.latch_within`](../../tools/formal/BtcPolicy/Progress.lean)
requires driver service within `B` slots of every instant and `driverSees =
true` throughout `t0 ≤ u ≤ t0 + B`; it yields the latch at `t0 + B + 1`.
`BtcPolicy.Progress.latch_within_of_read` retains `clampOn = .priorArm`,
`driverTime = .ratchet`, bounded driver service, and `ReadPast` at `t0`:
the ratchet having read `T` on an armed node. These are slots, not seconds.
Negatively, bounded service with every driver sample below `T` still fails,
even if intervening samples exceed `T`; eventual fairness alone supplies no
finite bound. `BtcPolicy.Progress.delayed_node_frozen`, over every schedule
from a reachable world, proves that a fire pass on the armed node queues no
hot partial. It does not establish latch latency or recall previously exposed
authority.

Changing ratchet updates conflicts with [ADR-0026 decision
1](../adr/0026-a-time-ratchet-a-clamped-t-and-a-one-way-release-close-the-clock-family.md): “Nothing else moves it — not a fire pass, a prune, a
tick of this driver or of the store prune driver, nor a refused request of
any kind — and it is never lowered”. Such an amendment needs an owner
decision and stops; scheduling changes separately need service evidence and
PIN-independent observations. No service bound is approved.

After the scope choice, queue F3's admission mechanism, F4's expiry authority
and F13's service premise separately, without dependencies among the findings.

Owner question: when the clock is corrected while `E` and `D` remain open,
receipts arrive every slot and signed work keeps competing with the driver,
should the intended guarantee be **explicitly conditional progress with named
enabling and bounded-service premises** (recommended; F3/F4/F13), progress
before expiry from correction and delivery alone (F3/F4, with a separately
bounded Lockdown service obligation for F13), or the existing unbounded
outages and delay with only their stated consequence limits (F3/F4/F13)?
