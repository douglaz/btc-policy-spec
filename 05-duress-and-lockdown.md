# 05 — Duress and Lockdown

The two-track duress machine: how a duress PIN silently records an intent, how the federation
commits the arm once `t` members hold the Carrier, what the freeze suppresses, how `T` is
computed, why Lockdown at `T` is unconditional, and how the best-effort sweep selects and fires
its fee rung. `ADR-0012` is the decision record and its "Accepted residuals" section is the
honest boundary; this document is the requirement set.

## The two tracks

**DUR-1** Every observable a node emits MUST be identical between a normal-PIN and a duress-PIN
request across: response bytes, response timing class, `/events`, `/healthz`, `/pending`, peer
message shapes and sizes, lock counts, allocation counts, candidate visits and store-lock hold
time. **SILENCE** is the invariant most easily lost to one innocuous new field, log line, counter
or metric; the rule for extending any surface is that if a pre-`T` duress carrier can change a
value, the value does not belong there. Silence is claimed against an adversary holding the
coordinator and the physical scene but no node (`SEC-10`); a node sees the PIN.

**DUR-2** Duress is two independent tracks. The **safety track** — freeze hot-class
finalization, then Lockdown at `T` — is keyed on the duress PIN alone plus `t`-of-`n`
confirmation, and depends on no chain view, balance, mempool, coverage or fee judgment. The
**sweep track** — combine and broadcast the pre-signed Escape at `T` — is best-effort, and every
admissibility check it performs is a fire-time check that can fail without touching the safety
track.

**DUR-3** Arming and Lockdown MUST take no transaction class, no coverage, no feerate and no
package-acceptance input. Coverage, feerate and mempool acceptance are fire-time sweep checks
and MUST NEVER be arm gates: a chain-view-dependent arm splits the armed set across nodes whose
backends disagree, and an unarmed sub-quorum then finalizes the coerced spend.

## Intent, confirmation, and the arm

**DUR-4** At ingress (`SPN-5` gate 12) the node MUST record a same-shaped **arm intent** for every
SpendRequest under either PIN, keyed by the Carrier identity, holding: the set of holders (empty
until staged), whether it is ready to propagate, whether its owner is still ruling, its duress bit
(monotonic OR with the constant-time-selected verdict), `first_seen`, its signed expiry `E` and
its monotonic deadline `D` (`NCH-33`), and whether it is committed and locally accepted. The intent
also holds its two commitment ids once `SPN-23` has computed them; an intent refused before then
names no pair. The intent write MUST run before the PIN attempt budget is charged, so a
locked-out node records a valid duress intent; the duress bit MUST be set for a refused-but-staged
duress request just as for an accepted one. **Ingress never arms.** The cover overlay of `DUR-10` is rewritten under both
PINs with `arm = false`.

**DUR-5** A **holder** of a Carrier is this node once it has staged the Carrier for propagation
(`SPN-32`), plus each distinct peer whose authenticated relay of the same Carrier this node
receives (`NCH-31`). Receiving a peer's relay proves the peer received and processed the Carrier,
not that it froze or signed. When the holder set reaches `t`, the node MUST run one **pin-uniform
holder decision** under a single store lock: mark the intent committed; write the overlay with
`arm` set to the **pair duress bit**: the OR of this intent's duress bit and those of every
resident intent and retained nonce tombstone (`NCH-40`) naming the same **spend commitment**,
under both PINs. An unbound intent uses only its own duress bit; absent bindings MUST NOT group
unbound intents. Apply this same bit to `sweep_active`, the selected Escape insertion and the
hot-candidate freeze. Only for a Carrier this node accepted, or replayed as accepted under
`SPN-23`, set `holder_quorum_reached` on both members of its pair, which opens their release
gate; if the intent names a pair, add that pair's Escape to `selected_escapes` with the pair's
duress bit (`DUR-10`); then retire the Carrier (`NCH-40`). A refused Carrier MUST NOT open any
candidate. Its holder decision MUST still perform the arm write, the scan over every hot
candidate, and the applicable set and window work under both PINs. A normal holder decision
performs the identical scan, overlay write, applicable set insertion and window refresh as its
duress twin with the same local acceptance and pair-binding outcome. The result separates
`committed` (pin-uniform, the only thing production may consume) from `armed` (duress-only, never
exposed). *(Amended 2026-10-02: refused staging grants holder authority to arm, never authority
to open candidates; pair binding follows commitment computation. Pair inheritance, including
nonce-tombstone metadata, decided 2026-10-02 and implemented 2026-10-03: separate Carriers retain
separate intents; staging or accepting a replay never arms by itself.)*

**DUR-6** A receipt for an intent whose `deadline ≤ mono_now` MUST be ignored; one whose
`expiry ≤ now` MUST answer the fixed 30-second retry (`NCH-36`) and change nothing; a sender
already counted, an uncommitted duplicate, or a committed intent MUST be an idempotent no-op. A
new holder is admitted only at attempt time `< E` while `mono_now < D`.

**DUR-7** Once armed, the node MUST enter **Lockdown** at `T` **unconditionally**: no branch, no
chain view, no sweep failure and no further authorization can skip it, and a dedicated deadline
driver attempts it on every 1-second tick with no backend I/O, one lock and one comparison
(`armed ∧ now ≥ T`). Lockdown is a latch that survives for the process lifetime with no reset;
every subsequent spend, refresh and claw-back answers `FRAUD_SUSPECTED` / `lockdown` / `funds
quarantined by policy`, presented as automated fraud prevention and never as "duress PIN used".
Lockdown blocks
NEW signing and MUST NOT block the in-flight Escape combine the sweep needs. The latch is
persisted only as `STO-4`'s extended attribute, and the only exit is the Recovery path.

**DUR-8** **The release gate.** No partial signature MAY leave a node before its candidate's
authorized fire event, and the gate is the sole egress. Every check that can block arming also
blocks signing at ingress, and a hot partial is released only when the node is NOT armed, with
the freeze bit set over every hot candidate under the same store lock that would release. So no
honest node ever releases a coerced partial, only `≤ t − 1` compromised nodes can, and that is
never a signing quorum. This coupling, not the holder count, is the safety proof: with
`n = 2t − 1` a set of `t` holders contains as few as one honest member, so `t` receipts cannot
prove `t` honest nodes froze. The count schedules when the commit happens; the gate is what
holds. The gate is symmetric: a SpendRequest pair under EITHER PIN waits for the holder decision
of a Carrier naming it, with the local acceptance authority of `DUR-5` ("only for a Carrier
this node accepted, or replayed as accepted"), before its fire time is release authority, or `t − 1` malicious peers could
withhold receipts, collect a node's matured share at fire time, and complete a coerced spend
before the duress carrier confirmed.

**DUR-9** The gate MUST fail closed. A panic while holding the sign lock or the store lock
poisons it; a poisoned node MUST release nothing, MUST force the Lockdown latch through a path
that takes no lock, and MUST stop its driver passes so that a frozen heartbeat beside
`locked_down: true` is the external signal (`API-19`). The fail-closed property MUST be asserted
by a test that poisons the lock and drives a fire pass, not left to the accident of lock order.
Opening the pair and setting the arm bit MUST be one atomic write: a duress candidate is never
observable as due-but-unfrozen.

**DUR-10** The **Armed overlay** holds: `active`, the deadline `fire_at` (`T`), `sweep_active`,
the set `selected_escapes` of Escape commitment ids, and `combine_slack_secs`. `active` has
exactly one writer — the holder decision with `arm = true` — and once set it is never cleared.
**Every** holder decision whose intent names a pair adds that pair's Escape id to
`selected_escapes` together with the pair duress bit (`DUR-5`), under either PIN, in identical
work; nothing is chosen over anything else and nothing is ever displaced (`ADR-0020`). An intent
refused before commitment computation has no Escape id to insert; that absence MUST NOT suppress its duress arm,
hot-candidate freeze, deadline computation or the refresh of existing selected windows. A
refused intent with computed ids MUST perform the same insertion without opening any candidate
(`DUR-5`: "A refused Carrier MUST NOT open any candidate"). Entries are keyed by Escape commitment
id alone; when two Carriers name the same Escape, the entry's duress bit becomes the OR of its
old value and the newly inserted pair bit, so a normal-PIN replay can never clear a duress authorization,
and the write is the same write under both PINs. Release of an entry requires BOTH
`sweep_active` AND that entry's own duress bit: `sweep_active` is a single overlay flag set for
the whole node by a holder decision with `arm = true`. It cannot by itself distinguish a marked
pair from an unrelated unmarked pair. An entry whose duress bit remains clear therefore sits in
the set present and never released. A normal-PIN holder decision can insert a set bit through
`DUR-5`'s "pair duress bit"; an unrelated pair's mark grants no authorization to this entry.
Each selected duress Escape is then gated, laddered, latched, finalized and
re-authorized on its own (`DUR-20`–`DUR-31`): a node releases its partial on every one whose own
fire-time checks pass. Nodes therefore need not agree on which Escape fires and
are not asked to. Several distinct duress Carriers — a retry after a timeout, a re-composed
spend — each carry their own Escape and reach nodes in different orders, and with a single
selector honest nodes could split 2/2/1 on 3-of-5 so that nothing reached `t`. With every
confirmed Escape selected, whichever one `t` nodes happened to see completes. This grants nothing
new: every Escape pays the escape descriptor (`CHN-14`), any two admissible Escapes whose
coverage is delivered by their own outputs overlap on inputs because each must cover
`escape_coverage_pct` of the vault (`DUR-24`) so only one can
confirm, and choosing which one is inside the powers `SEC-21` already grants a post-wrench
coordinator, which can "strip ladder rungs and re-sign, and thereby suppress or downgrade the
`T`-time sweep". Every selected Escape's coverage is delivered by its own outputs (`ADR-0022`).

**DUR-11** The freeze applies to every candidate with `hot = true`, existing and future, at once:
a frozen candidate is never due, never released, never finalized, and is refused at the
broadcast authorization even after mempool acceptance passed. Refreshes, claw-backs and Escape
candidates are unaffected. The Hot-budget ledger is not touched by the freeze (`POL-21`).

**DUR-36** An armed node MUST sign a claw-back exactly as an idle node does (`SPN-50`,
`SPN-51`): the freeze of `DUR-11` reaches hot-class candidates only, a claw-back records no
intent and reads no arm state, and the work is identical under both PINs and both states, so
the claw-back is neither a duress probe nor an armed-state oracle. A claw-back that spends the
armed Escape's inputs during `[arm, T]` pays the same escape descriptor (`CHN-14`, `CHN-35`), so
it is the sweep firing early: if it is still mempool-resident or confirmed when the Escape is
evaluated, the Escape releases nothing, failing no later than `DUR-21`'s ancestry step
(`WTC-24`) and never at coverage, since `DUR-22` restores a selected Escape's inputs; accepting
or signing the claw-back alone settles nothing, and one evicted before `T` leaves the Escape
admissible. After Lockdown a claw-back is refused with every other request
(`DUR-7`). "Sweep these coins now and lock down at `T`" is no longer one request: an Operator
who wants both claws back everything, after which Lockdown guards nothing, or submits a hot
spend under the duress PIN (`ADR-0022`).

**DUR-12** A hot spend already pending at a holder decision on a pair whose duress bit is set
MUST be suppressed by that decision: its fire is tombstoned and its partial never released.
An unbound duress holder decision suppresses it too (`DUR-5`: "An unbound intent uses only its own
duress bit"). Until a holder decision sets the node's arm bit, the node is not armed and the
spend is not suppressed. A later accepted Carrier naming a marked pair can supply that decision;
the remaining censorship residual is `DUR-34`.

## The deadline

**DUR-13** `T` MUST be computed at the holder decision, from the earliest `first_seen` among
this intent, every resident intent and every retained nonce tombstone (`NCH-40`) naming the same
spend commitment, under **both** PINs. An unbound intent uses its own `first_seen`, never another
unbound intent's. Each `first_seen` is the INGRESS-hold effective time at which the nonce was
consumed, never the commit-hold time, so that slow or selective delivery cannot stretch the
hostage window. An unrelated spend's record MUST NOT contribute. With `first_seen` denoting
that minimum, compute:

```
earliest_hot = min{ fire_at : candidate is hot, not broadcast, expiry ≥ now }   (if any)
t_ceiling    = first_seen + duress_delay_secs        # `t_ceiling`, never the threshold `t`
if earliest_hot exists:  t_ceiling = min(t_ceiling, earliest_hot − epsilon_secs)
T            = max(t_ceiling, now)                          # a past T fires now
```

When already armed, a later arm MAY only shrink `T`. Every comparison MUST use constant-time
selection so a normal and a duress commit do identical work.

**DUR-14** On every hot spend accepted while armed, `T ← max(min(T, its fire_at −
epsilon_secs), now)`. This is **dynamic `T`**: without it a post-arm hot spend with a nearer Hold
expiry would settle visibly under the normal PIN and be frozen under duress, leaking the armed
state before `T`. `duress_delay_secs` is therefore a **ceiling**, not a guarantee: a hot spend
whose Hold already matured at arm time collapses the window to now, and the ceremony MUST say
so (`MAN-29`).

**DUR-15** The DELAY before Lockdown lands has no finite bound and this set claims none. The
transition needs the sign lock; the lock is unfair; the `/sign` bulkhead (`API-4`) sheds excess
jobs but cannot change the memory-hard service rate, which one node-wide work lock serialises;
and a post-wrench coordinator holding the auth key can mint validly signed requests
indefinitely. A semaphore bounds simultaneous jobs, not successive ones, and MUST NOT be
described as bounding this delay. What is bounded is the CONSEQUENCE: a
merely delayed node is still frozen and releases nothing (`DUR-8`), `E` bounds new holder and
arm decisions, and `D` bounds residency. Read "unconditional Lockdown at `T`" everywhere as a
statement about the decision, never about its latency (`SEC-11`).

**DUR-16** There is no abort of the safety track and there MUST be no cancel operation for a
pending spend. Once armed, no key, PIN, or command cancels Lockdown; the user can truthfully say
"I cannot stop it, nobody can." A cancel would also be a duress oracle: cancel-then-refresh
completes under the normal PIN and is held under duress. The Escape is the implicit cancel
(`SPN-33`).

**DUR-18** A rebooted armed node is dead (`STO-1`): it holds no schedule, no partials and no
key, and contributes nothing further. If at least `t` armed nodes survive, the surviving set
attempts the sweep at `T`; below `t`, or on any fire-time failure, the outcome is Lockdown only
and the coins exit through Recovery. Killing nodes is denial, never theft.

## The sweep

**DUR-19** The sweep is best-effort. Its fire-time checks decide only whether the Escape is
broadcast; a failure leaves the node armed, frozen and — at `T` — locked down, with funds routed
to Recovery.

**DUR-20** Each selected Escape's fire window is `[T, T + combine_slack_secs]` for the overlay's
CURRENT `T`, not capped by its commitment's expiry. It is installed at that Escape's holder
decision, and every hot acceptance and every holder decision MUST visit every selected entry and
write its window as the constant-time selection of the shrunk bound or the retained one, under
BOTH PINs and whether or not `T` actually moved (`DUR-13`, `DUR-14`): an actual shrink MUST NOT
trigger a traversal a non-shrink does not, because `DUR-14` shrinks only on an armed node and a
traversal that ran only there would be work a normal-PIN twin does not do (`DUR-1`). The result
is that all selected windows share one `T` and one close; without it an Escape selected under an
earlier, later `T` would keep a window `SPN-41` closes at the new `T + slack` before the
Escape's own opened. Re-broadcast continues while the
window is open and that Escape is not confirmed; the loop is finite, and widening
`combine_slack_secs` widens the sweep horizon. `DUR-21` through `DUR-31` are stated for one
Escape and apply to each selected Escape independently.

**DUR-21** Before ANY partial of a selected Escape is released, the node MUST establish that
Escape's admissibility in this order, and MUST release nothing of it and burn none of its rungs
if any step fails — another selected Escape's outcome has no bearing beyond what its mempool
residency does to this one's prevouts, which `WTC-24` reads as spent: the ladder's rung
transactions exist; one batched mempool read over the whole ladder finds which rung, if any, is
resident (a resident txid outside the ladder is an error); the sweep environment of `DUR-22` is
computed; each rung's maximum finalized vsize (`CHN-16`) is computed; each rung's admissibility
(`DUR-23`, `DUR-24`) is decided; the rung is selected (`DUR-26`); the selected rung's ancestry is
validated (`WTC-24`); and only then the latch is advanced.

**DUR-22** The sweep's **protected value** — the coverage denominator — MUST be computed on
every pass from this node's current reads and never stored: the vault's confirmed value plus the
value of unconfirmed outputs whose parent transaction is in this node's vault-authorized set
(`SPN-33`), less the outputs of every selected Escape and of every resident rung, and then every
distinct input outpoint of EVERY selected Escape counted once at its `witness_utxo` value
whatever the read says of it — unspent, resident, confirmed spent or unconfirmed; a counted
input takes precedence over every exclusion, so a selected Escape spending another's change
output is still counted. Empty is an error. Within one pass every selected Escape is measured
against this one value, and on every pass the value is never smaller than the combined inputs of
the Escapes selected on it. That floor, not a value frozen at the arm, is what makes `MAN-9`'s
lower bound on coverage load-bearing — two input-disjoint selected Escapes, each delivering more
than half of a value no smaller than their combined inputs on whichever passes this node
measures them, cannot both cover — and what caps this node's aggregate sweep burn at
`100 − escape_coverage_pct` percent of what it sweeps. The guarantee is per node, over the
Escapes it had selected when it first released: an Escape selected after that release, or one
another node selected and this node never saw, can confirm beside it (`F59`) — a second fee,
never coins, since every Escape pays the escape descriptor (`CHN-14`). Restoring only the Escape
under evaluation lets the denominator shrink each time another selected Escape becomes resident,
so an Escape over the coins the first one left behind covers a smaller vault and passes
(`F54`). Unconfirmed **external** deposits MUST be excluded — their parents are not
vault-authorized and can be replaced out from under the sweep — unless a selected Escape spends
them, in which case they are counted and that Escape waits on `WTC-24`; an absent or inflated
prevout a selected Escape names is counted too, cannot confirm (`WTC-24`, `CHN-11`), and can only
raise this denominator against real Escapes: denial inside `SEC-21`. A claw-back (`CHN-35`)
changes this denominator only through the reads above: its inputs that are a selected Escape's
stay counted, its other inputs leave at mempool residency — the vault-unspent read includes the
mempool (`WTC-2`) — and its outputs, which all pay the escape descriptor, never enter. What the
coordinator composes over (`OPR-33`) never changes this denominator.

**DUR-23** Per rung: every input's `nSequence` MUST equal `0xfffffffd` if the Escape carries a
ladder and `0xffffffff` otherwise; `fee = total_in − Σ outputs`; `vsize` MUST be positive; and
`fee ≥ escape_feerate_floor × vsize` compared in arithmetic that cannot overflow, never as a
truncated integer feerate.

**DUR-24** Per rung, coverage MUST hold on **outputs**: `delivered × 100 ≥ protected_value ×
escape_coverage_pct`, where `delivered` is the sum of output values whose script derives from
the escape descriptor within `max_derivation_index`. Measuring on outputs is what caps the Escape's fee at
`(100 − escape_coverage_pct)%` of protected value — of the denominator of the pass the rung is
measured on, which `DUR-22`'s floor makes no smaller than the Escape's own inputs, so the cap
bounds the fee against the coins that Escape moves; a rung that would overpay fails here and is
never selected, so a fee spike above the cap is not overpaid — the sweep tops out.

**DUR-25** Admissibility before release MUST be evaluated at each rung's **maximum** finalized
vsize, so it still holds once the missing signatures land; after finalization it MUST be
re-evaluated on the exact finalized transaction at its exact vsize.

**DUR-26** Rung selection MUST be:

```
if the ladder has one rung:   rung 0 if admissible, else fail
target   = bump target (DUR-30), or 0 on any error or no reading
required = max(target, escape_feerate_floor)
needed   = the cheapest rung whose fee ≥ required × its maximum finalized vsize, else the top rung
choice   = the cheapest ADMISSIBLE rung ≥ needed,
           else the most expensive admissible rung (the cap),
           else fail
selected = max(choice, current latch)
if selected is not admissible: fail        # a lower rung cannot replace a higher live one
```

A fee-pressure reading is never new liveness authority: an error reading it falls back to the
sealed floor.

**DUR-27** The latch MUST be monotone and bounded by the ladder length, so the loop cannot
bump, unbump and rebump as a median jitters, and a reorg re-broadcast sends the same rung again.
Partials MUST be released for the prefix from the lowest admissible rung through the latch, and a
rung the node's own predicate refused MUST be released to nobody: a partial on an inadmissible
rung is finalizable authority in `t − 1` compromised hands. **Prefix** here is the CUMULATIVE
release obligation across fire passes, not a retransmission of its beginning on every pass;
`SPN-38` owns how the passes are batched and advances the cursor that makes them cumulative.

**DUR-28** Finalization takes the highest rung at or below the latch with `≥ t` distinct valid
partials on every input; quorum on an Escape's own commitment id IS cross-node agreement on that
Escape, and it is reached per Escape — several selected Escapes may each gather `t` on different
subsets of nodes. The partials counted are the finalizing node's *Held partial* set, defined in
`CONTEXT.md`: `SPN-36`'s "the partials received per `(input, signer)`", under `NCH-24` and
`NCH-25`. Of the Escapes one honest node had selected when it first released, at most one can
confirm, because they conflict on inputs or one fails coverage against `DUR-22`'s floor; across
subsets of nodes that selected different Escapes, or for an Escape selected after that release,
two can confirm (`F59`), each to the escape descriptor.
The finalized transaction MUST pass `DUR-23` and `DUR-24` again at its exact vsize.

**DUR-29** The finalized rung MUST pass package assembly and the backend's mempool-acceptance
test (`WTC-24`, `WTC-26`) and MUST be re-authorized under the store lock — this Escape still in
`selected_escapes` with `sweep_active` AND its own duress bit set, not frozen, window open —
immediately before the send, as
the linearization point between arming
and sending. A resident lower rung is replaced by RBF; the replacement MUST spend exactly the
same ordered outpoints.

**DUR-30** The **bump target** MUST be a pure function of the confirmed chain: with `tip` the
node's tip height, `anchor = tip − (tip mod 6)`; `median` = the 50th-percentile feerate of the
block at `anchor` in sat/vB, computed by the algorithm `WTC-2`'s backend contract fixes
(`WTC-15`); `target = ⌊median / 5⌋ × 5`, quantised **down**. No mempool reading, no fee estimator
and no wall clock may enter it: two honest nodes reading different medians select different rungs.
That is not fatal — the cumulative prefix release of `SPN-38` and `DUR-27` makes their released
sets overlap, and `DUR-28` finalizes "the highest rung at or below the latch with `≥ t` distinct
valid partials on every input", so a rung that enough nodes reached still completes. The cost of a
split is a sweep at a cheaper rung than the chain is asking for, which under fee pressure is the
difference between a confirmed sweep and coins left for Recovery. The three reducers each narrow
the split without closing it: quantising the anchor to six blocks means nodes whose tips differ by
a block usually read the same block, though tips straddling a multiple of six (5 and 6 anchor to 0
and 6) do not; the five-unit step means nodes reading different blocks usually agree, though
medians straddling a step boundary (4 and 5) do not; rounding down means the ladder never charges
for pressure the chain is not showing. No reading means no pressure, which sets `target = 0` and
leaves `required` at the sealed floor — it does NOT mean the base rung is selected, because
`DUR-26` still takes the cheapest ADMISSIBLE rung at or above `needed` and still applies
`selected = max(choice, current latch)`.

**DUR-31** A selected Escape MUST NOT be marked broadcast. On every pass the node re-classifies
each selected Escape's ladder: any rung confirmed ⇒ the paired spend's Hold and every conflicting
hot candidate are cleared (`SPN-33`) and that Escape stays resident and unlatched so an in-window
reorg re-sends the same rung; a rung resident at or above the latch ⇒ nothing; otherwise ⇒
combine and send the latched rung. A confirmed rung of one selected Escape spends inputs every
other Escape this node had selected before its release shares (`DUR-28`), so on every later pass each such Escape fails `DUR-21`'s
predicate no later than `WTC-24` — coverage may fail first once the spent coins leave the
denominator, and a resident txid outside its own ladder is an error earlier still — releases
nothing, and is pruned with its pair at window close (`SPN-41`). The invariant is that no partial
leaves and nothing is broadcast once a required input is confirmed spent; which step refuses is
not part of it.
`SPN-33`'s input-conflict invalidation names hot candidates only and is NOT what retires them; no
cross-Escape rule is needed because `WTC-24` already refuses to assemble over a spent prevout.

**DUR-32** On any sweep failure — pre-release inadmissibility, no preflight context, no quorum,
post-finalization inadmissibility, package rejection, broadcast error — the node MUST log and
continue. Lockdown at `T` has already happened; the outcome is frozen funds and Recovery, never
theft. A `fail` from `DUR-26` is the designed fail-safe, not an error path.

**DUR-33** A confirmed armed Escape MUST clear from the pending log the candidates it defeated —
its paired spend and every hot candidate sharing an input — and refund their reservations where
unexposed, exactly as a normal settlement does. *(The reference implementation once removed only
the paired candidate on this path — `DEF-5`.)*

## Residuals stated here

**DUR-34** **Censorship.** If the duress Carrier reaches fewer than `t` nodes, nodes that
recorded its intent can still arm at a later accepted Carrier's holder decision naming the marked
pair, including after the intent retires (`DUR-5`, `NCH-40`). A node that never recorded the
intent inherits no mark from it. If no holder decision sets its arm bit, it stays unfrozen and a
hot spend already pending can finalize at its Hold expiry. That spend is
user-authored and user-destined, so the attacker reaches funds only if they also hold the hot
wallet's keys. Admission remains metered, but `POL-20` states: "The Hot budget provides an
**acceptance-time admission bound**, not a rolling completion-loss bound." A PIN-independent
capacity refusal consumes, retains, signs and relays nothing; a delivery-horizon refusal keeps the
nonce tombstone and the relay record and follows the gate-specific staging rules `SPN-9` owns —
signing no partial on either path, creating no intent only at gate 10; neither contributes a
coerced partial. Only a true total drop, or sustained admission censorship, leaves the previously admitted
pending spend to finalize. Closed in a later version by a direct user-to-node path.

**DUR-35** **Forged receipts** can over-arm a proper subset of honest nodes — an admitter plus
`t − 1` forged holders — which is fund-identical to censorship and lands on the same residual:
Lockdown at `T`, then Recovery, never theft. An adversary who can partition delivery per link,
passing `t − 1` relays to one node while blocking the links among the rest, obtains a genuine
split; that adversary is stronger than the untrusted relay of `DOM-2` and is out of model. The
exact shape `n = 2t − 1` (`CHN-2`) is what leaves no unfrozen signing quorum outside an armed
set while tolerating every `t − 1` withholding minority.
