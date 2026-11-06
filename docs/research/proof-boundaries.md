# Proof boundaries of the headline theorems

Research task `bps-uaer.1`, base commit `e1c3784`. No protocol rule, model definition or theorem
statement changes.

For seven security claims, this record says why the theorem applies, what it takes from its caller,
and which planned work would derive what it takes. A declaration owns its statement and a
requirement owns its claim and scope; neither is restated. It covers these seven claims and is not
an inventory of the formal layer. The citation and identifier gates hold its declaration names and
requirement identifiers to what the build and the documents define.

**Premise classes.** *Protocol*: a protocol fact that should be derivable from reachable
transitions. *Bridge*: an abstraction relation needing a bridge to another existing module.
*Environment*: an environmental condition. *Outside*: a cryptographic or hardware assumption that
stays outside this phase.

**Planned work.** Each item's beads are children of `bps-uaer`.

| Name | Work | Bead |
| --- | --- | --- |
| composition | One abstract message family and a local projection over `Kernel.step` | `bps-uaer.2` |
| provenance | Partial delivery, cumulative extracted keys, derived honest provenance | `bps-uaer.3` |
| witness | The earlier-release exhibit as one distributed history | `bps-uaer.4` |
| cohort | Hold-protected blocking cohort | `bps-uaer.5` |
| every-input | Per-input possession and authorization | `bps-uaer.6` |
| ingress | Checked ingress to accepted state | `bps-uaer.7`, `bps-uaer.8` |
| sweep | Selected Escape to permitted submission, over backend state | `bps-uaer.9`, `bps-uaer.10` |
| federation silence | SILENCE lifted over the composed execution | `bps-uaer.11` to `bps-uaer.13` |
| accounting | Federation acceptance to the admission premises; a non-normative comparison, `hot-accounting-comparison.md` | `bps-uaer.14`, `bps-uaer.15` |
| progress | Progress, resource limits and Recovery composition | `bps-uaer.16` to `bps-uaer.18` |

## 1. Release provenance

**Owner:** `DUR-8`. **Theorem:** `Kernel.hot_release_provenance`.

**Why it applies.** Given one node's `Kernel.Execution` and a hot queue effect at input 0 in the next
step, it gives an unarmed node and `Kernel.NormalRelease` evidence in that history for this signer,
message and commitment. The evidence is derived by induction (`Kernel.openProvenance_execution`).

**Domain.** The initial boundary of `Kernel.Execution`, which leaves overlay, tombstones, clocks and
threshold unconstrained; every `Kernel.Event`.

**Excluded.** Other signers' rows, other candidate classes, inputs other than 0, and rows written by
`adversaryExposes` or `receivePartial`.

| Premise | Class | Status |
| --- | --- | --- |
| `hr`, the accepted-only refusal rule | Protocol | Discharged at `Kernel.current` |
| `hx`, the history is this node's own execution | Protocol | Discharged for an honest node of a federation by `Federation.project_execution`; given otherwise |
| Candidates an `accept` event carries are unconstrained | Bridge | Over `Ingress.CheckedTrace`, class, transaction, outflow, commitment id and expiry come from the request (`Ingress.accepted_validates`); the fire time stays the request's; given otherwise |
| One input, one candidate per rung | Bridge | Provenance stays at input 0. On a one-input transaction, with every counted signer among the keys, the counts agree with `Authority.quorum` (`Authority.exposed_refines`, `Authority.held_refines`); `Authority.input_zero_insufficient` shows the restriction is needed |
| A receipt's sender is the one the wire proved (`NCH-5`) | Outside | Retained |

**Positive:** `Exhibits.Provenance.normal_release_has_provenance`, on a reachable run.
**Negative:** `Exhibits.Provenance.holder_bypass_releases_without_provenance`, a deliberately broken
extra writer and not a withdrawn rule.

## 2. No exposed quorum

**Owner:** `DUR-8`'s "never a signing quorum". **Theorem:** `Kernel.no_exposed_quorum_without_normal`.

**Why it applies.** `Kernel.HonestExposureProvenance` and `Kernel.NoHonestNormalDecision` together say
that every input-0 row for the target message has a compromised signer, and the theorem then counts
distinct signers against `bound`. The proof is that count. Its safety content lies in those premises.

**Domain.** Any rules, signer histories and candidate, and any `Kernel.World`: `w` need not be
reachable.

**Excluded.** Possession at a combiner, other inputs, finalization, signature validity and the Bitcoin
message (`ADR-0023` decision 12).

| Premise | Class | Status |
| --- | --- | --- |
| `honestExposure`, for honest rows | Protocol | Derived over a composed execution by `Federation.honest_exposure_provenance`, with each signer's projection as its history and the extracted set as the compromised list; given otherwise |
| `honestExposure`, no honest non-hot row shares the message | Bridge | A premise of the derivation too, as `Federation.HotBinding`. For the input-0 message of an admissible hot-class member, over `Ingress.CheckedTrace`, it is `Ingress.hot_binding`, which takes a collision-free transaction identity (Outside); `Ingress.no_exposed_quorum` takes those two premises in its place for a checked spend; given otherwise |
| `noNormal`, no honest normal decision ever on this message | Environment | Given; for one target, `Federation.cohort_no_exposed_quorum` replaces it, and `bound`, with a Hold-protected cohort of honest signers whose keys are not extracted |
| `bound`, fewer than `t` distinct compromised signers | Outside | Retained; `Federation.no_exposed_quorum` states it over the cumulative extracted-key set |
| `w` as the exposure inventory of one federation | Bridge | The partial inventory, forged rows included, holds every honest node's rows (`Federation.node_matched`); `Exhibits.EarlierRelease.linked_preserves_prior_quorum` |

**Positive:** `Exhibits.Provenance.repeated_exposure_has_no_quorum`, on a reachable world. Each of its
honest rows has another message or another input, as the two premises force, so it exercises no honest
target row. `Exhibits.Composition.authorized_provenance` derives the premise on a composed run whose
inventory has honest target rows. **Negative:** `Exhibits.EarlierRelease.later_freeze_preserves_prior_quorum`
weakens `noNormal` to a cutoff, over an inventory not claimed reachable;
`Exhibits.EarlierRelease.linked_preserves_prior_quorum` does the same on a composed run.
`Exhibits.Composition.fabricated_honest_row_refused` drops `honestExposure` alone, on a kernel
execution whose rows the composed execution refuses, and
`Exhibits.Composition.extracted_set_reaches_threshold` drops `bound` alone, on a composed run.
`Exhibits.Ingress.checked_binding` derives the binding on a checked run, and
`Exhibits.Ingress.collision_breaks_binding` drops the collision-free identity alone: the same checked
run puts an honest Escape row on the spend's message.
**Every input.** `Federation.no_exposed_authorization` takes the composed theorem's premises and
concludes that no signatures drawn from the partial inventory give `Authority.normal` for the
candidate's transaction, on every input; the kernel theorem is unchanged.

## 3. Hot admission

**Owner:** `POL-20`, which says "The accounting theorem is `BtcPolicy.Ledger.bridge`, at one cut" and
holds the premises in prose. **Theorem:** `Ledger.bridge`, resting on `Ledgers.counting`. One node's
supply comes from `Ledger.liveSum_le_cap` and `Ledger.countsAt_of_sysRun`.

**Why it applies.** At supplied cuts, a cohort every spend of which is counted at `q` or more cuts,
over ledgers within the cap, has its outflow bounded in the cleared form of the theorem's conclusion.

**Domain.** `Ledger.bridge`: arbitrary cuts, with no execution behind them.
`Ledger.liveSum_le_cap`: any finite composed trace from any `Ledger.Sys` under the cap.
`Admission.fed_bridge`: the honest nodes' ledgers at the end of any schedule of
`FedSilence.lapply` steps from empty ledgers, legal or not, each at its own HotClock sample. A legal
schedule from a state a `Federation.Execution` reaches, with its ledgers forgotten, leaves a
`Federation.Execution` (`FedSilence.lrun_execution`); `Exhibits.Admission.run_execution` is that for the positive run. Conversely, on a schedule at each
step of which gate 24 admits over the ledgers it builds (`Admission.lfaithful`), forgetting the ledgers
leaves `Federation.run` over the same schedule (`Admission.lrun_faithful`), so the federation part of a
run built without ledgers is a ledgered run: section 10's is.

**Excluded.** `POL-20` says "MUST NOT be presented as a bound on funds completing or lost in an
arbitrary rolling window".

| Premise | Class | Status |
| --- | --- | --- |
| `hnd`, duplicate-free cohort ids | Bridge | Caller's list; given in `Admission.fed_bridge` too |
| `hamt`, one amount per commitment across cuts | Bridge | Derived over a ledgered federation run as `Admission.one_amount`: every row of an honest ledger is the reservation of a checked acceptance at that node (`Admission.row_origin`, `Admission.row_checked`), and `Ingress.one_amount_per_commitment` gives one amount per commitment id. Premises kept: empty ledgers at the start, every acceptance checked (`Ingress.CheckedTrace`), a collision-free commitment id (Outside), and each cohort amount a checked spend's outflow under its id (`hval`) |
| `hinv`, each cut's ledger within the cap | Protocol | Derived over a ledgered federation run as `Admission.led_le_cap`: node `i`'s ledger is `Ledger.sysRun` over its own events (`Admission.lrun_sys`), from an empty ledger |
| `hcohort`, `q` or more counted cuts per spend | Protocol | Derived over a ledgered federation run as `Admission.cohort_count`, for `POL-20`'s cohort read off the run (`Admission.Counted`): `q` distinct honest nodes at each of which the spend is counted (`Admission.counts_at_cut`). That `q` such nodes exist is the cohort's definition and stays the caller's |
| `Ledger.countsAt_of_sysRun`'s `hs`, `hr`, the guard values | Protocol | Discharged at the current values by `Exhibits.HotLedger.countsAt_of_sysRun_with_current`; premises of `Admission.fed_bridge`, discharged at the current values in `Exhibits.Admission.admission_bound_derived` |
| Its `hsplit` | Protocol | Derived: a step of the schedule at node `i` (`Admission.nodeTrace`) |
| Its `ha`, `hfresh`, `hprune`, the run holds an admission of this spend with no charge at its check, and keeps the row through every prune | Protocol | The terms of `Admission.Counted`, which is `POL-20`'s "accepted at a reservation time inside that node's own interval, counting only reservations not refunded while unexposed by the cut"; not derived from anything else |
| Its `hwin`, that admission inside the cut's trailing interval | Environment | Retained, inside `Admission.Counted` |
| Its `hm`, `Ledger.MonotoneHotClock` | Environment | Retained in the form it is used, `hclock`: every HotClock sample a node takes in the schedule is at or before its cut sample |
| The cuts are exactly the honest nodes, with `q` and the length as `t − c` and `n − c` | Environment | Retained |

**Positive:** `Ledger.bridge_nonvacuous`, hand-seeded rows;
`Exhibits.HotLedger.composed_row_counted_by_theorem_with_current`, a composed run of one node;
`Exhibits.Admission.admission_bound_derived`, a legal ledgered run of three honest nodes accepting
one checked spend, counted at all three cuts (`Exhibits.Admission.run_cuts`);
`Exhibits.LedgerSilence.coerced_admission_bound`, the end-to-end run of section 10.
**Negative:** `Ledger.rerun_exceeds_cap` and `Ledger.f61_per_spend_conclusion_false`, both hand-seeded;
`Exhibits.HotLedger.adr0014_refutes_completion_bound`, against the completion reading. Failing
siblings of the derivations: `Exhibits.Admission.collision_splits_amount` (`hamt` without a
collision-free commitment id), `Exhibits.Admission.seeded_ledger_breaks_premises` (`hinv` and
`hamt` from a hand-seeded start ledger), `Exhibits.Admission.refunded_not_counted`,
`Exhibits.Admission.retry_not_fresh` and `Exhibits.Admission.backward_clock_uncounts` (a
reservation refunded, a retry that places none, and a cut sample behind the node's own, each
uncounted).
`Exhibits.HotLedger.f63_twins_end_charging_nothing` keeps charge and authority apart and does not
refute this theorem. `Exhibits.LedgerSilence.too_late_needs_budget`: a history built without the ledger
that gate 24 refuses at the cap it runs under.

## 4. SILENCE

**Owner:** `DUR-1`, with the scope `SEC-10` holds. **Theorem:** `Silence.silence`,
`Silence.silence_initial`, and `Exhibits.TwoRun.silence_with_current`.

**Why it applies.** Two enrolment tables, one shared input trace and one coupled pair of states emit
equal `Silence.Obs` pairs along the walk `Silence.obsPair`, which stops at `Silence.preHorizon` or
`Silence.wfEvent`.

**Domain.** `Silence.silence`: any coupled pair meeting `Silence.NodeInv`. `Silence.silence_initial`:
one system taken twice, unarmed, with no candidates or Carriers and the sweep flag clear. The trace's
samples are unconstrained.

**Excluded.** Every other node. The docstring of `BtcPolicy.Silence` names what `Silence.Obs` omits.

| Premise | Class | Status |
| --- | --- | --- |
| The six rule and marker values | Protocol | Discharged at the current values by `Exhibits.TwoRun.silence_with_current` |
| `Silence.Coupled`, `Silence.NodeInv` | Protocol | Discharged by `Silence.silence_initial` for its one system taken twice, under its own `hi` and `hs`; given otherwise |
| One shared trace, with peer relays held equal | Bridge | Under one fixed exogenous schedule, discharged by `FedSilence.fed_silence` and `FedSilence.fed_silence_fresh`: the inventories, equal at the initial states, stay equal in both runs, and from a `Federation.Fresh` start the relays and partials a node receives come from the composed run. Against an observer that picks each step from its own run's observations, discharged by `FedSilence.fed_silence_adaptive` and `FedSilence.fed_silence_adaptive_fresh`. Each step's messages are compared per destination, by shape (`FedSilence.FObs`); no theorem gives their bytes, and `FedSilence.frame_preimage_length` gives an envelope preimage's length only from its payload's |
| The stop at `Silence.wfEvent` | Bridge | ingress. A claw-back's ingress stops the walk (`Exhibits.LedgerSilence.clawback_outside_walk`): it is born with a window close, which `Silence.NodeInv.noWindow` forbids a candidate no selected entry acts on |
| `SEC-10`'s "release-history premise" and "digest premise" | Outside | Retained |
| A coordinator honest until the wrench (`SEC-10`) | Environment | Retained |
| `DUR-1`'s "no record of either PIN from any source" | Environment | Retained |

**Positive:** `Exhibits.TwoRun.silence_on_armTrace`, whose prefix ends at the arm;
`Exhibits.LedgerSilence.coerced_silent`, the end-to-end run of section 10 against an observer.
**Negative:** `Exhibits.TwoRun.marker_leaks_with_armBit`,
`Exhibits.TwoRun.traversal_leaks_with_onlyWhenMoved`, `Exhibits.TwoRun.duress_only_insertion_leaks`,
`Exhibits.TwoRun.f60_ratcheted_close_alone_leaks`, `Exhibits.TwoRun.f60_ratcheted_driver_alone_leaks`
and `Exhibits.TwoRun.silence_needs_unarmed`. `Exhibits.TwoRun.horizon_is_where_the_runs_part` shows the
first divergence past the horizon.
On a two-node federation run, `Exhibits.FedSilence.fed_marker_leaks_with_armBit`,
`Exhibits.FedSilence.fed_traversal_leaks_with_onlyWhenMoved`,
`Exhibits.FedSilence.fed_close_on_effective_leaks`, `Exhibits.FedSilence.fed_driver_on_effective_leaks`
and `Exhibits.FedSilence.fed_duress_only_insertion_leaks` are the same leaks, and
`Exhibits.FedSilence.fed_horizon_is_where_the_runs_part` the same boundary.
`Exhibits.FedSilence.hidden_state_reader_leaks` is a scheduler that reads node 1's arm bit and so
distinguishes the families; it is not a `FedSilence.Observer`, the type `FedSilence.fed_silence_adaptive`
takes; on the end-to-end run, `Exhibits.LedgerSilence.arm_reader_leaks` is the same reader, and
`Exhibits.LedgerSilence.coerced_parts_at_fire` the boundary.
Per destination, `Exhibits.FedSilence.fed_duress_route_leaks` is a relay route that reads the duress
bit, `Exhibits.FedSilence.fed_duress_refund_leaks` a freeze that refunds a frozen charge (`POL-21`),
and `Exhibits.FedSilence.fed_horizon_frames` the post-horizon Escape partials addressed in one
family only. `Exhibits.FedSilence.equal_frames_unequal_bytes` is one frame whose envelope preimages differ
by the nonce alone.

## 5. Escape coverage

**Owner:** `DUR-22` and `DUR-24`; `DUR-28` says "Of the Escapes one honest node had selected when it
first released, at most one can confirm". **Theorem:** `Coverage.per_node_single_sweep`, resting on
`Coverage.denominator_floor`.

**Why it applies.** Its conclusion is `False`: two Escapes whose joint delivery fits within a nonzero
`S` inside each pass's selected inputs cannot both cover at or above the floor.

**Domain.** Any passes and Escapes, with no execution, chain or kernel state behind them.

**Excluded.** Federation-wide uniqueness, a later selection, another node's selection, and
confirmation.

| Premise | Class | Status |
| --- | --- | --- |
| `hpct`, a coverage at or above the `MAN-9` floor | Bridge | Caller's value; still a premise of `Sweep.single_sweep_needs_common_floor` |
| `hS`, `hf₁`, `hf₂`, a nonzero `S` within each pass's selected inputs | Bridge | Still premises there, stated over the passes `Sweep.readsAt` builds: the common floor a global result needs |
| `hconserve`, the pair's joint delivery within `S` | Bridge | Still a premise there |
| `h₁`, `h₂`, the coverage verdict at each measured pass | Protocol | Derived: each is `Sweep.check` at an assembly of a composed run (`Sweep.assembled_of_packageOk`), against the pass that node read |

**Positive:** `Exhibits.f59_floor_holds` with `Exhibits.f59_external_refused_with_current`, hand-seeded:
the floor holds on both passes, and one Escape covers while the other does not. No exhibit instantiates
the theorem itself. **Negative:**
`Exhibits.late_selection_admits_both`, `Exhibits.cross_node_admits_both`,
`Exhibits.f54_admitted_with_restoreOne`, `Exhibits.f59_external_admits_both_with_withdrawn` and
`Exhibits.subtracting_breaks_floor_on_that_pass`. On a composed run: positive
`Exhibits.Sweep.successful_sweep`; negative `Exhibits.Sweep.inadmissible_beside_admissible` and
`Exhibits.Sweep.different_selected_sets`, in which the floor fails at one node and both Escapes are
submitted.

## 6. Package validity

**Owner:** `WTC-24` and `WTC-25`. **Theorem:** `Package.admitted_only_when`.

**Why it applies.** It reads back what an admitted `Package.validate` verdict established, under either
guard value: the resident's inputs resolved, each input shown or among them, the ancestors the walk's,
all authorized and within the limit.

**Domain.** Any snapshot, mempool read, creator map, authorized list and candidate, with no execution
behind them.

**Excluded.** The module docstring of `BtcPolicy.Package` lists what is not modelled. No theorem here
says the package enters a mempool or a block.

| Premise | Class | Status |
| --- | --- | --- |
| `snap`, `mem`, as the node's reads of the chain | Bridge | Derived: one instant of the backend a node observed (`Sweep.snapshot`, which is `VaultUnspent.attempt` there by `Sweep.snapshot_attempt`) |
| `creator` | Bridge | Still a model parameter (`Sweep.Cfg`), keyed by outpoint |
| `authorized`, the set `SPN-33` writes | Protocol | Derived: `Sweep.authorized`, the txid of every candidate the node registered, read off its history; rungs past the first are not modelled |
| `Package.validate` is no conjunct of `Kernel.packageAccepted` | Bridge | The kernel is unchanged; in the composed model every assembly of an Escape needs it (`Sweep.assemblyOk`) |

**Positive:** `Exhibits.PackageAncestry.twin_admitted_with_current`, hand-seeded. **Negative:**
`Package.twin_refused_with_plainRead`, the withdrawn read, beside the universal refusals
`Package.unshown_refused` and `Package.unauthorized_ancestor_refused`. On a composed run:
`Exhibits.Sweep.ancestry_moves_before_assembly` refuses at a later read, and
`Exhibits.Sweep.ancestry_moves_before_send` submits after the instant moved, since the send reads no
backend fact.

## 7. Recovery authority

`BtcPolicy.Recovery`, change set `bps-uaer.18`. Newly formalized behaviour: abstract custody and coin lifetime over
`Timelock`, `RefreshAge.ChainView` and the run of `BtcPolicy.Settlement`. No restartable node, no anti-rollback hardware,
no protocol change. **Owner:** `CHN-4`, `CHN-10`, `OPS-23`, `OPS-26` and `SEC-54`. **State projection:**
`Recovery.to_settlement` forgets custody, death, latches and publication and leaves a `Settlement.Execution`. Representation:
`Sweep.Backend` gains `heights` and `mtps`, read only here.

| Layer | Declaration | Reads | Status |
| --- | --- | --- | --- |
| Script-level eligibility | `Recovery.eligible`, `Recovery.eligible_iff`, `Recovery.matured_iff` | The selector, `CHN-10`'s sealed `nSequence`, and each input unspent and past its own BIP68 lock at the instant | Derived from the instant |
| Custody | `Recovery.capable`, `Recovery.incapable_refused`, `Recovery.custody_step` | 2 distinct recovery keys, the descriptor, the network (`OPS-23`) | Supplied input, moved only by the environment |
| Possible | `Recovery.publish_iff`, `Recovery.publish_reads_no_federation`, `Recovery.immature_refused` | The two above | Derived |
| Included | `Recovery.included_origin`, `Recovery.included_respects_lock` | What an inclusion implies | Derived, one direction |
| Inclusion reached | `Recovery.included_within`, `Recovery.included_eventually`, `Recovery.no_inclusion_without_service` | `Progress.Profile` and a `Recovery.Serves` promise | Conditional, with its counterexample |

**Eligibility theorem.** `Recovery.publish_iff` is the answer to "when": eligible at the truth, capable, not yet
confirmed. `Recovery.publish_reads_no_federation` is `OPS-26`'s "no user key, no node quorum, no coordinator, no PIN": the
verdict reads no federation state. `Recovery.lockAge` is BIP68's measure for the next block, `MTP(tip)` less the MTP of the
confirming block's parent; `SPN-46`'s `RefreshAge.age` reads the confirming block and stays its own rule.

**A coin's history.** `Recovery.age_moves_only_by_chain`: every step but a chain move keeps every coin's age and verdict, a
latch, a death and an arming included. `Exhibits.Recovery.lockdown_does_not_restart` runs it. `Recovery.refresh_spends_parents`
and `Recovery.successor_own_history`: a confirmed refresh spends its inputs and its outputs count from its own block.
`Exhibits.Recovery.refresh_starts_own_count` includes `SPN-46`'s age admitting a refresh of a young coin.
A chain move stays free but for `Recovery.lockRespected`, so `Exhibits.Recovery.reorg_makes_coin_young`,
`Exhibits.Recovery.reorg_undoes_inclusion` and `Exhibits.Recovery.reorg_spends_coin` are reachable.

**Death and history.** `Recovery.dead_takes_no_step`, which also refuses copying a dead node's key (`DUR-18`), `Recovery.dead_sticky`, `Recovery.sent_step`, and
`Recovery.history_persists`, which reuses `Settlement.step_keeps_exposure`; `Exhibits.Recovery.death_keeps_record`,
`Exhibits.Recovery.copy_before_death_stays`.

**The classification.** `Recovery.failures` lists a coin's classes from one composed state and `Recovery.mem_failures`
is the exact reading of each:

| Class | Reading | Alone, on a reachable run |
| --- | --- | --- |
| `Failure.normalBlocked` | `Recovery.normalOpen` false: no user signature on some input, or under `t` signers on some input among those with a record, those with a copied key and those open | `Exhibits.Recovery.only_normal_blocked`, `Exhibits.Recovery.normal_blocked_by_user_key` |
| `Failure.fastUnavailable` | No Escape over the coin stands submitted, and no living honest node holds one assembled or passing `Sweep.check` at its read; a conflicted one does not count (`Recovery.conflicted`) | `Exhibits.Recovery.only_fast_unavailable` |
| `Failure.notMature` | `Recovery.matured` false | `Exhibits.Recovery.only_not_mature` |
| `Failure.missingCustody` | `Recovery.capable` false for the Operator | `Exhibits.Recovery.only_missing_custody` |
| `Failure.awaitingInclusion` | A transaction spending the coin is out and unconfirmed | `Exhibits.Recovery.only_awaiting` |

`Exhibits.Recovery.classes_stand_alone` collects the five: every class has a reachable scenario with it alone, so no two are
one. A coin a confirmed transaction spent stands in none (`Recovery.moved_no_failures`). Classes co-occur:
`Exhibits.Recovery.dead_federation`, `Exhibits.EndToEnd.safe_without_progress`. `Recovery.publish_of_clear` ties the two
Recovery classes to the route.

**Limits of the classes.** A class reads one target and one run: at a hot target's `Failure.normalBlocked`, a non-hot target over the same
coin can still read open (`Exhibits.EndToEnd.other_target_other_scenario`), which is `SEC-54`'s per-coin condition and why these classes do not
by themselves say a coin's only exit is Recovery. `Exhibits.Clawback.armed_signs_alike` runs one such target, a claw-back, signed and submitted at armed nodes (section 11). `Failure.normalBlocked` reads the present state; that it stays blocked is not claimed, and
`Recovery.normal_of_inventory` is the only direction proved. `Recovery.openSigner` is this module's reading of who could still
sign, built from what `Kernel.accept`, `DUR-9` and `DUR-11` say; no theorem says a closed signer signs nothing later.
`Failure.fastUnavailable` reads registered Escapes: whether any bounded request exists is section 9's. No theorem decides
operator diligence or hardware reliability: `Step.lose`, `Step.loseBackup` and `Step.copy` are free environment moves.

**Assumptions retained.** A sealed lock of zero is outside: BIP68 lets such a spend confirm with its unconfirmed parent, and
`Recovery.matured` reads confirmed coins alone, while `CHN-4` says "There is no hard floor". Possession is a list, with no keys or signatures behind it. A party reads the truth, not a node's
view. Fee and relay rules on a Recovery spend are outside. An instant's fields stay independent and MTP need not grow, as in
section 8's module and `BtcPolicy.Settlement`. Only spends a party has published are bound by `Recovery.lockRespected`; another
transaction spending a vault coin is external. `Step.latch` is held beside the node, not written into it, so each node still moves by
`Kernel.step` alone. Refresh cadence as a universal claim is not proved: `Exhibits.Recovery.refresh_starts_own_count` is one
history.

**`SEC-54`.** Rows 14, L1, L3, L7 and L8 now name these results and keep the rest as "No theorem carries". `SEC-54`'s
"A possible spend, including Recovery, guarantees neither broadcast nor confirmation" is `Recovery.no_inclusion_without_service`.

## 8. Progress

`BtcPolicy.Progress`, change set `bps-uaer.16`. Newly formalized behaviour plus counterexamples: no
clock repair is chosen, no safety theorem gains a premise on the schedule, and no bound is a
deployment figure. `Progress.Profile` names three environments: `adversarial`, `eventual` and
`bounded B`. Service alone gives no progress, so each theorem below also names what must be enabled
when service comes, and eventual service does not reach a finite expiry
(`Progress.eventual_misses_any_expiry`). `Progress.pRun` plays one schedule over `Lifetime.St`, the
ingress guard of `NCH-13` and the nonce log of `SPN-10` to `SPN-14`, and every section `Lifetime`
names stays `Lifetime.step` (`Progress.op_is_lifetime`). `Progress.driverStep` is `DUR-7`'s deadline
driver, apart from `Kernel.tick` (`Progress.tick_keeps_latch`, `Progress.driver_retires_nothing`).

| Goal | Reached means | Theorem and profile, with its enabling premise | Counterexample |
| --- | --- | --- | --- |
| Local computation | `Progress.Local`, the latch | `Progress.latch_within`, bounded, the comparison at the driver's own sample; `Progress.latch_within_of_read`, bounded, the ratchet having read `T`; `Progress.latch_eventually`, eventual, the comparison stable | `F13`: `Progress.f13_starved`, `Exhibits.Progress.f13_starved_run`, adversarial; `Progress.f13_postponed`, eventual and bounded by the postponement itself; `Exhibits.Progress.alternating_samples_never_latch`, bounded service, every driver sample below `T`, the wall past `T` between them |
| Message receipt | `Progress.Received`, a nonce the guard took | `Progress.received_within`, bounded, `Progress.envelopeFits` | `F3`: `Progress.f3_blackhole`, delivery at `bounded 0`; `Exhibits.Progress.f3_no_arming_run` |
| Arming | `Progress.Armed`, the arm bit | `Progress.armed_within`, bounded, `Progress.deciding` | `F4`: `Progress.f4_no_arming`, `Exhibits.Progress.f4_no_arming_run`, delivery at `bounded 0`; `Exhibits.Progress.f3_outlasts_expiry` |
| Escape submission | `Progress.Submitted`, a broadcast | `Progress.submitted_within`, bounded, `Progress.sendable` | `Exhibits.Progress.send_after_window_closes` |
| Chain inclusion | `Progress.Settled`, a settle pass whose view showed the transaction | `Progress.settled_within`, bounded, `Progress.settleable` | `Exhibits.Progress.submitted_is_not_included` |

Under `adversarial` every goal also has the empty schedule (`Progress.adversarial_starves`).

What is unbounded, and what it takes to bound it:

- `F13`. The delay has no bound under the existing model. The kernel's part of the consequence does, over every schedule from a reachable world:
  `Progress.delayed_node_frozen`, a fire pass on the armed node queues no hot partial, reusing
  `Kernel.no_hot_partial_while_armed`. A positive claim takes
  driver service within a bound, and either the comparison true at the driver's samples or the ratchet
  having read `T`. `DUR-15` says "this set claims none".
- `F3`. The outage grows with the excursion and survives perfect delivery. A positive claim takes the
  high-water within `NCH-12`'s past bound of the stamp (`Progress.envelopeFits`). The guard is modelled
  with no quota.
- `F4`. A Carrier below the latch cannot count a holder for the rest of its life, however its relays
  are scheduled, and `NCH-36` says "retries are bounded by `E` and `D`, never unbounded". New requests are a separate outage:
  `Progress.f4_every_request_refused` holds while the raw sample plus the age bound is at or below the
  latch, and `Progress.f4_log_outage` places the latch arbitrarily far ahead with two excursions. That
  placement needs an expiry signed against the first excursion, which only a hostile coordinator, or
  one sharing the excursion, signs. A positive claim takes the high-water below the expiry
  (`Progress.window_open_below_latch`).

Not modelled: the guard's quota, the outer-stale path's answers, the alternate-signature work,
`SPN-11`'s absent monotonic sample, the log's length and capacity, `API-19`'s `last_deadline_tick`,
machine timing, service rates and block production. A slot is a critical section, not a second. Only
envelope and driver grants read their `Env` from the log; `Grant.op` keeps `Lifetime`'s free `Env`.
`Grant.envelope` is the composition's own route to `Kernel.receipt`: it is not wired into
`Federation.Step`, so a relay here carries no provenance and the federation's theorems do not read
this run. Fast-exit feasibility is section 9; Recovery is section 7.

## 9. Fast-exit feasibility

`BtcPolicy.Feasibility`, change set `bps-uaer.17`. Research and counterexamples over existing rules: no
protocol change, no selection rule, and `F1`, `F2` and `F48` stay open. Base `001de60`. Requirements
read: `DUR-22`, `DUR-23`, `DUR-24`, `WTC-24`, `API-4`, `API-6`, `NCH-10`, `OPR-33`, `OPR-34`, `OPR-35`,
`OPR-39`, `OPR-46`, `CHN-22`, `CHN-34`. Reused: `Sweep.snapshot`, `Sweep.covered`, `Coverage.denominator`,
`Package.validate`, `Witness.maxVsize`.

**The question has three layers, and neither inclusion reverses.**

| Layer | Holds when | Reads |
| --- | --- | --- |
| `Feasibility.Vault.nodeOk` | A node takes the request and passes it at the read | `API-4`, `API-6`, `WTC-24`, `DUR-23`, `DUR-24` |
| `Feasibility.Vault.bounded` | Also inside what any composer and signer are held to | `OPR-35`, `CHN-22` |
| `Feasibility.composeEvery` | The composer as specified builds it | `OPR-33`, `OPR-34`, `OPR-39`, `CHN-21` |

`Feasibility.compose_bounded` is the inclusion from the third to the second, with no unconfirmed
vault-authorized value at the read and each coin's creator outside the mempool.

**Named assumptions.** `Feasibility.Parent.inDomain` is the assumed consensus transaction-size domain, weight at most
4 000 000. `Feasibility.Limits` carries the wire sizes, which this set fixes nowhere per input: 400 bytes per input
per PSBT and the shell are the exhibits' assumptions, not deployment figures. `Feasibility.Vault.retained` reads
`OPR-35`'s "candidate multiplicity" as the number of inventory coins a parent creates. A reading that also
multiplies by rungs only raises the projection, so a refutation stands under it, and the positive
states have parents small enough not to depend on it. `Feasibility.Vault.parentOf` says whether a full
transaction can be obtained, by txid, so coins of one creator share one parent. `Feasibility.feasible_iff_best` additionally takes `Feasibility.CountOnly`,
that the bounds reduce to a count and a per-coin test; `Feasibility.countOnly_of_slack` discharges it where
no additive bound binds first.

**What is proved.** The denominator stays whole: `Feasibility.Vault.denominator_request` measures a request drawn
from a canonical read with agreeing values against all of it. With other Escapes selected,
`Feasibility.base_le_denominator` gives at least the read less `DUR-22`'s excluded outputs, given distinct outpoints
and agreement on the coins they share. Under `CountOnly`, `Feasibility.feasible_iff_best`: a bounded request exists exactly when, for some
count within `N`, the most valuable usable coins of that count less the floor's fee reach the required
share of the whole read. Without it, `Feasibility.Vault.no_request_of_value_bound` is the general refutation, with
`Feasibility.Vault.fragmented_infeasible` and `Feasibility.Vault.unreachable_infeasible` as its two forms. Inside the domain eight
inputs always fit the retention bound (`Feasibility.Vault.eight_inputs_always_retained`). `Feasibility.deep_coin_excluded`:
`WTC-24`'s walk only grows with the inputs, so no selection goes around a coin over the limit. On the
composed sweep, `Feasibility.covered_false_of_value_bound` and `Feasibility.assembly_refused` take the verdict to
a refused assembly, and `Feasibility.no_submission_of_uncovered` to no submission.

| Shape | Feasible | Composer refuses, a request exists | No bounded request |
| --- | --- | --- | --- |
| `F1`, fragments | `Exhibits.Feasibility.fragments_feasible_below`, 620 of 1 213 coins | `Exhibits.Feasibility.dust_stops_composer_only`, 621 dust coins and one input that covers | `Exhibits.Feasibility.fragments_infeasible`, 1 216 equal coins |
| `F1`, large parent | `Exhibits.Feasibility.one_large_parent_composes` | `Exhibits.Feasibility.toxic_node_would_take`, at the node's layer only | `Exhibits.Feasibility.toxic_infeasible`, sixteen equal outputs of one parent |
| `F2` | `Exhibits.Feasibility.shallow_chain_feasible`, 24 ancestors | `Exhibits.Feasibility.prior_spend_composer_refuses`, with `Exhibits.Feasibility.confirmed_only_undercovers` | `Exhibits.Feasibility.deep_chain_infeasible`, a tail of 25 residents, refused at the node |
| `F48` | `Exhibits.Feasibility.f48_moves_the_verdict`, under `ignore` and `verify` | | `Exhibits.Feasibility.f48_moves_the_verdict`, under `refuse`; `Exhibits.Feasibility.missing_parent_infeasible`, no full previous transaction |

Each state in the last column satisfies `Feasibility.Vault.admissible` (`Exhibits.Feasibility.states_admissible`), and each
refutation there quantifies over every request. On a composed run, `Exhibits.Feasibility.feasible_constructed` and
`Exhibits.Feasibility.swept_request_validates` read the swept Escape as a valid request. `Exhibits.Feasibility.armed_no_fast_exit`
runs the other side: both nodes armed and frozen, one registered Escape uncovered, its assembly refused and
nothing submitted. A request over all three coins would pass at that read, so that run is one Escape's failure and
not a state with no request.

**What this shows about the findings.** Dust alone costs an outsider little and stops the composer. It does
not remove every request. Under a count bound there is none exactly when, at every count within `N`, the most
valuable usable coins less the floor's fee fall short of the share (`Feasibility.feasible_iff_best`): value outside
those coins, or a fee that outweighs them. With parents stripped, one consensus-valid parent paying the vault up to
eight times passes the retention bound whatever its size; `F1`'s large parent needs multiplicity, or a wire
that carries it. `Exhibits.Feasibility.vsize_capacity` gives the count at each end of the shapes: 620 inputs at
2-of-3 and 268 at 8-of-15, for one output. `Exhibits.Feasibility.ladder_lowers_capacity` shows the body cap binding
first with a full ladder at the assumed wire sizes. Under `refuse`, no request `OPR-46` strips passes
(`Feasibility.refuse_refuses_composed`), so that reading and the stripped wire cannot both stand.

**Bounded-selection ideas, compared and not chosen.** `Exhibits.Feasibility.selection_ideas_compared`: spending
every coin fails where a prefix works, a prefix fails where largest-first works, and largest-first fails
where a third selection works. Every selection fails on a state with no bounded request, being a request.
`F1`'s candidates remain the finding's to settle. Narrowing the denominator is no candidate:
`Exhibits.Feasibility.omitting_admits_two` lets two input-disjoint Escapes both cover, the case `MAN-9`'s floor
exists to refuse.

**Not modelled.** The primary spend and the pair's policy checks. `CHN-16`'s ladder beyond the PSBT count.
`DUR-26`'s rung selection and `DUR-21`'s check before release. `WTC-26`'s verdict and relay policy, so `OPR-35`'s
vsize bound is read as the composer's and never as the backend's. Coinbase maturity: `Sweep.Backend` carries
none, so a coin `WTC-28` leaves out of the inventory while the read shows it is not a state here. Exact PSBT
framing and base64 expansion. Each state is a backend instant with hand-chosen values; `Sweep.Step.chain` can
move to any of them, `Feasibility.Vault.admissible` does not ask how one was reached, and only
`Exhibits.Feasibility.armed_no_fast_exit` is run through the federation. How
much a depositor must spend to build a state is not a theorem.

## 10. One composed history

`BtcPolicy.Exhibits.EndToEnd`, change set `bps-uaer.18`: one request and one composed model, `Recovery.Execution` over
`Kernel.current`, three honest nodes, threshold 2. Each candidate is computed by `Ingress.check`.

| Stage | Declaration, on the run `coerced` |
| --- | --- |
| Checked ingress | `Exhibits.EndToEnd.coerced_checked`, `Ingress.CheckedTrace` over the run; `Exhibits.EndToEnd.coerced_history` for the verdict; `Exhibits.LedgerSilence.coerced_ledgered` for gate 24 at each acceptance, read from the ledger the run has built |
| Local decision | `Exhibits.EndToEnd.coerced_history`: nodes 1 and 2 armed, the hot spend frozen, the Escape released |
| Distributed authority | The same theorem: `t` distinct signers on every input of the Escape at node 1, delivered over the inventory |
| Permitted submission | The same theorem: coverage, ancestry and possession at node 1's read, the assembly admitted, and the send submitting the Escape's transaction |
| Inclusion | The same theorem: the chain alone shows it confirmed |

`Exhibits.EndToEnd.ordinary_history` is the same request with no duress, to the hot spend's submission.

**What duress can still prevent.** `Exhibits.EndToEnd.duress_withholds`: `Federation.cohort_no_exposed_quorum` on this
run, every premise decided on it: no exposed quorum for the hot spend when a Hold-protected, unextracted cohort leaves fewer than
`t` keys. That is the whole of the positive claim, for one target. **What it cannot:** a node outside the cohort still signs
(`Exhibits.EndToEnd.third_signs_alone`, one signer of the two needed); partials released before it stay out
(`Exhibits.EndToEnd.duress_too_late`, a quorum with both nodes armed); copied keys sign regardless
(`Exhibits.EndToEnd.copied_keys_defeat`); a claw-back is signed at armed nodes by `DUR-36`'s rule, which the model reads (`Exhibits.EndToEnd.other_target_other_scenario`) and runs beside `coerced` (`Exhibits.Clawback.armed_signs_alike`, section 11); a coin past its lock is open to anyone holding two recovery keys, duress or not
(`Exhibits.Recovery.two_keys_gate_on_maturity`). **Escape authority:** section 12 supplies abstract escape-wallet custody beside the same run. The composed steps remain identical under arbitrary custody; Operator-only authority, coercer authority and nobody retaining authority give different destination readings. Actual usable keys and custody completeness remain inputs.

**Safety holds and progress does not.** `Exhibits.EndToEnd.safe_without_progress`: the same request at an instant its Escape
does not cover: both nodes armed, the hot spend frozen with no quorum, nothing submitted, and the coin in three classes.
`Exhibits.EndToEnd.at_the_lock`: at the coin's lock, of this target, this Escape and Recovery, Recovery is the one that stands. `Exhibits.EndToEnd.sent_not_included`: the Escape out and the
chain never moving.

**The Hot ledger and SILENCE on it.** `BtcPolicy.Exhibits.LedgerSilence`, change set `bps-hmxr.2`, base `508083b`. Proof
and representation change: existing modules composed onto this run, no protocol change. Requirements read: `POL-16`, `POL-18`,
`POL-20`, `DUR-1`, `SEC-10`, `DUR-36`. Reused: `FedSilence.lapply`, `Ingress.check` with its `fits` input,
`Admission.fed_bridge`, `FedSilence.fed_silence_adaptive_fresh`. New: `Federation.run`, `Federation.runTrace`,
`Recovery.fedSteps`, `Recovery.fed_record`, `Admission.lfaithful`, `Admission.lrun_faithful`, `Admission.checked_on_ledger`.

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| The run carries its ledgers | `Exhibits.LedgerSilence.ledgered_is_run`, `Exhibits.LedgerSilence.lstate_fed`, `Exhibits.LedgerSilence.coerced_ledgered` | Any schedule from this run's start at which `Admission.lfaithful` holds: forgetting the ledgers of the ledgered replay of its federation steps leaves the run's federation state and trace, so the composed state with its ledgers (`Exhibits.LedgerSilence.LSt`) has the replay as its federation part. The backend, chain, custody and latch parts are the run's own, which no ledger reads. Decided on `coerced` at cap 100: nodes 1 and 2 each end with one row of 55, unexposed |
| Gate 24 read from the run's ledger | `Admission.checked_on_ledger`, in `Exhibits.LedgerSilence.coerced_ledgered` | Each acceptance is `Ingress.check`'s with `fits` set to `Ledger.admits` over that node's ledger as `Ledger.checked` leaves it at that step. Premises: `Ingress.CheckedTrace`, `Admission.lfaithful` |
| `POL-20`'s bound on it | `Exhibits.LedgerSilence.coerced_admission_bound` | `Admission.fed_bridge` at the three honest cuts, `q = 2`, every premise decided on the run. What section 3 leaves to the caller is this fixture's: all three nodes honest, so `q` and the length are `t − c` and `n − c` at `c = 0`; the commitment id is `Ingress.code`, collision-free (`Ingress.code_injective`) |
| SILENCE from its start | `Exhibits.LedgerSilence.silent_from_start` | `FedSilence.fed_silence_adaptive_fresh` at the current values, from this run's start with empty ledgers, every observer, the three manifest nodes as peers |
| SILENCE on `coerced` | `Exhibits.LedgerSilence.coerced_silent` | The observer that replays `coerced`'s federation steps, with PIN 1 duress in one family and ordinary in the other. Equal at the six steps the walk covers, both requests, relays and holder decisions; nodes 1 and 2 armed at `T = 95` in one family and neither in the other |

**Where SILENCE stops on this run.** The walk ends at node 1's first fire pass, past the duress family's `T`; there the families
part (`Exhibits.LedgerSilence.coerced_parts_at_fire`). The Escape's partials, node 1's read, the assembly, the send and the chain
all lie past it, and the backend and chain steps are not federation steps and are never walked. The claw-back is outside the walk
(`Exhibits.LedgerSilence.clawback_outside_walk`): on `Exhibits.Clawback.armedRun` the walk stops at its ingress at 70, inside the
horizon, because `Silence.wfEvent` refuses it. That refusal is needed by the proof: `Silence.NodeInv.noWindow` forbids a window
close on a candidate no selected entry acts on, and `Kernel.clawbackBorn` writes one. Bringing the claw-back inside means restating
that invariant. An observer that reads node 1's arm bit distinguishes the families on this run's prefix
(`Exhibits.LedgerSilence.arm_reader_leaks`) and is not a `FedSilence.Observer`. SILENCE's Outside and Environment premises of
section 4 stay as they are.

**What the ledger changes.** `Exhibits.LedgerSilence.too_late_needs_budget`: `tooLate` takes a second request over the same
transaction under a new commitment while the first reservation of 55 stands. Each commitment is booked in full (`POL-16`), so at
cap 100 gate 24 refuses it and the schedule is not `Admission.lfaithful`. The ledgered run stages that request, and
`Exhibits.EndToEnd.duress_too_late`'s outcome still holds there: both nodes armed, the hot spend's quorum in the inventory. At cap
110 the history is the ledgered run as written. The other histories of this section are faithful at cap 100
(`Exhibits.LedgerSilence.others_faithful`).

**What the history leaves beside it.** Time in this run is a set of sampled environments, and no service profile is applied to it.
`DUR-21`'s check and the ladder are outside, as in section 9. No bytes or timing beyond what `FedSilence.FObs` carries.

## 11. A claw-back run

`Kernel.Event.clawback`, `Ingress.checkClawback` and `BtcPolicy.Exhibits.Clawback`, change set `bps-hmxr.1`. Newly formalized
behaviour of existing rules: no protocol change. Base `c0791e0`. Requirements read: `SPN-50`, `SPN-51`, `DUR-7`, `DUR-11`, `DUR-36`,
`CHN-35`, `SPN-33`, `WTC-24`. Reused: `Kernel.born`, `Kernel.due`, `Kernel.releaseAuthorized`, `Classification.validateRequestShape`,
`Evaluate.evaluate`, and the model of section 10.

**The transition.** `Kernel.clawback` reads the Lockdown latch, the resident ids, the node's id and `combine_slack_secs`, and adds
`Kernel.clawbackBorn`'s one candidate: not hot, no pair, born open, its window opening at the accepting sample (`Clocks.Wall.openAt`) and
closing at the earlier of its expiry and that sample plus `combine_slack_secs`. It writes no Carrier and no overlay field
(`Kernel.clawback_records_nothing`) and reads none (`Kernel.clawback_reads_no_arm`). Every existing theorem proves with the event
in the alphabet. Statements that changed: `Kernel.OpenProvenance`, an induction invariant, reads hot residents only, because a
claw-back is open with no holder decision, and `Kernel.hot_release_provenance` is unchanged; `Federation.cand_origin` gains the
claw-back as an origin; `Ingress.CheckedTrace` also asks every claw-back to be `Ingress.checkClawback`'s candidate, which is
escape-class (`Ingress.checkClawback_classed`), so `Ingress.hot_binding` keeps its statement; `Progress.step_latW_request` and
`Progress.step_latW_other` count the claw-back among the requests a latch refuses, and so does `Recovery.baseOk`;
`EndToEnd.withholds_on` takes the claw-back requests it checks.

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| An armed node releases a claw-back as an idle one does | `Kernel.clawback_release_arm_blind` | `r.entryTarget = .escapeRole`; one candidate with no pair; equal time ratchet, `hold_secs` and `combine_slack_secs`, the overlay arbitrary |
| The same, run | `Exhibits.Clawback.armed_signs_alike` | Nodes 1 and 2 armed on `coerced`'s prefix, the claw-back taken at 70, before their `T` at 95, and the same steps on idle nodes: equal claw-back rows, both submitted |
| A locked-down node refuses it | `Kernel.clawback_refused_locked` | Any node with the latch set: the node is unchanged |
| A latched node takes none, run | `Exhibits.Clawback.latched_refuses_clawback` | Section 10's latch beside the node: the composed run admits no claw-back step there (`Recovery.baseOk`); node 3 alone signs, one of two |
| Duress still withholds the hot spend | `Exhibits.Clawback.withholds_beside_clawback` | `EndToEnd.withholds_on`, its premises decided on the run with the claw-back |
| A resident or confirmed claw-back stops the Escape at ancestry, not coverage | `Exhibits.Clawback.resident_clawback_defeats_escape` | The claw-back taken and submitted at 70, before `T` at 95; node 1's read at the Escape's assembly past `T`; the read without it, never resident or evicted before node 1's step at 90, admits the Escape; a chain move carries no clock, so "before `T`" is its place in the schedule |

**Not modelled.** `WTC-25`'s replacement test at the claw-back's ingress, and the two expiry predicates and gates before
verification, which are the request's. The claw-back's relay to peers: each node takes it by its own step. `DUR-21`'s check before
release, so the Escape's partials are released whatever the chain shows and the defeat is read at assembly, where `Sweep`'s guard
sits. That guard reads Escapes only, so the claw-back's own assembly, like a hot spend's, reads no backend: `WTC-24` is not checked
on it, and an assembly over a coin the instant does not hold is not refused. SILENCE across the ingress: `Silence.wfEvent` rejects the
event and the walk stops there, and section 10 says why. A refresh's ingress stays outside the kernel.

**Not decided by the set.** A claw-back byte-identical to a resident pair's Escape, under that pair's expiry, has the Escape's
`CHN-24` commitment: `CHN-35` and the Escape's rules both fix `nLockTime = 0` and `nSequence = 0xfffffffd`. `SPN-50` lists an
idempotent replay, and no requirement says what a node does with a claw-back naming a resident Escape's commitment.
`Kernel.clawback` registers nothing new on any resident id; the model gives the request no response, and that is no answer to the
question.

## 12. Escape-wallet custody beside the run

`BtcPolicy.EscapeCustody` and `BtcPolicy.Exhibits.EscapeCustody`, change set `bps-hmxr.3`, base `1b042b76`.
Newly formalized behaviour: the abstract custody input for `SEC-54` rows 9, 10 and L6. Representation change:
a wrapper retains the entire `Recovery.St` and adds escape custody; no protocol, ADR decision or guard value changes.
`ADR-0023` decisions 3 and 12 are retained. Reused: `Recovery.Execution`, `Recovery.admits`, `Recovery.apply`,
`Recovery.St.sent`, the checked `EndToEnd.coerced` history, and `Clawback.armedRun` with its checked candidate.

**Authority and its domain.** A supplied `EscapeCustody.Wallet` names a `k`-of-`m` wallet's distinct key ids;
`EscapeCustody.Wallet.Valid` requires a positive threshold no larger than that distinct list. A holder is any natural-number
identity: 0 is the Operator, each other identity an adversarial party or coalition. Keys are usable access, backups included;
key bytes and how access became usable are not represented. `EscapeCustody.heldKeys` filters by the wallet and the holder's
permanent losses and removes duplicates. `EscapeCustody.capable_iff`, for any wallet, custody and holder, reads capability as
`k` no greater than that distinct count. The numerical complement formula `m − k` is not proved here.
No bound on holders is imposed, and access of different holders is not pooled unless supplied under one coalition identity.

**Environment and projection.** Initial custody is free. Only `EscapeCustody.Step.copy` and `EscapeCustody.Step.lose` move it;
a copy supplies usable access from outside the model, while a loss means all of that holder's usable copies and backups are
permanently gone. `EscapeCustody.loss_sticky` preserves each recorded loss across every step;
`EscapeCustody.lost_unusable` excludes that key from the holder's count. A later copy attempt of that key is refused.
`EscapeCustody.environment_keeps_base` leaves the entire old state unchanged under either environment step.
`EscapeCustody.to_recovery` projects every wrapper execution to a `Recovery.Execution` after erasing escape-custody steps.
`EscapeCustody.record_projection` gives equality of the projected trace and state to the old run over the retained steps,
for arbitrary rules, initial states, histories and schedules. It derives no old guard premise.

**What a node cannot read.** `EscapeCustody.node_independent`, for arbitrary configuration, rules, honest ids, wrapper state,
history, replacement custody and composed step, gives the identical admission verdict and next composed state after replacing
custody, and preserves the original custody through the step. Its observation boundary is the entire composed state and step
verdict, not serialized responses or timing. No honest node or backend step can see the live/dead-wallet distinction within this
model. This does not establish SILENCE across claw-back ingress; section 10's horizon and section 11's obstruction remain.

**Outcomes and arrival.** `EscapeCustody.Reads` distinguishes Operator-only capability (Denial's authority component), some
adversarial holder's capability (Theft, even if the Operator also retains authority), and no capable holder at all (Loss).
Loss quantifies over every holder identity, and requires that the supplied custody account includes every usable backup and
holder. Denial additionally assumes the circumstance "later than wanted"; the model does not derive wishes or delay.
`EscapeCustody.Delivered` requires the transaction in the composed run's submitted record and confirmed on its supplied chain,
plus the custody reading at that instant. It does not itself check a destination: the route's checked escape classification
and the identification of that destination with the supplied wallet are separate premises. Abstract key access is not a proof
of cryptographic spending, and inclusion is never caused by custody or a node step.

| Exhibit | What is inhabited and what is assumed |
| --- | --- |
| `Exhibits.EscapeCustody.routes_project` with `Exhibits.EscapeCustody.execution` | Each of the three custody prefixes, followed by either the existing coerced sweep or armed claw-back with explicit inclusion, is legal and yields an execution. The projected trace and state equal the original run; custody stays at its prefix's value through inclusion |
| `Exhibits.EscapeCustody.operator_destinations` | Both checked routes, supplied Operator-only 2-of-3 authority, no other holder, explicit confirmation; Denial's timing circumstance assumed |
| `Exhibits.EscapeCustody.coercer_destinations` | The same routes, one coercer copying two distinct keys, the Operator losing those keys, explicit confirmation; Theft at the destination |
| `Exhibits.EscapeCustody.lost_destinations` | The same routes after the Operator permanently loses two keys and all their usable backups, nobody else holding authority, explicit confirmation; Loss at the destination |
| `Exhibits.EscapeCustody.stolen_theft` | The Operator's loss does not imply Loss: a coercer still retains authority; `EscapeCustody.retained_not_loss` gives the general obstruction for any retained capable holder |
| `Exhibits.EscapeCustody.duplicates_and_permanent_loss` | The wallet threshold is valid; two copies of one key fail it, and a copy after permanent loss is refused and cannot restore authority |
| `Exhibits.EscapeCustody.sent_is_not_arrival` | The same legal sweep stopped before the chain move is submitted and unconfirmed; custody supplies no inclusion guarantee |

**Negative controls.** The duplicate-key count and permanent-loss traps are planted in the existing workflow inventory.
The full workflow replay also previews the counts moved by the new current-rule exhibits before they are committed.

**Exact exclusions.** Descriptor policies other than `k`-of-`m`, non-key spending conditions, actual keys and signatures,
wallet signing and relay, physical custody and its drills (`OPS-60`, `OPS-61`), proof that every holder/backup is accounted for,
future physical key retention, and inclusion service. The same chain instants and synthetic requests are retained from the
previous histories. No runtime or hardware experiment is claimed. The claw-back collision question in section 11 stays open;
the ledger's accounting result and the SILENCE horizon in section 10, and the immature-coinbase text, are unchanged.

## Counterexamples that must stay counterexamples

Later work adds beside these and changes no definition that would make one stop proving. A composed
model that cannot reproduce one records the obstruction beside it.

| Declaration | What it keeps false |
| --- | --- |
| `Exhibits.EarlierRelease.later_freeze_preserves_prior_quorum`, `Exhibits.EarlierRelease.cutoff_is_strictly_weaker` | That a cutoff-only premise, a later freeze or a new commitment id bounds earlier authority |
| `Exhibits.ReleaseKernel.exposure_key_exhibit`, `Exhibits.ReleaseKernel.no_resident_release_does_not_mean_safe` | That a commitment-keyed or node-local history bounds authority |
| `Exhibits.ReleaseKernel.exposure_without_receivePartial_is_not_held`, `Exhibits.EarlierRelease.exposure_without_possession` | That exposed authority is possession |
| `Authority.input_zero_insufficient`, `Exhibits.EarlierRelease.possession_without_complete_authorization` | That a threshold at input 0 authorizes a transaction with more inputs |
| `Exhibits.EarlierRelease.deleted_candidate_retains_authority` | That deleting a candidate removes the authority it released |
| `Exhibits.Provenance.holder_bypass_releases_without_provenance` | That a release with no holder decision meets the provenance property |
| `Ledger.rerun_exceeds_cap`, `Ledger.f61_per_spend_conclusion_false` | The withdrawn re-test and the per-spend reading |
| `Exhibits.HotLedger.adr0014_refutes_completion_bound`, `Exhibits.HotLedger.f63_exposure_outlives_the_charges` | That admission accounting bounds completion or later authority |
| The negative SILENCE exhibits of section 4 | That each leak, or a run without the dropped premise, stays silent |
| `Exhibits.Cohort.matured_hold_releases`, `Exhibits.Cohort.undelivered_cohort_releases`, `Exhibits.Cohort.extracted_member_signs`, `Exhibits.Cohort.hold_unchecked_releases` | That a cohort blocks quorum without its timing, its count, its unextracted keys or the HotClock check |
| `Exhibits.late_selection_admits_both`, `Exhibits.cross_node_admits_both`, `Exhibits.Sweep.different_selected_sets` | That the single-sweep bound is federation-wide |
| `Exhibits.Sweep.insufficient_possession` | That the kernel's package test, read at input 0, is possession on every input |
| `Exhibits.Sweep.ancestry_moves_before_send` | That an ancestry check passed at assembly still holds at the send |
| `Package.twin_refused_with_plainRead` | That a plain read admits a replacement |
| `Exhibits.Settlement.mempool_sighting_evicted_with_withdrawn`, `Exhibits.Settlement.reorg_after_settlement_with_withdrawn` | That defeat read off the defeating transaction's presence survives its eviction or a reorganization |
| `Exhibits.Settlement.mempool_settlement_refunds_with_withdrawn` | That a mempool-only settlement may refund a reservation |
| `Exhibits.Settlement.late_confirmed_deposit` | That coverage checked at an assembly covers a deposit confirmed before the send |
| `Exhibits.Ingress.collision_breaks_binding` | That checking each request separates a spend's message from an Escape's without a collision-free identity |
| `Exhibits.Lifetime.preflight_race_without_marker`, `Exhibits.Lifetime.release_before_hold_admits_refresh` | That subordination read from the pending log alone, or a marker released before the registration hold, keeps a refresh off the Escape's input during a spend's preflight |
| `Exhibits.Lifetime.release_kept_at_refused_registration`, `Exhibits.Lifetime.unwind_by_commitment_drops_earlier_charge` | That a refused registration may keep its check's release, or unwind by commitment, and leave every charge in place |
| `Exhibits.Admission.retry_not_fresh`, `Exhibits.Admission.refunded_not_counted`, `Exhibits.Admission.backward_clock_uncounts` | That an admitted acceptance inside a node's interval is counted at its cut whether or not it placed the reservation, the reservation was refunded, or a later sample passed the cut's |
| `Exhibits.Admission.collision_splits_amount` | That checking every acceptance gives one amount per commitment without a collision-free commitment id |
| `Progress.f13_starved`, `Exhibits.Progress.f13_starved_run`, `Progress.f13_postponed` | That the delay before Lockdown at `T` has a bound, under an unfair lock or under eventual service |
| `Exhibits.Progress.alternating_samples_never_latch` | That bounded driver service latches without the comparison holding at the driver's samples |
| `Progress.f3_blackhole`, `Exhibits.Progress.f3_no_arming_run`, `Exhibits.Progress.f3_outlasts_expiry` | That a scheduling premise repairs the freshness outage |
| `Progress.f4_no_arming`, `Exhibits.Progress.f4_no_arming_run`, `Progress.f4_log_outage` | That a scheduling premise repairs an unrelated high-water latch |
| `Progress.eventual_misses_any_expiry`, `Progress.service_without_stable_enabling` | That eventual service gives delivery before a finite expiry, or that recurring service meets recurring enabling |
| `Exhibits.Feasibility.fragments_infeasible`, `Exhibits.Feasibility.toxic_infeasible`, `Exhibits.Feasibility.deep_chain_infeasible`, `Exhibits.Feasibility.missing_parent_infeasible` | That a bounded request covering enough value always exists |
| `Exhibits.Feasibility.dust_stops_composer_only`, `Exhibits.Feasibility.prior_spend_composer_refuses` | That the composer's refusal means no request exists |
| `Exhibits.Feasibility.omitting_admits_two` | That dropping a coin from the denominator is a harmless repair |
| `Exhibits.Recovery.before_maturity_refused` | That a Recovery spend is possible before a coin's lock has passed, or with the sequence that disables it |
| `Exhibits.Recovery.missing_custody_refused` | That a mature coin is enough without 2 recovery keys, the descriptor and the network |
| `Exhibits.Recovery.lockdown_does_not_restart`, `Exhibits.Recovery.refresh_starts_own_count` | That Lockdown restarts a coin's lock, or that a refresh's output inherits its parent's age |
| `Exhibits.Recovery.reorg_makes_coin_young`, `Exhibits.Recovery.reorg_undoes_inclusion`, `Exhibits.Recovery.reorg_spends_coin` | That maturity or inclusion, once shown, is final |
| `Exhibits.Recovery.classes_stand_alone` | That two of the five failure classes are one |
| `Exhibits.EndToEnd.duress_too_late`, `Exhibits.EndToEnd.copied_keys_defeat`, `Exhibits.EndToEnd.third_signs_alone` | That arming at every node prevents a quorum, or stops every signer |
| `Exhibits.Recovery.submission_outlives_sender`, `Exhibits.Recovery.copy_before_death_stays` | That a sender's death recalls its submission, or that a dead node's key can be copied after |
| `Exhibits.EndToEnd.safe_without_progress`, `Exhibits.EndToEnd.sent_not_included`, `Recovery.no_inclusion_without_service` | That safety carries progress, or that a possible spend is an included one |
| `Exhibits.LedgerSilence.too_late_needs_budget` | That a history built without the Hot ledger is one gate 24 admits |

## Proposed proofs and their non-vacuity examples

| Proposed result | Premise it takes over | Non-vacuity example it owes |
| --- | --- | --- |
| Honest projection is a `Kernel.Execution`, proved as `Federation.project_execution` | `hx` | `Exhibits.Composition.ordinary_run`, with `Exhibits.Composition.forged_relay_refused` on the other side |
| Derived `Kernel.HonestExposureProvenance`, proved as `Federation.honest_exposure_provenance` | `honestExposure`, honest rows | `Exhibits.Composition.authorized_provenance`, a run with nonempty honest target rows, which `Exhibits.Provenance.repeated_exposure_has_no_quorum` lacks |
| Linked earlier-release history, proved as `Exhibits.EarlierRelease.linked_preserves_prior_quorum` | The assembled `Exhibits.EarlierRelease.inventory` | That history, or the recorded obstruction instead of a proof |
| Hold-protected cohort, proved as `Federation.cohort_no_exposed_quorum` | `noNormal` and `bound`, for one target | `Exhibits.Cohort.cohort_blocks_quorum`, an earlier normal opening the Hold blocks, with a failing sibling per condition |
| Per-input authorization, proved as `Authority.normal_iff`, with `Authority.exposed_refines` and `Authority.held_refines` on one input | One input, one rung | `Exhibits.EveryInput.different_subsets_authorize`, hand-seeded; `Exhibits.EarlierRelease.linked_authorization`, on a composed run |
| Checked ingress, proved as `Ingress.accepted_validates`, `Ingress.one_amount_per_commitment` and `Ingress.hot_binding` | `accept` inputs, `hamt` at the candidates, the non-hot exclusion | `Exhibits.Ingress.checked_pair` and `Exhibits.Ingress.copies_reserve_alike`; `Exhibits.Ingress.checked_binding`, a run with honest rows of both classes; `Exhibits.Ingress.malformed_refused`, `Exhibits.Ingress.final_rung_refuses_group` and `Exhibits.Ingress.staged_duress_opens_nothing` |
| Ingress lifetime seams, proved as `Lifetime.refresh_subordinated_in_preflight`, `Lifetime.hold_logs_spend`, `Lifetime.hold_refusal_keeps_charges` and `Lifetime.hold_admitted_charges` | The registration hold as one transition, now named with the other sections in `Lifetime.Section.frame` (`Lifetime.step_frame`). Premises kept: `Lifetime.Subordination.pendingAndMarker` for the subordination result; an admitted, fresh pair and `Kernel.PendingSource.record` for the handoff; `Ledger.Release.acceptedAdmission` for the refusal results | `Exhibits.Lifetime.preflight_race_subordinated`, `Exhibits.Lifetime.panic_exit_releases`, `Exhibits.Lifetime.marker_hands_off` and `Exhibits.Lifetime.registration_refusals_keep_charges`; failing: `Exhibits.Lifetime.stuck_marker_subordinates`, `Exhibits.Lifetime.preflight_race_without_marker`, `Exhibits.Lifetime.release_before_hold_admits_refresh`, `Exhibits.Lifetime.release_kept_at_refused_registration` and `Exhibits.Lifetime.unwind_by_commitment_drops_earlier_charge` |
| Composed sweep, proved as `Sweep.assembled_of_packageOk`, `Sweep.submitted_in_order` and `Sweep.single_sweep_needs_common_floor`, with `Sweep.lift_unassembled` | `h₁`, `h₂`, `snap`, `mem`, `authorized`, the `Package.validate` link. Premises kept: `hpct`, `hS`, `hf₁`, `hf₂`, `hconserve`; the re-authorization before the send (`Kernel.Reauth`) for the order | `Exhibits.Sweep.successful_sweep`; failing: `Exhibits.Sweep.armed_without_eligible_escape`, `Exhibits.Sweep.insufficient_possession`, `Exhibits.Sweep.inadmissible_beside_admissible`, `Exhibits.Sweep.ancestry_moves_before_assembly`, `Exhibits.Sweep.ancestry_moves_before_send`, `Exhibits.Sweep.different_selected_sets` and `Exhibits.Sweep.stale_assembly_not_sent` |
| Chain observation in the sweep, proved as `Settlement.settlement_shown`, `Settlement.settlement_refunds_nothing`, `Settlement.exposure_persists` and `Settlement.defeat_persists`, with `Settlement.to_sweep` | The kernel's chain view at each step, now read off the acting node's latest observation (`Settlement.readOk`), an instant the truth has been (`Settlement.observed_was_truth`). Premises kept: repaired registration, the terminal flag, an honest node and the id resident throughout, for `Settlement.defeat_persists`; `Ledger.Settlement.retainOnMempool` and `Ledger.Release.acceptedAdmission` for the refund result; no inclusion or chain-progress premise, since no theorem concludes a confirmation | `Exhibits.Settlement.successful_sweep_observed`, `Exhibits.Settlement.mempool_sighting_evicted`, `Exhibits.Settlement.reorg_after_settlement`, `Exhibits.Settlement.reorg_keeps_exposure`; failing: `Exhibits.Settlement.conflicting_confirmed_spend`, `Exhibits.Settlement.late_confirmed_deposit`, and the three withdrawn runs listed above |
| Federation SILENCE under one fixed schedule, proved as `FedSilence.fed_silence` and `FedSilence.fed_silence_fresh`, over ledgered runs that are federation executions (`FedSilence.lrun_execution`) | The shared trace's peer relays and partials, produced by the composed run from a `Federation.Fresh` start. Premises kept: the six rule and marker values, `FedSilence.FCoupled` and `FedSilence.FInv` (discharged at `Federation.Fresh` with the sweep flags clear), the stop at `Silence.wfEvent`, and a schedule fixed in advance | `Exhibits.FedSilence.fed_run_silent`, 18 of 19 steps with relays and partials delivered and both nodes armed in one family, and `Exhibits.FedSilence.fed_horizon_is_where_the_runs_part`; failing: the five federation leaks of section 4 |
| Federation SILENCE against an adaptive observer, proved as `FedSilence.fed_silence_adaptive` and `FedSilence.fed_silence_adaptive_fresh`, with `FedSilence.awalk_walk` | The schedule fixed in advance: each run's next step is picked by one `FedSilence.Observer` from the observations that run has emitted, a function of that history alone by its type. Premises kept: those of the fixed-schedule row | `Exhibits.FedSilence.adaptive_run_silent`, an observer that branches on the partial inventory and selects the 18-step walk of `Exhibits.FedSilence.fed_run_silent`; failing: `Exhibits.FedSilence.hidden_state_reader_leaks` |
| Federation SILENCE per destination, proved as `FedSilence.fed_silence` and its siblings over `FedSilence.FObs` with addressed and delivered frames (`FedSilence.sent`, `FedSilence.received`), and `FedSilence.frame_preimage_length` with `Envelope.preimage_length` | That a peer message's destinations are an environment input. Premises kept: those of the fixed-schedule row, and one manifest peer list in both runs. Not derived: a payload's length or bytes, the JSON envelope, randomized nonces and signatures, transmission attempts | `Exhibits.FedSilence.fed_frames_per_destination`, the 18-step walk addressing every relay and partial to both other peers, node 3 included, and `Exhibits.FedSilence.fed_refund_run_silent`; failing: `Exhibits.FedSilence.fed_duress_route_leaks`, `Exhibits.FedSilence.fed_duress_refund_leaks`, `Exhibits.FedSilence.fed_horizon_frames`, `Exhibits.FedSilence.equal_frames_unequal_bytes` |
| Federation admission, proved as `Admission.fed_bridge`, with `Admission.led_le_cap`, `Admission.one_amount` and `Admission.cohort_count` | `hinv`, `hamt`, `hcohort`, at the honest nodes' cuts of a ledgered run. Premises kept: `hnd`, `hval`, `hs`, `hr`, empty start ledgers, `Ingress.CheckedTrace`, a collision-free commitment id, `hclock`, and `q` distinct honest nodes at which each spend is `Admission.Counted` | `Exhibits.Admission.admission_bound_derived`; failing: `Exhibits.Admission.collision_splits_amount`, `Exhibits.Admission.seeded_ledger_breaks_premises`, `Exhibits.Admission.refunded_not_counted`, `Exhibits.Admission.retry_not_fresh`, `Exhibits.Admission.backward_clock_uncounts` |
| Progress under named profiles, proved as `Progress.latch_within_of_read`, `Progress.latch_within`, `Progress.received_within`, `Progress.armed_within`, `Progress.submitted_within` and `Progress.settled_within`, with `Progress.delayed_node_frozen` for the hot partial | None taken over: each takes a service profile and an enabling premise, both new and both named. Safety results take neither | `Exhibits.Progress.goals_are_separate`, `Exhibits.Progress.bounded_service_latches`, `Exhibits.Progress.received_and_armed_inhabited`, `Exhibits.Progress.submitted_inhabited`, `Exhibits.Progress.settled_inhabited`, `Exhibits.Progress.read_past_survives_backward_wall`; failing: section 8's counterexamples |
| Fast-exit feasibility, proved as `Feasibility.feasible_iff_best`, `Feasibility.compose_bounded` and `Feasibility.Vault.no_request_of_value_bound`, with `Feasibility.no_submission_of_uncovered` | Coverage and ancestry verdicts at each read, now reached from named size and topology assumptions | `Exhibits.Feasibility.feasible_constructed` beside a state with no bounded request for each of `F1`, `F2` and `F48` |
| Recovery composition, proved as `Recovery.publish_iff`, `Recovery.included_origin` and `Recovery.age_moves_only_by_chain`, with `Recovery.mem_failures` | Each coin's maturity, now read from its own chain history. Premises kept: custody, a supplied input; the descriptor and network (`OPS-23`); inclusion, an environment move | `Exhibits.Recovery.mature_with_custody_included`, beside `Exhibits.Recovery.before_maturity_refused` and `Exhibits.Recovery.missing_custody_refused` |
