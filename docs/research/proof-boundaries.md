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
| `honestExposure`, no honest non-hot row shares the message | Bridge | A premise of the derivation too, as `Federation.HotBinding`. For the input-0 message of an admissible hot-class member, over `Ingress.CheckedTrace`, it is `Ingress.hot_binding`, which takes a collision-free transaction identity (Outside); `Ingress.no_exposed_quorum` takes those two premises in its place for a checked spend. Over `RungIngress.CheckedTrace`, whose checked ingress registers the Escape's rungs, it is `RungIngress.hot_binding`, rung rows included, with `RungIngress.no_exposed_quorum`; given otherwise |
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
samples are unconstrained. The event alphabet includes a claw-back's post-check registration
(`Kernel.Event.clawback`), answered by `Silence.respond` from `ClawbackIngress.verdict`: Lockdown
first, a resident pair's id second, otherwise `Accepted` by the commitment id with the instants
`Silence.clawTarget` records. `Silence.respond_clawback_pub` and
`Silence.respond_clawback_arm_blind` show that answer reads no arm state, `Silence.clawback_pub`
couples the registration, and `Silence.inv_clawback` carries `Silence.NodeInv` through it.

**What changed.** Before `bps-9oab.2`, `Silence.wfEvent` refused every claw-back, because
`Silence.NodeInv.noWindow` forbade a window close on any candidate no selected entry acts on. The
clause now admits an unpaired candidate that is not hot, which is what `Kernel.clawbackBorn` births,
and the old clause implies it. The earlier walks are kept as `Silence.obsPairPre`,
`FedSilence.walkPre` and `FedSilence.awalkPre`; each is a prefix of the expanded walk
(`Silence.obsPairPre_prefix`, `FedSilence.walkPre_prefix`, `FedSilence.awalkPre_prefix`), so the
earlier relation still holds under the same premises (`Silence.silence_pre`,
`FedSilence.fed_silence_pre`, `FedSilence.fed_silence_adaptive_pre`), and on a trace with no claw-back
the two single-node walks are one (`Silence.obsPairPre_eq`). On a schedule with no handler request step the
handler's walks are `FedSilence.walk` and `FedSilence.awalk` (`ClawHandler.hwalk_steps`,
`ClawHandler.hawalk_lift`).

**Excluded.** Every other node. The docstring of `BtcPolicy.Silence` names what `Silence.Obs` omits.

| Premise | Class | Status |
| --- | --- | --- |
| The six rule and marker values | Protocol | Discharged at the current values by `Exhibits.TwoRun.silence_with_current` |
| `Silence.Coupled`, `Silence.NodeInv` | Protocol | Discharged by `Silence.silence_initial` for its one system taken twice, under its own `hi` and `hs`; given otherwise |
| One shared trace, with peer relays held equal | Bridge | Under one fixed exogenous schedule, discharged by `FedSilence.fed_silence` and `FedSilence.fed_silence_fresh`: the inventories, equal at the initial states, stay equal in both runs, and from a `Federation.Fresh` start the relays and partials a node receives come from the composed run. Against an observer that picks each step from its own run's observations, discharged by `FedSilence.fed_silence_adaptive` and `FedSilence.fed_silence_adaptive_fresh`. Each step's messages are compared per destination, by shape (`FedSilence.FObs`); no theorem gives their bytes, and `FedSilence.frame_preimage_length` gives an envelope preimage's length only from its payload's |
| The stop at `Silence.wfEvent` | Bridge | A pair's request shape. Under the entry target as it stands every claw-back is admitted (`Silence.wfEvent_clawback_escapeRole`), so a claw-back ends the walk only at admission or the horizon; under the withdrawn `EntryTarget.idAlone` a claw-back under a selected id stays outside. The earlier stop at every claw-back is `Exhibits.LedgerSilence.clawback_outside_walk`, against `FedSilence.walkPre` |
| The claw-back handler's retained-replay log | Bridge | In `ClawHandler.hwalk`, which adds the handler's request step to `FedSilence.walk` with the same guard. Three transitions: a retained key replays the stored response and changes no state (`ClawHandler.replay_unchanged`); otherwise fresh evaluation is the composed step on `Kernel.Event.clawback` (`ClawHandler.fresh_projection`), whose refusal retains nothing and whose acceptance retains the request's key with the commitment's first `Accepted`. Lockdown precedes the lookup (`ClawHandler.lockdown_precedes_replay`); the key ignores the nonce (`ClawHandler.key_nonce`). The log is structured; for every encoder its lookup and retention are `ClawbackIngress.lookup`'s and `ClawbackIngress.retain`'s on the encoded log (`ClawHandler.lookup_encode`, `ClawHandler.retain_encode`). `ClawHandler.hfed_silence`, `ClawHandler.hfed_silence_fresh`, `ClawHandler.hfed_silence_adaptive` and `ClawHandler.hfed_silence_adaptive_fresh` carry the relation, with equal logs, or any one log for both runs, and the premises of the `FedSilence` forms; no response equality is assumed. Outside: the checks before the lookup, nonce admission, log expiry, cacheable evaluation refusals, the relay of the request and its re-relay on replay, and serialized bytes |
| `SEC-10`'s "release-history premise" and "digest premise" | Outside | Retained |
| A coordinator honest until the wrench (`SEC-10`) | Environment | Retained |
| `DUR-1`'s "no record of either PIN from any source" | Environment | Retained |

**Positive:** `Exhibits.TwoRun.silence_on_armTrace`, whose prefix ends at the arm;
`Exhibits.LedgerSilence.coerced_silent`, the end-to-end run of section 10 against an observer;
`Exhibits.ClawSilence.clawback_inside_walk`, the claw-back at 70 on the armed and idle families
through release, a backward sample, a delayed partial, the package check and the send, and
`Exhibits.ClawSilence.collision_both_families`, the paired-id refusal in both families with the pair
kept. `Exhibits.ClawHandler.handler_inside_walk` runs the handler's request step on the same
families: a retry under another nonce answers the stored `Accepted`, a changed-bytes request at the same
commitment misses the lookup and is evaluated afresh, and the claw-back's partial is delivered late,
twice and to one node only, through the package check and the send. `Exhibits.ClawHandler.replay_after_prune`
replays a key the log still holds after the candidate was pruned, without recreating it; log expiry is not
modelled. `Exhibits.ClawSilence.late_clawback_stops` is a claw-back past `T`, where the walk stops at the
horizon.
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
| `Package.validate` is no conjunct of `Kernel.packageAccepted` | Bridge | The kernel is unchanged; in the composed model every assembly of an Escape needs it (`Sweep.assemblyOk`), and on section 17's refined run every assembly of every class, as a replacement of the resident `Assembly.target` derives (`Assembly.guardOk`) |

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
`DUR-26`'s rung selection and `DUR-21`'s check before release, which section 13 adds on a refined run. `WTC-26`'s verdict and relay policy, so `OPR-35`'s
vsize bound is read as the composer's and never as the backend's. Coinbase maturity: `Sweep.Backend` carries
none, so a coin `WTC-28` leaves out of the inventory while the read shows it is not a state here; section 15 adds it
beside the backend, and its composer reduces to this one when nothing is left out. Exact PSBT
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
all lie past it, and the backend and chain steps are not federation steps and are never walked. The claw-back was outside the
walk as it stood before `bps-9oab.2` (`Exhibits.LedgerSilence.clawback_outside_walk`, now stated against `FedSilence.walkPre`):
the walk stopped at its ingress at 70, inside the horizon, because `Silence.NodeInv.noWindow` then forbade the window close
`Kernel.clawbackBorn` writes. With that clause restated (section 4), the claw-back is inside the walk
(`Exhibits.ClawSilence.clawback_inside_walk`). An observer that reads node 1's arm bit distinguishes the families on this run's prefix
(`Exhibits.LedgerSilence.arm_reader_leaks`) and is not a `FedSilence.Observer`. SILENCE's Outside and Environment premises of
section 4 stay as they are.

**What the ledger changes.** `Exhibits.LedgerSilence.too_late_needs_budget`: `tooLate` takes a second request over the same
transaction under a new commitment while the first reservation of 55 stands. Each commitment is booked in full (`POL-16`), so at
cap 100 gate 24 refuses it and the schedule is not `Admission.lfaithful`. The ledgered run stages that request, and
`Exhibits.EndToEnd.duress_too_late`'s outcome still holds there: both nodes armed, the hot spend's quorum in the inventory. At cap
110 the history is the ledgered run as written. The other histories of this section are faithful at cap 100
(`Exhibits.LedgerSilence.others_faithful`).

**What the history leaves beside it.** Time in this run is a set of sampled environments, and no service profile is applied to it.
These histories release before any read, so `DUR-21`'s check is outside them as written
(`Exhibits.CommonRun.old_history_not_refined`); section 14 runs them again with it. The ladder is outside, as in section 9. No bytes or timing beyond what `FedSilence.FObs` carries.

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
sits. Section 13 pairs the same residency at the release itself (`Exhibits.PreRelease.clawback_residency_pair`). That guard reads Escapes only, so on `Sweep`'s run the claw-back's own assembly, like a hot spend's, reads no backend: `WTC-24` is
not checked on it, and an assembly over a coin the instant does not hold is not refused. Section 17's refined run checks it in its own
class (`Exhibits.Assembly.clawback_assembled`). A refresh's ingress stays outside the kernel.

**SILENCE across the ingress** (`bps-9oab.2`, first part, base `aa96393`). Requirements read: `DUR-1`, `DUR-36`, `SPN-34`,
`SPN-50`, `SPN-51`, `SEC-10`; ADR decisions unchanged. Reused: `Silence.silence`, `FedSilence.fed_silence_adaptive_fresh`,
`Silence.clawback_pub`, `ClawbackIngress.register`, `Kernel.clawback_reads_no_arm`. The post-check registration is in the walk's
alphabet and answers `ClawbackIngress.verdict` (`Silence.respond`); the refusal is that verdict's, Lockdown first
(`ClawbackIngress.register_verdict`).

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| The response reads no arm state | `Silence.respond_clawback_pub`, `Silence.respond_clawback_arm_blind` | Two nodes with one projection, or one node with its arm bit, `T` and sweep flag changed |
| The registration keeps the invariant | `Silence.inv_clawback` | `Silence.NodeInv` before; `Silence.wfEvent` admits the claw-back |
| No claw-back is outside the shape boundary as the rule stands | `Silence.wfEvent_clawback_escapeRole` | `r.entryTarget = .escapeRole` |
| The earlier walks keep their relation | `Silence.silence_pre`, `FedSilence.fed_silence_pre`, `FedSilence.fed_silence_adaptive_pre` | The premises of `Silence.silence`, `FedSilence.fed_silence` and `FedSilence.fed_silence_adaptive` |
| Run, inside the horizon | `Exhibits.ClawSilence.clawback_inside_walk` | From `Exhibits.LedgerSilence.L0`, the six arming steps then the claw-back at nodes 1 and 2 at 70, before `T` at 95: all 14 steps walked with equal observations; `Accepted` at 70 with `remaining_secs = 0` in both families; a fire pass at the backward sample 60 releases nothing, the window `[70, 110]` opens at 70; a partial delivered later at 80; the package check and the send at 80 |
| Collision refusal in both families | `Exhibits.ClawSilence.collision_both_families` | The claw-back under the resident pair's Escape id at node 1, after the arming steps: `PSBT_INCONSISTENT` / `candidate_identity` in both families, node 1 unchanged |
| A claw-back past `T` | `Exhibits.ClawSilence.late_clawback_stops` | At 120 the duress family's node 1 is past its horizon: the walk stops at the horizon, not at the shape boundary |
| The handler's three transitions | `ClawHandler.replay_unchanged`, `ClawHandler.fresh_projection`, `ClawHandler.lockdown_precedes_replay`, `ClawHandler.nonce_independent` | A request after the checks before the lookup; a hit on a node not locked down; any encoder |
| A replay carries no tag | `ClawHandler.replay_indistinct` | A hit on a node where the claw-back is resident: the observation is fresh evaluation's with the stored response in place of the fresh one |
| The handler inside the walk | `ClawHandler.hfed_silence_adaptive_fresh` | `FedSilence.fed_silence_adaptive_fresh`'s premises and any one log for both runs |
| Retry, changed bytes and delivery, run | `Exhibits.ClawHandler.handler_inside_walk`, `Exhibits.ClawHandler.retry_changes_nothing` | After the six arming steps, all 18 steps walked against an observer: the claw-back at nodes 1 and 2 at 70, a retry under another nonce and one after release at 80 answered the stored `Accepted` with the state unchanged, a changed-bytes request at 70 evaluated afresh with node 1 unchanged and both keys retained beside the first `Accepted`, node 2's partial delivered to node 1 at 80 twice and never to node 3, the package check and the send |
| Replay after pruning, run | `Exhibits.ClawHandler.replay_after_prune` | A checked claw-back with expiry 90, accepted at 70 and pruned at 92, inside the horizon: a retry at the backward sample 80, with its key still in the log, whose expiry is not modelled, answers the stored `Accepted` at 70 and the candidate stays absent; a changed-bytes request then registers it again, answered at 80 |

Retained exclusions: nonce admission, the expiry predicates and decoding, which precede the lookup, and verification and
signing material, which follow it and precede this registration (`SPN-50`'s order: "the two expiry predicates, decode,
idempotent replay, pruning, verification"); the log's expiry at commitment expiry and cacheable evaluation refusals; the relay of the
claw-back request and its re-relay on replay; and serialized response bytes, since `Silence.Resp` carries the commitment id and
instants and the encoder is a free parameter. One negative control plants a claw-back answer that reads the arm bit and
asserts `Exhibits.ClawSilence.clawback_inside_walk`, the three `Exhibits.ClawHandler` runs and
`Exhibits.ClawHandler.retry_replays_first` fail; another plants it in the
replay's answer alone and asserts `Exhibits.ClawHandler.handler_inside_walk` and `Exhibits.ClawHandler.replay_after_prune` fail.
In `Exhibits.ClawHandler.replay_after_prune` the request that registers the claw-back again is answered `Accepted` at 80 while
its key is retained with the commitment's first `Accepted`, at 70, as `ClawbackIngress.retain` has it. `SPN-50` settles
what a later exact retry of that key answers: "a retained acceptance key MUST return the claw-back commitment's first
`Accepted` on this node verbatim", and "a later successful fresh evaluation adds its key without replacing earlier keys
or that first `Accepted`", so it answers 70, as `SPN-23` says of a spend: "A fresh evaluation's response is selected by
`SPN-34` and can differ from its later retained-key replay." `Exhibits.ClawHandler.retry_replays_first` asserts that
answer in both families. The run prunes at sample 92, past the expiry 90, then registers again at sample 80, before it.
That takes a backward wall step, and freshness needs both the raw wall sample and the high-water mark below the expiry
(`SPN-10`: "`expiry > effective_now`"; `SPN-13`: "`effective_now = max(high_water, raw_now)`"). The log must still hold
the key: `SPN-24` says "Log entries expire with their commitment", and `SPN-34` does not choose a log-pruning clock.

**Resident identity and retry.** The collision refusal is the owner-authorized amendment in
`SPN-51`: "the node MUST refuse `PSBT_INCONSISTENT` / `candidate_identity`". Identical complete
change-free Escape PSBT bytes, wallet, expiry, node policy version and fee evidence give identical
`CHN-24` commitment input; lock time and sequence equality alone do not. A fresh request nonce
changes neither that identity nor establishes a replay hit.

`ClawbackIngress.register_projection` proves, over every environment, node and candidate, that the response
wrapper's node is exactly `Kernel.clawback`'s node. `ClawbackIngress.refuses_pair` assumes Lockdown clear and
a resident paired id, and returns the refusal with the entire node unchanged; `ClawbackIngress.lockdown_first`
retains the earlier latch refusal. `Exhibits.Collision.pair_collision` takes the pair from legal idle
and armed prefixes of the existing end-to-end run; `Exhibits.Collision.checked_identity` checks the
same Escape as a claw-back. These are registration responses, not a whole-ingress SILENCE theorem.

Singleton replay is settled alongside the refusal, following the three-of-four reader majority;
the role/commitment/exact-byte key follows the two explicit exact-byte proposals rather than the
resident-id-only proposal. `ClawbackIngress.lookup` uses that key; `ClawbackIngress.retain` keeps existing entries
and the role/commitment's first acceptance bytes when adding another key. `ClawbackIngress.replay_preserves`
keeps the entire node and returns the supplied retained response verbatim. `Exhibits.Collision.retry_keys`
separates pair role, changed metadata and changed commitment from an exact singleton hit, and
`Exhibits.Collision.retry_retains_first` retains both accepted byte keys. Decoded PSBT and response
bytes are supplied, not a parser/serializer proof; log expiry, refusal eligibility, admitted nonce
consumption, actual signing material and relay work remain outside. Their structured forms, `ClawHandler.lookup` and
`ClawHandler.retain`, equal to them on the encoded log under every encoder (`ClawHandler.lookup_encode`,
`ClawHandler.retain_encode`), run inside the SILENCE walk through `ClawHandler.hwalk` (section 4). Section 10's SILENCE stop remains.

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
model. This does not establish SILENCE across claw-back ingress; sections 4 and 11 hold that, and section 10's horizon remains.

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
previous histories. No runtime or hardware experiment is claimed. The collision response and singleton retry are treated in section 11;
the ledger's accounting result and the SILENCE horizon in section 10, and the immature-coinbase text, are unchanged.

## 13. Release only after the pre-release check

`BtcPolicy.PreRelease` and `BtcPolicy.Exhibits.PreRelease`, change set `bps-9oab.3`, base `929b54e`. Newly formalized
behaviour: `DUR-21`'s check before an Escape's partial leaves, for the base rung, on the composed sweep. Representation
change: the kernel's fire pass takes a per-candidate verdict, and a refined sweep run computes it. No protocol, ADR
decision or guard value changes. Requirements read: `DUR-21`, `DUR-22`, `DUR-23`, `DUR-24`, `DUR-25`, `DUR-26`,
`DUR-27`, `DUR-32`, `DUR-36`, `WTC-24`, `CHN-34`, `SEC-9`. Reused: `Sweep.passAt`, `Sweep.covered`, `Sweep.ancestryOk`,
`Sweep.authorizedAt`, `Coverage.denominator`, `Witness.maxVsize`, `Federation.fanout`, and the checked request of
section 10 (`Exhibits.Ingress.req0`).

**The release boundary.** `Kernel.Env.withholds` names the Escape-role candidates whose verdict at this pass failed.
`Kernel.firePass` releases a candidate only when it is due, authorized (`DUR-10`) and not withheld, so a failed
candidate gets no queued partial and its release cursor does not move. Nothing is deleted after the fact. The kernel
reads no backend, and every kernel, federation and sweep result holds for every verdict. With nothing withheld the
pass is the one the kernel had before (`Kernel.firePass_nothing_withheld`). `Kernel.firePass_withheld`: a withheld
candidate stays as it was and none of the pass's effects is its own. `Kernel.firePass_split`: what the pass emits is
the old pass over the candidates not withheld, and nothing outside the registry changes with the verdict, so the
Lockdown branch, hot releases and every other candidate keep their work.

**The verdict and its order.** `PreRelease.attempt` builds one node's record for one candidate at one observed
instant, each value from the ones before it: the ladder (the base alone), one membership read over it, `DUR-22`'s pass
and protected value, the maximum finalized vsize (`PreRelease.maxVsize`, at the node's threshold), `DUR-23`'s fee at
that vsize (`PreRelease.feeOk`, in unbounded integers), `DUR-24`'s coverage, `DUR-26`'s one-rung selection
(`PreRelease.selectOne`) and `WTC-24`'s ancestry on the selected rung. `PreRelease.Attempt.verdict` reads them in
`DUR-21`'s order and reports the first step that fails. With no observation the verdict is `PreRelease.Stage.noRead`.
`PreRelease.verdict_release_iff` states the conjunction a release needs. `PreRelease.ancestry_after_selection`: a
failure at ancestry means the fee and coverage passed. `PreRelease.verdict_reads_no_possession`: possession is not
read, because `DUR-28`'s quorum belongs to assembly and the partials that make it are the ones this release sends.

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| Refined run | `PreRelease.Execution`, `PreRelease.releaseOk`, `PreRelease.failing`, `PreRelease.mem_failing` | `Sweep.Execution` with one more conjunct: a ladder pass lists no release, and a fire pass carries the verdict `PreRelease.failing` computes from the acting node's latest observation, its authorized set read off its history, and its registry. The pass does not consume the observation; reading it again is reading an instant the truth has been |
| Relation to the old abstraction | `PreRelease.to_sweep`, `PreRelease.execution_iff` | A refined run is a sweep run, same trace and state. A sweep run is refined exactly when every fire pass carries the computed verdict and every ladder pass lists no release. `PreRelease.fed_execution`, `PreRelease.armed_freezes_hot` and `PreRelease.submitted_in_order` follow |
| Safety without an Escape | `PreRelease.lift_safety`, `PreRelease.fire_available` | Every federation history with no assembly whose fire passes withhold every Escape-role candidate (the verdict with no observation) and whose ladder passes list no release lifts over every backend instant: arming, freezing, hot releases, claw-backs, Lockdown, extraction and forgery wait on no Escape. A fire pass carrying the computed verdict is admitted at every state |
| Release origin | `PreRelease.release_origin` | At an admitted fire pass, every row it adds to the partial inventory is a candidate's that the pass releases, over that candidate's transaction at the row's input, by this node; for an Escape-role candidate, the verdict at that pass released rung 0. No premise says the release was authorized |
| Inventory provenance | `PreRelease.inventory_provenance`, `PreRelease.Emitted` | Every row in the inventory names a signer in the cumulative extracted set, or was emitted by that signer's honest node at a fire pass whose verdict released it, if it is an Escape-role candidate's |
| No premature exposure | `PreRelease.no_premature_exposure` | The same, for a signer outside the cumulative extracted set: the extracted alternative is dropped only under that premise |
| Refusal | `PreRelease.refusal_preserves` | A failed verdict leaves the candidate as it was, its cursor included, and adds no row of it |
| Authority persists | `PreRelease.authority_persists` | The inventory, the extracted set and each node's exposure only grow; across a fire pass each candidate keeps its transaction and held set, and a release once recorded stays recorded |

**Exhibits.** Each is a decided refined run on section 10's model: three honest nodes, threshold 2, the checked request,
a coin of 510 000 and an Escape paying 499 800 (a model parameter in sats). The positive run is
`Exhibits.PreRelease.base_sweep` (with `Exhibits.PreRelease.base_sweep_execution`): both nodes release while each holds
only its own signature, and node 1 assembles and submits. A separate failure for each check:
`Exhibits.PreRelease.coverage_at_bound` (exactly at the bound releases; one sat more of protected value withholds),
`Exhibits.PreRelease.fee_at_max_vsize` (the fee passes at the finalized vsize and fails at the maximum),
`Exhibits.PreRelease.missing_prevout_withholds` and `Exhibits.PreRelease.late_deposit_moves_denominator`. Then
`Exhibits.PreRelease.observation_moves_decision`, where a read taken after the move fails and a stale read releases;
`Exhibits.PreRelease.one_fails_other_releases`, two selected Escapes in one pass; and
`Exhibits.PreRelease.armed_without_release`, where both nodes arm and freeze and nothing leaves. The remaining runs are
`Exhibits.PreRelease.later_attempt_releases`, `Exhibits.PreRelease.earlier_exposure_survives` and
`Exhibits.PreRelease.failed_then_forged` (an honest pass that withholds, then the node's key extracted and the partial
forged). The paired claw-back runs are `Exhibits.PreRelease.clawback_residency_pair` and
`Exhibits.PreRelease.clawback_resident_covered`. With the claw-back resident or confirmed at node 1's read, coverage
holds, ancestry fails and no Escape row leaves. With it evicted before the read, or never resident although accepted
and signed, the Escape is released. `Exhibits.PreRelease.bypass_not_refined` is a sweep run in `Sweep.lift_unassembled`'s
domain, releasing the Escape whatever the backend, that is not a refined run.

**The old boundary that changed.** `Sweep.lift_unassembled` is unchanged and stays a result about `Sweep` alone, where
a fire pass's verdict is unconstrained. Its refined replacement is `PreRelease.lift_safety`, with the restricted domain
above. Sections 9, 10 and 11 run on `Sweep`, so their histories release whatever the chain shows, as they say;
section 14 runs section 10's histories with the check. Two
gate controls plant the failures this section rules out. One drops the verdict from the fire pass, and the exhibits'
withholding fails. The other accepts any verdict at a fire pass, leaving only the check at assembly, and
`PreRelease.release_origin` and `PreRelease.refusal_preserves` fail.

**Not modelled.** The ladder beyond the base, on this run: section 16 checks it over reads supplied per pass, and its
one-rung case is this section's verdict. A resident txid outside the ladder in the
batched read: the read is one lookup per rung and cannot return one. `DUR-25`'s re-evaluation at the exact vsize stays
at assembly, where `Sweep.check` reads coverage and ancestry; the fee floor at the exact size is section 17's (`Assembly.exactOk`). "Empty is an error"
(`DUR-22`) is read as a zero protected value. Each transaction's legacy length and each outpoint's value are model
parameters keyed by id. The verdict reads an observed instant with no freshness bound. Over `Ingress.CheckedTrace`,
the candidate's transaction is the request's (`Ingress.accepted_validates`); the refined run alone does not require
checked ingress. This creates no liveness promise: a pass that withholds may be retried under the existing schedule.

## 14. The first milestone on one composed run

`Recovery.to_prerelease`, `Recovery.no_premature_exposure`, `PreRelease.failingAt_pub` and
`BtcPolicy.Exhibits.CommonRun`: the base-only part of `bps-9oab.8`, base `933163a`. Proof and representation
change: the composed run of section 10 now carries section 13's check; no protocol, ADR decision, guard value or
existing theorem statement changes. Requirements read: `DUR-21`, `DUR-1`, `DUR-8`, `DUR-19`, `DUR-28`, `DUR-36`,
`SEC-10`, `SEC-54`, `POL-16`, `POL-20`. Reused: `Recovery.Execution`, `Recovery.fed_record`, `PreRelease.Execution`,
`PreRelease.execution_iff`, `PreRelease.fill`, `PreRelease.no_premature_exposure`, `Federation.cohort_no_exposed_quorum`,
and section 10's histories with their ledgered replay and SILENCE walk.

**The common run.** Each history of section 10 runs again with each fire pass preceded by its node's read of the
instant the truth then is (`Exhibits.CommonRun.readFirst`), the fire pass's verdict written by `PreRelease.fill` and
then checked (`Exhibits.CommonRun.refined`), never assumed. The book is section 13's, in sats, with one more coin, outpoint 9,
of 1 000 000 that no Escape spends (`Exhibits.CommonRun.book`); each instant is section 10's with every confirmed
coin at this book's value (`Exhibits.CommonRun.inst`). Where the check releases, the verdict is empty and the federation
steps are exactly the history's as first written, so `Exhibits.CommonRun.same_federation` (from `Recovery.fed_record`)
gives the same federation state and trace.

| Claim | Owner | Declaration | Domain, alphabet and premises |
| --- | --- | --- | --- |
| The composed run is a refined run underneath | `DUR-21` | `Recovery.to_prerelease`, `Recovery.no_premature_exposure` | Every `Recovery.Execution`, over every composed step (sweep, latch, death, custody, publication), whose sweep steps carry the computed verdict and whose ladder passes list no release (`PreRelease.Checked`). Derived: the verdict, from the acting node's latest observation and history. Still supplied: the observed instant, with no freshness bound; extracted keys, a separate inventory origin |
| The verdict reads only the SILENCE projection | `DUR-21`, `DUR-1` | `PreRelease.failingAt_pub`, `PreRelease.failing_pub`, `PreRelease.verdict_congr` | Two nodes with one `Silence.pubNode`, at one authorized set and one observation, withhold the same ids: the verdict reads the threshold and the ids, roles and transactions of the candidates and the selected set, not the arm bit, `T`, duress bits, freezes or holder-written windows. Not derived: that the two families read one instant and one authorized set, since the walk carries no backend |
| Coerced, usable base Escape | `DUR-21`, `DUR-28`, `DUR-29` | `Exhibits.CommonRun.coerced_refined`, `Exhibits.CommonRun.coerced_rows_emitted` | Both nodes arm, read the vault and release rung 0 while each holds only its own signature; node 1's read before assembly shows coverage, ancestry and `t` signers on every input; the send submits the Escape; the chain alone confirms it. Federation steps equal section 10's `coerced`, verdict included. Every inventory row was emitted past its node's verdict |
| What section 10 established, on it | `DUR-8`, `POL-16`, `POL-20`, `DUR-1` | `Exhibits.CommonRun.coerced_carries` | Through the equal federation trace: checked ingress and the hot spend's binding, no exposed quorum for the hot spend (`Exhibits.EndToEnd.duress_withholds`), gate 24 faithful with the same ledgered replay, and the schedule `Exhibits.LedgerSilence.coerced_silent` walks. Its stop at node 1's first fire pass is unchanged |
| Ordinary | `DUR-28`, `POL-16` | `Exhibits.CommonRun.ordinary_refined`, `Exhibits.CommonRun.ordinary_faithful` | Unarmed nodes read before each pass and withhold nothing; the hot spend is user-signed with `t` signers on every input, submitted and confirmed; no Escape row. Federation steps equal `Exhibits.EndToEnd.ordinaryAll`'s, so its ledgers carry |
| Coerced, unusable Escape | `DUR-19`, `DUR-21`, `DUR-8` | `Exhibits.CommonRun.unusable_refined`, `Exhibits.CommonRun.unusable_withholds` | At the vault holding the large coin both verdicts stop at coverage and both passes withhold: no Escape row, both nodes armed, the hot spend frozen, nothing assembled or submitted, three failure classes. The cohort theorem, its premises decided on the run, leaves the hot spend no exposed quorum |
| Earlier exposure, then a failed attempt | `DUR-21`, `DUR-8` | `Exhibits.CommonRun.prior_exposure_survives` | `Exhibits.EndToEnd.tooLate`, federation steps unchanged by the reads: the hot quorum released before the coercion stays exposed after node 1's later pass at the large coin withholds both Escapes; at the vault the same pass releases the new Escape |
| Pre-horizon claw-back, both families | `DUR-36`, `DUR-1` | `Exhibits.ClawSilence.clawback_inside_walk`, `Exhibits.ClawHandler.handler_inside_walk`, `Exhibits.CommonRun.clawback_walk_verdict` | The walks of section 11 start from this run's six arming steps. At the claw-back's fire pass node 1 is armed in one family and not the other, one projection between them, so both withhold the same Escapes at every instant and authorized set: none at the vault, the Escape at the large coin |
| Submitted, never included | `SEC-54` | `Exhibits.CommonRun.sent_not_included_refined` | The checked coerced history before its chain move: the Escape is submitted, unconfirmed, the coin awaiting inclusion |

**What the run carries.** Checked request data to registration (`Exhibits.EndToEnd.coerced_checked`, by the equal
trace). Registration responses to the observer: section 11's walks over this run's arming steps. Release permission to
the partial effect and the inventory: `Recovery.no_premature_exposure`. Per-input deliveries to node 1's held set and
the backend reads at assembly: `Exhibits.CommonRun.coerced_refined`, through `Sweep.check`'s coverage, ancestry and
possession. Submission: the send's re-authorization at its own state (`Kernel.Reauth`), as in section 9. Inclusion:
the explicit chain step. The Hot ledger and its commitment-keyed accounting: `Exhibits.CommonRun.coerced_carries` and
`Exhibits.CommonRun.ordinary_faithful`. `Exhibits.CommonRun.prior_exposure_survives` rests on `Exhibits.EndToEnd.tooLate`, which gate 24 refuses at cap 100
(`Exhibits.LedgerSilence.too_late_needs_budget`). `EscapeCustody.record_projection` is stated for every rule set, start and
schedule, so custody can stand beside these runs; no custody exhibit is run again at this book.

**Integration failure and its class.** Section 10's histories release before any read: their fire passes come before
the node has read anything, so the verdict is `PreRelease.Stage.noRead` and the release is not one the check admits
(`Exhibits.CommonRun.old_history_not_refined`). The old execution was broader than `DUR-21`, the first class:
`PreRelease.execution_iff` restricts the old abstraction to the refined one, and adding the read before the pass
restores a refined run over the same federation steps. `Exhibits.EndToEnd.safe_without_progress` released both Escape
partials at an instant that does not cover the Escape and delivered one; with the reads that schedule is not a legal
refined run, and `Exhibits.CommonRun.unusable_refined` is the same history without the delivery. No failure of the
second or third class was found.

**The old boundary that changed.** Section 10 had `DUR-21`'s check outside its run. The coerced, ordinary,
unusable, earlier-exposure and submitted histories now run with it, over the same request, nodes and federation
steps where it releases. Section 10's exhibits are unchanged and stay about the run as first written.

**Remaining exclusions.** This is the first milestone's form of the integration, and it kept these out. Section 18
now carries the ladder's reads, the composer and the class checks on this run, and states what still stays out:
- The full ladder on this run. Section 16 checks `DUR-26`'s selection, `DUR-27`'s latch and cumulative release
  and `DUR-28`'s finalization from possession over reads supplied per pass; this run's check is still section
  13's, base rung only, and no ladder history runs on it.
- Immature coinbase composition on this run: the composer's selection and extra coverage check (`OPR-38`), the
  refusal with its clearing height, reorganization across maturity, and an immature-value history with a later
  accepted pass. Section 15 proves them over single backend instants; section 18 reads the composer at a composed run's instants.
- The other package checks were incomplete here: `DUR-25`'s re-evaluation at the exact finalized vsize and the fee
  floor at assembly, the assembly checks of the hot, paired-Escape and singleton claw-back classes, the claw-back's
  own `WTC-24` at assembly (section 11), and the class-specific re-authorization at the send. Section 17 adds them
  as `Assembly.Execution` and decides them on this section's ordinary and coerced histories and on a claw-back run of
  the same model (`Exhibits.Assembly`); section 18 states them on the composed run. A ladder rung's assembly on this
  run is still excluded.
- SILENCE on the refined run: the walk is over federation steps, so a pair of refined runs reading one instant
  and one authorized set in both families is the premise `PreRelease.failingAt_pub` takes, not a derived result,
  and section 10's stop at node 1's first fire pass remains.
- The observed instant's freshness, each transaction's legacy length and each outpoint's value as model
  parameters, and no runtime or deployment result.

## 15. The composer's immature coinbase

`BtcPolicy.Coinbase` and `BtcPolicy.Exhibits.Coinbase`, change set `bps-9oab.4`, base `0a3652a`. Newly formalized
behaviour: the adopted immature-coinbase composition of `OPR-33`, `OPR-38`, `OPR-65`, `OPR-68` and `WTC-28`, over
`Feasibility`'s backend instants. No protocol, ADR decision or guard value changes, and nothing here bears on `F69`'s
deployment question: no theorem says that waiting is an adequate response. Requirements read: `OPR-33`, `OPR-34`,
`OPR-38`, `OPR-65`, `OPR-68`, `OPR-69`, `OPR-82`, `WTC-6`, `WTC-12`, `WTC-28`, `DUR-22`, `DUR-24`, `CHN-21`. Reused:
`Feasibility.composeEvery`, `Feasibility.Vault.denominator_request`, `Feasibility.Vault.coverOk`, `Coverage.covers`,
`Formula.renderNat`, `Watchtower.Input`.

**The backend stays whole.** The scan is the instant's own `Sweep.Backend.confirmed`, so an immature coinbase stays in
the node's read and its denominator, as `WTC-6` requires: "Every path MUST serve an immature coinbase output paying
the vault script, since `DUR-22` counts it". `Coinbase.accept` validates every scanned coin and only then partitions
the scan into the inventory `U` and the immature coinbases left out. The spend composer reads `U` through
`Coinbase.view`, the same instant with its confirmed list narrowed; the node's read is the instant itself. A coin's
class comes from its creating transaction's inputs as `WTC-12` reads them (`Coinbase.kind`): a coinbase has exactly the
one coinbase input. No caller-supplied classification is read. The boundary that stays outside is `OPR-82`'s header
and hash checks: `Coinbase.Creating.active` stands for them and is not derived.

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| Maturity | `Coinbase.mature_iff` | Every tip and height: mature exactly from tip `h + 99`, equality included. A height condition, apart from `Recovery.matured`'s relative lock and refresh's MTP age |
| Validated before left out | `Coinbase.immature_validated`, `Coinbase.ordinary_kept`, `Coinbase.partition` | Over an accepted pass: each coin left out passed its reads and evidence, is a coinbase by its creating transaction and is short of maturity at the pass's tip. An ordinary coin is in `U` at any height. Every scanned coin is in `U` or left out. An invalid or inconsistent coin refuses the whole inventory first (`Coinbase.Refusal.evidence`) |
| `I` and the clearing height | `Coinbase.value_split`, `Coinbase.clear_is_last_maturity`, `Coinbase.tip_below_clear` | `I` is the sum of the coins left out, and with `U` it is the whole scan. At the reported height every counted coin has 100 confirmations. When at least one coin is left out, one block earlier one of them does not, and on an accepted pass the height is above its tip |
| The additional check | `Coinbase.extraCovers`, `Coinbase.extra_expr_agrees`, `Coinbase.extra_zero` | `Coverage.covers` at the widened amount, so no second arithmetic. The rendered `Coinbase.extraFormula` is proved to evaluate to it, and the copies gate finds it verbatim in `OPR-38`. With nothing left out it is `CHN-21`'s check |
| Spend | `Coinbase.spend_inputs`, `Coinbase.spend_passed_extra`, `Coinbase.spend_refuses_extra`, `Coinbase.spend_empty_inventory` | The request's inputs, which the primary and its Escape both spend, are `U`'s outpoints, with no immature coin among them. A composed spend passed the check. Where the check fails, or `U` is empty, the command refuses with `I` and the height, both numbers and no outpoint, and no request exists to sign |
| Relation to the old abstraction | `Coinbase.spend_reduces`, `Coinbase.ordinary_only` | On a pass that leaves nothing out, the spend is `Feasibility.composeEvery` over the same instant, with the same request and the same refusals. A history of ordinary outputs only leaves nothing out |
| Node denominator | `Coinbase.node_denominator`, `Coinbase.node_covers_iff_extra`, `Coinbase.composed_covers_at_node` | At the instant the composer read, with values agreeing with the book, no authorized unconfirmed value, `DUR-22`'s current guards and the request measured alone: the node's denominator is `total_in + I`, and its `DUR-24` on the request is the additional check |
| Claw-back | `Coinbase.claw_names_immature`, `Coinbase.claw_ok_iff`, `Coinbase.claw_all`, `Coinbase.claw_replace_reads_no_scan` | A known-outpoint set naming an immature coinbase refuses. Otherwise it composes exactly when `T` is non-empty, unique and in `U`, and its inputs are `T`. `--all` names `U`, reports the count left out, and with `U` empty refuses for want of a target. `--replace` reads neither the instant nor the scan |
| Refresh | `Coinbase.refresh_never_selects`, `Coinbase.refresh_held_back` | For every age rule, taken as a parameter: no immature coinbase is eligible, each is counted as held back, and a valid scan whose `U` is empty is the no-op, exit `0`, with no authorization. Whether eligible coins lead to an authorization is left to each batch's composition and signing, none of them modelled; a later batch is sent only after the earlier batch's watch observed it (`OPR-65`), also not modelled |
| Reorganization | `Coinbase.accept_reads_instant` | A pass reads only the instant's confirmed list, tip height and mempool, and its own records. Nothing carries over from an earlier pass, so a new observation recomputes maturity, `U`, `I` and the height |

**Exhibits.** Each is a decided instant at 2-of-3 with `Exhibits.Feasibility.lim`'s assumed sizes and a coverage of 51.
`Exhibits.Coinbase.no_coinbase_preserved`: ordinary coins only, and the spend is `Feasibility.composeEvery`'s request.
`Exhibits.Coinbase.absorbed_spend_composes`: a 5 000 immature coinbase beside 100 000, absorbed by coverage. The backend
still holds the coin, and the node's denominator at the read is 105 000. `Exhibits.Coinbase.exceeding_refuses`: 100 000
immature beside 100 000, where `CHN-21` passes and the additional check refuses with `I` = 100 000 and height 249.
`Exhibits.Coinbase.equality_passes`: exactly at equality the spend composes, and one sat more refuses.
`Exhibits.Coinbase.invalid_coinbase_refuses`: a mismatched value, a coinbase input mixed with a prevout, or a stale
header refuses the inventory for spend, claw-back and refresh alike. `Exhibits.Coinbase.immature_below_hundred`
(confirmations 1, 98 and 99) and `Exhibits.Coinbase.mature_at_hundred` (100, where the spend spends the coin).
`Exhibits.Coinbase.several_sum_and_last`: three coinbases at heights 120, 180 and 150, `I` = 12 000 and height 279.
`Exhibits.Coinbase.all_immature`: no empty spend, no empty `--all`, and the refresh no-op.
`Exhibits.Coinbase.clawback_outside_target`, `Exhibits.Coinbase.refresh_skips_immature` and
`Exhibits.Coinbase.refresh_only_immature_noop`, where an empty scan is refused with exit `1` and is not the no-op.
`Exhibits.Coinbase.reorg_recomputes`: a coin mature at tip 199 is left out again when a reorganization moves its block
to height 105. Then three cases where the composer passes or the wait ends and nothing follows from it.
`Exhibits.Coinbase.later_read_refuses`: the request composed at one read fails the node's coverage at a later one.
`Exhibits.Coinbase.later_coinbase_no_bound`: at the reported height 249, a new coinbase refuses the spend again, until
339. `Exhibits.Coinbase.stalled_chain_no_progress`: with the tip held at 200, a changed mempool and sequence give the
same refusal.

**Controls.** Two gate controls plant the failures this section rules out. One omits `I` from the additional check at
`Coinbase.composeSpend`'s call, and the exhibits that refuse on it fail. The other makes maturity strict, so 100
confirmations no longer suffice, and `Exhibits.Coinbase.mature_at_hundred` fails. The maturity of 100, the offset of 99
and the formula are emitted values the copies gate holds `OPR-33`, `OPR-38` and `WTC-28` to.

**The old boundary that changed.** Section 9's composer spent every confirmed coin of the backend, and its backend
carried no coinbase class. `Feasibility.composeEvery` is unchanged and stays `OPR-33`'s composer over an inventory
that leaves nothing out; `Coinbase.composeSpend` is the refinement, and `Coinbase.spend_reduces` is the relation.

**Not modelled.** `OPR-82`'s brackets, retries and freshness. Sorting the scan: it is taken in canonical order, so a
duplicate shows as an out-of-order outpoint. The primary's outputs and dust, and fee bounds beyond
`Feasibility.composeEvery`'s. Refresh's age order, its batches of `SPN-44`'s input limit, its fee cap and its watch.
The claw-back's fee, dust and output checks, and its order. A cache implementation, which is runtime conformance. On
the composed run, section 18 reads the spend composer at the instants node 1 observes; the claw-back and refresh
composers stay off it.

## 16. Ladder selection and cumulative release

`BtcPolicy.Ladder` and `BtcPolicy.Exhibits.Ladder`, change set `bps-9oab.6`, base `75e8df1`. Newly formalized
behaviour: section 13's check over the existing optional ladder, with `DUR-26`'s selection, `DUR-27`'s latch and
cumulative release through `SPN-38`'s cursor, and `DUR-28`'s finalization from a node's own possession. Representation
change: `PreRelease.Stage` gains `latched`, the failure "if selected is not admissible: fail" that only a ladder above
the base reaches. No protocol, ADR decision or guard value changes; the ladder stays sealed and opt-in (ADR 0016), at
most `Classification.maxRungs` rungs above the base, and nothing asks for one. The singleton claw-back carries no ladder
and is not read. Requirements read: `DUR-21`, `DUR-22`, `DUR-23`, `DUR-24`, `DUR-25`, `DUR-26`, `DUR-27`, `DUR-28`,
`DUR-29`, `DUR-30`, `SPN-27`, `SPN-32`, `SPN-36`, `SPN-38`, `NCH-24`, `NCH-25`, `CHN-16`, `WTC-24`. Reused:
`PreRelease.attempt`'s pieces (`PreRelease.membership`, `PreRelease.maxVsize`, `PreRelease.feeOk`), `Sweep.covered`'s
coverage, `Coverage.denominator`, `BumpTarget.target`, `Cursor.pass`, `Authority.quorum`, `Authority.signers`, and
section 10's checked request with two rungs added (`Exhibits.Ladder.ladder_from_ingress`).

**The attempt and the selection.** `Ladder.attempt` is section 13's record with every rung in place of the base: the
rung transactions, one membership read over them, `DUR-22`'s pass leaving out every resident rung's outputs
(`Ladder.passAt`, which is `Sweep.passAt` with no rung: `Ladder.passAt_no_rungs`), each rung's maximum finalized vsize,
fee and coverage, `DUR-26`'s selection (`Ladder.select`), and `WTC-24`'s ancestry on the selected rung, read as a
replacement of a resident lower rung when there is one (`Ladder.replacesOf`). `Ladder.select` is `DUR-26`'s
pseudo-code over the rungs in fee order, which `CHN-16` fixes and this model takes as given; `required` is the bump
target of a median reading, or `0` on an error or no reading, against the sealed floor (`Ladder.required`).

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| Selection | `Ladder.select_some`, `Ladder.select_sound` | Every rung count, `meets`, admissibility and latch on the ladder: a selected rung is on the ladder, admissible and at or above the latch, so a latched rung that is no longer admissible fails rather than letting a lower rung replace it |
| Verdict | `Ladder.verdict_release`, `Ladder.Attempt.verdict` | A verdict releasing rung `k` read an observation, selected `k`, which is on the ladder, admissible (fee and coverage at its maximum vsize) and at or above a latch on the ladder, and passed `k`'s ancestry. A failed selection names `PreRelease.Stage.latched` when some rung is admissible, `coverage` when some rung passes the fee, and `fee` otherwise |
| Pressure reading | `Ladder.target_none` | No reading is the zero target, and `required` is the floor. The base is not thereby selected: `choice` and the latch still decide |
| One rung is section 13 | `Ladder.select_one_rung`, `Ladder.verdict_one_rung`, `Ladder.failingAt_one_rung` | With no rung above any Escape's base, the verdict at latch 0 is `PreRelease.verdict` over every read, and `PreRelease.failingAt` is the list it withholds |
| Refusal | `Ladder.release_refused` | A verdict releasing no rung releases nothing and leaves the latch and the release floor where they were. A released verdict whose pass releases nothing leaves them too (`Ladder.after`) |
| Per-rung release | `Ladder.release_mem`, `Ladder.refused_not_released` | Every rung a pass releases was admissible at that pass's attempt and lies in `SPN-38`'s interval `[F, U]`, below the rung the verdict released. A rung the attempt refused is released at no position in the interval |
| Cumulative prefix | `Ladder.release_interval`, `Ladder.release_floor`, `Ladder.release_latch` | When the admissible rungs run unbroken from `a` through the released rung, the release is the cursor's interval whole. The floor never moves back; the latch never decreases and stays on the ladder; both move only on a pass that releases a rung |
| One rung, released once | `Ladder.release_one_rung`, `Ladder.release_exhausted` | With no rung above the base and one rung affordable, from a fresh latch and floor the pass releases rung 0 exactly when `PreRelease.verdict` does, leaving the floor at `1`, after which nothing is released: the kernel's `released` bit. The kernel does not model `SPN-38`'s quota, hence the premise |

**The run.** `Ladder.Execution` is one selected Escape across the federation. Each node retains its own ladder for
the run (`Ladder.RCfg.lad`: the base's user-signature hash and the rungs above it, which first deliveries may leave
different at different nodes), its latch and floor (`Kernel.Track`), and the partials it stored. An honest node's pass
reads a `Ladder.Read` the step supplies, with its own rungs in place of the read's for this Escape, and emits one
partial per input of each released rung (`Ladder.emits`), keyed by the rung's txid, its user-signature hash, the input
and the signer. A delivered partial is one of the inventory, stored only under `NCH-24`'s checks against the receiving
node's own ladder (`Ladder.stores`). The adversary extracts any key and forges under an extracted one.

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| Latch on the run | `Ladder.latch_bounded`, `Ladder.track_mono` | Every reachable state: each node's latch is below the length of the ladder it retains, and no step lowers a latch or a floor |
| Inventory provenance | `Ladder.inventory_provenance`, `Ladder.Emitted` | Every partial in the inventory names a signer in the cumulative extracted set, or an honest signer that emitted it at one of its passes, for a rung of its own ladder with that txid and user-signature hash, admissible at that pass's read and at or below the rung its verdict released. No premise says the release was authorized |
| Possession | `Ladder.held_origin`, `Ladder.held` | What a node holds is its own signature on a rung it retains, or an inventory partial that passed `NCH-24` against its own ladder |
| Finalization | `Ladder.finalize`, `Ladder.finalize_sound`, `Ladder.finalize_highest` | The highest rung at or below the latch with `Authority.quorum` over the node's possession, never the inventory: what it returns has the quorum on every input, and no rung with the quorum at or below the latch is passed over |
| No pooling | `Ladder.quorum_own_rung`, `Ladder.quorum_other_rung` | A rung's count reads only the records on its own transaction; records on other transactions alone give no quorum at a positive threshold |
| Who can be counted | `Ladder.counted_retains` | A signer counted on a rung at node `j` is `j`, an extracted key, or an honest node retaining a rung of that txid with the user-signature hash `j` stores it against |
| Common-base fallback | `Ladder.common_base_fallback` | No key extracted; the finalizing node honest and holding the base's quorum on every input, where `DUR-28`'s delivery, quota and window conditions enter, taken and not derived; every rung above the base up to its latch retained with matching user-signature material by fewer than `t` honest nodes. Then it finalizes the base. Nothing makes the base admissible or confirms it |

**Exhibits.** Each is decided. Except where named, each runs on section 13's states, with node 1 reading the vault or
a later deposit, over the ladder `Ingress.check` accepts on section 10's request (`Exhibits.Ladder.ladder_from_ingress`;
that request alone carries no rung). Two fixtures are not from it: `Exhibits.Ladder.refused_inside_prefix` puts the
rung `Exhibits.Ladder.r1low`, whose book value `CHN-16` would rule out, between the base and the top rung, and
`Exhibits.Ladder.partial_inputs` runs a two-input Escape (`Exhibits.Ladder.escM`) at a registry with nothing selected. `Exhibits.Ladder.empty_ladder`: no rung above the base is section 13's verdict, released once.
`Exhibits.Ladder.valid_ladder`: two medians select the two rungs, and a fresh pass releases the prefix from the base.
`Exhibits.Ladder.pressure_error`: no reading is the zero target, and from a latch at rung 1 the same read selects rung 1.
`Exhibits.Ladder.downward_target`: the median falls and the latched rung stays selected, with nothing queued anew.
`Exhibits.Ladder.latched_inadmissible`: after a deposit the latched rung fails coverage, and the selection fails at the
latch though lower rungs are admissible. `Exhibits.Ladder.tops_out`: the selected rung pays less than `required`.
`Exhibits.Ladder.refusal_ladder`: a ladder whose useful result is refusal, at coverage, with nothing moving.
`Exhibits.Ladder.passes_progress`: at one affordable rung per pass, three passes release the three rungs in turn and a
fourth releases nothing. `Exhibits.Ladder.refused_inside_prefix`: a rung inside the cursor's interval fails coverage
and is released to nobody. `Exhibits.Ladder.f51_on_ladder`: `F51` on the ladder, released under the anchor as it stands
and not under the withdrawn one. The runs across nodes: `Exhibits.Ladder.stripped_subsets` and
`Exhibits.Ladder.stripped_fallback` (compatible stripped subsets, with `Ladder.common_base_fallback` applied on the
run); `Exhibits.Ladder.possession_not_inventory`; `Exhibits.Ladder.user_sig_mismatch` (incompatible user-signature
material); `Exhibits.Ladder.split_across_rungs`; `Exhibits.Ladder.partial_inputs` (partial delivery across two
inputs); and `Exhibits.Ladder.extracted_then_forged`, the extracted-key origin.

**Controls.** Two gate controls plant the failures this section rules out. One releases the cursor's whole interval,
dropping the admissibility filter (`Ladder.relOf`), and `Exhibits.Ladder.refused_inside_prefix` fails. The other
selects `choice` without `max(choice, current latch)`, and the exhibits that hold a latch above `choice` fail. The
existing `F51` control, which anchors the cap on the cursor, now also fails `Exhibits.Ladder.f51_on_ladder`.

**The old boundary that changed.** Section 13 checked the base rung alone. `PreRelease.verdict` is unchanged and is
this section's verdict on a ladder of the base alone; `PreRelease.Stage` gains a constructor, and every
`PreRelease` result holds as before. The earlier cursor counterexamples (`Cursor.f51_refused_on_cursor`,
`Exhibits.f51_current_admits`, `Exhibits.dur30_split_finalizes_lower_latch`) are unchanged.

**Latch and floor on a pass that releases nothing.** Both stay where they were. With no rung affordable this is
`SPN-38`'s "release nothing and advance no release bookkeeping on this pass", read as covering the latch, so a latch
never rises on a pass that sends nothing. With the interval empty, or every rung of it refused, the floor stays by
"Only a pass that released at least one rung MUST set `release_floor = U + 1`", and the model holds the latch with it,
the conservative choice, recorded here as a reading.

**Not modelled.** The reads' binding to a composed run's state, and the kernel's own fire pass, which releases the
base alone: this section's run is one Escape with the reads as its input. Section 18 takes those reads from section 14's
run (`Ladder.readOf`); the kernel's fire pass still releases the base alone, and its ladder pass releases the rungs an
list names (`Kernel.ladderPass`), which the base-only refinement admits only when the list is empty and the ladder-aware
refinement only when it is `Ladder.release` at the run's read (`RungRelease.releaseOk`). A resident txid outside the ladder in the batched read. `DUR-25`'s re-evaluation at the exact
finalized vsize and `DUR-29`'s package check on a rung are section 17's `Assembly.rungCheck`, over the same per-pass
reads; `DUR-31`'s re-classification is not modelled. `CHN-16`'s relations
between rungs, which `Ingress` does not check. Delivery, quota and window conditions, which the fallback takes as
premises. The observation's freshness. No fairness, confirmation or fee-market guarantee is stated.

## 17. Assembly and submission for each class

`BtcPolicy.Assembly` and `BtcPolicy.Exhibits.Assembly`, change set `bps-9oab.7`, base `57304b0`. Newly formalized
behaviour of existing rules: the assembly checks of the three classes the model admits, the Escape's re-evaluation at
its exact finalized size, the backend's package verdict as the node reads it, and submission from an earlier assembly
plus the send's own re-authorization. No protocol, ADR decision or guard value changes; refresh stays outside.
Requirements read: `SPN-39`, `SPN-51`, `DUR-11`, `DUR-25`, `DUR-28`, `DUR-29`, `DUR-32`, `WTC-23`, `WTC-24`, `WTC-25`,
`WTC-26`, `CHN-34`, `CHN-35`. Reused: `Sweep.possessed`, `Sweep.covered`, `Sweep.ancestryOk`, `Sweep.authorizedAt`,
`Package.validate`, `Witness.finalizedVsize`, `Witness.finalized_le_max`, `PreRelease.feeOk`, `PreRelease.maxVsize`,
`Ladder.txs`, `Ladder.passAt`, `Ladder.replacesOf`, `Ladder.ancestryTx`, `Sweep.packageOk_origin`, and section 14's
model and histories.

**The class and the check.** `Assembly.classOf` reads what registration writes: the Escape of a pair is `escape`, an
unpaired candidate that is not hot is `clawback`, every other is `spend`, and checked ingress makes every spend hot.
A registered claw-back is in its own class and never in the Escape role (`Assembly.clawbackBorn_class`); it gets its
check from that class, which reads no coverage or fee floor (`Assembly.checkAt_clawback`), and so does a Hot spend
(`Assembly.checkAt_spend`). `Assembly.checkAt` reads, in `SPN-39`'s order, `t` distinct signers on every input of the
node's possession, the Escape's coverage at the assembly's own pass and its fee floor at the exact finalized vsize
(`Assembly.exactOk`), `WTC-24`'s ancestry as a replacement of the resident `Assembly.target` derives
(`Assembly.ancestry`), and the backend's verdict on the candidate alone (`Assembly.packageOk`, `WTC-23`). A claw-back's
target is the first resident other than itself that spends one of its inputs and is a claw-back the node registered,
now or earlier in its history (`Assembly.clawTxs`); a Hot spend and a base Escape replace nothing.

| Claim | Declaration | Premises and domain |
| --- | --- | --- |
| What an admitted assembly checked | `Assembly.checkAt_iff`, `Package.admitted_only_when` | Every authorized set, claw-back list, registry, possession, instant and candidate: the quorum on every input, the Escape's coverage and exact fee, an admitted ancestry verdict, and one tolerated entry from the backend. With `Package.admitted_only_when`, every input shown or the replaced resident's own, every unconfirmed ancestor authorized and at most `Package.ancestorLimit` |
| Replacement targets | `Assembly.target_registered` | A target is resident, a registered claw-back other than the candidate, and spends one of its inputs; only a claw-back has one. `Package.validate` then needs it in the authorized set and the same ordered outpoints |
| Package verdict | `Assembly.accepts_iff`, `Assembly.rejected_refuses` | One entry per member, each allowed or `txn-already-in-mempool`; any other rejection refuses. The entries are the backend's, an input (`Assembly.Cfg.test`) |
| Exact size | `Assembly.exact_le_max`, `Assembly.exact_fee_of_max`, `Assembly.feeOk_mono` | Under `Assembly.Fits` (one supplied witness per input, each at most `W_N` at the node's threshold and the key count), the exact finalized vsize is at most `PreRelease.maxVsize`, so a fee that met the floor before release meets it at the exact size |
| Relation to the old abstraction | `Assembly.to_prerelease`, `Assembly.execution_iff`, `Assembly.checkOf_escape`, `Assembly.guardOk_sweep` | A refined run is a `PreRelease` run, same trace and state; a `PreRelease` run is refined exactly when every assembly passes `Assembly.guardOk`. On an Escape the new check implies `Sweep.check` |
| Safety independence | `Assembly.of_unassembled`, `Assembly.lift_safety` | A `PreRelease` history with no assembly is a refined run; `PreRelease.lift_safety`'s histories lift over every backend instant |
| Send | `Assembly.send_admits`, `Assembly.submitted_in_order`, `Assembly.assembled_of_packageOk` | Under `Kernel.Reauth.beforeSend`: the send's admission adds no backend read, and every submission of any class is of a resident whose standing package test was earned at an earlier assembly that passed its class's check at that assembly's own reads (`Assembly.Assembled`), and which the send's own state finds due and authorized |
| A ladder rung | `Assembly.rungCheck`, `Assembly.rungCheck_sound`, `Assembly.rungCheck_base` | Over section 16's per-pass read: rung `m`'s own quorum, coverage and exact fee, its ancestry as a replacement of the resident lower rung (`Ladder.replacesOf`), and the backend's verdict. On a ladder of the base alone, rung 0's check is `Assembly.checkAt` |

**Premises.** Derived from the composed run: the observation, the authorized set and the registered claw-backs from
the node's own history, possession from `Federation.held`, and the order of assembly and send. Still supplied: the
backend's package verdict, each input's finalized witness weight with `Assembly.Fits` as the stated relation to the
candidate, each transaction's legacy length and each outpoint's value and creator, and, for a rung, section 16's
per-pass read, its possession and the rung index `Ladder.finalize` would return.

**Exhibits.** Each is decided, on section 14's model unless named otherwise. `Exhibits.Assembly.hot_assembled`,
`Exhibits.Assembly.escape_assembled` and `Exhibits.Assembly.clawback_assembled`: the ordinary history, the coerced one
and a claw-back run, each assembled and submitted in its class, and each refused when its coin is gone from the read;
the Escape's exact size is 220 against a maximum of 221, and stopped before the chain move it is submitted and not
included; the claw-back is also refused by another rejection reason. `Exhibits.Assembly.parents_distinguished`: an
authorized resident parent admitted, an external one refused as an unknown prevout, since `WTC-10`'s snapshot leaves an
external resident's output out, and an authorized parent over an external grandparent refused at that ancestor.
`Exhibits.Assembly.ancestor_bound` (24 admitted, 25 refused) and `Exhibits.Assembly.diamond_assembled` (three, not
four). `Exhibits.Assembly.clawback_replacement`: a claw-back over a resident registered claw-back admitted, reordered
or different inputs refused; `Exhibits.Assembly.unregistered_not_target`: a resident never registered as a claw-back is
no target, authorized or not; `Exhibits.Assembly.rung_replacement`: a rung's ancestry over the resident base.
`Exhibits.Assembly.rung_assembled`, on section 16's ladder and with the possession of its run: rung 1's whole check
passes, fresh and as the resident base's replacement, at an exact size of 220; it is refused before the second
partial arrives and when the backend rejects the rung, and rung 2, without a quorum, is refused.
`Exhibits.Assembly.package_entries`. `Exhibits.Assembly.unrelated_size`: without `Assembly.Fits`, a supplied size
refuses what passed before release. `Exhibits.Assembly.frozen_after_assembly`: a holder decision between a Hot spend's
assembly and its send freezes it, and the send submits nothing. `Exhibits.Assembly.backend_moves_after_assembly`: an
outsider's transaction resident over the coin after the assembly does not stop the send, which reads no backend.

**Controls.** Two gate controls plant the failures this section rules out. One returns `Assembly.guardOk` to the
Escape role alone, and `Exhibits.Assembly.hot_old_broader` fails. The other makes `Assembly.packageOk` ignore the
backend's entries, and `Exhibits.Assembly.clawback_assembled`, `Exhibits.Assembly.package_entries` and
`Exhibits.Assembly.rung_assembled` fail.
Five existing controls now also fail exhibits of this section: the re-authorization placed before assembly fails
`Exhibits.Assembly.frozen_after_assembly`; the replacement's ancestry read plain fails
`Exhibits.Assembly.clawback_replacement`, `Exhibits.Assembly.rung_replacement` and `Exhibits.Assembly.rung_assembled`;
`WTC-24`'s ancestor limit one higher fails `Exhibits.Assembly.ancestor_bound`; and the two `DUR-13` T-clamp plants,
which move the coerced history, fail `Exhibits.Assembly.escape_assembled`.

**The old boundary that changed.** `Sweep.assemblyOk` checked the Escape role alone, so a Hot spend or a claw-back
assembled over any instant. The refined run refuses some of those assemblies:
`Exhibits.Assembly.hot_old_broader` is a `PreRelease` run whose Hot spend assembles over a missing prevout and is not
an `Assembly` run. That is the first class of integration failure: the old execution was broader than `SPN-39`. Every
`Sweep` and `PreRelease` result is unchanged and applies through `Assembly.to_prerelease`.

**Not modelled.** Refresh. Section 18 states these checks on the composed run (`Assembly.of_composed`). A rung's
assembly on section 14's run: the kernel assembles one rung per candidate, and
`Assembly.rungCheck` reads section 16's supplied reads. The finalized transaction's bytes, its signatures' actual
lengths and `WTC-27`'s local deserialization. The backend's correctness, and what it does with a submission. `CHN-16`'s
relations between rungs, `DUR-31`'s re-classification, and the observation's freshness. In-flight candidates through
Lockdown stay the kernel's (`Kernel.lockdown_preserves_in_flight`).

## 18. The extensions on one composed run

`Ladder.readOf`, `Ladder.fire_withholds`, `Ladder.fire_release`, `Assembly.of_composed`, `Assembly.composed_submitted`,
`Assembly.guard_pub` and `BtcPolicy.Exhibits.Integrated`: the second part of `bps-9oab.8`, base `b1b4b7d`, which stays open
for the rung releases below. Integration only: no new model beside the existing modules, and no protocol, ADR decision, guard value or existing theorem statement
changes. Requirements read: `DUR-1`, `DUR-21`, `DUR-22`, `DUR-26`, `DUR-27`, `DUR-28`, `DUR-29`, `SPN-38`, `SPN-39`,
`OPR-33`, `OPR-38`, `WTC-6`, `WTC-28`. Reused: section 14's composed run (`Exhibits.CommonRun.integ`, its book and
instants), section 17's class checks and backend verdict (`Exhibits.Assembly.acfg`), section 16's ladder with two rungs
from checked ingress, and section 15's composer and evidence records.

| Claim | Owner | Declaration | Domain, alphabet and premises |
| --- | --- | --- | --- |
| The ladder's read on the composed run | `DUR-21` | `Ladder.readOf` | The read a fire pass takes in a composed sweep state after its history: the acting node's authorized set, registry and latest observation, which `PreRelease.failing` reads there. Still supplied: the median reading, since the run carries no fee estimate, and the rungs above the base, which `Ladder.RCfg.read` puts in |
| The kernel's fire pass is the ladder's verdict at that read | `DUR-21` | `Ladder.fire_withholds` | Every trace whose fire passes carry the verdict and whose ladder passes list no release (`PreRelease.Checked`), every fire pass in it and every median: the ids it withholds are those whose ladder verdict at the read it takes, at latch 0 with no rung above the base, is not a release |
| The ladder's pass at that read releases the base where the fire pass does | `DUR-27` | `Ladder.fire_release` | The same traces, an Escape-role candidate of the acting node, a fresh latch and floor, no rung above the base and one rung affordable (the kernel has no `SPN-38` quota): the pass releases rung 0 when the fire pass does not withhold the id, and when it releases nothing the fire pass withholds it |
| The class checks on the composed run | `SPN-39` | `Assembly.of_composed` | Every `Recovery.Execution`, over every composed step, whose fire passes carry the verdict, whose ladder passes list no release, and whose assemblies pass their class's check (`Assembly.Checked`), the check's guards being the run's (`cfg.pre.sweep = rc.sweep`): its sweep trace and state are an `Assembly.Execution` |
| Send-time re-authorization on it | `DUR-29` | `Assembly.composed_submitted` | The same runs and guards, under `Kernel.Reauth.beforeSend`, and a send `Assembly.admits` at its state: what it submits is a resident due and authorized at the send's own state, whose package test was earned at an earlier assembly that passed its class's check (`Assembly.Assembled`) |
| The class check and the SILENCE projection | `DUR-1` | `Assembly.guard_pub`, `Assembly.checkAt_node`, `Assembly.checkAt_cand` | Two nodes with one `Silence.pubNode`, at one authorized set, claw-back list, possession and instant, admit the same assembly of every commitment id: the check reads a node through its threshold and the selected Escapes' transactions, and a candidate through its class and transaction. Not derived: that the two families read one instant, authorized set, claw-back list and possession |

**The common executions.** Each is decided, never assumed, on the composed run except where the row says otherwise.

| Execution | Declaration | What it exercises |
| --- | --- | --- |
| Ordinary Spend | `Exhibits.CommonRun.ordinary_refined`, `Exhibits.CommonRun.ordinary_faithful`, `Exhibits.Assembly.hot_assembled`, `Exhibits.Integrated.common_assembled` | The hot spend assembled in its class and submitted, its Hot ledgers carried |
| Coerced Spend, usable base Escape | `Exhibits.CommonRun.coerced_refined`, `Exhibits.CommonRun.coerced_carries`, `Exhibits.Assembly.escape_assembled`, `Exhibits.Integrated.common_assembled` | Arming, Hot withholding, the verdict, possession on every input, the Escape's class check at its exact size, the send |
| Pre-horizon claw-back in both families | `Exhibits.ClawSilence.clawback_inside_walk`, `Exhibits.ClawHandler.handler_inside_walk`, `Exhibits.CommonRun.clawback_walk_verdict`, `Exhibits.Integrated.clawback_walk_guard`, `Exhibits.Integrated.clawback_walk_assembles`, `Exhibits.Assembly.clawback_assembled` | The walks through the claw-back's registration and response, over federation steps with no backend. Where node 1 is armed in one family only, one verdict and one assembly check in both; at the walk's own assembly step the claw-back's class check passes in both families, at the vault and the possession its two partials give, which the walk does not carry and the exhibit supplies alike to both. The claw-back's assembly on the composed run is `Exhibits.Assembly.clawback_assembled`'s run, without the arming prefix |
| Coerced Spend, unusable Escape | `Exhibits.CommonRun.unusable_refined`, `Exhibits.CommonRun.unusable_withholds`, `Exhibits.Integrated.common_assembled` | Safety with no progress: both passes withhold, and the class check admits no assembly of the Escape |
| Ladder with changing observations | `Exhibits.RungRelease.rung_on_run`, `Exhibits.RungRelease.refused_rung_on_run`, `Exhibits.Integrated.ladder_on_run`, `Exhibits.LadderPass.rung_rows`, `Exhibits.LadderPass.base_only` | Below: per-rung release and latch on `Ladder`'s own run, its reads the composed run's. The kernel's ladder pass queues the listed rungs' partials, shown one kernel step from a state with rungs written in (`Exhibits.LadderPass.withRungs`); no ladder pass of `PreRelease`'s refined execution (`PreRelease.Execution`), or of an honest node on a federation execution checked by `Ingress.check` (`Ingress.CheckedTrace`), queues a partial. On the ladder-aware run a reachable ladder pass releases the rungs `Ladder.release` computes at the node's own read, with the Escape registered at `Kernel.accept` as checked ingress registers it (`Exhibits.RungIngress.ladder_registered`, `Exhibits.RungIngress.rung_run_checked`); a rung partial delivered to a peer is in that peer's possession over the ladder, which counts it on its own rung alone (`Exhibits.RungIngress.rung_held_on_run`); no rung is assembled or sent |
| Immature-value refusal and later accepted pass | `Exhibits.Integrated.immature_then_accepted` | Below |
| Prior honest signature exposure | `Exhibits.CommonRun.prior_exposure_survives`, `Exhibits.Integrated.common_assembled` | Earlier authority through arming and a later failed attempt, on a run that passes the class checks |
| Submitted but never included | `Exhibits.CommonRun.sent_not_included_refined`, `Exhibits.Assembly.escape_assembled`, `Exhibits.Integrated.common_assembled` | The Escape assembled in its class and sent, and not confirmed |

**The ladder on the run.** `Exhibits.Integrated.lsched` is section 14's coerced arming with both fire passes, a second
pass of node 1 at the vault, then the large coin confirming and a third pass of node 1 that reads it; it is legal,
refined and assembly-checked. `Exhibits.Integrated.lrun` is a legal `Ladder.Execution` over every node retaining both
rungs (`Exhibits.Integrated.irc`) whose passes read what the matching fire passes read, `Ladder.readOf` at steps 7, 9,
11 and 14, with a median of 100 and then 200 supplied. Node 1 latches `r1` and releases the prefix from the base; at the
higher median it latches `r2` and releases `r2` alone; at the large coin no rung covers and the latch and floor stay.
Node 1 finalizes `r1`, where node 2's partial gives it two signers, and not `r2`, which only it signed. On a ladder of
the base alone the same reads release the base at step 7 and nothing at step 14, which is what those fire passes
withheld. The ladder's book (`Exhibits.Integrated.ibook`) is the run's at every coin the run reads
(`Exhibits.Integrated.ibook_agrees`) and adds the rungs' outputs.

**The composer on the run.** `Exhibits.Integrated.cbSched` runs the same arming at an instant whose large coin is an
immature coinbase confirmed at height 4, then moves the chain to tip 103. The composer reads each of node 1's
observations, with the run's guards and book and the node's authorized set (`Exhibits.Integrated.vaultAt`), and the
evidence `Exhibits.Integrated.cbPass`. The run's guards here give each outpoint the creator the evidence names
(`Exhibits.Integrated.csw`: coin 9 from the coinbase transaction 8, at height 4 on the backend), and are otherwise
section 14's. At the first it refuses the spend with `I` = 1 000 000 and clearing height 103,
before any request exists, while the node's verdict at the same read counts the coinbase, fails the Escape at coverage
and withholds it, as `WTC-6` and `DUR-22` require. At tip 103 the composer's pass is accepted and composes a spend of
both coins, which covers at that read. The Escape already registered still fails coverage there and no Escape partial
is in the inventory: the accepted pass is a new request, and nothing says it is signed, sent or included.

**What the run carries.** On these runs: checked request data to
registration: `Exhibits.EndToEnd.coerced_checked`, by section 14's equal trace, and with the ladder
`Exhibits.RungIngress.rung_run_checked`. Registration responses to the observer:
section 11's walks over this run's arming steps, now with one assembly check in both families. Release permission to
the partial effect and the inventory: `Recovery.no_premature_exposure`, and for the ladder `Ladder.inventory_provenance`
on a run whose reads are the composed run's. No ladder pass of a refined execution queues a partial
(`PreRelease.ladder_releases_nothing`); on the ladder-aware run the rung partials a ladder pass queues are
`RungRelease.inventory_provenance`'s third alternative (`RungRelease.EmittedRung`). Per-input deliveries to the held set: `Federation.held` in the class check
(`Assembly.checkOf`), and for a rung `RungIngress.held` on the composed run (`Exhibits.RungIngress.rung_held_on_run`)
beside `Ladder.held` on `Ladder`'s own run. Backend and exact-size checks to assembly: `Assembly.of_composed`.
Current-state authorization to submission: `Assembly.composed_submitted`. Inclusion: the explicit chain step. The Hot
ledger and its commitment-keyed accounting: section 14, unchanged.

**Observational compatibility.** The class check restricts which assemblies a run admits and changes no response,
work marker or addressed effect of any step. It reads nothing `Silence.pubNode` erases (`Assembly.guard_pub`), so it
adds no observation the walks do not cover. The ladder's run is its own and adds no step to the walks.

**Controls.** No new control. Five existing ones now also fail exhibits of this section: the two `DUR-13` T-clamp
plants, which move the coerced arming, fail `Exhibits.Integrated.clawback_walk_guard` and
`Exhibits.Integrated.ladder_on_run`; the plant that omits `I` from the additional check, the one that makes maturity
strict and the fire pass releasing past the verdict fail `Exhibits.Integrated.immature_then_accepted`.

**Integration failures and their class.** One, being repaired. On a ladder of the base alone the kernel's fire pass
and the ladder's pass agree (`Ladder.fire_release`). With rungs above the base the composed run could not carry them:
the kernel's candidate had one transaction, so a rung that an honest node's pass releases under `DUR-27` had no partial
effect, inventory row, delivery or possession on the composed run, and the kernel releases the base by section 13's
check, where `DUR-26`'s selection over the whole ladder may release nothing. That is the second class: the
representation excludes legal executions, and its repair is to give the kernel's candidate its ladder. The kernel's
ladder pass below is the first part of that repair: the kernel's candidate now holds its rungs, and a ladder pass
queues the partials of the rungs its step lists. No ladder pass of a `PreRelease.Execution` queues a partial
(`PreRelease.ladder_releases_nothing`), and on a federation execution checked by `Ingress.check`
(`Ingress.CheckedTrace`) none of an honest node's does, since that check hands the kernel no rung
(`Ingress.resident_no_rungs` with `Kernel.ladderPass_no_rungs`); the exhibits that queue rung partials start from a state with the rungs
written in (`Exhibits.LadderPass.withRungs`). The ladder-aware run below is the second part: it binds a ladder pass's release to `Ladder.release` at
the run's read (`RungRelease.releaseOk`), and the fire pass over the whole ladder below is the third: it withholds an
Escape's base where its ladder refuses it (`LadderRelease.releaseOk`). Checked ingress that registers the rungs and
possession over them below are the fourth: on a reachable run through that ingress a rung is released, delivered and
counted in the receiving node's possession (`Exhibits.RungIngress.rung_held_on_run`). Still open: no rung is assembled
or sent on the composed run, so until then a rung's finalization runs on `Ladder`'s own run, bound to the composed run
by its reads only (`Exhibits.Integrated.ladder_on_run`). No failure of the third class was found. The first-class failures on these runs stay section 14's
(`Exhibits.CommonRun.old_history_not_refined`) and section 17's (`Exhibits.Assembly.hot_old_broader`).

**The old boundary that changed.** Sections 15, 16 and 17 proved their results over instants and reads supplied to each
call, and section 14 left the ladder, the composer and the class checks off its run. The class checks and the send's
re-authorization now hold on the composed run (`Assembly.of_composed`), the ladder's read is the fire pass's
(`Ladder.readOf`) and agrees with the kernel's verdict on a ladder of the base alone, and both the ladder's passes and
the composer read the instants of one composed run.

**The kernel's ladder pass.** The third part of `bps-9oab.8`, base `90e8cf4`: `Kernel.Event.ladderPass`, beside the fire
pass, with no change to the fire pass, its verdict or any `Kernel.firePass_*` statement. Requirements read: `DUR-9`,
`DUR-10`, `DUR-19`, `DUR-21`, `DUR-27`, `NCH-23`, `SPN-36`, `SPN-38`. No protocol, ADR decision or guard value changes.

| Claim | Owner | Declaration | Domain, alphabet and premises |
| --- | --- | --- | --- |
| The kernel's candidate holds its ladder | `SPN-36` | `Kernel.Cand.above`, `Kernel.Cand.baseSig`, `Kernel.Cand.track`, `Kernel.Cand.ladder` | The rungs above the base with their user-signature hashes, registration-owned (`Kernel.born` keeps them and starts the latch and floor fresh); empty for a claw-back and for every candidate `Ingress.check` hands over |
| The ladder pass releases what its step lists | `DUR-27` | `Kernel.ladderPass`, `Kernel.ladderAt`, `Kernel.rungEffects`, `Kernel.ladderPass_effect` | Every rule value, environment and node: for an Escape-role candidate that is not hot and that the fire pass's due and `DUR-10` tests admit, the release `Env.ladder` lists under its id is its new latch and floor, and each listed rung above the base is queued once per input on that input's message, not hot. The base and an index past the ladder queue nothing; under `Kernel.PoisonGate.asserted` (the current rules) a poisoned node releases nothing and forces Lockdown; under `Kernel.PoisonGate.byLockOrder` the pass does not test poisoning. What the list holds is an input, as `Env.withheld` is |
| Nothing listed, nothing released | `DUR-27` | `Kernel.ladderPass_nothing`, `Kernel.ladderPass_no_rungs` | An empty `Env.ladder`: every candidate unchanged and no partial; candidates with no rung: no partial whatever is listed |
| The base-only refinement | `DUR-21` | `PreRelease.releaseOk`, `PreRelease.ladder_releases_nothing` | `PreRelease.Execution` admits a ladder pass only when it lists nothing, so its ladder passes queue nothing and change no candidate; sections 13 and 14 hold as before on every history with no ladder pass, and over the new alphabet only by excluding every listed release |
| A run checked by `Ingress.check` carries no rung | `DUR-8` | `Ingress.resident_no_rungs`, `Ingress.cand_above_origin` | Every honest node's candidates, at every state of a federation execution whose acceptances and claw-backs are checked: `Ingress.cand` and `Ingress.checkClawback` hand over no rung and no step adds one. So `Ingress.hot_binding` and `Ingress.no_exposed_quorum` keep their statements |
| SILENCE through the ladder pass | `DUR-1` | `Silence.ladderPass_pub` | Inside the walk, with the fire pass's premises: the per-candidate test factors through the projection (`Silence.release_factor`) and the rungs, latch and floor are public, so two coupled nodes write the same projection and queue the same partials |

**Statements changed, old and new.** Each changed statement says what it said before on every history with no ladder
pass; the old form is kept under a `_pre` name, proved from the new one or, for `Ingress.queued_cand_pre`, by the old
proof.
- `PreRelease.lift_safety` (`DUR-19`): new premise `hlad`, every ladder pass of the history lists nothing
  (`env.ladder = []`). The ground is compatibility with the old alphabet: no history the old statement covered takes a
  ladder pass, so the premise holds on each of them, and the old premise `hfire`, an exact equality on the fire pass's
  withheld list, does not reach the new event. The premise says the pass lists nothing, which is stronger than that it
  releases nothing: it also excludes a pass that lists a release and queues no partial
  (`Exhibits.LadderPass.base_only`), and such a pass can still write the latch and floor it lists: outside the
  asserted poisoned-node branch, for a non-hot Escape-role candidate with a matching entry that is due and passes
  `Kernel.releaseAuthorized` (`Kernel.ladderAt`). Old form:
  `PreRelease.lift_safety_pre`, with the premise that the history takes no ladder pass.
- `Assembly.lift_safety` (`DUR-19`): the same premise, since it lifts `PreRelease.lift_safety` through the class check.
  Old form: `Assembly.lift_safety_pre`.
- `PreRelease.releaseOk_lift`: the same premise for one step. Old form: `PreRelease.releaseOk_lift_pre`.
- `PreRelease.queue_only_firePass`: old conclusion `e = .firePass`; new `e = .firePass ∨ (e = .ladderPass ∧
  env.ladder ≠ [])`. Old form: `PreRelease.queue_only_firePass_pre`, at a step that is not a ladder pass.
  `PreRelease.inventory_provenance` keeps its statement: the refinement's ladder passes list nothing.
- `Ingress.queued_cand`: old conclusion, a queued input-0 row is a resident candidate's input-0 message with its
  class; new, that or the input-0 message of a rung above the base that a resident candidate holds, not hot. The old
  form fails at a ladder pass (`Exhibits.LadderPass.rung_not_base`). Old form: `Ingress.queued_cand_pre`, at a step
  that is not a ladder pass.

**Exhibits.** `Exhibits.LadderPass.rung_rows`: at node 1's state at step 7 of `Exhibits.Integrated.lsched`, where the
Escape is due and the fire pass releases its base, with two rungs written above the base, one spending two inputs, a
ladder pass listing rungs 0, 1 and 2 queues one partial per input of each rung above the base and none of the base,
the fan-out adds nothing to them, and the latch and floor become the listed ones. `Exhibits.LadderPass.nothing_listed`:
the fire pass's environment lists nothing and the pass changes nothing; a release listed for the Escape before it is
due, at step 4, queues nothing. `Exhibits.LadderPass.base_only`: on the composed run itself, whose Escape came through
checked ingress, a ladder pass listing every rung queues nothing, and the refinement admits one only when it lists
nothing. `Exhibits.LadderPass.rung_not_base`: the counterexample to the old form of `Ingress.queued_cand`.

**The ladder-aware run.** The fourth part of `bps-9oab.8`, base `41ab1be`: `BtcPolicy.RungRelease`, a refinement of the
sweep run beside `PreRelease`, with no change to any existing statement. Requirements read: `DUR-21`, `DUR-26`, `DUR-27`,
`DUR-30`, `WTC-15`, `SPN-38`. No protocol, ADR decision or guard value changes. The backend's instant now reports each
block's median feerate (`Sweep.Backend.medians`), read only here.

| Claim | Owner | Declaration | Domain, alphabet and premises |
| --- | --- | --- | --- |
| The median a pass reads | `DUR-30` | `RungRelease.medianOf` | The median of the block at the anchor of the observed instant's tip; none reported is `DUR-30`'s no pressure. The backend's report of it (`WTC-15`) is the instant's, as its confirmed coins are |
| The release a ladder pass must list | `DUR-27` | `RungRelease.readAt`, `RungRelease.entry`, `RungRelease.listed`, `RungRelease.releaseOk` | A ladder pass is admitted only when its `Env.ladder` is, for each Escape-role candidate of the acting node whose release names a rung, `Ladder.release` at that node's `Ladder.readOf` in the pass's state and history, at the observation's median, with every Escape's retained rungs in the read (`RungRelease.rungsOf`, so `DUR-22`'s pass leaves out every resident rung) and the rungs the candidate retains (`Kernel.Cand.above`) under its own id and its own latch and floor (`Kernel.Cand.track`); a list naming a release only where the node's Escape-role ids are distinct, which `Kernel.ids_nodup` gives under `Kernel.Rules.registration = .preserve`. A fire pass carries `PreRelease.failing` as before |
| The relation to the base's refinement | `DUR-21` | `RungRelease.to_pre`, `RungRelease.pre_iff`, `RungRelease.inventory_provenance_quiet` | A run whose ladder passes list nothing is a `PreRelease.Execution`; over a history whose ladder passes are taken where the computed release names no rung (`RungRelease.Quiet`) the two refinements are one, and the inventory result is `PreRelease.inventory_provenance`'s |
| Rung origin | `DUR-27` | `RungRelease.rung_origin`, `RungRelease.ladderAt_own`, `RungRelease.rung_authorized` | Every row an honest ladder pass adds is a rung above the base that an Escape-role candidate of that node retains, not hot, due and `DUR-10`-authorized, on that rung's message at the row's input, under its commitment, listed in that candidate's own release: its read had an observation, its verdict released a rung at or above this one, and this rung was admissible at that attempt. The kernel reads each candidate's own entry. A rung sharing the base's txid is expanded over the base's inputs by `Federation.others`, on that txid's messages |
| A refused rung | `DUR-27` | `RungRelease.refused_rung` | Every row the pass adds under an Escape-role candidate's commitment releases a rung index other than one that candidate's own predicate refuses at its read. Rungs are told apart by index: two rungs sharing a txid share their messages, which the theorem does not separate |
| Availability | `DUR-27` | `RungRelease.ladder_available` | At an honest node with distinct Escape-role ids, a ladder pass carrying the computed release is admitted whatever the environment's other fields |
| The inventory | `DUR-21` | `RungRelease.inventory_provenance`, `RungRelease.EmittedRung`, `RungRelease.no_premature_exposure`, `RungRelease.recovery_no_premature_exposure` | Every row names an extracted signer, or an honest signer that emitted it at a fire pass past the base's verdict (`PreRelease.Emitted`, unchanged) or at a ladder pass as a rung its candidate's own release listed; a signer outside the cumulative extracted set drops the first. On the composed run with custody, under `RungRelease.Checked` with the run's guards |

`PreRelease.inventory_provenance`, `PreRelease.no_premature_exposure` and `Recovery.no_premature_exposure` keep their
statements and their domain: they are the base's results over the base's refinement, which still excludes every listed
release. The ladder-aware results are new theorems beside them; base rows keep their rung-0 verdict.

**Exhibits.** `Exhibits.RungRelease.rung_on_run`: section 14's coerced arming with the Escape registered with both
rungs of section 16 above its base (`Exhibits.RungRelease.esR`, at `Kernel.accept`), then node 1's ladder passes at the
vault with a median of 100, at the vault with a median of 200, and at the large coin, each fire pass and ladder pass
carrying the value computed at its own state and history (`RungRelease.fill`). It is a legal run of the refinement
(`Exhibits.RungRelease.rung_run_execution`). At the first ladder pass the computed release latches `r1` and releases
the prefix from the base; at the second it latches `r2` and releases `r2` alone. The inventory under the Escape's
commitment is the two base partials of the fire passes and node 1's partials on `r1` and `r2`, none hot, and node 1's
Escape ends at latch 2 and floor 3. The base's refinement does not admit the run. `Exhibits.RungRelease.refused_rung_on_run`:
at the large coin node 1's predicate admits no rung, the computed release lists nothing, and a ladder pass listing
`r2` at the latch and floor it holds is refused.

**Controls.** One new: making `RungRelease.releaseOk` admit every ladder pass fails `Exhibits.RungRelease.refused_rung_on_run`
alone, with `RungRelease.escape_nodup`, `RungRelease.ladderAt_own` and `RungRelease.pre_iff` stubbed, whose proofs read the
check. Three existing ones now also reach this part: the two `DUR-13` T-clamp plants, which move the coerced arming,
also fail `Exhibits.RungRelease.rung_on_run`, so each count rises by one; the plant that admits a forged partial under
any signer also stubs `RungRelease.inventory_provenance`, whose proof reads that guard as
`PreRelease.inventory_provenance`'s does.

**An integration failure found.** The second class, repaired by the next part (the fire pass over the whole
ladder): the fire pass judges an Escape with rungs by
the base alone (`PreRelease.failing`), while `DUR-21` establishes admissibility over the whole ladder before any partial
of it. Where the ladder's attempt fails and the base's own passes, as when the selected rung's ancestry fails, the
fire pass releases a base partial that `DUR-21` withholds. The model's honest exposure is then larger than the
protocol's, so no safety result is overstated by it, but the base rows' verdict is not `DUR-21`'s for an Escape with
rungs. The requirements do not conflict: an inadmissible base is not a failed step, and `DUR-27` releases from the
lowest admissible rung.

**Remaining exclusions.**
- Which release a ladder pass lists is checked on the ladder-aware run (`RungRelease.releaseOk`), not on
  `PreRelease`'s or `Assembly`'s: a rung's possession and finalization run on `Ladder`'s own run, bound to the
  composed run by its reads and not by its inventory or possession, and a rung's assembly is `Assembly.rungCheck` over
  those reads (section 17). `Ingress.check` hands the kernel no rung, so the exhibits register the rungs at
  `Kernel.accept` or write them into the state; `RungIngress.check`'s acceptance is that registration (the part on
  checked ingress below).
- The base's refinement and its results, `Recovery.no_premature_exposure` included, establish no `DUR-21`
  authorization for a rung release: they admit only ladder passes that list nothing. The ladder-aware results do, for
  the rung's own release, and `Exhibits.RungIngress.rung_run_checked` puts this part's run through checked ingress.
- On this run the fire pass judges an Escape with rungs by the base alone (the integration failure above); the
  next part's run does not.
- A resident rung's replacement: `Sweep.authorizedAt` collects the registry's base txids alone, so once a rung is
  resident, a higher rung's selection reads it as the replacement of an unauthorized resident (`Ladder.replacesOf`)
  and its ancestry fails. The exhibit's mempool stays empty; computing rung authorization from retained candidates
  is open.
- On a run checked by `Ingress.check` a ladder pass queues no partial (`Ingress.resident_no_rungs` with `Kernel.ladderPass_no_rungs`),
  but it is not inert: outside the asserted poisoned-node branch it can write the listed latch and floor of a non-hot
  Escape-role candidate with a matching entry that is due and passes `Kernel.releaseAuthorized` (`Kernel.ladderAt`),
  and under `Kernel.PoisonGate.asserted` a poisoned node instead forces Lockdown. `Kernel.Cand.track` quotes `SPN-36`'s "monotone", and nothing on the composed run
  enforces or proves it.
- On `Ladder`'s own run the median reading and the rungs each node retains are supplied to each pass; on the
  ladder-aware run they are the observation's and the candidate's.
- The composer is the Operator's program, beside the run: it reads the run's instants and composes no request the run
  then registers.
- SILENCE on the refined run: one instant, authorized set, claw-back list and possession in both families is the premise
  `PreRelease.failingAt_pub` and `Assembly.guard_pub` take, and section 10's stop at node 1's first fire pass remains.
- The observed instant's freshness, `OPR-82`'s header checks (`Coinbase.Creating.active`), each transaction's legacy
  length and each outpoint's value, the backend's package verdict, and no runtime or deployment result.

**The fire pass over the whole ladder.** The fifth part of `bps-9oab.8`, base `7a0bbaf`: `BtcPolicy.LadderRelease`, a
refinement of the sweep run beside `RungRelease`, with no change to any existing statement. It repairs the integration
failure above. Requirements read: `DUR-21`, `DUR-26`, `DUR-27`. No protocol, ADR decision or guard value changes.
`Kernel.firePass` and its results are unchanged: the verdict stays the step's input there.

| Claim | Owner | Declaration | Domain, alphabet and premises |
| --- | --- | --- | --- |
| The verdict a fire pass must carry | `DUR-21` | `LadderRelease.baseOk`, `LadderRelease.refuses`, `LadderRelease.withheldAt`, `LadderRelease.releaseOk` | A fire pass is admitted only when its `Env.withheld` lists the ids of the acting node's Escape-role candidates whose base's verdict fails, as `PreRelease.failing` reads it, or that retain rungs above the base and whose ladder, at the candidate's own read (`RungRelease.readAt`) and latch, has no observation, does not release a rung, or refuses the base at that attempt. A ladder pass carries `RungRelease.ladderOk` |
| The relation to the earlier refinements | `DUR-21` | `LadderRelease.failing_sub`, `LadderRelease.withheldAt_bare`, `LadderRelease.rung_iff`, `LadderRelease.admits_ladder`, `LadderRelease.EmittedBase.pre` | Every id the base's verdict withholds is withheld here; where the acting node's Escape-role candidates retain no rung the two verdicts are one, and over a history whose fire passes are all taken there (`LadderRelease.Bare`) the run is exactly `RungRelease`'s; a ladder pass admitted here is admitted there; a base row emitted here carries `PreRelease.Emitted`'s rung-0 verdict |
| Base origin | `DUR-21` | `LadderRelease.base_origin`, `LadderRelease.baseOk_iff` | Every row an honest fire pass adds is a released candidate's, on its transaction's message at the row's input, under its commitment; for an Escape-role candidate the base's verdict released rung 0 and, when it retains rungs, the ladder's verdict at its own read and latch released a rung, with an observation and the base admissible at that attempt. No premise that the release was authorized |
| A refused ladder | `DUR-21` | `LadderRelease.refused_base` | At an admitted fire pass, for an Escape-role candidate that retains rungs and whose ladder refuses its base, every row the pass adds under its commitment is a candidate's that is not in the Escape role, such as the spend sharing the commitment id |
| Availability | `DUR-21` | `LadderRelease.fire_available` | At an honest node a fire pass carrying the computed verdict is admitted whatever the environment's other fields |
| The inventory | `DUR-21` | `LadderRelease.inventory_provenance`, `LadderRelease.EmittedBase`, `LadderRelease.no_premature_exposure`, `LadderRelease.recovery_no_premature_exposure` | `RungRelease`'s alternatives with the fire pass's strengthened to `LadderRelease.EmittedBase`; on the composed run with custody under `LadderRelease.Checked` with the run's guards |

`RungRelease`'s results keep their statements and domain; the results here are new theorems beside them. Base rows keep
their rung-0 verdict and gain the ladder's.

**Exhibits.** `Exhibits.LadderRelease.base_withheld_on_run`: nodes 1 and 2 take the coerced request with the Escape
retaining both rungs and arm; node 2 takes a ladder pass at the vault with a median of 100 before its first fire pass,
which latches `r1` and queues `r1`'s partial; a second coin of 450 000 confirms and node 2 fires reading it. There the
base is admissible and `r1` is not: the base's verdict withholds nothing, the ladder's selection fails at the latch
(`PreRelease.Stage.latched`), and the verdict over the whole ladder withholds the Escape, so the inventory under its
commitment holds node 2's `r1` partial alone. On the same history `RungRelease`'s refinement fires with nothing
withheld and its inventory gains node 2's base partial, and that fire pass is refused here. It is a legal run of the
refinement (`Exhibits.LadderRelease.base_run_execution`). `Exhibits.LadderRelease.base_on_run`: the previous part's
schedule (`Exhibits.RungRelease.rung_on_run`), whose fire passes release both base partials, is a legal run here too.

**Controls.** One new: dropping the ladder's disjunct from `LadderRelease.refuses` fails
`Exhibits.LadderRelease.base_withheld_on_run` alone, with `LadderRelease.base_origin` and `LadderRelease.refused_base`
stubbed, whose proofs read the disjunct. Six existing ones now also reach this part: the plant whose fire pass releases
past the pre-release verdict, the plant whose selection ignores the latch and the two `DUR-13` T-clamp plants, which
move the coerced arming, also fail that exhibit, so each count rises by one; the plant that admits every ladder pass also stubs `LadderRelease.releaseOk_iff_bare`, whose ladder case reads
`RungRelease.releaseOk`; and the plant that admits a forged partial under any signer also stubs
`LadderRelease.inventory_provenance`, whose proof reads that guard as `RungRelease.inventory_provenance`'s does.

**Remaining exclusions.**
- The base's release is the kernel's `released` bit, made once; it is not tied to `SPN-38`'s cursor, and a ladder
  pass's release names the base without queueing it (`Kernel.rungEffects`).
- `Ingress.check` hands the kernel no rung, so the exhibit registers the rungs at `Kernel.accept`, as `RungIngress.check`
  registers them (the next part); a rung's assembly and send are not on this run.
- The earlier part's other exclusions stand.

**Checked ingress with the ladder, and possession over it.** The sixth part of `bps-9oab.8`, base `295b1ac`:
`BtcPolicy.RungIngress`, beside `BtcPolicy.Ingress` and `Federation.held`, with no change to any existing statement.
`Ingress.check`, `Ingress.CheckedTrace`, `Ingress.resident_no_rungs`, `Ingress.hot_binding`,
`Ingress.no_exposed_quorum`, `Federation.storable` and `Federation.held` keep their statements and their domain.
Requirements read: `SPN-27`, `SPN-32`, `SPN-36`, `CHN-29`, `NCH-24`, `DUR-8`, `DUR-28`. No protocol, ADR decision or
guard value changes.

| Claim | Owner | Declaration | Domain, alphabet and premises |
| --- | --- | --- | --- |
| Checked ingress registers the ladder | `SPN-32` | `RungIngress.check`, `RungIngress.withLadder`, `RungIngress.rung`, `RungIngress.check_accepted`, `RungIngress.check_other` | A SpendRequest whose Escape and rungs each carry a supplied user-signature hash (`RungIngress.Signed`, `CHN-29`): `Ingress.check` on the request without the hashes, and on acceptance the Escape's candidate with each rung's transaction (`Ingress.tx`) and hash in the request's order, and the base's hash. Every other verdict is `Ingress.check`'s |
| What an acceptance carries | `SPN-27` | `RungIngress.accepted_validates`, `RungIngress.accepted_rungs`, `RungIngress.accepted_classed` | `Ingress.check` accepted the plain request with the same spend; at most three rungs, each admissible and through gate 25, so each is the transaction of an admissible escape-class member; the spend retains no rung |
| The relation to `Ingress.check` | `SPN-32` | `RungIngress.check_strip`, `RungIngress.check_ofPlain` | Dropping the ladder from an accepted Escape gives `Ingress.check`'s acceptance; a request with no rung and the base hash 0 is checked exactly as before |
| A checked run with rungs | `DUR-8` | `RungIngress.CheckedTrace`, `RungIngress.resident_classed`, `RungIngress.step_classed` | Every federation execution whose honest acceptances are this check's and whose claw-backs are checked: every resident candidate of an honest node, at every state, is classed and every rung it retains is escape-class |
| The message binding with rungs | `DUR-8` | `RungIngress.hot_binding`, `RungIngress.no_exposed_quorum` | The same executions with a collision-free transaction identity: `Federation.HotBinding` for an admissible hot-class member's input-0 message, through `Ingress.queued_cand`'s rung alternative; `Federation.no_exposed_quorum` with those premises in place of the binding. What stays: `hr`, `noNormal`, `bound` |
| Possession over the ladder | `DUR-28` | `RungIngress.ownSigs`, `RungIngress.storable`, `RungIngress.held`, `RungIngress.held_origin` | The node's own signature on every input of every rung it retains and the partials its store took on any of them, the store finding the rung by txid and testing the input's range, kept while their candidate stays resident; on every federation execution each signature is the node's own or a partial of the inventory. A rung's count reads only its own transaction's records (`Ladder.quorum_own_rung`) |
| The relation to `Federation.held` | `DUR-28` | `RungIngress.held_sub`, `RungIngress.held_bare`, `RungIngress.held_plain` | It contains `Federation.held`; it equals it where no candidate retains a rung at the end or at any frame of the node's history, so at every honest node of every execution checked by `Ingress.check` |

**Exhibits.** `Exhibits.RungIngress.ladder_registered`: the check accepts `Exhibits.Ladder.reqL` with the base's hash 0
and the rungs' 11 and 12, giving `req0`'s spend and the Escape `Exhibits.RungRelease.esR`, the very candidate the
earlier rung runs register at `Kernel.accept`; a rung missing `CHN-15`'s sequence refuses the request, and with no
rung the check accepts `req0`'s pair as `Ingress.check` does. `Exhibits.RungIngress.rung_held_on_run`:
`Exhibits.RungRelease.rung_on_run`'s schedule with node 1's `r1` partial delivered to node 2 at the end is a legal
run of the fire pass over the whole ladder, its acceptances are this check's, and node 2's Escape retains both rungs,
so `Ingress.CheckedTrace` cannot hold of it. Node 2 then holds two signers on `r1`'s input, its own and node 1's,
which is `DUR-28`'s quorum at a threshold of 2 over its possession on the ladder; `Federation.held` holds no `r1`
record there; on `r2` node 2 holds only its own signature; a partial on a rung it does not retain is not stored.
`Exhibits.RungIngress.rung_run_checked` and `Exhibits.RungIngress.rung_run_hot_binding` instantiate
`RungIngress.CheckedTrace` and `RungIngress.hot_binding` on that run.

**Controls.** One new: a store test that reads a candidate's base alone fails `Exhibits.RungIngress.rung_held_on_run`
alone, with nothing stubbed. Two existing ones now also reach this part: the two `DUR-13` T-clamp plants, which move
the coerced arming, also fail `Exhibits.RungIngress.rung_held_on_run`, so each count rises by one.

**Remaining exclusions.**
- Of `NCH-24`'s store test, `RungIngress.storable` keeps what `Federation.storable` keeps, "the rung is found by txid"
  and the input's range, over the ladder. It does not test the signer's range: a partial forged under an extracted
  key outside the key set is stored, and only the count's key filter (`Authority.signers`) drops it. It does not read
  the candidate's expiry, so a partial can be stored against an expired candidate not yet pruned.
- `NCH-24`'s "the user-signature hash matches": a partial row (`Kernel.Exp`) carries no user-signature hash, so
  `RungIngress.storable` does not compare one, and two nodes retaining one rung txid under different hashes store
  each other's partials on it. The comparison is `Ladder.stores`', on `Ladder`'s own run. The hash itself is supplied
  with the request and not computed from the user's signatures, which the decoded members do not carry.
- `SPN-32`'s "The resident Escape MUST also have the same **ordered rung txids**, including the empty list" on a
  repeat: `Kernel.pairAdmits` compares a resident's transaction, class, expiry and pair, not its rungs, so a repeat
  whose rungs differ from the resident Escape's is retained as compatible, where `SPN-32` refuses it as a conflicting
  resident commitment. Through `Ingress.check` every ladder is empty and the comparison holds; through this check it
  is not represented. The retained resident keeps its own ladder, so no rung the repeat carries is registered or
  released, but the repeat's response is the model's, not `SPN-32`'s.
- The kernel's own store (`Kernel.receivePartial`, `Kernel.Cand.heldSigners`) and the assembly's possession
  (`Assembly.checkOf` over `Federation.held`) read the base alone. No rung is assembled or sent on the composed run.
- `CHN-14`–`CHN-16`'s relations between the rungs are not checked, as in `BtcPolicy.Ingress`.

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
| `Exhibits.PreRelease.bypass_not_refined` | That every sweep history, releasing whatever the backend shows, is one the pre-release check admits |
| `Exhibits.CommonRun.old_history_not_refined` | That section 10's history, releasing before any read, is one the pre-release check admits |
| `Exhibits.Coinbase.later_read_refuses` | That the composer's additional check, passed at one read, is the node's coverage at another |
| `Exhibits.Coinbase.later_coinbase_no_bound`, `Exhibits.Coinbase.stalled_chain_no_progress` | That the reported maturity height bounds how long a spend can be refused, or that waiting reaches it |
| `Exhibits.Ladder.tops_out` | That the selected rung pays the fee a pressure reading asks for |
| `Exhibits.Ladder.possession_not_inventory`, `Exhibits.Ladder.split_across_rungs` | That a quorum in the inventory, or signatures pooled across rungs, lets a node finalize |

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
| Pre-release authorization, proved as `PreRelease.release_origin`, `PreRelease.inventory_provenance` and `PreRelease.no_premature_exposure`, with `PreRelease.execution_iff` and `PreRelease.lift_safety` | The fire pass's release regardless of the backend, now gated per candidate by the verdict the acting node computes from its latest observation and history. Premises kept: the observed instant's freshness, each transaction's legacy length and outpoint values, the ladder beyond the base | `Exhibits.PreRelease.base_sweep`, beside a failure per check (`Exhibits.PreRelease.coverage_at_bound`, `Exhibits.PreRelease.fee_at_max_vsize`, `Exhibits.PreRelease.missing_prevout_withholds`) and `Exhibits.PreRelease.bypass_not_refined` |
| Pre-release authorization on the composed run, proved as `Recovery.to_prerelease` and `Recovery.no_premature_exposure`, with `PreRelease.failingAt_pub` | Section 10's release before any read, now gated per candidate on the composed run, custody, death, latch and Recovery steps beside it. Premises kept: those of section 13; for SILENCE, one instant and one authorized set in both families | `Exhibits.CommonRun.coerced_refined` and `Exhibits.CommonRun.ordinary_refined`, beside `Exhibits.CommonRun.unusable_refined`, `Exhibits.CommonRun.prior_exposure_survives` and `Exhibits.CommonRun.old_history_not_refined` |
| Pre-release authorization over the ladder, proved as `Ladder.select_sound`, `Ladder.inventory_provenance`, `Ladder.refused_not_released` and `Ladder.common_base_fallback`, with `Ladder.verdict_one_rung` | Section 13's base-only verdict, now over the optional ladder, with the latch, `SPN-38`'s cursor and finalization from possession. Premises kept: the reads, supplied per pass and not bound to the composed run; `CHN-16`'s relations between rungs; for the fallback, the base's quorum in the finalizing node's possession | `Exhibits.Ladder.valid_ladder`, `Exhibits.Ladder.passes_progress` and `Exhibits.Ladder.stripped_fallback`, beside `Exhibits.Ladder.refusal_ladder`, `Exhibits.Ladder.latched_inadmissible`, `Exhibits.Ladder.refused_inside_prefix` and `Exhibits.Ladder.user_sig_mismatch` |
| The extensions on the composed run, proved as `Assembly.of_composed`, `Assembly.composed_submitted`, `Ladder.fire_withholds`, `Ladder.fire_release` and `Assembly.guard_pub` | The ladder's reads, the class checks and the composer's instants, each supplied per call; now the composed run's own. Premises kept: the median reading and retained rungs; the check's guards equal to the run's; the backend's package verdict; rung releases on the composed run from an unchecked list, which the refinement admits only when empty; for SILENCE, one instant, authorized set, claw-back list and possession in both families | `Exhibits.Integrated.ladder_on_run`, `Exhibits.Integrated.immature_then_accepted` and `Exhibits.Integrated.common_assembled`, beside the unusable history's refused assembly and the refusals in `Exhibits.Integrated.immature_then_accepted` |
