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
| accounting | Federation acceptance to the admission premises | `bps-uaer.14`, `bps-uaer.15` |
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

**Excluded.** `POL-20` says "MUST NOT be presented as a bound on funds completing or lost in an
arbitrary rolling window".

| Premise | Class | Status |
| --- | --- | --- |
| `hnd`, duplicate-free cohort ids | Bridge | Caller's list; accounting |
| `hamt`, one amount per commitment across cuts | Bridge | At the candidates `Kernel.accept` receives, `Ingress.one_amount_per_commitment`, which takes a collision-free commitment id (Outside); that every row of a cut comes from a checked acceptance is accounting |
| `hinv`, each cut's ledger within the cap | Protocol | One node derived; linking a cut to a run is accounting |
| `hcohort`, `q` or more counted cuts per spend | Protocol | One node's count follows from `Ledger.countsAt_of_sysRun`; the cross-node count is accounting |
| `Ledger.countsAt_of_sysRun`'s `hs`, `hr`, the guard values | Protocol | Discharged at the current values by `Exhibits.HotLedger.countsAt_of_sysRun_with_current` |
| Its `hsplit`, `ha`, `hfresh`, `hprune`, the run holds an admission of this spend with no charge at its check, and keeps the row through every prune | Protocol | Given; accounting |
| Its `hwin`, that admission inside the cut's trailing interval | Environment | Retained |
| Its `hm`, `Ledger.MonotoneHotClock` | Environment | Retained |
| The cuts are exactly the honest nodes, with `q` and the length as `t − c` and `n − c` | Environment | Retained |

**Positive:** `Ledger.bridge_nonvacuous`, hand-seeded rows;
`Exhibits.HotLedger.composed_row_counted_by_theorem_with_current`, a composed run of one node.
**Negative:** `Ledger.rerun_exceeds_cap` and `Ledger.f61_per_spend_conclusion_false`, both hand-seeded;
`Exhibits.HotLedger.adr0014_refutes_completion_bound`, against the completion reading.
`Exhibits.HotLedger.f63_twins_end_charging_nothing` keeps charge and authority apart and does not
refute this theorem.

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
| One shared trace, with peer relays held equal | Bridge | Under one fixed exogenous schedule, discharged by `FedSilence.fed_silence` and `FedSilence.fed_silence_fresh`: the inventories, equal at the initial states, stay equal in both runs, and from a `Federation.Fresh` start the relays and partials a node receives come from the composed run. An adaptive observer and per-destination observation stay open |
| The stop at `Silence.wfEvent` | Bridge | ingress |
| `SEC-10`'s "release-history premise" and "digest premise" | Outside | Retained |
| A coordinator honest until the wrench (`SEC-10`) | Environment | Retained |
| `DUR-1`'s "no record of either PIN from any source" | Environment | Retained |

**Positive:** `Exhibits.TwoRun.silence_on_armTrace`, whose prefix ends at the arm.
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

**Owner:** `CHN-4`, `CHN-10` and `SEC-54`. **Theorem:** none. `SEC-54` says "No theorem carries the rest
of this two-key theft" and "No theorem carries this no-Recovery".

**What exists.** No event of `Kernel.Event` authorizes a Recovery spend, and no module models a coin's
maturity together with key custody. `Timelock.nsequence_derived` is the lock's encoding,
`Alerts.classify_recovery_iff` reads the branch from a witness, and
`Exhibits.WatchtowerAlerts.recovery_never_swallowed_with_current` is detection. None is authority.

| Premise a future theorem would take | Class | Status |
| --- | --- | --- |
| Each coin's maturity, read from its own chain history | Protocol | progress |
| Possession of the required recovery keys | Outside | Retained |
| The descriptor and its network (`OPS-23`) | Environment | Retained |
| Inclusion in an admissible chain history | Environment | Retained |

**Exhibits.** None retained for authority, positive or negative.

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
| Federation admission | `hinv`, `hcohort`, for honest cuts | A run whose reservations produce the cuts `Ledger.bridge_nonvacuous` seeds by hand |
| Recovery composition | The rows of section 7 | A mature coin with custody held, beside not-yet-mature and missing-custody runs |
