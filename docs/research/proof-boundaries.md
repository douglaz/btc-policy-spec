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
`Federation.Execution` (`FedSilence.lrun_execution`); `Exhibits.Admission.run_execution` is that for the positive run.

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
one checked spend, counted at all three cuts (`Exhibits.Admission.run_cuts`).
**Negative:** `Ledger.rerun_exceeds_cap` and `Ledger.f61_per_spend_conclusion_false`, both hand-seeded;
`Exhibits.HotLedger.adr0014_refutes_completion_bound`, against the completion reading. Failing
siblings of the derivations: `Exhibits.Admission.collision_splits_amount` (`hamt` without a
collision-free commitment id), `Exhibits.Admission.seeded_ledger_breaks_premises` (`hinv` and
`hamt` from a hand-seeded start ledger), `Exhibits.Admission.refunded_not_counted`,
`Exhibits.Admission.retry_not_fresh` and `Exhibits.Admission.backward_clock_uncounts` (a
reservation refunded, a retry that places none, and a cut sample behind the node's own, each
uncounted).
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
| One shared trace, with peer relays held equal | Bridge | Under one fixed exogenous schedule, discharged by `FedSilence.fed_silence` and `FedSilence.fed_silence_fresh`: the inventories, equal at the initial states, stay equal in both runs, and from a `Federation.Fresh` start the relays and partials a node receives come from the composed run. Against an observer that picks each step from its own run's observations, discharged by `FedSilence.fed_silence_adaptive` and `FedSilence.fed_silence_adaptive_fresh`. Each step's messages are compared per destination, by shape (`FedSilence.FObs`); no theorem gives their bytes, and `FedSilence.frame_preimage_length` gives an envelope preimage's length only from its payload's |
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
`Exhibits.FedSilence.hidden_state_reader_leaks` is a scheduler that reads node 1's arm bit and so
distinguishes the families; it is not a `FedSilence.Observer`, the type `FedSilence.fed_silence_adaptive`
takes.
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
this run. Fast-exit feasibility is section 9; Recovery is `bps-uaer.18`.

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
| Recovery composition | The rows of section 7 | A mature coin with custody held, beside not-yet-mature and missing-custody runs |
