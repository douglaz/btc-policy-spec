# Milestone 3 bounded finding triage

Baseline: `8b123b35ce3ae69f793f99f72781db15f902683a`; see the [baseline card](milestone-3-baseline.md).
This is preparation only. No policy is adopted and no finding is closed. No fresh validation was run.
Finding status comes from [the selected entries in the findings ledger](../../16-open-findings.md#findings);
task status below is a bounded reading of [the separate task ledger](../../.beads/issues.jsonl).
An F-number identifies a design finding; a `bps` id identifies work. Their statuses are not interchangeable.

## Selected findings

Every row is **open** at this baseline. No selected finding is resolved since baseline. The older scheduling
holds and their reconciliation are recorded separately below; they do not change these classifications.

| Finding | Evidence at the baseline | Existing task | Next bounded sources |
| --- | --- | --- | --- |
| F48 — open | The finding says: “The node-side rule — refuse, ignore, or verify when present — is unstated”. Under `composeEvery lim txid s = .ok q`, `Feasibility.refuse_refuses_composed` concludes `s.bounded lim .refuse q = false`. `Exhibits.Feasibility.f48_moves_the_verdict` uses its fixed `largeVault` and `lim`: the stripped request is bounded under `ignore` and `verify`, while every request fails `nodeOk` under `refuse`. This compares readings; it selects none. | `bps-xmq1.9`, deferred | The F48 source list below; [proof boundaries §9](proof-boundaries.md#9-fast-exit-feasibility). |
| F1 — open | `Exhibits.Feasibility.dust_stops_composer_only` retains a bounded request despite composer refusal; `Exhibits.Feasibility.fragments_infeasible` and `Exhibits.Feasibility.toxic_infeasible` refute every bounded request in their fixed admissible states. `Feasibility.feasible_iff_best` takes `Feasibility.CountOnly`; it is not an unconditional selection remedy. Wire sizes remain supplied. | `bps-xmq1.9`, deferred | [F1](../../16-open-findings.md#findings), [§9](proof-boundaries.md#9-fast-exit-feasibility), `Feasibility.Limits`, `Feasibility.CountOnly`, `Feasibility.feasible_iff_best`, and the F48 size-contract sources below. |
| F2 — open | `Exhibits.Feasibility.prior_spend_composer_refuses` retains a request the composer cannot build; `Exhibits.Feasibility.deep_chain_infeasible` retains an admissible state without a bounded request. Both are fixed abstract backend reads, not a discovery implementation. No bounded discovery mechanism is selected. | `bps-xmq1.9`, deferred | [F2](../../16-open-findings.md#findings), [§9](proof-boundaries.md#9-fast-exit-feasibility), `OPR-39` in [the composer section](../../17-operator-program.md#the-composer-and-its-chain-view), `DUR-22`, `WTC-24`, and those exhibits. |
| F3 — open | `Progress.f3_blackhole` retains the freshness outage with delivery at every slot. More delivery cannot supply `Progress.envelopeFits`; `Progress.received_within` takes it as well as bounded service. No decay or message exception is selected. | `bps-xmq1.10`, deferred | [F3](../../16-open-findings.md#findings), [§8](proof-boundaries.md#8-progress), `Progress.f3_blackhole`, `Progress.received_within`, `NCH-12`, `NCH-13`, `NCH-38` in [the channel](../../06-node-channel.md). |
| F4 — open | `Progress.f4_no_arming` retains failure despite relays at every slot; `Progress.f4_log_outage` places the log latch arbitrarily far ahead, requiring an expiry signed against the excursion. A positive window result takes the high-water below expiry (`Progress.window_open_below_latch`). No split or replacement of that authority is selected. | `bps-xmq1.10`, deferred | [F4](../../16-open-findings.md#findings), [§8](proof-boundaries.md#8-progress), those declarations, `SPN-12`/`SPN-13` in [the spend lifecycle](../../04-spend-lifecycle.md), `NCH-36`/`NCH-37` in [the channel](../../06-node-channel.md). |
| F13 — open | `Progress.f13_starved` and `Progress.f13_postponed` retain unbounded Lockdown delay. `Progress.latch_within` needs bounded driver service and the comparison at its own sample; `Progress.latch_within_of_read` instead needs the ratchet having read `T`. [§8](proof-boundaries.md#8-progress) states: “A slot is a critical section, not a second.” Possession in §33 supplies no runtime bound. | `bps-xmq1.10`, deferred | [F13](../../16-open-findings.md#findings), [§8](proof-boundaries.md#8-progress), [§33](proof-boundaries.md#33-possession-on-the-expiry-aware-lifecycle-run), those declarations, `SEC-11` in [security](../../12-security-requirements.md) and `DUR-15` in [duress](../../05-duress-and-lockdown.md). |

## Next F48 source list

Keep user signing, wire transformation, node ingress, exact-transaction/signature validation and backend observation
as distinct stages. Read these sources before preparing the decision record:

- [CHN-22](../../02-onchain-contract.md): “Every input of every PSBT a user signs MUST carry its **full previous transaction**”.
- [OPR-35 and OPR-46](../../17-operator-program.md): “Two size bounds, both refused BEFORE allocation”;
  “Every `non_witness_utxo` is stripped from the WIRE PSBTs after verification”.
- [SPN-25](../../04-spend-lifecycle.md): “require the PSBT's `witness_utxo` script and value to equal the chain's”; read
  its confirmed-prevout premise and absent/unconfirmed branch together.
- [API-4/API-6](../../07-node-api.md) and [NCH-10](../../06-node-channel.md), for the body and envelope bounds.
- [`Feasibility.refuse_refuses_composed`](../../tools/formal/BtcPolicy/Feasibility.lean) and
  [`Exhibits.Feasibility.f48_moves_the_verdict`](../../tools/formal/BtcPolicy/Exhibits/Feasibility.lean), with [§9](proof-boundaries.md#9-fast-exit-feasibility).

The missing node-side rule is an open choice, not an adopted refusal requirement conflicting with stripping.
Choosing an incompatible reading or amending an existing rule needs an owner decision. This record stops before that choice.

## Task dispositions and reconciliation

The task descriptions still say “Held until the owner schedules it” for `bps-xmq1.9`, `bps-xmq1.10` and
`bps-xmq1.11`; each is **deferred**. These older scheduling holds **require reconciliation** independently of the
findings' open status. A separately recorded `bps-xmq1.9` comment dated 2026-11-23 now supersedes its hold for bounded
record preparation only, retaining deferred status for downstream policy work pending the owner's choice. That
reconciliation adopts no policy. This session prepares only these research records; no tracker was written here.
The holds on clock work and external evidence remain; this record schedules neither remedies nor experiments.

`bps-8bbx.2` is **in_progress**, with landed receipt tranches and remaining lifecycle SILENCE. Its older blanket
hold must be read with its later scheduling and completion comments. The latest landed scope is [§31's receipt step](proof-boundaries.md#31-silence-over-the-receipt-step-on-one-domain),
not whole-lifecycle SILENCE; [§30](proof-boundaries.md#30-the-expiry-aware-receipt-on-the-lifecycle-run) owns the execution.
`bps-xmq1.11` remains the deferred evidence-boundary task, not authority to infer implementation or deployment assurance.

| Existing follow-up | Verified disposition | Bounded evidence or remaining work |
| --- | --- | --- |
| `bps-xmq1.20` | Closed; keep closed | [Second milestone review](proof-boundaries.md#the-second-milestones-review): nonempty inputs and distinct contributor keys are now named in §27 and the possession entry rows. |
| `bps-xmq1.21` | Open | [§33](proof-boundaries.md#33-possession-on-the-expiry-aware-lifecycle-run): ladder-pass base possession has no exhibit. |
| `bps-xmq1.22` | Open; records require reconciliation | [§30](proof-boundaries.md#30-the-expiry-aware-receipt-on-the-lifecycle-run) states `ReceiptLifecycle.reregister_refused` per request; the [contract's *Lifetimes* paragraph](receipt-lifecycle-contract.md) still describes the stronger run-level form. Leave that amendment to this existing task. |
| `bps-xmq1.23` | Open | §33's envelope-label premise remains supplied; derive it under named premises or record the obstruction. |
| `bps-xmq1.24` | Open | §33 lacks split-signer evidence on the expiry-aware layer above the existing fixtures' threshold; retain `Exhibits.Ladder.split_across_rungs`. |
| `bps-xmq1.25` | Open | [§32](proof-boundaries.md#32-the-release-quota-on-the-expiry-aware-lifecycle-run): `ReceiptQuota.inputs_inv` and `ReceiptQuota.pass_count_checked` lack their own checked-run exhibit on the layer. |

## Separate boundaries

[F69](../../16-open-findings.md#findings) remains separate: “Open: whether a deployment needs anything beyond waiting.”
Its adopted maturity treatment is recorded in [§15](proof-boundaries.md#15-the-composers-immature-coinbase);
it is neither a toxic-parent remedy nor a decision adopted here.

[ADR-0022 decision 3](../adr/0022-the-escape-class-is-pin-less.md#decisions) says: “No minimum input count and no disjointness”.
Its consolidation resolution remains closed; F1's remaining topology question does not reopen it. No duplicate task is needed.
