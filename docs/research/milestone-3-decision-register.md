# Milestone 3 decision register

This record consolidates decisions and queues work; it changes no rule and closes no finding.
Evidence links below are pinned to repository base
`36d37d6e001209d9a058e1d4b04a9aec49b6e7db`; the original evidence baseline is
`8b123b35ce3ae69f793f99f72781db15f902683a`. F48's later authority is the direct owner
decision below. Earlier records' pending-choice language
and historical comparisons must be interpreted through this register, not as current authority.

## Recorded authority

The F48 pick below is the owner's direct decision of 2026-11-24, withdrawing the prior
option-1 pick. The other picks retain their acceptance under the owner's standing panel
rule of 2026-11-05; the owner may overrule them before landing. Acceptance authorizes only
the stated scope.

| Pick | Authority and record | Exclusions |
| --- | --- | --- |
| F48: forbid `non_witness_utxo` in node `/sign` PSBTs at existing decode steps; accept absence subject to other checks. | **Direct owner decision, 2026-11-24:** “yes”; reason “I don't see why it's hard to refuse a syntatically invalid request”; “follow rec” on keeping decode step 17. Prior option-1 pick (`bps-xmq1.9`, comment 359) withdrawn. | Post-nonce, post-PIN for Spend, with no reordered or new pre-PIN check. Normative/API amendment and formal correspondence pending; diagnostics and parser mechanics unchosen. |
| F1/F2 option 1: first document a bounded supported-state promise with explicit refusal outside it. | **Three of three readers.** `bps-xmq1.9`, comment 360. | No selection, topology, proof-carrier, discovery or RPC choice; no completed supported-state promise. |
| F3/F4/F13: conditional progress with named enabling and bounded-service premises. | **Three of three readers.** `bps-xmq1.10`, comment 358. | Scope only; no mechanism, service bound, requirement or ADR change. No residual is newly accepted. |

All other protocol and semantic choices remain **open with the owner**. Future design,
service and evidence authors own the corresponding proposals and evidence, not authority
to change those choices. F48 remains open until a later normative amendment; the other
selected findings also remain open. There is no fresh triage here.

## Findings, evidence and completion

Each entry gives the smallest next change and evidence required to complete that change,
not criteria claimed satisfied by this writing pass.

**F48 — direct owner decision recorded; prior pick withdrawn.**
[The decided format/decode form](f48-node-prevtx-decision.md#decided-formatdecode-form)
owns the assessment, quotations, earlier-failure effects, replay condition and excluded
observations. Presence becomes invalid request format at existing decode steps, distinct
from the historical late policy check and from `ParentRule.refuse`'s refusal of absence.
Completion requires the named SPN-5/SPN-8/API-5 and variant-decode amendment, preserved cache
eligibility, and formal correspondence; the model has no refuse-presence reading.
The record supplies only a PIN-outcome argument conditional on reaching decode, not a
byte-length, timing, intent-equality or production theorem. Other duties and choices remain
as stated there; no ADR change or finding closure is selected.

**F1 — decision recorded for scope; design open.**
[Conditional feasibility, F1](conditional-spend-feasibility.md#f1-confirmed-value-can-exceed-construction-or-existence-bounds)
separates `Exhibits.Feasibility.dust_stops_composer_only` from
`fragments_infeasible` and `toxic_infeasible`, under that section's explicit abstract
cost, retention and coverage assumptions. OPR-33 says “there is no coin selection and no
omission.” First write the supported-state/refusal contract; the owner must separately
choose any selection, topology or carrier amendment. Completion requires a stated domain,
construction-versus-existence distinction and boundary refusals, without a universal exit promise.

**F2 — decision recorded for scope; discovery open.**
[Conditional feasibility, F2](conditional-spend-feasibility.md#f2-authorization-and-a-bounded-view-are-separate-obligations)
pins `Exhibits.Feasibility.prior_spend_composer_refuses` and `deep_chain_infeasible` to
their resident-Spend and over-depth fixtures. OPR-39 says “confirmed-only” and
“prove authorization from the vault-spend ancestry — never merely from a script paying
the vault”. The next design author must specify a coherent bounded view, authorization,
replacement handling and resource limits. OPR-32's closed RPC inventory says “No generic
method string, no batch”; widening it **needs an owner decision**. Completion requires
that decision before a discovery contract and shallow/deep, changed-view and unavailable-evidence cases.

**F3 — decision recorded for progress scope; admission mechanism open.**
[Clock record, F3](clock-fault-decisions.md#f3-channel-freshness-after-a-forward-excursion)
pins `BtcPolicy.Progress.f3_blackhole` to a forward latch and corrected traffic delivered
every slot; quota and outer-stale answers are outside the model. NCH-38 says “A receiver's
wall-clock correction MUST NOT lower the freshness high-water”. The owner must decide
whether existing receipt-only exceptions meet the chosen scope before any broader design.
Completion requires named enabling premises and replay, quota, refusal-nonmutation and
PIN-independent observation evidence; lowering the latch **needs an owner decision**.

**F4 — decision recorded for progress scope; expiry authority open.**
[Clock record, F4](clock-fault-decisions.md#f4-a-pruned-refresh-poisons-attempt-authority)
gives the accepting-prune trace and `BtcPolicy.Progress.f4_no_arming` with resident
Carrier expiry at or below the nonce latch, despite continuous relays.
`f4_log_outage` additionally needs an expiry signed against the excursion.
SPN-12 says “one shared non-decreasing high-water mark”; SPN-10 says “expiry > effective_now”.
Splitting authority or sampling raw time **needs an owner decision**. The next author must
scope that choice; completion requires rollback, capacity, refusal-nonmutation, immutable
accepted-`D` and PIN-uniform evidence, without changing F3's latch.

**F13 — decision recorded for progress scope; service premise open.**
[Clock record, F13](clock-fault-decisions.md#f13-lockdown-needs-service-and-an-enabled-comparison)
pins `BtcPolicy.Progress.f13_starved` and `f13_postponed` to competing signed work and
delayed driver service. DUR-15 says “The DELAY before Lockdown lands has no finite bound
and this set claims none”. A future service author must propose enabling and service
premises for owner acceptance. Completion requires evidence for both; eventual fairness
alone supplies no finite bound. Changing ratchet updates **needs an owner decision** under
ADR-0026 decision 1: “Nothing else moves it”.

**F18 — blocked on named human evidence.**
[Stage-9 evidence](coercion-human-review-packet.md#stage-9-evidence-still-needed) and
[ADR-0017](../adr/0017-one-external-review-at-stage-9.md) retain “FREEZE, then REVIEW,
then CAPS LIFT”. The future evidence author must identify the frozen artifact and collect
the external human review and dispositions. Completion requires that review's sign-off
and remediation evidence before caps lift; no theorem supplies it. Reordering needs the owner.

**F21 — blocked on named human evidence.** The same packet's stage-9 section owns the
brief. OPS-18 says “has not been read by a human security reviewer and MUST be, before it
is relied on”; OPS-69 says “every step names a real operator command”. The future
evidence author must assemble the defect history and matching runbook, then obtain the
human reading and stranger's dry run. Completion requires their reports and remediated,
re-tested dispositions under ADR-0017, not this register or a theorem.

**F22 — analysis complete; evidence and decisions pending.**
[The observation boundary and premise ledger](silence-observation-inventory.md#surfaces-beyond-that-proof)
identify `ReceiptLifecycle.xvapply`, `LifecycleSilence.XVObs` and the missing assembly
relation. SEC-10 says “The **scope of SILENCE** MUST be stated wherever it is claimed”.
The [wire experiment's dependencies](silence-wire-experiment.md#dependencies-and-consequence)
require an authorized serializer harness, fresh states and reproducible controls, whose
availability remains unconfirmed. The evidence author must establish those first.
Completion of a sample means interpretable paired captures and explicit exclusions;
it cannot close end-to-end timing. No deployed timing theorem is claimed.

## Ordered follow-up work

1. Scope F48's decided decode-format/API amendment and formal correspondence, leaving unchosen
   diagnostics and parser mechanics open. Independently, document the F1/F2 supported-state promise and refusals.
   Keep F1 design and F2 discovery available separately after their own owner decisions.
2. Independently scope F3 admission, F4 expiry authority and F13 service/enabling evidence.
   Each mechanism follows its own decision; none waits for the other findings. Evidence
   preparation for F18/F21/F22 can proceed without selecting those mechanisms.
3. Queue existing evidence/record tasks from [the receipt lifecycle boundaries](proof-boundaries.md#30-the-expiry-aware-receipt-on-the-lifecycle-run):

| Existing task | Next deliverable |
| --- | --- |
| `bps-xmq1.21` | Add the missing ladder-pass base-possession exhibit on §33's layer. |
| `bps-xmq1.22` | Reconcile per-request `ReceiptLifecycle.reregister_refused` with the contract's stronger *Lifetimes* wording; stop for a semantic conflict. |
| `bps-xmq1.23` | Derive §33's supplied envelope labels under named premises, or record the obstruction. |
| `bps-xmq1.24` | Supply split-signer evidence above the fixture threshold, retaining `Exhibits.Ladder.split_across_rungs`. |
| `bps-xmq1.25` | Exhibit §32's `ReceiptQuota.inputs_inv` and `pass_count_checked` on checked runs. |

These tasks need their named layer/premise inputs before evidence changes. Keep `.20`
closed; its premise correction is recorded in the second milestone review. Local review
items remain local. `bps-8bbx.2`'s landed receipt scope and `bps-xmq1.11`'s deferred
evidence boundary confer no deployment assurance.

Every stream preserves DUR-22's entire per-pass denominator, including restored selected inputs:
“every distinct input outpoint of EVERY selected Escape counted once” and “a counted input
takes precedence over every exclusion”. It preserves SPN-25's backend comparison quoted above,
CHN-11's “`SIGHASH_ALL`”, CHN-23's “validate a
request's complete transaction group and build every sighash before signing any”, and
its pair over “the same non-empty coin set”, plus CHN-16's “same ordered input set”.
OPR-35 says “refused BEFORE allocation”; OPR-51 watches
“output 1 of the primary — its vault change”; SPN-32 registers “as one **pair** in the
candidate registry atomically”. Shape changes must preserve those watch/registration duties.

F69 stays separate under [the maturity record, §15](proof-boundaries.md#15-the-composers-immature-coinbase).
Its open deployment question belongs to the owner; the next evidence author must assess
whether waiting suffices, with deployment evidence. No theorem establishes adequacy.
ADR-0022 decision 3, “No minimum input count and no disjointness”, keeps consolidation closed.

## One prepared independent review

Historical preparation for the withdrawn F48 option-1 pick: not run or sent, no longer a
current review instruction, and no replacement for F18/F21 human evidence.
Review the selected claim that F48 option 1 can coexist with unchanged signer full-parent
duties and independent backend authority. Use the pinned F48 option-4 analysis and
recommendation, conditional-feasibility evidence section, CHN-22, OPR-46 and SPN-25.
Premises are verified signer parents, stripped authenticated wire requests, and independent
node backend comparisons. Can a missing-parent or supplied-mismatch case force weakening
any of those duties? Report a concrete counterexample or bounded compatibility argument
with exact owner quotations. Stop at an unstated decode/error/cache choice or normative
conflict and return it to the owner; do not select a mechanism or expand into an audit.

## Formal admission and separate next-tranche estimate

The smallest proposed tranche is one paired assembly-transition observation relation,
not whole-lifecycle SILENCE. Its specific uncertainty is whether common
`Assembly.guard_pub` inputs can be justified from paired `ReceiptLifecycle.Execution`
assembly transitions. Those are the owning declarations; SEC-10 (scope quoted above),
DUR-1's “Every observable a node emits MUST be identical” and SPN-3's “identical operations
in the identical order” own the requirements. Receipt-step equality does not fill this gap.

Admission requires an explicit transition/observer domain, justified guard coupling and the
[receipt premise ledger](silence-observation-inventory.md#receipt-step-evidence), including
`mk = .committed`, traversal `always`, dynamics `dynamic`, `Registration.preserve`, ratchet
close/driver, `VCoupled`, both `FInv`, common parameters and the shared admitted schedule
within its sticky horizon. The receipt examples `lifecycle_cases`, `lifecycle_horizon` and
`expired_decisions_leak` are background only. Admission of the proposed assembly tranche is
**blocked on named missing evidence**: a paired assembly-transition history with a defined
observer and concrete observable outcome, and a concrete assembly-level limiting
counterexample. Both artifacts are required before admitting work on this tranche.
No wider theorem is asserted.

Estimate this future tranche separately at **2–4 working days**, conditional on those
inputs and later authorization for proof/check work. Completion means the scoped relation,
success and limiting exhibits, premise-aligned prose and a negative control rejecting a
planted PIN-dependent assembly guard/public-output branch in the covered transition.
No such control is added or run now. A weaker theorem, dropped coverage, altered progress
meaning or contradiction **needs an owner decision**. There is no proof or normative work here.
