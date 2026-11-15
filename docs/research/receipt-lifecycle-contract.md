# The expiry-aware receipt on the lifecycle run: integration contract

Task `bps-xmq1.3`, base `151aff9`, scheduled by the 2026-11-13 next-steps plan. Records only: no definition, theorem
statement, gate, requirement or ADR changes. This record fixes the design that `bps-xmq1.4` implements and lists what
that change set proves, exhibits and controls. A change set that departs from it amends this record first, under the
same review. Requirements read: `NCH-24`, `NCH-25`, `SPN-32`, `SPN-41`, `POL-18`, `POL-19`, `DUR-28`, `DUR-29`,
`DUR-31`.

**Why a contract.** The receipt that evicts an expired candidate runs on the ledgered federation run
(`ReceiptExpiry.xrun`, section 25 of `proof-boundaries.md`). The lifecycle run (`Lifecycle.Execution`, section 23)
delivers a partial through `Kernel.receivePartial`: it carries no Hot ledger, its variant-bound store
(`VariantReceipt.kept`) reads no expiry, and its permits read no eviction. Conjoining the two execution predicates is
not a composition, and taking an evicting receipt as the lifecycle's delivery would store a partial where the
receipt evicts.

## The extension

One reusable transition and one layer over the lifecycle run, both beside the existing definitions.

1. **The receipt on the labelled ledgered state.** A step of `VariantSilence.VFed` (a ledgered federation, the honest
   envelopes sent so far, each node's kept records) that is `VariantSilence.vapply` with `ReceiptExpiry.xapply` in
   place of `FedSilence.lapply`, and with two changes to the store `VariantSilence.vstore` computes:
   - at a delivery the receiver's lookup evicts on (`ReceiptExpiry.evictsAt`), nothing arrives;
   - at a step that births a record under an id at its acting node, a step after which that node holds more records
     under the id than before (the count `Lifecycle.births` compares), the node's kept records under that id are
     dropped.

   Off an evicting delivery and off a birth under an id already resident at the acting node, the step is
   `VariantSilence.vapply` (from `ReceiptExpiry.xapply_unevicted`). The same transition is the domain the SILENCE
   work of `bps-8bbx.2` lifts next (see *The observer and SILENCE*).

   Under `Registration.preserve` no step births under an id already resident at its acting node: `Kernel.accept`
   births a pair only with both ids absent (`Kernel.pairAdmits`), and `Kernel.clawback` only under an absent id. A
   node then holds at most one record per id (`Kernel.ids_nodup`; an eviction only removes records). So the birth
   drop finds nothing left, since the residency filter of `VariantSilence.vstore` dropped the id's records at the
   step that ended its residency. The birth drop, like the birth clause of the agreement subdomain below, matters
   only under `Registration.rebirth`.
2. **The layer.** Its state is a `Lifecycle.State` with each node's Hot ledger, the envelopes and the kept records:
   the receipt's state, whose federation is the lifecycle state's. Its steps are the lifecycle run's,
   `RungAssembly.Step` with a label. At a federation step the federation, the ledgers, the envelopes and the store
   are the receipt step's (1). Every other field is `Lifecycle.apply`'s on the step with each acceptance mapped
   through `FedSilence.kernelStep`, the Hot budget's staged refusal, as `FedSilence.ltrace` maps it. Rung steps,
   chain moves and observations are `Lifecycle.apply`'s and leave the ledgers, envelopes and store as they were. Off
   an evicting delivery the receipt's federation is `Federation.apply`'s on the mapped step
   (`ReceiptExpiry.xapply_unevicted`, `FedSilence.lapply_fed`), so there the layer's step is the lifecycle step.
3. **Admission.** `Lifecycle.admits` on the mapped step, with one substitution: the assembly guard reads the layer's
   possession, `VariantSilence.vheld`'s form (`RungIngress.ownSigs` and the kept records), in place of
   `ClassAssembly.heldAt`. So `ClassAssembly.finalAt`, `ClassAssembly.candOk`, `ClassAssembly.guard` and
   `ClassAssembly.assembleOk` are restated beside, each with that possession and its body otherwise the same. A
   delivery's label is admissible as `VariantSilence.vlabelOk` has it.

**Alternatives not taken.**
- Changing `Federation.apply`'s delivery, and `VariantReceipt.arrival`, to the expiry-aware receipt. Every layer above
  would inherit the eviction with no restating, but every definition under every result over `Federation.Execution`
  and above would change. The lookup would also have to move below `FedSilence`, which `ReceiptExpiry` imports.
- A new lifecycle state machine with its own receipt: it duplicates the protocol the existing layers state.
- The layer above with `Lifecycle.admits` unchanged. Its assembly would read `VariantReceipt.held`, recomputed from
  the labelled history, beside the store the receipt step writes and the SILENCE tranche reads. Possession would
  have two homes, and their agreement would have to be proved and would rest on a node holding at most one record
  per id. Under `Registration.rebirth` they part: `VariantReceipt.held` keeps records across a birth under an id
  that stays resident, and after an eviction that leaves another record under the same id.

## The mapping

| Component | Reused | The receipt's treatment | Lifetime |
| --- | --- | --- | --- |
| Candidate registry | `ReceiptExpiry.lookup`, `ReceiptExpiry.keepsAt`, `ReceiptExpiry.evict`, `ReceiptExpiry.receive`, `Kernel.prune` | The lookup at the delivery's own sample: missing, expired with no open Escape window on its pair, or live (`Kernel.exemptEscape` keeps the delayed slot under either PIN). On expired, every record under the id that the keep test rejects leaves, and nothing is stored (`ReceiptExpiry.evicts_answer`, `ReceiptExpiry.evicted_pruned`); otherwise `Kernel.receivePartial` runs. The eviction is per id, not per pair, and runs no armed removal; the prune pass is unchanged | An evicted record's residency ends. The next record under its id at the node is a birth (`Kernel.born`, `Kernel.register`, or a claw-back's `Kernel.clawbackBorn`) |
| Variant-bound Held store | `VariantReceipt.storable`, `VariantReceipt.arrival`, `VariantReceipt.addNew`, `VariantSilence.vstore`, `VariantSilence.vheld`, `RungIngress.ownSigs` | On a live lookup, the store's own checks (the rung by txid, the input range, the Escape-role hash, the signer range) and the first-record rule (`NCH-25`) decide what is kept. On an expired or missing lookup nothing arrives. The kernel's own signer set, which `Kernel.receivePartial` writes on a live lookup, compares no hash and is not this store | A record stays while a record under its id is resident at the node, and is dropped at a birth under its id there, which under `Registration.preserve` finds none left (see *The extension*). A partial retransmitted after a birth counts only once a live lookup and the store test in the new lifetime keep it |
| Hot ledger | `Ledger.sysStep` (through `FedSilence.lapply`, the budget's refusal included), `ReceiptExpiry.sysRecv`, `Ledger.refundAtPrune`, `Ledger.markExposed` | Under the guards of `Ledger.current`: `Ledger.Release.acceptedAdmission` and `Ledger.Refund.onCollection` are the premises of `ReceiptExpiry.refund_only_permitted`, and `ReceiptExpiry.exposed_kept` needs the first. The main change states its ledger results, examples and control with those premises. At an eviction, `Ledger.refundAtPrune` against the node the eviction leaves: a row goes only when it is unexposed, past its signed expiry on the wall sample and not resident (`ReceiptExpiry.refund_only_permitted`). That reads every row of the node's ledger, as a prune pass does, so a row of another commitment already collected goes under the same condition. An exposed row stays whole (`ReceiptExpiry.exposed_kept`). A receipt that does not evict is `Ledger.sysStep`'s (`ReceiptExpiry.sysRecv_unexpired`) | Rows are keyed by commitment, as decided for `F63`, not by lifetime: an unexposed row of an evicted commitment whose wall sample has not passed its expiry stays until a later step refunds it |
| Signature authority and inventory | `ReceiptExpiry.wstep_exposure`, `ReceiptExpiry.xapply_inventories`, `Federation.extracted_grows` | The arriving partial joins the receiver's exposure rows in every case, eviction and refusal included. The partial inventory, the relays and the extracted set do not move at a delivery. Only local retention can shrink | Exposure and the inventory never shrink across lifetimes |
| Release state | `Kernel.receivePartial`, `ReceiptExpiry.evict`, `Kernel.born`, `Retained.step_frame` | A live receipt writes only the signer set of the records under the id, so every latch, floor and `released` bit stays. An eviction removes records whole and leaves every other record as it was | Kept while the record is resident. A birth starts at zero, and no other step resets it |
| Send permissions | `Lifecycle.permAfter`, `Lifecycle.keeps`, `Lifecycle.sendOk`, `RungAssembly.escapeAt` | None: a delivery is no pass, prune, birth, settlement or send, so `Lifecycle.keeps` keeps every permit, the affected ones included. While no Escape-role record under the id is resident at the node, `Lifecycle.sendOk` refuses every send under it | A permit's lifetime is the stretch with no birth under its id at its node, and the birth ends it (`Lifecycle.permit_birth`) |
| Submission history | `Lifecycle.subsAfter`, `Lifecycle.history_kept` | A delivery adds no entry and removes none | Entries outlive every lifetime |
| Observer | `ReceiptExpiry.answer`, `ReceiptExpiry.XObs`, `VariantSilence.checks`, `VariantSilence.storeObs` | Per delivery: the receiver, the signer, the label, the answer, and the store's decisions only when the lookup is live. The eviction addresses no peer (`FedSilence.sent` is empty at a delivery) | Later consequences appear in the observations of the steps that have them: a send that is no longer admitted adds no submission |

**Why the eviction ends no permit.** Ending the node's permits at the eviction, as `Lifecycle.ends` does at a prune,
would end permits under unrelated ids. Ending only those under the evicted id adds nothing a send can use while the
Escape-role record is gone. Under `Registration.preserve` the eviction removes the id's only record at the node.
Under `Registration.rebirth`, where several records can share an id, it would also end a permit of a record under
the same id that the keep test kept. The review of this contract is asked to check this choice.

**Lifetimes.** The registration lifetime is the one `Lifecycle.births` already reads. Two consequences of the
existing rules become reachable on this domain, and the main change exhibits them without changing either rule.
- *A split pair.* The lookup evicts under one id, so a spend can be evicted while its Escape, under another id, stays
  resident until its own lookup or the next prune pass, or the reverse. While exactly one member is resident, a
  re-registration of the pair is refused whole and leaves every resident untouched (`SPN-32`: `PSBT_INCONSISTENT` /
  `candidate_identity`). In the model, under `Registration.preserve`, `Kernel.pairAdmits` needs both ids resident or
  both absent (`Kernel.pairAdmits_shape`), and otherwise `Kernel.accept` takes `Kernel.refuse`, which leaves the
  registry as it was. A re-registration births the pair again only once both ids are absent. ADR-0023's decision 12
  rejects completing a half-resident pair, and this record keeps that.
- *Re-registration after an eviction.* `Kernel.accept` registers only at an effective time at or before the signed
  expiry it reads (`Clocks.Mono.deadline`), and the eviction needs an effective time past the record's expiry. The
  run's samples are inputs with no premise that effective time never falls at a node. So an example that re-registers
  an evicted commitment states the sample it uses. The main change states that when every request under the evicted
  id signs an expiry equal to the record's and effective time at the node does not fall, no re-registration through
  `Kernel.accept` births under that id there. A claw-back is outside that statement: `Kernel.clawback` checks no
  expiry and, at a node not locked down (`Kernel.clawback_refused_locked`), births under any id not resident there.

## The atomic receipt

**Order.** `NCH-24`: "check wallet equality, signer equals sender, sighash type; then under the store lock: the
candidate exists, else `UNKNOWN_CANDIDATE`". The model draws the boundary before the lock: a
delivery is admitted only at an honest receiver and only for a partial in the inventory (`Federation.admits`), with
an admissible label. Wallet, sender and sighash type are not modelled and are taken as passed by every admitted
delivery, an environment assumption the execution predicate carries and each theorem about a delivery states. Only a
delivered partial can evict: a relay, a request or a refusal naming an expired commitment never does. The rung, the
hash, the ranges and the signature come after the lookup, so an admitted partial that would fail them still evicts an
expired candidate, a forged one under an extracted key included. The lookup reads the receiver's state, the id and
the sample, never the partial's origin.

**One transition.** For an admitted delivery the step:
1. reads the receiver's state before the step and the delivery's own sample;
2. distinguishes missing, expired and live (`ReceiptExpiry.lookup`);
3. on expired, evicts, takes the ledger's refund and the exposure bit, and appends the exposure row, all in the step;
4. on live, runs `Kernel.receivePartial`, then the store's checks and the first-record rule before anything is kept;
5. ends no permit, and leaves the others as they were (above);
6. leaves the pending log as it was: `ReceiptExpiry.evict` writes only the registry, and the pending log is pruned by
   the prune pass alone (`SPN-42`);
7. answers `UNKNOWN_CANDIDATE` or found (`ReceiptExpiry.answer`). Found means only that the lookup passed. It is not
   `NCH-17`'s `ACCEPTED` reply, and the store's decision stays separate.

**Clocks.** The lookup compares the record's expiry and the Escape window with effective time, `Kernel.Env.eff`,
which is `Clocks.Effective.ofWall` of the wall sample and the high-water. The refund compares a row's signed expiry
with the raw wall sample (`Ledger.refundAtPrune`, `POL-19`'s expiry disjunct). Both come from the delivery's own
sample, never from a pass's or the prune pass's, and the main change keeps them as two readings. Effective time is
never below the wall sample, so the one split case is an eviction at an effective time past the expiry with the wall
sample at or before it: the record is evicted and its unexposed row stays until a later step finds the wall past the
expiry.

## What the main change proves

- **Agreement with the lifecycle run.** On the subdomain where no delivery evicts and no step births under an id
  already resident at its acting node, forgetting the ledgers, envelopes and store, with acceptances mapped through
  `FedSilence.kernelStep`, leaves a `Lifecycle.Execution`, and the kept records are `VariantReceipt.kept` of the
  labelled history (as `VariantSilence.agrees_step` has it). So every result over `Lifecycle.Execution`, and through
  `Lifecycle.to_classed`, `Lifecycle.to_ladder` and `Lifecycle.to_settlement` the earlier layers' results, apply
  there. Conversely, the useful lifecycle run (`Exhibits.Lifecycle.lifecycle_run`, whose deliveries never evict:
  `Exhibits.ReceiptExpiry.lifecycle_unevicted`) is a run of the layer, with Hot ledgers under which its acceptances
  stand. So are the settled-Escape histories, which run on other schedules: both schedules of
  `Exhibits.Lifecycle.settled_base_blocks_resend` and both of `Exhibits.Lifecycle.settled_base_blocks_replacement`
  (the plan's case of a settled Escape that later needs a valid replacement or rebroadcast). Each is lifted with
  admissible labels, Hot ledgers under which its acceptances stand and no evicting delivery, and the lifted run
  keeps the sends that exhibit admits. Instead of these lifts, the main change may prove the general converse: every
  `Lifecycle.Execution` under `Registration.preserve` with admissible labels whose deliveries never evict is the
  forgetting of a run of the layer under Hot ledgers that refuse none of its acceptances. Under
  `Registration.rebirth` the layer's store drops at a birth records that `VariantReceipt.kept` keeps, so the
  converse is not claimed there.
- **Agreement with the receipt.** At every delivery the lookup, the answer, the registry left and the ledger are
  `ReceiptExpiry.lookup`'s, `ReceiptExpiry.answer`'s and `ReceiptExpiry.sysRecv`'s at the receiver's state and the
  delivery's sample. The federation and ledger part of the run is `ReceiptExpiry.xrun` over its federation steps,
  with every step admitted (`ReceiptExpiry.xlegal`), so the receipt's results apply at each step.
- **History.** Every exposure row, inventory partial, relay, extracted key and submission at an earlier state is at
  every later one (the restated `Lifecycle.history_kept`).
- **No send across a lifetime.** Every rung send is on a permit recorded at an earlier admitted assembly by the same
  honest node, of the same rung and txid, with no birth under the id at that node between, and with the Escape-role
  record resident at the send (the restated `Lifecycle.permit_origin` and `Lifecycle.submitted_origin`). An evicting
  receipt leaves every permit as it was. Under `Registration.preserve`, where a node holds at most one record per id,
  no send is admitted under the evicted id until a birth has ended the old permits.
- **Retention apart from authority.** A kept record came from a live lookup whose store test passed, at or after the
  last birth under its id at the node. An eviction or a birth can remove Held material at the node, while every
  exposure row and inventory partial stays.
- **Assembly and release.** A rung's assembly on the layer is the finalization at the latch over the layer's
  possession and passes `Assembly.rungCheck`; `ClassAssembly.rung_sound`, stated for any possession, unfolds what that
  established. The base path restates `ClassAssembly.guard_sound`. An evicting receipt leaves every record it keeps
  unchanged, which with `Retained.step_frame` at the kernel steps lets the main change restate
  `Retained.lifetime_mono` on the layer. No
  projection to `RungAssembly.Execution` that keeps rung steps is claimed, nor one to `ClassAssembly.Execution` off
  the agreement subdomain. Step-local results (`Lifecycle.permit_birth`, `Lifecycle.permit_consumed`,
  `Retained.step_frame`) apply directly to the steps the layer takes from `Lifecycle.apply`.

Release accounting (`SPN-38`, section 26) and possession under service (section 27) on this layer are `bps-xmq1.5`'s,
not the main change's.

## Examples

Each on a run of the layer, with the requirement it exercises.

| Case | Expected | Owner |
| --- | --- | --- |
| A delivery just before, exactly at and strictly after the expiry | Live, live, evicted: at equality nothing is evicted | `NCH-24` |
| The delayed-slot exemption under the duress PIN and under the normal PIN's inert slot | Live under both while the window is open; evicted past it | `SPN-41` |
| A missing candidate; one already pruned | `UNKNOWN_CANDIDATE`, nothing created or stored, the ledger as it was | `NCH-24` |
| An expired unexposed reservation; an expired exposed one | The first refunded at the eviction, the second whole | `POL-18` |
| The split clock: effective time past the expiry, the wall sample not | Evicted, no refund; a later step on a wall past the expiry refunds | `POL-18`, `POL-19` |
| A valid variant; a mismatched one, the candidate live | Kept; refused with the lookup found, exposed, not Held | `NCH-24` |
| A mismatched variant or an out-of-range signer, the candidate expired | Evicted all the same | `NCH-24` |
| A duplicate before and after a lifetime boundary | Before: no second record. After an eviction: `UNKNOWN_CANDIDATE`. After a birth: kept as the new lifetime's first record | `NCH-25` |
| An assembly, then an eviction, then a send on the old permit | The send is not admitted | `DUR-29`, `DUR-31` |
| An eviction, a re-registration under the same commitment (both ids absent, its sample stated), then reuse of the old Held records or permit | Neither counts; the old partial is Held again only through a new receipt | `DUR-28`, `DUR-31` |
| A split pair, then a re-registration of the pair while the other member is resident | The other member stays until its own lookup or the prune pass; the re-registration is refused whole, births nothing and leaves every resident as it was | `SPN-32`, `SPN-41` |
| An unrelated live candidate, one sharing the evicted one's transaction under another commitment | Its records, permits, release state and ledger row unchanged | `POL-18`, `DUR-29` |

**Acceptance.** One run of the layer exhibits an evicting receipt and its lifecycle consequence together: a send,
an assembly or a Held count that the same prefix with the lifecycle's own delivery admits or counts, and that the run
refuses or no longer counts after the eviction, or the converse. An eviction exhibit beside an unchanged lifecycle
exhibit does not meet it. The limiting counterexample that goes with it is the lifecycle run admitting or counting
what the layer refuses, added to *Counterexamples that must stay counterexamples*.

**Negative controls.** Each fails on its intended exhibit, stubbing only an owning proof the plant breaks first:
- a `Lifecycle.keeps` that ignores births, so a permit recorded in a prior lifetime authorizes a send in the next:
  it fails the re-registration example. That example makes the new Escape's rung due and release-authorized at the
  send, at its stated sample, so that in the clean tree only the ended permit refuses the send. A store that only
  keeps its records across a birth cannot fail any example under `Registration.preserve` (see *The extension*), so
  it is not a control;
- a receipt whose refund drops a row whatever its exposure bit: it fails the exposed-reservation example, and
  `Exhibits.ReceiptExpiry.exposed_charge_stands` with it.

## The observer and SILENCE

The main change defines the delivery's observation above and proves that its answer is `ReceiptExpiry.xfobs`'s and,
on a live lookup, its decisions are `VariantSilence.storeObs`'s. It states no SILENCE theorem. On this domain
`VariantSilence.checks` reports found for any resident record, an expired one included, so the observation carries
the answer and gives the store's decisions only on a live lookup. The SILENCE tranche of `bps-8bbx.2` that follows
lifts over the receipt step of *The extension* with this observation. It reuses `ExpirySilence.keepsAt_factor` and
`VariantSilence.checks_pub`, and the birth drop reads only record counts under an id. A change to the transition or
the observation needs this record amended first.

## Existing definitions and statements

**Changed by the main change:** none. Every existing definition, theorem statement and docstring keeps its meaning,
since each describes its own layer: `Lifecycle.Execution` still reads no expiry, `VariantReceipt.kept` still reads no
lookup, and `Kernel.receivePartial` still states the lookup as a boundary. The proof record gains a section, and the
entry point gains a row for the layer, as records.

**Changes the main change may raise, each a separate question under the rule for existing definitions:**
- factoring the possession out of `ClassAssembly.finalAt`, `ClassAssembly.candOk`, `ClassAssembly.guard` and
  `ClassAssembly.assembleOk`, so that the layer instantiates them instead of restating four bodies;
- moving `ReceiptExpiry.keepsAt` and `ReceiptExpiry.lookup` below `Federation`, needed only by the rejected route of
  changing `Federation.apply`.

The gates gain exhibits and the two controls; the counts of existing controls whose plants reach the new exhibits
move, and are measured, not predicted.

## Exclusions

- Wallet equality, signer equals sender, sighash type and signature verification: inside the admission boundary,
  not modelled.
- The answer's bytes, response timing, the store lock and the sender's back-off (`NCH-8`, `F22`); no bound in seconds
  (`F13`).
- SILENCE over the layer (`bps-8bbx.2`), release accounting and possession under service (`bps-xmq1.5`).
- Checked ingress stays a separate predicate on the federation trace (section 21); Refresh ingress, and a hash source
  for a candidate that is not Escape-role, stay outside (sections 19 and 20).
- The split pair and re-registration after an eviction are exhibited as the existing rules give them, not changed.
