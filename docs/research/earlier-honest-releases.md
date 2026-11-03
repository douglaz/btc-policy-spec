# Earlier honest releases: the cutoff boundary

Research task `bps-g3rf`, 2026-11-02. No protocol rule changes.

The candidate premise is `BtcPolicy.Kernel.NoHonestNormalSince`: for every honest signer,
every commitment and every recorded frame whose effective sample is at or after a fixed
wall cutoff, there is no `BtcPolicy.Kernel.NormalOpening` for the target message.
Earlier normal decisions remain allowed. The implication
`BtcPolicy.Kernel.no_normal_implies_no_normal_since` proves that the existing
`BtcPolicy.Kernel.NoHonestNormalDecision` implies this candidate, and
`BtcPolicy.Exhibits.EarlierRelease.cutoff_is_strictly_weaker` supplies an inhabited
non-converse. Neither predicate assumes an authority count.

The candidate does **not** imply absence of quorum, even if every honest node later arms
and freezes both old and new candidates. The counterexample is
`BtcPolicy.Exhibits.EarlierRelease.later_freeze_preserves_prior_quorum`, using the fixtures
in `BtcPolicy.Exhibits.EarlierRelease`. Its threshold is 3, with identities 0–4,
only identity 0 compromised, and a target symbolic message `(100, 0)`.

| Effective sample | Honest histories |
| --- | --- |
| 10 | All four accept the same old hot spend and its Escape under an ordinary Carrier. |
| 20, 21 | Identities 1 and 2 receive distinct relays from 3 and 4; only 1 and 2 open the old hot spend. |
| 100 | Identities 1 and 2 release their own target partials. |
| 110 | All four accept a duress Carrier naming new commitments over the same transactions, with later expiry. This is the cutoff. |
| 120, 121 | Identities 1 and 2 receive relays from 3 and 4; identities 3 and 4 receive relays from 1 and 2. All four arm. |
| 150 | Honest fire passes expose no further target partial. Identity 0 contributes compromised target authority under the new commitment. |

The final inventory contains exactly the distinct signers `[0, 1, 2]` for the target
input, despite all four honest nodes being armed and holding both hot candidates frozen.
The honest rows retain the old commitment id; the compromised row names the new one.
Both candidates have exposed quorum because `BtcPolicy.Kernel.exposedQuorum` filters by
message and input, not commitment or candidate class. Signers are deduplicated. Repeated
rows or repeated commitments for one signer would add no authority; the existing
`BtcPolicy.Exhibits.Provenance.repeated_exposure_has_no_quorum` checks that distinction.

No peer partial is delivered in the new exhibit: every resident candidate holds only its
node's own partial. Durable exposure therefore does not establish possession at a combiner.
`POL-18` says "A partial that has left the node is finalizable authority in `t − 1` compromised
hands". `SPN-32` says "MUST transmit none of those partials in the response or to any peer at this point";
local ingress signing is not exposure. The counterexample counts earlier queued hot partials
and the compromised key, not the honest withheld signatures created at ingress.
`DUR-11` says "a frozen candidate is never due, never released, never finalized";
that resident-state rule does not retract a signature already outside the node.

## Premises and limits

* **History consistency:** every identity's exact retained history has an
  `BtcPolicy.Kernel.Execution` from an initially unarmed, empty node; all use
  `BtcPolicy.Kernel.current`, threshold 3 and the same transactions and parameters.
  Honest exposure is the union of their actual queue-effect rows. The counterexample
  explicitly proves `BtcPolicy.Kernel.HonestExposureProvenance`, including the earlier
  normal decision for each honest row. The inventory world is not claimed reachable.
  Carrier senders are distinct peers that have accepted the corresponding Carrier in
  their own history. Nevertheless no network semantics links these histories, checks
  authenticated transport, or proves sent/received correspondence. That holds of this
  exhibit as stated; the next section links the same histories. `DUR-5` says a relay
  "proves the peer received and processed the Carrier, not that it froze or signed".
  No distributed-execution theorem or resolution of `F39` is claimed.
* **Time:** the chosen effective and monotonic samples increase in each local history.
  The cutoff is a history restriction on those supplied samples, not a globally trusted
  clock, a delivery guarantee, or an invariant that follows merely from current arming.
* **Message binding:** the kernel's `BtcPolicy.Kernel.sighash` is the symbolic pair
  `(tx.id, input)`. The fixture uses identical target transactions under both commitment
  ids. Applying it to Bitcoin requires binding each symbolic identity to the same actual
  BIP143 message, including transaction, input, witness script and coin value, and
  excluding honest non-hot authority for that target. Neither signature binding nor
  collision resistance is proved. `SPN-23` says "compute the spend's and the Escape's commitments";
  replay identity does not change the identity of an already signed message.
* **Validity and completeness:** the exposure rows stand for valid usable signatures of
  the named authorized distinct node keys. Cryptographic verification, unforgeability,
  valid user authority, actual storage/availability to a spender and completeness of
  the inventory are external assumptions. The compromised set means all extracted keys
  still authorized for the coin, not only hosts presently controlled. The one compromised
  identity is explicitly below threshold; honest rows have provenance rather than being
  fabricated through environment events.
* **Inputs and finalization:** this result counts one indispensable input, index 0.
  `DUR-28` requires "`≥ t` distinct valid partials on every input". An upper bound below
  threshold at any indispensable input rules out that target's Normal completion,
  subject to the message/validity/completeness assumptions. Reaching threshold at input 0
  proves no transaction completion: other inputs, the user signature in `CHN-1`, actual
  possession, package validation and broadcast remain separate. `F65`'s corrected
  exposure/possession distinction is preserved. Recovery and alternative transactions
  are outside this target-specific statement.

## One composed execution

Task `bps-uaer.4`, 2026-11-03. The local histories above link into one reachable
`BtcPolicy.Federation.Execution` over `BtcPolicy.Kernel.current` with none of them changed:
`BtcPolicy.Exhibits.EarlierRelease.linked_preserves_prior_quorum`. No obstruction was found.
The schedule, the threshold, the transactions, the samples and the compromised identity are
the ones above; no premise of the counterexample changed.

Honest identities 1–4 each start at `BtcPolicy.Exhibits.EarlierRelease.initial`; identity 0
is outside the honest list and has no world of its own.

| Composed steps | What they carry |
| --- | --- |
| Four acceptances, two relays | All four accept the old Carrier; 3 and 4 emit its relay. |
| Four deliveries | The relays of 3 and 4 reach 1 and 2, at samples 20 and 21. No other relay of the old Carrier is delivered. |
| Two fire passes | 1 and 2 queue their old target partials into the partial inventory. |
| Four acceptances, four relays | All four accept the duress Carrier and emit its relay. |
| Eight deliveries | Relays of 3 and 4 reach 1 and 2; relays of 1 and 2 reach 3 and 4, at samples 120 and 121. |
| Four fire passes | All four queue only Escape partials. |
| Extract, forge | Identity 0's key is copied and signs its row under the new commitment. |

Over that one execution the theorem shows each honest projection is exactly
`BtcPolicy.Exhibits.EarlierRelease.history` and ends at
`BtcPolicy.Exhibits.EarlierRelease.world`. Each delivered relay names an honest sender that
processed the Carrier (`BtcPolicy.Federation.receipt_origin`). Each row of the partial
inventory was queued by its honest signer or signed with the copied key
(`BtcPolicy.Federation.part_origin`), and the partial inventory is the rows of
`BtcPolicy.Exhibits.EarlierRelease.inventory`, reordered. The provenance premise is derived by
`BtcPolicy.Federation.honest_exposure_provenance` rather than proved row by row, under its
message-binding premise `BtcPolicy.Federation.HotBinding`, which holds of this run. The rest
is the conclusion of the local exhibit: the cutoff premise holds, the all-history premise
fails, the copied set has one signer against threshold 3, all four honest nodes end armed with
both hot candidates frozen and only their own partial held, and both candidates have exposed
quorum. The history-consistency limit above is thereby removed for this witness: the assembled
inventory is the partial inventory of a reachable composed execution.

The composition keeps its own boundaries. Authentication is ideal. A relay carries no request
body; here all four accept the same request under each Carrier identity, so the witness does
not rely on that gap. Clocks are per node and never compared, so the cutoff is still a
restriction on supplied local samples. A relay that is never delivered is a drop the
composition allows; nothing guarantees delivery. The derivation takes the accepted-only
refusal rule, the value of `BtcPolicy.Kernel.current`.

**Possession only where delivered.** The witness delivers no partial.
`BtcPolicy.Exhibits.EarlierRelease.linked_possession_only_where_delivered` extends it by
delivering the target rows of identity 2 and identity 0 to identity 1: its old candidate then
holds 1 and 2, its new one 1 and 0, and no candidate holds three, because the rows sit under
two commitments and only identity 1's own signature is under both. Identities 2–4 still hold
only their own partial, and the exposed quorum is unchanged. A holder of rows under both
commitments, such as an adversary holding the copied key, is not a step of the composition:
exposure counts partials that have left a node, as above, and is not possession.

The research answer below is unchanged. The linked witness refutes a cutoff-only replacement
of the all-history premise on a reachable composed execution; it does not show every useful
weaker premise impossible. Input 1, user authority, package validation and inclusion stay out.

## Research answer

The prior-authority history motivates the counterexample; fresh duress, selective delivery
and failed Escape explain its boundary. Fresh withholding can block new authority; selective
delivery does not prove enough honest withholding; failed Escape does not erase old Normal
authority or prove coins moved. Those finite histories are recorded in the paper's model-run
records at paper commit `de8b6d8`; its account at `3abf67a`, "Evidence and remaining questions",
correctly describes the existing theorem as conditional. The spec exhibit is self-contained
and requires neither the paper repository nor its fixtures to build.

There is no stronger safety theorem here. The new result refutes the proposed **cutoff-only**
weakening, even with subsequent honest freeze and honest exposure provenance. It does not prove
that every strictly weaker premise is impossible. A useful positive theorem would need a
restriction on which honest signers could have supplied earlier target authority, supported
by history or a mechanism establishing that restriction. Merely assuming that the union of
earlier honest signers and compromised keys has cardinality below threshold restates the
desired bound and is not this research result. Current arming, a new commitment id and lack
of recent normal decisions supply no such restriction. No protocol amendment is proposed.
The existing all-history theorem and its qualifications remain intact.
