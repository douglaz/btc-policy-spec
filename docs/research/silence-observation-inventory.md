# SILENCE observation inventory

This record inventories evidence, proposes no policy and closes no finding.
[SEC-10](../../12-security-requirements.md) requires “The **scope of SILENCE**
MUST be stated wherever it is claimed”. Here the adversary holds the coordinator
and physical scene at the wrench, but no node. Its release-history premise
requires “no node has run a compromised release while the current PINs were in
use”; its digest premise requires “the adversary holds no copy of either PIN
digest and that neither PIN is enrolled in another vault, in either role”.
Prior PIN recordings and earlier coordinator compromise also defeat this
comparison's knowledge boundary. Neither premise is established by the model.

## Receipt-step evidence

Classification: proved under stated premises, for the logical observer only.
[The receipt proof boundary](proof-boundaries.md) identifies
`ReceiptLifecycle.xvapply` and `LifecycleSilence.XVObs`. The observer sees
`ReceiptExpiry.xfobs`' federation projection and `ReceiptLifecycle.dobs`:
receiver, signer, label, answer, and `VariantSilence.Checks` only on a live
lookup. Missing or expired lookups expose no store decisions; `found` alone
does not establish liveness. An expired candidate without an open Escape
window is evicted, answers `UNKNOWN_CANDIDATE`, takes the modeled refund and
stores nothing. Birth drops and removal of departed candidates are included.

`LifecycleSilence.xvfed_silence` takes `mk = .committed`, traversal `always`,
dynamics `dynamic`, `Registration.preserve`, and ratchet-based close time and
deadline driver. Entry requires `VariantSilence.VCoupled`: federation coupling,
one envelope list and equal kept records at honest nodes; both runs satisfy
`FedSilence.FInv`. `LifecycleSilence.xvfed_silence_fresh` discharges these from
`Federation.Fresh` with clear sweep flags, nothing sent and nothing kept.
Configured receiver keys, Hot guards, cap and window are common parameters.

The common labelled `FedSilence.PStep` schedule includes kernel inputs,
process steps, relays, partial deliveries, extraction and forgery, with each
receipt's label and sample shared. Samples may move backward. `xvwalk` stops
at the first inadmissible step, or one whose acting node fails
`Silence.preHorizon` in either run or whose request shape fails
`Silence.wfEvent`. The horizon allows an unarmed state or a driver's sample
strictly below current `T`, under the ratchet driver premise; admitted requests
are non-hot Escape without incoming window-close values. The full stop is
sticky, including after a later backward sample. Adaptive equality restricts
`LifecycleSilence.XVObserver` to its covered public observation history alone.

Useful exhibits are `Exhibits.LifecycleSilence.lifecycle_silent`,
`lifecycle_cases`, `lifecycle_rebirth` and `lifecycle_exemption`.
`lifecycle_horizon` exhibits the sticky stop; `expired_decisions_leak` shows
why exposing expired-lookup decisions breaks equality. `xvwalk_xwalk` relates
the projection without decisions on every schedule; `xvwalk_walk` needs no
evicting delivery, while `xvwalk_vwalk` and `xvwalk_split` additionally need
residency and no birth under a resident id. Those bridge restrictions are not
extra premises of receipt-step SILENCE. Logical `XVObs` is not automatically
a deployed wire observer.

## Surfaces beyond that proof

Classification: specified but unproved for deployed serialized fields, errors,
lengths, handler work and timing. [DUR-1](../../05-duress-and-lockdown.md)
requires “Every observable a node emits MUST be identical” between PIN classes;
[SPN-3](../../04-spend-lifecycle.md) requires “identical operations in the
identical order”. Actual observers include the coordinator reading responses,
events, health and pending state; peer endpoints seeing destinations, envelopes
and retry traffic; and any attacker able to measure queue, lock, storage or
network effects. Allocation, lock counts and store-lock hold time also need
evidence. [F22](../../16-open-findings.md) records “end-to-end SILENCE timing
has no hard gate”. No seconds bound or deployment assurance follows.

Peer destination and shape equality is proved only in the federation projection
under its coupling, invariants and horizon. Shared quotas and retries are
outside the current formal guarantee: [NCH-15](../../06-node-channel.md) says
“The quota is per node, not sealed, and has no fairness”; NCH-8 says
“an `UNKNOWN_CANDIDATE` reply or a transport error waits the next backoff step
and advances it”. Receipt/release quota accounts do not establish that deployed
shared behavior. Other lifecycle steps and passes are outside the current
SILENCE guarantee. One precise missing relation maps paired
`ReceiptLifecycle.Execution` assembly transitions to equal public observations,
preserving coupling and justifying common `Assembly.guard_pub` inputs;
receipt-step equality supplies no such relation.

## Possession and human boundaries

Classification: possession is proved conditionally, not as SILENCE.
[The possession premise ledger](proof-boundaries.md) gives
`ReceiptPossession.possession_window` and `possession_within`. Distinct eligible
contributors, an honest separate receiver, compatible candidates, nonempty
transaction inputs, threshold and row labels need configuration, signing and
validation evidence. `Ready` throughout the pass window needs candidate-lifetime
enforcement; admitted passes, backend verdicts, listing and `BaseReady` need
release-policy evidence. Pass and delivery windows need future scheduler,
transport and processing service evidence. Receiver chain-view inputs need
backend evidence; `Possession.Retains` through the endpoint needs storage and
retention enforcement. These are supplied premises, not approved service bounds.
Non-eviction and no birth under the id are separately derived through
`unevicted_of_resident` and `unborn_of_resident` under `Registration.preserve`.

`Exhibits.ReceiptPossession.layer_possession` and `layer_base_possession`
illustrate success; `layer_starved`, `layer_expired_first`, `layer_evicted_after`,
`layer_pruned_after` and `layer_label_mismatch` limit it. Slots are not seconds;
possession is not assembly, submission or confirmation. Human coercion and
Recovery usability remain outside this guarantee. [SEC-41](../../12-security-requirements.md)
says “No theorem carries this conditional Recovery-only claim or ‘it is not
private’”. No complete SILENCE claim is made here.
