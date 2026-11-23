# Accepted-response wire comparison

This specifies one bounded future comparison, runs nothing and creates no
milestone. [API-12](../../07-node-api.md) says “A decodable request answers
HTTP 200 with one of two externally tagged bodies”. Select only its Accepted
response to a valid hot Spend. The observer is the coordinator receiving that
HTTP response, under [SEC-10](../../12-security-requirements.md): “silence
against a coordinator that turns hostile at the wrench”.

## Pair and capture boundary

Use paired fresh isolated states with the same presented PIN enrolled normal
in one and duress in the other. Hold public request and transaction data,
initial public state, keys, configuration, clock samples, execution schedule
and observer knowledge equal. Only the enrollment role and its necessarily
related private state differ. Preserve SEC-10's release-history premise,
“no node has run a compromised release while the current PINs were in use”,
and digest premise, “the adversary holds no copy of either PIN digest and that
neither PIN is enrolled in another vault, in either role”. Exclude prior PIN
records and coordinator compromise before the wrench. The observer controls
no node.

The finite sample is one successful Accepted response from each state for
that single request. Capture the coordinator-visible decrypted HTTP encoding
from the status line through headers, framing and the final body byte. Record
raw bytes, total and component lengths, header names and values, field presence,
types and values. Inspect the `accepted` tag, `commitment_id`, `first_seen`
and `remaining_secs`; API-12 quotes SPN-34's “with `first_seen` the ingress time
and `remaining_secs = fire_at − first_seen`”. Fix transport protocol and
compression settings. Preserve original captures; do not normalize any
secret-dependent field, omission, ordering or length.

Common randomness is justified only for a named production source whose
distribution and consumption are independent of PIN class. Document that
justification before coupling its draws; otherwise retain independent draws
and mark affected byte equality uninterpretable. Do not demand equality of
independently randomized ciphertext or signatures. This capture ends above
transport encryption, and API-12 says “There is no variant carrying a signature
or a PSBT”. Unexpected randomized content needs investigation, not deletion.

## Dependencies and consequence

An authorized implementation harness connected to the production serializer,
fresh-state construction, and reproducible clock and schedule controls are
dependencies, not capabilities established here. Their availability requires
confirmation; this record does not assert that an external harness is absent.

A PIN-correlated response difference directs the next work to that encoding
path before widening the sample. An uninterpretable randomized difference
requires attribution before any verdict. Equal interpretable captures support
only this sample and boundary. They leave other requests, retained states,
refusals, peer effects, CPU cost, queue and lock timing, and network timing
unknown. [F22](../../16-open-findings.md) says the deterministic replacement
“ends at handler return and covers neither post-handler fan-out nor arbitrary
CPU cost”. This comparison cannot close that finding or establish deployed
SILENCE.
