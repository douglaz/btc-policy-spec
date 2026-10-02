# Lean for btc-policy: from executable specification to an independent signer

**Revised:** September 15, 2026  
**Specification baseline:** `douglaz/btc-policy-spec`, `main` at `aa46b1c286a3f29b0dbac62adcbf63904e96f02b`  
**Baseline commit:** September 14, 2026, 19:10:09 UTC, "spec: fix the defects the review of the claw-back pass found (F57)"  
**Replaces:** the September 10 report against `442372062a6cabff4df9d1fcef691755eaad9925`  
**Status:** Proposed architecture and verification roadmap. This review implements no proofs, runs no implementation conformance suite, and audits no deployed binary. Every theorem and implementation stage below is a proposal unless explicitly identified as an existing specification requirement.

## Executive recommendation

Use Lean in two complementary tracks.

**Start now with an offline, executable formal model.** Make it an independent policy evaluator, a byte-level conformance oracle, a model of request admission and signature release, and a source of minimized counterexamples for other implementations. It should initially hold no production keys, process no real PINs, and have no authority over live signing.

**Build toward a Lean-centered federation node.** Reuse reviewed executable definitions and proved functions for protocol interpretation, policy and lifecycle decisions. Surround them with independent decoding and an explicitly trusted, narrowly specified runtime boundary for cryptography, secret storage, clocks, concurrency and operating-system lifecycle enforcement.

The current specification makes the initial project broader than a policy predicate. It has three request kinds, a schema-revision-4 manifest, chain-based refresh bounds, a set of independently authorized duress Escapes, and a pin-less immediate claw-back. Those distinctions belong in the model from its first version. They do not justify postponing useful small proofs until a whole daemon exists. [R4] [R5] [R6] [R10]

```text
Executable policy, classification and request-shape model
    -> proved byte encodings, size calculations and public-artifact checks
    -> lifecycle model, counterexamples and differential conformance tests
    -> offline ceremony verifier / test-only shadow implementation
    -> optional local enforcement component
    -> independently implemented Lean-centered signing node
```

Every stage should remain useful even if the full signer is never deployed. The decisive boundary is not whether a signature was computed in Lean. It is whether the actual transaction and every exposure of signing authority obey the modeled authorization conditions.

### What changed since the earlier report

| Current specification fact | Consequence for this roadmap |
|---|---|
| `SpendRequest`, `RefreshRequest` and `ClawbackRequest` are distinct request kinds | Separate request kind, transaction class and candidate role. Do not model every escape-class transaction as a paired Spend. |
| Schema revision is `4`, sealing `policy_version` and both refresh bounds | Replace the old manifest corpus and prove the current field layout and version refusal rules. |
| Refresh age comes from the creating transaction's confirming-block MTP | Remove any node-local refresh-history model. Add replacement, input-count and coin-count proofs. |
| Every confirmed Carrier contributes an Escape entry, including inert normal-PIN cover entries | Model per-entry duress authorization, OR merging, uniform window updates and the common coverage denominator. |
| Claw-back is pin-less, immediate, single-transaction and has no vault change | Prove the no-change guard and settlement terminality, not the retired escape-class-pair/residual design. |
| Maximum finalized size and release batching now have explicit contracts | Prove serialization-derived size and the cursor-anchored batch algorithm rather than assuming library behavior. |
| `SEC-54` explicitly owns accepted compromise and loss cases | Scope security claims to retained keys and custody assumptions, not a blanket "theft requires a node quorum" statement. |

These are current requirements or recorded corrections, not changes proposed by this report. Their owners are `MAN-2`/`MAN-3`, `CHN-30`–`CHN-35`, `SPN-38` and `SPN-43`–`SPN-51`, `DUR-10`/`DUR-20`/`DUR-22`, and `SEC-54`. The correction history is `F50`–`F57`. Numbered owning requirements govern when historical descriptions differ. [R4] [R5] [R6] [R9] [R10] [R14] [R16]

## 1. What Lean can establish, and what remains outside the proof

Lean checks proof terms against definitions and assumptions. Executable definitions can also run as programs. Neither capability automatically establishes end-to-end signer security. The meaning of the formal statement, its dependencies and the connection to deployment still need review. [L1] [L2]

| Claim | Meaning | Additional work required |
|---|---|---|
| Verified model | The mathematical machine preserves a stated property | Establish that its definitions express the intended current requirements |
| Verified Lean function | An executable function satisfies its contract | Connect actual bytes and observations to the function's domain |
| Verified integration | Runtime behavior refines the model | Account for decoding, scheduling, I/O, FFI, authoritative state and egress |
| Trustworthy deployment | The reviewed artifact runs under the required assumptions | Build integrity, custody, host independence, secret handling and lifecycle enforcement |

A theorem about Lean does not prove independently written Rust or Go. Differential tests establish agreement only on tested inputs. Universal agreement needs a formal connection, such as a justified translation or refinement proof.

Native execution introduces another boundary: Lean's compilation pipeline includes generated C and a C compiler. Kernel checking of a theorem is not a proof of that entire execution pipeline. Maintain separate **proof trust-base** and **execution trust-base** ledgers. [L3] [L4]

### 1.1 Define the security claim before proving it

`OVR-1` now delegates accepted theft cases to `SEC-54`. For example, an attacker holding the user key, coordinator credential and escape-wallet key can steal through the pin-less claw-back without a PIN or compromised node quorum. Two compromised recovery keys can spend coins whose recovery lock has matured. A lost escape key can turn a successfully delivered sweep into permanent loss. These are declared boundaries, not evaluator bugs. [R1] [R14]

Accordingly, prove properties such as **destination confinement**, **authorized release**, **bounded admission**, and **conditional preservation of operator custody** separately. The last must state which destination and recovery keys remain outside the attacker. Do not rename successful delivery to the sealed escape descriptor as unconditional theft prevention.

Represent the compromise matrix's named exceptions explicitly. Its combination rule has qualifications and undefined combinations where a loss removes a defense. A formal model should expose those cases for specification review, not silently totalize them with an optimistic default. [R14]

## 2. Start with the pure policy core

`POL-1`, `POL-3` and `POL-15` separate policy evaluation from clocks, chain reads, PIN processing and mutable state. Keep that boundary. Add transaction classification and request-shape validation as distinct operations, rather than turning the pure evaluator into a miniature node. [R2]

```text
evaluatePolicy(decodedPSBT, sealedPolicy) -> PolicyVerdict
classify(decodedTransaction, sealedPolicy) -> ClassificationResult
validateRequestShape(requestKind, classifiedMembers, sealedPolicy) -> ShapeVerdict
step(nodeState, event, explicitObservations) -> TransitionResult
```

This is proposed interface notation, not compiled Lean code. Use separate types for amounts, outpoints, scripts, evidence, request kind, transaction class, candidate role, refusal code and clock domain. In particular, an escape-class transaction is not by itself proof of duress authorization.

### 2.1 Model all three request kinds correctly

| Request kind | Required class and group | PIN and scheduling | Additional obligations |
|---|---|---|---|
| Spend | Hot-class primary plus mandatory escape-class Escape and optional ladder | PIN-bearing. Pair starts closed until its Carrier's holder decision. Hot primary has a Hold. | The Escape has separate duress authorization and fire-time checks. |
| Refresh | One refresh-class transaction | Pin-less, born open, fire window begins at ingress | Coarse subordination, chain-age interval, at most 24 inputs, sealed refresh fee cap and replacement sequence |
| Clawback | One escape-class transaction with every output paying the escape descriptor | Pin-less, born open, fire window begins at ingress | No vault change, no ladder, `nLockTime = 0`, every input sequence `0xfffffffd`, ordinary policy fee cap |

This describes admission and scheduling, not guaranteed broadcast or confirmation. Refresh and claw-back still require coordinator authentication, valid user signatures, local validation and sufficient node partials. They are not new on-chain branches: the descriptor still has Normal and Recovery paths. [R4] (`SPN-37`, `SPN-43`–`SPN-51`) [R10] (`CHN-1`, `CHN-11`, `CHN-31`–`CHN-35`) [R12] (`API-9`–`API-12`)

A SpendRequest with an escape-class primary is now refused. Do not carry forward the withdrawn escape-class paired spend or its residual. Likewise, a ladderless mandatory Escape uses `0xffffffff`, while a claw-back uses `0xfffffffd`. Sharing a destination class does not make their request rules interchangeable. [R10] [R15] (`OPR-20`–`OPR-25`)

### 2.2 Highest-value initial proof targets

**Destination soundness.** Successful evaluation implies every output belongs to the vault or an allowed destination under the exact descriptor-derivation relation. PSBT derivation hints never authorize a destination. Cover the inclusive derivation bound, multipath branches and definite descriptors. [R2] (`POL-3`, `POL-4`, `POL-10`)

**Classification soundness and request compatibility.** Escape-class cannot include a hot output. A mixed hot-plus-escape transaction may pass the output allowlist and must still fail classification. Then prove that only the class appropriate to the request kind is admitted. Retain the end-to-end mixed-output mutation test, and add the Spend-versus-Clawback distinction. [R7] (`CNF-22`–`CNF-25`) [R10] (`CHN-30`–`CHN-35`)

**No vault-coin amplification.** `CHN-30` requires the number of vault-derived outputs not to exceed the number of inputs, for every class. Prove the local count inequality and its preservation through a chain of authorized transitions. Keep external deposits outside the latter theorem's closed-world premise: an attacker can still create new vault coins externally. [R10] [R9] (`F54`)

**Claw-back no-change.** Prove that an admitted claw-back creates no vault output at all. This is stronger than merely classifying it as escape-class. Without it, repeated claw-backs can burn fees from successive vault-change outputs. With it, that particular recursive burn path is absent. This is a conditional accounting theorem, not a promise that the destination's keys remain safe or that coins can never be redeposited. [R10] (`CHN-35`) [R9] (`F57`)

**Hot outflow.** Prove the specified saturating calculation, including all outputs other than permitted vault and escape categories, and prove that equality with the per-transaction cap passes. Keep saturation behavior separate from ordinary mathematical addition and prove agreement on the domain where saturation is unreachable. [R2] (`POL-11`)

**Fee arithmetic.** Establish non-overflowing input/output sums and `total_out <= total_in` before subtracting. Then prove the exact guard `fee * 100 <= 10 * total_in`, including equality and one-satoshi-over cases. Lean's natural-number subtraction truncates at zero, so replacing unsigned arithmetic with `Nat` does not remove the first guard. [R2] (`POL-12`) [L5]

**Refusal precedence.** Prove first-failure order, not merely eventual rejection. Pure evaluation precedes classification. Therefore an invalid ClawbackRequest containing hot outputs can hit `HOT_BUDGET_EXCEEDED` before its class failure. Do not remove that reachable code merely because a valid claw-back has zero hot outflow. [R4] (`SPN-26`, `SPN-50`) [R12] (`API-24`)

**Useful acceptance.** Include concrete positive witnesses and acceptance theorems for each valid request kind at the appropriate layer. A policy function that always refuses can satisfy many safety implications vacuously.

### 2.3 Avoid hiding the difficult part in an assumption

An initial model may parameterize descriptor membership. Label the theorem accordingly: policy soundness **assuming that membership correctly implements the specified descriptor derivation**. It is not yet a theorem about real scripts.

Progressively discharge that assumption through a verified implementation or a documented trusted primitive. Do not feed Lean Rust-computed `is_change`, `is_hot` or `is_escape` flags and count agreement as independent destination validation. Keep coverage of `MAN-39`'s accepted grammar visible. [R6]

## 3. Put the byte boundary and exact arithmetic on the roadmap immediately

A decoded-object oracle is useful but cannot detect a parser defect shared by every consumer of that decoded object. Add a raw-byte entry point and keep its decoder independent from the implementation under test.

```text
Raw request / PSBT / public-artifact bytes
    -> bounded structural decoding
    -> boundary-specific validation
    -> independently derived domain values
    -> classification, policy and lifecycle checks
    -> decision, commitment bytes and modeled effects
```

Initially use synthetic inputs and public fixtures only. Real request bodies create the separate secret-memory obligations of `STO-11` and `STO-12`. [R8]

### 3.1 Keep protocol identities and encoders distinct

The current contract requires at least these distinctions:

| Object | Binding rule that the oracle must reproduce |
|---|---|
| Coordinator request | Vault-bound tagged hash, with request bytes `0x01`, `0x02`, `0x03` for Spend, Refresh and Clawback |
| PSBT in an authenticated request | Exact base64 string in the signed preimage, not a decode/re-encode substitute |
| Commitment | Its own big-endian encoding and untagged SHA-256, including ordered transaction fields |
| Other specified tagged preimages | The little-endian framing of `WIR-18`, with domain-specific field lists |
| User-signature hash | Ordered, length-prefixed DER signatures, each followed by its sighash byte |
| Carrier identity | Node-local identity under its own derivation and retention rules, not a federation-global commitment ID |

Prove encoder framing and injectivity over the fields actually encoded. Do not prove a stronger field-binding claim than the commitment supports: signature and other validation metadata can change without changing a commitment. Replay matching therefore needs its additional bindings. [R3] (`WIR-18`–`WIR-24`) [R10] (`CHN-24`–`CHN-29`) [R4] (`SPN-23`, `SPN-24`) [R11] (`NCH-31`, `NCH-32`)

Hash binding should be a collision reduction: if two different encoded values have the same digest, they exhibit a collision, assuming the encoding distinguishes those values. SHA-256 is not injective over arbitrary byte strings. Keep that cryptographic boundary separate from proved byte framing.

### 3.2 Schema revision 4 is a hard conformance boundary

Model `MAN-2`'s complete current preimage, including `policy_version`, `refresh_min_interval_secs` and `refresh_max_feerate`. Preserve normalized allowlist sorting, deduplication and escape exclusion, node order, endpoint order, and all integer widths. The descriptor, threshold shape and timelock are bound transitively through `wallet_id`, not as additional independent preimage fields. Endorsements authenticate the manifest but are not themselves fields of its hash preimage. [R6]

`protocol_version = 4` is the current manifest schema revision and channel-envelope version. Domain tags remain `/v0`. Revisions 1–3 never had sealed vaults and must be rejected outright, not supported by invented compatibility encoders. Version checking comes before current-schema validation. Future cold-path compatibility for genuinely sealed revisions starts at revision 4. [R6] (`MAN-3`) [R15] (`OPR-11`, `OPR-12`)

Prove that the live configuration reconstructs the expected manifest and refuses a changed sealed parameter before serving. Do not assert that every timing or resource parameter is manifest-sealed: `MAN-7` identifies node-local values, and the PIN attempt budget remains node-local even though the ceremony writes it into each config. [R6] (`MAN-7`, `MAN-11`, `MAN-35`)

### 3.3 JSON equivalence is not SILENCE equivalence

Across implementations, ordinary HTTP responses are compared by status and decoded members, not insignificant JSON whitespace or object order. Within one implementation, normal-PIN and duress-PIN executions still owe byte-identical responses where SILENCE requires them. These are different equivalence relations. [R3] (`WIR-1`, `WIR-11`) [R11] (`NCH-17`) [R5] (`DUR-1`)

Use separate decoder profiles for request bodies, strict channel envelopes, configuration and public artifacts. Request unknown members are ignored, channel-envelope extras are prohibited, and unknown top-level node-config keys are fatal. Preserve bounded integer syntax, raw versus hex-decoded nonce lengths, padded base64, strict DER and high-S rejection without normalization. Envelope-size prediction and request padding have additional byte-sensitive rules. [R3] (`WIR-1`–`WIR-6`) [R6] (`MAN-7`) [R11] (`NCH-10`, `NCH-21`, `NCH-22`)

A structural fixture is not automatically an accepted request. `WIR-7`'s PSBTs lack the signatures and evidence necessary for policy acceptance, and `WIR-10` deliberately separates envelope and partial structural examples. Keep decoder tests, authentication vectors and positive end-to-end fixtures in different test categories. [R3]

### 3.4 Prove maximum finalized size from serialization

`CHN-34` now gives a byte-defined target, rather than leaving a library accessor to define the answer. For the specified Normal-path witness:

```text
W_N = 73*t + 34*n + 232
    = 141*t + 198                      when n = 2*t - 1

maximum_finalized_vsize = floor((4*B + 2 + input_count*W_N + 3) / 4)
```

Here `B` is the legacy, witness-free transaction serialization with its empty scriptSig framing, and `W_N` is the per-input witness contribution. Prove the formula by constructing and measuring the specified witness script and maximum-length witness, including the 71-byte strict-DER low-S signature ceiling before the sighash byte. Exercise every supported shape from 2-of-3 through 8-of-15 and supported non-default timelocks. [R10] (`CHN-34`) [R7] (`CNF-136`)

Then prove that valid shorter signatures produce an actual finalized vsize no larger than the bound. Do not require equality. Use the maximum for pre-release fee admissibility and refresh fee bounds, and the actual size for the checks the specification requires after finalization. Distinguish this witness signature bound from the wire's general DER-length limit. [R10] (`CHN-20`, `CHN-34`) [R4] (`SPN-47`) [R5] (`DUR-25`) [R7] (`CNF-101`, `CNF-136`)

### 3.5 Descriptor normalization is not descriptor semantics

The vault template is narrow, but `MAN-39`'s public destination grammar includes multiple descriptor families, typed Miniscript, public extended keys, ordered multipath and Taproot trees. An implementation limited to a convenient subset has a coverage limitation, not permission to redefine conformance. [R6]

Keep text normalization, key derivation, script construction and witness satisfaction separate. Prove exactly the prescribed lexical and alias rewrites, supplied-checksum validation and output rendering. Do not claim that all semantically equivalent descriptor trees normalize identically. Do not reorder `sortedmulti`'s textual key expressions simply because its script construction sorts derived keys. [R6] (`MAN-39`)

## 4. An early practical application: an offline ceremony verifier

The first useful standalone tool should validate **public artifacts**, independently of the ceremony implementation and without any node or user signing secret.

Model the live-vault checks in `OPR-10`–`OPR-15`: load the named public files, reject unsupported schema revision first, normalize and parse the descriptor, reconstruct its script, verify threshold and key ordering, recompute `wallet_id` and `manifest_hash`, check the convenience fields against descriptor authority, and verify every channel endorsement. Check network and destination parameters from the authenticated manifest. [R15] [R6]

The recovery lock is per vault. Do not hardcode the default 180-day value into the verifier. Validate the time-based encoding and read the chosen lock back from the descriptor. Treat manifest `recovery_timelock`, `t` and `n` as claims to cross-check, not independent authority over the descriptor. [R10] (`CHN-1`–`CHN-8`) [R15] (`OPR-13`)

A second, separately labeled report can reproduce the public portions of the escape-key independence check: derivation-range, ancestor-key and fingerprint comparisons. It cannot prove unrelated paths came from different seeds, that devices are independent, that backups still exist, or that the escape key is outside a coercer's reach. [R6] (`MAN-28`) [R14] (`SEC-54`)

This complements the implementation-diverse descriptor check already recommended before funding. The ceremony remains trusted, and an artifact verifier cannot recover intended keys or policy from attacker-selected artifacts alone. Operators still need an independent statement of what they intended to authorize. [R6] (`MAN-37`)

Keep `node-*.toml`, PIN digests, backend credentials and ceremony secret state outside this public-tool input and logging scope. File publication, parent-directory integrity and orphaned staging recovery are separate filesystem obligations, not facts proved by checking the manifest hash. [R6] (`MAN-32`–`MAN-40`) [R9] (`F49`)

### 4.1 Extend the public checker to user-authorization groups

A second offline use is a key-less validator for the three-arm user-signer seam. Prove that the group is validated in full before any signature is requested, and that a malformed last ladder rung cannot leave a partially signed result. Validate full previous transactions, witness evidence, group shape, sequences, fee relations and the displayed amounts from the same canonical values. This checks authorization intent independently from the coordinator without putting a real user key into the Lean tool. [R15] (`OPR-20`–`OPR-29`) [R10] (`CHN-22`, `CHN-23`)

The signer seam deliberately receives no PIN. That gives a structural noninterference result for this interface, not a proof of the node's end-to-end SILENCE. Likewise, caller-supplied request labels and wallet IDs must be checked against independently loaded sealed state. [R15] (`OPR-21`, `OPR-22`)

Keep the scope of the ladder ceiling explicit. `OPR-28` says the ceiling check is "an honest-path composition discipline, not enforcement against a hostile coordinator". A user signature binds transaction bytes, not their base-versus-rung role. Prove the signer's local ceiling check without claiming that a role label cryptographically prevents later reuse of already signed bytes. [R15]

## 5. Model the lifecycle, not just the policy

The next major investment is a pure transition system with explicitly supplied observations:

```text
step : State x Event x Observations -> State x Effects
```

Events should represent protocol linearization points, not an entire HTTP handler. Include nonce admission, PIN-work completion, chain-preflight completion, holder arrival, candidate registration, settlement, release attempts, timer ticks and fatal runtime failures. Distinguish raw wall time, effective freshness high-waters, monotonic time and chain MTP. MTP is not an interchangeable fourth reading of the node's wall clock. [R4] [R5] [R11] [R13]

Separate public protocol state, secret-bearing state and emitted effects. An abstract signature token is useful, but the implementation connection must establish exactly which validated bytes it authorizes.

### 5.1 Prove invariants over reachable states

Define initial states, legal transitions and reachability, then prove initialization and preservation. Begin with these targets:

| Area | Proposed invariant or transition theorem |
|---|---|
| Admission | Each failure has the specified nonce-consumption, propagation and staging effects |
| Replay | Cached results do not bypass earlier PIN/arming hooks, post-preflight clocks or required byte matching |
| Accounting | Historical exposure and retained reservations survive candidate removal where required |
| Registration | The candidate group and capacity reservation are installed atomically |
| Hold | Hot authority is withheld until its authorized release event |
| Arming | Pair opening and duress freeze cannot be observed as separate writes |
| Selected Escapes | Each entry needs its own duress bit, and that bit cannot be cleared by a normal retry |
| Settlement | A terminal hot candidate never becomes due again merely because its conflicting transaction leaves the mempool |
| Lockdown | The latch is monotone and prohibits new signing, while permitted pre-signed Escape work remains possible |
| Death | Loss of safety state cannot resume the same key generation as an empty fresh signer |

These map to current admission, lifecycle, duress and persistence rules. They are not assertions that proofs already exist. [R4] [R5] [R8]

Model API timeout as distinct from job cancellation: a `/sign` handler can return 408 while its detached job retains its permit and continues. A trace that stops the underlying request on HTTP timeout does not model the specified lifecycle. [R12] (`API-4`)

### 5.2 Creation, scheduling and exposure are different authorities

```text
CreatePartial -> StorePartial -> AuthorizeRelease -> QueueForTransport
              -> ExposePartial -> CombineTransaction -> BroadcastTransaction
```

Use distinct effects rather than a single `signAndSend`. A signature created after policy checks can still be released too early or become usable after the state that originally authorized it has changed. The last release/send authorization must be atomic with the state transitions that can forbid it. [R4] (`SPN-32`, `SPN-38`, `SPN-39`) [R5] (`DUR-8`, `DUR-29`)

Do not infer that `t` holder receipts mean `t` honest nodes froze. With `t - 1` compromised members, they can contain just one honest holder. The intended safety argument is the coupling between admissible signing, holder-confirmed pair opening and the sole release gate. Preserve its network and compromise assumptions. [R5] (`DUR-5`, `DUR-8`, `DUR-35`)

Track exposure independently of registry residency. Under `SPN-33`, mempool settlement can remove pending entries and make input-conflicting hot candidates terminal, but it does not refund their budget charges. Confirmation, signed expiry and exposure aging have different refund rules. In particular, claw-back eviction does not make an already defeated hot candidate due again. [R4] [R2] (`POL-18`, `POL-19`)

### 5.3 Refresh: chain age, bounded size and usable replacements

Refresh is a particularly valuable compact formal submodel. Its pin-less and hold-less nature makes its own bounds load-bearing. There is **no node-local refresh log** in the current design. [R4] (`SPN-43`–`SPN-49`) [R8] (`STO-6`)

For every input, formalize:

```text
creating transaction confirmed on the active chain
and MTP(tip) - MTP(creating transaction's confirming block) >= sealed interval
```

Read confirmation by the creating transaction's txid, not the mempool-inclusive prevout's confirmed flag. A resident replacement can hide an otherwise confirmed input from that prevout read. Model the chain observations explicitly and reject missing or inactive-chain evidence rather than manufacturing an age. [R4] (`SPN-43`, `SPN-46`) [R13] (`WTC-2`)

Proposed proofs should connect age, no coin amplification, the 24-input cap and the maximum-finalized-size fee cap. State the result per specified chain-age interval and bounded transaction shape, not as a guaranteed real-time calendar loss rate. Arbitrary external deposits and reorg assumptions must remain explicit. [R4] (`SPN-44`, `SPN-46`, `SPN-47`) [R10] (`CHN-30`, `CHN-34`)

Replay the old alternating-honest-signer burn trace from `F52`, showing why changing which honest node co-signs cannot reset chain age. Also prove positive replacement cases: an unconfirmed refresh has not reset the input coins' chain age, its `0xfffffffd` sequence signals replacement, and ancestry handling recognizes an authorized resident refresh over exactly the same ordered outpoints. Do not conflate correct node admission with guaranteed mempool acceptance. [R9] (`F52`, `F54`) [R13] (`WTC-24`, `WTC-25`)

Keep subordination separate: any live hot pending entry or an in-flight Spend/claw-back preflight blocks refresh on that node, even for disjoint input sets. Its refusal is node-local and propagates. The age and sealed refresh-fee refusals have different propagation treatment. [R4] (`SPN-43`, `SPN-45`, `SPN-50`)

### 5.4 Claw-back: a distinct emergency request, not a fast duress pair

Model claw-back as one born-open, non-hot, non-duress candidate. It records no arm intent or Spend Carrier deadline, consumes no PIN budget, and changes no Armed overlay. It is admitted on an armed node as on an idle one, but not after Lockdown. Its request authentication and ordinary admission rules still apply. [R4] (`SPN-50`, `SPN-51`) [R5] (`DUR-36`)

Do not add refresh's subordination, interval, 24-input limit or sealed feerate cap. Their omission is deliberate. The defenses are the no-change shape, ordinary policy validation, the 10% fee guard, and fire-time input/ancestry requirements. Include positive cases for a young coin, more than 24 inputs within the actual size limits, and a fee above the refresh-specific cap but within `POL-12`. [R4] [R10] (`CHN-35`) [R7] (`CNF-146`)

The inflight marker still matters: refresh must not consume a claw-back's inputs during its preflight. A resident claw-back replacement needs the exact ordered outpoints and an authorized resident transaction. A mempool-dependent `UNKNOWN_INPUT` from that replacement check must not poison the deterministic policy-refusal cache. [R4] (`SPN-50`) [R13] (`WTC-25`)

Accepting or signing a claw-back does not settle anything. A claw-back that actually becomes mempool-resident or confirmed can defeat the armed Escape's inputs. Selected Escape inputs remain restored in the coverage denominator, so the relevant conflict fails at ancestry, not by pretending coverage disappeared. Eviction before `T` leaves the Escape admissible subject to its other checks. [R5] (`DUR-22`, `DUR-36`) [R7] (`CNF-55`)

### 5.5 Multiple selected Escapes: prove the actual set model

Replace any single-winner selector with a set keyed by Escape commitment ID. Every holder-confirmed Carrier contributes an entry under both PINs. Its per-entry duress bit is OR-merged, so a normal retry cannot clear prior authorization. Release requires both global `sweep_active` and the entry's own duress bit. Otherwise arming one pair could expose an unrelated normal-PIN pair's Escape. [R5] (`DUR-5`, `DUR-10`) [R4] (`SPN-38`)

Prove pin-uniform insertion and traversal, and prove that every relevant holder decision and hot acceptance updates all selected windows using the current `T`. Work cannot occur only when an armed node actually shrinks `T`. The windows are not capped by the original commitment expiry. [R5] (`DUR-13`, `DUR-14`, `DUR-20`)

For the coverage theorem, first define `DUR-22`'s protected-value construction: confirmed and vault-authorized unconfirmed value, restoration of inputs of **every** selected Escape, and exclusion of selected Escape outputs and resident-rung outputs. External unconfirmed deposits are excluded. Restoring only the Escape currently under evaluation recreates the denominator-shrink defect. [R5] (`DUR-22`) [R9] (`F54`)

Then prove the weighted-set lemma: two input-disjoint Escapes cannot each deliver more than half of the same positive protected value, provided their delivered outputs are funded by inputs in that common value universe. Connect this lemma to input authenticity, value conservation, the denominator construction and `escape_coverage_pct >= 51`. The counting lemma alone is not a proof that the runtime supplied a common denominator. [R5] (`DUR-24`) [R6] (`MAN-9`)

Keep the scope honest. Equal protected-value inputs, compatible snapshots and the selected-set assumptions must be premises or separately proved facts. `DUR-22` also specifies effects of claw-backs and mempool reads. Do not silently replace it with an invented permanently immutable snapshot, or claim agreement between arbitrary nodes merely because their tip heights match. Any ambiguity exposed while connecting the lemma to those reads belongs back in the specification.

Prove safety per selected Escape. Progress is conditional on enough nodes authorizing and delivering partials for the same Escape and an admissible rung. The set model removes the old arrival-order single-selector failure, but cannot make every delivery schedule yield a sweep. Retain `CNF-140`'s positive cross-node trace and its normal-entry isolation and disjoint-Escape negative controls. [R7]

### 5.6 Fee selection and cumulative release need their own proofs

The fee signal is not an unspecified median. `WTC-2` defines the non-coinbase population, score `floor(4*fee/weight)`, weight-weighted threshold and empty-block result. `DUR-30` selects the six-block anchor and rounds the resulting rate down to a multiple of five. Prove this pure arithmetic independently from the backend adapter. [R13] [R5]

For `SPN-38`, prove the complete cursor algorithm, including the repaired anchor:

```text
rung_budget = max(saturating_sub(peer_quota, 2), 1)
affordable  = floor(rung_budget / positive_input_count)
if affordable = 0: release nothing, cursor unchanged

F = max(release_floor, lowest_admissible_rung)
quota_cap = min(last_rung, F + affordable - 1)
U = min(latch, quota_cap)
if F > U: release nothing, cursor unchanged
otherwise queue [F, U], then set release_floor = U + 1
```

The cap is anchored on `F`, not the old cursor. Prove boundedness, no arithmetic overflow, no skipped admissible interval, and monotone cursor advancement only after a nonempty scheduled batch. Under repeated successful passes and sufficient quota, the remaining authorized interval is eventually scheduled. That conditional progress claim does not assume the shared peer quota is fair. Transport retries must not rewind the cursor or repeatedly requeue an already scheduled prefix. [R4] (`SPN-38`) [R11] (`NCH-8`, `NCH-15`) [R9] (`F51`)

Separately prove the latch never decreases, refused rungs expose no partial, and finalization selects the highest rung at or below the latch with sufficient valid partials on every input. A missing fee reading sets the target to zero, not necessarily the selected rung to zero: the sealed floor, admissibility and existing latch remain effective. [R5] (`DUR-26`–`DUR-30`) [R7] (`CNF-37`, `CNF-50`, `CNF-52`, `CNF-143`)

### 5.7 Preserve known limitations instead of proving stronger false claims

Keep the `POL-20` acceptance-time cohort bound separate from completion loss. Under its stated cohort and compromise premises, its coefficient is `(n - c)/(t - c)` times the per-node cap. Reproduce the delayed-holder counterexample showing that completion in a later interval can exceed the withdrawn rolling completion-loss claim while all admissions complied. Label admission, first exposure and completion times separately. [R2] [R7] (`CNF-58`)

Prove the unconditional Lockdown **decision** when its transition executes under its premises. Do not infer a finite execution delay from an unfair lock, a bulkhead or a dedicated thread. `DUR-15` and `F13` expressly disclaim that bound. [R5] [R9]

Likewise, duress submission is not instantaneous cancellation of every pending spend. Preserve holder-confirmation, delivery, censorship and per-link network assumptions. Reproduce `F3` and `F4` as counterexample traces without adopting an unselected clock repair. `F39` remains an open deployment/network question, not something to close by adding fairness to a theorem silently. [R5] (`DUR-34`, `DUR-35`) [R9]

## 6. Treat SILENCE as a relational property

SILENCE compares normal-PIN and duress-PIN executions of the same implementation under matching public inputs and a specified environment. Define an observation function and the concealment horizon, then prove a two-run property over those observations. [R5] (`DUR-1`) [R14] (`SEC-10`)

```text
observe(normal_run, authorized_concealment_window)
    = observe(duress_run, authorized_concealment_window)
```

The horizon must account for dynamic `T` and the earliest permitted visible divergence. Do not assume `duress_delay_secs` provides a minimum hidden interval. Do not extend the threat model to compromised nodes or a coordinator that learned the PIN before coercion. [R5] (`DUR-13`, `DUR-14`) [R14]

Use three evidence layers:

| Layer | Evidence sought | Not established by this layer alone |
|---|---|---|
| Protocol observations | Responses, projections and peer message shapes | Equal machine-level cost |
| Abstract work trace | Operation order, lock/allocation events, traversals and work counts | Compiler, cache and scheduler behavior |
| Native execution | Measured timing, memory behavior and runtime review against a stated cost model | A universal timing theorem without the model and proof |

The current model needs both per-entry selected-Escape observations and armed-versus-idle claw-back cases, including cached requests. Uniform window refresh and unconditional combination of the global and per-entry Escape bits are especially important. Correct PIN work is not enough if a later traversal or relay leaks the distinction. [R5] (`DUR-10`, `DUR-20`, `DUR-36`) [R7] (`CNF-40`, `CNF-41`, `CNF-55`, `CNF-140`)

`F22` still records that end-to-end SILENCE timing lacks a hard gate and that deterministic handler instrumentation does not cover all post-handler fan-out or arbitrary CPU work. Lean can improve protocol-level evidence without making that residual disappear. Do not assign opaque secret-dependent work a unit cost and advertise the resulting equality as constant-time execution. [R9]

## 7. Differential testing architecture

Build a versioned, language-neutral test driver outside the production signing path. Support both decoded-domain and raw-byte cases. Stateful tests need ordered events, explicitly typed clock readings, backend snapshots, network outcomes and synchronization barriers.

Compare exact normative bytes where required and semantic outcomes elsewhere. Relevant outputs include refusal code and precedence, class, normalized descriptor text, preimages and hashes, replay matching, candidate terminality, selected-entry authorization, reservation accounting and released rung sets. Do not require arbitrary diagnostic prose, node-local Carrier identities or ordinary JSON formatting to agree across languages. Within one implementation, compare normal/duress observations under the stricter SILENCE relation. [R3] [R4] [R5] [R6] [R11]

Use diverse input sources: published fixtures, Lean-generated cases, independent generators, manually designed adversarial cases and known historical regressions. A test corpus generated only from the Lean model can reproduce its own omissions. On disagreement, minimize and retain the case. Neither a language majority nor a compiling theorem automatically settles which implementation is correct.

### 7.1 Priority regression and mutation matrix

| Test family | Required distinction | Current anchors |
|---|---|---|
| Policy and class | Allowed mixed destinations still fail class validation | `CNF-13`–`CNF-25`, especially `CNF-22` |
| Manifest and startup | Revision 4 and changed sealed values produce the correct early refusal | `MAN-2`, `MAN-3`, `CNF-137`, `CNF-138` |
| Size and fee | Measured witness size, shorter signatures, every threshold shape | `CNF-101`, `CNF-136`, `WIR-36` |
| Refresh | Chain-age bound, no amplification, dust/input cap and actual replacement path | `CNF-32`, `CNF-139` |
| Claw-back | No change, no refresh-only guards, inflight exclusion and terminal hot candidates | `CNF-25`, `CNF-55`, `CNF-146` |
| Selected Escapes | Per-entry duress isolation, OR merge, all-input restoration and uniform window updates | `CNF-140` |
| Release | Admissible start above cursor, zero-capacity batch, cumulative progress and final reauthorization race | `CNF-37`, `CNF-143` |
| Replay and exposure | Corrected PSBT re-evaluated, cached acceptance does not skip hooks, no mempool refund | `CNF-29`, `CNF-30`, `CNF-38` |
| Wire/API | All three request digests, strict signature profile, decoded channel responses | `WIR-21`, `WIR-31`, `CNF-59`, `CNF-60`, `CNF-106`, `CNF-145` |
| Relational behavior | Handler, read-surface and armed/idle claw-back twins | `CNF-40`, `CNF-41`, `CNF-55` |

These anchors identify required evidence, not evidence supplied by this report. Mutate the implementation or authoritative input to remove the relevant guard and require the named gate to fail. Include the `lowest_admissible > release_floor` cursor case: all-zero-start fixtures missed precisely that regression. [R7] [R9] (`F51`)

Retain the specification repository's own fixture, arithmetic, vector, citation and gate-control checks. A Lean proof of copied constants does not establish that the published requirement still contains those constants. Add a traceability check binding theorem statements and fixtures to the pinned requirement text, and make changes to that text trigger review. [R16] [R9] (`F14`, `F32`, `F50`, `F51`)

Use synthetic traces. Real request bodies, PIN-bearing authenticated preimages, retained signatures that enable a cheap PIN test, and hidden arm state must not leak into a diagnostic corpus. A new production trace format would need its own information-flow review. [R8] (`STO-11`, `STO-12`)

## 8. Reuse strategy and repository organization

Keep normative requirements in `btc-policy-spec` and pin the baseline in a separate `btc-policy-lean` repository. Suggested organization:

```text
BtcPolicy/Domain/
BtcPolicy/Policy/
BtcPolicy/Classification/
BtcPolicy/RequestShape/
BtcPolicy/Encoding/
BtcPolicy/Descriptors/
BtcPolicy/WitnessSize/
BtcPolicy/Manifest/
BtcPolicy/ChainObservations/
BtcPolicy/State/
BtcPolicy/Protocol/
BtcPolicy/Assumptions/
BtcPolicy/Proofs/
BtcPolicy/Executable/
BtcPolicy/Runtime/               # later, explicitly trusted boundaries
Tests/Fixtures/
Tests/Traces/
Tests/Counterexamples/
Tests/Mutation/
spec-baseline.json
docs/coverage.md
docs/trusted-boundary.md
docs/runtime-refinement.md
```

Separate readable semantic definitions from efficient representations and prove agreement. Keep proof-time dependencies distinct from the executable dependency graph. A broad theorem import is not automatically a suitable daemon dependency.

`btc-verified` remains a relevant reuse candidate. Its public documentation describes serialization, transaction components, computable hashing and packed-byte implementations refined against simpler specifications. These are foundations to inspect module by module, not documentation of a complete btc-policy PSBT/descriptor/manifest/lifecycle signer. This review examined project documentation, not its proof artifacts or a clean build. [B1] [B2] [B3] [B4]

The packed-codec pattern is especially useful: prove the understandable representation first, then prove that the optimized codec computes the same result for all inputs. Audit assumptions, integer bounds, accepted binary forms, dependencies and the pinned revision before reuse. Do not require canonical re-encoding where btc-policy deliberately accepts multiple equivalent representations. [B3] [B4] [R3]

Lean's `mvcgen` can generate verification conditions for supported monadic `do` programs. It may help with state-transforming executable components after their semantic contracts exist. It does not automatically verify an arbitrary concurrent network daemon or discharge the OS assumptions of `STO-9`–`STO-13`. [L7] [R8]

## 9. Later deployment options

### 9.1 Test-only shadow implementation

A non-voting Lean implementation can run the realistic protocol harness with synthetic PINs on regtest, parse independent request bytes and reconstruct modeled state. It contributes no federation signature.

A production observer cannot reconstruct private arm, holder, replay or reservation state from public traffic alone. Exposing that state for an observer can create a new leak. Specify exactly what is observable before claiming complete shadow validation. [R5] [R8] [R12]

### 9.2 Local veto or enforcement component

A Lean checker can be an additional local gate, but it is not another federation member and contributes no additional independent key.

Its authorization must bind the exact validated manifest, transaction bytes, request kind, candidate, relevant state version and permitted action. A generic `approved = true` is insufficient. In particular, request kind cannot be inferred only from transaction class: an Escape and claw-back have different release conditions.

The key-owning service must have no bypass. For stateful authorization, the Lean component must either own the authoritative state or use an interaction whose consistency is established. Caller-supplied snapshots cannot manufacture proof-backed permission. An arm, terminality or Lockdown transition must invalidate conflicting pending effects at the actual final authorization boundary. [R4] (`SPN-33`, `SPN-38`, `SPN-39`) [R5] (`DUR-9`, `DUR-29`)

A Lean proposition in an FFI type is not a runtime capability. Propositions are erased or represented irrelevantly at that boundary. Authenticate ordinary data and enforce state ownership where the key actually resides. Process separation may contain a component failure, but does not defeat a compromised kernel. [L6]

### 9.3 Preferred long-term target: a Lean-centered signer

```text
Transport and independent chain adapters
                  |
Independent bounded decoding and validation
                  |
Lean policy, request-shape and lifecycle core
                  |
Atomic release / send authorization boundary
                  |
Native cryptography, secret buffers and OS lifecycle enforcement
```

Use Lean for the independent interpretation and decisions whose connection to the protocol has been proved. Keep the lower layers narrow, but do not label them untrusted merely because they sit below a verified core.

The native boundary may include ECDSA, Argon2id, secure randomness, secret-buffer ownership, lifecycle attributes and deadline-thread support. Define explicit correctness and failure contracts for each. Never expose an externally reachable arbitrary-digest signing service whose caller can bypass request and release authorization. [R6] (`MAN-17`, `MAN-22`) [R8]

A pure-Lean secret-key implementation is optional research, not a prerequisite. Arithmetic correctness alone does not establish constant-time operations, nonce safety or erasure. Preserve a well-reviewed native cryptographic dependency when a replacement would reduce assurance merely to improve the diversity table.

## 10. Production blockers that must be solved explicitly

### Secret memory and PIN-bearing input

`STO-11` covers the entire path, not only the long-lived signing key: network body, decoded PIN, authenticated preimage, padded request, Carrier material, KDF matrix and temporary copies. Secret buffers must be final-size before copying secrets, redacted, and zeroized on destruction. `STO-12` separately forbids retained material that enables cheap offline PIN testing. [R8]

Lean uses reference counting, and strings and arrays can share storage or copy it during updates. Deallocation is not evidence of erasure. Do not use ordinary `String`, `ByteArray` or `Nat` as a secure-secret abstraction simply because memory is managed. A secure native buffer helps only if every conversion, parser, exception and callback respects its ownership contract. [L8]

This creates a design decision for a production byte-level parser. It must either operate through reviewed secret-buffer facilities or be split at a precisely specified boundary whose decoding is trusted. The public-fixture parser used by the offline oracle does not automatically solve that production problem.

### Exceptions, concurrency and one-shot lifecycle

The deployment must prevent re-entry of the same key generation after safety-state loss. Model the startup ordering: checks and bind, then create-only generation claim before accepting a connection. Model the Lockdown attribute and its fail-closed RAM behavior separately. A pure theorem cannot protect a shell that restarts the key with empty state. [R8] (`STO-1`–`STO-5`)

The current runtime rules are not fully language-neutral. `STO-9` prescribes sign-lock then store-lock ordering, blocking sections, synchronous chain RPC and restrictions on await-aware locks. `STO-10` prescribes poison-aware failure handling. `STO-13` requires a dedicated OS deadline thread. An actor/event-loop replacement is a proposed specification change, not automatically conformant because its model looks cleaner. [R8]

The overview still says every node runs the same code, while `OVR-16` and `OVR-17` explicitly support other-language implementations. Resolve that documentation inconsistency for a deliberately heterogeneous federation. It does not erase the concrete runtime obligations that still require an accepted mechanism or specification revision. [R1]

### Open design questions remain open

| Issue | Consequence for Lean work |
|---|---|
| `F1`, toxic or fragmented inputs | Report composability limits. Do not omit protected value to make a request fit. |
| `F2`, composition over authorized unconfirmed value | Separate what a node can validate from what the operator composer currently constructs. |
| `F3`, `F4`, freshness high-waters | Preserve counterexamples and compare proposed repairs without silently deploying one. |
| `F8`, `F9`, alternative node lifecycle | The current target remains one-shot. Recoverable state is a different design decision. |
| `F37`–`F39`, routed transport, read perimeter and per-link partitions | Parameterize proof assumptions and identify deployment decisions still needed. |
| `F47`, poison-path latch write | Do not silently bless its async-worker exception. |
| `F48`, node handling of full previous transactions | Do not import the user signer's full-parent requirement into the node's decoder contract. |
| `F49`, orphaned ceremony staging | Prove only an accepted ownership mechanism, not PID existence as a substitute. |

`F48` deserves particular care: `CHN-22` requires full previous transactions at the **user signer**, whereas the node gets prevout truth from its backend and the wire path strips full parents after signing. The node-side missing/present-full-parent policy is explicitly unresolved. Mark that coverage boundary rather than making the Lean oracle an accidental new protocol authority. [R9] [R10] [R15]

Also retain the actual deployment boundary: loopback is the current stage-1 transport form, and the authenticated routed mechanism remains a named decision. Passing local regtest does not establish production transport independence. [R6] (`MAN-4`) [R11] (`NCH-2`) [R12] (`API-1`)

### Resource use and deployment integrity

Termination is not a practical resource bound. Model limits on bytes, parser depth, descriptor work, candidate counts, reserved signature growth, ancestry and work queues. Test exhausted and interrupted paths. Do not invent arbitrary rejection limits and call a subset implementation fully conformant.

Pin Lean, the native compiler, runtime, libraries and build inputs. Inspect the actual linked artifact and its FFI replacements. The FFI documentation still describes an unstable interface, so its boundary needs version-specific regression tests. [L6]

Neither a proof nor green local tests remove external review, custody drills or rollout gates. `F18` still records the absence of external human review, and `F21` keeps human review of the coercion procedure distinct from another automated pass. [R9]

## 11. Proof engineering and delegated contributions

For every claimed theorem, record the pinned requirement IDs, exact formal statement, referenced definitions, assumptions, proof status, implementation coverage and known counterexamples outside its scope. Give acceptance and resource obligations the same visibility as rejection theorems.

Require transitive axiom audits. Reject `sorryAx` and unapproved custom axioms. Distinguish ordinary logical axioms from cryptographic assumptions and native-computation trust. Grepping only for `Lean.trustCompiler` is insufficient: current Lean can introduce a separate axiom for each native evaluation. [L9] [L2]

Use clean builds and explicit proof replay in CI. The checker tooling needs an update from the earlier report: the standalone `lean4checker` repository is deprecated, and its documentation says `leanchecker` is bundled from Lean 4.28.0. For a compatible pinned toolchain and a project umbrella module named `BtcPolicy`, the documented invocation pattern is:

```sh
lake build
lake env leanchecker --fresh BtcPolicy
```

This is a proposed CI pattern, not a command run by this review. Replaying through Lean's kernel is additional checking, not an independently implemented proof checker. [L10]

For higher assurance, validate that the checked theorem matches a separately trusted statement, and use sandboxed proof production plus independently implemented checking where supported. Untrusted proof builds can execute code. Keep production credentials and signing material out of that environment. [L2]

For delegated contributions, separate statement ownership from proof production. A contributor assigned a proof should not be allowed to weaken its statement, redefine membership, assume denominator agreement, add a trusted signer primitive, or modify the acceptance corpus in the same task. Review critical definitions and theorem changes separately.

A practical claim record should distinguish `proposed`, `proved in model`, `executable refinement proved`, `differentially tested` and `runtime evidence reviewed`. These are not interchangeable badges. Track missing evidence without converting it into an axiom.

Changes in the spec should trigger a semantic review, not merely a baseline-hash update. The histories of `F51`, `F54` and `F57` are especially good regression material: each shows a plausible repair that required a further correction. A successful proof of the previous abstraction does not excuse failing to model the changed boundary. [R9]

## 12. Diversity accounting: retain and sharpen the earlier recommendation

A different implementation contributes diversity only where it independently implements the relevant behavior. A Lean wrapper around the same parser, descriptor library or state machine does not independently validate those components. An offline Lean oracle contributes evidence and **zero federation votes**.

For the specified topology `n = 2*t - 1`, limiting every implementation family to at most `t - 1` keys requires at least three families: two cover at most `2*t - 2` nodes. Thus Rust plus Go remains a useful initial engineering combination, but cannot alone eliminate every implementation-family quorum in this topology. This is a counting result, not a claim about comparative language quality. [R10] (`CHN-2`)

For example, `2 Rust + 2 Go + 1 Lean` in a 3-of-5 federation avoids a threshold-sized application family. But if the two Rust nodes and the Lean node share a key-compromising native dependency, that dependency still spans three keys.

Maintain overlapping failure classes for policy, parsing, descriptors, crypto, runtime, compiler backend, OS, provider, credentials and operators. Record what failure each class could cause. A conservative refusal can destroy availability without granting theft authority, while a secret compromise or unauthorized-release defect has different consequences.

The new compromise matrix makes the scope even clearer: application diversity does not protect a lost escape wallet, coercer-reachable escape custody or a compromised recovery quorum after maturity. Review node implementation diversity and destination/recovery custody as separate dimensions. [R14] (`SEC-54`)

Mixed-fleet tests must establish compatible user-signature handling, commitment and manifest bytes, all three request kinds, cumulative rung delivery, finalization and the Escape path under documented failure assumptions. Do not replace mature cryptography with a weak independent implementation just to balance the matrix.

## 13. Acceptance-gated implementation plan

| Stage | Deliverable | Gate to proceed |
|---|---|---|
| A | Pinned schema-4 model, requirement coverage and trust ledgers | Current request kinds and unresolved boundaries are explicit. No invented answers to findings. |
| B | Pure policy, class and request-shape core | Positive cases for all three kinds, mixed-output rejection, no-change and no-amplification proofs, fee guards, precedence and mutation controls |
| C | Independent codecs, witness-size model and public ceremony verifier | Current vectors, measured serialization across all shapes, version refusals, endorsement checks and explicit descriptor coverage |
| D | Lifecycle and relational models | Replay/accounting/release invariants, chain-age refresh, selected-Escape set, claw-back terminality and reproduced residual traces |
| E | Mixed-language regtest shadow implementation | Independent parsing, semantic and byte-level comparisons, resource failures, adversarial ordering and no production secrets |
| F | Lean-centered node with a reviewed native boundary | Secret-memory design, lifecycle enforcement, conformant concurrency, final egress linearization and complete applicable conformance evidence |
| G | Eligible independent federation member | External review, existing rollout decisions and gates, operational evidence, and reviewed dependency/custody topology |

These are acceptance gates, not calendar estimates or assertions of current implementation status.

The first bounded work package should still be **policy plus classification**, now explicitly including request-kind compatibility, claw-back no-change, the all-class vault-output-count rule, fee arithmetic and refusal precedence. Deliver a synthetic-data differential CLI rather than a privileged service.

In parallel, establish the **schema-4 byte model and serialization-derived maximum vsize**. They are compact, high-value targets whose mistakes affect every implementation. Make the **public-artifact ceremony verifier** the first standalone application.

The next stateful package should focus on **refresh age/replacement and selected-Escape release**, with claw-back settlement and retained budget accounting integrated into the same event model. This prioritizes the boundaries that the latest correction rounds actually changed.

The long-term target remains a **Lean-centered signer**, not an entire new Bitcoin node or an entirely new cryptographic stack. Keep each node's independently operated backend under an explicit contract and extend the verified boundary only when its assumptions and runtime connection have been reviewed. [R13] (`WTC-1`, `WTC-2`)

## Final assessment

The earlier report's central recommendation survives: Lean is useful immediately without holding a key, and a verified executable core can later reduce the gap between the specification and application decisions.

The updated priority is more precise. Start with the three request kinds, schema-4 identities, exact witness-size accounting and non-vacuous policy proofs. Then formalize chain-based refresh, per-entry Escape authorization, the protected-value construction, cumulative release, claw-back terminality and exposure-aware accounting.

Do not advertise an unconditional theft-prevention theorem, a finite Lockdown latency bound, machine-level SILENCE from output equality, or conformance across a boundary the specification leaves undecided. The model should make those distinctions harder to overlook, not hide them behind a "verified" label.

**Recommended end state: independent Rust and Go implementations, a continuously useful Lean model and conformance toolchain, and eventually a Lean-centered signer whose proved logic, runtime assumptions, secret-handling boundary and shared failure classes are all explicitly identified.**

---

## Source register and review scope

The uploaded September 10 report is the editorial starting point. Specification references below were checked against the pinned September 14 commit, not against implementation code. Numbered requirements are the current authority. The findings register is used to distinguish current rules, historical counterexamples and genuinely unresolved decisions. No claim here certifies that the reference implementation has adopted the current requirements.

### Pinned specification sources

- **[R1] 00-overview.md.** OVR-1, OVR-8 through OVR-17, and the system-context description.
- **[R2] 03-policy-checks.md.** POL-1 through POL-22, including pure evaluation, fee arithmetic and admission accounting.
- **[R3] 08-wire-contract.md.** WIR-1 through WIR-11, WIR-18 through WIR-24, and current vector/fixture families.
- **[R4] 04-spend-lifecycle.md.** SPN-5 through SPN-51, especially replay, terminality, release batching, Refresh and Clawback.
- **[R5] 05-duress-and-lockdown.md.** DUR-1 through DUR-36, especially per-entry selection, window updates, coverage and release.
- **[R6] 09-manifest-config-ceremony.md.** MAN-1 through MAN-40, including schema 4, sealing, public artifacts and normalization.
- **[R7] 15-conformance-checklist.md.** Applicable conformance evidence, especially CNF-22, CNF-25, CNF-29, CNF-37, CNF-40, CNF-55, CNF-58 and CNF-136 through CNF-146.
- **[R8] 11-state-and-persistence.md.** STO-1 through STO-15, including no refresh log, secret ownership and prescribed runtime mechanisms.
- **[R9] 16-open-findings.md.** Current OPEN/OWNER DECISION/CONTINGENT boundaries and correction records F50 through F57.
- **[R10] 02-onchain-contract.md.** CHN-1 through CHN-35, including the on-chain template, classification, maximum size and claw-back shape.
- **[R11] 06-node-channel.md.** NCH-1 through NCH-25 and Carrier identity/receipt rules, especially transport, padding, quota and reply semantics.
- **[R12] 07-node-api.md.** API-4, API-9 through API-16, read surfaces and API-24.
- **[R13] 10-watchtower-and-chain.md.** WTC-1 through WTC-25, especially exact backend observations, coherent reads and authorized replacements.
- **[R14] 12-security-requirements.md.** SEC-2 through SEC-15 and SEC-54, including trust boundaries and the compromise-and-loss matrix.
- **[R15] 17-operator-program.md.** OPR-1 through OPR-29, especially live-vault construction and the three-arm user-signer boundary.
- **[R16] README.md.** Specification authority, repository gate descriptions and withdrawn identifiers.

### Lean documentation checked September 15, 2026

The language reference's `latest` edition identified itself as **4.34.0** during this review. That is a documentation observation, not selection or certification of a production toolchain. Pin a reviewed version and use matching documentation. The checker migration note is cited separately because the proof-validation chapter still uses the older tool name.

- **[L1].** Lean Language Reference, introduction and current manual version.
- **[L2].** Validating a Lean Proof, statement validation, proof replay and sandboxed checking.
- **[L3].** Elaboration and Compilation, logical and native-execution boundaries.
- **[L4].** Run-Time Code, execution representation and runtime context.
- **[L5].** Natural Numbers, including truncated subtraction.
- **[L6].** Foreign Function Interface, instability, ownership and erased propositions.
- **[L7].** The mvcgen tactic, monadic verification conditions.
- **[L8].** Reference Counting, sharing and copying behavior.
- **[L9].** Axioms, transitive dependency inspection and native-evaluation trust.
- **[L10].** Official migration notice from standalone lean4checker to bundled leanchecker.

### External reuse material

These are public project documentation pages checked during this review, not audited or locally rebuilt proof artifacts. Pin and inspect a concrete project revision before depending on it. The broader consensus roadmap is not a prerequisite for the proposed btc-policy work.

- **[B1].** Project overview and documented scope.
- **[B2].** Crypto module documentation.
- **[B3].** Packed representations and refinement documentation.
- **[B4].** Serialization contracts and canonical encoding documentation.

### Evidence delivered by this review

This deliverable is a source-grounded documentation revision and proposed work plan. It does not include a Lean implementation, checked proof terms, a conformance run, executed repository gates, a production dependency audit or human security-review sign-off. Code blocks describing interfaces and algorithms are design notation unless explicitly marked as a shell invocation pattern.

[R1]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/00-overview.md
[R2]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/03-policy-checks.md
[R3]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/08-wire-contract.md
[R4]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/04-spend-lifecycle.md
[R5]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/05-duress-and-lockdown.md
[R6]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/09-manifest-config-ceremony.md
[R7]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/15-conformance-checklist.md
[R8]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/11-state-and-persistence.md
[R9]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/16-open-findings.md
[R10]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/02-onchain-contract.md
[R11]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/06-node-channel.md
[R12]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/07-node-api.md
[R13]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/10-watchtower-and-chain.md
[R14]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/12-security-requirements.md
[R15]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/17-operator-program.md
[R16]: https://github.com/douglaz/btc-policy-spec/blob/aa46b1c286a3f29b0dbac62adcbf63904e96f02b/README.md
[L1]: https://lean-lang.org/doc/reference/latest/
[L2]: https://lean-lang.org/doc/reference/latest/ValidatingProofs/
[L3]: https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/
[L4]: https://lean-lang.org/doc/reference/latest/Run-Time-Code/
[L5]: https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/
[L6]: https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/
[L7]: https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/
[L8]: https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/
[L9]: https://lean-lang.org/doc/reference/latest/Axioms/
[L10]: https://github.com/leanprover/lean4checker
[B1]: https://github.com/ProofOfKeags/btc-verified
[B2]: https://github.com/ProofOfKeags/btc-verified/blob/master/BtcVerified/Crypto/README.md
[B3]: https://github.com/ProofOfKeags/btc-verified/blob/master/BtcVerified/Packed/README.md
[B4]: https://github.com/ProofOfKeags/btc-verified/blob/master/BtcVerified/Serialize/README.md
