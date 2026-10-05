# A formalized clause lives in Lean, the Markdown requirement renders it, and a proof is never conformance

Status: **accepted**.

The formal layer describes and checks the system and implements none of it. A checker asks
what interacting rules imply, beyond whether their citations resolve.

## Decisions

**1. The formal layer lives in this repository, under `tools/formal/`, namespace `BtcPolicy`.**
A formalized clause's home is its Lean declaration, tagged `@[req "POL-20"]`
with the identifier it formalizes; `lake exe gate` emits the requirement index from those
attributes and there is no other manifest. The Markdown requirement keeps its identifier, its
MUST, its rationale, its amendment record and its retained traps; its rendered formula, table or
figure is a copy of the declaration, held to it by a gate (decision 5). Until a clause's copy is
gated, the Markdown stays authoritative and the Lean is a checking interpretation.
`check_ids.py` reads the requirement index and refuses a tag naming an identifier nothing defines.

**2. A theorem is never conformance.** `tools/check_coverage.py` counts
conformance items and nothing from the formal layer; no `CNF` identifier appears in
`tools/formal/`. A proof is about the formal model under its stated assumptions; a conformance item
is about a running implementation (`OVR-17`). A conformance item may cite the theorem it
exercises; the theorem never cites the item. The ban also covers comments: it keeps a future
regex from counting a docstring as coverage. A docstring names the race, not the item.

**3. Trust policy, enforced by the gate, plus kernel replay.** Every constant of every
project module, tagged or not, in every namespace, may depend on `propext`, `Classical.choice` and
`Quot.sound` and on nothing else; `sorryAx` is refused transitively, wherever it sits; the project
declares no `axiom`, and the gate checks that promise for every constant rather than inferring it
from tagged dependencies; `native_decide` is refused everywhere, `BtcPolicy.Explore` included.
The source refusal covers `csimp`, `implemented_by` and `extern`, since the emitters must print
what the kernel proved about. `Explore` may hold untagged scratch, held to the same axiom policy
as everything else, and nothing tagged; the gate checks both. The gate and the emitters are
library code (`BtcPolicy.Exe`) so the walk covers them; the executable roots are one import
and one `main` each, held byte for byte by the wrapper.

Exhibits over rationals close by `decide +kernel`; general rational identities close by `grind`
on core Lean; every `Nat` floor, mod and inequality closes by `omega`; a predicate written as a
`Prop` `def` needs a `Decidable` instance beside it or `decide` fails to elaborate in a way that
reads as a proof gap, so the module template writes such predicates as `Bool`. No Mathlib: it is
added only in a commit that names the theorem it is for and the infrastructure it would otherwise
rebuild, with the cache, CI-time and version-coupling cost stated — "cannot close without it" is
not the threshold, a named need is. In addition to the axiom walk, `tools/check_formal.sh` runs
`lake env leanchecker --fresh BtcPolicy`, which replays every declaration through the kernel from
a fresh environment; the wrapper propagates its exit status and fails visibly when the tool is
missing. The walk refuses a proof that rests on the wrong axiom; the replay refuses an `.olean`
the build wrote that the kernel does not accept. The replay has no negative control in CI,
because such an `.olean` is not constructible from source.

**4. The nix shell is the one way to run the gates.** `flake.nix` pins Lean
4.30.0 from nixpkgs and provides `python3` with `argon2-cffi` and `cryptography` for the vector
gate; CI enters the same shell. A missing toolchain is a red gate, not a skipped one.
One pin: `flake.lock`.

**5. Figures are held to the declarations that derive them.** The derivations —
`CHN-4`'s BIP68 encoding and exact days, `CHN-2`'s shapes, `POL-20`'s coefficients,
`DUR-30`'s floor interval, `MAN-16`'s widths (derivations, not copies: `63 − 1`, `⌈63/8⌉`,
`8 × 2`), `ADR-0014`'s delayed-holder trace, `SPN-38`'s boundary rows — are theorems.
The tables are rendered regions. A theorem over Lean-side constants reads nothing of the document:
`CHN-4`'s `4224679`, `CHN-2`'s `8-of-15`, `POL-20`'s `(2 − 1/t)`, `DUR-30`'s
`⌊median / 5⌋ × 5`, `MAN-16`'s `62` and `SPN-38`'s prose formulas are inline figures with
no table to render. The Lean build emits `values.jsonl` beside `regions.jsonl` — each named
scalar or formula string a tagged declaration owns — and `tools/check_copies.py` reads every
operand and result from the documents, failing closed on unrecognised wording. It compares what
it reads from each owning sentence, and from every copy of it (`CHN-1`, `CHN-8`, `CHN-10` for
`CHN-4`; `WIR-16` for `NCH-12`; `NCH-13`'s prune offset, its own declaration defined equal to
`NCH-12`'s bound), to the emitted value instead of recomputing it. The Lean constant cannot read
the Markdown; Python reads both. `check_gate_controls.py` owns the copies and regions controls.

A region in a requirement must match the declaration's tag. In an ADR, the `Region` structure's
`home` field names the ADR (`"ADR-0014"`, for example), and the gate accepts a region in
`docs/adr/NNNN-*.md` exactly when `home` names it. No second map: the placement is the
declaration's, and a region whose `home` names a file that does not exist is red.
`match` compares backticked and bold tokens only; a bare number changed from 1 to 99 in a
`match` cell is not drift. Every arithmetic table is `render`, with its prose labels carried by
the declaration. `ADR-0014`'s timeline includes its row labels; `SPN-38`'s boundary table
includes a rendered "cap on the cursor" column so the distinguishing rows are visible.
The region gate's marker regex and the citation gate's name resolver use `BtcPolicy.`.

**6. Every semantic choice a dated amendment changed is a parameter of the model that carries it**,
with a `current` value that is the requirement as it stands, and the module holds the trace under
each value: the bad trace is refused under the current rule and admitted under the value that
stood before. Registration's `current` instantiations and executable verdicts live in
`Exhibits`, alongside the current exhibits for refused opening and the current verdicts for
pair inheritance and hot-release provenance (decision 12).
Not only Booleans: `SPN-38`'s anchor is `Anchor.onF | Anchor.onCursor`, `DUR-22`'s restoration
is `Denominator.restoreAll | restoreOne`, the refresh interval's source is `.chainMtp | .perNodeLog`.
CI flips `current` and requires the named theorem red. The twin rule is for historically repaired
semantics and their regression coverage; a codec round trip or a general identity needs no twin,
and is not decoration without one. The one-token flip against the row theorems is the acceptance
criterion, never a row's shape: `a > 0` is necessary but not sufficient for `SPN-38`'s anchors
to differ (`600 | 1 | 0 | 2 | 3 | 3` gives the same cap under both).

The arithmetic exhibits include `DUR-14`'s `T' ≤ max(T, now)` with `T' ≤ T` refuted (`F58`),
`DUR-22`'s half-value lemma with `restoreOne` admitting the remainder at every coverage (`F54`),
and the iterated `SPN-38` pass with `stuck_forever` versus `progress_on_F` (`F51`).

**7. Vocabulary.** `CONTEXT.md` owns the formal-layer vocabulary.
*Witness* is the segwit witness here (`CHN-9`), so a concrete input or trace the formal layer
executes is an **exhibit**; bare *model* is `ADR-0012`'s Model A, B and R, so the formal layer's
is the **formal model**, and a named one is a compound — *the release-gate model* — never bare.
*Oracle* has two meanings in this set and the formal layer takes neither: a surface that leaks
a secret (`NCH-3`) and, per `OPR-81`, "the word is reserved for implementation diversity" —
an independent tool that checks a ceremony artifact (`MAN-37`). A Lean evaluator a signer imports
is not an independent oracle for itself. The lifecycle and SILENCE terms — observer projection,
concealment horizon, refinement, trusted boundary — enter the glossary when the first model
uses them, not before.

**8. The reuse boundary.** `tools/formal/` is written for proof. The future
`btc-policy-lean` implementation imports it as a lake git dependency at a pinned commit, so each
clause has one definition, and that repository owns any optimized representation together with the
theorem that it agrees with the readable one. The gate and the emitters are library code so the gate
walks them (decision 3), and an implementation that imports the library takes them along; only
the executable roots sit outside it. The subdirectory packaging is tested in CI: a scratch
consumer requires `tools/formal` at the checked-out commit with `subDir` and builds a theorem
over the kernel. The implementation records its own conformance status per `OVR-17`.
No implementation, verifier or shadow node ever lives here. The signer also follows `STO-9`'s
"Lock order MUST be sign lock, then store lock, wherever both are held" and `STO-13`'s
"Lockdown deadline driver"; an actor design is a proposed amendment to
their owners, not conformance by a cleaner model.

**9. Acceptance and review.** A formal-layer commit goes through the ordinary review loop
like any specification commit. A released signature is keyed on its sighash message and input,
never on `commitment_id`. `CHN-24` binds "the coordinator-proposed `expiry`; and the
node's own `policy_version`", neither of which is in the transaction; `CHN-11` requires
"BIP143 P2WSH sighash computed with `SIGHASH_ALL`". Two requests over one transaction have
two commitments and one sighash per input, and a partial released under the first is finalizable
authority for the second. Exposure is keyed `(sighash message, input, signer)`, lives at world
level, and is never pruned by candidate eviction, settlement or node death. The retained trap is
`BtcPolicy.Exhibits.ReleaseKernel.exposure_key_exhibit`; `BtcPolicy.Kernel.exposedQuorum`
owns the argument against a node-local exposure history.

**11. Work is tracked in beads, prefix `bps`.** `.beads/` is committed;
`docs/agents/issue-tracker.md` says how. `16-open-findings.md`'s `F` numbers stay the register of
open design questions; a bead may cite a finding and a finding may cite the bead that works it,
and neither replaces the other.

**12. The release and Carrier kernel.**

### Clocks, transitions and proof boundaries

The clock types live in their own module with private constructors
and private fields, so a raw sample cannot be minted into another clock: `Effective.ofWall`
(`SPN-13`: "`effective_now = max(high_water, raw_now)`"), `Mono.deadline` returning `Option`
(`NCH-33`: "in checked arithmetic that fails closed"),
`Mtp` in the chain view, `Mono` with no generation index — a rebooted node is dead and the
HotClock is "process-lifetime" (`NCH-41`). `SPN-14`'s "handler generations" are memo
generations: `NCH-32` says "A memo generation is `(signature_tag, expiry, deadline)`". The term that retires a Carrier from a `Wall` is a type error and CI
compiles it and asserts the exact mismatch; a wall-to-wall
comparison that deletes a Carrier confuses no type, so retirement is also a guard
parameter with a behavioural flip (`NCH-35`: "Wall readings are attempt signals, not retirement authority"). A
forward-then-backward excursion keeps the intent under the current rule and loses it under
the withdrawn value (`DEF-1`). No `arm` event:
`DUR-10` gives `active` "exactly one writer — the holder decision with `arm = true`".
Arming is a receipt reaching `t` on a Carrier using `DUR-5`'s "pair duress bit", or its own
bit if unbound, in one step that opens the pair only with local acceptance authority, ORs the bit into every hot
candidate's freeze bit, sets `armed` and retires the Carrier. `DUR-9`'s
"Opening the pair and setting the arm bit MUST be one atomic write" is a theorem by induction,
not a parameter, and a hot candidate accepted while armed is born frozen
(`DUR-11`'s "future"). Eviction is the chain view shrinking, an environment input. The
pending log is a projection of the registry by its flags, so `DEF-5` and `F57` row 8 are one
flag with one flip. A world step lifts the node step and carries exposure keyed (sighash
message, input, signer), a list whose membership is monotone under every event; the
no-hot-partial-while-armed invariant is over transitions, because an armed node still holds
the authority it released before. `packageAccepted` and `send` are two events, and `send`
re-authorizes and emits `broadcast` in one transition, the effect meaning irrevocable
submission: an implementation that unlocks between the recheck and the socket write refines
it, one that rechecks before assembly does not (`DUR-29`: "MUST be re-authorized under the store lock",
"immediately before the send"; `SPN-39`: "the linearization point between
arming and sending"). Partials expose at `firePass` (`SPN-38`: "queued for transport"), the transaction at `send`, nothing at
`packageAccepted`. Poison is a state bit the fire pass reads: the transition exists, emits
nothing and forces the latch, and the removed rule is the `DEF-4` flip. Settlement marks every
input-conflicting resident terminal; terminal is sticky and never due, each stated as a
property so the flag cannot be vacuous. Bounded enumeration is an exhibit over a stated
start state and alphabet with no completeness claim.

The sighash boundary is the fixed symbolic definition `BtcPolicy.Kernel.sighash`,
returning `(tx.id, i)` over `Kernel.Sighash`, an abbreviation for `Nat × Nat`. It reads only
the transaction's abstract identity `tx.id` and the input index, with no request fields;
it does not inspect the other fields of `Tx`. There is no pluggable function field or BIP143
instance. `CHN-11` requires "BIP143 P2WSH sighash computed with `SIGHASH_ALL`", over the
"whole two-branch witness script" and "with the input's `witness_utxo` value". Computing
those bytes and their digest, and proving their cryptographic binding, remain outside the
formalization. Adding framing would require a separate decision and would
establish a field layout alone, not cryptographic binding (decision 3 and `Encode`'s module
documentation). Unforgeability, backend truth, delivery, lock discipline and the `≤ t − 1`
compromise bound stay hypotheses the module docstring names. The selected-Escape, accounting
and SILENCE rules are in decision 14.

### Relay provenance and possession

A relay carries the wire's `sender_node_id`; a Carrier holds distinct relay senders in place
of a count. `BtcPolicy.Kernel.Carrier` owns the argument, and
`BtcPolicy.Exhibits.ReleaseKernel.duplicate_relay_is_one_holder` checks it (`F65`).
Finalizability is `BtcPolicy.Kernel.exposedQuorum` over the world's exposure (`POL-18`) and
`BtcPolicy.Kernel.heldQuorum` over the candidate's held set (`DUR-28`).
`BtcPolicy.Kernel.packageAccepted` reads possession behind this node's own release;
`BtcPolicy.Kernel.receivePartial` supplies authenticated possession and appends exposure.
The arguments and named per-input and per-rung possession boundaries live at
`BtcPolicy.Kernel.exposedQuorum` and `BtcPolicy.Kernel.receivePartial`.
`BtcPolicy.Kernel.packageAccepted` owns the limitation of the `released` proxy and the
fire-pass assembly token carrying the selected rung needed when ladder and quota dimensions
enter the kernel. Exposure retains decision 9's identity and lifetime.

### Registration

`SPN-32` owns compatibility and the indivisible refusal cases:
"Each resident MUST have the requested role (spend or Escape), the request's other id recorded as
its sibling, and the same transaction, hot classification and expiry." The decision rejects
completing a half-resident pair, treating equal per-id fields as sufficient for crossed or swapped
pairs, and rebirthing retained candidates. The ordered pair identity is stamped by
`Kernel.register`; incoming metadata has no authority. Equal-expiry assumptions cannot replace
an explicit one-member refusal. The formal model asserts no sibling co-residency property over unrelated
expiries.

`SPN-32` also owns the ladder comparison: "The resident Escape MUST also have the same **ordered
rung txids**, including the empty list." Comparing PSBT bytes would refuse valid re-encodings;
comparing lifecycle state could distinguish PINs. The kernel still has no ladder, so its exhibits
make no claim about that comparison. Runtime coverage lives in `CNF-34`.

Registration preservation and schedule reapplication are separate writes. `SPN-23` says
"re-applies its schedule, records its own intent (`DUR-4`), and re-stages"; retaining residents does not disable the
hot-acceptance shrink or traversal. `SPN-29` owns unwind: "only a reservation placed by this
request MUST be unwound in the same step." Its existing-reservation case is exercised through
`Ledger.sysStep`, alongside the no-new-row case, within the live reservation window.

The `Registration` guard parameter retains the historical rebirth behavior. The same
accept/settle/replay/receipt/fire trace releases a hot partial under `rebirth` and none under
`preserve`. General uniqueness and terminal-id proofs require `preserve`; their `current`
instantiations and the executable verdicts live in `Exhibits`. Registration refusal stages;
`SPN-5` row 29 owns that classification (Staging: "yes").

`Trace.Cand` represents candidate input, not a resident snapshot; `Trace.Cand.toKernel` leaves pair identity absent, and registration
derives it from the request positions.

### Refused Carriers

`DUR-4` owns pair availability: "its two commitment ids once `SPN-23` has computed them; an
intent refused before then names no pair". No earlier decoding or gate reordering is introduced.
`DUR-5` owns opening authority: "A refused Carrier MUST NOT open any candidate". It preserves
`DUR-4`'s "the duress bit MUST be set for a refused-but-staged duress request just as for an
accepted one" and "Ingress never arms". Selection follows `DUR-10`: "Every holder decision
whose intent names a pair". An unbound intent carries no fabricated selection id.

The kernel represents refused staging as ingress, and stores optional binding and local
acceptance separately from the intent's duress bit. `Kernel.refused_receipt_preserves_opening`
proves preservation of every resident's opening authority on reachable worlds. `RefusedOpening`
retains the historical grant to bound refused Carriers as `allStaged`; its distinguishing trace
and historical result live in `Kernel.RefusalCases`, and the current exhibits in `Exhibits`.

`Ledger.sysStep` stages budget refusal without reserving, and `Ledger.afterEvent` requires local
acceptance evidence before placing a reservation. `Silence.Input.refusal` applies the enrolment
table to a PIN-bearing refusal; the coupling and observation proof cover its ingress and holder decision. The formal model still
assumes authentication, PSBT validation and the upstream staging classification; it proves no
machine timing property.

### Pair inheritance

`DUR-5` owns the "pair duress bit" and its scope: "every resident intent and retained nonce
tombstone" naming the "same **spend commitment**". The holder decision uses the inherited bit throughout; `DUR-4` still says "Ingress never arms".
`SPN-32` still requires that "an already resident compatible pair is left exactly as is".
Metadata therefore belongs to the separate intents and their nonce tombstones, never to a
resident candidate. `DUR-5` preserves "A refused Carrier MUST NOT open any candidate";
binding associates a decision with a pair, while local acceptance grants opening authority.

`DUR-13` owns "the earliest `first_seen`" under "both PINs". The normal-first, duress-later
trace distinguishes this from both the deciding Carrier's own time and a duress-only minimum.
`NCH-40` owns retention "until both wall expiry and `D` have ended" and the explicit boundary
"no holder authority". Retirement after a completed decision retains the original metadata
just as deadline retirement does. A receipt addresses only a live Carrier, and retained nonce
identity prevents a replay from recreating it. `NCH-33`'s sample is "taken before authentication";
a wait before the ingress-hold sample can shorten `D` on correct clocks. The censor traces
therefore assume no lockstep between wall and monotonic samples.

The kernel's `Inheritance`, `IntentRetention` and `IngressTime` guard parameters each retain
a withdrawn value. `Kernel.InheritanceCases` owns their executable traces and historical
results; `Exhibits.Inheritance` owns the verdicts over `current`. The retention check isolates
that guard with inheritance enabled, and the time check isolates its guard with retained
metadata enabled. The workflow flips each independently, asserts the exact error count and
attributes every failure to its intended exhibit. Its list is the verification inventory.
`CNF-29`, `CNF-44`, `CNF-46`, `CNF-47`, `CNF-58` and `CNF-64` own runtime coverage.

The kernel represents completed holder decisions and the store prune driver's retirement.
Non-staged owner exits, unwinding, process death, nonce bytes, memo generations and capacity
accounting remain outside its event alphabet. Tombstones have no holder set or opening field.
The SILENCE projection retains their public metadata and erases only their duress bits.
Machine timing and allocation behavior require runtime evidence.

### Hot-release provenance

`DUR-8` owns the gate: a pair "waits for the holder decision of a Carrier naming it".
`Kernel.Execution` records the existing transitions from
exactly the `Kernel.Reachable` initial boundary; `reachable_has_execution` and
`Execution.reachable` connect the representations. History is proof evidence, never node state
or runtime authority. Opening provenance uses the actual inherited pair bit and local acceptance.
`DUR-8` states the counting corollary's premises: "conditional on
`BtcPolicy.Kernel.HonestExposureProvenance` for every relevant honest signer's row,
`BtcPolicy.Kernel.NoHonestNormalDecision` across all commitments on that message, and fewer
than `t` distinct compromised signers". It also bounds it: "the cross-signer hypothesis is
not proved for arbitrary environment-supplied rows".

`Kernel.ProvenanceCases` owns the executable inputs and the deliberately broken extra-writer
twin, which grants quorum at fire time without a holder decision. It is not a historical guard
value. `Exhibits.Provenance` holds the current verdicts, the general theorem's instantiation
after Carrier retirement, and the nonempty counting example with repeated signers and different
commitments on one message. The workflow remains the negative-control inventory. The proof adds no federation or runtime behavior.

**13. Pure models and their boundaries.** Classification uses abstract output kinds with
descriptor membership as the named `member` assumption (`POL-4`: "Descriptor membership MUST
be decided by **re-derivation and script equality**"). It covers `CHN-30`'s "The escape test MUST
run before the hot test for each output" and "the number of outputs that derive from the vault
descriptor MUST NOT exceed the number of inputs", request shapes, and the no-change value-flow
twin (`CHN-35`: "no vault-derived output") for the repeated burn
(`F57`), with positive exhibits for each request kind and mixed outputs passing the allowlist
but failing classification (`DEF-15`).
Policy derivation carries membership behind that assumption and `POL-6`'s "return the first
failure" order. The model equates the code set for `API-24` with the reachable set from that
order (`F57`); `API-24` says "every other code is reachable exactly as on a spend". `BtcPolicy.Membership` owns the structural membership derivation and its boundary.

The refresh-age alternation trace is admitted under `.perNodeLog` and refused under
`.chainMtp` (`F52`).
The counting theorem `(t − c) A ≤ (n − c) cap` for `POL-20`'s "**acceptance-time admission bound**"
is over a list of ledgers;
the release-cursor cross-node prefix overlap reaches a sweep rung (`SPN-38`, `DUR-28`).

The encoders (`CHN-25`, `WIR-18` to `WIR-27`) work over bound-field records with
`decode ∘ encode`, injectivity over the fields actually bound, and the theorem that signature
metadata is not bound. `CHN-24`'s "Two distinct transactions MUST never share a commitment"
rests on encoding injectivity plus a named collision assumption on the admitted domain.
The manifest preimage is schema 4 with version refusal (`MAN-2`, `MAN-3`). Maximum finalized
vsize is derived from serialization for every shape and admitted lock, with the accessor forms
`W_N − 1` and `W_N + 4` refuted (`CHN-34`, `F51`, `F56`).

**14. Selected Escapes, accounting and SILENCE.** The selected set is keyed by Escape id with
OR-merged bits and uniform window refresh. The denominator is computed from the chain view and
the set (`DUR-22`); `BtcPolicy.Coverage` owns its per-pass and across-pass guarantees and
boundaries. The accounting bridge makes `ADR-0014` a reachable refutation of the completion
bound while the admission theorem holds; `BtcPolicy.Ledger` owns the bridge.
SILENCE is a two-run relation over an observer projection with a stopped, sticky concealment
horizon under dynamic `T`, `DEF-12`'s marker and `F54`'s conditional traversal as the leaky
twins. `F3`, `F4` and `F13` stay traces with no repair chosen.

### Resubmissions and the observation walk

`SPN-23` says an accepted repeat "re-applies its schedule, records its own intent (`DUR-4`), and
re-stages". `Silence.wfEvent` does not exclude either incoming id because it is selected.
The actual `Silence.obsPair` walk covers these repeats, and `Silence.silence` proves observation
equality over that walk.

`Silence.NodeInv` carries duplicate-free resident ids. `Kernel.register_origin` separates
retained candidates from new births, and `Kernel.ids_nodup_step` carries registration uniqueness.
`Silence.inv_sysStep` preserves the invariant through the composed transition, including budget
refusal. Its window bound applies to selected candidates with opening authority: `DUR-10`
says "Every holder decision whose intent names a pair", while `DUR-5` says "A refused Carrier
MUST NOT open any candidate". Selection therefore implies neither residency nor opening.
A later registration can create a closed selected candidate; its holder decision installs the
window when it opens it.

The theorem assumes coupled initial states satisfying `NodeInv`, the rule parameters in
its signature, and `MonotoneSamples`. The relation stops at either entering state's concealment
horizon or its request-shape boundary: non-hot Escape and no incoming window-close values.
The initial invariant is discharged for the exhibits' common empty state, not for every state
admitted by `Kernel.Reachable.init`. No selected-id exclusion is hidden in a trace premise.

`Exhibits.TwoRun.resubmissions_full_prefix` checks full input length, both entering-state
horizons and equality of every observation for its trace family; the adjacent `silence_on_…`
theorems instantiate the general relation with discharged premises. The family covers the original
repeat, same-PIN and cross-PIN holder decisions, bound refusal before residency, and budget refusal
followed by acceptance. `Exhibits.TwoRun` also retains the real-horizon stopping and backward-clock
exhibits. The workflow's guard-flip steps hold the measured failures to their declarations.

The relation uses the observer fields and two-enrolment experiment in `Silence`.
The proof establishes no machine timing, allocation behavior, serialized size, federation-wide SILENCE or runtime conformance.
`DUR-1` remains normative.

**15. Backend, operator and trace boundaries.** The reorg cursor and cache models
(`DEF-6`, `DEF-21`) and the delivery reducer and watch selection (`DEF-8`, `F56`)
carry their rules in their modules. Implementation trace adapters are the boundary at which
`btc-policy-lean`'s runtime evidence meets the model (decision 8).

### Published synthetic trace

The block below is the language-neutral trace an implementation replays against the formal
model: one synthetic trace
over the kernel alphabet — accepted, relayed to a holder quorum, released on a fire pass, completed
by a peer's partial, package-tested and sent — with the effects the kernel emits carried on the
entries of the steps that emit them, so the verdict is stated over a replay that refuses an effect
on any other step. `BtcPolicy.Trace` owns the format: the versioned alphabet, which carries no byte
string, and its mapping to the backend and operator modules' inputs, `BtcPolicy.Trace.encode` and
`BtcPolicy.Trace.decode` with their round trip, the replay `BtcPolicy.Trace.replayKernel` and the
decided verdict `BtcPolicy.Trace.published_replays_with_current` over it, and the negative exhibits
that name the malformed shapes `decode` refuses and the misplaced effect the replay refuses.
`BtcPolicy.Render.traceVector` owns this region: the bytes are what the regions gate holds to the
encoding of the published trace, and the digest is what the vector gate recomputes from them, a
plain SHA-256 with no `tag =` line because the string is hashed by the gate alone and never by the
protocol. The replay adapter is implementation and lives in `btc-policy-lean` (decision 8); what it
must demonstrate over this block is `CNF-147` and `CNF-148` in `15-conformance-checklist.md`,
recorded per `OVR-17`. Every trace this repository publishes is synthetic — the project's rule,
stronger than `STO-11`'s — and no identifier in the block is derived from anything.

The format version is emitted in the region. Alphabet or layout changes change the version
byte and its digest. The current layouts carry the vault outputs a
ledger row's block spends (`LedgerRow.vaultSpends`), the wallet's list of completion markers,
and `vaultRepair`'s bracket view `atMarker` and walk above the settled block (`Scan`). The state
holds a single cache slot and the cold scan an in-progress repair started from as an optional
cache, holding re-import to that scan. `vaultServe` carries the view captured when the delta
walk starts after the views bracketing the wallet read; `WTC-6` measures the walk by "the tip
captured when the walk starts". `vaultRepairFailed`, tag 9, carries the state of the attempt
that stops before re-import. The state also carries a `bool` after the repair latch recording
whether a cold scan has replaced the cache since the latch set (`BtcPolicy.VaultUnspent.State`);
`BtcPolicy.VaultUnspent.refresh` reads it. `WTC-9` owns the rule: "From the latch setting until
a cold scan has replaced the cache, every refresh with no attempt in progress starts a repair
attempt from a cold scan, whatever cache it holds".

Refused-but-staged kernel ingress carries the
Carrier id, duress bit, signed expiry, optional computed pair and refusal code.
`BtcPolicy.Trace.KernelEvent.toKernel` maps it to refused staging. The codec's round-trip
theorem covers it; `BtcPolicy.Exhibits.Refusal.refused_trace_codec_and_replay` checks encoded
bound and unbound refusals, live holder decisions and the subsequent fire pass.

A trace of a superseded version is refused before anything else in it is read:
`BtcPolicy.Trace.decode_refuses_other_versions` is the rule over every other version byte;
the refusal exhibits are in `BtcPolicy.Trace`.

<!-- formal: BtcPolicy.Render.traceVector -->
```vector
preimage =
0506000000                                                          # version 5, 6 entries
8b000000013200000000000000050000000000000000000000010a00000000c8    # entry 1: kernel accept cid 10
0000000100000064000000010000000400000000000000640000000000000001
0000000000000000000000016400000000c80000000200000065000000020000
0004000000000000000400000001000000000000000000000000000000000000
00000000000000c800000000000000
22000000013200000000000000050000000000000000000000020a0000000100    # entry 2: kernel receipt cid 10 from 1
000000000000
300000000178000000000000003c000000000000000000000003010000001200    # entry 3: kernel firePass, emits queuePartial cid 1
0000016400000000000000000000000101000000
2e0000000178000000000000003c00000000000000000000000b640000000000    # entry 4: kernel receivePartial cid 1 from 1
000000000000010000000100000000000000
1e0000000178000000000000003c000000000000000000000004010000000000    # entry 5: kernel packageAccepted cand 1
0000
270000000178000000000000003c000000000000000000000005010000000100    # entry 6: kernel send cand 1, emits broadcast tx 100
0000050000000264000000
sha256 = 044512aa477ac903226ee0c1fc346101d8d95f20dbd7c1e24238c037c8b79fe1
```
<!-- /formal -->

## Considered options

**A separate repository for the model.** Rejected: a check that guards this set lives with it;
a check outside the repository can cease to exist without the set noticing. The separate
repository is for the implementation (decision 8).

**A hand-kept `requirements-map.json`.** Rejected as a third copy, and because a key naming
`CNF` ids is one regex away from being counted as coverage (decision 2).

**Lean is authoritative for everything, Markdown cites it.** Rejected: the citations gate cannot
read Lean, most of the set is prose no checker can carry, and a requirement is more than its formula.

**Tables alone guard the figures.** Rejected: a table-only port leaves inline copies unchecked.
The owning lists of negative controls are in `check_gate_controls.py` (decision 5). Replacing
repeated figures with citations cannot eliminate the copies gate: a refusal message needs the
literal value.

**An axiom policy only over tagged declarations, or an exemption for `Explore`.** Rejected:
an untagged `@[csimp]` lemma proved by `sorry` can register a compiler replacement for a tagged
definition and make the emitters print the replacement; a hand-written axiom named like a minted
one can hide under a namespace exemption. Decision 3 applies to every constant and refuses the
replacement attributes.

**Clock types alone prevent Carrier retirement by wall time.** Rejected: a wall-to-wall
comparison can delete a Carrier without confusing types. The behavioural guard and its
forward-then-backward trace live beside the clock boundary in decision 12.

**Bounded enumeration establishes a general safety claim.** Rejected: the send race is two
events from a package-accepted state and six from acceptance; three events from acceptance
silently miss the defect. Decision 12 requires a stated start and alphabet, without completeness.

**A model checker beside the proof assistant.** Not adopted: the safety results here are
inductive theorems over every reachable state — `BtcPolicy.Kernel.inv_reachable` and
`BtcPolicy.Kernel.no_hot_partial_while_armed` — while a bounded checker checks one fixed finite
instance to a depth and says nothing about the next size up. The lifted kernel invariant holds
for arbitrary `n` under arbitrary interleaving. Sharing a transition system is not the reason:
The exhibits and theorems in `BtcPolicy.Ledger` and `BtcPolicy.Silence` share their module's
`step`, while `BtcPolicy.Coverage` relates
independently supplied passes through shared definitions. `decide` over `BtcPolicy.Exhibits`
runs bounded exhibits, not general proofs. A checker can aid discovery on a measurement branch outside `main`, but a second statement
of a rule is a second normative copy with no gate holding it to the clause it restates.

## Consequences

`tools/formal/` carries `lean-toolchain`, `lakefile.toml`, `BtcPolicy/Req.lean`, and one module
per formal model under `BtcPolicy/`. `BtcPolicy.lean`'s imports are the list, read through
`lean --deps`, and the wrapper refuses a module missing from it, recursively.
`BtcPolicy/Exhibits.lean` holds the current exhibits; `BtcPolicy/Exe.lean` holds the gate and
emitters. The executable roots are `Gate.lean`, `Render.lean` and `Values.lean`, held to the
shape in decision 3. `tools/check_formal.sh` runs first in `tools/check-all.sh` and writes the
requirement index, regions and emitted values; `tools/check_copies.py` and
`tools/check_regions.py` read them and run last.

`.github/workflows/gates.yml` enters the nix shell and holds the list of negative controls,
one per formal check that has one. `check_gate_controls.py` owns the copies and regions lists.
The records in `docs/archive/` are non-normative, outside the gates' corpus and never a rule's home.
