# A formalized clause lives in Lean, the Markdown requirement renders it, and a proof is never conformance

Status: **accepted 2026-09-16** (proposed the same day against `lean-01.md` and `lean-02.md`,
both reviewed at `aa46b1c`; decided with the Operator in one session; amended and accepted after
two independent readers of one brief — a first and a second reader, neither seeing
the other — each ran Lean 4.30.0 and proved the six derivations of decision 5 before answering).
Both readers closed all six on core Lean under `propext`, `Classical.choice` and `Quot.sound`
alone, no `sorry`, no `native_decide`, no Mathlib, every file under half a second: `CHN-4` by
`decide`; `CHN-2` and `DUR-30` for every `t` and every median by `omega`; `POL-20`'s rational
coefficients per shape by `decide +kernel` and in general by `grind`; `ADR-0014`'s trace as data
by `decide`; `SPN-38`'s ten rows with the anchor as a parameter by `decide`, and the anchor flip
refuting the row theorems in both readers' mutants. Both said amend, then accept; the amendments
are decisions 5, 7, 9 and 10 below and the port adaptations. Does not amend the README's
"specifications only": the formal layer describes and checks the system and implements none of
it.

## The problem as found

The seven gates read the documents; one, `tools/check_arithmetic.py`, executes arithmetic. Nothing
checks that the interacting rules imply the security claims the set makes. The set's own record is
why that matters: `POL-20` once claimed a rolling completion-loss bound that a two-spend trace
refuted (`ADR-0014`), `SPN-38`'s release cursor anchored its cap on the wrong variable until a
boundary row exposed it (`F51`), `DUR-22`'s denominator shrank each time a selected Escape became
resident (`F54`), and the one-shot burn argument the claw-back rested on was false until a reviewer
showed the change-permitting variant (`F57`). Each passed every gate and at least two readers,
because each citation resolved while the consequences contradicted. `lean-01.md` and `lean-02.md`
both propose that a checker ask what a rule *implies*; `lean-01.md` also found that `DUR-14`'s
`T ← max(min(T, fire_at − ε), now)` can numerically exceed the old `T` when `now > T`, so `CNF-47`'s
"never grows" was the wrong theorem (`F58`, closed before the panel read).

`provisiond-spec` decided the mechanism on 2026-09-13 (its `docs/adr/0025`) and has run it green
since: `tools/formal/` in the specification repository, declarations tagged with the identifier
they formalize, an axiom gate, a rendering gate, historical defects as executable negative cases,
and a negative control per check in CI. This ADR ports that decision and records where this set
differs. The panel found that the port as first proposed would have lost seven of the fourteen
arithmetic negative controls; decision 5 is the repair.

## Decisions

**1. The formal layer lives in this repository, under `tools/formal/`, namespace `BtcPolicy`.**
(Decided 2026-09-16.) A formalized clause's home is its Lean declaration, tagged `@[req "POL-20"]`
with the identifier it formalizes; `lake exe gate` emits the requirement index from those
attributes and there is no other manifest. The Markdown requirement keeps its identifier, its
MUST, its rationale, its amendment record and its retained traps; its rendered formula, table or
figure is a copy of the declaration, held to it by a gate (decision 5). Until a clause's copy is
gated, the Markdown stays authoritative and the Lean is a checking interpretation. `lean-02.md`'s
separate repository for the model and `lean-01.md`'s hand-kept `requirements-map.json` are
rejected below.

**2. A theorem is never conformance.** (Decided 2026-09-16.) `tools/check_coverage.py` counts
conformance items and nothing from the formal layer; no `CNF` identifier appears in
`tools/formal/`. A proof is about the formal model under its stated assumptions; a conformance item
is about a running implementation (`OVR-17`). A conformance item may cite the theorem it
exercises; the theorem never cites the item. The first reader asked to admit `CNF` ids in
comments; refused — the coverage gate reads `*.md` today, and the ban is what keeps a future regex
from counting a docstring as coverage. A docstring names the race, not the item.

**3. Trust policy, enforced by the gate, plus kernel replay.** (Decided 2026-09-16; tactic notes
added by the panel; the `Explore` exemption withdrawn the same day by the review loop; the axiom
policy widened from tagged declarations to every constant on 2026-09-17.) Every constant of every
project module, tagged or not, in every namespace, may depend on `propext`, `Classical.choice` and
`Quot.sound` and on nothing else; `sorryAx` is refused transitively, wherever it sits; the project
declares no `axiom`, and the gate checks that promise for every constant rather than inferring it
from tagged dependencies; `native_decide` is refused everywhere, `BtcPolicy.Explore` included.
The policy was first stated over tagged declarations only, and a reviewer reproduced the gap: an
untagged `@[csimp]` lemma proved by `sorry` registered a compiler replacement for a tagged
definition, the emitters printed the replacement, and every step of the gate stayed green — so
the walk applies the one axiom filter to every constant, and `csimp` joins `implemented_by` and
`extern` in the source refusal, since the emitters must print what the kernel proved about.
`Explore` may hold untagged scratch, held to the same axiom policy as everything else, and
nothing tagged; the gate checks both. The exemption as first
decided — `native_decide` permitted under `Explore`, its minted axiom the one axiom the project may
hold — was withdrawn when the review loop showed, and a reviewer reproduced, that a hand-written
axiom named like the minted one, under `Explore`, passed every check; every repair of the
exemption's shape left another form, and the exemption bought nothing a `decide +kernel` in a
scratch file does not. The gate and the emitters are library code (`BtcPolicy.Exe`) so the walk
covers them; the three executable roots are one import and one `main` each, held byte for byte
by the wrapper. Exhibits over rationals close by
`decide +kernel`; general rational identities close by `grind` on core Lean; every `Nat` floor,
mod and inequality closes by `omega`; a predicate written as a `Prop` `def` needs a `Decidable`
instance beside it or `decide` fails to elaborate in a way that reads as a proof gap, so the
module template writes such predicates as `Bool`. No Mathlib: it is added only in a commit that
names the theorem it is for and the infrastructure it would otherwise rebuild, with the cache,
CI-time and version-coupling cost stated — "cannot close without it" is not the threshold, a
named need is. In addition to the axiom walk, `tools/check_formal.sh` runs
`lake env leanchecker --fresh BtcPolicy`, which replays every declaration through the kernel from
a fresh environment; the wrapper propagates its exit status and fails visibly when the tool is
missing. The walk refuses a proof that rests on the wrong axiom; the replay refuses an `.olean`
the build wrote that the kernel does not accept. The replay has no negative control in CI,
because such an `.olean` is not constructible from source; this sentence is the record of that.

**4. The nix shell is the one way to run the gates.** (Decided 2026-09-16.) `flake.nix` pins Lean
4.30.0 from nixpkgs and provides `python3` with `argon2-cffi` and `cryptography` for the vector
gate; `tools/requirements.txt` and the README's venv block are deleted, and CI enters the same
shell. A missing toolchain is a red gate, not a skipped one. One pin: `flake.lock`. The pilot runs
`check_vectors.py` on the nixpkgs versions before the venv block goes; the second reader noted that
nobody had.

**5. `tools/check_arithmetic.py` is split by what fails when the document changes, not by where
a number sits.** (Decided 2026-09-16; amended by the panel the same day.) Today that gate does two
things in one pass: it derives, and it reads every operand and result from the documents,
failing closed on unrecognised wording. The derivations — `CHN-4`'s BIP68 encoding and exact
days, `CHN-2`'s shapes, `POL-20`'s coefficients, `DUR-30`'s floor interval, `MAN-16`'s widths
(derivations, not copies: `63 − 1`, `⌈63/8⌉`, `8 × 2`), `ADR-0014`'s delayed-holder trace,
`SPN-38`'s boundary rows — become theorems, and the two tables become rendered regions. But a
theorem over Lean-side constants reads nothing of the document: `CHN-4`'s `4224679`, `CHN-2`'s
`8-of-15`, `POL-20`'s `(2 − 1/t)`, `DUR-30`'s `⌊median / 5⌋ × 5`, `MAN-16`'s `62` and `SPN-38`'s
two prose formulas are inline figures with no table to render, and both readers showed that seven
of the fourteen arithmetic negative controls go green after a table-only port. So the Lean build
also emits `values.jsonl` beside `regions.jsonl` — each named scalar or formula string a tagged
declaration owns — and `tools/check_copies.py` keeps the arithmetic gate's owner-reading regexes
and compares what it reads from each owning sentence, and from every copy of it (`CHN-1`, `CHN-8`,
`CHN-10` for `CHN-4`; `WIR-16` for `NCH-12`; `NCH-13`'s prune offset, its own declaration
defined equal to `NCH-12`'s bound), to the emitted value instead of
recomputing it. The Lean constant still cannot read the Markdown; Python reads both. Acceptance:
`check_gate_controls.py` keeps all fourteen arithmetic controls — eleven under the copies gate,
three (the two table edits and the dropped rows) under the regions gate, since a table is now a
region — and every one is still red after `check_arithmetic.py` is deleted, each for the gate
that now owns it. `provisiond-spec` deleted its
arithmetic gate outright; its two formulas had no inline copies.

**6. Every semantic choice a dated amendment changed is a parameter of the model that carries it**,
with a `current` value that is the requirement as it stands, and the module holds two theorems:
the bad trace is refused under `current` and admitted under the value that stood before.
(Decided 2026-09-16; scoped by the panel.) Not only Booleans: `SPN-38`'s anchor is
`Anchor.onF | Anchor.onCursor`, `DUR-22`'s restoration is `Denominator.restoreAll | restoreOne`,
the refresh interval's source is `.chainMtp | .perNodeLog`. CI flips `current` and requires the
named theorem red. The twin rule is for historically repaired semantics and their regression
coverage; a codec round trip or a general identity needs no twin, and is not decoration without
one. The one-token flip against the row theorems is the acceptance criterion, never a row's
shape: both readers proved that `a > 0` is necessary but not sufficient for `SPN-38`'s two
anchors to differ (`600 | 1 | 0 | 2 | 3 | 3` gives the same cap under both), so the table gate's
"a row with `a > 0`" guaranteed nothing.

**7. Vocabulary.** (Decided 2026-09-16; corrected by the panel.) `CONTEXT.md` gains
**specification gate**, **formal model**, **exhibit**, **assumption**, **property**, and — after
the panel — **guard parameter**, **negative control**, **rendered region**, **emitted value** and
**requirement index**. Two of `provisiond-spec`'s terms cannot be imported: *witness* is the
segwit witness here (`CHN-9`), so a concrete input or trace the formal layer executes is an
**exhibit**; bare *model* is `ADR-0012`'s Model A, B and R, so the formal layer's is the **formal
model**, and a named one is a compound — *the release-gate model* — never bare. *Oracle* has two
meanings in this set already and the formal layer takes neither: a surface that leaks a secret
(`NCH-3`) and, per `OPR-81`, "the word is reserved for implementation diversity" — an
independent tool that checks a ceremony artifact (`MAN-37`). The proposed ADR said "never a
checker"; that was wrong, and a Lean evaluator a signer imports is not an independent oracle for
itself. Terms the lifecycle and SILENCE work will need — observer projection, concealment
horizon, refinement, trusted boundary — enter the glossary when the first model uses them, not
before.

**8. The reuse boundary.** (Decided 2026-09-16.) `tools/formal/` is written for proof. The future
`btc-policy-lean` implementation imports it as a lake git dependency at a pinned commit, so each
clause has one definition, and that repository owns any optimized representation together with the
theorem that it agrees with the readable one. The gate and the emitters are library code so the gate
walks them (decision 3), and an implementation that imports the library takes them along; only
the three one-line executable roots sit outside it. The subdirectory packaging is tested in CI
since milestone 5 (2026-09-17): a scratch consumer requires `tools/formal` at the checked-out
commit with `subDir` and builds a theorem over the kernel. `btc-policy-lean` is created when the offline ceremony verifier of `lean-02.md` §4
starts — after the encoders, the schema-4 preimage and the `CHN-34` size model exist as
declarations — and records its own conformance status per `OVR-17`. No implementation, verifier
or shadow node ever lives here. `STO-9`'s lock order and `STO-13`'s dedicated driver are
requirements on that signer too; an actor design is a proposed amendment to their owners, not
conformance by a cleaner model.

**9. Acceptance and review.** (Decided 2026-09-16; one question settled by the panel; the second
panel ran 2026-09-17.) This ADR was accepted after the two-reader panel whose brief is
`.context/lean-panel-brief.md` and whose answers are beside it. Thereafter a formal-layer commit
goes through the ordinary review loop like any specification commit. The panel ran again before
the release-gate model on `.context/m4-panel-brief.md`: both readers built the kernel in scratch
Lean, closed every item on core Lean, said amend then build, and their amendments are decision 10
item 4. The two contested points were settled by execution as this decision asked: exposure lives
at world level (a commitment-keyed or node-local history loses the authority a partial released
under one commitment carries for a second over the same transaction, in both readers' probes),
and the pre-send re-authorization is the linearization point (the same trace broadcasts under the
withdrawn check-before-assembly value). What the readers refuted in the proposal: `DEF-1` is not
made unrepresentable by clock types (a wall-to-wall comparison that deletes a Carrier confuses no
type), an `arm` event has no writer in the set, and "three events deep" from acceptance never
reaches the race. One question the proposal listed as contested is not,
on the set's own text, and is settled here: a released signature is keyed on its sighash message
and input, never on `commitment_id`. `CHN-24` binds "the coordinator-proposed `expiry`; and the
node's own `policy_version`", neither of which is in the transaction; `CHN-11` signs the BIP143
sighash and nothing off-chain. Two requests over one transaction have two commitments and one
sighash per input, and a partial released under the first is finalizable authority for the
second. Exposure is keyed `(sighash message, input, signer)`, lives at world level, and is never
pruned by candidate eviction, settlement or node death.

**10. Scope, in this order.** (Decided 2026-09-16; reordered by the panel.) Each milestone's
acceptance criterion is a check that fails on a named recorded defect.

1. **Pilot, widened.** Decision 5 with its fourteen controls kept; the two tables as regions
   (`ADR-0014`'s emitted as `render` with its row labels in the declaration, so the numbers are
   compared, plus a rendered "cap on the cursor" column beside `SPN-38`'s so the distinguishing
   rows are visible); the `F51` anchor flip red at the row theorems; and three thirty-line
   theorems both readers closed in scratch and that each fail on a dated defect: `DUR-14`'s
   `T' ≤ max(T, now)` with the old `T' ≤ T` refuted (`F58`), `DUR-22`'s half-value lemma with
   `restoreOne` admitting the remainder at every coverage (`F54`), and the iterated `SPN-38` pass
   with `stuck_forever` versus `progress_on_F` (`F51`). Plus the CI controls, `flake.nix`, and the
   README, AGENTS and CONTEXT edits.
2. **Classification and claw-back conservation.** `CHN-30` with escape-before-hot order, the
   vault-output-count rule, `CHN-35` no-change as a parameter with the value-flow twin showing
   the repeated burn (`F57`), mixed outputs passing the allowlist and failing class (`DEF-15`),
   request-shape for all three kinds, positive exhibits for each so nothing holds vacuously.
   Over an abstract output kind; descriptor membership is a named assumption.
3. **Lifecycle arithmetic.** `F52`'s alternation table admitted under `.perNodeLog` and refused
   under `.chainMtp`; the `POL-20` counting theorem `(t − c) A ≤ (n − c) cap` over a list of
   ledgers; `SPN-38`'s cross-node prefix overlap reaching `DUR-28`'s rung. Pulled ahead of the
   encoders because it holds six dated defects to their three and is thirty-line theorems.
4. **The release and Carrier kernel.** (Amended 2026-09-17 by the second panel; both readers
   said amend, then build.) Four clock types in a module of their own with a private constructor
   and private fields, so a raw sample cannot be minted into another clock: `Effective.ofWall`
   (`SPN-13`), `Mono.deadline` returning `Option` (`NCH-33`'s checked arithmetic, failing closed),
   `Mtp` in the chain view, `Mono` with no generation index — a rebooted node is dead and the
   HotClock is process-lifetime (`NCH-41`), and `SPN-14`'s "handler generations" are `NCH-32`'s
   memo generations. The term that retires a Carrier from a `Wall` is a type error and CI
   compiles it and asserts the exact mismatch; but both readers compiled a wall-to-wall
   comparison that deletes a Carrier and confuses no type, so retirement is also a guard
   parameter with a behavioural flip (`NCH-35`: a forward-then-backward excursion keeps the
   intent as it stands and loses it under the withdrawn value, `DEF-1`). No `arm` event:
   `DUR-10` gives `active` "exactly one writer — the holder decision with `arm = true`".
   Arming is a receipt reaching `t` on a Carrier using `DUR-5`'s "pair duress bit", or its own
   bit if unbound (decided 2026-10-02, implemented 2026-10-03; see the inheritance amendment
   below), in one step that opens the pair only with local acceptance authority
   (amended 2026-10-02; see the refused-Carrier amendment below), ORs the bit into every hot
   candidate's freeze bit, sets `armed` and retires the Carrier (`DUR-5`); `DUR-9`'s atomicity is then a
   theorem by induction, not a parameter, and a hot candidate accepted while armed is born frozen
   (`DUR-11`'s "future"). Eviction is the chain view shrinking, an environment input. The
   pending log is a projection of the registry by its flags, so `DEF-5` and `F57` row 8 are one
   flag with one flip. A world step lifts the node step and carries exposure keyed (sighash
   message, input, signer), a list whose membership is monotone under every event; the
   no-hot-partial-while-armed invariant is over transitions, because an armed node still holds
   the authority it released before. `packageAccepted` and `send` are two events, and `send`
   re-authorizes and emits `broadcast` in one transition, the effect meaning irrevocable
   submission: an implementation that unlocks between the recheck and the socket write refines
   it, one that rechecks before assembly does not (`DUR-29`, `SPN-39`). Partials expose at
   `firePass` ("queued for transport"), the transaction at `send`, nothing at
   `packageAccepted`. Poison is a state bit the fire pass reads: the transition exists, emits
   nothing and forces the latch, and the removed rule is the `DEF-4` flip. Settlement marks every
   input-conflicting resident terminal; terminal is sticky and never due, stated as three
   properties so the flag cannot be vacuous. Bounded enumeration is an exhibit over a stated
   start state and alphabet with no completeness claim: from the package-accepted state the race
   is two events deep, six from acceptance, where "three deep" was a silent success under the
   flip. The sighash is a named boundary, a structure whose field is a function of the transaction
   and the input index and of no request field; milestone 5 supplies the BIP143 encoder as its
   instance, and unforgeability, backend truth, delivery, lock discipline and the `≤ t − 1`
   compromise bound stay hypotheses the module docstring names. Scope is hot egress: the Escape
   half of the race (selected removal), the overlay beyond `armed`, `selected_escapes`, the
   ledger and `T` arrive with milestone 7. Both readers put this before the full encoders: the
   most important state assumptions must not wait on a descriptor parser.
5. **Encoders, manifest and size.** `CHN-25` and `WIR-18` to `WIR-27` as encoders over bound-field
   records with `decode ∘ encode`, injectivity over the fields actually bound, and the theorem
   that signature metadata is not bound; `CHN-24`'s "Two distinct transactions MUST never share
   a commitment" reworded as encoding injectivity plus a named collision assumption on the
   admitted domain; `MAN-2`'s schema-4 preimage with `MAN-3` version refusal; `CHN-34`'s maximum
   finalized vsize derived from serialization for every shape and admitted lock, with the accessor
   forms `W_N − 1` and `W_N + 4` refuted (`F51`, `F56`). This is the trigger for `btc-policy-lean`.
6. **Policy derivation.** `POL-4` membership behind the named `member` assumption, discharged
   progressively; `POL-6` first-failure order; `API-24`'s code set equal to `POL-6`'s reachable
   set (`F57`).
7. **Selected Escapes, accounting and SILENCE.** The set keyed by Escape id with OR-merged bits
   and uniform window refresh; `DUR-22`'s denominator computed from the chain view and the set,
   with the across-pass claim returned to `DUR-22` as a precise gap if the normative construction
   does not supply it; the accounting bridge making `ADR-0014` a reachable refutation of the
   completion bound while the admission theorem holds; SILENCE as a two-run relation over an
   observer projection with a stopped, sticky concealment horizon under dynamic `T`, `DEF-12`'s
   marker and `F54`'s conditional traversal as the leaky twins. `F3`, `F4`, `F13` kept as traces
   with no repair chosen.
8. **Backend, operator and runtime refinement.** Reorg cursor and cache model (`DEF-6`, `DEF-21`),
   the delivery reducer and watch selection (`DEF-8`, `F56`), and implementation trace adapters —
   the boundary at which `btc-policy-lean`'s runtime evidence meets the model.

**Scope extension, 2026-09-21: message provenance.** (Narrowed by a three-reader panel whose
brief is `.context/f65-panel-brief.md`.) A relay carries the wire's `sender_node_id` and a
Carrier holds its distinct relay senders in place of a count. It reaches milestones 4 and 7 —
the Carrier and the receipt event are 4's, the two-run relation over them is 7's — and extends
neither acceptance criterion: both were met on the model as it stood, and this is a defect found
after them, not a criterion they missed. `F65` owns the defect, the argument for the repair and
the repair's own check. Decision 9 is untouched. The node-local finalizability predicate the same
panel proposed was adopted by the 2026-09-23 extension below.

**Scope extension, 2026-09-23: node-local possession.** (Settled by three further three-reader
panels whose briefs are `.context/f65b-panel-brief.md`, `.context/f65c-panel-brief.md` and
`.context/f65d-panel-brief.md`.) Finalizability is two predicates:
`BtcPolicy.Kernel.exposedQuorum` over the world's exposure (`POL-18`) and
`BtcPolicy.Kernel.heldQuorum` over the candidate's held set (`DUR-28`).
`BtcPolicy.Kernel.packageAccepted` reads possession behind this node's own release, and an
authenticated partial-receive event, `BtcPolicy.Kernel.receivePartial`, supplies possession and
appends exposure. Decision 9 is untouched: exposure is still world-level, still keyed
`(sighash message, input, signer)`, and still never pruned. Per-input and per-rung possession are
named boundaries, as is the fire-pass assembly token that replaces the `released` proxy when the
ladder and the quota enter the kernel. It reaches milestones 4 and 7 — the kernel and the receive
event are 4's, the SILENCE relation over the receive is 7's — and extends neither acceptance
criterion, for the same reason as the extension above. `F65` owns the argument.

**Published exhibit, 2026-09-24: the trace format.** The block below is the language-neutral trace
an implementation replays against the formal model, milestone 8's last item: one synthetic trace
over the kernel alphabet — accepted, relayed to a holder quorum, released on a fire pass, completed
by a peer's partial, package-tested and sent — with the two effects the kernel emits carried on the
entries of the steps that emit them, so the verdict is stated over a replay that refuses an effect
on any other step. `BtcPolicy.Trace` owns the format: the versioned alphabet, which carries no byte
string, and its mapping to each milestone-8 module's inputs, `BtcPolicy.Trace.encode` and
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

The version history below records subsequent publications of the block. Its format version is
emitted in the region. The existing trace's entry bytes are unchanged; the version byte and its
digest change when the alphabet or its layouts change.

- **Version 2** (`387505f`). The layout had already moved under version 1 without a change of
  number: a ledger row had gained the vault outputs its block spends (`LedgerRow.vaultSpends`), the
  wallet its list of completion markers in place of a single anchor, and the `vaultRepair` entry
  its second bracket view (`atMarker`) and the walk above the settled block (its `Scan`), all for
  the settled-depth amendment (`ADR-0024`). The catch-up amendment then replaced the state's two
  cache fields with the single cache slot and added the flag for a repair attempt in progress, and
  the number moved for all of them at once.
- **Version 3** (`bps-8s0.11.21`). Three changes, each because the model function an entry maps to
  changed. The `vaultServe` entry carries a third view, the one captured when the delta walk
  starts, after the view captured before the wallet's listing and the view read when its
  reconciliation ends: `WTC-6` measures the walk by "the tip captured when the walk starts", and
  the model had been reading the tip the refresh captured first. The state carries the cold scan a
  repair attempt in progress started from, as an optional cache where version 2 carried the flag,
  so that the re-import is held to that scan. And the `vaultRepairFailed` entry is new, tag 9, its
  one field the state: the attempt that stops before its re-import, which `WTC-9` now ends as a
  failure.
- **Version 4** (`bps-8s0.11.25`). One change. The state carries whether a cold scan has replaced
  the cache since the repair latch set, one `bool` after the latch
  (`BtcPolicy.VaultUnspent.State`). `WTC-9` as amended on 2026-10-02 turns on it — `WTC-9`: "From
  the latch setting until a cold scan has replaced the cache, every refresh with no attempt in
  progress starts a repair attempt from a cold scan, whatever cache it holds" — and
  `BtcPolicy.VaultUnspent.refresh` reads it, so the state a version-3 entry carries no longer names
  a state of the model.

- **Version 5** (`bps-8s0.34`, 2026-10-03). Refused-but-staged kernel ingress has its own
  tag, carrying the Carrier id, duress bit, signed expiry, optional computed pair and refusal
  code. `BtcPolicy.Trace.KernelEvent.toKernel` maps it to refused staging. The codec's
  round-trip theorem covers it; `BtcPolicy.Exhibits.Refusal.refused_trace_codec_and_replay`
  checks encoded bound and unbound refusals, live holder decisions and the subsequent fire pass.

A trace of a superseded version is refused before anything else in it is read:
`BtcPolicy.Trace.decode_refuses_other_versions` is the rule over every other version byte,
`BtcPolicy.Trace.wrong_version_refused` the exhibit at version 4,
`BtcPolicy.Trace.third_version_refused` the one at version 3,
`BtcPolicy.Trace.second_version_refused` the one at version 2 and
`BtcPolicy.Trace.first_version_refused` the one at version 1.

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

**11. Work is tracked in beads, prefix `bps`.** (Decided 2026-09-16.) `.beads/` is committed;
`docs/agents/issue-tracker.md` says how. `16-open-findings.md`'s `F` numbers stay the register of
open design questions; a bead may cite a finding and a finding may cite the bead that works it,
and neither replaces the other.

## Port adaptations the panel found

- **ADR placement.** `provisiond-spec`'s region gate finds the requirement whose body holds a
  region and refuses a mismatch with the declaration's tag; inside an ADR it finds none, so
  `ADR-0014`'s table tagged `POL-20` cannot pass the unchanged gate. The `Region` structure gains a
  `home` field the declaration states (`"ADR-0014"`), emitted with the region, and the gate accepts
  a region in `docs/adr/NNNN-*.md` exactly when `home` names it. No second map: the placement is
  the declaration's, and a region whose `home` names a file that does not exist is red.
- **Numeric tables render.** `match` compares backticked and bold tokens only; a bare number
  changed from 1 to 99 in a `match` cell is not drift. Every arithmetic table is `render`, with its
  prose labels carried by the declaration as `ldg31Table` does in the precedent.
- **Namespace.** The region gate's marker regex and the citation gate's name resolver are
  `Provisiond.`-specific; the port parameterizes both to `BtcPolicy.`. "Ported" means run.
- **Recursive modules.** The orphan-module check walks `BtcPolicy/*.lean`; a `BtcPolicy/Lifecycle/`
  layout needs it recursive from the first subdirectory.
- **Requirement ids in tags.** `check_ids.py` reads the requirement index and refuses a tag naming
  an identifier nothing defines.
- **The committed reviews are records, not owners.** `lean-01.md` and `lean-02.md` restate
  formulas the requirements own; the gates read them for ids and citations, and nothing cites
  them as the home of a rule.

## Considered options

**A separate `btc-policy-lean` repository for the model**, `lean-02.md` §8. Rejected: a check that
guards this set lives with it; the gates lived in a scratch directory once and ceased to exist
without anyone noticing (`README.md`). The separate repository exists, but for the implementation
(decision 8). Both readers concurred.

**A hand-kept `requirements-map.json`**, `lean-01.md` §7. Rejected as a third copy, and because a
key naming `CNF` ids is one regex away from being counted as coverage. Both readers concurred.

**Lean is authoritative for everything, Markdown cites it.** Rejected: the citations gate cannot
read Lean, most of the set is prose no checker can carry, and a requirement is more than its
formula.

**Delete `check_arithmetic.py` whole**, as `provisiond-spec` did. Rejected: seven controls lost
(decision 5). **Split by table versus sentence**, the proposal as first written. Rejected by both
readers for the same seven controls; the emitted-value comparison is the "inline span" mechanism
the proposal deferred, in its cheapest form.

**Rewrite `CHN-8`, `CHN-10`, `WIR-16` and `NCH-13` to cite their owners instead of repeating the
number.** Worth doing where a sentence survives it, but a refusal message needs the literal value,
so the copy gate stays.

**Mathlib from the first module.** Rejected on both repositories' evidence: nothing needed it, and
it costs a multi-gigabyte cache and an exact-tag coupling to the Lean version.

**`native_decide` for exhibits.** Rejected under `@[req]`: `decide +kernel` closes the same
exhibits under the standard axioms.

**Axiom walk without kernel replay.** Considered; the replay is one line and seconds, so it lands
with the pilot rather than later.

**Keep `requirements.txt` beside the flake.** Rejected: two pins for the same libraries.

**Land without a panel.** Rejected by the Operator, and the panel earned its round: it found the
seven lost controls, the insufficient `F51` row, the `oracle` contradiction and the ADR-placement
break, none of which the proposal's author had seen.

**`CNF` ids as labelled comments in `tools/formal/`**, the first reader's request. Refused
(decision 2).

**`lean-01.md`'s vertical-slice pilot** — Hot-budget model, admission theorem and
delayed-completion counterexample first. Rejected by both readers: the accounting theorem needs
the whole ledger model; it is milestone 7.

**Strict B → C → D**, the proposal's order. Rejected by both readers: the full encoders and
descriptor grammar can absorb a long period while the state assumptions the September defects
lived in stay untested. Milestones 3 and 4 now precede the encoders.

**Create `btc-policy-lean` now, empty.** Rejected: nothing to import until milestone 5, and an
empty repository is where scope leaks.

**A model checker beside the proof assistant.** (Rationale rewritten 2026-09-21; the decision is
unchanged.) Not adopted: the safety results here are inductive theorems over every reachable
state — `BtcPolicy.Kernel.inv_reachable`, and `BtcPolicy.Kernel.no_hot_partial_while_armed` for
"every reachable world, every rule value, every environment" — and a bounded checker produces no
such thing. It checks one fixed finite instance to a depth, and says nothing about the next size
up. Lifting the kernel invariant to `n` nodes under an arbitrary interleaving cost nine lines of
proof and holds for all `n`; no checker states that at any budget.

The earlier wording gave a different reason — that bounded traces are enumerated by `decide` in
the files the invariant proofs live in, so exhibit and theorem share one `step`. That is true of
`BtcPolicy.Ledger` and `BtcPolicy.Silence` and false of `BtcPolicy.Coverage`, whose theorems
relate independently supplied passes through shared definitions with no transition system joining
them. The decision does not rest on it. It also compared the wrong mechanism: `decide` over
`BtcPolicy.Exhibits` is how this set writes *exhibits*, which are bounded by construction and
meant to be; it is not how it proves anything.

What a checker does do better is discovery. Measured on one composed slice, a checker returned a
five-state counterexample in under a second where the same seeded break gave `decide` a bare
`false`. That is a reason to keep a measurement branch out of `main`, not to adopt a second
formalism: a second statement of a rule is a second normative copy, and nothing gates it against
the clause it restates.

## Consequences

- `tools/formal/` with `lean-toolchain`, `lakefile.toml`, `BtcPolicy/Req.lean`, one module per
  formal model under `BtcPolicy/` — `BtcPolicy.lean`'s imports are the list, read through
  `lean --deps`, and the wrapper refuses a module missing from it, recursively —
  `BtcPolicy/Exhibits.lean`, `BtcPolicy/Exe.lean` holding the gate and the two emitters, and the
  three one-line executable roots `Gate.lean`, `Render.lean`, `Values.lean`, held to that shape
  byte for byte. `tools/check_formal.sh` runs first in `tools/check-all.sh` and writes the
  requirement index, the regions and the emitted values; `tools/check_copies.py` and
  `tools/check_regions.py` read them and run last.
- `tools/check_arithmetic.py` is replaced by `tools/check_copies.py`; `tools/requirements.txt` is
  deleted; `flake.nix` and `flake.lock` are added.
- `.github/workflows/gates.yml` enters the nix shell and gains one negative control per formal
  check that has one. The workflow holds that list and nothing here restates it: the review loop
  that hardened the pilot added a control with nearly every finding, and a count or an
  enumeration written here was wrong within the day. The fourteen arithmetic controls carry over
  — eleven to the copies gate, three to the regions gate — with more beside them;
  `check_gate_controls.py` holds those lists.
- `README.md`'s gates table gains the formal, copies and regions rows and loses the arithmetic
  row; its ADR table gains this row and the two it was missing; `AGENTS.md` names the shell and the
  `@[req]` rule.
- `CONTEXT.md` carries the ten terms of decision 7 and the corrected `oracle` note.
- `16-open-findings.md` carries `F58`, closed; `00-overview.md` no longer says every node runs
  the same code (both landed before the panel read).
- `lean-01.md`, `lean-02.md` and both panels' briefs and answers are the record of how this was
  decided; the reviews at the root, the panels under `.context/`, which is not committed.

## Registration amendment — 2026-10-03

Accepted for `bps-8s0.29`. `SPN-32` owns compatibility and the indivisible refusal cases:
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
instantiations and the executable verdicts live in `Exhibits`. The refused-Carrier amendment
below adds staging to registration refusal; `SPN-5` row 29 owns that classification
(Staging: "yes"). The inheritance amendment below completes the metadata change while
preserving this registration rule. The SILENCE resubmission domain remains separate work.

The trace input schema stays at its existing version. `Trace.Cand` represents candidate input,
not a resident snapshot; `Trace.Cand.toKernel` leaves pair identity absent, and registration
derives it from the request positions. No encoded field or published trace byte changed.

## Refused-Carrier amendment — decided 2026-10-02, implemented 2026-10-03

`DUR-4` owns pair availability: "its two commitment ids once `SPN-23` has computed them; an
intent refused before then names no pair". No earlier decoding or gate reordering is introduced.
`DUR-5` owns opening authority: "A refused Carrier MUST NOT open any candidate". It preserves
`DUR-4`'s "the duress bit MUST be set for a refused-but-staged duress request just as for an
accepted one" and "Ingress never arms". Selection follows `DUR-10`: "Every holder decision
whose intent names a pair". An unbound intent carries no fabricated selection id.

The kernel now represents refused staging as ingress, and stores optional binding and local
acceptance separately from the intent's duress bit. `Kernel.refused_receipt_preserves_opening`
proves preservation of every resident's opening authority on reachable worlds. `RefusedOpening`
retains the historical grant to bound refused Carriers as `allStaged`; its distinguishing trace
and historical result live in `Kernel.RefusalCases`, and the current exhibits in `Exhibits`.

`Ledger.sysStep` stages budget refusal without reserving, and `Ledger.afterEvent` requires local
acceptance evidence before placing a reservation. Registration refusal keeps the ordered-pair
repair above. `Silence.Input.refusal` applies the enrolment table to a PIN-bearing refusal; the
coupling and observation proof cover its ingress and holder decision. The formal model still
assumes authentication, PSBT validation and the upstream staging classification; it proves no
machine timing property. The inheritance amendment below adds pair metadata without changing
local opening authority.

## Pair inheritance amendment — decided 2026-10-02, implemented 2026-10-03

`DUR-5` owns the "pair duress bit" and its scope: "every resident intent and retained nonce
tombstone" naming the "same **spend commitment**". Per-Carrier arming is withdrawn. The
holder decision uses the inherited bit throughout; `DUR-4` still says "Ingress never arms".
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
The SILENCE projection retains their public metadata and erases only their duress bits; the
existing observations, horizon and admitted trace domain are preserved. Machine timing and
allocation behavior still require runtime evidence. The trace format stays at version 5:
only derived internal state changed, and the published input/effect bytes still replay.
The separate resubmission-domain, provenance and BIP143-boundary work is not part of this amendment.
