# How Lean could strengthen `btc-policy-spec`

**My recommendation is to use Lean as an executable, theorem-backed semantic core of the specification, not initially as another production node implementation.**

The greatest opportunity is not adding more requirements. It is connecting the existing requirements so that their combined consequences can be checked: which state transitions preserve safety, which assumptions a guarantee actually needs, and which plausible-sounding guarantees are false.

I reviewed the repository at commit **`aa46b1c286a3f29b0dbac62adcbf63904e96f02b`**, including the protocol and security requirements, operator workflow, relevant conformance cases, defect and finding histories, and existing verification gates. This is a specification-level analysis, not a claim that the design or its implementations have now been formally verified.

## 1. What matters about this particular system

This is considerably more than a policy function attached to a multisig wallet.

The on-chain contract provides a user-plus-federation Normal path and a separate, timelocked 2-of-3 Recovery path. Much of the intended protection is enforced **off-chain**, through withholding signatures, candidate lifecycle rules, duress handling, immutable configuration, and the operator procedure. The nodes—not the coordinator—assemble and broadcast ordinary transactions.

The three request types also have materially different security arguments:

| Request  | What authorizes its behavior                                                                                 | Important distinction                                          |
| -------- | ------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------- |
| Spend    | User and coordinator authorization, PIN processing, mandatory Escape, Hold, Hot budget, holder/release rules | A refusal can still need to propagate or stage duress evidence |
| Refresh  | User and coordinator authorization, chain-derived age, refresh fee bounds, subordination                     | No PIN and no Hold                                             |
| Clawback | User and coordinator authorization, escape-only outputs, no vault change                                     | No PIN, no refresh interval, and no refresh-specific fee cap   |

These differences are explicit in the current model and should remain distinct in any formalization. In particular, the new pin-less clawback must not be modeled as merely another refresh or another duress spend.

The repository already does substantial verification work. Its seven gates check identifiers, fixtures, obligations, coverage, citations, vectors, and arithmetic. Its mutation controls deliberately break documents and require the intended gate failure. That is a strong base, but it does not establish that the interacting protocol rules imply the security claims.

**Lean should fill that semantic gap rather than replace the existing gates.**

---

## 2. The different ways to use Lean

I would distinguish these mechanisms rather than treating “formal verification” as one activity.

| Mechanism                                      | What it adds                                                    | Best application here                                                 |
| ---------------------------------------------- | --------------------------------------------------------------- | --------------------------------------------------------------------- |
| **Validated types and constructors**           | Makes distinctions and admissibility conditions explicit        | Clock domains, manifest validity, request classes, identifiers        |
| **Executable specification**                   | Defines exact decisions independently of production code        | Policy evaluation, classification, gate outcomes, canonical encodings |
| **Mathematical proofs**                        | Establishes parameterized results rather than checking examples | Admission bound, coverage intersection, fee and size bounds           |
| **State-machine invariants**                   | Proves properties survive every modeled transition              | Carrier lifecycle, replay, freezing, release, poison, node death      |
| **Relational proofs**                          | Compares executions that differ in secret state                 | SILENCE and armed-versus-idle behavior                                |
| **Counterexample exploration**                 | Finds and preserves executions disproving excessive claims      | Delayed completion, clock excursions, partitions, historical defects  |
| **Refinement proofs and differential testing** | Connects an abstract specification to a more concrete system    | Multiple implementations and concurrency-sensitive paths              |
| **Verified artifact checkers**                 | Checks concrete outputs against proved predicates               | Sealed manifests, ceremony artifacts, migration evidence              |

These mechanisms reinforce one another. For example, an executable state machine can generate traces for tests, support an inductive safety proof, and replay a counterexample against a deliberately broken version.

The theorem names and contracts below are **proposed deliverables**, not existing Lean results.

## 3. First establish the right semantic model

Before writing proofs, I would make three modeling decisions explicit.

### 3.1 Separate the different kinds of identity and authority

This is one of the most important issues in your system.

You have several identities that intentionally bind different things:

* The Bitcoin transaction and its per-input signature messages.
* The protocol commitment, which additionally includes fields such as expiry and policy version.
* The coordinator-authenticated request, which binds exact request data.
* The Carrier identity, which is node-local and memory-hard.
* The channel envelope, which identifies an individual transport attempt.

These are not interchangeable. The commitment encoding and coordinator request encoding have different field sets, and Carrier identity is salted per boot rather than globally identical across nodes.

**A fresh protocol commitment is not necessarily fresh Bitcoin spending authority.**

An off-chain expiry or a different commitment ID does not make a previously released Bitcoin signature unusable. Your operator specification already acknowledges a related distinction: a signature authenticates transaction bytes, not an authorization’s “base Escape” versus “rung” label.

Consequently, the formal model should track released signatures by the **actual Bitcoin signature message and input**, not only by `commitment_id`.

Otherwise, it could incorrectly prove safety by placing reusable signatures into separate commitment buckets.

### 3.2 Model historical exposure outside local node state

A useful abstract world would contain something like:

```text
World
  immutable vault and manifest
  local state of each node
  messages and pending transport work
  historically exposed signature authority
  historically compromised keys
  chain and mempool views
  wall-clock readings per node
  monotonic-clock readings per node
```

The exposure history must survive candidate pruning, request expiry, node death, and removal of a transaction from a mempool.

Your ledger already treats exposed partials differently from unexposed reservations. Your one-shot lifecycle erases local state, but that must not be modeled as revoking material already copied elsewhere.

I would also specify the exact exposure boundary. Conservatively, a share may need to count as exposed once handed to an outbox that can transmit it without another authorization check—not merely once a peer acknowledges receipt.

### 3.3 Model results as effects, not just acceptance booleans

For the stateful protocol, this is insufficient:

```text
request → accepted | refused
```

A better semantic result is:

```text
request + state + environment
  → verdict
  + new state
  + outbound work
  + public observations
  + abstract work trace
```

This follows directly from `SPN-5`: different refusal paths have different nonce, propagation, and holder-staging effects. A model that treats every refusal as “nothing happened” would omit part of the duress mechanism.

---

## 4. Concrete formalization targets

### A. Pure policy evaluation: the easiest useful executable specification

`03-policy-checks.md` is a natural starting point because it explicitly separates pure evaluation from clocks, chain queries, PIN checks, and mutable state. It also distinguishes evaluation from transaction classification. A mixed hot-plus-escape transaction can pass individual destination checks and still need to fail classification.

I would write both:

**A declarative acceptance predicate**, expressing what must hold.

**An executable checker**, implementing the specified ordering and returning the exact structured refusal.

Then prove:

$$
\operatorname{checkPolicy}(p,x)=\operatorname{accepted}
\iff
\operatorname{PolicyAccepts}(p,x)
$$

The two directions matter. Soundness alone would permit a checker that rejects everything.

Beyond acceptance, prove the **first-failure semantics**. A transaction that violates both the allowlist and the Hot cap must return the earlier refusal, not whichever check an implementation happens to run first.

Specific targets include:

| Proposed property                                                          | Requirement connection |
| -------------------------------------------------------------------------- | ---------------------- |
| Accepted inputs belong to the vault                                        | `POL-9`                |
| Derivation hints cannot turn an unauthorized output into authorized change | `POL-10`               |
| Hot outflow has exactly the specified exclusions                           | `POL-11`               |
| Empty input/output sets are rejected                                       | `POL-7`                |
| Mixed hot/escape outputs cannot acquire Escape privileges                  | `CHN-30`, `CNF-22`     |
| Classification respects the escape-before-hot precedence                   | `CHN-30`               |
| Refusal precedence is deterministic                                        | `POL-6`, `CNF-14`      |

These are already important conformance obligations. Lean would turn them into statements over all modeled inputs rather than only generated examples.

**Implementation detail:** prove arithmetic first over mathematical integers or naturals, then separately prove that the bounded implementation reproduces it, including overflow refusals. A proof over unbounded integers does not establish correctness of a wrapping machine-integer implementation.

### B. Wire contracts: prove binding, not merely matching vectors

The wire layer is unusually suitable for formalization because the repository already specifies canonical encodings precisely.

It also contains distinctions easy to lose during reimplementation: commitments use big-endian encoding, other signed preimages use little-endian encoding, displayed txids differ from internal byte order, and coordinator nonces differ from channel nonces in how their bytes are interpreted.

The initial proofs should establish:

$$
\operatorname{decode}(\operatorname{encode}(x))=\operatorname{some}(x)
$$

and, on the admitted domain:

$$
\operatorname{encode}(x)=\operatorname{encode}(y)\Rightarrow x=y
$$

Also prove exact encoded lengths, checked integer widths, and canonicalization idempotence.

There is an important specification-strength correction to make explicit here:

**Encoding injectivity and hash collision resistance are different claims.**

The former can be proved directly. Universal injectivity of SHA-256 over a larger message space cannot be true. Therefore, wording about distinct transactions always receiving distinct commitment IDs should be decomposed into:

> Distinct semantic commitment records have distinct canonical encodings. Treating their hashes as distinct additionally relies on the cryptographic binding assumption.

This would make `CHN-24` and `CNF-9` more precise without changing the intended protocol.

The same module should formalize **what is deliberately not bound**. Two PSBTs can share a transaction commitment while differing in metadata relevant to validation. That makes the replay-cache key a separate proof obligation:

> Correcting previously invalid signature or prevout metadata must force the required reevaluation rather than inherit a cached refusal.

Your current replay requirements already address this. Lean would help ensure the key definition and the checker’s actual dependencies remain aligned after future changes.

A later extension would prove that the fixed vault script implements the intended Normal and Recovery branches under an explicitly selected script-validation semantics. I would not start by formalizing all of Bitcoin, and I would keep consensus validity, relay standardness, and your narrower accepted profile distinct.

### C. The release gate: the highest-value security proof

This is where I would put the most formal-methods effort.

The core argument is **not** simply:

> Two threshold quorums intersect.

For \(n=2t-1\), two size-\(t\) quorums intersect, but their intersection can consist entirely of compromised nodes. For example, two 3-of-5 quorums can intersect in one compromised member.

Your specification instead makes the local release rule load-bearing: a pair remains closed until its own holder decision, and the opening/arming decision is atomic. Holder receipts do not by themselves mean that a signing quorum has honestly frozen.

I would prove this in layers.

**Local safety.** Every honest-node release event satisfies the candidate’s current authorization conditions. Closed pairs, frozen hot candidates, and poisoned critical state produce no prohibited egress.

**Transition preservation.** Every modeled transition preserves that invariant, including replay, holder confirmation, expiry, registration failure, timeout continuation, panic, and settlement.

**Federation consequence.** Combine the local result with distinct-signer counting and explicit cryptographic assumptions to establish the intended bound on newly available coerced spending authority.

The third layer must account for previously exposed signatures and per-input quorums. It must not silently assume that every finalized transaction uses one identical signer subset on every input.

There is also a concrete concurrency proof obligation: the reauthorization immediately before sending must genuinely be the linearization point. Your `CNF-143` already names the relevant race—arming or removal after package acceptance but before send.

**Do not prove only that `canRelease` returns false on frozen state.** Prove that no complete execution can emit the share or broadcast through another path after that authorization becomes invalid.

### D. The Hot-budget theorem: separate mathematics from accounting

`POL-20` is an excellent first mathematical proof.

Let \(c<t\) be the number of compromised nodes, and let the eligible admission cohort have total outflow \(A\). Each eligible spend needs at least \(t-c\) honest acceptances, while each of the \(n-c\) honest ledgers can account for at most `cap`.

Double-counting gives:

$$
(t-c)A\leq(n-c)\operatorname{cap}
$$

For \(n=2t-1\), that yields the specified factors, including \(2-1/t\) with no compromised nodes and \(t\) at \(c=t-1\).

But I would split the formal work into two deliverables:

**Combinatorial theorem:** the inequality follows from the per-node bounds and acceptance multiplicities.

**Accounting theorem:** the actual reservation, exposure, refund, and aging transitions establish those premises for the exact cohort defined by `POL-20`.

Without the second, we have proved the counting argument while assuming the difficult accounting is correct.

Equally valuable is formalizing the **counterexample to the stronger completion claim**. Your ADR describes a 2-of-3 execution where a first spend is admitted at time 0 but released at 100, then a second is admitted at 121 and released at 141. A 120-second completion interval contains \(2V\), despite all ledgers complying with their admission rules.

The arithmetic gate explicitly checks that example’s numbers, not a protocol execution. Lean could additionally establish:

> This trace is reachable in the model, its admission invariants hold, and the claimed rolling completion bound fails.

That is a strong use of formalization: **protect the specification from becoming more confident than its mechanism permits.**

### E. Clocks, expiry, and Carrier retirement

The clock rules deserve a dedicated module, not repeated arithmetic in unrelated proofs.

Use distinct types for wall instants, effective high-water instants, monotonic instants, durations, and chain median-time-past. Conversions between them should be named operations with explicit premises.

The Carrier’s monotonic deadline is fixed at acceptance, while receipt authority also depends on its signed wall-clock expiry. Wall movement must not retire or extend Carrier state, and holder eligibility, candidate expiry, and reservation retention use different boundary conditions.

Good targets include `carrier_deadline_immutable`, `wall_step_does_not_retire_carrier`, `retired_nonce_not_reanimated`, and `stale_cleanup_cannot_delete_new_generation`.

There is also a concrete wording issue formalization would clarify. `DUR-14` uses:

$$
T'=\max(\min(T,\operatorname{fireAt}-\epsilon),\operatorname{now})
$$

When `now > T`, the new numeric value can exceed the old one, although it means “act now,” not “grant additional delay.” Thus literal `T' ≤ T` is not the right unrestricted theorem. More accurate properties are:

$$
T'\leq\max(T,\operatorname{now})
$$

and:

$$
\operatorname{now}\leq T\Rightarrow T'\leq T
$$

This would reconcile the intended urgency rule with conformance wording that says the deadline never grows. I would treat this as a clarification of the formal claim, not evidence of a new exploitable defect.

Finally, keep three propositions separate: release remains safe, Lockdown does not depend on sweep success, and Lockdown eventually executes. The last needs scheduling assumptions. A finite latency bound needs stronger assumptions still, and the current specification explicitly claims none.

### F. SILENCE: a relational proof, not an ordinary invariant

SILENCE compares executions that differ in secret state. That requires a different formal mechanism from proving that one execution never reaches a bad state.

I would define an observer projection covering the specified response bytes, read surfaces, message shapes and lengths, and abstract work events. Then define the relation between two initial states and corresponding requests.

The desired statement is approximately:

$$
\operatorname{EquivalentPublicInputs}(w_1,w_2)
\Rightarrow
\operatorname{Observe}(\operatorname{run}(w_1))
=
\operatorname{Observe}(\operatorname{run}(w_2))
$$

up to the explicitly permitted reveal boundary.

The subtle part is the observer model. The coordinator sees the PIN bytes it relays. What it is not supposed to learn is whether those bytes match normal or duress enrollment. The two-world relation must represent that knowledge correctly rather than simply erase inconvenient observations.

Your deterministic conformance checks already compare handler operations, masked state projections, work counts, and public responses across normal/duress and armed/idle cases. They provide a useful starting observation vocabulary.

I would develop two separate results:

**Functional noninterference:** responses, public state, and protocol-visible effects do not distinguish the cases prematurely.

**Abstract cost noninterference:** the modeled work traces also agree.

Neither proves constant-time behavior of compiled code on actual hardware. Allocators, runtimes, caches, transport, and scheduling remain another assurance layer. The repository already recognizes that end-to-end timing assurance is not supplied by the current deterministic handler checks.

Also preserve your existing distinction: interimplementation JSON compatibility is generally semantic, whereas normal-versus-duress response equality is byte-level **within one implementation**.

### G. Escape selection and fee ladders

I see three separable proof families.

**Coverage intersection.** Given a common protected-value universe of value \(V>0\), two Escapes each requiring more than half that value cannot have disjoint input value. But the useful proof must connect the arithmetic to `DUR-22`’s actual denominator construction, including restoration of all selected Escapes’ inputs. Proving the half-value lemma alone does not verify the denominator.

Do not extend that result to arbitrary different snapshots or future deposits without another theorem.

**Selection and progress.** Prove the latch is monotone, selected rungs are admissible, emitted batches fit their budget, and the release cursor advances when a complete eligible rung fits. Your earlier cursor-anchoring defect is an ideal negative control: the broken formula should reproduce a stuck execution.

Progress of the local cursor is not a guarantee that a peer receives the messages.

**Size and fee bounds.** Prove the maximum finalized size from a serialization model, then prove admissible final witnesses fit it. Keep these distinct:

$$
v_{\text{actual}}\leq v_{\max}
$$

$$
\operatorname{fee}\leq Rv_{\max}
$$

The second does not imply actual feerate is at most \(R\). Your refresh cap is explicitly expressed against maximum finalized vsize. Lean would help preserve that precise meaning rather than let a variable named “feerate cap” acquire a stronger interpretation.

### H. Refresh and clawback need different multi-transaction arguments

For refresh, the interesting result concerns **coin lineage across confirmations**, not merely one accepted transaction.

The model should show that refreshing creates new outputs whose chain-derived age must satisfy the interval before another refresh can consume them. Alternating which honest node participates cannot bypass that shared chain fact. This directly addresses the historical per-node-history weakness recorded in `F52` and `CNF-139`.

Replacement, confirmation, and reorg behavior must remain explicit. A chain-MTP theorem should not be advertised as an unconditional real-wall-clock burn-rate theorem.

For clawback, the argument is different:

> Every output leaves the vault for the escape descriptor, so the transaction does not preserve vault change that can fund the next iteration of the same fee-burning attack.

Formalize that as a value-flow property and preserve a counterexample for the old change-permitting variant. The claim concerns the swept value and its descendants under stated assumptions, not an unlimited future in which new funds can be deposited.

The compromise matrix should remain attached to those assumptions. In particular, control of the escape key changes the meaning of an otherwise valid clawback. A proof of “outputs reach the escape descriptor” is not by itself a proof that the owner retains the funds.

### I. Operator and ceremony semantics

These are good targets for smaller, bounded state machines.

For the operator, formalize monotonic delivery knowledge:

```text
DefinitelyNotSent → PossiblyDelivered
```

Once an attempt might have delivered bytes, a later error must not restore certainty of non-delivery. Exact chain observation, not a peer’s `accepted` response, establishes the command’s success condition.

Other useful properties are that the complete authorization group is validated before any signature, the signed display and ordered transactions match the approved preview, and ordinary composer paths cannot invoke a broadcast operation.

For the ceremony, a verified checker could establish that an accepted artifact set satisfies manifest, endorsement, threshold, and configuration constraints.

It cannot establish physical custody independence or unrelated-path seed independence that the artifacts do not reveal. Nor should an atomic-publication proof silently assume host-power-loss durability that the current publication procedure does not promise.

## 5. Use formal models to explore unresolved designs

Lean would also help before a design choice is settled.

For `F3` and `F4`, compare alternative clock/high-water rules against the same replay, retirement, and receipt-recovery properties. For `F39`, vary network partition and delivery assumptions explicitly instead of inheriting conclusions from loopback topology.

For the lifecycle decision, retain the current one-shot model and separately model a hypothetical restartable node. Then ask which restored states are necessary to preserve invariants. This would make the requirement to protect all five safety-bearing state categories a compositional argument rather than a checklist alone.

For composition failures such as `F1`, the question can be framed as satisfiability:

> Does any transaction exist satisfying the inventory, coverage, fee, dust, and size constraints?

A checked witness or counterexample is useful even when no universal success theorem is possible under the chosen assumptions.

Bounded exploration is not an unbounded proof. Likewise, a counterexample in an abstraction must be checked for realizability before it is reported as a protocol defect.

## 6. Connecting this to multiple implementations

I would support three integration levels.

### An executable oracle first

Expose pure Lean functions over a language-neutral test format. Feed the same canonical transactions, configuration, clocks, chain snapshots, and protocol events to the Lean model and each implementation.

Compare more than verdicts: first refusal, state effects, reservations, outbound messages, release events, and public projections all matter.

Cedar provides a directly relevant example: its project maintains a Lean formalization and differential randomized testing against the Rust production implementation. ([GitHub][1])

For stateful tests, equality must account for permitted nondeterminism. Different node histories are not automatically a violation. Either inject equivalent environments or check that each implementation trace is permitted by the abstract transition relation.

### Refinement proofs for selected components later

For a critical component, define a relation \(R\) between concrete and abstract state and prove that each concrete operation corresponds to permitted abstract behavior:

$$
R(c,a)\land c\rightarrow c'
\Rightarrow
\exists a',\ a\rightarrow^{*}a'\land R(c',a')
$$

This is particularly relevant to split-phase preflight and reauthorization: the abstract atomic operation must be justified by the actual lock boundaries and intervening checks.

Aeneas is worth piloting for suitable pure Rust components. Its purpose is translating Rust into functional representations for theorem provers, but its documentation lists important limitations, including concurrent execution. I would not assume it can verify the whole asynchronous node. ([Aeneas][2])

### Keep implementation diversity meaningful

I would **not** begin by making every production implementation call one shared Lean runtime library.

Use the same formal contract and test corpus, but retain independent implementations. Shared specification mistakes remain a correlated risk, so the formal definitions themselves deserve independent review.

Veil is worth evaluating for state-machine exploration and invariant discovery. It is embedded in Lean and targets transition-system safety, with concrete and symbolic checking examples. Its current repository describes a pre-release, and liveness remains a future direction, so pin and assess a version rather than treating it as a turnkey solution. ([GitHub][3])

## 7. Repository structure and proof discipline

I would begin with a small `formal/` subtree, growing it only as properties become concrete:

```text
formal/
  lean-toolchain
  lakefile.toml
  BtcPolicy/
    Types.lean
    Policy.lean
    Wire.lean
    Budget.lean
    State.lean
    Carrier.lean
    Release.lean
    Observations.lean
    Counterexamples.lean
  requirements-map.json
```

The initial authority rule should be simple:

**The existing requirements remain normative. The Lean model is a checked semantic companion, with explicit mappings and explicit disagreements.**

Later, selected byte layouts or decision tables could have a formal definition designated as their canonical owner. That should be an explicit change, not an accidental second source of truth.

For each important property, record its requirement IDs, formal statement, assumptions, proof status, and implementation evidence separately. “The model theorem is proved” and “the implementation has passed conformance traces” are different facts.

A prose change should flag the mapping for review. Lean cannot determine automatically that a changed English paragraph was translated faithfully.

### Audit assumptions, not merely build success

Lean permits axioms, and unfinished proofs can depend on `sorryAx`. Current `native_decide` also introduces invocation-specific axioms for native evaluation. The toolchain provides ways to inspect transitive axiom dependencies. ([Lean Language][4])

Therefore, I would require pinned toolchains, checked proof dependencies, explicit cryptographic/environmental assumptions, and review of changes to theorem statements. Do not accept “the proofs still build” when someone has weakened the proposition or strengthened its premises.

For particularly important results, independent proof validation is an additional option, with the validation method and its trust assumptions recorded. ([Lean Language][5])

### Prevent vacuous success

A model that rejects every request can satisfy many safety statements.

Require constructive successful executions alongside prohibitions: an honest spend completes, duress reaches the intended safety state, clawback works without a PIN, and Recovery becomes possible under its conditions.

Also carry your existing mutation-testing philosophy into the formal layer. Deliberately reintroduce premature pair opening, wall-based Carrier retirement, incomplete replay keys, mempool-based refunds, global-only Escape activation, or the wrong release-cursor anchor. Require a meaningful proof failure or checked counterexample—not an unrelated build error. The repository already supplies the history and testing philosophy for this.

## 8. What I would implement first

| Priority                           | Deliverable                                                                        | Why this order                                                                                |
| ---------------------------------- | ---------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- |
| **First pilot**                    | Hot-budget model, general admission theorem, and delayed-completion counterexample | Exercises both proving a true guarantee and rejecting a false stronger one                    |
| **Parallel early work**            | Pure policy/classification and wire encoders                                       | Immediately useful as independent executable oracles                                          |
| **Next security milestone**        | Carrier, exposure history, pair opening, freeze, and release model                 | Captures the central duress safety argument                                                   |
| **Next relational milestone**      | SILENCE over specified observations and abstract work                              | Builds on a precise state and event model                                                     |
| **Then broaden**                   | Escape coverage/ladder, refresh lineage, clawback value flow, operator delivery    | Extends assurance across the major supporting mechanisms                                      |
| **Later implementation assurance** | Targeted refinement and fixed-script semantics                                     | Connects the model more tightly to production behavior without starting with the entire stack |

My strongest recommendation is to make the first pilot a **vertical slice**, not a collection of disconnected arithmetic lemmas:

> Define the budget state and exposure semantics, prove the admission bound, establish a reachable delayed-completion counterexample, and replay corresponding traces against an implementation.

That would demonstrate the whole workflow while addressing a distinction the project has already found easy to misstate.

After that, concentrate on the release/Carrier model. SILENCE should follow once the state and observation boundaries are precise.

**The result to aim for is not “this vault is formally verified.” It is a collection of narrowly stated, connected guarantees: what is proved, under which assumptions, against which semantic model, and with what evidence linking implementations to it.**

For this repository, that would be a substantial improvement over either more prose review or a Lean rewrite alone.

[1]: https://github.com/cedar-policy/cedar-spec "https://github.com/cedar-policy/cedar-spec"
[2]: https://aeneasverif.github.io/aeneas/ "https://aeneasverif.github.io/aeneas/"
[3]: https://github.com/verse-lab/veil "https://github.com/verse-lab/veil"
[4]: https://lean-lang.org/doc/reference/latest/Axioms/ "https://lean-lang.org/doc/reference/latest/Axioms/"
[5]: https://lean-lang.org/doc/reference/latest/ValidatingProofs/ "https://lean-lang.org/doc/reference/latest/ValidatingProofs/"

