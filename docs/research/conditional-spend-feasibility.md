The original analysis below assumed that nodes accept requests that omit full previous
transactions; its comparison of F48 options 1/2 is historical, not a current choice.
For stripped output, [OPR-46](../../17-operator-program.md) says
“Every `non_witness_utxo` is stripped from the WIRE PSBTs after verification”; options
1/2 therefore have no difference in parent admission. Supplied-parent handling still
differs: ignoring a supplied parent and verifying it are different rules. Option 3
refuses omission: `Feasibility.refuse_refuses_composed` rejects every stripped composed
request. Carrying parents instead can exceed body limits, as
`Exhibits.Feasibility.f48_moves_the_verdict` demonstrates. The
[owner's F48 decision](f48-node-prevtx-decision.md#decided-formatdecode-form) now forbids
parents at existing node-request decode steps, with its normative amendment pending.
The absent-parent feasibility conclusions under their stated model premises are unchanged;
no production or supplied-parent theorem is gained.
This record starts no consolidation work and amends no earlier record.

## What the evidence establishes

[The feasibility record](proof-boundaries.md#9-fast-exit-feasibility) separates
discovery, bounded existence and current construction. Discovery must obtain coins,
parents and authorization evidence within a coherent bounded view. Existence asks
whether some request fits. Construction asks whether the specified composer builds
one. Evidence for one is not evidence for all three.

`Feasibility` requests are abstract Escape requests. Primary Spend classification,
complete group policy, exact PSBT framing and base64 expansion are not modeled;
ladder modeling counts PSBTs without proving its complete shape. These examples
are not a production ceremony theorem, optimizer or universal fast-exit guarantee.
The assumed 400-byte per-input per-PSBT costs and 620-input capacity are model
figures, not production measurements. The exhibits assume 2-of-3, one P2WSH output,
primary and Escape on the wire, and a 1 sat/vB floor unless stated otherwise.

In [Feasibility.CountOnly](../../tools/formal/BtcPolicy/Feasibility.lean), for
every nonempty outpoint list `r` whose valued coins are a sublist of `s.read`,
`wireOk && ancestryOk && boundOk = true` must be equivalent to
`r.length ≤ N` and every selected coin passing `usable`. This is an assumption,
not a property of arbitrary inventories. `feasible_iff_best` additionally requires
`denominator = .restoreAll`, `external = .countedWhenSpent`, ascending read
outpoints, book values agreeing with every read coin, positive total and positive
coverage percentage. Only then does the best usable value at some count through
`N`, less that count's floor fee, characterize existence against the whole total.

`countOnly_of_slack` supplies that assumption for stripped requests when the parent
rule is not refusal, `vsizeOf N ≤ vsizeCap < vsizeOf (N + 1)`, shell plus
`N × psbts × perInput` fits the body, adding envelope fits the message, every read
parent exists and has bytes at most `m`, `N × inputMaps × m ≤ retainedCap`, and
every read coin's creator is absent from the mempool.

`compose_bounded` requires a non-refusal parent rule, `.restoreAll`,
`.countedWhenSpent`, ascending confirmed outpoints, agreement between book and
confirmed values, `Sweep.additions s.A s.b = []`, every confirmed coin's creator
absent from the mempool, and `composeEvery lim txid s = .ok q`. Its conclusion
is that this abstract `q` is bounded. Neither converse nor production completion
follows.

## F1: confirmed value can exceed construction or existence bounds

[OPR-33](../../17-operator-program.md) says “there is no coin selection and no
omission.” [DUR-22](../../05-duress-and-lockdown.md) says “What the coordinator
composes over (`OPR-33`) never changes this denominator.” Selection can change
the numerator and costs, never discard deposits from the denominator.

| State | Bound and stage | Does another selection help? | Evidence and limit |
| --- | --- | --- | --- |
| A normal bounded confirmed state fits. | Retention, preflight vsize and wire bounds pass. | Selection is unnecessary if the whole request covers. | `feasible_constructed` validates the abstract construction under its premises. |
| Many confirmed outputs accumulate. | The modeled vsize capacity binds at composition. | Sometimes: 620 of 1 213 equal coins cover the unchanged total. | `fragments_feasible_below` proves existence, not current selection. |
| A signer parent is large. | Retained full-parent bytes bind before retention. | Sometimes multiplicity falls enough; size alone is insufficient to refute existence. | `one_large_parent_composes` contrasts with `toxic_infeasible`. |
| A bounded selection exists but composition refuses. | Whole-inventory vsize preflight fails. | Yes: one valuable coin covers with dust still counted. | `dust_stops_composer_only` has 621 dust coins beside that coin. |
| No bounded request exists. | Retention or vsize and whole-denominator coverage conflict. | No selection can repair the state. | `toxic_infeasible` and `fragments_infeasible` quantify over every request. |

For a concrete example, [the existing toxic fixture](../../tools/formal/BtcPolicy/Exhibits/Feasibility.lean)
uses sixteen outputs worth 100 000 sat each from one parent. `huge` has
1 000 base bytes and 3 980 000 witness bytes; `huge_in_domain` establishes
the assumed consensus domain and space for the outputs. The denominator remains
1 600 000 sat. Eight inputs retain `8 × 2 × 3 981 000 = 63 696 000` bytes;
nine retain 71 658 000 bytes, exceeding 64 MiB, or 67 108 864 bytes.
The projection uses candidate multiplicity and both input maps. Eight inputs
provide only 800 000 sat before fees, half the denominator, below the model's
greater-than-half coverage floor. More inputs fail retention. Stripping wire
parents changes neither calculation. The existing `toxic_infeasible` establishes
the universal refusal under its model assumptions; these arithmetic steps are
not measurements or a new proof about production encoding.

F1 therefore has both construction-only failures and states without bounded
requests. Discovering every confirmed output does not cure either bound. A large
parent with sufficiently few selected outputs need not be toxic; missing signer
parents remain a separate refusal, even when wire admission accepts omission.

| Proposal | Layer it could improve | Remaining refusal or conflict |
| --- | --- | --- |
| Declare an unsupported-state boundary. | It makes discovery and construction refusals intelligible. | It creates no request in an infeasible state and needs an explicit supported-state promise. |
| Add bounded selection. | It could improve construction where existence already holds. | `OPR-33` says “no coin selection and no omission”; the owner has reopened it for design only (`bps-xmq1.9`, comment 364). No algorithm or amendment is adopted; skipped coins still count. |
| Constrain supported topology. | It could improve existence within a maintained domain and simplify discovery. | External deposits still enter coverage; topology cannot exclude them by wish. |
| Revise the proof carrier. | It could improve retention or wire feasibility and construction. | `CHN-22` requires a “full previous transaction”; replacing it needs an owner decision. |

The [composed-shape rule](../../02-onchain-contract.md) specifies “the destination
plus one mandatory vault-change output”; a two-change proposal conflicts with
that shape and needs an owner decision. [ADR-0022, decision 3](../adr/) says
“No minimum input count and no disjointness: a one-coin vault claws back its one
coin”. Its consolidation resolution stays closed. Reintroducing a disjoint-reserve
requirement as a claw-back prerequisite conflicts with that decision and needs an
owner decision; no such amendment is drafted here. `selection_ideas_compared`
also defeats treating every-coin, prefix or largest-first selection as a universal
optimizer. All alternatives remain proposals.

## F2: authorization and a bounded view are separate obligations

[OPR-34](../../17-operator-program.md) requires refusal of the “WHOLE inventory”
for a scanned confirmed coin absent at the same tip. OPR-39 says composition is
“confirmed-only” and future unconfirmed composition must “prove authorization
from the vault-spend ancestry — never merely from a script paying the vault”.
These construction rules differ from DUR-22's coverage of “unconfirmed outputs
whose parent transaction is in this node's vault-authorized set”.

| State | Discovery and current construction | Conditional existence |
| --- | --- | --- |
| A prior Spend remains resident. | Whole-inventory refusal applies; silently spending the remainder is not authorized construction. | `prior_spend_composer_refuses` admits confirmed value plus authorized change; `confirmed_only_undercovers` rejects the remainder. |
| Authorized ancestry is shallow. | Authorization evidence still needs a chosen discovery mechanism. | `shallow_chain_feasible` fits 24 candidate ancestors in the abstraction. |
| Ancestry is deep or unavailable. | Missing evidence refuses; depth cannot be solved by inventing authorization. | `deep_chain_infeasible` rejects every request at its state; unavailable signer parents independently obstruct bounded requests. |
| The view changes, evicts or later reappears. | A new coherent view and bounded retries are needed. | An old verdict proves no later existence or construction guarantee. |

[WTC-24](../../10-watchtower-and-chain.md) says “more than 24 distinct ancestors
is an error” and “Every parent MUST be resolved against ONE mempool snapshot”.
The deep fixture's tail has 24 ancestors while a candidate spending it has 25.
Its remaining confirmed value cannot cover the full denominator. Removing that
tail from selection therefore cannot help. Changed membership does not revoke
already authorized bytes: OPR-34 warns that “eviction does not prove the
already-authorized bytes cannot return”.

The missing bounded discovery contract must specify authorization evidence,
a coherent tip/mempool view, conflict and replacement handling, and explicit
count, depth, byte, call and retry limits. Their values are not selected here.
`gettxspendingprevout` plus qualified raw reads and bounded ancestry is only a
candidate. It is neither a hidden backend extension nor permission for a generic
wallet or mempool download.

OPR-32's closed set is “exactly nine calls”: `getblockchaininfo`,
`getbestblockhash`, `scantxoutset` over the definite vault script,
`gettxout(txid, vout, true)`, `getblockhash(height)`, block-qualified
`getrawtransaction(txid, false, blockhash)`, `getblockheader(blockhash, true)`,
`estimatesmartfee(6, "CONSERVATIVE")` and `getmempoolinfo`. It also says
“No generic method string, no batch, no wallet endpoint, no mutating or
broadcasting method, no cache, no background work.” Adding the candidate method
or widening raw-read qualification conflicts with that contract and needs an
owner decision. The amendment stops here.

F2's conclusion is conditional existence for some authorized shallow states,
current construction refusal, and genuine node-level infeasibility for the deep
fixture. A discovery mechanism cannot make an over-depth package admissible.

## Bounds and preserved authority

The ledger names the enforcing owners; equality behavior follows their quoted
contracts, rather than a new threshold policy.

| Resource and unit | Owner and enforcement stage | Failure and evidence |
| --- | --- | --- |
| Signer parents use retained bytes. | OPR-35 says “at most 64 MiB, equality passing”, before retention. | Multiplicity can refuse locally; `toxic_infeasible` exhibits this. |
| Finalized size uses vB. | OPR-35 says “at most 100 000 vB”, at zero-amount preflight. | Composition refuses before candidate reads; `vsize_capacity` is model evidence. |
| Raw JSON uses bytes. | [API-4](../../07-node-api.md) says “larger than 1 048 576 bytes”, before decoding. | Node failure is HTTP 413. |
| Encoded envelopes use bytes. | API-6 checks authenticated `max_msg_bytes`; [NCH-10](../../06-node-channel.md) says “The envelope body is bounded by `max_msg_bytes`”. | Node failure is HTTP 400; `ladder_lowers_capacity` uses assumed encoding costs. |
| Peer load uses authenticated envelopes per window. | NCH-15 specifies a “rolling quota” and “no fairness”. | `RATE_LIMITED` is not a delivery-time guarantee. |
| Ancestry work uses distinct ancestors. | WTC-24 bounds validation before assembly. | Deep ancestry refuses; proposed discovery byte/call/retry budgets remain unselected. |

OPR-46 separately requires a pre-PIN “worst-case request shell” and says “the
actual request is rechecked before ingress”. Its local typed refusal precedes
the node failures above; neither successful preflight nor spare quota proves
relay or confirmation.

DUR-22 requires “every distinct input outpoint of EVERY selected Escape counted
once” and “a counted input takes precedence over every exclusion”. Its entire
per-pass denominator, including restored selected inputs, stays authoritative under the
current rules. The [retained-floor design scope](milestone-3-decision-register.md#findings-evidence-and-completion)
allows proposals for accounting amendments only for owner approval; unchanged restoration
is not a blanket constraint on that reopened design. F1 selection still counts skipped coins,
and the other duties below remain preserved.
[SPN-25](../../04-spend-lifecycle.md) requires confirmed prevout script and value
“to equal the chain's”; no proposal substitutes script equality for backend truth.
CHN-11 retains `SIGHASH_ALL`. CHN-23 requires “validate a request's complete
transaction group and build every sighash before signing any”, with the pair
over “the same non-empty coin set”. CHN-16's “same ordered input set” and rung
shape remain obligations. OPR-35's bounds remain “refused BEFORE allocation”.

Topology changes must rebind the watched output: OPR-51 currently watches
“output 1 of the primary — its vault change”. SPN-32 requires registration
“as one **pair** in the candidate registry atomically”. Neither watch identity
nor atomic registration can be left behind by a shape change.

## Existing evidence and the scope decision

| Fixture identifiers in `Exhibits.Feasibility` | Purpose and limit |
| --- | --- |
| `dust_stops_composer_only`, `fragments_feasible_below` | They distinguish bounded existence from whole-inventory construction. |
| `fragments_infeasible`, `toxic_infeasible`, `missing_parent_infeasible` | They refute every bounded request within their modeled states. |
| `prior_spend_composer_refuses`, `confirmed_only_undercovers` | They expose authorized-change coverage and construction refusal. |
| `shallow_chain_feasible`, `deep_chain_infeasible` | They bracket candidate ancestry, without defining discovery. |
| `f48_moves_the_verdict`, `armed_no_fast_exit` | They show conditional parent admission and one armed failure, respectively; the latter is not universal infeasibility. |

[F69](../../16-open-findings.md) remains separate: its maturity rule concerns
chain height, with OPR-38 naming “`h + 99`”. Waiting has no finite real-time
recovery promise, nor does maturity promise that other bounds pass.

The [decision register](milestone-3-decision-register.md#recorded-authority) records the
later direct owner answers on `bps-xmq1.9`, comment 364. For F1, “follow rec” on
2026-11-24 authorizes supported-state documentation plus bounded-selection design,
strengthening comment 360. OPR-33 is reopened for design only; skipped coins still count
and DUR-22 is unchanged by that authorization. No algorithm, topology, proof carrier,
amendment or implementation is chosen.

For F2, the owner's exact answer of 2026-11-24 is “We should review this limitation of
unconfirmed coins. Call a panel to design support for it”. The one-spend-in-flight limit
is not accepted. The register owns the split design-panel record; neither design was
chosen. The owner's “yes” of 2026-11-25 authorizes retained-floor design first and parks
the prior unconfirmed-value discovery choice. ADR-0020 decision 1 is reopened for design
only, with the constraint that two Escapes must not drain the vault between them; the
conditional panel result must return to the owner before anything changes. F1 and F2
next work therefore cannot be treated as wholly independent.

`bps-2egj` owns the confirmed sequential-Spend availability defect and its full history;
the register carries the compact example and scope. It is recorded on the bead pending
later authorized normative work, not added to `16-open-findings.md` here. The existing
positive and negative exhibits retain their stated premises; a selected-alone feasibility
exhibit does not prove sequential lifecycle success while an old Escape record counts.
Current rules remain unchanged and no retained-accounting repair is adopted. F48's owner
decision is recorded above, with the normative amendment pending.
