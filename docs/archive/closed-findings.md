**F15. CLOSED — the refresh bounds are sealed; the PIN attempt budget is node-local by
decision.** (`btc-policy-g8f`, P2; decided 2026-09-12.) `MAN-7` named three values the ceremony
never wrote, so every provisioned node ran on defaults and none was manifest-sealed. The finding
conflated two axes — *sealed* and *ceremony-written* — across three values that share only the
accident of being defaulted, and it closes as two decisions plus one obligation that applies to
all three. `ADR-0018` is the record: what was decided, and the four alternatives rejected to reach
it. Owners: `MAN-2` (schema revision 4), `MAN-3`, `MAN-7`, `MAN-9`, `MAN-27`, `SPN-43`;
`CNF-138`. Sealing the number was one of two decisions the `ADR-0006` bound needed; `ADR-0019`
was the other.

**F32. CLOSED — the extraction review exposed incompatible rules and ineffective checks.**
(Specification repository, review of `be7a784`, corrected 2026-09-09.) These corrections apply
here; the reference implementation was inspected as evidence but was not changed. The corrected
contracts and verification owners are indexed below. The conformance checklist identifies cases
that still require evidence from each implementation.

| Review issue | Current owner and verification |
|---|---|
| Admission accounting presented as a rolling completion-loss guarantee | `POL-20`; `ADR-0014`; `CNF-58`; `BtcPolicy.Budget` |
| Pending expiry predicate selected live entries | `SPN-42`; `API-21`; `CNF-35` |
| Maximum-size fee estimate treated as exact finalized size | `CHN-20`; `CNF-101` |
| Missing node-key derivation parameters | `MAN-17`; `CNF-102`; `tools/check_vectors.py` |
| Descriptor identity depended on a library renderer | `MAN-39`; `CNF-103`; `tools/check_vectors.py` |
| Arithmetic gate checked copied Python constants | now `tools/check_copies.py` against what the declarations emit; document mutations in `tools/check_gate_controls.py` |
| Malformed embedded PSBTs | `WIR-7`; `tools/check_fixtures.py`; fixture mutations in `tools/check_gate_controls.py` |
| Conformance demanded witness bytes change a witness-free commitment | `CHN-25`; `CNF-12`; `CNF-104`; `tools/check_vectors.py` |
| Replay prose promised to avoid preflight I/O | `SPN-21`; `SPN-23`; `CNF-29` |
| Imported ADR prescribed a competing descriptor and schema | `ADR-0013`; authority convention in `README.md` |

The spending-bound correction narrows the claim and preserves admission accounting. The replay
correction distinguishes backend I/O from evaluation of its result. Neither introduces a new
release-time ledger or an early replay shortcut. The current definitions, rather than the
review's proposed alternatives, are the owners listed above.

**F33. CLOSED — fresh-eyes review found conflicting implementer contracts.**
(Specification repository, corrected 2026-09-09.) This closes the specification corrections
listed below. It does not assert that the reference implementation has adopted them; each
implementation owes the conformance evidence at the listed owners.

| Review issue | Current owner and verification |
|---|---|
| Corrected PSBT poisoned by a cached refusal for the same commitment | `SPN-23`, `SPN-24`, `CHN-27`; `CNF-10`, `CNF-29` |
| Mempool-only settlement treated as authority to refund a reservation | `SPN-33`, `POL-18`, `POL-19`; `CNF-30`, `CNF-38` |
| Quota arithmetic underflow or no complete rung fitting a batch | `SPN-38`; `CNF-37`; `BtcPolicy.Cursor`, `tools/check_gate_controls.py` |
| User-signing groups excluded Refresh and fee-ladder rungs | `CHN-23`; `CNF-105` |
| Signer input rules made the node's required prevout record optional | `CHN-22`; `CNF-105` |
| Peer-signing prohibition also excluded authenticated request relays | `NCH-3`, `SPN-2` |
| Signature profile left high-S rejection versus normalization unspecified | `WIR-6`, `CHN-13`, `SPN-7`; `CNF-106` |
| Pre-PIN refusal summary contradicted nonce-consumption order | `SPN-4`, `SPN-5`; `CNF-26` |
| Channel reason table contradicted partial validation order | `NCH-18`, `NCH-24`; `CNF-60` |
| Generic body rules contradicted routing and channel responses | `API-3`, `WIR-1`, `WIR-9`; `CNF-70` |
| Envelope fixture described a different payload from its encoded bytes | `WIR-10` |
| Configuration, subordination and channel-poison references pointed to unrelated owners | `MAN-7`, `MAN-9`, `SPN-31`, `NCH-19` |

**F44. CLOSED — whether the residual of an escape-class pair gets a fee ladder.**
(`btc-policy-sqn`; `OPR-41`.) Closed 2026-09-14 by `ADR-0022`: there is no residual. The
claw-back is one transaction with no ladder, fee-bumped by a replacement over the same coins
(`CHN-35`, `WTC-25`).

**F50. CLOSED — a three-reviewer fresh-eyes round found values that existed only as a library's
behaviour.** (Specification repository, corrected 2026-09-10. Reviewed by three independent
reviewers; Bitcoin Core `fc6923cec5b4` and `rust-miniscript` 12.3.7
were read as evidence and were not changed.) The theme is one an interoperability set is
uniquely exposed to: a rule whose inputs are named after a dependency's accessor, or left to
"as the backend reports it", reads as complete and is not. Each correction below is landed here;
each implementation still owes the conformance evidence at the listed owner.

| Review issue | Current owner and verification |
|---|---|
| Maximum finalized vsize named a library accessor and defined no bytes | `CHN-34`; `CNF-136`; `WIR-36`, `tools/check_vectors.py` |
| `release_floor` was used by `SPN-38` and defined nowhere | `SPN-38`, `DUR-27`; `CNF-37`; `BtcPolicy.Cursor` |
| Delivery-horizon staging: prose contradicted the ingress gate table | `SPN-9`, `SPN-17`, `DUR-34`; `CNF-26` |
| `/pending` claimed cross-node response byte identity nothing provides | `API-21`, `WIR-1`; `CNF-41` |
| Channel replies were published "verbatim" against a byte-comparing client | `NCH-17`, `WIR-11`; `CNF-60` |
| `policy_version` must be federation-uniform but was sealed by nothing | `MAN-2`, `MAN-3`; `CNF-76`, `CNF-137`; `WIR-27` |
| Envelope `nonce` preimage cell disagreed with its own vector | `NCH-11`, `WIR-2`; `WIR-29`, `tools/vector_profiles.py` |
| "50th-percentile feerate" named three different functions of one block | `WTC-2`, `DUR-30`; `CNF-52` |
| `DUR-10` sweep selection was arrival-ordered and could split so that nothing fired | `DUR-10`, `ADR-0020` — every confirmed Escape is selected; `CNF-140` |
| `CHN-29` omitted the per-input sighash byte `WIR-23` hashes | `CHN-29`; `WIR-30` |
| `WIR-12`'s manifest fixture carried a bad checksum, two off-curve keys, two malformed keys, and non-canonical node order | `WIR-12`; `tools/check_fixtures.py` |
| `WIR-13`/`WIR-14` carried an extended key that decodes to 63 bytes | `WIR-13`, `WIR-14` |
| The fixture gate never parsed a descriptor string | `tools/check_fixtures.py` |
| The coverage gate credited no cited range interior, hiding real gaps in noise | `tools/check_coverage.py` |

Sealing `policy_version` bumped the manifest schema revision to `3` (`MAN-3`), which changes the
envelope's and the endorsement's `protocol_version` and every published manifest, endorsement and
envelope digest. That is a hard incompatibility with anything sealed at revision `2`, taken
deliberately: no vault exists in testing or production, so the cost is zero now and would be a
migration later. A revision-2 manifest MUST fail a revision-3 node's version check rather than
load (`CNF-76`).

**F51. CLOSED — the follow-up round caught a regression `F50` itself introduced, and two
interop splits nobody had looked for.** (Specification repository, corrected 2026-09-11. Same
three reviewers, re-run against the landed result.) The lesson worth keeping is that `F50`'s
largest defect was created by `F50`: a clean-looking one-paragraph edit to `SPN-38` defined the
release interval's start as `F` while leaving its cap anchored on `release_floor`, so a candidate
whose lowest admissible rung sat above the cursor released nothing on every pass, forever. The
published boundary table could not see it — every row had `a = 0`, where `F` collapses to
`release_floor` — which is why the table now carries a column giving the cap the withdrawn cursor anchor
would produce, rendered from `BtcPolicy.Render.spn38Table`, and why the control is not a row's
shape but the one-token flip of `BtcPolicy.Cursor.current` that `ADR-0023` decision 6 requires
red — `a > 0` is necessary for the anchors to differ and not sufficient.

| Review issue | Current owner and verification |
|---|---|
| `SPN-38`'s cap anchored on the cursor livelocked an admissible-above-cursor candidate | `SPN-38`; `CNF-37`; `BtcPolicy.Cursor`, `BtcPolicy.Exhibits`, the anchor-flip control in `.github/workflows/gates.yml` |
| `SPN-47`'s `vsize` had three readings spanning 82–203 vB on one transaction | `SPN-47` → `CHN-34`; `CNF-32` |
| The refresh refusal codes were assigned to no `SPN-19` propagation class | `SPN-43` |
| `CHN-34` mirrored the deprecated accessor's expression in its normative formula | `CHN-34`; `CNF-136` |
| `CHN-34` claimed low-S `S` never needs a sign-padding byte | `CHN-34` |
| The `⌊fee / vsize⌋` bias was published backwards | `WTC-2` |
| `DUR-30` claimed a median split converges on "the lower of two latches" | `DUR-30` → `DUR-28`; `CNF-52` |
| `DUR-30`/`CNF-52` claimed no fee reading means the base rung, contradicting `DUR-26` | `DUR-30`; `CNF-52` |
| `MAN-2`/`CNF-137` overclaimed "retriable forever" and "no quorum ever" | `MAN-2`; `CNF-137` |
| `MAN-2` called the Carrier identity the request digest; `NCH-31` stretches it under a per-boot salt | `MAN-2` |
| `MAN-5` called every non-convenience manifest field hash-bound, including endorsements | `MAN-5` |
| `CNF-137`'s negative test was unreachable once the seal landed | `CNF-137` |
| `CHN-29` cited `NCH-30` for a payload member `NCH-23` owns | `CHN-29` |
| `WIR-1` voided member order everywhere, contradicting `API-10` | `WIR-1` |
| The witness gate hardcoded `CHN-34`'s outer framing term and measured only 2-of-3 | `tools/vector_profiles.py`; two controls |
| The descriptor gate never Base58Check'd an extended key | `tools/check_fixtures.py`; one control |

Two reviewer claims were themselves rejected. `OVR-9` was said to overclaim by contradicting
`DUR-10`; it does not — `OVR-9` is scoped "from the same chain state" and `DUR-10`'s
non-convergence is arrival-ordered, which is not chain state. The two are cross-referenced rather
than amended. And `OVR-9` was offered as the reason to seal `refresh_max_feerate`; it proves too
much, because `SPN-9` states "The horizon is per-node, not sealed (`MAN-7`)" and `hold_secs`,
`max_commitment_age_secs` and `delivery_horizon_secs` all yield divergent verdicts by design, with
`SPN-19` existing to handle exactly that. The live argument for sealing the refresh bounds is
`ADR-0006`: they are the security bounds standing in for the Hold and the PIN on a pin-less,
hold-less class, and `POL-17` seals `hot_window_secs` even though `POL-16`'s ledger is per node.
That decision is `F15`, closed the next day by `ADR-0018`.

Two of `F50`'s claims did NOT survive verification and are recorded so they are not
re-filed: `CHN-16`'s arithmetic was alleged to be wrong, and is not — it is exact, and
`rust-miniscript`'s current `max_weight_to_satisfy()` returns precisely the value it wants
(`W_N − 1`); only the DEPRECATED `max_satisfaction_weight()` whose name `CHN-16` used returns
something else (`W_N + 4`), and the reference implementation calls the current one. And a median
disagreement was alleged to stop the sweep firing at all; `DUR-27`'s "prefix from the lowest
admissible rung through the latch" permits convergence on the lower latch under `SPN-38`'s
"common ladder with compatible user-signature hashes" premise and sufficient successful passes
and delivery. The cost in that case is a sweep at a cheaper rung than the chain is asking for. `DUR-30`'s own motivating sentence had
carried the same error and is corrected.
**F52. CLOSED — the refresh interval is read from the chain, not from a node's own log.** (Specification repository, found 2026-09-12 by the review round that
closed `F15`; decided the same day, `ADR-0019`.) `SPN-46` had latched on a refresh **this node
accepted**, from a log that was per node. Two consequences followed, neither fixable by sealing,
because sealing makes nodes share a number and both of these were nodes holding different
histories. `SPN-46` now reads a coin's age from the chain — `MTP(tip) − MTP(confirming)` — and a
node keeps no refresh log at all, which closes both. The trace is kept so the defect is not re-filed against it.

*Burn.* With one compromised node — `c = 1 < t`, admitted by `SEC-2`'s A5 — a chain of refreshes
could alternate which honest node co-signed, and no honest node ever saw two consecutive links. On
2-of-3, seeding the divergence with a single subordinated node (`SPN-45`) and then alternating:

| day | refresh | accepted by | outcome |
|---|---|---|---|
| 1 | seed over `X` | B | no quorum, but B's log now holds `X` and A's does not |
| 3 | `X→Y` | A, M | quorum |
| 5 | `Y→Z` | B, M | quorum |
| 7 | `Z→W` | A, M | quorum |

Seven confirmed refreshes in fifteen days against a thirty-day interval, and it did not stop.
A refresh is pin-less (`SPN-43`), so the attacker needed the user key and the coordinator auth
key and no PIN. Under the chain rule the second link is refused on every honest node: `Y` is
younger than the interval on the chain they all read.

*Bumping.* Acceptance latched and nothing un-accepted, so for the rest of the interval a refresh
could not be replaced (same inputs) or CPFP'd (the log recorded outputs too), and the composer had
one attempt at a confirming feerate per coin per interval. Under the chain rule an unconfirmed
refresh leaves no trace, so its replacement is admissible everywhere. `CNF-139` exercises both.

Two other fixes were weighed and are recorded in `ADR-0019`: accepting the burn as a residual —
it was slow, loud (every link tripped `WTC-17` on the node it bypassed), capped and profitless —
and refusing any coin descending from a transaction this node had not itself approved, which
would have made one transient backend failure a permanent refusal on a host `STO-1` forbids
restarting.

**F53. CLOSED — the refresh fee cap changed from relative to absolute with no record.**
(Specification repository, found and closed 2026-09-12.) `ADR-0012`'s refresh section specifies
"a **tight refresh-specific fee cap** (a real self-spend pays a normal feerate — **a small
multiple of the node's fee estimate** — never the 10%)", while `SPN-47` encodes an absolute
sealed `sat/vB`, and nothing said which won. `SPN-47` now states the supersession and its reason:
a multiple of a per-node backend estimate diverges between honest nodes by construction. The ADR
is left as the historical record it is; the README's authority convention already makes the
requirement win.

**F54. CLOSED — the review of `ADR-0019` and `ADR-0020` found three P1 defects in them.**
(Specification repository, found and corrected 2026-09-12 by the same three reviewers.) Same
lesson as `F51`, one level up: the two ADRs that moved the design furthest were written in one
pass and each carried a defect the next reader found in minutes. The author had said this was
where he would least trust himself unreviewed; that was correct, and the review was the cheapest
thing in the round.

| Defect | Owner and verification |
|---|---|
| The refresh bump path admitted and then could not fire: `WTC-24` read the resident's inputs as spent, and refresh had no BIP125 signalling | `WTC-24`, `WTC-25`, `CHN-18`, `SPN-44`; `CNF-139` |
| `WTC-2` had no row yielding median-time-past, and `SPN-43` read the interval under the lock | `WTC-2`, `SPN-43` |
| A refresh could fan one coin into thousands, each refreshable next interval, so the per-coin bound bounded nothing | `CHN-30`; `CNF-139` |
| A normal-PIN pair's Escape was fireable once any other Carrier armed, because `sweep_active` is one flag for the node | `DUR-10`, `DUR-5`; `CNF-140` |
| Cross-clearing cited `SPN-33`, which names hot candidates only | `DUR-31`; `CNF-140` |
| Selected windows were not re-installed when `T` shrank | `DUR-20` |
| The overlap argument held only for the default coverage; `MAN-9` admitted values at which two Escapes could both confirm | `MAN-9`; `CNF-86` |
| Seven sentences left describing the state before `ADR-0019` | `MAN-2`, `DUR-5`, `DUR-21`, `F15`, `ADR-0018`, `CNF-138` |

The fix commit was itself reviewed by the same pair, and carried five more, two of them new:

| Defect in the fix | Owner and verification |
|---|---|
| Ingress still read refresh age off the mempool-inclusive prevout flag, so a replacement was refused one step before the repaired fire pass | `SPN-43`, `SPN-46`; `CNF-139` |
| `DUR-22` restored only the Escape under evaluation, so the denominator shrank per resident Escape and two disjoint Escapes both confirmed at every coverage — the `MAN-9` floor had fixed a proof whose premise the spec never held | `DUR-22`, `MAN-9`; `CNF-140` |
| The output-count rule closed fan-out on refreshes only; dust deposited from outside could pad a refresh to standardness size and burn ten million satoshis per vault coin per interval | `SPN-44`, `CHN-30`; `CNF-139` |
| Re-installing windows on a `T` shrink was work only an armed node did | `DUR-20` |
| The per-entry duress bit had no merge rule, and nothing said it is read unconditionally | `DUR-10`, `SPN-38`, `DUR-29` |
| `SPN-43` cited `API-16` for delivery to every node; `API-16` stops at the first acceptance | `SPN-43` |

**F55. CLOSED — whether the duress claw-back residual is meant to fire at all.**
(Specification repository, found 2026-09-13 by the review of the merge; closed 2026-09-14 by
`ADR-0022`.) The residual admitted by `DUR-22` only once its sibling confirmed, inside a
sixty-second window from `T`, almost never fired, and the rest of the vault exited through
Recovery. The answer was not to widen the window but to remove the residual: the claw-back is
now one pin-less transaction (`CHN-35`, `SPN-50`) and a SpendRequest is always a hot spend plus
its Escape. The trace is kept in `ADR-0022` so the defect is not re-filed.

**F56. CLOSED — the review of the merge found the operator program written against the design
the review rounds had withdrawn.** (Specification repository, found and corrected 2026-09-13 by
two independent reviewers, run against the merged tree.) The merge (`388f0be`) stitched
an extension pass written before `ADR-0018`–`ADR-0020` to the rounds that produced them, and
resolved its four collisions by intent without a reviewer. Eighteen files auto-merged
textually; no gate reads a sentence. The theme this time: a document describing the OLD owner's
rule in its own words survives the merge intact and wrong.

| Defect | Owner and verification |
|---|---|
| `CHN-1`'s template hardcoded `older(4224679)` "with keys substituted and nothing else varied" beside a per-vault `CHN-4` | `CHN-1`, `CHN-6`; `tools/vector_profiles.py` measures a non-default lock |
| `CHN-4` called the timelock "sealed in the manifest as `recovery_timelock` (`MAN-2`)"; it is `MAN-5`'s convenience field, hash-bound through `wallet_id`, and a node has no such key to compare | `CHN-4`, `CHN-8`, `OPR-78`; `CNF-114` |
| `OPR-15` called `policy_version` "the one manifest field outside the preimage" and retained neither refresh bound | `OPR-15`; `CNF-117` |
| `WTC-28` had `OPR-33` extending the inventory to unconfirmed value against `OPR-39`'s confirmed-only composition, and `OPR-33` restated the denominator `DUR-22` owns, backwards | `WTC-28`, `OPR-33`; `CNF-93` |
| `OPR-56` derived deposit addresses "at a stated derivation index"; `CHN-3` makes every vault key definite, so the vault has one address | `OPR-56`, `OPR-59`; `CNF-124` |
| `OPR-51`'s only watch was output 1 of the primary; an `escape` leg and a one-in-one-out `refresh` have no output 1 | `OPR-51`, `OPR-68`; `CNF-122` |
| `OPR-65` then claimed the composer honoured the interval and watched to confirmation; the backend inventory then in `OPR-32` returned no confirming-block MTP, and the watch then in `OPR-51` demonstrated broadcast | `OPR-65`; `CNF-122` |
| `OPR-38` had both shapes finalizing at exactly the priced vsize, against `CHN-20`'s "a smaller size is valid: strict-DER ECDSA signatures vary in length" | `OPR-38`; `CNF-136` |
| `OPR-60` reconciled "sign events" `API-18` does not emit, and promised losslessness past the queue's capacity | `OPR-60`, `OPR-54`; `CNF-123` |
| `OPR-69` had the residual firing at `T` unconditionally; it fires only under duress and only if its sibling confirms in the window | `OPR-69`, `DUR-22`; `CNF-122`, `CNF-140`, `F55` |
| `DUR-22` left "departed value" undefined, two readings a fee apart | `DUR-22`; `CNF-140` |
| `ADR-0020`'s "only one can confirm" held only for self-delivered coverage; two residuals crediting one confirmed sibling can both confirm, harmlessly | `DUR-10`, `ADR-0020` |
| `MAN-35` defaulted every optional key, discarding sealed values `MAN-27` asks for | `MAN-35`; `CNF-115` |
| `CNF-80` admitted only a zero ceiling, where `MAN-13` admits a bounded non-zero one | `CNF-80` |
| `OPS-6` told the display to project maturity for coins confirmed now; `OPR-62` reads the unspent set | `OPS-6`; `CNF-125` |
| `CHN-2` justified `n ≤ 15` by witness standardness; 15 is the P2SH sigop bound, and P2WSH is nowhere near a limit | `CHN-2` |
| `SPN-33` read as retiring the disjoint residual with its settled sibling | `SPN-33` |
| `OPR-12`'s rationale, `OPR-77`, `OPS-27`'s duplicated MUST, `OPS-28`'s "plus `wallet_id`", `OPS-65`'s policy list, two wrong citations in `OPR-30` and `OPR-65`, `CNF-139`'s `F36`, `F51`'s "remains open", eight tool comments citing `F34` | each |
| The witness gate accepted an empty shape table and measured only the default lock | `tools/vector_profiles.py`; two controls |

Two reviewer claims were rejected. That the claw-back contract is "decorative": the immediate
leg is the claw-back and fires at its holder decision; only the residual is window-starved
(`F55`). The other disputed the then-current individual-coin composer on the basis of the
node's input cap. At that time the node's permission to batch did not mandate batching by
the composer; the review retained the individual-coin shape.

**2026-10-06 amendment:** that composer rationale no longer holds. The current owners are
`OPR-32` for the method inventory, `OPR-33` for accepted chain evidence and `OPR-65` for refresh
composition; verification is in `CNF-151`. The row and review disposition above record the
earlier correction, not the current contract.

**F57. CLOSED — the review of the claw-back pass found the one-shot burn argument false and the
retirement incomplete.** (Specification repository, found and corrected 2026-09-14 by two
independent reviewers, run against `feb3ca0`.) The lesson is `F54`'s again: the most
confident paragraph in the commit, `SPN-50`, and the decision under it, carried the defects.

| Defect | Owner and verification |
|---|---|
| `ADR-0022` decision 3 permitted vault change as "pointless"; with change, an attacker holding the user key and the credential burns ten percent per block, forever | `CHN-35`; `CNF-146` |
| `CHN-35` required confirmed inputs and `SPN-50` enforced nothing; two implementations would disagree on a claw-back over a resident refresh's output | `CHN-35`, `SPN-50`; `CNF-146` |
| `OVR-1` claimed theft requires the user key and `t` node keys, contradicting `SEC-54` rows 5, 6 and 10 | `OVR-1`; `CNF-146` |
| `NCH-21`'s padding budget named no Clawback | `NCH-21`; `CNF-66` |
| `SPN-5` gate 23 still admitted the retired escape-class spend | `SPN-5`; `CNF-25` |
| The coordinator-request vector parser rejected class byte `0x03` and the promised vector was absent | `WIR-31`, `tools/vector_profiles.py` |
| `API-24` excluded the wrong codes: `HOT_BUDGET_EXCEEDED` is reachable before classification, `BAD_PIN` is PIN-only not hot-only | `API-24`, `API-13`; `CNF-145` |
| `SPN-33`'s "terminal" was undefined once the registry sentence was deleted; a defeated hot spend could fire at Hold expiry after the claw-back was evicted | `SPN-33`, `SPN-38`; `CNF-146` |
| `DUR-22`'s claw-back sentence had the coins leaving at confirmation; the vault-unspent read includes the mempool, and a selected Escape's inputs stay restored | `DUR-22`; `CNF-140` |
| `DUR-36` had the Escape failing `DUR-21` on the strength of the claw-back being signed; only a resident or confirmed claw-back defeats it, at ancestry, never coverage | `DUR-36`; `CNF-55` |
| `clawback` run again over the same outpoints was refused locally by `OPR-34`'s inventory rule, so the bump path could not execute | `OPR-67`–`OPR-69`, `OPR-34`; `CNF-122` |
| A refresh could register during a claw-back's preflight and consume its input | `SPN-50` (in-flight marker); `CNF-146` |
| `DEF-5` had every settlement refunding reservations, against `SPN-33`'s mempool rule | `DEF-5` |
| `OPS-60` attributed to `OPS-33` a check `OPS-33` did not contain | `OPS-33`, `OPS-60` |
| `SEC-54` counted four outcome words and used five; its combination rule had no order and no cells for a loss that removes a row's own defence | `SEC-54` |
| `OPS-30`'s new triggers had no ordering and a false analogy; `DUR-10` quoted a sentence `SEC-21` no longer contains; `DUR-7`, `OPS-10`, `CNF-48`, `NCH-31`, `NCH-14`, `SPN-11`, `SPN-12`, `DOM-21`, `WTC-18`, `WIR-7`, the overview diagram, `CNF-42`, `OPR-7` and `OPR-65` still enumerated two request kinds or restated the old shape; the spend fixture's signature was one byte too long | each |

**F58. CLOSED — `CNF-47` asked for a theorem `DUR-14` does not hold.** (Specification
repository, found 2026-09-15 by `lean-01.md` §4E while stating the property formally; corrected
2026-09-16.) `DUR-14` sets `T ← max(min(T, its fire_at − epsilon_secs), now)`. When `now > T`
the new value is `now`, numerically above the old `T`: it means "act now", not "grant more
delay", and `DUR-7`'s deadline driver fires a `T` at or below `now` on its next tick either way.
`CNF-47` nevertheless said `T` "never grows", which is false on exactly that input, and a
conformance suite that asserted it literally would have gone red on a correct implementation or
been written to pass on a wrong one. The properties that hold are `T' ≤ max(T, now)` and
`now ≤ T ⇒ T' ≤ T`; `CNF-47` now states them. Wording, not a defect in the mechanism: no
implementation could have used the excursion, because a `T` in the past already fires now. The
first defect this set's formal layer found, before that layer existed (`ADR-0023`).

**F59. CLOSED — `DUR-22` claimed one denominator fixed across every pass; the load-bearing
property is a floor, and the single-sweep guarantee is per node.** (Specification repository,
found 2026-09-18 while stating `ADR-0023` milestone 7's denominator theorem; four independent
readers on one brief against
`c5fd52d`, each proving the floor in scratch Lean and each finding the traces below; corrected
2026-09-19.) `DUR-22` defined the protected value as live reads and, in the same clause, called
it "the vault as it stood when armed" and "one denominator across every selected Escape and
every pass". The reads move between passes, by the clause's own list; what `MAN-9`'s argument
needs is that every pass's denominator is at least the combined inputs of the selected Escapes,
so that two input-disjoint Escapes each covering more than half of it cannot both cover on
whichever passes they are measured.

| Defect | Owner and verification |
|---|---|
| "One denominator across every pass" was false; the property that carries `MAN-9` is the floor, and "as it stood when armed" was neither the reads nor a snapshot | `DUR-22`, `MAN-9`; the milestone 7 theorems over `BtcPolicy.Coverage`; `CNF-140` |
| "Restored" and "unconfirmed external deposits MUST be excluded" conflicted for a selected Escape's unconfirmed external input: excluded on the first pass, a first Escape covers and lands; counted on the second once it confirms, a second input-disjoint Escape covers too, and both confirm | `DUR-22` (counted regardless of the read; excluded unless a selected Escape spends them); `CNF-140` |
| The `confirmed + restored − excluded` shape of `BtcPolicy.Coverage`'s denominator can fall below the floor when a selected Escape spends another's change output; the denominator is a filter on the read with every distinct selected input outpoint added once, counted inputs taking precedence over exclusions | `DUR-22`; `BtcPolicy.Coverage` |
| "Only one can confirm" (`DUR-28`, `DUR-31`, `ADR-0020`, `CNF-140`) held federation-wide only if every honest node had measured both Escapes: on 2-of-3 with one compromised node and two honest nodes that selected different Escapes, two quorums form and both confirm, input-disjoint; the guarantee is per node over the Escapes it had selected at its first release | `DUR-22`, `DUR-28`, `DUR-31`, `ADR-0020`; `CNF-140` |
| An Escape selected after a node's first release, over a coin that entered the vault after the first was measured, can confirm beside it — structural, not wording: no ingress rule puts a coin in a denominator before the coin exists | `DUR-22`; accepted residual, below |
| A selected Escape naming an absent or inflated prevout (`SPN-25`: "A prevout the backend reports absent or unconfirmed is tolerated here") raises every later denominator and can fail every real Escape; it cannot confirm itself | `DUR-22`; accepted residual inside `SEC-21`'s "Censoring or selectively delivering requests can suppress the sweep or influence which selected Escape confirms, including by delivering a request whose selected Escape inflates the coverage denominator" |

What the residuals cost and what was rejected. Every Escape and every claw-back pays the escape
descriptor (`CHN-14`, `CHN-35`), so a double sweep is a second fee, capped per sweep by
`DUR-24` and in aggregate by the floor at `100 − escape_coverage_pct` percent of what is swept;
never principal. A snapshot of the vault at the arm commit was rejected: it is a chain read and
a write on the holder-decision path, which `DUR-3` forbids, and a frozen scalar without a frozen
coin universe still lets a later Escape cover with value from outside it. Refusing at ingress an
Escape whose input is neither confirmed nor vault-authorized was rejected: a deposit that
confirms before the second Escape is submitted passes it. Counting only inputs the backend
resolves was rejected: a coin unseen on the first pass and seen on the second is the double-sweep
trace. The closures that would end the late-selection residual are new contracts, none adopted:
a coin universe frozen at a node's first release, a designated coin every Escape must spend
(which one claw-back turns into total sweep denial), or one release per node per armed episode
(which restores the 2/2/1 denial `ADR-0020` removed). The bounds that would end the phantom
denial are likewise open: extending `SPN-25`'s equality to mempool-resident parents, or making an
Escape with an unresolved input at the episode's first release ineligible for the rest of it.

**F61. CLOSED — `POL-20`'s cohort was stated over one interval the federation does not have,
and `DOM-24` gave the HotClock a different origin from its two owners.** (Specification
repository, found 2026-09-20 while stating `ADR-0023` milestone 7's accounting bridge; three
independent readers on one brief against `79704d3`;
corrected the same day.) The counting theorem of milestone 3 is discharged by `POL-18`'s and
`POL-19`'s transitions, and stating that discharge exposed what the cohort was quantified over.

| Defect | Owner and verification |
|---|---|
| The cohort read as one global interval of length `hot_window_secs`, but each node ages its ledger against its own HotClock (`POL-22`) and this set bounds no two HotClocks' rates; with clocks of different rates every local admission passes while the global cohort exceeds the bound | `POL-20`; `BtcPolicy.Ledger.bridge` over `BtcPolicy.Ledgers`, and `BtcPolicy.Ledger.bridge_nonvacuous`, whose three nodes count one spend from three samples no single interval holds |
| The exclusion's quantifier was ambiguous: read per spend rather than per reservation, a spend keeps a counted acceptance whose reservation has been refunded, and the theorem's conclusion is then false, not merely unproved | `POL-20`; `CNF-58`; `BtcPolicy.Ledger.f61_per_spend_conclusion_false` |
| `DOM-24` defined the HotClock as "elapsed seconds since the process started" where `POL-22` and `NCH-41` both define it from the channel's construction | `DOM-24`, `POL-22`, `NCH-41` |

The cohort is now node-indexed: trailing intervals at one cut of the execution, one local
sample per node, no clock value compared to another. That is a cross-node statement and needs
no delivery model, so it is this milestone's and not a multi-node deferral. A corollary in
physical time — one wall interval mapping to at most `hot_window_secs` of elapsed HotClock at
every node — needs a rate premise nobody in this set discharges, and none is adopted; `SPN-10`
pins every accepting node's raw wall clock to `[E − max_commitment_age_secs, E)` around one
coordinator-signed expiry, which aligns acceptances but says nothing about how ledgers age
between them. Not a defect in the bound, which held under the per-node reading all along: a
defect in what the sentence said the bound was about.

**F65. CLOSED — a receipt named no sender, so a duplicate relay counted twice, and the package
test read world-level availability, so a node could assemble from partials it never received;
both corrected. The exposure key names no recipient, and that half is deliberate.**
(Specification repository, found 2026-09-21 by lifting the kernel invariant to `n` nodes; narrowed
the same day by a three-reader panel, none of whom accepted the first direction; the receipt half
corrected 2026-09-21; the assembly half settled by three further panels the same day, worked in
beads `bps-8s0.12` through `bps-8s0.16`, and corrected 2026-09-23.)

**The receipt half, corrected.** `DUR-5` requires the holder set to be this node "plus each
distinct peer whose authenticated relay of the same Carrier this node receives", and `DUR-6`
requires that "a sender already counted, an uncommitted duplicate, or a committed intent MUST be
an idempotent no-op". `BtcPolicy.Kernel.receipt` took a commitment id and no sender, and
`BtcPolicy.Kernel.commits` counted into a `Nat`. A number cannot express "already counted", so
neither clause was representable and one peer relaying twice reached `t`. That opened the gate
`DUR-8` describes — "a SpendRequest pair under EITHER PIN waits for the holder decision
of a Carrier naming it" — one relay early, under either PIN. A
modelled defect, not a wording gap.

The repair, chosen 2026-09-21 and unanimous across the panel: the receipt event carries the
authenticated `sender_node_id`, and the Carrier holds those relay senders in place of a count.
`ADR-0012` already specifies exactly this — a node "counts ITSELF … plus the distinct
`sender_node_id`s that relay it back, and arms once that holder set reaches t" — so this node
stays implicit and `BtcPolicy.Kernel.holderCount` adds it.
`BtcPolicy.Kernel.addSender` is the insertion, and it is what keeps the field a set of peers.
It makes `DUR-6`'s no-op the identity rather than a count that happens not to be read
(`BtcPolicy.Kernel.addSender_of_counted`), and it refuses this node's own id, because `DUR-5`
counts "each distinct peer" and this node is already the `+ 1`. That the field is a set is a
property of every reachable world and not of the writer alone:
`BtcPolicy.Kernel.relaySenders_nodup` carries it by induction, which is what makes
`holderCount`'s length a count of peers rather than of relays.
`BtcPolicy.Exhibits.ReleaseKernel.duplicate_relay_is_one_holder` runs one trace on which the
holder set refuses the duplicate and the withdrawn count does not: its quorum conjunct is what
goes red if the count comes back, and the count is computed beside it so the comparison is
visible. `BtcPolicy.Exhibits.ReleaseKernel.self_relay_is_not_a_second_holder` is the same
refusal for a relay carrying this node's own id. `ADR-0023` decision 9 and the exposure key are
not touched; the scope extension is recorded in `ADR-0023` decision 10. `CONTEXT.md` names the
type: *Node id*, whose `_Avoid_` list includes "peer id". The gain is fidelity plus `DUR-6`, not
a new safety result — `ADR-0012` records that
the count "is a timing/liveness mechanism, NOT the safety proof", the proof being the release
gate that `BtcPolicy.Kernel.no_hot_partial_while_armed` already carries. The repair met the bar
below on every line.

The exposure half is not a defect. `ADR-0023` decision 9 settles it by execution: exposure lives at
world level because "a commitment-keyed or node-local history loses the authority a partial
released under one commitment carries for a second over the same transaction, in both readers'
probes". `BtcPolicy.Exhibits.ReleaseKernel.exposure_key_exhibit` is that probe kept as a retained
trap, and `BtcPolicy.Exhibits.ReleaseKernel.no_resident_release_does_not_mean_safe` is the false
safety statement a node-local reading would let one prove. `CONTEXT.md` states the concept the same
way: exposed authority "outlives everything node-local". Keying an exposure by recipient would turn
one released partial into one row per peer and put that trap red.

**The assembly half, corrected.** `BtcPolicy.Kernel.packageAccepted` decided from world-level
availability. Its quorum conjunct was a predicate, `finalizable`, that counted the distinct signers
in the world's exposed authority against this node's `t`, so the model admitted a node assembling a
package from partials it never received, under a declaration tagged `DUR-28` that modelled none of
the possession `DUR-28` counts. Four panels of three readers settled the repair, in this order. The
first, the one that narrowed this finding, split 1–2 on assembly and deferred it: one reader would
split the predicate — a global one still reading the exposure, so the trap keeps its subject, and a
local one reading possession held on the candidate, so candidate pruning removes possession while
the world's exposure stays — and the other two would document the boundary and wait for delivery
semantics. The second chose to build the split now, unanimously: a global predicate over the world's
exposure, a node-local one over possession held on the candidate, and an authenticated
partial-receive event that `adversaryExposes` must never imply, because authority that has left its
signer has not thereby reached this node. Its readers found the local concept already owned by the
set — `SPN-36`'s candidate carries "the partials received per `(input, signer)`", and `NCH-24`'s
checks end "then store it" — and found no reason to wait for milestone 8, whose delivery reducer is
the operator's outbound delivery knowledge and supplies no inbound store: `OPR-49`'s state starts
"definitely not sent" and advances to "possibly delivered, exact bytes" on "EVERY attempt that is
not `NotSent`". The third settled how assembly is gated once possession is local: `packageAccepted`
gains this node's own `released` conjunct, justified only inside the kernel's no-quota abstraction,
rather than assembly folding into the fire pass, which would undo `ADR-0023` decision 10 item 4's
"`packageAccepted` and `send` are two events". The fourth settled the shape of possession: a bare
list of signers, since this kernel already collapses the input and rung dimensions, seeded with this
node's own signer at registration, with no separate own-signature bit and no reuse of `Exp`, whose
commitment id and class possession has no use for.

The work landed as one bead per green commit: possession (`bps-8s0.12`), the predicate split
(`bps-8s0.13`), the receive event (`bps-8s0.14`), the cutover with its bridge (`bps-8s0.15`), and
this record (`bps-8s0.16`), last because the rule lands before the record.

What landed. `BtcPolicy.Kernel.exposedQuorum` (`POL-18`) is the world predicate: the distinct
signers whose input-0 partial over the candidate's sighash is in the world's exposed authority. Its
tag is `POL-18` because "A partial that has left the node is finalizable authority in `t − 1`
compromised hands" is a statement about the world, not about this node. No transition reads it:
`BtcPolicy.Exhibits.ReleaseKernel.exposure_key_exhibit` and the other exposure exhibits are stated
over it, and it is the bridge's conclusion. `BtcPolicy.Kernel.heldQuorum` (`DUR-28`) counts
`Cand.heldSigners`, the candidate's *Held partial* set (`CONTEXT.md`), seeded at registration with
this node's own signer because `SPN-36` says a candidate is "born fully signed and fully withheld".
`BtcPolicy.Kernel.receivePartial` (`NCH-24`) is the store: it finds the candidate by id, compares
the recomputed sighash, reads the input, and inserts the signer idempotently
(`BtcPolicy.Exhibits.ReleaseKernel.duplicate_partial_preserves_held`); the validation `NCH-24` runs
before "then store it" is a named boundary hypothesis, not modelled. It is the only event that adds
a signer after registration, and the step that runs it appends the exposed-authority row whether or
not the store keeps the partial: a partial that arrived has left its signer either way.
`packageAccepted` (`SPN-39`) now reads `c.released && heldQuorum w.node.t c` where it read the
world, and `finalizable` is deleted.

The bridge is `BtcPolicy.Kernel.released_held_exposed` (`DUR-28`): on every `Reachable` world, a
resident candidate this node has released and whose held set reaches `t` has `t` distinct signers
in the world's exposed authority on its input-0 sighash. So the cutover narrows what a node may
assemble and never widens it. It is false for a hand-built `World`, which can hold a signer with
no exposure row. What rules that out on a reachable world: registration resets the held set to
this node's signer and `released` to false, the fire pass first sets `released` in the step that
appends this node's own row, and the receive stores only the input-0 partial on the candidate's
sighash that its unconditional exposure append records. It is one-directional: exposed authority
this node never received does not become possession. Four exhibits separate the predicates, each a
`decide` over one trace:

| Exhibit | What it proves |
|---|---|
| `BtcPolicy.Exhibits.ReleaseKernel.exposed_not_held_cannot_assemble` | This node has released and another signer's partial is in the world's exposed authority without having been delivered: `exposedQuorum` holds, the candidate is released, and `packageAccepted` leaves it unassembled. The converse of the bridge fails here |
| `BtcPolicy.Exhibits.ReleaseKernel.received_can_assemble` | The same release with that partial delivered through `receivePartial`: the held set is this node's signer and the peer's, the candidate is released, and the package is assembled |
| `BtcPolicy.Exhibits.ReleaseKernel.held_without_release_cannot_assemble` | The peer's partial is held and the candidate is due with held quorum, but no fire pass has run, so nothing is released and nothing is assembled: the `released` conjunct is live |
| `BtcPolicy.Exhibits.ReleaseKernel.receivePartial_admits_peer` | Before any fire pass, one received peer takes the held set from this node's signer alone to both signers and reaches held quorum, while `exposedQuorum` is false, nothing is released and the step emits nothing |

The `released` conjunct is a modelling order, not a rule read off the set, and the `packageAccepted`
docstring says so. `SPN-39` puts finalization on the fire pass — "On every fire pass, for each due
candidate, the node MUST: … otherwise finalize on a clone at the highest rung at or below the latch
that carries at least `t` distinct valid partials on every input" — but `SPN-38` permits a pass that
releases nothing: "If `affordable_rungs = 0`, release nothing and advance no release bookkeeping on
this pass." So `released` stands for "a pass processed this candidate" only where
`BtcPolicy.Kernel.firePass` releases every due candidate, which it does here because this kernel has
no quota. `Cand` carries no ladder and the kernel finalizes at `sighash c.tx 0`, so `released` is
`released_through` at rung 0. The conjunct gates assembly and leaves possession alone: this node's
own signature is held from registration, released or not, and only assembly waits for the pass. The
bridge needs it, and `BtcPolicy.Exhibits.ReleaseKernel.receivePartial_admits_peer` is why — own
withheld possession plus one received peer is held quorum with nothing of this node's exposed. The
third panel also recorded what replaces it: a candidate-wide boolean is the wrong durable predicate
once a pass can release nothing, or release one rung while finalizing another, so the fire pass
should leave an assembly token carrying the rung it selected, for `packageAccepted` to match.

The cutover forced one modelling decision. `receivePartial` stores a partial only at input 0,
because `exposedQuorum` counts only input-0 rows, and a partial on an unmodelled input is exposed
authority without modelled possession: stored, it would put a signer in the held set that the
world predicate never counts. It rests on two sentences. One is the kernel's boundary assumption,
not a requirement: "input 0 stands for every input", which `Cand.heldSigners`' docstring in
`Kernel.lean` states and `exposedQuorum`'s calls "the boundary assumption made visible". The other
is `NCH-24`'s "the input and signer are in range", read at the only input this kernel models. The
step's exposure append stays unconditional.
`BtcPolicy.Exhibits.ReleaseKernel.input7_receipt_is_exposed_not_held` is the trap: a peer's
partial on input 7 appends its row to the world's exposed authority, the held set stays this
node's signer alone and short of quorum, and after this node's fire pass the candidate is released
and still not assembled. Without the guard the held set reaches `t` on a row `exposedQuorum` never
counts, that exhibit goes red, and `BtcPolicy.Kernel.released_held_exposed` is false.

Two claims the panels refuted, recorded so they are not proposed again. Both were arguments for
deferring the split in the second panel's own brief, and two of its readers refuted both
independently. First, that the world-level predicate was a safe over-approximation of the local
one — local ⊆ global — so a model assembling from the world was the stronger test. False: the
two are incomparable. A node holds its own withheld signature before any fire pass, since
`SPN-36` says a candidate is "born fully signed and fully withheld", with nothing of it exposed,
so local possession can reach quorum where the world predicate cannot:
`BtcPolicy.Exhibits.ReleaseKernel.receivePartial_admits_peer` runs it on a trace. The other
direction is world-level quorum with no local possession.
`BtcPolicy.Exhibits.ReleaseKernel.exposure_key_exhibit` holds `exposedQuorum` on a candidate
this node never released, over a transaction whose earlier candidate is no longer resident, and
`BtcPolicy.Exhibits.ReleaseKernel.exposure_without_receivePartial_is_not_held` states the held
side outright: world quorum, the held set this node's signer alone, `heldQuorum` false. Second,
that the cutover weakens `BtcPolicy.Kernel.no_hot_partial_while_armed`. False:
`BtcPolicy.Kernel.no_hot_partial_while_armed` never read the finalizability predicate; it reads
the node's freeze bits, through the invariant that every hot candidate of an armed node is
frozen. Nor was `BtcPolicy.Exhibits.ReleaseKernel.bounded_from_ready` evidence for the quorum
conjunct, then or now: its step check tests nothing possession can affect, as the docstring
heading its section has said since the cutover.

Two claims in this finding's first draft were too strong and are withdrawn. `DUR-28`'s "several
selected Escapes may each gather `t` on different subsets of nodes" reads as subsets of *signers*,
which `Exp.signer` already represents, so it does not by itself require a recipient in the key. And
the probe's `finalizable_without_receiving` proved no reachable execution: its premise supplied the
global count, and the model it was stated over, whose `finalizable` has since been deleted, had no
delivery history at all.

No single-node theorem was affected by either half. `BtcPolicy.Kernel.inv_reachable` and
`BtcPolicy.Kernel.no_hot_partial_while_armed` read the node, not the exposure, and prove as they
did. The bar, which both halves met, item by item: decision 9's "never pruned by candidate eviction,
settlement or node death" is preserved — the exposure is still one world-level list that no event
shrinks — and `BtcPolicy.Exhibits.ReleaseKernel.exposure_key_exhibit` still proves; `DUR-28`'s
per-Escape quorum is kept distinct from `F63`'s per-commitment identity — `heldQuorum` counts on one
candidate, which for an Escape is the commitment `DUR-28` names ("quorum on an Escape's own
commitment id IS cross-node agreement on that Escape"), with its qualification "That agreement
covers the base transaction, not the ladder"; the exposure keeps its sighash key and
the Hot ledger's unit, `F63`'s subject, was neither read nor changed; no per-node branch breaks
`DUR-1`, which requires every observable to be "identical between a normal-PIN and a duress-PIN
request" — `receivePartial` branches on the candidate id, the message and the input, never on
`armed`, a duress bit or the selected set, and the conjuncts `packageAccepted` gained read
`released` and the held set, both of which the SILENCE projection keeps; the SILENCE two-run
relation is preserved with the sender coupled rather than erased — a relay and a partial receive are
each one `Input.pinless` event common to both runs, so `BtcPolicy.Silence.silence` proves as it did;
and `BtcPolicy.Kernel.inv_step`'s `adversaryExposes` case still discharges, beside a
`receivePartial` case of its own.

Named boundaries, not open questions. The finding closes with two dimensions deferred and named.
Possession is per signer only: the held set carries neither input nor rung, so `DUR-28`'s
"`≥ t` distinct valid partials on every input" is represented by the input-0 abstraction, and
per-input and per-rung possession arrive with those dimensions. And the fire-pass assembly token
carrying the selected rung replaces the `released` proxy when the ladder and the quota enter the
kernel. `ADR-0023` decision 10 records the decision as its 2026-09-23 scope extension.

**F66. OPEN — a compromised node release can leave normal-PIN history on the coordinator.**
(Specification repository, four-reader design review of the refusal fault list, 2026-10-05;
`bps-syg`.) `OVR-13` says "A node sees the submitted PIN in plaintext" and scopes the
guarantee to an adversary who "holds the coordinator and the physical scene but no node".
`DUR-1` states the same boundary: "Silence is claimed against an adversary holding the
coordinator and the physical scene but no node". `SEC-10` names a "coordinator that turns
hostile at the wrench" and warns that "a compromised node sees the PIN in plaintext".
`DOM-2` supplies the premise: "holding the coordinator auth key but no history of the normal
PIN". The open question is what establishes that absence of history when node-supplied values
survive on the coordinator.

The hand-off need not involve a coordinated adversary. A backdoored node release could observe
a normal PIN during earlier legitimate use and encode it into values the operator program
retains. A later coercer could seize the coordinator and recover the PIN history using an
encoding recoverable from the release, without owning a node, controlling the coordinator
before coercion, or communicating or coordinating with the party that introduced the backdoor.
The compromised release and the later coercer are distinct: the latter acquires the physical
scene and coordinator at coercion, but the retained data could already contain the normal PIN.

The persistent channels predate the fault-list addition. `OPR-60` requires "Alert consumption
MUST poll `/events` on EVERY node" and "persisting each node's consumed events and returned
cursor atomically". This retains both the returned per-node `/events` cursor and the consumed
events. For the cursor, `API-18` says "The queue assigns sequence numbers from 1" and
"`cursor = the highest sequence number the queue has ever assigned`". The cursor's numeric
bound comes from `WIR-1`: "every JSON number MUST be an integer within ±(2⁵³ − 1) with no exponent or
fraction". For the events, `API-18`'s fixture contains the transaction-id field "spend_txid",
the outpoint field "outpoint" and the script field "script". A malicious release could supply
chosen values in these returned fields to carry PIN-derived data. That is an inference about
a malicious release, not permission for an honest node to depart from the event or sequence
semantics.

`OPS-47` requires "A release MUST be reproducible" and "signed with a key whose holder and
verification path are stated". These build and signing properties reduce the backdoor risk;
they do not establish that the source being reproduced and signed contains no backdoor.
`ADR-0012`, Accepted residuals, already records that a compromised node "can hand the harvested
normal pin to a hostile-at-wrench coordinator". Here the hand-off could occur through retained
data without any required coordination between the backdoor author and the later coercer.
This is an open specification concern, not a claim that a release has been compromised or an
implementation exploit demonstrated.

Two directions, neither adopted: explicitly place the guarantee under the premise that no
node runs a compromised release, with prospective owners `OVR-13`, `SEC-10` and `DOM-2`; or
constrain what the operator program persists from node-chosen values, with prospective owners
`OPR-60` and `API-18`. The choice and any design of those constraints belong to the specification
owner. This finding amends no requirement and remains open independently of the work item's
closure; neither direction is a settled remedy.

