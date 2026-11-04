# 12 — Security requirements

Normative. The threat model, the load-bearing invariants, and the residual risks, each stated
as a requirement or as an explicitly accepted residual. This document cites the rule that
implements each property rather than restating it; where a sentence here and one in the owning
document disagree, the owning document is right and the disagreement is a defect to record.

## What is protected

**SEC-1** The protected asset is the coins, and the protected property is: **a spend happens only
when the user genuinely wants it, and a spend the user does not want can be stopped before it
settles — including when the user is being physically coerced.** No theorem carries "a spend happens only
when the user genuinely wants it" or "a spend the user does not want can be stopped before it
settles — including when the user is being physically coerced". Secondary assets are the node
signing keys, the two PIN digests, the coordinator auth key, the escape and recovery keys, and
the node preimages.

## Adversaries

**SEC-2** The design MUST hold against each adversary below to the stated extent, and an
implementation MUST NOT claim more:

| # | adversary | holds | the design's answer |
|---|---|---|---|
| A1 | remote attacker or malware on the coordinator, pre-wrench | the relay, network position | a trust failure, not an adversary the design defeats: it can read the normal PIN and nullify duress (`SEC-42`); node validation still bounds what it can authorize (Partial formal support for the decoded validation verdict: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. `POL-4` says "BIP32 derivation, script construction and cryptography remain an external boundary." For admission accounting, including accepted-reservation retention/counting, `BtcPolicy.Ledger.liveSum_le_cap`, `BtcPolicy.Ledger.countsAt_of_sysRun`, `BtcPolicy.Ledger.cohortCount_le_charging` and `BtcPolicy.Ledger.bridge` have the premises and scope owned by `POL-20`. `POL-20` says "The Hot budget provides an **acceptance-time admission bound**, not a rolling completion-loss bound." For the composed-run cap invariant, `POL-20` says "for every finite `tr` of composed steps from `sys`, under `liveSum sys.led ≤ cfg.cap`, it concludes `liveSum (sysRun g cfg r sys tr).1.led ≤ cfg.cap`". For accepted-reservation counting, `POL-20` says "it concludes `countsAt cfg.window sp.id { led := (sysRun g cfg r sys (pre ++ [last])).1.led, now := last.1.mono } = true`", "This is one node's count, not the federation's `hcohort`: which nodes are honest and that at least `q` of them meet these premises remain the caller's claim" and "No theorem carries the rest of" the clause "at the cut each honest ledger still charges its counted reservations". For the cut-count comparison, `POL-20` says "`cohortCount window cuts id ≤ Ledgers.charging (cuts.map fun k => holds k.led) id`, at that cut" and "No theorem carries the rest of" the clause "every counted spend charges at least `t − c` honest ledgers". For the bridge, `POL-20` says "The accounting theorem is `BtcPolicy.Ledger.bridge`, at one cut", "its conclusion is `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`" and "Identifying `cfg.cap` with `cap`, `cfg.window` with `hot_window_secs`, `q` with `t − c`, and `cuts` with exactly one entry for each honest node, of length `n − c`, remain the caller's premises about the federation." `POL-20` says "each node ages its ledger against its own HotClock", "so one interval of physical time across the federation is not an object this bound has", "MUST NOT be presented as a bound on funds completing or lost in an arbitrary rolling window" and "No replacement rolling completion-loss formula is specified." Partial row-retention support: `BtcPolicy.Ledger.retained_outside_prune_and_admission`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e` and `row`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `he : e ≠ .prune`, `hadm : admitted sys.world (sysStep g cfg r env sys e).1.world e = false` and `hrow : row ∈ sys.led`, gives a row after that composed step with the same `cid`, `amount`, `reservedAt` and `expiry`; it does not assert equality of the exposure bit. Partial refund support: `BtcPolicy.Ledger.prune_refunds_only_collected`, for arbitrary `g`, `cfg`, `r`, `env`, `sys` and `row`, under `hr : g.release = .acceptedAdmission`, `hf : g.refund = .onCollection`, `hrow : row ∈ sys.led` and `hgone : holds (sysStep g cfg r env sys .prune).1.led row.cid = false`, proves `row.exposed = false`, `Wall.atOrBefore env.wall row.expiry = false` and absence of that id from the candidates after that prune step. This is conditional on removal of the charge, not a theorem that a refund occurs. For released-charge due support, `POL-19` says "So that expiry is strictly below the ratchet" and "is never due again while its expiry is unchanged". `BtcPolicy.Ledger.released_never_due`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e`, `row`, later finite composed trace `tr`, candidate `c` and sample `env'`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `hcl : r.closeTime = .ratchet`, `he : e ≠ .prune`, `hrow : row ∈ sys.led`, `hgone : holds (sysStep g cfg r env sys e).1.led row.cid = false`, `hhot : c.hot = true`, `hwc : c.windowClose = none` and `hexp : c.expiry = row.expiry`, proves `due r env' (sysRun g cfg r (sysStep g cfg r env sys e).1 tr).1.world.node c = false`. These row-retention, conditional-refund and later-due endpoints neither revoke exposed signatures nor establish actual payment or a rolling completion-loss bound. For the exposed-authority limit, `POL-20` says "Already exposed signatures also remain valid after their reservations age out", "`BtcPolicy.Kernel.exposure_monotone` proves only `∀ x ∈ w.exposure, x ∈ (step r env w e).1.exposure`, across one kernel step, for every `r`, `env`, `w` and `e`" and "For signature validity, the remainder starts at one state and continues through a kernel or composed step to either kind of run."; no theorem carries the rest), and it holds no federation key |
| A2 | thief with the user key | the key, no PIN, subject to `SEC-10`'s "digest premise" | cannot produce a valid request (`SPN-18`; no theorem carries this); the allowlist and Hot budget bound anything that does pass (Partial formal support for the decoded validation verdict: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. `POL-4` says "BIP32 derivation, script construction and cryptography remain an external boundary." For admission accounting, including accepted-reservation retention/counting, `BtcPolicy.Ledger.liveSum_le_cap`, `BtcPolicy.Ledger.countsAt_of_sysRun`, `BtcPolicy.Ledger.cohortCount_le_charging` and `BtcPolicy.Ledger.bridge` have the premises and scope owned by `POL-20`. `POL-20` says "The Hot budget provides an **acceptance-time admission bound**, not a rolling completion-loss bound." For the composed-run cap invariant, `POL-20` says "for every finite `tr` of composed steps from `sys`, under `liveSum sys.led ≤ cfg.cap`, it concludes `liveSum (sysRun g cfg r sys tr).1.led ≤ cfg.cap`". For accepted-reservation counting, `POL-20` says "it concludes `countsAt cfg.window sp.id { led := (sysRun g cfg r sys (pre ++ [last])).1.led, now := last.1.mono } = true`", "This is one node's count, not the federation's `hcohort`: which nodes are honest and that at least `q` of them meet these premises remain the caller's claim" and "No theorem carries the rest of" the clause "at the cut each honest ledger still charges its counted reservations". For the cut-count comparison, `POL-20` says "`cohortCount window cuts id ≤ Ledgers.charging (cuts.map fun k => holds k.led) id`, at that cut" and "No theorem carries the rest of" the clause "every counted spend charges at least `t − c` honest ledgers". For the bridge, `POL-20` says "The accounting theorem is `BtcPolicy.Ledger.bridge`, at one cut", "its conclusion is `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`" and "Identifying `cfg.cap` with `cap`, `cfg.window` with `hot_window_secs`, `q` with `t − c`, and `cuts` with exactly one entry for each honest node, of length `n − c`, remain the caller's premises about the federation." `POL-20` says "each node ages its ledger against its own HotClock", "so one interval of physical time across the federation is not an object this bound has", "MUST NOT be presented as a bound on funds completing or lost in an arbitrary rolling window" and "No replacement rolling completion-loss formula is specified." Partial row-retention support: `BtcPolicy.Ledger.retained_outside_prune_and_admission`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e` and `row`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `he : e ≠ .prune`, `hadm : admitted sys.world (sysStep g cfg r env sys e).1.world e = false` and `hrow : row ∈ sys.led`, gives a row after that composed step with the same `cid`, `amount`, `reservedAt` and `expiry`; it does not assert equality of the exposure bit. Partial refund support: `BtcPolicy.Ledger.prune_refunds_only_collected`, for arbitrary `g`, `cfg`, `r`, `env`, `sys` and `row`, under `hr : g.release = .acceptedAdmission`, `hf : g.refund = .onCollection`, `hrow : row ∈ sys.led` and `hgone : holds (sysStep g cfg r env sys .prune).1.led row.cid = false`, proves `row.exposed = false`, `Wall.atOrBefore env.wall row.expiry = false` and absence of that id from the candidates after that prune step. This is conditional on removal of the charge, not a theorem that a refund occurs. For released-charge due support, `POL-19` says "So that expiry is strictly below the ratchet" and "is never due again while its expiry is unchanged". `BtcPolicy.Ledger.released_never_due`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e`, `row`, later finite composed trace `tr`, candidate `c` and sample `env'`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `hcl : r.closeTime = .ratchet`, `he : e ≠ .prune`, `hrow : row ∈ sys.led`, `hgone : holds (sysStep g cfg r env sys e).1.led row.cid = false`, `hhot : c.hot = true`, `hwc : c.windowClose = none` and `hexp : c.expiry = row.expiry`, proves `due r env' (sysRun g cfg r (sysStep g cfg r env sys e).1 tr).1.world.node c = false`. These row-retention, conditional-refund and later-due endpoints neither revoke exposed signatures nor establish actual payment or a rolling completion-loss bound. For the exposed-authority limit, `POL-20` says "Already exposed signatures also remain valid after their reservations age out", "`BtcPolicy.Kernel.exposure_monotone` proves only `∀ x ∈ w.exposure, x ∈ (step r env w e).1.exposure`, across one kernel step, for every `r`, `env`, `w` and `e`" and "For signature validity, the remainder starts at one state and continues through a kernel or composed step to either kind of run."; no theorem carries the rest) |
| A3 | thief with the user key and the normal PIN | both | bounded, not prevented: allowlist, per-transaction cap, velocity window (`POL-16`–`POL-20`) (Partial formal support for the decoded validation verdict: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. `POL-4` says "BIP32 derivation, script construction and cryptography remain an external boundary." For admission accounting, including accepted-reservation retention/counting, `BtcPolicy.Ledger.liveSum_le_cap`, `BtcPolicy.Ledger.countsAt_of_sysRun`, `BtcPolicy.Ledger.cohortCount_le_charging` and `BtcPolicy.Ledger.bridge` have the premises and scope owned by `POL-20`. `POL-20` says "The Hot budget provides an **acceptance-time admission bound**, not a rolling completion-loss bound." For the composed-run cap invariant, `POL-20` says "for every finite `tr` of composed steps from `sys`, under `liveSum sys.led ≤ cfg.cap`, it concludes `liveSum (sysRun g cfg r sys tr).1.led ≤ cfg.cap`". For accepted-reservation counting, `POL-20` says "it concludes `countsAt cfg.window sp.id { led := (sysRun g cfg r sys (pre ++ [last])).1.led, now := last.1.mono } = true`", "This is one node's count, not the federation's `hcohort`: which nodes are honest and that at least `q` of them meet these premises remain the caller's claim" and "No theorem carries the rest of" the clause "at the cut each honest ledger still charges its counted reservations". For the cut-count comparison, `POL-20` says "`cohortCount window cuts id ≤ Ledgers.charging (cuts.map fun k => holds k.led) id`, at that cut" and "No theorem carries the rest of" the clause "every counted spend charges at least `t − c` honest ledgers". For the bridge, `POL-20` says "The accounting theorem is `BtcPolicy.Ledger.bridge`, at one cut", "its conclusion is `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`" and "Identifying `cfg.cap` with `cap`, `cfg.window` with `hot_window_secs`, `q` with `t − c`, and `cuts` with exactly one entry for each honest node, of length `n − c`, remain the caller's premises about the federation." `POL-20` says "each node ages its ledger against its own HotClock", "so one interval of physical time across the federation is not an object this bound has", "MUST NOT be presented as a bound on funds completing or lost in an arbitrary rolling window" and "No replacement rolling completion-loss formula is specified." Partial row-retention support: `BtcPolicy.Ledger.retained_outside_prune_and_admission`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e` and `row`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `he : e ≠ .prune`, `hadm : admitted sys.world (sysStep g cfg r env sys e).1.world e = false` and `hrow : row ∈ sys.led`, gives a row after that composed step with the same `cid`, `amount`, `reservedAt` and `expiry`; it does not assert equality of the exposure bit. Partial refund support: `BtcPolicy.Ledger.prune_refunds_only_collected`, for arbitrary `g`, `cfg`, `r`, `env`, `sys` and `row`, under `hr : g.release = .acceptedAdmission`, `hf : g.refund = .onCollection`, `hrow : row ∈ sys.led` and `hgone : holds (sysStep g cfg r env sys .prune).1.led row.cid = false`, proves `row.exposed = false`, `Wall.atOrBefore env.wall row.expiry = false` and absence of that id from the candidates after that prune step. This is conditional on removal of the charge, not a theorem that a refund occurs. For released-charge due support, `POL-19` says "So that expiry is strictly below the ratchet" and "is never due again while its expiry is unchanged". `BtcPolicy.Ledger.released_never_due`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e`, `row`, later finite composed trace `tr`, candidate `c` and sample `env'`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `hcl : r.closeTime = .ratchet`, `he : e ≠ .prune`, `hrow : row ∈ sys.led`, `hgone : holds (sysStep g cfg r env sys e).1.led row.cid = false`, `hhot : c.hot = true`, `hwc : c.windowClose = none` and `hexp : c.expiry = row.expiry`, proves `due r env' (sysRun g cfg r (sysStep g cfg r env sys e).1 tr).1.world.node c = false`. These row-retention, conditional-refund and later-due endpoints neither revoke exposed signatures nor establish actual payment or a rolling completion-loss bound. For the exposed-authority limit, `POL-20` says "Already exposed signatures also remain valid after their reservations age out", "`BtcPolicy.Kernel.exposure_monotone` proves only `∀ x ∈ w.exposure, x ∈ (step r env w e).1.exposure`, across one kernel step, for every `r`, `env`, `w` and `e`" and "For signature validity, the remainder starts at one state and continues through a kernel or composed step to either kind of run."; no theorem carries the rest), and the Hold gives the user a window to claw back (`OPS-15`) (Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold`, for arbitrary `r`, `env`, `n` and `c`, under `h : r.holdCheck = .hotClock`, `hc : c.hot = true` and `hm : c.acceptedAt.aged env.mono n.holdSecs = false`, proves `due r env n c = false` at that sample. This is a local due test, not delivery or successful claw-back; For the response-bound claim, `SPN-34` says "subject to the reservation premise below"; this points to `SPN-34`'s "reservation premise", and `SPN-34` says "No theorem carries this response-bound claim across re-registration with a surviving ledger reservation." This premise citation claims no proof and `OPS-13` says "`hold_secs` has no positive lower bound". Partial conflict-defeat support: `BtcPolicy.Kernel.settle_marks_conflicts`, for arbitrary `env`, `n` and `tx`, under `hs : env.chain.seen.contains tx = true`, marks each resident hot candidate with a different transaction id and conflicting inputs terminal; `BtcPolicy.Kernel.terminal_never_due`, for arbitrary `r`, `env`, `n` and `c`, under `hr : r.defeat = .terminalFlag` and `h : c.terminal = true`, proves false due. This composition starts with a supplied chain observation; it does not establish timely claw-back arrival. Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. `BtcPolicy.Classification.required_pays_no_vault_coin` and the claw-back arm of `BtcPolicy.Classification.admitted_members_classed` at `.required`, for arbitrary `nSequence`, `nLockTime` and `outs`, under `h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, give escape classification and no vault outputs. This is conditional symbolic shape support, not destination authority or arrival; no theorem carries the rest) |
| A4 | coercion — the wrench, on a coordinator holding "no history of the normal PIN" (`DOM-2`), subject to `SEC-10`'s "release-history premise" and "digest premise", with no record of either PIN from any source (`DUR-1`) | the user, and everything they know | the duress PIN: a ceremony identical to the attacker, silently arming a sweep at `T` and locking the federation down (`05`); a wrench that begins mid-spend is `SEC-42`'s (`SEC-54` row 17) (Partial projected-silence support: `BtcPolicy.Silence.silence`, for one node, two enrolment tables and one shared input trace, assumes `Coupled` initial systems and `NodeInv` at each initial node's own ratchet, with marker `.committed`, traversal `.always`, dynamics `.dynamic`, registration `.preserve`, close time `.ratchet` and driver time `.ratchet`. It proves equality of the `Obs` pairs emitted by `obsPair`; that walk stops before either entering state fails `preHorizon` or `wfEvent` rejects the event. The horizon is unarmed or strictly before the entering state's current `T` at the driver sample; admitted acceptances have a non-hot Escape and no incoming window-close values. `BtcPolicy.Silence.silence_initial`, under those rule and marker premises, gives the same equality from one system taken twice with `armed = false`, empty candidates and Carriers, and `sweepActive = false`. These are projections, not serialized bytes or timing. `BtcPolicy.Silence.pending_pub` and `BtcPolicy.Silence.pub_lockedDown` give equal initial pending listings and latches from coupling alone; `BtcPolicy.Silence.markerOf_pub` also needs the committed marker, and `BtcPolicy.Silence.respond_pub` needs coupling alone. Partial arming/sweep support: `BtcPolicy.Kernel.holderDecision` assigns `armed` and `sweepActive` by OR with `pairDuress` and writes `T = writtenDeadline`, by definition. `BtcPolicy.Kernel.holderDecision_writes_every_window`, for any rules, environment, node and Carrier, assumes a candidate in that decision's resulting list, `entryActs = true`, and membership in the selection computed by `selectIntent` with `pairDuress`; it proves its fire time equals the decision's `T` and its close equals that `T` plus `combineSlack`. `BtcPolicy.Kernel.armed_sticky` preserves a true arm bit across one arbitrary kernel step. `BtcPolicy.Exhibits.TwoRun.horizon_is_where_the_runs_part` is a closed example: after its fixed `armTrace`, a supplied fire pass at 250 queues the duress world's Escape partial and none in the normal world, while the observation walk stops before that pass. `BtcPolicy.Exhibits.ReleaseKernel.armed_escape_can_broadcast` proves a reachable armed state and symbolic Escape broadcast for its fixed prefix, supplied peer partial, package acceptance and send. These examples do not establish payment or a federation-wide deadline driver. Partial hot-release exclusion: `BtcPolicy.Kernel.no_hot_partial_while_armed`, for a reachable armed world, proves a fire pass queues no hot partial; `BtcPolicy.Kernel.no_hot_broadcast_while_armed` additionally assumes `r.reauth = .beforeSend` and proves every effect of a send addresses a resident non-hot candidate. No theorem carries the rest of the ceremony, silence, arming/sweep or federation Lockdown claims.) |
| A5 | `c < t` compromised nodes | up to `t − 1` keys | cannot reach quorum; the Hot bound is stated for `c < t` (`POL-20`); silence is NOT claimed against them (`SEC-10`) (Partial quorum support: `BtcPolicy.Kernel.no_exposed_quorum_without_normal`, for any rules, signer histories, compromised-signer list, world and candidate, assumes `HonestExposureProvenance` for the candidate's input-0 sighash, `NoHonestNormalDecision` for that message across all commitments, and fewer than `w.node.t` distinct compromised signers. It proves `exposedQuorum w c = false`. The honest-exposure premise requires normal-release evidence in each relevant honest signer's execution history, including message binding; it is not derived for arbitrary incoming exposure rows. This is an input-0 exposed-authority count, not an unconditional federation or cryptographic threshold theorem. Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with the retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. No theorem carries the rest of the quorum or Hot-bound claims. The refusal to claim silence against compromised nodes is a scope boundary, not a theorem.) |
| A6 | `≥ t` compromised nodes plus the user key | a quorum and the key | **out of scope — this breaks the vault.** The threshold is the boundary (No theorem carries this threshold-compromise claim; it remains an accepted scope boundary.) |
| A7 | coordinator-auth-key thief | user key, PIN, and the auth key | can feed one node directly and let propagation arm the federation; bounded by allowlist, Hot budget and Hold; visible on every node's `/pending` (`API-21`) (Partial decoded-validation support: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. This is a decoded verdict; derivation and cryptography remain external boundaries. Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with the retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold`, for any rules, environment, node and candidate, assumes `r.holdCheck = .hotClock`, `c.hot = true` and `c.acceptedAt.aged env.mono n.holdSecs = false`; it proves `due r env n c = false` at that sample. This is a local due test, not a positive minimum Hold or successful claw-back. Partial pending-list support: `BtcPolicy.Kernel.prune_keeps_pending`, under `r.pendingSource = .record`, proves that pruning any node at one supplied environment preserves its `pending` list at that same environment. `BtcPolicy.Kernel.pending` under `.record` lists this node's pending-log ids whose expiry is at or after the call's effective time, by definition. Neither establishes receipt or visibility on every node. No theorem carries the rest of direct feeding, propagation/arming, Bounded or visibility on every node.) |
| A8 | chain-level adversary | miners, mempool, fee market | cannot steal; can delay: fee spikes, censorship and reorgs are met by the ladder, re-broadcast and reorg handling, and every failure degrades to frozen funds and Recovery (Partial symbolic shape support: `BtcPolicy.Classification.admitted_members_classed`, assuming `validateRequestShape rule r = true`, gives a hot primary, Escape-class Escape and Escape-class ladder members in the SpendRequest arm. Symbolic output classes do not prove cryptographic inability to steal. Partial ladder support: `BtcPolicy.Cursor.progress_on_F`, for any quota, input count and candidate, assumes `affordableRungs quota inputs ≠ 0`, `max c.floor c.a ≤ c.last` and `max c.floor c.a ≤ c.latch`; it proves that `pass .onF` releases a nonempty interval starting at `max c.floor c.a` and advances the floor to its upper end plus one. This is a supplied local release pass, not fee sufficiency, broadcast delivery or confirmation. Partial package support: `BtcPolicy.Package.admitted_only_when`, assuming `validate` returns `.admitted anc` for supplied ancestry rules, creator, snapshot, mempool read, authorized set, candidate and optional replacement, proves the required resident read and shown-or-resident inputs, exact ancestry, authorization of every ancestor and the ancestor limit. It does not prove mempool acceptance. Partial reorg support: `BtcPolicy.Watchtower.reconcile_rewinds`, for a supplied chain view and cursor with `c.anchors = a :: older`, assumes the newest anchor is inactive and some older anchor is active; it proves that `reconcile .anchored` drops the inactive prefix, retains the first active anchor and its suffix, and sets `next` to that anchor's height plus one. `BtcPolicy.Watchtower.reconcile_none_active`, assuming every stored anchor is inactive in that view, proves reconciliation returns `genesis`. These are cursor results under supplied observations, not eventual scans or transaction inclusion. No theorem carries the rest of inability to steal, delay handling, re-broadcast, or the claim that every failure degrades to frozen funds and Recovery.) |
| A9 | supply chain | a dependency or the build | bounded by a small dependency set and a written policy (`OPS-46`); weakly defended (`SEC-46`) (No theorem carries this supply-chain bound or its weak-defence assessment; the dependency and build-policy premises remain owned by `OPS-46` and `SEC-46`.) |

## The compromise-and-loss matrix

**SEC-54** `SEC-2` names adversaries by what they hold. This matrix names the outcome for every
combination of what the attacker holds and what the Operator still holds, so that a decision
about any path — a new pin-less class, a changed sweep rule — is made against the cells it
moves rather than against a story. The secrets are `DOM-10`'s: the **user key** `U`, the
**coordinator credential** `C`, a **node quorum** `N` (`t` node keys) or fewer `n<t`, **two
recovery keys** `R`, **escape-wallet signing authority** `E`, the **normal PIN** `P` and the
**duress PIN** `D`. `E` means spending authority under the supplied escape descriptor,
including access through usable backups; copies of one key count once. Losing the Operator's
`E` does not imply that nobody retains `E`. (No theorem carries the matrix's exhaustive combination claim, the escape-authority and key-loss threshold claims, or the host-knowledge claims. The descriptor, backup and custody premises remain owned by `DOM-10` and `OPS-60`; this annotation assigns no meaning to the excluded custody cases.)

The numeric threshold formulas apply only to a `k`-of-`m` escape wallet: `E` then means access
to at least `k` of its `m` distinct keys, and losing `E` means retaining fewer than `k` keys:
more than `m − k` keys and all their usable backups are lost. Fewer compromised keys do not
give the attacker `E`; losing at most `m − k` keys does not remove the Operator's `E`. These
are escape threshold variables, unrelated to the federation's `t` and `n`. Single-sig is the
accepted `k = m = 1` case. For other descriptor policies, the set makes no threshold-based
coercion, custody or loss claim. Authority follows the supplied descriptor, including any
non-key spending conditions; it is not inferred from a count of keys. This notation describes
the supplied wallet, not an additional escape spending policy. "Attacker" is anyone acting against
the Operator's wishes, the coercer included; the coordinator host pre-wrench (`SEC-42`, `SEC-43`) holds `C`, reads `P` when it is entered, and
holds `U` while the user key is software. The PIN digests have no letter: `OPS-35` requires every
copy off the node hosts to be destroyed before funding, and `OPS-30` requires new PINs for a
rotation's successor, `OPS-34` for a rollout stage's vaults and `OPS-73` for every pair of an
Operator's vaults (`SEC-10`). A coercer who holds a
copy anyway, or can test the PIN in another vault that enrolled it anyway, can test the PIN offered
before relaying it and withhold a duress request, and once it has the normal PIN it
nullifies duress as in row 8; silence is not claimed against it (`SEC-10`). A coercer who holds a
record of either PIN from any source can compare the PIN offered with it in the same way (`DUR-1`). Rows 1 and 4 assume `SEC-10`'s "digest premise", under which the thief holds no copy of either PIN digest. `SEC-10` says a holder of one "can test offline whether a PIN it holds is the one enrolled in that digest's role", so it can search the copy for that PIN; a thief who finds the normal PIN holds row 2's `U` `P`, and one who finds the duress PIN holds row 4's `U` `D`. (No theorem carries these digest-destruction, PIN-history, offline-testing or request-withholding claims. The digest and release-history premises remain owned by `SEC-10`, and the PIN-record premise by `DUR-1`; adopted scope is not a proof of those premises.)

Outcomes are exactly five words. **Nothing**: no valid request exists. **Bounded**: hot spends
inside the allowlist and Hot budget, clawed back inside the Hold. **Denial**: the coins reach the
escape wallet or Recovery, under the Operator's keys, later than wanted. **Theft**: coins reach
a wallet the attacker controls. **Loss**: coins reach a wallet nobody can spend. An Operator
loss row is the exit that remains. (Partial decoded-validation support: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. This is a decoded verdict; derivation and cryptography remain external boundaries. Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with the retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold`, for any rules, environment, node and candidate, assumes `r.holdCheck = .hotClock`, `c.hot = true` and `c.acceptedAt.aged env.mono n.holdSecs = false`; it proves `due r env n c = false` at that sample. This is a local due test, not a positive minimum Hold or successful claw-back. No theorem carries the rest of the five outcome definitions, including valid-request impossibility, successful claw-back, destination arrival, retained spending authority or eventual Recovery. The definitions classify outcomes; the admission and local due results do not establish those outcomes.)

Recovery exclusivity and permanent loss are assessed per coin from a payment freeze or each
node's Lockdown, treating the stated key losses as permanent. They apply only when no
already-signed payment, in-flight Escape or claw-back, user-signed refresh, or other permitted
Normal-path spend can still move that coin. Include later signing by an unlocked quorum with
the required credentials (`DUR-11`, `DUR-36`, `SPN-43`–`SPN-51`). Loss of `U` prevents fresh user
signatures, not completion of earlier user-signed transactions (`CHN-9`, `CHN-12`, `API-11`).
A possible spend, including Recovery, guarantees neither broadcast nor confirmation.

The combination rule: a cell's outcome is the worse of its attacker row and its loss row,
ordered Nothing < Denial < Bounded < Theft < Loss, except where a row below names the
combination, and undefined where the loss removes the attacker row's own defence — a lost `C`
removes row 2's request entirely (Nothing, then Recovery); loss of the Operator's `E` removes
Bounded's spendable claw-back destination (without preventing the claw-back request itself), so
no quantified funds-loss rate is specified here for a row-2 thief before Recovery matures (`POL-20`); a lost `U` removes
fresh user signatures for row 14's refresh, not completion of earlier user-signed refreshes;
subject to the per-coin condition above, each remaining coin matures into the attacker's reach. Loss at the escape destination
requires that nobody retains `E`: if the attacker retains `E`, a sweep is Theft
even when the Operator has lost `E`. The decisions and their amendments are recorded in
`ADR-0021`. (No theorem carries this ordering or these independent combination outcomes, including Recovery after credential loss and loss of a spendable claw-back destination. Row 2 retains its admission-only budget premises, and the loss rows retain their recovery and custody premises. No theorem carries the lost-`U`/row-14 fresh-signing, earlier-refresh completion or conditional maturation claim either; user-signature validity and key loss remain external cryptographic boundaries.)

| # | attacker holds | Operator still holds | outcome today | where it is enforced | status |
|---|---|---|---|---|---|
| 1 | `U`, no PIN, subject to `SEC-10`'s "digest premise" | everything | Nothing (no theorem carries this) | `SPN-18`: no PIN, no valid request (no theorem carries this) | settled (`A2`) |
| 2 | `U` `P` | `D` `E` `C` `N` `R` | Bounded (Partial formal support for the decoded validation verdict: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. `POL-4` says "BIP32 derivation, script construction and cryptography remain an external boundary." For admission accounting, including accepted-reservation retention/counting, `BtcPolicy.Ledger.liveSum_le_cap`, `BtcPolicy.Ledger.countsAt_of_sysRun`, `BtcPolicy.Ledger.cohortCount_le_charging` and `BtcPolicy.Ledger.bridge` have the premises and scope owned by `POL-20`. `POL-20` says "The Hot budget provides an **acceptance-time admission bound**, not a rolling completion-loss bound." For the composed-run cap invariant, `POL-20` says "for every finite `tr` of composed steps from `sys`, under `liveSum sys.led ≤ cfg.cap`, it concludes `liveSum (sysRun g cfg r sys tr).1.led ≤ cfg.cap`". For accepted-reservation counting, `POL-20` says "it concludes `countsAt cfg.window sp.id { led := (sysRun g cfg r sys (pre ++ [last])).1.led, now := last.1.mono } = true`", "This is one node's count, not the federation's `hcohort`: which nodes are honest and that at least `q` of them meet these premises remain the caller's claim" and "No theorem carries the rest of" the clause "at the cut each honest ledger still charges its counted reservations". For the cut-count comparison, `POL-20` says "`cohortCount window cuts id ≤ Ledgers.charging (cuts.map fun k => holds k.led) id`, at that cut" and "No theorem carries the rest of" the clause "every counted spend charges at least `t − c` honest ledgers". For the bridge, `POL-20` says "The accounting theorem is `BtcPolicy.Ledger.bridge`, at one cut", "its conclusion is `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`" and "Identifying `cfg.cap` with `cap`, `cfg.window` with `hot_window_secs`, `q` with `t − c`, and `cuts` with exactly one entry for each honest node, of length `n − c`, remain the caller's premises about the federation." `POL-20` says "each node ages its ledger against its own HotClock", "so one interval of physical time across the federation is not an object this bound has", "MUST NOT be presented as a bound on funds completing or lost in an arbitrary rolling window" and "No replacement rolling completion-loss formula is specified." Partial row-retention support: `BtcPolicy.Ledger.retained_outside_prune_and_admission`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e` and `row`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `he : e ≠ .prune`, `hadm : admitted sys.world (sysStep g cfg r env sys e).1.world e = false` and `hrow : row ∈ sys.led`, gives a row after that composed step with the same `cid`, `amount`, `reservedAt` and `expiry`; it does not assert equality of the exposure bit. Partial refund support: `BtcPolicy.Ledger.prune_refunds_only_collected`, for arbitrary `g`, `cfg`, `r`, `env`, `sys` and `row`, under `hr : g.release = .acceptedAdmission`, `hf : g.refund = .onCollection`, `hrow : row ∈ sys.led` and `hgone : holds (sysStep g cfg r env sys .prune).1.led row.cid = false`, proves `row.exposed = false`, `Wall.atOrBefore env.wall row.expiry = false` and absence of that id from the candidates after that prune step. This is conditional on removal of the charge, not a theorem that a refund occurs. For released-charge due support, `POL-19` says "So that expiry is strictly below the ratchet" and "is never due again while its expiry is unchanged". `BtcPolicy.Ledger.released_never_due`, for arbitrary `g`, `cfg`, `r`, `env`, `sys`, `e`, `row`, later finite composed trace `tr`, candidate `c` and sample `env'`, under `hs : g.settlement = .retainOnMempool`, `hr : g.release = .acceptedAdmission`, `hcl : r.closeTime = .ratchet`, `he : e ≠ .prune`, `hrow : row ∈ sys.led`, `hgone : holds (sysStep g cfg r env sys e).1.led row.cid = false`, `hhot : c.hot = true`, `hwc : c.windowClose = none` and `hexp : c.expiry = row.expiry`, proves `due r env' (sysRun g cfg r (sysStep g cfg r env sys e).1 tr).1.world.node c = false`. These row-retention, conditional-refund and later-due endpoints neither revoke exposed signatures nor establish actual payment or a rolling completion-loss bound. For the exposed-authority limit, `POL-20` says "Already exposed signatures also remain valid after their reservations age out", "`BtcPolicy.Kernel.exposure_monotone` proves only `∀ x ∈ w.exposure, x ∈ (step r env w e).1.exposure`, across one kernel step, for every `r`, `env`, `w` and `e`" and "For signature validity, the remainder starts at one state and continues through a kernel or composed step to either kind of run." Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold`, for arbitrary `r`, `env`, `n` and `c`, under `h : r.holdCheck = .hotClock`, `hc : c.hot = true` and `hm : c.acceptedAt.aged env.mono n.holdSecs = false`, proves `due r env n c = false` at that sample. This is a local due test, not delivery or successful claw-back; For the response-bound claim, `SPN-34` says "subject to the reservation premise below"; this points to `SPN-34`'s "reservation premise", and `SPN-34` says "No theorem carries this response-bound claim across re-registration with a surviving ledger reservation." This premise citation claims no proof and `OPS-13` says "`hold_secs` has no positive lower bound"; no theorem carries the rest); the Operator claws back without a PIN (`CHN-35`) (Partial conflict-defeat support: `BtcPolicy.Kernel.settle_marks_conflicts`, for arbitrary `env`, `n` and `tx`, under `hs : env.chain.seen.contains tx = true`, marks each resident hot candidate with a different transaction id and conflicting inputs terminal; `BtcPolicy.Kernel.terminal_never_due`, for arbitrary `r`, `env`, `n` and `c`, under `hr : r.defeat = .terminalFlag` and `h : c.terminal = true`, proves false due. This composition starts with a supplied chain observation; it does not establish timely claw-back arrival. Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. `BtcPolicy.Classification.required_pays_no_vault_coin` and the claw-back arm of `BtcPolicy.Classification.admitted_members_classed` at `.required`, for arbitrary `nSequence`, `nLockTime` and `outs`, under `h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, give escape classification and no vault outputs. This is conditional symbolic shape support, not destination authority or arrival; no theorem carries the rest) | `POL-16`–`POL-20`, `OPS-15`, `OPS-19` | settled (`A3`) |
| 3 | `U` `P` `C` | `D` `E` `N` `R` | Bounded; the request reaches nodes directly and is visible on every `/pending` (Partial decoded-validation support: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. This is a decoded verdict; derivation and cryptography remain external boundaries. Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with the retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold`, for any rules, environment, node and candidate, assumes `r.holdCheck = .hotClock`, `c.hot = true` and `c.acceptedAt.aged env.mono n.holdSecs = false`; it proves `due r env n c = false` at that sample. This is a local due test, not a positive minimum Hold or successful claw-back. Partial pending-list support: `BtcPolicy.Kernel.prune_keeps_pending`, under `r.pendingSource = .record`, proves that pruning any node at one supplied environment preserves its `pending` list at that same environment. `BtcPolicy.Kernel.pending` under `.record` lists this node's pending-log ids whose expiry is at or after the call's effective time, by definition. Neither establishes receipt or visibility on every node. No theorem carries the rest of Bounded, direct reach or visibility on every node.) | `API-21`, `OPS-19` | settled (`A7`) |
| 4 | `U` `D` | `E` `N` `R` | Denial: the sweep pays the escape wallet the Operator holds; a holder of `U` `P` `D` can send `P`, which is row 2 (Partial arming/sweep support: `BtcPolicy.Kernel.holderDecision` assigns `armed` and `sweepActive` by OR with `pairDuress` and writes `T = writtenDeadline`, by definition. `BtcPolicy.Kernel.holderDecision_writes_every_window`, for any rules, environment, node and Carrier, assumes a candidate in that decision's resulting list, `entryActs = true`, and membership in the selection computed by `selectIntent` with `pairDuress`; it proves its fire time equals the decision's `T` and its close equals that `T` plus `combineSlack`. `BtcPolicy.Kernel.armed_sticky` preserves a true arm bit across one arbitrary kernel step. `BtcPolicy.Exhibits.ReleaseKernel.armed_escape_can_broadcast` proves a reachable armed state and symbolic Escape broadcast for its fixed prefix, supplied peer partial, package acceptance and send. These examples do not establish payment or a federation-wide deadline driver. No theorem carries the rest of Denial, payment to a retained escape wallet or the holder's choice of the normal PIN; row 2 retains its own premises.) | `DUR-2`, `CHN-14` | settled |
| 5 | `U` + any PIN + `E` | `N` `R` | **Theft**: a claw-back or a duress sweep pays the attacker's escape wallet (Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. Partial shape support:  `BtcPolicy.Classification.required_pays_no_vault_coin` and the claw-back arm of `BtcPolicy.Classification.admitted_members_classed` at `.required`, for arbitrary `nSequence`, `nLockTime` and `outs`, under `h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, give escape classification and no vault outputs. This is conditional symbolic shape support, not destination authority or arrival. `BtcPolicy.Classification.admitted_members_classed`, for arbitrary `rule` and spend request under `validateRequestShape rule r = true`, also gives an Escape-class Escape and ladder members. Output classes do not establish spending authority. No theorem carries the rest of Theft or sweep/claw-back payment to the attacker; the custody premise remains owned by `OPS-60`.) | `OPS-60`, `ADR-0003` | settled: `E` custody is the whole defence |
| 6 | `U` `C` `E`, no PIN | `P` `D` `N` `R` | **Theft**: a claw-back needs no PIN (`SPN-50`) (Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. Partial shape support:  `BtcPolicy.Classification.required_pays_no_vault_coin` and the claw-back arm of `BtcPolicy.Classification.admitted_members_classed` at `.required`, for arbitrary `nSequence`, `nLockTime` and `outs`, under `h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, give escape classification and no vault outputs. This is conditional symbolic shape support, not destination authority or arrival. No theorem carries the rest of Theft or the assertion that no PIN defends against these holdings; escape authority and payment remain outside these results.) | `CHN-35`, `SPN-50` | decided 2026-09-14: accepted (`ADR-0021`, `ADR-0022`). This attacker has already defeated `OPS-60`'s custody rule for `E`, and no PIN defends against them, since the duress PIN pays the same wallet |
| 7 | `C` alone, or `C` + `n<t` | `U` `P` `D` `E` `R` | Nothing: no user signature (No theorem carries this no-user-signature request-impossibility claim; user-signature validation remains an external cryptographic boundary.) | `CHN-11`, `SPN-5` | settled |
| 8 | coordinator host pre-wrench (`C`, reads `P`, `U` while software) | `D` `E` `R` | Bounded theft: hot spends up to the budget, and duress is nullified by PIN substitution (Partial decoded-validation support: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` without further hypotheses, proves that `evaluate cfg p = none` is equivalent to consistency, ownership, allowlisted outputs, the per-transaction Hot-cap check and the fee-cap check. This is a decoded verdict; derivation and cryptography remain external boundaries. Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with the retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold`, for any rules, environment, node and candidate, assumes `r.holdCheck = .hotClock`, `c.hot = true` and `c.acceptedAt.aged env.mono n.holdSecs = false`; it proves `due r env n c = false` at that sample. This is a local due test, not a positive minimum Hold or successful claw-back. Partial symbolic completion support: the closed `BtcPolicy.Trace.published_replays_with_current`, over its fixed `w0` and `publishedInputs` under `Kernel.current`, proves replay with the hot candidate released and broadcast, its Escape neither released nor broadcast, and the node unarmed. Its supplied normal acceptance, holder receipt, fire pass at HotClock age 55 with Hold 50, peer partial, package acceptance and send do not model PIN substitution or guarantee transport or confirmation. No theorem carries the rest of conditional theft, PIN substitution or duress nullification.) | `SEC-42`, `SEC-43`, `ADR-0015` | settled, conditional theft |
| 9 | the wrench, on a coordinator holding "no history of the normal PIN" (`DOM-2`), subject to `SEC-10`'s "release-history premise" and "digest premise", with no record of either PIN from any source (`DUR-1`): the user, `U` `P` `D` `C` | `E` out of the coercer's reach, `N` `R` | Denial: duress sweeps to the escape wallet at `T`, Lockdown follows (Partial arming/sweep support: `BtcPolicy.Kernel.holderDecision` assigns `armed` and `sweepActive` by OR with `pairDuress` and writes `T = writtenDeadline`, by definition. `BtcPolicy.Kernel.holderDecision_writes_every_window`, for any rules, environment, node and Carrier, assumes a candidate in that decision's resulting list, `entryActs = true`, and membership in the selection computed by `selectIntent` with `pairDuress`; it proves its fire time equals the decision's `T` and its close equals that `T` plus `combineSlack`. `BtcPolicy.Kernel.armed_sticky` preserves a true arm bit across one arbitrary kernel step. `BtcPolicy.Exhibits.TwoRun.horizon_is_where_the_runs_part` is a closed example: after its fixed `armTrace`, a supplied fire pass at 250 queues the duress world's Escape partial and none in the normal world, while the observation walk stops before that pass. `BtcPolicy.Exhibits.ReleaseKernel.armed_escape_can_broadcast` proves a reachable armed state and symbolic Escape broadcast for its fixed prefix, supplied peer partial, package acceptance and send. These examples do not establish payment or a federation-wide deadline driver. Partial hot-release exclusion: `BtcPolicy.Kernel.no_hot_partial_while_armed`, for a reachable armed world, proves a fire pass queues no hot partial; `BtcPolicy.Kernel.no_hot_broadcast_while_armed` additionally assumes `r.reauth = .beforeSend` and proves every effect of a send addresses a resident non-hot candidate. No theorem carries the rest of Denial, the sweep-to-wallet-at-`T` claim or federation Lockdown.) | `05`, `SEC-8` | settled (`A4`) |
| 10 | the wrench reaching `E` too (for a `k`-of-`m` escape wallet, at least `k` distinct keys, including access through usable backups) | `N` `R` | **Theft**, at `T` or immediately by claw-back; against this coercer duress buys nothing and the set claims nothing (Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. Partial shape support:  `BtcPolicy.Classification.required_pays_no_vault_coin` and the claw-back arm of `BtcPolicy.Classification.admitted_members_classed` at `.required`, for arbitrary `nSequence`, `nLockTime` and `outs`, under `h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, give escape classification and no vault outputs. This is conditional symbolic shape support, not destination authority or arrival. `BtcPolicy.Exhibits.ReleaseKernel.armed_escape_can_broadcast` is a closed example under current rules: its fixed prefix, supplied peer partial and package acceptance reach an armed world whose send emits an Escape broadcast. Neither result establishes arrival at `T`, immediate payment or coercer authority. No theorem carries the rest of Theft or the claim that duress buys nothing; the custody premise remains owned by `OPS-60`.) | `OPS-60`, `ADR-0003` | amended 2026-10-06: `OPS-60` requires "a coercer holding the user cannot reach any such spending key set within the sweep's window"; the failure-domain check is `OPS-33`; physical custody remains unverifiable |
| 11 | `n<t` node keys, with or without `U` `P` | the rest | Nothing beyond row 2's Bounded; no quorum; silence not claimed against a node the attacker controls, which sees the PIN, or a holder of a PIN-digest copy (`SEC-10`); a copy of the keys that runs no node is inside `DUR-1`'s claim when the attacker also holds no record of either PIN from any source (Partial quorum support: `BtcPolicy.Kernel.no_exposed_quorum_without_normal`, for any rules, signer histories, compromised-signer list, world and candidate, assumes `HonestExposureProvenance` for the candidate's input-0 sighash, `NoHonestNormalDecision` for that message across all commitments, and fewer than `w.node.t` distinct compromised signers. It proves `exposedQuorum w c = false`. The honest-exposure premise requires normal-release evidence in each relevant honest signer's execution history, including message binding; it is not derived for arbitrary incoming exposure rows. This is an input-0 exposed-authority count, not an unconditional federation or cryptographic threshold theorem. Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with the retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. For row 2's remaining Bounded support, the decoded validation, Hold and conditional conflict-defeat/claw-back results retain exactly the premises and limits annotated in row 2; no extra defence follows from the copied keys. Partial projected-silence support: `BtcPolicy.Silence.silence`, for one node, two enrolment tables and one shared input trace, assumes `Coupled` initial systems and `NodeInv` at each initial node's own ratchet, with marker `.committed`, traversal `.always`, dynamics `.dynamic`, registration `.preserve`, close time `.ratchet` and driver time `.ratchet`. It proves equality of the `Obs` pairs emitted by `obsPair`; that walk stops before either entering state fails `preHorizon` or `wfEvent` rejects the event. The horizon is unarmed or strictly before the entering state's current `T` at the driver sample; admitted acceptances have a non-hot Escape and no incoming window-close values. `BtcPolicy.Silence.silence_initial`, under those rule and marker premises, gives the same equality from one system taken twice with `armed = false`, empty candidates and Carriers, and `sweepActive = false`. These are projections, not serialized bytes or timing. `BtcPolicy.Silence.pending_pub` and `BtcPolicy.Silence.pub_lockedDown` give equal initial pending listings and latches from coupling alone; `BtcPolicy.Silence.markerOf_pub` also needs the committed marker, and `BtcPolicy.Silence.respond_pub` needs coupling alone. This per-node two-run theorem takes peer relays as shared inputs; it does not prove that copying keys adds no knowledge. No theorem carries the rest of Bounded, the quorum claim or the copied-key silence claim; the controlled-node and digest-copy exclusions remain scope boundaries.) | `POL-20`, `SEC-10`, `DUR-1` | settled (`A5`); silence boundary for a copied key stated 2026-10-21 |
| 12 | `N` (a quorum) without `U` | `U` `P` `D` `E` `R` | Nothing: the Normal path needs the user signature (No theorem carries this no-user-signature Normal-path impossibility claim; user-signature validation remains an external cryptographic boundary.) | `CHN-1`, `CHN-11` | settled |
| 13 | `N` `U` | — | out of scope: the threshold is the boundary (No theorem carries this threshold-compromise claim; it remains the scope boundary matched with A6.) | `SEC-2` | settled (`A6`) |
| 14 | `R` (two recovery keys) | everything else | **Theft of every coin whose timelock has matured**; only refresh keeps a coin young, and Lockdown ends new refresh signing at locked nodes. Subject to the per-coin condition above, after Lockdown the recovery holders are the sole custody of every straggler the sweep left in the vault, until that coin's own timelock matures, counted from its confirmation (`CHN-4`), with only `OPS-3`'s alert against them (Partial in-flight support: `BtcPolicy.Kernel.lockdown_preserves_in_flight`, for arbitrary rules, environment, world and candidate id without further hypotheses, proves that changing only the Lockdown latch leaves the fire-pass release effects and resulting candidates, package-accepted candidates and send effects equal. `BtcPolicy.Kernel.exposure_monotone`, for arbitrary rules, environment, world and event, preserves membership of every earlier exposure entry across one step. These are local projections and history membership, not signature validity or successful payment. Partial alert support: `BtcPolicy.Alerts.recovery_never_swallowed`, for any snapshot and supplied spend, assumes `isRecovery s.witness = true` and proves a Recovery verdict. `BtcPolicy.Alerts.duty_ignores_lockdown`, for any other duty inputs, equates its result with the latch set and clear. These do not establish actual chain scans or alert delivery. No theorem carries the rest of this two-key theft, refresh/maturity, new-refresh-signing exclusion, conditional sole-custody or custody/alert-defence claim.) | `SEC-35`, `OPS-26`, `OPS-33` | decided 2026-09-14: settled as is. Refresh cadence, `OPS-33`'s failure-domain rule and the alert are the defence; no stronger custody rule, because the holders must stay reachable for `OPS-60`'s drill, and a custody plan is judged against the post-Lockdown sentence, not against "a backstop" |
| 15 | miners, mempool, fee market | everything | Denial: delay, then Recovery (Partial ladder support: `BtcPolicy.Cursor.progress_on_F`, for any quota, input count and candidate, assumes `affordableRungs quota inputs ≠ 0`, `max c.floor c.a ≤ c.last` and `max c.floor c.a ≤ c.latch`; it proves that `pass .onF` releases a nonempty interval starting at `max c.floor c.a` and advances the floor to its upper end plus one. This is a supplied local release pass, not fee sufficiency, broadcast delivery or confirmation. The quota, latch and admissibility floor are inputs, not guaranteed chain conditions. Partial package support: `BtcPolicy.Package.admitted_only_when`, assuming `validate` returns `.admitted anc` for supplied ancestry rules, creator, snapshot, mempool read, authorized set, candidate and optional replacement, proves the required resident read and shown-or-resident inputs, exact ancestry, authorization of every ancestor and the ancestor limit. It does not prove mempool acceptance. Partial reorg support: `BtcPolicy.Watchtower.reconcile_rewinds`, for a supplied chain view and cursor with `c.anchors = a :: older`, assumes the newest anchor is inactive and some older anchor is active; it proves that `reconcile .anchored` drops the inactive prefix, retains the first active anchor and its suffix, and sets `next` to that anchor's height plus one. `BtcPolicy.Watchtower.reconcile_none_active`, assuming every stored anchor is inactive in that view, proves reconciliation returns `genesis`. These are cursor results under supplied observations, not eventual scans or transaction inclusion. No theorem carries the rest of Denial, delay or eventual Recovery.) | `SEC-38`, `A8` | settled |
| L1 | — | lost `U` | Recovery after each coin matures (No theorem carries this Recovery-after-maturity claim; the Recovery premises remain owned by `OPS-26`.) | `OPS-26` | settled |
| L2 | — | lost `C` and its backup | Normal path bricked; Recovery (No theorem carries the Normal-path failure or eventual Recovery claim; the loss and Recovery premises remain owned by `SEC-36` and `OPS-20`.) | `SEC-36`, `OPS-20` | settled |
| L3 | — | lost the node quorum (more than `n − t` nodes dead) | Recovery (No theorem carries this Recovery claim after loss of the node quorum; the Recovery premises remain owned by `OPS-26`.) | `DUR-18`, `OPS-26` | settled |
| L4 | — | forgot `P` | cannot spend; claw back, then rotate with new PINs (Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. Partial shape support: `BtcPolicy.Classification.required_pays_no_vault_coin` and the claw-back arm of `BtcPolicy.Classification.admitted_members_classed` at `.required`, for arbitrary `nSequence`, `nLockTime` and `outs`, under `h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, give escape classification and no vault outputs. This is conditional symbolic shape support, not destination authority or arrival. Partial conflict-defeat support: `BtcPolicy.Kernel.settle_marks_conflicts`, for arbitrary `env`, `n` and `tx`, under `hs : env.chain.seen.contains tx = true`, marks each resident hot candidate with a different transaction id and conflicting inputs terminal; `BtcPolicy.Kernel.terminal_never_due`, for arbitrary `r`, `env`, `n` and `c`, under `hr : r.defeat = .terminalFlag` and `h : c.terminal = true`, proves false due. This composition starts with a supplied chain observation; it does not establish timely claw-back arrival. No theorem carries the rest of the forgotten-normal-PIN, claw-back or rotation claims, including the same-day remedy without the duress PIN or recovery holders. The rotation premises remain owned by `OPS-30`.) | `OPS-15`, `OPS-30` | decided 2026-09-14: the claw-back needs no PIN (`ADR-0022`), so the remedy is same-day and needs neither the duress PIN nor the recovery holders |
| L5 | — | forgot `D`, or both PINs | no duress path until rotated; claw back, then rotate with new PINs (Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. Partial shape support: `BtcPolicy.Classification.required_pays_no_vault_coin` and the claw-back arm of `BtcPolicy.Classification.admitted_members_classed` at `.required`, for arbitrary `nSequence`, `nLockTime` and `outs`, under `h : validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, give escape classification and no vault outputs. This is conditional symbolic shape support, not destination authority or arrival. Partial conflict-defeat support: `BtcPolicy.Kernel.settle_marks_conflicts`, for arbitrary `env`, `n` and `tx`, under `hs : env.chain.seen.contains tx = true`, marks each resident hot candidate with a different transaction id and conflicting inputs terminal; `BtcPolicy.Kernel.terminal_never_due`, for arbitrary `r`, `env`, `n` and `c`, under `hr : r.defeat = .terminalFlag` and `h : c.terminal = true`, proves false due. This composition starts with a supplied chain observation; it does not establish timely claw-back arrival. No theorem carries the rest of the lost-duress-path, claw-back or rotation claims, including the remedy shared with L4. The rotation premises remain owned by `OPS-30`.) | `OPS-15`, `OPS-30` | decided 2026-09-14: same remedy as L4, which was the strongest reason for the pin-less claw-back (`ADR-0022`) |
| L6 | — | lost `E`, nobody else retains `E`, and a sweep fires (for a `k`-of-`m` escape wallet, more than `m − k` keys and all their usable backups are lost) | **Loss**: the coins sit in a wallet nobody can spend, and no node can tell a live escape wallet from a dead one (No theorem carries the lost-escape-authority Loss claim or the claim that a node cannot distinguish a live escape wallet from a dead one. A supplied output classification is not a proof of spending authority, payment or future key retention; the custody and drill premises remain owned by `OPS-60` and `OPS-61`.) | `OPS-60`, `OPS-61` | decided 2026-09-14, scope amended 2026-10-06: the custody drill is the whole defence; the protocol adds nothing, since a proof of possession at seal time says nothing about a backup a year later |
| L7 | — | lost two of the three `R` | no Recovery; subject to the per-coin condition above, vault coins stranded after any freeze or Lockdown are permanently lost, while coins a sweep or claw-back reached under a retained `E` stay spendable (No theorem carries this no-Recovery, conditional permanent-loss or retained-escape-authority spendability claim. The per-coin condition above is a scope condition, not proof that other spends are absent; key loss, cryptographic spending authority and destination spendability remain external boundaries.) | `OPS-33`, `OPS-26`, `OPS-30` | decided 2026-09-14: the custody drill is the defence, and one lost recovery key is a rotation trigger (`OPS-30`) while the Normal path still works, as a dead node is (`OPS-5`) |
| L8 | — | lost the descriptor backup | Recovery cannot be composed; the coins are unspendable once the federation is gone (No theorem carries the Recovery-composition or eventual-unspendability claim after loss of the descriptor backup; the backup premise remains owned by `OPS-23`.) | `OPS-23` | settled: the backup is promiscuous by design |
| 16 | a later coercer holds coordinator history carrying an encoding left by a compromised node release, without earlier control of the coordinator or present control of a node | remaining keys and PINs | silence is not claimed for PINs entered while that release ran; at the wrench, holding the user, `U` `P` `D` `C`, with `E` out of the coercer's reach: at worst Bounded theft, as in row 8. Where that history gives the coercer the normal PIN, it substitutes it, so the Escape never arms and no node locks down, and the coerced hot spend completes after the Hold, up to the budget; where it gives only the duress PIN, the coercer can test the PIN offered before relaying it and withhold a duress request, and once it has the normal PIN it nullifies duress as in row 8. Other holdings follow the applicable attacker and loss rows (Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold` assumes `r.holdCheck = .hotClock`, `c.hot = true` and `c.acceptedAt.aged env.mono n.holdSecs = false`; it proves `due r env n c = false` at that sample, not eventual release or completion. Supplemental fixed-example support: the closed `BtcPolicy.Trace.published_replays_with_current`, over `w0` and `publishedInputs` under `Kernel.current`, proves replay with hot candidate 1 released and broadcast, Escape candidate 2 quorum-opened but neither released nor broadcast, empty Carriers, an unarmed final node and two signer exposures. Its one normal (`duress = false`) acceptance at HotClock 5, holder receipt, supplied fire pass at 60 with Hold 50, peer partial, package acceptance and send fix the execution. `BtcPolicy.Kernel.armed_sticky` preserves a true arm bit across any step; by induction over `Kernel.run`, the fixed replay's final false bit therefore also excludes arming at any prefix of that replay. These facts do not quantify over substituted-PIN or coerced histories. The theorem has no Lockdown conjunct; symbolic broadcast guarantees neither transport, arrival nor confirmation. No theorem carries the rest of the release-history, PIN-testing/substitution, duress-nullification, no-node-Lockdown or coerced-completion claims.) | `SEC-10` ("release-history premise"); `OPS-30` ("sweeps FIRST and builds the successor after"); `POL-20` | decided 2026-10-05: accepted boundary (`ADR-0021`); fund outcome decided 2026-10-21: conditional theft accepted, a case `SEC-42` does not count (`ADR-0021`) |
| 17 | the wrench beginning mid-spend, on a coordinator holding the normal PIN in RAM (`SEC-42`): the user, `U` `P` `D` `C` | `E` out of the coercer's reach, `N` `R` | Bounded theft, as in row 8: the coordinator substitutes the normal PIN it holds, so the Escape never arms and no node locks down, and the coerced hot spend completes after the Hold, up to the budget; silence is not claimed against it (`SEC-10`) (Partial Hot-accounting support: `BtcPolicy.Ledger.liveSum_le_cap`, for any guards, configuration, rules and finite composed trace, assumes the starting `liveSum ≤ cfg.cap` and preserves that inequality. `BtcPolicy.Ledger.bridge`, at supplied node cuts, assumes duplicate-free cohort ids, matching reservation amounts, each cut's `liveSum ≤ cfg.cap` and at least `q` counted cuts per cohort spend; it proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. Taking `q = t − c`, `cuts.length = n − c`, and those cuts as exactly the honest nodes is the caller's premise. This is admission accounting, with retention/counting premises owned by `POL-20`, not a rolling completion-loss bound. Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold` assumes `r.holdCheck = .hotClock`, `c.hot = true` and `c.acceptedAt.aged env.mono n.holdSecs = false`; it proves `due r env n c = false` at that sample, not eventual release or completion. Supplemental fixed-example support: the closed `BtcPolicy.Trace.published_replays_with_current`, over `w0` and `publishedInputs` under `Kernel.current`, proves replay with hot candidate 1 released and broadcast, Escape candidate 2 quorum-opened but neither released nor broadcast, empty Carriers, an unarmed final node and two signer exposures. Its one normal (`duress = false`) acceptance at HotClock 5, holder receipt, supplied fire pass at 60 with Hold 50, peer partial, package acceptance and send fix the execution. `BtcPolicy.Kernel.armed_sticky` preserves a true arm bit across any step; by induction over `Kernel.run`, the fixed replay's final false bit therefore also excludes arming at any prefix of that replay. These facts do not quantify over substituted-PIN or coerced histories. The theorem has no Lockdown conjunct; symbolic broadcast guarantees neither transport, arrival nor confirmation. No theorem carries the rest of the mid-spend normal-PIN substitution, duress-nullification, no-node-Lockdown or coerced-completion claims.) | `SEC-42`, `POL-20`, `SEC-10` | settled, conditional theft: `SEC-42` counts "a wrench that begins mid-spend while the normal PIN is in RAM" among the histories of a coordinator compromised before the wrench |

Row 6 is the cell the pin-less claw-back moved (`ADR-0022`), and the reason the decision was
made here: before it, every coin that left the vault for anywhere but the vault itself needed a
PIN, which row 6's attacker does not hold. Rows L4
and L5 are what the move bought. (Partial pin-less support: the closed `BtcPolicy.Policy.clawback_codes` proves absence of its unreachable codes, including BAD_PIN, from `reachable`, presence of HOT_BUDGET_EXCEEDED in `reachable` and equality of the two pure evaluators. Composed with `BtcPolicy.Policy.evaluate_in_reachable`, for arbitrary `r` and `c` under `h : evaluateSpend r = some c`, it excludes BAD_PIN from that pure verdict; this composition is not a new theorem. `BtcPolicy.CoordRequest.Request.clawback` has no PIN field, by definition; neither result proves admission of the complete request. The credential and node-availability premises remain owned by `OPS-15`. No theorem carries the rest of this historical comparison or the remedy attributed to L4 and L5, including same-day payment and rotation; their `OPS-15` and `OPS-30` premises remain in force.)

## Trust boundaries

**SEC-3** **User to coordinator.** The coordinator is trusted before the wrench and hostile from
it (`DOM-2`). Its signature proves only "this vault's coordinator authored this request", never
that the request is legitimate. No theorem carries "this vault's coordinator authored this request". It MUST NOT persist the PIN (`DOM-4`), MUST hold it in RAM only,
and MUST never log it anywhere; the day a request is logged "for debugging", PIN substitution
comes back. No theorem carries "PIN substitution
comes back".

**SEC-4** **Coordinator to node** is the hard boundary. Every node re-runs every gate in
`SPN-5`'s order and never signs because it was told to (`NCH-3`). Partial decoded-validation support: `BtcPolicy.Evaluate.acceptance_exact`, for arbitrary `cfg` and `p` with no further hypotheses, proves `evaluate cfg p = none` iff consistency, input ownership, allowlisted outputs, the per-transaction Hot cap and the fee cap all hold. `POL-4` says "BIP32 derivation, script construction and cryptography remain an external boundary." This is neither the full `SPN-5` sequence nor a node-signing theorem. No theorem carries the rest of "Every node re-runs every gate in
`SPN-5`'s order and never signs because it was told to".

**SEC-5** **Node to node.** A peer is transport. Authority is cryptographic, rooted in the sealed
manifest: envelope signatures by endorsed channel keys (`NCH-5`, `NCH-11`), partials verified
against recomputed sighashes (`NCH-24`).

**SEC-6** **Node to chain.** Each node runs its own backend and is its own watchtower; a node
that cannot read the chain fails closed (`WTC-1`). Partial watchtower-cursor support: `BtcPolicy.Watchtower.pass_errored`, for arbitrary `sh`, `tt`, `c` and `tip` with no further hypotheses, proves `pass sh tt c tip .errored = c`. This keeps the supplied cursor unchanged on a supplied error; it does not model backend calls or the signing gate. Partial sweep-read support: `BtcPolicy.VaultUnspent.retry_fails_closed`, with no hypotheses, proves `readWithRetry none none = none`: two supplied failed attempts yield no snapshot. This does not establish backend health detection or signing refusal. No theorem carries the rest of "a node
that cannot read the chain fails closed".

**SEC-7** **The ceremony** is trusted (`MAN-37`). "Trusted until the wrench" describes the
operating coordinator, not the setup tool.

## Load-bearing invariants

Each is enforced by code, not convention; each is what a reviewer should try hardest to break.

**SEC-8** **SILENCE** (`DUR-1`). Across every observable a node emits, a duress ceremony is
identical to a normal one. `BtcPolicy.Silence.silence` and
`BtcPolicy.Silence.silence_initial` carry the per-node projection equality in `DUR-1`'s formal
scope, which says "emit equal observer projections" and "The walk stops when either entering
state fails" `BtcPolicy.Silence.preHorizon`, or the request shape is rejected. Their marker,
rule, coupling and initial-state premises, and the narrower initial-projection results
`BtcPolicy.Silence.pending_pub`, `BtcPolicy.Silence.pub_lockedDown`,
`BtcPolicy.Silence.obsOf_eq`, `BtcPolicy.Silence.markerOf_pub` and
`BtcPolicy.Silence.respond_pub`, are scoped there; application is subject to `SEC-10`'s
"release-history premise" and "digest premise". No theorem carries the rest of "Across every observable a node emits, a duress ceremony is
identical to a normal one". Break it and the wrench attacker learns the duress PIN was used and
escalates. No theorem carries "Break it and the wrench attacker learns the duress PIN was used and
escalates". This is the invariant most easily lost to an innocuous new field or endpoint.

**SEC-9** **Signer/partial coupling and the release gate** (`DUR-8`). A partial is finalizable
authority the moment `t − 1` compromised peers hold it, so every fire-time check runs before
release and the gate is the sole egress.
`BtcPolicy.Kernel.hot_release_provenance` carries only the local hot input-0 release portion:
`DUR-8`'s formal scope says "is unarmed and has an earlier normal-PIN holder" decision,
under its execution, accepted-only opening and release-effect membership premises. That scope
also says "this proves neither BIP143 binding nor full per-input or per-rung finalizability".
`BtcPolicy.Exhibits.ReleaseKernel.exposure_key_exhibit` supplies a fixed symbolic example:
under `BtcPolicy.Kernel.current`, from `BtcPolicy.Exhibits.ReleaseKernel.w0` on
`BtcPolicy.Exhibits.ReleaseKernel.twoRequestsTrace`, with `t = 2` and Hold zero, node 0
releases under commitment 1, that candidate expires, and signer 2 exposes a partial for
commitment 5 over the same transaction. It proves `exposedQuorum wTwo c1' = true` at
input 0; it proves no Bitcoin signature verification, assembly or gate breach. No theorem
carries the rest of "A partial is finalizable
authority the moment `t − 1` compromised peers hold it"; no theorem carries the rest of
"every fire-time check runs before
release and the gate is the sole egress". Break it and a `t − 1` set combines a transaction the
honest node refused. No theorem carries this.

**SEC-10** The **scope of SILENCE** MUST be stated wherever it is claimed: silence against a
coordinator that turns hostile at the wrench, across every observable a node emits (`DUR-1`:
"Every observable a node emits MUST be identical between a normal-PIN and a duress-PIN
request"), including response bytes, timing class, `/events`, `/healthz`, `/pending` and peer
effects. This list gives examples; it is not exhaustive.
`BtcPolicy.Silence.silence` and `BtcPolicy.Silence.silence_initial` carry only `DUR-1`'s
per-node projection equality under the premises and initial-state boundaries of its formal
scope: "emit equal observer projections", with a walk that "stops when either entering state
fails" `BtcPolicy.Silence.preHorizon` or the request-shape check. The narrower initial-projection
results `BtcPolicy.Silence.pending_pub`, `BtcPolicy.Silence.pub_lockedDown`,
`BtcPolicy.Silence.obsOf_eq`, `BtcPolicy.Silence.markerOf_pub` and
`BtcPolicy.Silence.respond_pub` have the distinct premises and horizons that scope names.
`BtcPolicy.FedSilence.fed_silence` and the results beside it carry that projection equality over a
federation's composed run, with each peer message compared by its destination and shape, under the
premises and the horizon `DUR-1` names for them.
Application is subject to this requirement's "release-history premise" and "digest premise".
No theorem carries the rest of "silence against a
coordinator that turns hostile at the wrench, across every observable a node emits". The **release-history premise** of
this scope is that no node has
run a compromised release while the current PINs were in use. This covers their lifetime, not
just the moment of coercion: an earlier compromised release can leave an encoding of a PIN on
an otherwise honest coordinator for a later coercer to read. No theorem carries this. The party that compromised the
release and the later coercer need not communicate or be the same party. No theorem carries this. It is not a claim that no
adversary can learn the PIN class: a compromised node sees the PIN in plaintext, a coordinator
compromised before the wrench reads and substitutes it, a holder of a copy of either PIN digest can
test offline whether a PIN it holds is the one enrolled in that digest's role, and a holder of a
record of either PIN from any source can compare it with the PIN offered at the wrench (`DUR-1`).
Its **digest
premise** is that the adversary holds no copy of either PIN digest and that neither PIN is enrolled
in another vault, in either role. A digest of a PIN enrolled in another vault is such a copy,
whatever its salt, since `OPS-35` says "each digest checks a PIN against its enrolled role in one
Argon2 evaluation"; and whoever holds that vault's coordinator auth key, a coordinator serving both
vaults included, can test the PIN against that vault's running nodes without coins: a request
carrying a PIN not enrolled there is refused `BAD_PIN` (`SPN-18`) before any coin is fetched
(`SPN-5`), and a staged one carrying that vault's duress PIN, accepted or refused, arms it once its
holder set reaches `t` (`DUR-4`, `DUR-5`), so it locks down at `T` (`DUR-7`).
No theorem carries "A digest of a PIN enrolled in another vault is such a copy,
whatever its salt". No theorem carries "whoever holds that vault's coordinator auth key, a coordinator serving both
vaults included, can test the PIN against that vault's running nodes without coins".
`BtcPolicy.Kernel.receipt` supplies only the modeled holder-decision step: under the
`DUR-5` holder rule it calls `BtcPolicy.Kernel.holderDecision` on a Carrier found by id before its
`D` and `E`, when the admitted sender brings its holder count to at least `t`; `BtcPolicy.Kernel.holderDecision` writes the arm
with the pair duress bit. These definitions take authenticated sender identity and the
PIN-class bit as inputs, not a running-node PIN test. No theorem carries the rest of
"a request
carrying a PIN not enrolled there is refused `BAD_PIN` (`SPN-18`) before any coin is fetched
(`SPN-5`), and a staged one carrying that vault's duress PIN, accepted or refused, arms it once its
holder set reaches `t` (`DUR-4`, `DUR-5`), so it locks down at `T` (`DUR-7`)". `OPS-30` forbids such
enrolment for a rotation's successor, `OPS-34` for a rollout stage's vaults and `OPS-73` for every
pair of an Operator's vaults, and `OPS-35`
requires every copy off the node hosts to be destroyed before funding; these procedures do not
establish the premise, and no theorem does. Destruction cannot revoke a copy already taken, and the
claim does not reach a copy
that rule cannot destroy: one acquired from a node host through provider access (`SEC-28`), or one
kept or intercepted by whatever carried a configuration to a node host, which the set does not
specify (`F40` covers only the image). No theorem carries "Destruction cannot revoke a copy already taken". End-to-end timing has no hard gate (`SEC-47`). No theorem carries this.

**SEC-11** **Unconditional Lockdown at `T`** (`DUR-7`), as a decision and never as a latency
(`DUR-15`). No theorem carries this. Break it and duress becomes survivable for the attacker. No theorem carries this.

**SEC-12** **Determinism across the honest set** (`OVR-9`, `POL-1`, `DUR-30`).
The definitions `BtcPolicy.Evaluate.evaluate` and `BtcPolicy.Policy.evaluateSpend` give the
same model verdict for the same decoded `Psbt` and `Cfg`, including the supplied `derive`
function. `BtcPolicy.BumpTarget.anchor` and `BtcPolicy.BumpTarget.target` give the same anchor
and target for the same supplied tip and median. These are pure model functions, not a proof
that honest nodes supply equal derivations, medians, admissibility results or rung latches.
No theorem carries the rest of "Determinism across the honest set". Break it and
partials cover different transactions, no rung reaches `t`, and the Escape fails when needed.
No theorem carries "partials cover different transactions", "no rung reaches `t`", or
"the Escape fails when needed".

**SEC-13** **Escape-key independence**: `DOM-11` requires "Each escape key MUST be generated
independently on a device that holds no other vault role"; the check is `MAN-28`. A breach
that gives the coercer `E` turns the sweep and claw-back into theft; `SEC-54` defines it as
"spending authority under the supplied escape descriptor".
No theorem carries "A breach that gives the coercer `E` turns the sweep and claw-back into theft". Independence is required per key
even when that key alone does not give spending authority.

**SEC-14** **Policy purity** (`POL-1`).
`BtcPolicy.Evaluate.evaluate` is a pure function of the decoded `Psbt` and `Cfg`; the latter
supplies `derive`, `max`, `vault`, `escape`, `allow` and `hotMaxPerTx`. This definition models
purity with derivation supplied as a function; no theorem carries the rest of "Policy purity"
for an implementation. Break it and refusals stop being deterministic. No theorem carries this.

**SEC-15** **Fail closed** (`OVR-10`, `DUR-9`, `STO-10`). Every unknown, error or degraded state
refuses or locks down; funds route to Recovery rather than moving.
`BtcPolicy.Kernel.poisoned_releases_nothing`, with `r.poison = .asserted` and
`w.node.poisoned = true`, proves that one `.firePass` emits no effects and sets `lockedDown`.
`BtcPolicy.Evaluate.acceptance_exact` characterises acceptance for every decoded `Psbt` and
`Cfg`: consistency, input ownership, allowlisted outputs, the hot budget and the fee cap must
all hold. `BtcPolicy.Evaluate.faults_nonempty_refuses`, with `faults cfg p ≠ []`, gives a
refusal with the head fault's code. These are decoded-data predicates with `derive` supplied,
not runtime error handling. `BtcPolicy.VaultUnspent.retry_fails_closed` proves only
`readWithRetry none none = none`, for two refused snapshot reads. No theorem carries the rest
of "Every unknown, error or degraded state refuses or locks down". No theorem carries
"funds route to Recovery rather than moving".

## Surfaces

**SEC-16** `/sign` is the main gate and its order is `SPN-5`.
`BtcPolicy.Gates.rows` records the gate labels and nonce, propagation and staging columns;
`BtcPolicy.Gates.thirty_gates`, with no hypotheses, proves that the list has 33 rows and
that every gate number from 1 through 30 resolves. This is table data, not a handler execution.
No theorem carries the rest of "`/sign` is the main gate and its order is `SPN-5`". The nonce is consumed atomically
under the sign lock; the memory-hard work and the chain I/O are deliberately outside it, so
neither lengthens the section a waiting Lockdown contends for — but the acquisition delay itself
remains unbounded (`DUR-15`).
No theorem carries "The nonce is consumed atomically under the sign lock", or that the
memory-hard work and chain I/O outside it do not lengthen the contended section.
The kernel models atomic transitions, not locks or acquisition delay; no theorem carries
the rest of this sentence.

**SEC-17** `/channel` is manifest-pinned, endorsed, quota'd and size-bounded (`06`). The
diagnostic it publishes to `/events` MUST be pin-independent (`NCH-16`).
No theorem carries "`/channel` is manifest-pinned, endorsed, quota'd and size-bounded".

**SEC-18** `/events` carries on-chain watchtower alerts and one channel diagnostic, and nothing
about pending or armed state (`API-18`).
`BtcPolicy.Alerts.alertOf` and `BtcPolicy.Alerts.alertsOf` construct only watchtower alerts
from the supplied authorized snapshot and spends; their definitions take no pending or arm
state. They do not model the channel diagnostic or the whole `/events` response.
No theorem carries the rest of "`/events` carries on-chain watchtower alerts and one channel
diagnostic, and nothing about pending or armed state".

**SEC-19** `/healthz` is four atomic loads and MUST stay free of duress-dependent content
(`API-20`).
No theorem carries "`/healthz` is four atomic loads". The residual is co-residency latency, which reflects what else the host is doing
and is equally present on every surface and on the TCP accept. No theorem carries this.

**SEC-20** `/pending` lists sorted opaque ids only (`API-21`).
`BtcPolicy.Kernel.pending` returns only model `Nat` ids filtered at the supplied effective
time; it neither sorts nor encodes them. No theorem carries the rest of
"`/pending` lists sorted opaque ids only". Its bytes are asserted identical
across normal and duress and across armed-pre-`T` and idle twins.
`BtcPolicy.Silence.pending_pub`, with `pubNode r x = pubNode r y`, proves equal pending
lists at the same supplied `env`. `BtcPolicy.Silence.silence` carries equality of the model
observations, including those lists, along `obsPair`, with `g = .committed`,
`r.traversal = .always`, `r.dynamics = .dynamic`, `r.registration = .preserve`,
`r.closeTime = .ratchet`, `r.driverTime = .ratchet`, `Coupled r a b`, and both initial
`NodeInv` premises at their own ratchets. The walk shares inputs and stops at either
entering state's horizon or the `wfEvent` boundary; applying it to secrecy remains subject
to `SEC-10`'s "release-history premise" and "digest premise", and `DUR-1`'s limits.
No theorem carries the rest of "Its bytes are asserted identical across normal and duress
and across armed-pre-`T` and idle twins". It is the one read surface
that waits on the sign lock, and it is NOT structurally isolated from arm-dependent work: the
release pass holds the same lock.
No theorem carries "It is the one read surface that waits on the sign lock", or that the
release pass holds that lock and the route is not structurally isolated from arm-dependent work. What keeps its timing pin-uniform is dynamic `T` (`DUR-14`),
which keeps the pre-`T` due set empty on armed and idle nodes alike; if that ever stopped
holding this would need re-analysis.
`BtcPolicy.Silence.not_due_pub_of_armed`, with `r.closeTime = .ratchet`,
`r.driverTime = .ratchet`, `NodeInv r n n.ratchet`, `preHorizon r env n = true`,
`n.armed = true`, `c ∈ n.cands`, `c.hot = true` and
`selEsc r (selIds n) c = false`, proves that the projected candidate is not due, even with
its freeze erased. This is a hot-candidate model result, not a bound on lock work or timing.
No theorem carries the rest of "What keeps its timing pin-uniform is dynamic `T`", or the
rest of "which keeps the pre-`T` due set empty on armed and idle nodes alike". A separate, weaker residual: the route is unauthenticated,
so any network observer can poll it and infer that a request was being processed, including
one that was refused — a spend-activity timing channel, not a duress oracle.
No theorem carries "any network observer can poll it and infer that a request was being
processed, including one that was refused", or "a spend-activity timing channel, not a
duress oracle".

**SEC-21** A post-wrench coordinator's power is exactly: censor, selectively deliver, strip
ladder rungs and re-sign, and submit a claw-back, which pays only the escape wallet (`CHN-35`:
"paying EVERY output to the escape descriptor").
`BtcPolicy.Classification.admitted_members_classed`, with
`validateRequestShape rule r = true`, proves that an admitted claw-back is escape-class;
`BtcPolicy.Classification.required_pays_no_vault_coin`, with
`validateRequestShape .required (.clawback nSequence nLockTime outs) = true`, excludes vault
outputs. Together with `classify`, this carries the output-kind restriction in the model,
where membership is supplied; it does not establish descriptor derivation or the coordinator's
complete powers. No theorem carries the rest of "A post-wrench coordinator's power is exactly". Censoring or selectively delivering requests
can suppress the sweep or influence which selected Escape confirms, including by delivering a
request whose selected Escape inflates the coverage denominator (`DUR-22`: "an absent or inflated
prevout a selected Escape names is counted too").
`BtcPolicy.Exhibits.phantom_denies_a_real_escape`, with no hypotheses, proves that
`e1` fails 51-percent coverage in `passPhantom`: `e1` spends value 60 and the selected phantom
names value 1000 in a read totaling 100. This is one fixed denial, not a delivery strategy
or confirmation theorem. No theorem carries the rest of "Censoring or selectively delivering
requests can suppress the sweep or influence which selected Escape confirms". Stripping uniformly or differently per node
only downgrades the `T`-time sweep, at worst to the base when that base is admissible. This
bound assumes a common base with matching user-signature material and enough successful fire
passes, quotas and partial delivery; it promises neither confirmation nor success under arbitrary
delivery failure (`DUR-28`: "This fallback requires enough successful fire passes, quotas and
partial delivery within the fire windows").
`BtcPolicy.Cursor.finalized_reaches`, with `m ≤ top` and
`t ≤ nodes.countP (released · m)`, proves that model finalization returns rung `m` or higher.
This carries only the rung-selection part once the required releases are supplied; it does
not prove that stripping leaves enough matching partials at the base, or model user signatures,
delivery or confirmation. No theorem carries the rest of "Stripping uniformly or differently
per node only downgrades the `T`-time sweep, at worst to the base when that base is admissible".
It cannot redirect funds, cause arbitrary bytes to be broadcast, create a new
attacker-authorized spend, or steal.
No theorem carries "It cannot redirect funds, cause arbitrary bytes to be broadcast, create a
new attacker-authorized spend, or steal". A pre-wrench-compromised one can substitute the PIN
(`SEC-42`). No theorem carries "A pre-wrench-compromised one can substitute the PIN".

**SEC-22** The chain backend requires a synced transaction index and the sealed chain's identity
before any other check (`WTC-3`). The ceremony is the highest-consequence surface (`MAN-24`–
`MAN-38`). The node configuration and preimage are the at-rest surface: the key is derived at
start from a preimage the machine does not hold (`MAN-15`). No theorem carries this.

## The PIN

**SEC-23** Both enrolled digests MUST be evaluated on every request and the verdict selected in
constant time (`SPN-16`); a short-circuit would cost a duress PIN one extra Argon2 evaluation,
measurable by the coordinator-controlling attacker and averageable over replays.
No theorem carries "a short-circuit would cost a duress PIN one extra Argon2 evaluation,
measurable by the coordinator-controlling attacker and averageable over replays". A byte-compare
alone is not sufficient. No theorem carries this.

**SEC-24** A valid duress PIN is a matching compare: it MUST never consume the attempt budget and
MUST arm regardless of lockout (`MAN-23`, `DUR-4`). The budget rate-limits wrong PINs only, so
flooding wrong PINs produces denial and never an unfrozen quorum.
`BtcPolicy.Kernel.no_hot_partial_while_armed`, with `Reachable r w` and
`w.node.armed = true`, proves that one fire pass queues no hot partial. It does not model the
PIN attempt budget or exclude authority released before arm. No theorem carries the rest of
"flooding wrong PINs produces denial and never an unfrozen quorum".

**SEC-25** The PIN is plaintext to the nodes — Direction 3 of `ADR-0012`, accepted permanently.
A device-bound coordinator-opaque token would need hardware beyond PSBT signing; a two-key
device-visible scheme closes substitution but sacrifices the hostage window.
No theorem carries "A device-bound coordinator-opaque token would need hardware beyond PSBT
signing", or "a two-key device-visible scheme closes substitution but sacrifices the hostage window". Direction 3 stands
on two reasons: silence protects the person, and the residual is honestly bounded.
`BtcPolicy.Silence.silence` proves equal model observations along `obsPair`, with
`g = .committed`, `r.traversal = .always`, `r.dynamics = .dynamic`,
`r.registration = .preserve`, `r.closeTime = .ratchet`, `r.driverTime = .ratchet`,
`Coupled r a b` and both initial `NodeInv` premises at their own ratchets. The runs share
inputs and stop at either entering state's horizon or the `wfEvent` boundary; applying this
to secrecy remains subject to `SEC-10`'s "release-history premise" and "digest premise".
`DUR-1` says "emit equal observer projections" and
"No theorem carries the rest of this silence clause".
No theorem carries the rest of "silence protects the person", or "the residual is honestly bounded". The
allowlist constrains WHERE coins go, never WHO controls the destination; that is what makes the
Hot budget enforceable, and it is a narrower property than "stops theft".
The modeled destination predicate `BtcPolicy.Classification.allowlisted` tests output kinds,
not key ownership. `POL-20` calls its Hot result an "acceptance-time admission bound";
its `BtcPolicy.Ledger.bridge` takes the cohort, amount, cap and counting premises stated there
and proves `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`. This carries that accounting
bound, not a theft bound or a proof that allowlisting alone enforces it. No theorem carries
the rest of "The allowlist constrains WHERE coins go, never WHO controls the destination", or
"that is what makes the Hot budget enforceable".

**SEC-26** Higher-entropy PINs are defence in depth, not load-bearing: the one-compromised-node
duress trigger is closed by coordinator request signing (`SPN-7`), and duress detection by a
compromised node is already accepted.
No theorem carries "Higher-entropy PINs are defence in depth, not load-bearing", or
"the one-compromised-node duress trigger is closed by coordinator request signing".

## Deployment

**SEC-27** Every federation node MUST run on its own host, with its own backend, on genuinely
independent infrastructure. A deployment in which one host holds more than `t − 1` signing keys
is not a `t`-of-`n` deployment whatever the descriptor says: the first thing an attacker
should do is take that host, and `OPS-52` is what makes that misprovisioning fail at deploy
time.
No theorem carries "A deployment in which one host holds more than `t − 1` signing keys
is not a `t`-of-`n` deployment whatever the descriptor says", or
"`OPS-52` is what makes that misprovisioning fail at deploy time".

**SEC-28** No correlation class — provider account, network block, physical location,
household, operator — MAY host `t` nodes (`ADR-0009`). From rollout stage 6 a deployment tool
MUST refuse such a topology; stages 2–5 run under `ADR-0015`'s test-only waiver with capped
funds, and any claim of compliance dates from stage 6. Sealing does not substitute for
diversity: a VPS is never sealed against its provider's console and rescue mode.

**SEC-29** The coordinator host MUST NOT itself become a correlation class: provider-console
sessions for the node hosts must not all live, logged in, on the machine that drives the vault
and sits beside the user under duress.

**SEC-30** Provider-account hygiene — strong second factor, no provider session on the
coordinator host — is part of the security perimeter of every sealed node (`ADR-0005`).

**SEC-31** A `/unseal` endpoint, a durable never-cleared Lockdown flag, and any location holding
`t` preimages are each individually rejected (`ADR-0007`); they are the reasons node
resurrection cannot be safely revived, not a roadmap.
No theorem carries "node resurrection cannot be safely revived".

## Residuals — accepted, and named

Every residual below is accepted deliberately. An implementation MUST NOT claim to have closed
one without the change that closes it being recorded against the finding.

**SEC-32** **`t` compromised nodes plus the user key is unrecoverable** (A6).
No theorem carries "`t` compromised nodes plus the user key is unrecoverable". The mitigation is
operational — `SEC-28` — not cryptographic.

**SEC-33** **Censorship** (`DUR-34`). A hot spend pending before the wrench can finalize once it
is due (`SPN-38`) when the duress Carrier is kept from `t` nodes.
Fixed completion example: `BtcPolicy.Exhibits.HotLedger.adr0014_completions`, with
`BtcPolicy.Exhibits.HotLedger.adr0014`, `sys0`, `plain`, `cfg`, `V`, `BtcPolicy.Budget.params`,
`BtcPolicy.Kernel.current` and `BtcPolicy.Ledger.current`, proves the two recorded broadcast
completions. The fixture starts unarmed, receives honest peer partials and contains no duress
Carrier; it is not a multi-node censorship or confirmation theorem. No theorem carries the rest of
"A hot spend pending before the wrench can finalize once it is due (`SPN-38`) when the duress Carrier is kept from `t` nodes". User-authored and user-destined, so
attacker funds only with stolen hot keys.
No theorem carries "User-authored and user-destined, so attacker funds only with stolen hot keys". `POL-20` states: "The Hot budget provides an
**acceptance-time admission bound**, not a rolling completion-loss bound."
For admission, `POL-20` says "The accounting theorem is `BtcPolicy.Ledger.bridge`, at one cut",
"its conclusion is `q * Ledgers.outflow cohort ≤ cuts.length * cfg.cap`" and
"No replacement rolling completion-loss formula is specified." Its cohort, amount, cap and
counting premises remain owned by `POL-20`. A window of
completions can include admissions from different windows; the counterexample belongs to
`ADR-0014` and the conformance case is `CNF-58`.
The fixed example is `BtcPolicy.Exhibits.HotLedger.adr0014_refutes_completion_bound`:
with that same fixture and configuration, some completion window exceeds the withdrawn
`n / t` bound. `BtcPolicy.Exhibits.HotLedger.adr0014_completions` records its two completions
from the two distinct acceptance times in that trace. Completions here are modeled broadcasts,
not confirmed transactions or a general loss bound.

**SEC-34** **The hostile-at-wrench crippled Escape.** The coordinator can compose a compliant
but crippled Escape; the coverage threshold and feerate floor bound it, and it can still strand
up to `100 − escape_coverage_pct` percent of the vault in Recovery limbo.
Partial coverage arithmetic: `BtcPolicy.Coverage.burn_bound`, for natural `i`, `d`, `P` and `pct`,
assumes `d ≤ i`, `i ≤ P` and `covers d P pct = true`; it proves
`(i - d) * 100 + i * pct ≤ i * 100`. This bounds undelivered value among the inputs moved,
not the unswept vault or Recovery; the denominator premise is owned by `DUR-22` and coverage
by `DUR-24`. No theorem carries "The coordinator can compose a compliant but crippled Escape".
No theorem carries the rest of "the coverage threshold and feerate floor bound it".
No theorem carries "it can still strand up to `100 − escape_coverage_pct` percent of the vault in Recovery limbo". Denial, not theft. No theorem carries this.

**SEC-35** **Post-Lockdown stragglers versus stolen recovery keys.** After Lockdown a locked
node cannot sign new Normal-path transactions. For straggler coins no already-signed payment,
in-flight Escape or claw-back, user-signed refresh, or other permitted Normal-path spend can
still move (`SEC-54`'s per-coin condition), recovery holders have sole custody until that coin's own timelock matures,
counted from its confirmation (`CHN-4`), with only an alert in opposition. Recovery-key custody is the sole protection from Lockdown until
that coin's own timelock matures.
Partial local admission exclusion: by the definitions of `BtcPolicy.Kernel.accept` and `BtcPolicy.Kernel.refuse`, a locked-down node is unchanged by `accept`. This is Carrier admission, not a complete model of Normal-path signing; refresh and claw-back ingress are not kernel events. Partial alert support: `BtcPolicy.Alerts.recovery_never_swallowed`, for any snapshot and supplied spend, assumes `isRecovery s.witness = true` and proves a Recovery verdict; `BtcPolicy.Alerts.duty_ignores_lockdown`, for any other duty inputs, equates the duty result with the latch set and clear. This is local classification and processing, not alert delivery or protection efficacy. No theorem carries the rest of the new-signing, conditional sole-custody, timelock-exposure or sole-protection claim; the per-coin exclusion is a scope condition, not a proved absence of other spends.

**SEC-36** **Coordinator auth-key loss bricks the Normal path.** The pubkey is pinned in the
immutable manifest; rotation is a new vault, and the ceremony backs the key up separately for
that reason (`MAN-29`).

**SEC-37** **A hot spend accepted before the duress PIN can bring Lockdown forward to a moment a
coercer chooses.** A hot spend accepted before the first duress-PIN ingress, not broadcast, whose
fire window has not closed at the arm caps `T` at its `fire_at − epsilon_secs`, or at `now` when
`now` is later, whether or not it can still fire.
One-decision cap: `BtcPolicy.Kernel.earliestHotFire_le`, with `c ∈ n.cands`,
`inHotDomain r env n c = true` and `c.fireAt = some f`, gives an earliest time at or before `f`.
`BtcPolicy.Clocks.Wall.belowFire_initial` uses that ordering to bound `newDeadline`;
`BtcPolicy.Clocks.Wall.belowFire_clamp` preserves the bound on `writtenDeadline`, with its
sample-order premise discharged at the same `env.eff`. By the definition of `holderDecision`,
its written `T` is thus at or before `max(f − n.epsilon, env.eff)` for this domain member.
This is one local decision, not a trace-wide or coercer-control theorem.
Fixed examples: `BtcPolicy.Exhibits.TwoRun.arm_before_fire_at_is_capped` and
`BtcPolicy.Exhibits.TwoRun.arm_at_close_is_capped` use `edgeTrace` at 60 and 140;
`BtcPolicy.Exhibits.TwoRun.settled_spend_in_window_caps_arm` uses `settledTrace` for each
Boolean claw-back choice, proving `T = 510` after settlement or terminal marking. These use
`BtcPolicy.Kernel.current`, `BtcPolicy.Ledger.current`, `BtcPolicy.Exhibits.TwoRun.cfg`,
`sys0` and `tblD`; the fixture is one 2-of-3 node with delay 200, epsilon 5 and slack 40.
They prove these executions, not arbitrary payment-time control. No theorem carries the rest of
"A hot spend accepted before the first duress-PIN ingress, not broadcast, whose fire window has not closed at the arm caps `T` at its `fire_at − epsilon_secs`, or at `now` when `now` is later, whether or not it can still fire". It can therefore bring Lockdown forward to a
moment a coercer who knows the owner's payment times chooses. `DUR-14` says "a hot spend in the
hot domain at arm time whose `fire_at − epsilon_secs` has already passed collapses the window to
now", and `DUR-13` says "A settled or terminal hot candidate whose window has not closed stays in
it". `duress_delay_secs` is a ceiling.
For the initial computation, `BtcPolicy.Deadline.initial_le_ceiling`, over natural
`start`, `delay`, `now`, `eps` and optional earliest hot time `eh`, proves
`initialT start delay now eh eps ≤ max (start + delay) now` without further hypotheses.
This is one arithmetic computation, not a run-wide bound from the first ingress.
No theorem carries the rest of "`duress_delay_secs` is a ceiling". This residual is accepted, a spend settled (`SPN-33`) or
made terminal by a claw-back while its window is open included, for the reason `ADR-0028` decision
3 gives.

The floor beside it, absent a backward wall step: once armed, `T` stays at or above `F +
min(duress_delay_secs, hold_secs − epsilon_secs)`, with `F` the effective time of the first
duress-PIN ingress and the subtraction saturating at zero, except through such a spend.
Fixed floor examples: `BtcPolicy.Exhibits.TwoRun.floor_holds_on_ordinary_routes` proves seven
recorded deadlines equal `500 + min 200 (h - 5)` for `h ∈ [100, 300]` on `floorTrace h`;
`BtcPolicy.Exhibits.TwoRun.floor_holds_on_crossed_refusal` proves seven equal 700 on
`crossedFloorTrace` at Hold 300. They use `runHold`, `holdSys`, `cfg`, `tblD`,
`BtcPolicy.Kernel.current` and `BtcPolicy.Ledger.current`; their horizon checks also use `tblN`.
The fixture starts empty and unarmed at one 2-of-3 node, with delay 200, epsilon 5 and slack 40;
`F` is 500. These are finite executions, not an invariant over all traces. No theorem carries
the rest. Every
later hot spend's `fire_at` is at or after `F + hold_secs`, since `SPN-30` says "A hot-class
spend's fire time is `ingress_now + hold_secs`"; every start `DUR-13` computes after `F` is at or
after it; and every write of `T` is at or after its own `now`.
`BtcPolicy.Kernel.T_written_only_by_arm_or_accept`, for any rule, environment, world and event,
assumes `(step r env w e).1.node.T ≠ w.node.T`; it proves the event is a receipt or an acceptance.
For the numeric part, `BtcPolicy.Deadline.initialT` and `BtcPolicy.Deadline.shrink` have an
outer `max` with `now`. By the definitions of `newDeadline`, `writtenDeadline` and
`holderDecision`, a holder decision's written `T` is at or after its effective sample.
`BtcPolicy.Silence.shrunk_cases`, for any rule, environment, node and request pair, proves
`shrunkDeadline` is either the old `T` or, on an armed hot acceptance, a `shrinkDeadline`
value. Under `shrunkDeadline r env n sp es ≠ n.T`, its value is therefore at or after `env.eff`.
These are local expression/call bounds, not a first-ingress or run invariant. No theorem carries
the rest of "every write of `T` is at or after its own `now`". No theorem carries
"Every later hot spend's `fire_at` is at or after `F + hold_secs`", or
"every start `DUR-13` computes after `F` is at or after it". A replay of a spend this node has
broadcast, a hot spend whose window has closed without this node broadcasting it, a refusal whose
computed Escape id is a resident hot spend's, which writes no hot `fire_at` (`DUR-13`), and a late
ordinary decision therefore leave `T` at or above the floor.
The fixed ordinary-route and crossed-refusal floor examples above cover these routes on their
recorded traces; `BtcPolicy.Exhibits.TwoRun.shut_unfired_spend_keeps_first_arm`, with `sys0`,
`cfg`, `tblD` and the current kernel and ledger on `unfiredTrace`, proves the first arm writes
700 and checks both tables' horizons (also `tblN`). No theorem carries the rest of
"A replay of a spend this node has broadcast, a hot spend whose window has closed without this node broadcasting it, a refusal whose computed Escape id is a resident hot spend's, which writes no hot `fire_at` (`DUR-13`), and a late ordinary decision therefore leave `T` at or above the floor". Where `hold_secs − epsilon_secs` is
the smaller arm and the first duress-PIN ingress accepted a hot spend, that spend, while it is in
`DUR-13`'s hot domain at the arm, caps `T` at `F + hold_secs − epsilon_secs`, or at the arm's `now`
when that is later; where that spend is in the domain at an arm landing by then and no such spend
caps it lower, as in `BtcPolicy.Exhibits.TwoRun.floor_holds_on_ordinary_routes`, `T` lands on the
floor. Either arm can be the smaller.
The two Hold values in `BtcPolicy.Exhibits.TwoRun.floor_holds_on_ordinary_routes` witness the two
arms and equality on that trace, with the fixture and limits above. The one-decision cap
composition above also supplies the numerical upper cap when the domain member's supplied
`fireAt` is `F + hold_secs`; it does not derive that fire time from first ingress.
No theorem carries the rest of
"that spend, while it is in `DUR-13`'s hot domain at the arm, caps `T` at `F + hold_secs − epsilon_secs`, or at the arm's `now` when that is later",
or "where that spend is in the domain at an arm landing by then and no such spend caps it lower, as in `BtcPolicy.Exhibits.TwoRun.floor_holds_on_ordinary_routes`, `T` lands on the floor". Where `hold_secs < epsilon_secs` the floor is `F`, which
every write after `F` keeps.
With saturating natural subtraction, `hold_secs < epsilon_secs` makes
`min(duress_delay_secs, hold_secs − epsilon_secs)` zero, hence the displayed floor is `F`.
The local update bounds above put a holder decision's value, and a changed `shrunkDeadline`
value, at or above `F` when their own effective sample is at or above `F`; the latter also
requires `shrunkDeadline r env n sp es ≠ n.T`. This is not a first-ingress/run invariant.
No theorem carries the rest of "Where `hold_secs < epsilon_secs` the floor is `F`, which every write after `F` keeps". `BtcPolicy.Exhibits.TwoRun.floor_holds_on_ordinary_routes` runs both
arms, `BtcPolicy.Exhibits.TwoRun.floor_holds_on_crossed_refusal` such a refusal, and
`BtcPolicy.Exhibits.TwoRun.shut_unfired_spend_keeps_first_arm` a first arm with a hot spend whose
window shut unfired.

**SEC-38** **A sustained fee spike above what the ladder can pay** leaves the Escape unconfirmed
and the coins frozen for Recovery. It interacts badly with the 10% fee cap on small vaults.

**SEC-39** **A pre-positioned vault-authorized replacement of an Escape's unconfirmed parent**,
signed before the wrench and broadcast after it under full-RBF, removes the Escape's chained
input; the outcome matches accepted total censorship — funds safe, Lockdown, no theft.
No theorem carries "the outcome matches accepted total censorship — funds safe, Lockdown, no theft".

**SEC-40** **No external human has reviewed this system** (`ADR-0017`, `F18`). One review, at
rollout stage 9, gates the lift of the dust caps; three capped mainnet rungs run before it with
the cap as the mitigation. Correlated automated review panels — including the reference
project's own — are not a substitute, and this set must not be read as evidence that a review
has happened.

**SEC-41** **The Recovery path is the only exit from Lockdown for coins no other permitted
Normal-path spend can still move (`SEC-54`), and it is not private.**
No theorem carries this conditional Recovery-only claim or "it is not private". A
Recovery spend is branch-identifiable on-chain by construction (`CHN-9`).
Partial witness-selector support: `BtcPolicy.Alerts.selector_snoc`, for arbitrary prefix `l`,
selector `sel` and final element `last`, proves `selector (l ++ [sel, last]) = some sel`.
`BtcPolicy.Alerts.isRecovery` tests whether that selector is `some []`, by definition.
This identifies a supplied witness's empty selector, not script execution or privacy of an
on-chain Recovery spend. No theorem carries the rest of
"A Recovery spend is branch-identifiable on-chain by construction (`CHN-9`)".

**SEC-42** **A coordinator compromised BEFORE the wrench nullifies duress.** Persistent malware,
a poisoned build, a tampered dependency, or a wrench that begins mid-spend while the normal PIN
is in RAM: any of these reads the normal PIN and substitutes it, so the Escape never arms, no
node locks down, and — because every observable is pin-uniform by design — the user sees exactly
what a working duress path would show.
Fixed no-arm example: `BtcPolicy.Trace.published_replays_with_current`, over its fixed
`w0` and `publishedInputs` under `BtcPolicy.Kernel.current`, proves the final node is unarmed.
`BtcPolicy.Kernel.armed_sticky`, for any rules, environment, world and event, assumes
`w.node.armed = true` and preserves that bit across one step. Induction over `Kernel.run`
therefore excludes arming at every prefix of that fixed normal replay, whose inputs are
described below. This is not a PIN-substitution or no-Lockdown theorem. No theorem carries
the rest of "any of these reads the normal PIN and substitutes it, so the Escape never arms, no
node locks down". Partial observation support: `BtcPolicy.Silence.silence`, for one node, two
enrolment tables and one shared input trace, assumes `g = .committed`,
`r.traversal = .always`, `r.dynamics = .dynamic`, `r.registration = .preserve`,
`r.closeTime = .ratchet`, `r.driverTime = .ratchet`, initial `Coupled r a b` and both
initial `NodeInv` premises at their own ratchets. It proves equal `Obs` pairs along
`obsPair`, which stops before either entering state fails `preHorizon` or `wfEvent` rejects
the event. These are projected observations, not machine timing or serialized bytes; application
to secrecy has the premises owned by `SEC-10`. It does not cover a coordinator compromised
before the wrench. No theorem carries the rest of "because every observable is pin-uniform by design — the user sees exactly
what a working duress path would show". This is **conditional theft**, not mere nullification:
the coerced hot spend completes after the Hold, and an attacker who also holds the hot keys owns
it.
Partial Hold support: `BtcPolicy.Kernel.not_due_before_hold`, under
`r.holdCheck = .hotClock`, `c.hot = true` and
`c.acceptedAt.aged env.mono n.holdSecs = false`, proves `due r env n c = false` at that
sample. This is a local no-early-due result, not eventual completion or attacker ownership.
Fixed completion example: `BtcPolicy.Trace.published_replays_with_current`, over its fixed
`w0` and `publishedInputs` under `BtcPolicy.Kernel.current`, proves replay with hot candidate 1
released and broadcast, Escape candidate 2 neither released nor broadcast, the node unarmed,
and two signer exposures. The fixture supplies one normal acceptance, a holder receipt, a fire
pass at HotClock age 55 with Hold 50, a peer partial, package acceptance and send. It does not
model coercion, PIN substitution, key theft, transport or confirmation. No theorem carries the
rest of "the coerced hot spend completes after the Hold, and an attacker who also holds the hot keys owns
it". The mitigations map vector by vector: reproducible builds close the poisoned-build and
tampered-dependency vectors (`OPS-47`);
No theorem carries "reproducible builds close the poisoned-build and
tampered-dependency vectors (`OPS-47`)"; a hardened dedicated coordinator host reduces the
probability of resident malware without removing the capability;
No theorem carries "a hardened dedicated coordinator host reduces the
probability of resident malware without removing the capability"; **nothing** addresses the
mid-spend wrench. The residual is likelihood-reduced but unclosed, and it would remain unclosed
if both mitigations shipped. The remaining controls are the Hot budget and velocity window,
the Hold, the allowlist, and hardware user signing; they do not justify a rolling loss budget
(`POL-20`: "No replacement rolling completion-loss formula is specified."). The only true
prevention is a device-bound PIN, which is hardware-gated and unplanned.
No theorem carries "The only true prevention is a device-bound PIN".

**SEC-43** **The user key is software in every current driver**, on the coordinator host, which
merges A3 with `SEC-42`: an attacker who owns that host skips the wrench and signs.
No theorem carries "an attacker who owns that host skips the wrench and signs". Hardware
signing is deliberately deferred past the dust-capped rollout rungs and MUST gate the lift of
the caps (`ADR-0015`, `OPS-37`).

**SEC-44** **Reboot-death is an assumption enforced by a warning** (`STO-3`). The node warns on a
non-volatile filesystem and proceeds only under an explicit override; in that state the model's
premise does not hold.

**SEC-45** **A wall clock already wrong at Carrier acceptance** makes `D` too early or too late
(`NCH-33`). Later excursions cannot delete or extend Carrier state, but no local stopwatch can
prove the admission sample was true.
Partial deadline support: `BtcPolicy.Kernel.D_immutable`, for any rules, environment, world
and event, proves that a Carrier resident after a step either has a prior resident with the
same `cid` and `D`, or belongs to the step's accepted or refused ingress. It does not prove
residency. Under `r.retire = .byMono`, `BtcPolicy.Kernel.carrierRetained` and
`BtcPolicy.Kernel.tick` retire by `env.mono.before k.D`, independently of the wall sample.
`BtcPolicy.Exhibits.ReleaseKernel.def1_refused_with_current` proves the fixed `def1Trace`: an
acceptance at wall 50, HotClock 5 and expiry 200 fixes `D = 155`; the store-driver tick at
wall 1000000 and HotClock 15 retains it, and a receipt at wall 60 and HotClock 20 commits
candidate 1. This uses `BtcPolicy.Kernel.current` and the one-node `w0` fixture, not a full
nonce-store or clock-truth model. No theorem carries the rest of
"Later excursions cannot delete or extend Carrier state". The ordinary outcome is denial; composed with `t − 1`
compromised nodes and stolen hot keys it is the same conditional theft as censorship, with the
admission/completion distinction recorded in `SEC-33`.
No theorem carries "The ordinary outcome is denial" or
"composed with `t − 1` compromised nodes and stolen hot keys it is the same conditional theft as censorship".
Closing it needs external time authority and is not part of this revision.

**SEC-46** **Supply chain is defended by a written policy and a build discipline**, not by
cryptographic provenance a user can check on the chain. `OPS-46` and `OPS-47` are the whole
defence; an implementation that has not met `OPS-47` is defended by policy alone.
No theorem carries "Supply chain is defended by a written policy and a build discipline"
or "an implementation that has not met `OPS-47` is defended by policy alone".

**SEC-47** **End-to-end timing has no hard gate** (`F22`). The deterministic replacement compares
response bytes, ordered handler operations and pin-masked state projections across eight request
shapes, ending at handler return; post-handler fan-out and arbitrary CPU cost are exercised by
live scenarios with no pass/fail on timing. SILENCE remains normative; this is the evidence
boundary.

**SEC-48** **The delay before Lockdown at `T` has no finite bound** (`DUR-15`, `F13`).

**SEC-49** **The freshness high-water can blackhole an honest peer for unbounded real time**
(`NCH-38`, `F3`), and an unrelated Refresh can advance the coordinator-nonce high-water past a
live Carrier (`SPN-12`, `F4`).

**SEC-50** **The full UTXO-set scan remains the fallback**: `WTC-6` says "a bounded delta walk
of at most 32 blocks from a cached anchor whose block is still active" precedes it.
In the cache-source model, `BtcPolicy.VaultUnspent.serve` tries the wallet, delta walk,
then cold scan. `BtcPolicy.VaultUnspent.served_cold_otherwise` proves that fallback when
`(serve g L st v after walk s).1 ≠ .wallet` and
`(serve g L st v after walk s).1 ≠ .deltaWalk`.
`BtcPolicy.VaultUnspent.served_delta_only_when`, given
`(serve g L st v after walk s).1 = .deltaWalk`, proves a delta base with
`c.anchor.active walk = true` and a successful `deltaWalk` from it; that definition limits
nonempty walks to `deltaWindow = 32` blocks.
`WTC-6` says "A walk that covers less is discarded whole, as is one that fails any proof
(`WTC-12`), and the refresh falls through to the cold scan", but "A walk that completes becomes
the cache even where it ends below the tip".
`BtcPolicy.VaultUnspent.uncovered_walk_serves_cold`, under `.whole`, proves the short-range
fallback with `walletServed st v after = false` and
`∀ c, st.cache = some c → coversRange c walk s = false`. A failed `BtcPolicy.Watchtower.linked`
check makes a nonempty `BtcPolicy.VaultUnspent.deltaWalk` return `none`; with no wallet
source, `serve` then cold-scans. `BtcPolicy.VaultUnspent.delta_commits_walk_on_any_branch`,
under `.partialWalk` and `.untied`, proves commitment with
`deltaBase rt st = some c`, `c.anchor.active w = true`,
`deltaWalk L c s = some c'` and `coversRange c w s = true`, without requiring the endpoint
to be the captured tip. `BtcPolicy.VaultUnspent.refresh_installs_served`, for any rules,
ledger, state, views and scan, proves the served cache replaces the old one and becomes the
next delta base. These are local source-selection results, not backend execution or cost proofs.
For the latch's initial cold scan, `WTC-9` says "From the latch setting until a cold scan has
replaced the cache, every refresh with no attempt in progress starts a repair attempt from a cold
scan, whatever cache it holds"; `WTC-9` says "thereafter, while the latch holds, the cache is
advanced by delta walks or their cold-scan fallback".
`BtcPolicy.VaultUnspent.latched_unscanned_starts_attempt`, under `.neededScan`, proves the
initial cold scan replaces the cache and starts the attempt with `st.latched = true`,
`st.scanned = false` and `st.attempting = false`.
`BtcPolicy.VaultUnspent.latched_refresh_never_wallet_read`, with `st.latched = true`, proves
the refreshed cache is a cold scan or a successful delta walk, and is unchanged by replacing
the wallet and the after-listing view. These results concern the model's refresh state.
`WTC-9` says "A wallet holding no completion marker is not latched" and "A failed build or
repair is therefore not retried while delta walks succeed; the cache does not depend on the wallet".
`BtcPolicy.VaultUnspent.unbuilt_wallet_never_latches`, under `.scoped`, proves observation
leaves the latch unchanged with `w.markers = []`; it does not clear an existing latch.
`BtcPolicy.VaultUnspent.attempt_starts_only_at_cold_scan`, with `st.attempting = false` and
`(refresh g L st v after walk s).attempting = true`, proves that refresh served the cold scan,
so a refresh serving a delta walk starts no attempt. The wallet-independence result above
requires `st.latched = true`; no theorem carries the rest of "the cache does not depend on the wallet".
So a node whose backend cannot serve the descriptor wallet pays the cold scan to seed its first
cache, and after that only when the cached anchor's block leaves the active chain or a walk is
discarded; a latched node also cold-scans from the latch setting until a scan has replaced its
cache, and a repair that keeps failing adds none.
The cache-source and attempt parts of this consequence are carried by the declarations above,
under their stated hypotheses. `BtcPolicy.VaultUnspent.repair_keeps_cache`, for any import
rules, ledger, views, scan and state, proves `repair` leaves the cache unchanged; actual
backend service and scan cost are outside that model. No theorem carries the rest of
"a node whose backend cannot serve the descriptor wallet pays the cold scan to seed its first cache".
`WTC-6` says "Bitcoin Core serialises it process-wide". The risk is availability, not theft, and
the scan's mainnet cost is an implementation's to measure before it relies on the fallback.
No theorem carries "The risk is availability, not theft".

**SEC-51** **Real-chain evidence is an implementation property.** Which paths an implementation
has exercised on a public chain, and which only on regtest, is recorded by that implementation;
this set claims none of it.

## What a reviewer should attack first

**SEC-53** In order of damage if wrong: SILENCE — diff every observable between the two PIN
classes, hunting a length-preserving difference; the release gate — any path where a partial
leaves before every fire-time check, or any second egress; determinism — two honest nodes that
could disagree on a verdict or a rung from the same chain state, especially across
manifest-pinned fields; Lockdown unconditionality — a failure that skips it, since delay is
already known and unbounded; the ceremony — a way to seal a vault whose manifest, descriptor,
keys or coordinator secret disagree, or an independence violation past `MAN-28`; fail-closed-ness
— an error path that moves coins or admits a spend.
