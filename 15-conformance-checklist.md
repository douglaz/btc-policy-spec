# 15 — Conformance checklist

What an implementation must demonstrate before it holds funds. Each item names the requirement it
proves and is written so it can become a test. The reference implementation's launch gate once ran
red for dozens of consecutive runs while work merged on the assumption it was watching (`DEF-16`);
treat any unchecked box below as that same green check.

Items marked *(reference: …)* name the reference implementation's test or harness scenario that
demonstrates the property, so a reimplementer knows what shape of evidence has been accepted
before. They are pointers, not the requirement.

## Build and gate

- [ ] **CNF-1** The implementation builds from a clean checkout with pinned dependencies and no
      network-dependent manual step, and CI asserts the committed lockfiles are current BEFORE
      entering the build environment. (`OPS-48`)
- [ ] **CNF-2** The declared lint gate passes at warnings-as-errors on the declared source.
      (`OPS-46`)
- [ ] **CNF-3** The test suite and every gate below fail when a safety property is deliberately
      broken — verified against an injected regression that turns the gate red and names itself,
      and repeated in CI rather than remembered. (`DEF-16`, `DEF-15`)
- [ ] **CNF-4** No gate has been loosened, ignored or marked flaky to make it green; a red that
      cannot be explained is an open finding, not a tolerance; a scenario whose timing depends
      on machine speed derives its windows from measurement, never from a constant. (`DEF-16`)

## On-chain contract

- [ ] **CNF-5** The template parser refuses each malformed shape of `CHN-8` with its distinct
      error: not `wsh`, not `or_i`, wrong branch forms, an `older` that is height-based
      (`older(30375)` by name) or differs from the sealed `recovery_timelock`, recovery not
      2-of-3, any ranged key, any duplicate key, `t < 2`, `n ≠ 2t − 1`, `n > 15` — the last
      three at assemble, finalize and node load alike. (`CHN-1`–`CHN-5`)
- [ ] **CNF-6** The default `4224679 = 30375 | (1 << 22)` is a time-based relative lock of 180
      days; a vault sealed with another time-based value parses and a Recovery spend sets
      exactly the sealed value as `nSequence`; `0xffffffff` fails to satisfy the branch.
      (`CHN-4`, `CHN-10`, `OPR-78`)
- [ ] **CNF-7** Canonical node order is lexicographic over the key expression, `node_id` is the
      position, and startup refuses a duplicate id, a gap, an out-of-range id, and a signing key
      that is not the canonical key at its id. (`CHN-7`, `MAN-11`)
- [ ] **CNF-8** `wallet_id` is the single SHA-256 of the checksummed canonical descriptor
      string, identical on coordinator and node. (`CHN-6`)
- [ ] **CNF-9** The commitment encoding is injective over every field including input and
      output ORDER, big-endian, with txids in internal byte order; two transactions differing
      only in `nVersion`, `nLockTime` or one input's `nSequence` get distinct ids. (`CHN-24`,
      `CHN-25`) *(reference: `prop_commitment_binding`)*
- [ ] **CNF-10** `commitment_id` is the untagged SHA-256 of that encoding as 64 lowercase hex,
      and the replay log uses it as primary lookup with the complete matching keys, never the
      outpoint set. (`CHN-26`, `CHN-27`, `SPN-23`)
- [ ] **CNF-11** A user signature with any sighash type but `SIGHASH_ALL` is `BAD_SIGHASH`; a
      missing or non-verifying one is `USER_SIG_INVALID`; verification is against the node's own
      recomputed P2WSH sighash over the whole witness script. (`CHN-11`, `CHN-12`)
- [ ] **CNF-12** Mutation properties are checked separately at their owning boundaries:
      a single-field mutation of the commitment preimage changes the commitment id; changing
      coordinator-authenticated PSBT bytes invalidates the original coordinator signature; and
      changing a transaction field covered by the user's `SIGHASH_ALL` signature is still
      refused after the coordinator re-signs. Input/output order, outpoints, output values and
      scripts, version, locktime and sequences are included. Witness/signature metadata is not
      a commitment field: adding a valid partial preserves the commitment, while invalid user
      signatures and witness-bearing signer PSBTs are refused at their respective validation
      boundaries. (`CHN-11`, `CHN-12`, `CHN-22`, `CHN-25`, `SPN-7`, `WIR-21`)
      *(reference: `prop_mutation`; additional witness/metadata cases require separate evidence)*
- [ ] **CNF-101** A correctly priced 3-of-5 transaction with valid shorter DER signatures
      finalizes below its maximum vsize and is accepted at the unchanged absolute fee. A wrong
      shape estimate or finalized size above the recomputed maximum is refused. (`CHN-13`,
      `CHN-20`)

- [ ] **CNF-102** The node-key vector reproduces the complete Argon2id output and compressed
      public key; zero and out-of-range scalar outputs are refused without reduction or retry.
      (`MAN-17`, `WIR-33`)
- [ ] **CNF-103** Canonical descriptor fixtures reproduce lexical and alias normalization,
      checksums, hardened paths and ordered multipath; equivalent accepted spellings yield the
      same manifest bytes, and unsupported grammar is refused. (`MAN-39`, `WIR-34`)
- [ ] **CNF-104** The single-SHA256 commitment vector reproduces both preimage and digest,
      including integer framing and the distinction between display-order and internal-order
      txids. (`CHN-24`, `CHN-25`, `CHN-26`, `WIR-35`)
- [ ] **CNF-105** The user signer accepts each admissible request group, including a Refresh
      and a Spend with a valid nonempty ladder. A malformed final rung returns no signed member.
      Missing `witness_utxo` or disagreement with the selected full-parent output is refused
      before any signing. (`CHN-22`, `CHN-23`)
- [ ] **CNF-106** For every signature boundary in the wire profile, a valid low-S signature
      passes and its mathematically equivalent high-S twin is refused using that boundary's
      invalid-signature outcome. No receiver silently normalizes it into an accepted signature
      or replay tag. (`WIR-6`, `CHN-13`, `SPN-7`, `NCH-32`)
- [ ] **CNF-136** The maximum finalized vsize is derived by SERIALIZING the witness script and a
      maximum-length witness and measuring the bytes, and reproduces `W_N` for every production
      shape from 2-of-3 to 8-of-15, the worked transaction's legacy size, weight and vsize, and
      the 71-byte DER ceiling under low-S. `weight` is 4 × the LEGACY serialization: a
      segwit-framed empty witness is refused rather than silently double-counting the `+ 2` and
      per-input `+ 1`. A library satisfaction-weight accessor is checked against the fixture
      rather than trusted by name: at 2-of-3 the current `max_weight_to_satisfy()` returns 479,
      the deprecated `max_satisfaction_weight()` returns 484, and `W_N` is 480 — so an
      implementation that reads either accessor and does not adjust is wrong by one or by four
      weight units per input. (`CHN-34`, `CHN-16`, `CHN-20`, `WIR-36`)
- [ ] **CNF-141** A Normal-path witness is built, broadcast on a regtest backend, and confirms,
      with its elements in exactly this serialization order: the empty `CHECKMULTISIG` dummy, `t`
      federation signatures in descriptor key order, the user signature, a single `0x01` byte as
      the branch selector in the second-to-last position, the witness script last. The
      Recovery-path witness carries an EMPTY push as selector and no user or federation
      signature. A witness with the selector anywhere else, or federation signatures out of
      descriptor order, fails script validation — asserted by broadcasting it, not by comparing
      bytes. (`CHN-9`, `CHN-10`)
- [ ] **CNF-142** An Escape spends only vault outputs, pays every destination output to the
      escape descriptor, and has `nLockTime = 0`. Exercise `CHN-15`'s "every input's `nSequence`
      to `0xfffffffd`" on the base with an empty and a nonempty ladder, and on every rung.
      In otherwise valid, user-signed requests, fault one input's sequence in the base with
      each ladder shape and in each rung in turn: gate 25 refuses `escape:bump_ladder` and
      stages nothing (`SPN-27`: "any other sequence value refuses as `escape:bump_ladder`"). The
      composer's ladder derives rungs at `4×`, `16×` and `64×` the base fee, funds each from the
      largest output with ties to the lowest index, and drops a rung by each of `CHN-17`'s three
      rules exercised separately — over the sealed ceiling, funded output below 10 000 satoshis,
      increase below `CHN-16`'s minimum; with `escape_bump_max_fee_pct = 0` the ladder is empty.
      (`CHN-14`, `CHN-15`, `CHN-16`, `CHN-17`, `SPN-27`)

## Policy checks

- [ ] **CNF-13** Every check of `POL-6` has a passing and a failing test on both the spend and the
      Escape, the latter with the `escape:` check prefix. (`POL-6`, `POL-13`, `SPN-27`)
- [ ] **CNF-14** The evaluation order holds: a spend that is both non-allowlisted and over the
      Hot cap is `DEST_NOT_ALLOWED`; one both over the cap and over the fee cap is
      `HOT_BUDGET_EXCEEDED`. (`POL-6`)
- [ ] **CNF-15** Exercise `POL-4`'s "derive indices `0..=max` if it has a wildcard": a
      successful wildcard derivation at `max_derivation_index` matches; a successful script at
      `max + 1` does not match when it differs from every derivation actually scanned in the
      descriptor (`BtcPolicy.Membership.not_matches_beyond_max`). Include a descriptor with
      wildcard and definite paths, and the zero bound. Exercise `POL-4`'s "both the external
      and the internal chain are scanned" and "A definite descriptor ignores `max`".
      Exercise `POL-4`'s "An index the library cannot derive is skipped": a failed index
      contributes no match, even for an empty output script, and a later successful derivation
      can still match. An everywhere-failing derivation matches nothing. These are runtime
      acceptance tests; the formal proofs do not establish implementation conformance.
- [ ] **CNF-16** `OP_RETURN`, dust to a stranger, and an allowlisted wallet's address beyond
      the bound are all `DEST_NOT_ALLOWED`; a vault script beyond the bound on an INPUT is
      `UNKNOWN_INPUT`. (`POL-9`, `POL-10`)
- [ ] **CNF-17** An unrecognised output with a `bip32_derivation` hint is `CHANGE_NOT_DERIVABLE`
      and without one is `DEST_NOT_ALLOWED`; the hint never makes an output pass. With multiple
      unrecognised outputs, demonstrate both opposed hint orders `[false, true]` and
      `[true, false]`: `POL-10` requires "the first such output in transaction order MUST decide
      the refusal code from its own hint". Include a recognised prefix to distinguish the first
      unrecognised output from the first transaction output. Assert that both unrecognised outputs
      appear in the fault list in transaction order, each with its own hint-selected code, in
      both opposed hint orders and with the recognised prefix; the outer code and check remain
      the first failing output's verdict. (`POL-10`, `API-25`)
- [ ] **CNF-150** Exercise `API-25`'s "Eligibility is exactly this inventory" with positive
      cases for every row, not just absence checks. At the pure evaluator boundary, use matching
      nonempty transaction/map counts and multiple missing `witness_utxo` inputs; separately
      supply every `witness_utxo` and multiple foreign input scripts; separately pass both
      earlier checks and fail multiple destinations. Assert the exact nonempty lists and the
      head code/check. For node-path cases, pass all preceding admission, signature and other
      gates with correctly signed requests; do not substitute a signature refusal for a policy
      refusal. Exercise the pure missing-UTXO row directly when signature verification prevents
      it being reached through ingress; do not reorder ingress to expose it.
      (`API-12`, `API-14`, `API-25`, `POL-7`, `POL-9`, `POL-10`, `POL-13`)

      Exercise list ordering with nonadjacent failures and passing items before and between them.
      With exactly 32 failures assert all are present and `truncated = false`; with 33 and a
      larger set assert the first 32 and `truncated = true`. Fault both an earlier and a later
      eligible check, and both the spend and Escape, and assert that only the first refusing
      check on the first refused transaction contributes. A passing spend followed by a failing
      base Escape must emit `tx = escape` and the corresponding prefixed outer check. Compare
      decoded pure-check lists across honest nodes with identical evaluation inputs, without
      requiring cross-node serialization equality. (`API-25`, `SPN-27`)

      With otherwise valid signatures over the submitted prevout evidence, supply multiple
      confirmed script/value mismatches against the backend, including each mismatch kind;
      assert the ordered input list. Absent/unconfirmed prevouts do not enter that list. On
      Refresh and Clawback separately, arrange mempool-spent inputs failing the replacement test
      and assert `replacement_inputs`, `UNKNOWN_INPUT` and the respective transaction role;
      include multiple failed inputs and a passing replacement twin. Reach the refresh interval
      check with earlier checks passing, test too-young and unconfirmed creating transactions
      separately and together, and assert the precise input list. At equality of the interval
      assert no age refusal; differing tips may change the chain-dependent list. Use controlled
      chain answers to isolate these checks without changing their order.
      (`API-25`, `SPN-25`, `SPN-43`, `SPN-46`, `SPN-50`)

      Assert omission for every no-list category in `API-25`, including each preceding
      emptiness/map-count row at the evaluator boundary, signature failures, classification,
      fees, budgets, capacity and rung-only failures. Paired normal/duress Spend requests that
      reach each applicable eligible check must have identical diagnostic members within one
      node; a PIN refusal must not expose later diagnostics. Refresh and Clawback tests remain
      pin-less. Replay each cacheable list-bearing spend refusal with the exact PSBT under a
      fresh nonce and assert the member is verbatim; mutate derivation metadata without changing
      the commitment and assert fresh evaluation. Change the relevant chain/replacement state
      and assert fresh verdicts, and verify Escape and ladder refusals never populate the
      spend-refusal entry. (`API-25`, `DUR-1`, `SPN-23`, `SPN-24`)

      Exercise the coordinator with a valid nonempty list for each admissible side/code family
      and every transaction role it can send; assert those members are usable diagnostics.
      Then inject malformed types, missing fields, empty entries, duplicate/descending indices,
      mixed sides, both/neither index field,
      negative/fractional/out-of-bounds indices, extra entry fields, excess entries, non-Boolean
      `truncated`, a true truncation flag on a short prefix, unknown codes, incompatible code
      families, wrong output-hint codes, a head code differing from the outer code, an unsent
      transaction and a rung role. Assert whole
      member discard, bounded allocation before decoding, and the same refusal delivery/watch/
      retry behavior as the absent-member twin. Vary `check` and `detail`, including an Escape
      prefix and secret-like text, and show they supply no diagnostic authority.
      (`API-16`, `API-25`, `OPR-50`)

      Where optional rendering is implemented, a valid list actually displays on a live
      interactive terminal in local words attributed to the node, beside a computable local
      evaluation. Redirect that receiving output while leaving another terminal attached:
      suppress the list. Inspect logs, artifacts and persisted state for absence of the list
      and derived comparisons; retain only the closed refusal code. Verify `check`, `detail`
      and other peer-chosen diagnostic text are never printed or retained. For absent, invalid,
      valid and deliberately lying but structurally valid lists, compare sent requests, retries,
      recomposition, coin selection, outcome reports and exit status: all must be identical.
      Include batched refresh in this comparison, using the scenarios in `CNF-122` and
      `CNF-151`; compare batch memberships, authorizations and held-back counts too.
      Compare chain-call traces with diagnostics enabled and disabled under `OPR-65`'s
      "This diagnostic feature adds no chain calls."
      (`API-16`, `OPR-8`, `OPR-9`, `OPR-65`)
- [ ] **CNF-18** `hot_outflow` excludes vault and escape outputs and the fee, sums several hot
      outputs, counts an unrecognised output, and the per-transaction cap refuses exactly when
      `outflow > hot_max_per_tx` — equality passes, one satoshi over refuses — for every class.
      (`POL-11`) *(reference: `prop_refusal_core`)*
- [ ] **CNF-19** The fee cap admits `fee × 100 = 10 × total_in` and refuses one satoshi more;
      outputs exceeding inputs is `PSBT_INCONSISTENT` / `fee_cap`; an empty input or output set
      is `psbt_consistency`. (`POL-7`, `POL-12`)
- [ ] **CNF-20** The policy core has no clock, chain, PIN, network or mutable-state dependency,
      demonstrated the way the language allows — in Rust, a dependency list of exactly the
      consensus and descriptor crates and no I/O in the module. (`POL-1`, `POL-15`, `OPS-46`)
- [ ] **CNF-21** An allowlist or escape descriptor whose extended-key flavour disagrees with the
      sealed network is refused at assemble, at finalize and at node load, naming the role and
      never printing key material; a definite key passes on every network. (`POL-8`)
- [ ] **CNF-22** A spend paying 99% to the hot wallet and dust to the escape wallet passes
      evaluation — every output is allowlisted — and is refused `PSBT_INCONSISTENT` /
      `transaction_class` by classification under BOTH PINs; the conformance suite MUST
      construct this spend end to end, not only at the unit level, and MUST be shown to go red
      naming that scenario when the mixed arm is faulted to return escape-class. (`CHN-30`,
      `POL-10`, `DEF-15`)
- [ ] **CNF-23** Property: over arbitrary output sets against fixed vault, escape and hot
      descriptors, an attacker-controlled output is only ever hot-class or refused — never
      escape-class, never refresh-class — and the refusal core matches an independent oracle.
      (`CHN-30`, `CHN-31`) *(reference: `prop_refusal_core`)*
- [ ] **CNF-24** A refresh-shaped SpendRequest and a non-refresh RefreshRequest are both refused
      `transaction_class`, and an Escape that is not escape-class is `escape:transaction_class`.
      (`CHN-32`)
- [ ] **CNF-25** A SpendRequest whose spend is escape-class is refused `transaction_class`
      under both PINs, and the same transaction submitted as a ClawbackRequest is accepted; a
      ClawbackRequest whose transaction is hot-class or refresh-class is refused
      `transaction_class`. (`CHN-32`, `CHN-35`)

## Spend lifecycle

- [ ] **CNF-26** The gate order of `SPN-5` holds with its three columns: for each refusal, whether
      the nonce was consumed, whether the request reached the outbox, and whether this node
      counted itself a holder, asserted by reading state, not logs. The delivery-horizon
      predicate is exercised at BOTH of its positions: refused at gate 10 it propagates, records
      no intent and counts this node in no holder set; refused at gate 13 or 16 it propagates AND
      stages the intent the arm hook already wrote. Neither signs a partial. (`SPN-5`, `SPN-9`,
      `SPN-17`, `SPN-19`)
- [ ] **CNF-27** The nonce log prunes an expired entry before judging its nonce replayed, judges
      a live entry replayed before consulting capacity, refuses at 4 096 without evicting, and
      mutates neither entries nor the high-water on any refusal. (`SPN-11`, `SPN-14`)
- [ ] **CNF-28** A backward clock step cannot revive a pruned nonce, and a forward reading passes
      through `effective_now` unchanged; the upper freshness bound uses the raw clock.
      (`SPN-10`, `SPN-13`)
- [ ] **CNF-29** Resubmitting an accepted request after all preceding gates pass answers the
      recorded `Accepted` verbatim and re-stages; resubmitting the same refused commitment and
      exact spend PSBT bytes answers the recorded refusal and does not stage. Correcting an
      invalid user signature or prevout script without changing the commitment forces fresh
      evaluation; a fresh-nonce duress retry with corrected valid bytes stages normally.
      A duress resubmission of a normal-accepted commitment under a fresh nonce records a
      duress intent. Conversely, stage a duress intent A and a normal accepted copy B naming the
      same spend commitment; keep A below quorum, let B reach a live holder decision, and assert
      arm, sweep authorization, selected Escape's set bit and the freeze before a fire pass.
      Staging and replay acceptance alone leave the node unarmed; the hot partial never leaves,
      and only an eligible Escape releases when its window opens. Repeat with B accepted before
      and after A retires at `D` while the pair's expiry still admits B, including a correct-clock
      pre-authentication sample followed by a lock wait. Retain separate intents and unchanged
      resident lifecycle state. The all-normal twin releases the hot partial. (`DUR-5`, `NCH-40`)
      A fresh retry whose fetch fails before its clock bounds end returns cached
      `Accepted`; a retry whose fetch consumes the expiry or delivery margin instead takes the
      post-preflight clock refusal and stages. Neither case skips the PIN/arm hook or performs
      backend I/O under a node lock. (`SPN-20`, `SPN-21`, `SPN-23`, `SPN-24`)
      *(reference: `duress-resubmission`,
      `preflight_concurrency::a_fetch_failure_does_not_override_an_already_accepted_replay`;
      the elapsed-clock case requires separate evidence)*
- [ ] **CNF-30** The velocity window refuses when the live sum plus the new outflow exceeds the
      cap, refuses at 4 096 reservations naming capacity, ages against the monotonic clock while
      also holding until wall expiry, keeps a reservation whose partial was released or
      broadcast, and refunds an unexposed one on expiry or conflicting confirmation. A forward wall step does not
      free a live reservation. Within a live reservation window, a registration refusal preserves
      an earlier acceptance's reservation for the same commitment, but unwinds a reservation
      newly placed by this request. Exercise the complete ingress/registration transition.
      (`POL-16`–`POL-19`, `SPN-29`) *(reference: `censorship-residual-bounded`)*
- [ ] **CNF-31** A refresh is `REFRESH_SUBORDINATED` while any spend is pending or in its
      preflight, including one whose inputs do not overlap the refresh; the two halves of the
      predicate produce byte-identical refusals. (`SPN-45`)
- [ ] **CNF-32** `REFRESH_TOO_SOON` fires for an input that was an OUTPUT of a refresh accepted
      within the interval, and `REFRESH_FEE_EXCEEDS_CAP` admits `fee = cap × vsize` and refuses
      one satoshi more, where `vsize` is the MAXIMUM FINALIZED vsize of `CHN-34` and not the
      unsigned transaction's size — a case whose two readings differ by more than a factor of two,
      so a test that does not name which one it used proves nothing. (`SPN-46`, `SPN-47`,
      `CHN-34`)
- [ ] **CNF-33** A refresh racing a spend's out-of-lock preflight is subordinated, demonstrated
      live with the spend held inside its preflight window by a deterministic backend barrier
      that releases on the harness's signal — never by sleeps or by stopping a backend
      process. (`SPN-31`, `DEF-7`)
- [ ] **CNF-34** Candidate registration charges the whole reservation up front, refuses the pair
      atomically with `CANDIDATE_CAPACITY` when it cannot admit both members, never evicts a
      live candidate for capacity, and leaves an already-resident compatible pair untouched by
      registration. Fresh registration records reciprocal sibling ids and the requested roles,
      with exactly one candidate per id. Same-PIN and cross-PIN fresh-nonce replays add the Carrier
      while preserving non-default terminal, released, held-partial and quorum state; separately
      exercise schedule reapplication, armed shrink and window traversal under both PINs.
      Under either PIN, exercise the identity refusals in `SPN-32`: both one-member directions,
      crossed pairs, swapped roles, equal ids (also on an empty registry), mismatching transaction,
      hot classification or expiry, and an unpaired claw-back in either position. Every refusal
      returns `PSBT_INCONSISTENT` / `candidate_identity` and leaves all residents unchanged.
      Exercise a differing ordered rung-txid list, including empty versus nonempty, and valid
      changed PSBT bytes with identical transactions and ordered rung txids: the former refuses,
      the latter stays compatible after fresh evaluation. Settle a claw-back, replay the defeated
      pair under a fresh nonce, reach its holder decision, then evict the claw-back from the chain
      view and drive a fire pass: the defeated spend releases nothing. (`SPN-32`, `SPN-33`, `SPN-23`,
      `DUR-14`, `DUR-20`)
- [ ] **CNF-35** `/pending` lists exactly the live, accepted, unsettled hot-class commitments,
      sorted. An entry remains before and at its expiry and is removed strictly after it;
      before expiry, only settlement of it, its sibling, or an input-conflicting transaction
      removes it. Refresh stays subordinated while that entry is live after the in-flight marker
      ends, under both PINs. (`SPN-30`, `SPN-33`, `SPN-42`, `SPN-45`, `API-21`)
- [ ] **CNF-36** `EXPIRY_TOO_SHORT` fires with check `delivery_horizon` at `expiry = now +
      horizon − 1` and passes at equality; with check `commitment_expiry` at `expiry = fire_at +
      slack − 1` for a hot spend and passes at equality. (`SPN-9`, `SPN-30`)
- [ ] **CNF-37** Release sends the prefix of rungs from the release floor through
      `min(latch, quota_rung_cap)`, samples the release time after the guard is held, and sends
      nothing for a frozen hot candidate or a closed pair. Quotas below the reserved allowance
      do not underflow; a batch unable to fit a complete rung sends nothing and advances no
      release bookkeeping; computed caps never exceed the last rung. The cursor starts at 0,
      advances to `U + 1` only on a pass that released at least one rung, and is never rewound:
      a quota-starved candidate reaches its top rung across successive passes instead of
      re-sending its lowest rung forever, and a pass that releases nothing leaves it unchanged.
      (`SPN-38`, `DUR-8`, `DUR-27`)
- [ ] **CNF-38** Mempool settlement removes input-conflicting hot candidates from `/pending`
      but retains their reservations independently of candidate residency. Subsequent conflicting
      confirmation, including an armed Escape, refunds only unexposed reservations; removing
      candidates alone does not refund them. Expiry and aging follow the budget rules.
      (`SPN-33`, `POL-18`, `POL-19`, `DUR-33`, `DEF-5`)
- [ ] **CNF-39** A request fans out to every peer exactly once and ends after one round at
      `n × (n − 1)` relays; a node never relays a request whose nonce it did not consume.
      (`SPN-35`, `NCH-28`)

## Duress and Lockdown

- [ ] **CNF-40** SILENCE is gated deterministically: for each of at least these request shapes —
      first Carrier, armed, fresh and replay-cached claw-back, replay-cached hot, Hot-budget
      refusal, a locked-out node, and an in-flight receipt for the same nonce — the synchronous
      response, the ordered handler operations, a pin-masked projection of the whole channel
      store and of the whole sign state including the attempt budget, the schedule-work counts,
      the PIN evaluation count and the Carrier derivation count are identical under both PINs.
      Wall-clock skew is measured and reported as advisory only. (`DUR-1`, `SEC-47`, `DEF-11`)
      *(reference: `normal_and_duress_ingress_op_sequences_*`, `two-spend-probe`)*
- [ ] **CNF-41** `/healthz` and `/pending` bodies are byte-identical between a node armed through
      the production confirmation path before `T` and an idle twin from the same configuration,
      and between the same request under the normal and the duress PIN. (`API-20`, `API-21`)
      *(reference: `healthz_is_byte_identical_on_an_armed_pre_t_node`,
      `pending_is_byte_identical_*`)*
- [ ] **CNF-42** Both Argon2id digests are evaluated on every SpendRequest in fixed order, the verdict
      is constant-time selected with a double match reading as duress, an empty or over-long PIN
      is forced wrong AFTER both evaluations, and the attempt budget is charged once with
      normal ≡ duress ≡ no-op. (`SPN-16`, `MAN-23`, `SEC-23`)
- [ ] **CNF-43** After flooding wrong PINs to lock a node out, a valid duress request still
      records its intent, still stages, and the node still arms at `t`; a correct PIN while locked
      out gets the same `BAD_PIN` bytes as a wrong one. (`SPN-18`, `DUR-4`, `SEC-24`)
      *(reference: `lockout-then-duress`)*
- [ ] **CNF-44** Ingress never sets the arm bit; the arm commits only when `t` distinct holders
      are counted on the receipt path; `committed` and `armed` are separate values and nothing
      in production keys on `armed`. Exercise each staged refusal class in the `SPN-5` gate
      table under both PINs, before and after commitment computation: reach an actual distinct
      holder quorum before `E` and `D`, assert the decision occurred, then drive a fire pass.
      Check `DUR-5`'s "A refused Carrier MUST NOT open any candidate" against a resident closed
      pair and unrelated residents, preserving already-open authority. Check `DUR-4`'s "an
      intent refused before then names no pair" and `DUR-10`'s "Every holder decision whose
      intent names a pair": unbound refusals insert no selected id, bound refusals do the
      applicable set work, and both still perform duress arm, hot freeze, deadline and window
      work. Compare responses and ordered work between PIN twins through the decision. Accepted
      ingress and accepted replay are positive opening controls. Repeat bound normal refusals
      with a resident and then a retired duress intent on the same spend: the decision inherits
      the mark but still opens nothing. Unbound normal refusals inherit neither the mark nor
      the time of another unbound intent. Include registration refusal,
      retained lifecycle fields, older reservations and request-local unwind. (`DUR-4`, `DUR-5`,
      `DUR-10`, `SPN-23`, `SPN-29`, `SPN-32`, `DEF-12`)
- [ ] **CNF-45** For each arm-split vector — an Escape corrupted so local policy refuses before
      propagation, a request oversized past a peer's `max_msg_bytes`, an expiry lapsing
      mid-fan-out — at most `t − 1` releasable partials of the coerced spend exist anywhere in
      the federation. (`DUR-8`) *(reference: `arm-split-closed`, `selective-delivery`)*
- [ ] **CNF-46** A hot spend pending before a holder decision on a marked pair is suppressed at
      that decision, including a normal-PIN copy inheriting the mark, even when it races the Hold
      expiry, and its partial is never released. (`DUR-12`) *(reference: `hold-expiry-race`)*
- [ ] **CNF-47** `T` uses the earliest same-spend ingress-hold `first_seen` under both PINs,
      including nonce tombstones. Exercise an earlier normal intent, an earlier duress intent,
      deadline retirement and retirement after a completed holder decision. Choose samples
      where the effective-time floor and hot-Hold cap do not hide the difference from the
      deciding Carrier's own time or the earliest duress-only time. Another spend's earlier
      record does not contribute; an unbound intent uses only its own sample. Compare ordered
      scan and write work under both PINs. The deadline shrinks to `earliest pending
      hot fire_at − ε` on every later hot acceptance, and never exceeds `max(T, now)`: while
      `now ≤ T` it never grows, and a `T` in the past is pulled to `now` and fires now — the suite
      MUST construct that late acceptance and MUST NOT assert `T' ≤ T` on it (`F58`). (`DUR-13`,
      `DUR-14`)
- [ ] **CNF-48** Lockdown lands at `T` when the sweep is inadmissible, when the backend is
      unreadable, when package acceptance fails, and when the chain reorgs under it; every
      subsequent spend, refresh and claw-back is `FRAUD_SUSPECTED` and the in-flight Escape combine is not
      blocked. (`DUR-7`, `DUR-19`, `DUR-32`) *(reference: `fire-time-failure`,
      `reorg-duress-lockdown`)*
- [ ] **CNF-49** A sign lock or store lock poisoned by a panic makes the fire pass release
      NOTHING, forces the Lockdown latch through the lock-free path, stops the driver passes, and
      freezes the heartbeat beside `locked_down: true`; opening the pair and setting the arm bit
      are one atomic write. (`DUR-9`, `STO-10`, `DEF-4`)
- [ ] **CNF-50** The sweep selects the cheapest admissible rung at or above the bump target, falls
      back to the most expensive admissible rung, never selects below the latch, and the latch is
      monotone and bounded by three; with one rung it reads no fee signal. (`DUR-26`, `DUR-27`)
- [ ] **CNF-140** Every confirmed duress Escape is selected, and none is chosen over another. On
      3-of-5 with three distinct duress Carriers delivered so that nodes confirm them 2/2/1, the
      Escape two nodes confirmed plus a third that later confirms it reaches `t` partials and
      fires; a single-selector implementation fires nothing. Each selected Escape is gated on its
      own: one composed over a stale UTXO set fails its own coverage and releases nothing while
      the others proceed. After one selected Escape confirms, every other Escape the node had
      selected before that release fails `DUR-21`'s predicate on the next pass — no later than
      `WTC-24` — releases nothing, and all are pruned together at window close; the assertion is
      no egress, not which step refused. Two input-disjoint Escapes at coverage 51, both selected
      before the first release, one resident, do NOT both pass `DUR-24`, because the denominator
      counts both Escapes' inputs on every pass; an Escape over an unconfirmed external deposit
      selected after the first release, and an Escape another node selected, are the two that
      can confirm beside it (`F59`), and each pays the escape descriptor. An entry whose duress
      bit remains clear is never released even after another Carrier arms the node: `DUR-10`
      requires "BOTH `sweep_active` AND that entry's own duress bit". Exercise the inherited
      set-bit case separately through `CNF-29` and the bound-refusal cases through `CNF-44`.
      The holder decision's set insertion, scan and window refresh
      are byte-identical under both PINs; a shrink of `T` re-installs every selected window.
      (`DUR-10`, `DUR-20`, `DUR-21`, `DUR-24`, `DUR-28`, `DUR-31`, `SPN-38`, `ADR-0020`)
- [ ] **CNF-149** On `n = 5`, `t = 3`, use honest nodes with no prior candidate or partials
      for this base. Start with one common user-signed base and three already signed distinct
      higher rungs `r1`, `r2`, `r3`, all satisfying ingress. Keep the
      same spend, expiry, base bytes and user-signature material in every request; the
      coordinator only strips rungs and authenticates the shortened requests, obtaining no
      new user signatures. Give each shortened request body a distinct fresh coordinator nonce.
      Deliver `{base, r1}` first to two nodes, `{base, r2}` first to two,
      and `{base, r3}` first to one, under duress. Each node accepts its first pair and retains
      that local ladder. Then allow normal relay and holder decisions for every variant:
      `SPN-32`'s "same **ordered rung txids**, including the empty list" makes later different
      ladders refuse `candidate_identity`, while its "Staging on registration refusal
      remains governed by `SPN-5`, row 29 (Staging: “yes”)" permits holder progress; assert that
      refusal never merges or replaces the resident ladder.
      Arrange timely holder quorums for each locally accepted Carrier so all nodes open and
      select their common Escape. Keep every local variant admissible throughout fire, including
      the base at maximum and exact finalized vsize, with a target that latches each local top
      rung. Provide enough successful fire passes, quota and partial delivery within every fire
      window to release the full local prefix and deliver every base partial to every node.
      `NCH-24` requires "the rung is found by txid" and "the user-signature hash matches":
      assert that the base pools across all nodes, while each higher rung's retained/released
      partials come only from its original two, two or one nodes, never a quorum. Partials
      computed during a later refused registration do not enter the resident ladder or release.
      Observe each node's finalization result
      as the base, under `DUR-28`'s "highest rung at or below the latch with `≥ t` distinct valid
      partials on every input". Hold backend submission until all local finalization results
      have been captured, so another node's broadcast or settlement cannot hide a result.
      No initial delivery fails ingress; no node dies, expires, exhausts quota or loses required
      delivery, and no input conflict or admissibility failure explains the absence of higher-rung
      quorum.
      This tests `SEC-21`'s "at worst to the base when that base is admissible", not confirmation
      or progress under arbitrary delivery failure. (`CHN-15`, `CHN-16`, `SPN-27`, `SPN-32`,
      `SPN-35`, `SPN-38`, `DUR-5`, `DUR-10`, `DUR-21`, `DUR-23`–`DUR-28`, `NCH-24`, `NCH-27`,
      `SEC-21`)
- [ ] **CNF-143** `SPN-39` requires finalization "at the highest rung at or below the latch that
      carries at least `t` distinct valid partials on every input, walking downward"; a rung
      ABOVE the latch holding `t` partials is not finalized. Demonstrate per-input finalization
      in separate runs with a common, accepted Escape ladder consisting of a base and a higher
      rung, each with exactly inputs 0 and 1. Reach the holder quorum, select and activate the
      Escape under duress, and reach its open fire window with the latch at the higher rung.
      Keep both rungs admissible at maximum and exact finalized vsize, the candidate resident,
      due, unexpired and nonterminal, and its inputs unspent. Provide enough quota and successful
      fire passes to release the finalizing node's prefix through the latch. All partials counted
      below must be valid for their rung and input, with matching user-signature hashes; deliver
      peer partials through the authenticated channel and observe their acceptance. Hold further
      partial delivery and all backend submissions until the finalization result is captured;
      no rung is already visible in the mempool or chain.

      First, for `t ≥ 2`, arrange exactly `t` distinct held signers on input 0 of the higher
      rung and exactly `t − 1` on input 1, including the finalizing node's own partial in each
      set. Give the base `t` distinct valid held partials on every input, again including that
      node's own. On the fire pass, observe successful finalization of the base and no
      finalization of the higher rung: merely observing no broadcast does not pass.

      Separately, with `n = 3`, `t = 2` and distinct signers A, B and C, finalize at node B.
      On the higher rung give B exactly A+B on input 0 and B+C on input 1: B's own partial is
      already held on both, and only A's input-0 and C's input-1 partials are delivered there.
      Observe successful finalization of that higher rung. Each input meets the threshold
      independently; an identical signer subset across inputs is not required. `NCH-23` sends
      "one message per released rung per signed input" and `NCH-25` stores "at most one partial
      per `(rung, input, signer)`". Admission refusal, invalid partials, a candidate that is not
      due, expiry or settlement cannot substitute for either finalization result.

      The re-authorization under the store lock immediately before
      the send is the linearization point between arming and sending: with the freeze bit set, or
      the Escape removed from `selected_escapes`, AFTER package acceptance returns and BEFORE the
      send, nothing is broadcast. Demonstrate it by injecting exactly that ordering, because a
      check placed before assembly instead of before the send passes every other item here and
      leaves the window `DUR-11` exists to close.
      (`DUR-11`, `DUR-28`, `DUR-29`, `SPN-39`, `NCH-23`, `NCH-25`)
- [ ] **CNF-51** Coverage and the floor are evaluated in overflow-safe arithmetic on outputs at
      the maximum finalized vsize before release and on the exact vsize after finalization; a
      rung that overpays past `100 − coverage` percent is never selected. (`DUR-23`–`DUR-25`)
- [ ] **CNF-52** The bump target is `⌊median(block at tip − tip mod 6) / 5⌋ × 5`, reads no
      mempool, and an error or absent reading yields `target = 0` — after which `DUR-26` still
      selects the cheapest admissible rung at or above the sealed floor and still honours the
      latch, so a test asserting "the base rung" is only correct when rung 0 is admissible and the
      latch is 0. The median follows `WTC-2`'s
      five steps exactly: non-coinbase population and non-coinbase denominator, per-transaction
      score `⌊fee × 4 / weight⌋`, weight-accumulated to the first score with
      `2 × cumulative ≥ total`, no interpolation, empty ⇒ 0. A block of many small high-feerate
      payments beside a few large consolidations MUST be exercised, because that is where a
      count median and a weight-weighted median diverge by orders of magnitude rather than by
      the five-unit step. (`DUR-30`, `WTC-15`, `WTC-2`)
- [ ] **CNF-53** An Escape over a replaced external parent never releases a share, and Lockdown
      at `T` holds regardless. (`DUR-22`, `WTC-24`) *(reference: `toxic-parent`)*
- [ ] **CNF-54** An Escape chains off an in-flight refresh's output rather than conflicting with
      its input; coarse subordination holds; the coerced spend is dead. (`DUR-22`, `SPN-45`)
      *(reference: `in-flight-refresh`)*
- [ ] **CNF-55** A claw-back fires at ingress on an armed node and on an idle one with
      byte-identical responses and identical ordered handler operations; it touches no PIN
      budget, no intent and no overlay; one that spends the armed Escape's inputs is signed, and
      while it is resident or confirmed at `T` the Escape releases nothing, failing at `WTC-24`
      and never at `DUR-24`, whereas one evicted before `T` leaves the Escape admissible; a
      locked-down node refuses it. (`DUR-36`, `SPN-51`)
      *(reference: `escape-class-sequences`)*
- [ ] **CNF-56** A killed node cannot restart on the same generation and cannot rejoin; with
      `t` or more armed survivors the sweep still fires; below `t` the outcome is Lockdown only.
      (`DUR-18`, `STO-1`, `STO-4`) *(reference: `reboot-death`)*
- [ ] **CNF-57** An armed Escape whose confirming block is re-orged out re-settles from the
      retained candidate at the same rung and still beats the coerced spend whose input the reorg
      re-opened. (`DUR-31`) *(reference: `reorg-escape-resettles`)*
- [ ] **CNF-58** With the duress Carrier kept from a holder quorum, an already-pending hot
      spend can complete on nodes with no holder decision setting the arm bit; nodes that
      recorded the mark arm if a later accepted Carrier naming that pair reaches its holder
      decision. A new coerced pair releases no honest hot partial. Verify the
      acceptance-time cohort bound of `POL-20` from admission records, including refunded
      unexposed reservations. Reproduce `ADR-0014`'s delayed-holder trace: its completion interval
      exceeds the withdrawn completion-loss bound while every ledger passes its admission
      checks. The report MUST distinguish admission time, first release and completion time.
      (`DUR-34`, `POL-18`, `POL-19`, `POL-20`)
      *(reference: `censorship-residual-bounded` for the censorship case; the delayed-holder
      trace requires separate evidence)*

## The channel and the Carrier

- [ ] **CNF-59** Every vector block in `08-wire-contract.md` reproduces from its published
      preimage, and the implementation's own encoder produces those bytes from the described
      fields. (`WIR-25`–`WIR-31`)
- [ ] **CNF-60** Each rejection reason of `NCH-18` is produced by its named condition and by
      nothing else, in its owning validation order, and a rejection is never retried by the sender.
      A partial naming an unknown candidate with a wrong sighash type takes `WRONG_SIGHASH_TYPE`.
      A sender classifies every reply on its HTTP status and decoded `status` member: the same
      reply serialized compactly and with spaces after its colons is accepted identically, and
      neither is treated as a transport anomaly. (`NCH-8`, `NCH-17`, `NCH-18`, `NCH-24`,
      `WIR-1`, `WIR-11`)
- [ ] **CNF-61** An envelope one second outside `[now − 300, now + 60]` is stale; seen nonces are
      pruned by their own timestamps so a future-stamped nonce lives until the high-water
      catches up; the high-water never lowers. (`NCH-12`, `NCH-13`)
- [ ] **CNF-62** The quota is charged before the nonce is inserted, is charged for stale and
      replayed envelopes, is not charged for an envelope that fails signature verification, and
      `retry_after_secs` equals the time until the oldest charge leaves the window. (`NCH-15`)
- [ ] **CNF-63** The receipt outcomes of `NCH-29` are produced by their named states: an in-flight
      owner answers `RATE_LIMITED{1}` before any memory-hard reservation and without recording
      the sender; a clock-refused exact receipt answers `RATE_LIMITED{30}` and mutates nothing;
      the outer-stale path answers `STALE_TIMESTAMP` for every non-matching, terminal, malformed,
      unknown or non-Spend case. (`NCH-29`, `NCH-36`, `NCH-37`, `DEF-1`)
- [ ] **CNF-64** `D` is fixed at acceptance and unmoved by a forward or backward wall step, a
      retry, a relay, an alternate signature or an unrelated accept; a receipt at `mono_now ≥ D`
      is ignored; the intent and memo retire only through the triggers listed in `NCH-40`; the nonce
      tombstone survives until both `E` and `D` end, retaining the original duress bit,
      `first_seen` and optional computed pair ids after each retirement trigger that leaves
      the process alive. Process death removes all of it. Assert no new holder, repeated arm,
      opening or deadline extension on receipts to retired and already committed Carriers,
      including after wall rollback, and no re-creation through nonce replay. Pruning with only
      one clock bound ended retains the entry; both ended removes it. Normal tombstones and
      unrelated marked pairs create no inherited duress. Candidate expiry is unaffected. (`NCH-33`–
      `NCH-35`, `NCH-40`) *(reference: the Carrier clock mutation controls)*
- [ ] **CNF-65** An unseen valid alternate signature on a live body costs at most one
      non-blocking derivation per `(nonce, sender)`, a busy slot consumes no allowance, a
      mismatch spends it, a third unfamiliar signature is terminal, and the exact resolved
      signature stays usable. (`NCH-39`)
- [ ] **CNF-66** Every protocol-valid Spend request pads to one payload length regardless of PIN
      length, every envelope pads to one length regardless of signature length, and neither
      secret-bearing buffer reallocates. (`NCH-21`, `NCH-22`, `WIR-17`)
- [ ] **CNF-67** Each endpoint attempt carries a fresh envelope, the retry schedule of `NCH-8` is
      followed, a `RATE_LIMITED` wait does not advance the backoff, and a message past its
      deadline is given up. (`NCH-7`, `NCH-8`)
- [ ] **CNF-68** A partial on an unknown or expired candidate answers `UNKNOWN_CANDIDATE` (and
      the expired one is evicted with its reservation refunded), a duplicate is an idempotent
      `ACCEPTED` that never displaces the first, and a partial on an inadmissible rung is
      released to nobody. (`NCH-24`–`NCH-26`, `DUR-27`)
- [ ] **CNF-69** A peer assertion or partial never authorizes a new signature or early release.
      A positive control shows the same listener parses a validated share from every honest
      node while the federation is whole. A relayed coordinator-authenticated request executes
      local ingress and may sign only after local acceptance. (`NCH-3`, `SPN-2`, `NCH-27`)
      *(reference: `wiretap_positive_control`; request-relay case requires separate evidence)*

## The HTTP API

- [ ] **CNF-70** Every route answers its documented status codes and bodies — 413, 408, 400, 500
      on `/sign`; 429 and 500 on `/pending`; the tagged 400/409/429 on `/channel`; 404 and 405
      elsewhere, both with empty bodies — and the `/sign` job detached by the handler deadline
      still commits its verdict. (`API-2`–`API-8`, `API-22`, `WIR-1`, `WIR-9`)
- [ ] **CNF-71** `/events` loses nothing and duplicates nothing across cursor reads, its cursor
      advances with nothing new, a re-scanned spend does not re-alert, and eviction at 1 024
      releases the key. (`API-17`, `API-18`, `WTC-20`)
- [ ] **CNF-72** `/healthz` has exactly the five fields, the heartbeat is bucketed to 10 seconds,
      published by the deadline driver alone, and never regresses on a backward clock step;
      `vault_wallet_serving` reads `false` against a backend started with `-disablewallet` and
      the node logs one warning at boot. (`API-19`, `API-20`, `WTC-3`)
- [ ] **CNF-73** A concurrent `/pending` read is shed with 429 immediately, the permit survives
      the poller disconnecting, and a poisoned lock answers 500. (`API-22`)
- [ ] **CNF-74** Unknown members in a request are ignored, the retired `signed_psbt` response
      shape does not decode, and a body without `escape` does not decode. (`WIR-4`, `API-10`,
      `API-12`)
- [ ] **CNF-75** Decoder robustness: arbitrary bytes, near-valid bodies with one field replaced,
      one byte flipped or a truncation, and authenticated garbage — a correctly signed envelope
      or request whose payload is noise — never panic at any parser, and the near-valid corpus
      asserts the EXACT reject reason. (`API-5`, `NCH-18`) *(reference: `prop_decoder`,
      `prop_decoder_robustness`)*
- [ ] **CNF-145** Every refusal `code` the implementation can emit is one of exactly `API-13`'s
      set and every `check` one of exactly `API-14`'s, asserted by enumerating the
      implementation's emitters against the two lists — a string either side does not name is a
      defect in whichever is wrong, never a tolerance. `WRONG_DESCRIPTOR` and
      `escape_class_residual` are never emitted, and
      every `escape:`-prefixed check has its unprefixed twin. This is the API contract a second
      implementation matches, and it graduates to BLOCKING with the other wire items.
      (`API-13`, `API-14`, `POL-13`, `POL-14`)
- [ ] **CNF-146** The claw-back carries none of refresh's guards and all of a spend's: a
      claw-back is accepted while a hot spend is pending on the node and, once resident, defeats
      it (`SPN-33`); one over a coin younger than `refresh_min_interval_secs` is accepted; one
      whose fee exceeds `refresh_max_feerate × vsize` but not `POL-12`'s cap is accepted, and one
      over the cap is `FEE_EXCEEDS_CAP`; one with 25 inputs is accepted; one with any
      `nSequence` other than `0xfffffffd`, a non-zero `nLockTime`, or a vault-derived output is
      `transaction_class`; a foreign output receives `POL-10`'s refusal and one with hot outputs
      over the cap `HOT_BUDGET_EXCEEDED`, both before classification; one over a resident
      vault-authorized refresh's output is `Accepted` at ingress and assembled once `WTC-24`
      admits the parent, while one over an unconfirmed external deposit is refused at fire
      time; a refresh arriving during a claw-back's preflight is `REFRESH_SUBORDINATED`; a
      claw-back whose sibling hot spend it defeated is never finalized at Hold expiry, including
      after the claw-back is evicted; a higher-fee claw-back over the same
      ordered outpoints as a resident one is accepted, assembled as a replacement (`WTC-25`) and
      enters the mempool, and one over a different outpoint set that overlaps the resident is
      `UNKNOWN_INPUT`; a `spend` variant carrying the same PSBT is `transaction_class`; the
      response is `Accepted` with `remaining_secs = 0`, the txid is in the vault-authorized set,
      the request is relayed, and `/pending` never lists it. (`CHN-35`, `SPN-50`, `SPN-51`,
      `API-24`)

## Manifest, configuration, ceremony

- [ ] **CNF-76** Changing any one preimage field — including the network byte, `policy_version`,
      the ladder ceiling, either fire-time selector, and the allowlist's exclusion of the escape
      descriptor, and both refresh bounds — changes `manifest_hash`, and a node whose recomputed
      hash differs from `expected_manifest_hash` fails to start. A manifest at any earlier schema
      revision MUST NOT be loadable: `MAN-3` makes that a version error before any other schema
      check, and states that no vault was ever sealed below revision 4, so an implementation
      refuses 1-3 rather than carrying encoders for them. (`MAN-2`, `MAN-3`, `MAN-11`)
- [ ] **CNF-77** An endorsement that does not verify is refused at finalize and, if smuggled
      past it, at every node's startup; the wire carries none. (`MAN-6`, `NCH-5`)
- [ ] **CNF-78** The ceremony accepts a valid independent 2-of-3 escape bundle supplied through
      the bundle path and a valid independent single-sig escape. It accepts both single-sig
      representations in `MAN-26`, whose compatibility rule is "Assembly MUST normalize it to the
      one-entry array before checking independence". Also accept an otherwise valid independent
      bundle with the schematic policy `wsh(or_i(pk(A),and_v(v:pk(B),pk(C))))`, substituting valid
      ranged extended public keys with origins for A, B and C and supplying the matching
      inventory. These letters are policy placeholders, not executable key strings. The case
      permits A alone or B and C together, with no single threshold over those keys. Its
      acceptance exercises `MAN-26`: "Subject to these bundle preconditions and all other ceremony
      validation requirements, including `MAN-27`, `POL-8` and all of `MAN-28`, the ceremony MUST
      accept any escape descriptor in the public grammar; it MUST NOT require a single numeric
      threshold, classify the spending policy, or add a policy-eligibility test".
      Require evidence for every cosigner under
      `MAN-28`: "every compared key and its role, the scanned range and branches, the per-cosigner
      verdict and the overall verdict, and the residual limits of the check".
      Each negative case starts from an otherwise valid independent multisig bundle, changes
      only the condition under test, and places the offending cosigner beyond the first array
      entry and first distinct descriptor key expression. Refuse a later cosigner sharing a
      master fingerprint with an earlier one; a later cosigner's derived key equal to a node key;
      and a later cosigner sharing a hot-wallet fingerprint. Retain cases for equality with the
      user, recovery and coordinator auth keys, for available ancestor-key overlap, and for
      derived or ancestor overlap with the hot wallet. Exercise overlap at the inclusive upper
      bound and on a non-first multipath branch. Update matching bundle metadata when changing
      a descriptor so that these cases fail independence, not inventory validation.
      Refuse a mixed descriptor whose first key is ranged with origin and a later key is definite
      or origin-less; also refuse wholly definite and key-less descriptors, and equal escape/hot
      descriptors. These whole-descriptor cases use otherwise suitable inputs wherever the
      targeted defect permits them. A shared-seed case MUST exhibit a detectable key equality or
      fingerprint match, not demand detection of unrelated paths. The report carries `MAN-28`'s
      limit: "The evidence MUST NOT claim seed independence or physical device separation".
      (`DOM-11`, `MAN-26`, `MAN-27`, `MAN-28`)
- [ ] **CNF-79** The ceremony refuses a federation shape other than `t ≥ 2, n = 2t − 1, n ≤ 15`
      — 9-of-17 and 1-of-1 by name — a ranged vault key, a zero-port endpoint or one outside the
      stage's transport form, two nodes on one port, and an escape bundle of the wrong role or
      without a descriptor. Refuse a cosigner inventory with missing, extra, repeated or
      mismatched entries, including a later entry's fingerprint inconsistent with its origin;
      a scalar fingerprint on a multisig descriptor; and a bundle carrying both fingerprint
      forms. Each case is otherwise valid. (`CHN-2`, `MAN-4`, `MAN-26`, `MAN-27`)
- [ ] **CNF-80** A zero ladder ceiling seals; a non-zero ceiling seals only inside `MAN-13`'s
      three bounds and only for a vault whose operator program composes rungs (`OPR-40`); a
      ceiling above the fee cap, above the coverage headroom, or above one fifth of it is
      refused with its own reason at assemble and again at finalize. (`MAN-13`, `MAN-31`)
- [ ] **CNF-81** Only `bitcoin`, `signet` and `regtest` are accepted as the network, with every
      alias, testnet and custom signet refused naming the allowed set; the code bytes are `1`,
      `2`, `3`. (`MAN-14`, `WIR-27`)
- [ ] **CNF-82** `finalize` interrupted before any artifact leaves a directory with no sealed set,
      interrupted after leaves one complete set, refuses an existing `sealed/` even when
      byte-identical, and two overlapping runs cannot publish each other's remnant. (`MAN-32`)
      *(reference: the staging fail-point seam)*
- [ ] **CNF-83** Every secret artifact is owner-only from its first byte and a looser existing
      file is never written in place; `independence.txt` is the only file read back from disk.
      (`MAN-33`, `MAN-34`)
- [ ] **CNF-84** The preimage is read with echo suppressed on a terminal, must be exactly 16 hex
      characters, is never re-prompted, and a derived key absent from the descriptor is a fatal
      startup error naming the cause. (`MAN-16`, `MAN-18`)
- [ ] **CNF-85** PIN digest validation refuses each case of `MAN-21`, including equal salts, and
      the Carrier KDF uses the maximum parameters of both slots with a fresh per-boot salt.
      (`MAN-21`, `MAN-22`)
- [ ] **CNF-86** Every load-time inequality of `MAN-9` is refused at its boundary and accepted one
      unit inside it, including the channel-gated ones only when `[channel]` is present.
      (`MAN-9`)
- [ ] **CNF-137** `policy_version` is manifest-sealed: the ceremony writes one value into every
      `node-<id>.toml`, and a node whose configured value differs from the federation's recomputes
      a different `manifest_hash` and refuses to start, before binding a socket. Demonstrate the
      reason it exists separately, and note that the obvious test does not reach it: once
      `policy_version` is sealed, two nodes differing in it also differ in `manifest_hash`, so a
      relay between them is rejected `WRONG_MANIFEST` at the envelope (`NCH-18`) long before any
      candidate lookup. To exercise the underlying failure, hold the channel's manifest identity
      constant and perturb only the value each node bakes into the commitment: the two then
      compute different `commitment_id`s for identical transaction bytes, both answer `Accepted`,
      and each one's partials draw `UNKNOWN_CANDIDATE` until the sender's message deadline lapses,
      so quorum forms only inside a group that shares a value and reaches `t`. Arming and Lockdown
      at `T` still work throughout, because a relay is matched to its Carrier by coordinator nonce
      (`NCH-32`). (`MAN-2`, `MAN-11`, `MAN-27`, `CHN-24`, `API-15`, `NCH-24`)
- [ ] **CNF-138** Both refresh bounds are manifest-sealed: a node whose `refresh_min_interval_secs`
      or `refresh_max_feerate` differs from the federation's refuses to start, and
      `refresh_max_feerate = 0` is refused at load rather than silently stranding the vault.
      Neither `REFRESH_FEE_EXCEEDS_CAP` nor `REFRESH_TOO_SOON` propagates — both are read from
      state every honest node shares — and `REFRESH_SUBORDINATED` still does, because the pending
      log and the in-flight marker are the per-node inputs the refresh path has left. The ceremony writes one value for
      each bound into every node config rather than defaulting it. (`MAN-2`, `MAN-7`, `MAN-9`,
      `MAN-27`, `SPN-43`, `SPN-46`, `SPN-47`)
- [ ] **CNF-139** Refresh age is read from the chain and from nothing else, and a node holds no
      refresh log. With every node at the same tip: a coin whose creating transaction confirmed
      one second of MTP short of `refresh_min_interval_secs` ago is `REFRESH_TOO_SOON` on every
      node and admissible on every node at equality; an unconfirmed input is refused; and the
      alternation trace `BtcPolicy.RefreshAge.alternation` (`ADR-0019`, `F52`) — one compromised
      signer rotating which honest node co-signs —
      stops at its second link on every honest node, because the first link's output is younger
      than the interval on the chain they all read. A refresh signed but never confirmed leaves no
      chain trace, so its higher-fee replacement over the same inputs is accepted, assembled over
      the resident as a replacement (`WTC-25`), and enters the mempool by BIP125 (`CHN-18`): that
      is the bump path end to end, and an implementation that keeps a private acceptance record
      and refuses it, or reads the resident's inputs as spent and cannot assemble it, has
      reintroduced the defect. The replacement's inputs read ABSENT from a mempool-inclusive
      prevout fetch while the resident is in the mempool; the age is nonetheless read from the
      creating transaction's confirming block by txid and the replacement is admitted — an
      implementation that reads age off the prevout fetch's confirmed flag refuses it
      `REFRESH_TOO_SOON` and has made the verdict depend on its own mempool. Any transaction
      with more vault-derived outputs than inputs is refused as having no class (`CHN-30`), and a
      refresh with more than 24 inputs is refused (`SPN-44`). (`SPN-46`, `SPN-47`, `WTC-1`, `ADR-0019`, `F52`)

## Chain and watchtower

- [ ] **CNF-87** A backend on the wrong chain, on a custom signet, on signet with no challenge, or
      reporting a challenge on a non-signet chain is refused at startup before any other check;
      initial block download, a missing or unsynced transaction index, and an incremental relay
      fee above 1 000 sat/kvB are refused after it. (`WTC-3`)
- [ ] **CNF-88** A Recovery-path spend is classified from the empty branch selector in the
      witness and takes precedence even when its txid is authorized; a vault spend the node
      REFUSED alerts as unrecognised; a spend the node accepted does not. (`WTC-17`–`WTC-19`)
- [ ] **CNF-89** A spend re-landing at or below the cursor after a reorg is still classified; the
      cursor rewinds to the fork point; a reorg deeper than 100 re-scans from genesis; each of
      the three chain proofs discards the pass on failure; a block arriving on top during a scan
      keeps the pass while a replaced block at the captured tip height discards it; and a panic
      anywhere in a pass resets the cursor to genesis. (`WTC-12`–`WTC-14`, `DEF-6`)
      *(reference: `reorg-watchtower-cursor`)*
- [ ] **CNF-90** A package is the candidate alone, its unconfirmed ancestors are resident and
      authorized, more than 24 ancestors is refused, a replacement spends exactly the resident
      rung's outpoints, and only `txn-already-in-mempool` is tolerated. (`WTC-23`–`WTC-26`)
- [ ] **CNF-91** The wallet birthday covers every output a reorg that leaves the settled block
      active can make live; the settled block is re-proved before the descriptors and again
      before the marker are imported; a repair never starts later than the wallet already
      covers; a wallet read is discarded unless the tip captured before it is still the tip after
      the reconciliation; a delta walk covers every height above the cache's anchor through the
      lesser of the tip captured when the walk starts and 32 blocks above that anchor, so that a
      block arriving during a discarded wallet read is walked, and a walk that covers less — a
      walk of no block below that tip included — is discarded for the cold scan; a refresh that
      finds the repair latch set and no cold scan published since it set cold-scans and starts an
      attempt, whatever cache it holds,
      and while the latch is set no wallet read replaces the cache; a refresh that finds an
      attempt in progress starts no second one; an attempt whose cold scan or wallet call fails
      or times out, before the re-import or during it, ends and leaves any latch set, and the
      next attempt starts only from a cold scan the cache itself needs, so a build or repair that
      keeps failing costs no scan of its own; a wallet holding no completion marker is not
      latched; and the fire path never scans the UTXO set. (`WTC-5`–`WTC-9`, `DEF-21`)
- [ ] **CNF-92** The vault-unspent snapshot is discarded if the tip or the mempool sequence
      moved, retried once, then fails closed. (`WTC-10`)
- [ ] **CNF-93** Against a live backend: the composer refuses the whole inventory when a scanned
      coin is mempool-spent, refuses an immature coinbase,
      prices both shapes at their preflighted vsizes, and leaves the backend's UTXO set and
      mempool unchanged. Exercise `OPR-32`'s "closed, read-only set of exactly nine calls"
      using its method inventory. For spend and claw-back, exercise `OPR-33`'s "there is no
      coin selection and no omission, subject to the claw-back contracts"; preserve the named-set
      and replacement cases. For refresh, exercise its "The entire stable confirmed inventory
      MUST be validated before any refresh filtering"; eligibility scenarios live in `CNF-151`.
      Exercise `OPR-33`'s "rejects duplicates, off-script records and an empty set", "runs the
      zero-amount two-shape preflight", and "every closing value and script equals its opening
      read". Shared evidence, retry and initial-block-download cases live in `CNF-151`.
      A correct header must not bypass a missing mempool-inclusive candidate, an opening-value
      mismatch or a closing-value change; `OPR-34` requires "refuse the WHOLE inventory".
      Both size bounds refuse before allocation,
      an absent fee estimate yields a zero rate rather than an invented floor, and a destination for another
      network is refused before any chain read. (`WTC-28`, `CHN-18`, `CHN-19`, `CHN-20`,
      `CHN-21`, `OPR-32`, `OPR-33`, `OPR-34`, `OPR-35`, `OPR-36`, `OPR-37`, `OPR-38`, `OPR-39`)
      *(reference: the `core-view` CI leg)*

## State and secrets

- [ ] **CNF-94** A node on a non-volatile filesystem refuses to start without the override, a
      second process on the same config inode fails the generation claim, and a non-empty
      Lockdown attribute is adopted as locked at load. (`STO-3`, `STO-4`)
- [ ] **CNF-95** Secret buffers are zeroized on drop, redacted from every debug rendering, and
      never reallocate after a secret is written into them, asserted in a debug build; no PIN
      appears in any log, alert, replay entry or trace. (`STO-11`, `STO-12`)
- [ ] **CNF-144** Lock order is sign lock then store lock wherever both are held, asserted by an
      instrumented build or lock-order checker that fails on inversion rather than by reading the
      code; the fire pass's release loop takes the sign lock before its nested store
      acquisitions; and no standard-library lock is held across an await point. The property is
      what makes `DUR-9`'s fail-closed release depend on the order rather than on luck.
      (`STO-9`, `DUR-9`)
- [ ] **CNF-148** No secret `STO-11` lists reaches an entry the trace adapter emits, asserted by
      a test that feeds the adapter a node holding every listed secret and finds none of their
      bytes in its output; every trace in the adapter's corpus is synthetic; and no synthetic
      identifier is derived from a PIN, a preimage or a key, so a captured trace lets nothing test
      the plaintext PIN. (`STO-11`, `STO-12`)

## Operations

- [ ] **CNF-96** A Recovery spend built from cold artifacts alone is refused by the network as
      non-final before maturity, does not finalize with one recovery key, and confirms with two
      after the median time past crosses the lock; every surviving node alerts on it.
      (`OPS-27`, `CHN-10`) *(reference: `demo recovery-drill`, `recovery`)*
- [ ] **CNF-97** The stage drill asserts Lockdown and the sweep independently, and Recovery runs
      against a fresh deposit to the locked-down vault. (`OPS-39`)
- [ ] **CNF-98** A named commit rebuilds byte-identically on a different machine, the release is
      signed with a key whose verification path is stated, and CI gates the dependency graph
      with a vulnerability audit. (`OPS-47`)
- [ ] **CNF-99** The dependency inventory recipe fails — with a non-zero status, not an empty
      listing — when the committed lockfiles are stale. (`OPS-48`)
- [ ] **CNF-100** One honest spend has confirmed on a public chain the implementation does not
      control, through a live federation with a nonzero Hold, and its record carries every
      field of `OPS-65` including its own scope and staleness statement. (`SEC-51`, `OPS-65`)

## Node internals added after the first extraction

- [ ] **CNF-107** A third concurrent `/sign` is shed with HTTP 429 and the one fixed body while
      two jobs run; a request answered 408 still holds its permit until its detached job ends;
      the shed bytes are identical across PIN classes and request shapes of one size; a refresh
      consumes a permit; a shed request consumed no nonce. (`API-4`)
- [ ] **CNF-108** A request whose `policy_version` differs from the node's is refused
      `PSBT_INCONSISTENT` / `policy_version` after signature verification and before the nonce
      log records anything; the same request as a relay receipt creates no receipt state and
      answers the peer nothing distinguishable. (`API-15`, `SPN-5`)
- [ ] **CNF-109** Ancestry validation of a candidate with `K` unconfirmed parents issues exactly
      one mempool membership read, asserted by call count and not by timing. (`WTC-24`)
- [ ] **CNF-110** An abnormal exit injected between the alternate-signature claim and its
      resolution leaves no pending marker behind, and the guard never clears a newer
      generation, a completed resolution or a spent mismatch. (`NCH-42`)
- [ ] **CNF-111** The Lockdown deadline driver runs on a thread outside the runtime, its spawn
      failure aborts startup before the listener binds, and an armed and an idle node publish
      the same heartbeat bucket on the same driven tick. (`STO-13`, `API-20`)
- [ ] **CNF-112** A test that proves an ordering synchronises on the real milestone with a
      witness channel or barrier and never polls the scheduler; a test never assumes a released
      ephemeral port stays unbound; a scenario whose work cost is calibrated derives its
      settlement window from that calibration, refuses loudly at its top when the cost cannot
      fit, and names every wait. (`CNF-4`)
- [ ] **CNF-113** A deliberate contradiction planted in a second copy of the transaction-class
      predicate, of the manifest preimage field list, and of the spend-request field list is
      caught by the gates, demonstrated once per rule. (`F14`, `AGENTS.md`)
- [ ] **CNF-114** On mainnet a below-default `recovery_timelock` requires a typed confirmation
      containing the value, recorded in `ceremony-state.json` while the manifest carries only
      the value as `MAN-5`'s convenience field; the ceremony
      displays the duration and earliest maturity in human units; the timelock and the ladder
      ceiling are one prompt. (`OPR-78`, `OPR-79`)
- [ ] **CNF-115** The ceremony writes `refresh_min_interval_secs`, `refresh_max_feerate` and
      `[pin_attempt_budget]` identically into every node config; it refuses a group- or
      other-writable parent directory, and proceeds on a mode-less filesystem only under the
      recorded flag. (`MAN-35`, `MAN-40`)
- [ ] **CNF-147** The implementation's trace adapter emits only entries of `BtcPolicy.Trace`'s
      alphabet at its published version; it replays the synthetic trace `ADR-0023` publishes
      through the formal layer pinned as its lake dependency and reproduces the decided verdict,
      the final world and each step's effects; it refuses each malformed shape the negative
      exhibits name: a wrong version byte, an entry tag no constructor carries, a truncated
      entry, bytes after the last entry, and an effect on any step but the one that emitted it;
      and, because the alphabet carries a spend's witness as the class `CHN-9`'s selector yields
      and never as bytes, the adapter's own reading of that selector from a real witness is
      demonstrated by a test over the Normal, Recovery, other and short-stack shapes, since the
      replay cannot check it. (`ADR-0023`, `CHN-9`, `OVR-17`)

## The operator program

- [ ] **CNF-116** Exit status is `0`, `1` or `2` exactly as `OPR-4` assigns; no secret byte
      appears in `argv`, the environment, a log or an artifact; `--help` performs no file or
      network access; a non-UTF-8 name and a malformed socket exit `2`; the PIN reader refuses
      cap+1 without authenticating the prefix and restores the terminal on every exit path; a
      peer's `check` and `detail` and a backend-chosen txid never appear in output, and a
      `PSBT_INCONSISTENT` explanation never says "recompose"; no production path from a spend,
      escape or refresh command can reach a broadcast call, and no HTTP response is reported
      as success. (`OPR-1`, `OPR-2`, `OPR-3`, `OPR-4`, `OPR-5`, `OPR-6`, `OPR-7`, `OPR-8`,
      `OPR-9`)

      With a valid nonempty refresh inventory and zero eligible coins, assert no authorization
      and no authorization-record entry or request, the no-eligible stdout report with the exact
      held-back count and no chain identifiers, and exit
      `0`: `OPR-65` requires "refresh MUST send nothing and write no authorization" and
      "reports on stdout that nothing is eligible, with the held-back count, and exits `0`".
      Exercise the no-op exception in `OPR-4` ("or refresh completed `OPR-65`'s no-op") and
      `OPR-2`'s boundary, "No HTTP response from a node is success". Backend
      failure, invalid or empty composer inventory, node refusal and inconclusive watch remain
      distinct error cases; none may be reported as this no-op. Repeat with long and short
      refresh intervals. Eligibility scenarios are in `CNF-151`; batch outcomes are in `CNF-122`.
- [ ] **CNF-117** Each of the nine live-vault conditions refuses when violated singly, before
      any socket; a malformed decoy `coordinator-auth.secret` beside the public artifacts is
      ignored; an old-revision manifest is refused before any current-field error and still
      parses for the cold path; a credential whose key is not the pinned one is refused; the
      live vault holds no secret and its `max_msg_bytes` conversion is checked; a secret file
      that is group-readable, a symlink or a FIFO is refused; the cookie refuses cap+1 and is
      re-read per RPC; the key guard exposes no raw view (asserted at compile time where the
      language allows); the user key and the credential are never open together. (`OPR-10`,
      `OPR-11`, `OPR-12`, `OPR-13`, `OPR-14`, `OPR-15`, `OPR-16`, `OPR-17`, `OPR-18`, `OPR-19`)
- [ ] **CNF-118** The signer never returns a partially signed group: the `(Hot, Escape)` pair
      signs, a self-paired pair and an `(Escape, Escape)` pair refuse before any signature, a
      Clawback arm's single member must classify escape-class and carries `0xfffffffd` on every
      input, and the Escape base and every rung satisfy `CHN-15`'s "every input's `nSequence`
      to `0xfffffffd`" with an empty or nonempty ladder; a sequence fault refuses the whole
      group before signing. A rung one satoshi over the sealed
      ceiling refuses while the base is exempt, an equal-fee rung is named as such, a caller's
      `wallet_id` hint does not prevent a cross-vault refusal, the seam receives no PIN, and an
      input not the vault's is a refusal, not a skip. (`OPR-20`, `OPR-21`, `OPR-22`, `OPR-23`,
      `OPR-24`, `OPR-25`, `OPR-27`, `OPR-28`, `OPR-30`)
- [ ] **CNF-119** The display renders without a key file open, no output line contains the
      word "transaction", `outflow` excludes vault change, the recorded execution order holds
      with composition refusal before the user key, `SPEND` is accepted only exactly and end of
      input is not acceptance, and a substitution between preview and authorization aborts
      before the PIN through the display-and-txids binding; when the ceiling admits rungs the
      rung count, fees and top-rung share are shown before signing. (`OPR-29`, `OPR-40`,
      `OPR-42`, `OPR-43`, `OPR-44`, `OPR-45`)
- [ ] **CNF-120** Every endpoint receives byte-identical bytes under `min(now + 60 s,
      aggregate)`; `400` and `413` advance the delivery state and continue; `NONCE_REPLAYED`
      stops only after a possible delivery; a mismatched `accepted` continues; `NotSent` occurs
      only when connect fails; the wire PSBTs carry no `non_witness_utxo` and an oversize
      request is refused locally before ingress; the clocks are sampled once and the expected
      commitment id is computed locally; a response crossing the cap is an ambiguous failure
      that keeps a valid status. (`OPR-46`, `OPR-47`, `OPR-48`, `OPR-49`, `OPR-50`)
- [ ] **CNF-121** The pre-ingress warning is written and flushed before the first request byte;
      all endpoints `NotSent` yields the definite-no-delivery report and no watch; a
      pre-deadline null continues; exactly one final poll runs at the deadline; a report-sink
      failure after possible delivery latches exit `1` without skipping the final poll; a
      claw-back carries no ladder. (`OPR-41`, `OPR-51`)
- [ ] **CNF-122** `clawback` refuses an empty selection, a duplicate, an unknown, spent or
      off-vault outpoint, and an unstable scan, before signing and the network; it accepts a
      one-coin vault and a selection covering every coin; the transaction's inputs are exactly
      the named set, it pays one output to the escape descriptor, no vault change, every
      `nSequence` at `0xfffffffd`; it reads no PIN and opens no credential before the user key
      is dropped; it is watched on its output 0 and reaches exit `0` when it appears; run again
      with `--replace` while the first is resident it composes over the recorded outpoints at a
      strictly higher fee and the nodes accept it as a replacement, and with `--outpoint` and
      `--all` together it exits `2`; help text states that the sweep is pin-less, the bump path
      and the coercion ordering; `rotate` orders its steps by trigger.
      (`OPR-66`, `OPR-67`, `OPR-68`, `OPR-69`, `OPR-76`)

      Exercise refresh batch outcomes under `OPR-65`: "Batch k+1 MUST be sent only after batch
      k's watch observed it" and "The first unobserved batch MUST stop the run and leave all
      later batches unsent". Use a valid inventory composing three batches. Observe all batches
      and assert exit `0`; separately observe batch 1, then make batch 2 locally refused before
      sending (a batch failing output validity), refused, definite no-delivery or inconclusive,
      leaving batch 3 unsent and asserting exit `1` in each case.
      In every trace, assert no next send before the preceding observation and an outcome for
      every batch: `OPR-65` requires "report every batch's outcome as observed, locally refused,
      refused, no-delivery, inconclusive or unsent". No outpoint or other prohibited diagnostic
      identifier appears. Repeat the refusal case for the refresh refusal inventory named in
      `OPR-65`, with no dropped input, split batch or refusal-driven retry: "The program MUST
      NOT drop an input, split the refused batch or retry because of that refusal."

      Current-batch delivery and watch coverage lives in `CNF-120` and `CNF-121`.
      After batch 1 was observed and batch 2 was definitely not delivered, assert the warning
      relief names only batch 2: `OPR-51` says "A later batch's no-delivery does not erase any
      earlier batch's history or authorize replay of the invocation." Inject a report-write failure
      after possible delivery and still observe every batch; the latched exit remains `1`
      under `OPR-51`'s "makes the exit `1` even if the backend later observes the change".
      The zero-eligible no-op is exercised in `CNF-116`, eligibility and batch construction in
      `CNF-151`, and fault-list independence in `CNF-150`. (`OPR-2`, `OPR-4`, `OPR-8`, `OPR-49`,
      `OPR-51`, `OPR-65`)

      Exercise `OPR-66`'s boundary, "once the program's own chain view shows every predecessor
      coin named by the sweep as spent", in a compromise-signal rotation. Begin with a nonempty
      named sweep input set and persisted predecessor consumed events, returned cursors and
      refusal codes. While a named coin remains unspent in the program's own view, show that
      polling and retained state continue, even after node acceptance or command submission.
      Spend the named set into the mempool, leave it resident, then evict it: no deletion or
      polling stop is permitted, since `OPR-66` says "a mempool spend is insufficient to trigger
      deletion or stop polling". Reintroduce the spend and confirm it.
      Then establish the complete named set as spent through that view, inspect every persisted
      container for deletion of predecessor node-supplied data, including any copies in audit
      records, and observe that subsequent monitoring issues no predecessor-node polls:
      `OPR-66` says "MUST delete everything the program persisted from the predecessor's nodes"
      and "MUST stop polling the predecessor's nodes".

      Include a later deposit that keeps the predecessor balance nonzero at retirement and a
      coin unconfirmed at the original sweep. Discover both through the program's own chain
      view after node polling stops, then claw them back once they meet the existing composer
      contract; `OPR-66` requires "Retirement MUST preserve the locally held artifacts and
      signing access" and "Discovery MUST use the program's own chain view". Inspect that
      rotation imposed no Lockdown. Check the documented deletion limit, `OPR-66`'s "not backups
      or notifications already delivered", with those external copies left outside the cleanup
      assertion. Check that no forensic-erasure or restored-SILENCE claim is made. Repeat with
      an ordinary rotation and a live vault to demonstrate that their polling and retention
      duties continue (`OPR-66`: "Routine rotations and live-vault monitoring retain their
      ordinary polling and retention duties").
- [ ] **CNF-123** `status` reports an unreachable node rather than dropping it and does not
      hang; `pending` shows per-node divergence; both diff against the authorization record,
      which every authorizing command writes before its first request byte; help states that a
      pending id is insufficient to identify coins. (`OPR-52`, `OPR-53`, `OPR-54`, `OPR-55`)
- [ ] **CNF-124** `receive` renders the one address Bitcoin Core's `deriveaddresses` derives
      for the sealed definite descriptor on the sealed network, with the coordinator absent,
      holds no index state, discloses that every deposit reuses that address, and retires it
      with the vault; the release documentation's oracle table names a library family per property.
      (`OPR-56`, `OPR-57`, `OPR-58`, `OPR-59`, `OPR-81`)

      Exercise `OPR-58`'s "including each coin's confirmation height and remaining chain time"
      with differently aged coins, checking their values and total as well as confirmation
      information and independently computing each remaining time from `OPR-62`'s
      "`max(0, MTP(P) + duration - MTP(tip))`". Spend one confirmed coin into the mempool,
      retain it there for days, evict it, then reintroduce and confirm the spend. While the
      confirmed set is unchanged, the listed membership and total remain unchanged. After
      confirmation, compare both against the newly accepted confirmed population, including
      any new vault output. Check the label and help against `OPR-58`'s "labelled a confirmed-chain
      total, never available-to-spend value", and assert no per-coin mempool mark or
      mempool-inclusive read. Maturity's population transition is exercised in `CNF-125`.
      An empty vault must give zero coins and a zero
      total: `OPR-58` says "An empty vault MUST list zero coins and a zero total, without
      composer refusal." Trace the independent `OPR-82` path ("This contract makes no
      mempool-inclusive `gettxout` call and requires no composer empty-set refusal or Escape
      preflight") for both cases.
- [ ] **CNF-125** Exercise `OPR-62`'s "Maturity MUST be computed per coin from the descriptor's
      recovery lock" and "reported as the earliest maturity across the unspent set";
      against a 90-day vault the nags fire at day 60 and day 75 and never at day 120;
      the countdown is computed with the
      coordinator absent; alerts are pulled from every node, a restart around cursor
      persistence neither re-processes nor skips an event, queue overflow during consumer
      downtime is reported as a gap, and events are correlated per node; the documentation
      states the pull trust limit and that the maturity
      control protects the Operator who looks. (`OPR-60`, `OPR-61`, `OPR-62`, `OPR-63`,
      `OPR-64`)

      On a controlled chain, use the default descriptor lock `L = 4224679`, a coin confirmed
      at height 100, predecessor MTP `1700000000` and confirming-block MTP `1700000600`.
      Its duration is `15552000` seconds. Arrange accepted tips at heights 199, 200 and 201
      with MTP `1715551999`, `1715552000` and `1715552001` respectively. At these tips the
      remaining chain times must be 1, 0 and 0 seconds, with next-block time eligibility false,
      true and true: `OPR-62` requires "`MTP(tip) >= MTP(P) + duration`, with equality passing".
      At height 200, a projected `100 × 600` seconds since confirmation is far below the
      duration, while chain time already permits recovery; using the confirming block's MTP
      instead would wrongly wait until `1715552600`. Vary wall time and the candidate block's
      timestamp without moving its parent's MTP and show the verdict is unchanged.
      Use an otherwise valid recovery transaction with the exact sequence from `CHN-10`:
      "`4224679` exactly, and in general to the sealed `recovery_timelock`". A valid time verdict
      must not be presented as signature or full transaction validation: `OPR-62` reports
      "time eligibility, not signature sufficiency or every other transaction-validity rule".
      Retain a later-confirming unspent coin in the same inventory to distinguish each coin's
      countdown from the earliest reported maturity. Obtain the evidence with the coordinator
      absent, from the descriptor and the accepted chain view.

      Spend the earliest-maturing coin into the mempool while retaining that later coin.
      Exercise `OPR-62`'s "A confirmed coin whose vault spend is in the mempool keeps counting
      until that spend confirms." Compare with an otherwise identical chain-only view on
      arrival, after days of mempool residency, and after eviction: both coins still count,
      their predecessor blocks stay fixed, and the earliest figure has no mempool-induced
      jump or countdown restart. As tips advance during residency, only the accepted chain MTP
      changes the remaining times. Reintroduce the spend and confirm it; the next accepted
      scan excludes the spent coin and the later coin now determines earliest maturity.
      This confirmation is the chain-set transition, not an arrival, eviction or residency
      threshold. Balance's total is exercised in `CNF-124`.
- [ ] **CNF-126** `recover` composes from the descriptor and a chain view with no manifest, fails
      at composition before maturity with a clear message, broadcasts itself without touching
      a node, and completes with three holders on three machines exchanging the PSBT file; a
      vault sealed before the live commands existed is documented as exiting through Recovery.
      (`OPR-72`, `OPR-73`, `OPR-74`, `OPR-75`, `OPR-77`)

      Demonstrate maturity reporting and recovery using `OPR-62`'s "from the descriptor and a
      chain view alone" and `OPR-74`'s "no manifest at all", including with the coordinator
      absent. Trace `OPR-82` independently of composer prerequisites: "This contract makes no
      mempool-inclusive `gettxout` call and requires no composer empty-set refusal or Escape
      preflight." Population and empty-balance cases are in `CNF-124` and `CNF-125`.
      A premature recovery still fails before broadcast,
      per `OPR-72`: "A premature attempt MUST fail at composition with a clear message".
      The fixture does not establish a network trust source; that open question is `F67`.
      Supplying a controlled chain view is not evidence that this gap is solved.

- [ ] **CNF-151** Exercise independent evidence under `OPR-82`, its composer integration under
      `OPR-33`, maturity under `OPR-62` and refresh under `OPR-65` against controlled chain
      reads, recording the accepted inventory and the resulting authorizations, requests,
      reports and outcomes.

      For `OPR-65`'s "MTP(tip) - MTP(confirming) >= I + min(86 400, I)" and "Only coins
      meeting this inequality are eligible; equality passes", set `I = 172800` and test ages
      `259199`, `259200` and `259201` seconds: hold back only the first. Repeat with the short
      interval `I = 60` and ages `119`, `120` and `121` seconds to exercise a margin equal to
      the interval itself. Derive ages from the confirming block's own MTP. Recovery-time
      calculation cases are in `CNF-125`.

      Inject absent, failed, malformed, stale, inactive and height/hash-mismatched tip,
      confirming and predecessor headers, including a predecessor that does not match the
      confirming header's `previousblockhash`. None may yield an accepted subset:
      `OPR-82` requires "Missing, stale, inactive, malformed, mismatched or failed evidence
      invalidates the whole evidence set, never a reason to skip a coin or call it too young".
      Exercise both the independent balance/maturity/recovery path and composer integration.
      Trace the independent path to verify `OPR-82`'s "This contract makes no mempool-inclusive
      `gettxout` call and requires no composer empty-set refusal or Escape preflight". Fault
      the block-hash resolution and block-qualified creating transaction separately: missing
      or failed reads, wrong txid, missing referenced output and mismatched value or script
      invalidate the evidence. Include a bad header for a coin that would otherwise be too
      young: `OPR-33` requires "The entire stable confirmed inventory MUST be validated before
      any refresh filtering". Composer-specific candidate checks are exercised in `CNF-93`.

      Check `OPR-82`'s "At `h = 0`, use the confirming genesis block itself" without a negative
      predecessor-height lookup. Reorg between the scan, parent/header reads and closing tip
      read; reject a mismatched scan anchor or mixed view under `OPR-82`'s "the chain info's
      tip, the scan's anchor, the captured before-tip, every other tip read and the closing tip
      MUST agree". For composition and independent balance, maturity and recovery callers
      separately, exercise a coherent fresh bracket after observed movement and movement
      exhausting `OPR-82`'s "at most three brackets per invocation, with no sleep, backoff or
      scheduler". Assert the actual bracket count and no delay or scheduling. An erroneous
      header without observed movement remains terminal without a retry: `OPR-82` says
      "An erroneous header alone is not observed tip movement and does not authorize a retry."
      Assert whole-evidence refusal, exit `1` and an evidence-failure report, with no omitted
      coin and no successful no-nag-due result, under its "Exhaustion is a local refusal with
      exit `1`, not an inconclusive watch" and "The program MUST report the evidence failure".

      For every caller above, set the initial-block-download flag on otherwise coherent chain
      info and assert refusal, exit `1` and the evidence-failure report: `OPR-82` requires
      "The chain info MUST NOT report initial block download." Clear the flag on a coherent
      behind view and show that it passes without a freshness threshold. Inspect balance and
      maturity reports for that accepted height and MTP, including an empty balance: `OPR-58`
      says "Balance MUST print the accepted tip's height and MTP" and `OPR-62` says
      "Maturity reporting MUST print the accepted tip's height and MTP".

      Supply fifty eligible coins in shuffled scan order, with confirming-block MTP ties,
      outpoint order opposed to age order, and an eligible dust input. Assert batch membership
      and sending order of 24, 24 and 2, from one accepted pass, with tied ages resolved by
      canonical outpoint order: `OPR-65` requires "sort eligible coins by increasing
      confirming-block MTP, break ties by canonical outpoint order, and partition that order
      into consecutive batches within that input limit" and "Each batch MUST be filled to
      the limit before starting the next; only the final batch may be smaller". Inspect each
      batch against its "exactly one output to the vault script, paying the sum of its inputs
      less its fee" and "Each batch is a separate transaction and a separate
      `RefreshAuthorization` containing one PSBT". Check its per-transaction fee cap and
      `CHN-18`'s "`nSequence` to `0xfffffffd`" and "inputs in canonical outpoint order (sorted by
      txid then vout, no duplicates)".
      The dust input remains included because
      `OPR-65` requires "Every eligible coin MUST be included, with no input-value threshold".
      Keep output and fee validity satisfied in this fixture; separately show that their
      failures do not authorize dropping dust. Add a young coin while keeping the eligible set
      unchanged: the same batches proceed and the held-back report gives exactly one, with no
      outpoint or other chain identifier (`OPR-65`: "Coins held back for age or margin MUST be
      reported only by count").

      The zero-eligible no-op is exercised in `CNF-116`, batch outcomes and stopping in
      `CNF-122`, and fault-list independence in `CNF-150`.
      (`OPR-4`, `OPR-8`, `OPR-33`, `OPR-58`, `OPR-62`, `OPR-63`, `OPR-65`, `OPR-72`, `OPR-82`,
      `CHN-18`, `SPN-44`, `SPN-47`)

## Deployment and rollout

- [ ] **CNF-127** A co-located federation is refused at deploy time without the bypass; with it,
      every emitted artifact carries the machine-readable non-promotable marker and the stage
      evidence records the engagement; the bypass symbol is absent from the stage-6 artifact;
      the read-surface perimeter is recorded before the nodes are reachable; the diversity
      statement is attested. (`OPS-40`, `OPS-51`, `OPS-52`, `OPS-57`)
- [ ] **CNF-128** A request posted to one ingress reaches every node and node-side broadcast;
      suppressing only request-carrier propagation makes the same path fail; the operator
      program is absent from the node image and present only in the coordinator host's install
      slot. (`OPS-8`, `OPS-50`, `OPS-54`)
- [ ] **CNF-129** Two independent builds of the sealed node image are identical; the image has
      no SSH, no package manager and no operator program; the residual-capability enumeration
      exists; the stage readiness check fails when the reviewed binary is replaced. (`OPS-53`)
- [ ] **CNF-130** A regtest migration from a five-node vault with one dead node completes; the
      successor check refuses a shorter timelock and a reused key; the audit record reconstructs
      the event unaided; exercise duress and disclosure of a compromised node release as
      separate triggers for `OPS-30`'s "sweeps FIRST and builds the successor after", and an
      ordinary patch without a compromise signal for "verifies the successor FIRST". Check
      compromise-signal guidance against `OPS-30`: "the Operator SHOULD enroll successor PINs
      such that neither new PIN verifies against either predecessor digest", including a role
      swap. Verify that enrollment performs no predecessor-digest comparison, adds no ceremony
      refusal for PIN reuse and requires no old PINs for rotation: "Enrollment tooling does not
      check this recommendation" and "the rotation does not require the old PINs". Check the
      scope: "This recommendation does not apply to routine rotations".
      Nothing provisioned under the waiver, the coordinator host included, is carried into
      stage 6. (`OPS-30`, `OPS-32`, `OPS-59`)
- [ ] **CNF-131** Key material is restored from backups alone with the primaries set aside; the
      failure-domain check is run against the real assignment and recorded, covering the
      key-role list in `DOM-10` and naming every escape key's backup. Record the Operator-identified
      spending key sets and demonstrate restoration of spending authority under the supplied
      descriptor, following `OPS-60`: "The Operator MUST identify the key sets that can spend
      under the supplied descriptor". Assess whether a coercer holding the user can reach any
      such set through keys or usable backups within the sweep's window. For a `k`-of-`m`
      wallet, record `k` and `m` and demonstrate restoration of enough distinct keys to reach
      `k`; `SEC-54` limits this formula: "The numeric threshold formulas apply only to a
      `k`-of-`m` escape wallet". Include the single-sig case and a 2-of-3 assignment where
      reaching one key does not reach the threshold; a backup of that key MUST NOT count as
      another key. Also exercise the other-policy case in `CNF-78`, using the Operator's
      identified spending key sets without demanding a numeric threshold or ceremony analysis:
      assess both the one-key and the two-key spending alternatives and record the actual
      restoration drill. Losing the one-key alternative alone need not destroy authority;
      restoring only one key of the two-key alternative does not restore that alternative.
      The check also covers the coordinator-auth-key combination in `OPS-33`, which names
      "the coordinator auth key together with any escape spending key set". Each recovery
      holder is confirmed reachable; the stage's recovery-holder realism is recorded.
      (`DOM-10`, `SEC-54`, `OPS-33`, `OPS-58`, `OPS-60`, `OPS-61`)
- [ ] **CNF-132** The five-step lifecycle drill is performed and records what broke, and is
      re-run by someone who did not design it; the lifecycle ADR names one model and every
      losing document it supersedes. (`OPS-62`, `OPS-63`)
- [ ] **CNF-133** The freeze's artifact set names one commit and contains the matrix run, the
      fresh public-chain spend and the commit statement; the Path suite is invocable,
      parameterised by network and vault, and returns pass or fail; no rung is climbed with a
      gate of the stage table unmet, and each stage has written abort criteria, descent rules
      and a ratified, observed cap. (`OPS-55`, `OPS-56`, `OPS-64`, `OPS-65`, `OPS-66`)
- [ ] **CNF-134** The launch gate runs on every push under a commit-specific concurrency group,
      carries no unconditional-run step, retains the artifacts of `OPS-67`, and its scorecard
      states the debug profile and what a green run does not prove; the Fault suite, where it
      exists, gates no stage; no merged change is cited as a rollout authorization. (`OPS-67`,
      `OPS-71`, `OPS-72`)
- [ ] **CNF-135** An independent party rebuilds the alpha artifact byte-identically; the warning
      is in the artifact; every review finding has a recorded disposition re-tested against the
      shipped commit; the coercion procedure was closed by a human reviewer and a stranger's
      dry run, never by an automated pass. (`OPS-68`, `OPS-69`, `OPS-70`)

## Tiering — which of these gate what

An untiered checklist is an unbounded commitment. These tiers gate holding funds; they do not
forbid doing a cheap item early.

**The rule.** For each item, name the production event where its test would fail, then ask: can
the Operator undo it with a sweep, a rotation or an apology? would the Operator even know it
happened without this control? can a coordinator that turned hostile at the wrench trigger it
with no human in the loop?

**BLOCKING** — "no" to the first; "no" to the second where the hidden harm is irreversible; or
"yes" to the third for anything that moves a partial or a coin. The irreversible families are
**a coerced partial released** (`CNF-37`, `CNF-45`–`CNF-49`, `CNF-53`, `CNF-56`, `CNF-143`,
`CNF-144`), **silence broken** (`CNF-40`–`CNF-44`, `CNF-55`, `CNF-63`, `CNF-66`, `CNF-150`), **a wrong
transaction agreed** (`CNF-5`–`CNF-12`, `CNF-50`–`CNF-52`, `CNF-59`, `CNF-76`, `CNF-77`,
`CNF-102`–`CNF-106`, `CNF-108`–`CNF-112`, `CNF-136`–`CNF-138`, `CNF-141`, `CNF-142`), **a theft
admitted** (`CNF-13`–`CNF-25`, `CNF-27`–`CNF-30`, `CNF-34`, `CNF-38`, `CNF-58`, `CNF-139`,
`CNF-146`), **a
secret escaped** (`CNF-78`, `CNF-83`–`CNF-85`, `CNF-95`, `CNF-116`, `CNF-117`), **the chain
misread** (`CNF-87`–`CNF-92`, `CNF-151`), **the exit lost** (`CNF-96`, `CNF-126`, `CNF-140`, `CNF-149`), **a coin spent
twice or a sweep under-covered by the coordinator** (`CNF-118`–`CNF-122`), the ingress and claim
invariants (`CNF-107`, `CNF-110`, `CNF-111`), and the epistemic pair without which every other
tick is testimony (`CNF-1`, `CNF-3`, `CNF-4`).

**PRE-SCALE** — failures the Operator absorbs at one-vault scale by watching every request and
reading every alert by hand: `CNF-26`, `CNF-31`–`CNF-33`, `CNF-35`, `CNF-36`, `CNF-39`,
`CNF-54`, `CNF-57`, `CNF-60`–`CNF-62`, `CNF-64`, `CNF-65`, `CNF-67`–`CNF-75`, `CNF-79`–`CNF-82`,
`CNF-86`, `CNF-93`, `CNF-94`, `CNF-97`, `CNF-99`, `CNF-100`, `CNF-101`, `CNF-108`, `CNF-109`,
`CNF-112`–`CNF-115`, `CNF-123`–`CNF-125`, `CNF-127`, `CNF-128`, `CNF-130`–`CNF-132`, `CNF-145`,
`CNF-147`, `CNF-148`.
The trigger is whichever comes first: a second vault; a vault the Operator does not personally
watch; or a second independent implementation, at which point the wire items (`CNF-59`,
`CNF-70`–`CNF-75`, `CNF-145`) and the replay items (`CNF-147`, `CNF-148`) graduate to BLOCKING
because the wire contract and the trace both implementations replay against the formal layer
are then the only things shared.

**DEFERRED** — `CNF-2`, `CNF-98`, `CNF-129`, `CNF-133`–`CNF-135`: real, and gating the sealed
rungs, the lift of the dust caps and the alpha rather than the first sealed vault.

**The blocking count** is derived from the lists above, not written here; a number in prose is
wrong the first time either end moves.
