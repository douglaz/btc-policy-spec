# 03 — Policy checks

The per-node PSBT checks every node runs before it signs, and the Hot budget. The pure half
(this document) takes a decoded PSBT and sealed parameters and returns one verdict; it has no
clock, no chain, no PIN and no node state, which is what lets every honest node reach the same
verdict. The stateful checks — freshness, replay, the Hold, the velocity window, refresh bounds —
are in `04-spend-lifecycle.md` and cite this document rather than restate it.

## Purity

**POL-1** Policy evaluation MUST be a pure function of the decoded PSBT and the sealed
parameters: the vault descriptor, the allowlist, the escape descriptor, `max_derivation_index`
and `hot_max_per_tx`. Same inputs, same verdict, on every node. It MUST NOT read a clock, a
chain, a PIN, a peer, or any mutable node state.

**POL-2** Evaluation MUST read each input's prevout script and value from the PSBT's
`witness_utxo`. It is the node's responsibility, before calling evaluation, to cross-check every
confirmed `witness_utxo` against its own chain backend (`SPN-25`); a `witness_utxo` that
disagrees with the chain is refused there, not here.

**POL-3** The only cryptography evaluation performs is script derivation. It does not verify
signatures (`CHN-12` happens before it), does not recompute sighashes, and does not decode
PSBT bytes (undecodable input is an HTTP 400 at the wire, `API-5`).

## The derivation primitive

**POL-4** Descriptor membership MUST be decided by **re-derivation and script equality**, never
by address string comparison and never by trusting a PSBT's `bip32_derivation` hint. For a
descriptor `d`, a script `s` and a bound `max`:

1. expand `d` into its single-path descriptors (a BIP389 `<0;1>` descriptor yields two, so both
   the external and the internal chain are scanned);
2. for each single descriptor, derive indices `0..=max` if it has a wildcard, or index 0 only
   if it is definite;
3. `s` matches iff some derived scriptPubKey equals `s` byte-for-byte.

The scan is inclusive of `max` and stops at the first match. An index the library cannot derive
is skipped. A definite descriptor ignores `max`.

The formal homes are `BtcPolicy.Membership.matchesScript_iff` for successful derivation and
failure skipping, and `BtcPolicy.Membership.matchesScript_local` for locality through the
inclusive bound. `BtcPolicy.Membership.not_matches_beyond_max` covers a wildcard path's
successful script at `max + 1` when it differs from every derivation scanned in this descriptor;
it assumes no global injectivity or path separation. BIP32 derivation, script construction and
cryptography remain an external boundary. Runtime evidence belongs to `CNF-15`.

**POL-5** Allowlist descriptors and the escape descriptor MUST use the public descriptor
grammar and rendering profile of `MAN-39`, which states: "A parser's customary display format
is not protocol authority." The destination grammar permits ranged keys with origin, BIP389
multipath, bare extended keys, or definite keys where the selected script context permits them.
The network-flavour check remains separate (`POL-8`); the vault descriptor is restricted to the
fixed template (`CHN-1`).

## Evaluation order

**POL-6** Evaluation MUST run these checks in this order and return the first failure. The order
is load-bearing: `DEST_NOT_ALLOWED` outranks `HOT_BUDGET_EXCEEDED`, and `HOT_BUDGET_EXCEEDED`
outranks `FEE_EXCEEDS_CAP`, so that a theft to a stranger is named as such and an over-cap spend
takes the propagation path `SPN-19` gives it.

| # | Check | Refusal code | `check` string |
|---|---|---|---|
| 1 | PSBT consistency | `PSBT_INCONSISTENT` | `psbt_consistency` |
| 2 | Input ownership | `UNKNOWN_INPUT` | `input_ownership` |
| 3 | Destinations | `DEST_NOT_ALLOWED` or `CHANGE_NOT_DERIVABLE` | `destination_allowlist` / `verified_change` |
| 4 | Hot budget, per transaction | `HOT_BUDGET_EXCEEDED` | `hot_budget` |
| 5 | Fee cap | `PSBT_INCONSISTENT` or `FEE_EXCEEDS_CAP` | `fee_cap` |

**POL-7** **PSBT consistency** MUST refuse, in order: a transaction with no inputs; one with no
outputs; an input-map count that differs from the transaction's input count; an output-map
count that differs from its output count; any input without a `witness_utxo`. The two emptiness
rules exist because an empty transaction has fee zero and would vacuously pass every other check.

**POL-8** **Network flavour** is checked once at load, not per request: every allowlist and
escape descriptor's extended keys MUST carry the flavour of the sealed network — main-kind
(`xpub`) for `bitcoin`, test-kind (`tpub`) for `signet` and `regtest` — and a definite key is
network-neutral. Signet versus regtest cannot be told apart from a key prefix and is a backend
identity check instead (`WTC-3`). The error names the role and the two flavours and never
prints key material.

**POL-9** **Input ownership**: every input's `witness_utxo` script MUST derive from the vault
descriptor within `max_derivation_index` (`POL-4`). A vault script past the bound is
`UNKNOWN_INPUT` exactly like a foreign script.

**POL-10** **Destinations**: every output MUST either derive from some allowlist descriptor, or
derive from the vault descriptor (verified change). An output that does neither is refused, and
the PSBT's untrusted `bip32_derivation` on that output decides only WHICH code: non-empty means
the coordinator claimed change, so `CHANGE_NOT_DERIVABLE` / `verified_change`; empty means
`DEST_NOT_ALLOWED` / `destination_allowlist`. `OP_RETURN`, dust to a stranger, and an
allowlisted wallet's address beyond the bound all fall here; there is no special case.

Separately from the verdict, **classification** (`CHN-30`) runs the same output scan and refuses
a mixed-class or unclassifiable spend `PSBT_INCONSISTENT` / `transaction_class`. Evaluation does
not call classification: a mixed hot-plus-escape spend passes evaluation, because every output is
individually allowlisted, and is caught only by the class check. Both MUST run on every spend.

**POL-11** **Hot budget, per transaction**: `hot_outflow > hot_max_per_tx` MUST be refused,
where `hot_outflow` is the sum of every output's value EXCEPT outputs that derive from the vault
descriptor and outputs that derive from the escape descriptor, with saturating addition. Equality
passes. The check runs for every class with no class argument: refresh and escape sweeps have
zero outflow by construction and cannot trip it; an output no descriptor recognises counts,
since over-counting can only refuse. Several hot outputs are summed, never capped individually.
The fee is excluded — it pays miners, is already bounded by `POL-12`, and is not
attacker-extractable. `hot_max_per_tx` is mandatory sealed configuration with no default.

**POL-12** **Fee cap**: with `total_in = Σ witness_utxo values` and `total_out = Σ output
values` in arithmetic that cannot overflow, `total_out > total_in` MUST be refused
`PSBT_INCONSISTENT` / `fee_cap`; otherwise `fee = total_in − total_out`, and `fee × 100 > 10 ×
total_in` MUST be refused `FEE_EXCEEDS_CAP`. Equality passes. The 10% is a fixed constant for
every class, not configuration, and it is a bug guard rather than a security control
(`ADR-0006`): the Hold and the PIN carry the burn defence for hot-class, and refresh has its own
bounds (`SPN-45`–`SPN-47`) precisely because it has neither.

## The verdict

**POL-13** A refusal MUST carry `{code, check, detail}`: the code from the closed set in
`API-13`, the check string from the table above, and a human-readable detail. The same codes,
with `check` prefixed `escape:`, are emitted when the request's Escape fails the same
evaluation (`SPN-27`), so the full alphabet of check strings includes an `escape:` twin of every
row.

**POL-14** Evaluation MUST NOT emit `WRONG_DESCRIPTOR` or `FRAUD_SUSPECTED`; the first is
declared for completeness and never produced, the second belongs to Lockdown (`DUR-7`).

## What evaluation deliberately does not check

**POL-15** These are structural boundaries an implementation MUST preserve, so that the pure
half stays pure and the stateful half stays where its state is:

- no clock, so no expiry, Hold, fire time, `EXPIRY_TOO_SHORT` or `COMMITMENT_EXPIRED`;
- no chain, so no prevout existence, confirmation depth, balance, double-spend or mempool;
- no signature cryptography, no coordinator authentication, no nonce;
- no PIN, no duress, no arming, no Lockdown, no propagation — the per-transaction Hot cap is
  pin-independent by design, which is what lets it fire at ingress without becoming a duress
  oracle;
- no node state: no replay log, no candidate registry, no velocity window, no refresh interval
  or feerate, no subordination, no capacity;
- no feerate, weight, size, dust, standardness, input or output count, `nVersion`, `nLockTime`,
  `nSequence` or ladder rule — those are `CHN-14`–`CHN-19` and `SPN-27`;
- no descriptor template or network-flavour check per request — those are startup checks.

## The Hot budget

The per-transaction cap above is one half. The other half needs node state and lives at
ingress, but the bound they enforce together is stated here because it is a policy property.

**POL-16** A node MUST meter every hot-class spend it ACCEPTS — pending or broadcast — against a
rolling window: the sum of `hot_outflow` over accepted hot spends whose reservation is live MUST
NOT exceed `hot_max_per_window`, or the spend is refused `HOT_VELOCITY_EXCEEDED` /
`hot_budget_velocity` before signing. The reservation ledger is bounded at 4 096 entries; a full
ledger refuses with the same code and a detail naming the capacity rather than the window.

**POL-17** The three parameters MUST be sealed in the manifest preimage (`MAN-2`) and validated
at load: `hot_window_secs ≥ max_commitment_age_secs`, so no candidate outlives the window that
meters it; both caps strictly positive, because a zero silently reduces the vault to
escape-and-refresh-only ("disable the hot wallet" is an empty allowlist, not a budget setting);
and `hot_max_per_tx ≤ hot_max_per_window`, equality meaning one maximal spend may consume the
whole window. The pinned hot allowlist, the escape descriptor and `max_derivation_index` are
sealed beside them because they decide what the sum counts.

**POL-18** A reservation is placed at acceptance, idempotently per commitment (a retry keeps the
original reservation time), and is released ONLY when the candidate reaches a terminal state
without ever having released its partial or broadcast — expired unbroadcast, or invalidated by a
conflicting confirmation while unexposed. A partial that has left the node is finalizable
authority in `t − 1` compromised hands and meters exactly as a broadcast does. Mempool eviction
and reorg are deliberately not tracked: over-counting refuses a later spend, netting could admit
a coerced one.

**POL-19** The window MUST age against a **monotonic** clock and the reservation MUST also be
held while the candidate's wall-clock expiry is live: `live ⇔ reserved_at ≥ now_mono −
window_secs ∨ wall_now ≤ expiry`, both boundaries inclusive. A forward wall step would
otherwise erase a whole window's reservations while their spends were still broadcastable; a
backward step would stretch a candidate past the monotonic window. The union can only
over-count.

**POL-20** The Hot budget provides an **acceptance-time admission bound**, not a rolling
completion-loss bound. Let `cap = hot_max_per_window` and `c < t` be the compromised signer
count. At any cut of the execution, let `now_i` be honest node `i`'s HotClock sample there and
its trailing interval `[now_i − hot_window_secs, now_i]`, both boundaries inclusive. Consider
the cohort of hot spends each of which at least `t − c` honest nodes accepted at a reservation
time inside that node's own interval, counting only reservations not refunded while unexposed
by the cut. Its admitted outflow is at most `((n − c) / (t − c)) × cap`: at the cut each honest
ledger still charges its counted reservations, each ledger holds at most `cap`, and every
counted spend charges at least `t − c` honest ledgers. The intervals are per node and no two
are ever compared: each node ages its ledger against its own HotClock (`POL-22`), and this set
states no bound on how far two HotClocks' rates may differ, so one interval of physical time
across the federation is not an object this bound has (`F61`). For the production shape
`n = 2t − 1`, the coefficient at `c = 0` is `(2 − 1/t)`, below `2 × cap` in outflow, and the
full `c = t − 1` tolerance admits at most `t × cap` for that cohort.

Acceptance, first partial release and completion can occur in different windows. This formula
MUST NOT be presented as a bound on funds completing or lost in an arbitrary rolling window,
and `cap ≤ tolerable per-window loss ÷ t` MUST NOT be offered as a sufficient loss-sizing rule.
No replacement rolling completion-loss formula is specified. Already exposed signatures also
remain valid after their reservations age out; detection and Recovery are still necessary.
The delayed-holder counterexample and the retained-accounting decision live in `ADR-0014`;
`CNF-58` exercises the distinction.

**POL-21** The ledger lives under the channel store lock beside the candidate registry
(`DOM-21`) so that a candidate's terminal removal and its release are one atomic step. The
duress freeze MUST NOT touch the ledger: a refund that happened only under duress would be the
timing signal `DUR-1` forbids; the frozen candidate's reservation is refunded at the expiry sweep
that collects it, strictly after Lockdown.

**POL-22** The monotonic clock of `POL-19` is the node's **HotClock**: elapsed seconds since the
channel was constructed, never wall time, pinnable only in tests. It is the same clock that fixes
Carrier deadlines (`NCH-33`).
