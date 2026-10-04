# 02 — On-chain contract

What the vault looks like on the chain, and the byte-exact rules every implementation must
reproduce: the descriptor template, the recovery timelock, the sighash rule, the commitment, and
the transaction-class predicate. Nothing here depends on a node's state; it is the part of the
system Bitcoin consensus enforces plus the pure derivations every party computes identically.

## The descriptor

**CHN-1** A vault's spending policy MUST be the following Miniscript descriptor, with the keys,
`t`, and the recovery timelock `RECOVERY_TIMELOCK` (`CHN-4`) substituted and nothing else
varied:

```
wsh(or_i(and_v(v:pk(USER),multi(t,NODE_0,…,NODE_{n−1})),and_v(v:older(RECOVERY_TIMELOCK),multi(2,REC_A,REC_B,REC_C))))
```

On a default vault `RECOVERY_TIMELOCK` renders as `4224679`, and every worked descriptor in this
set uses that value.

The string is written with no whitespace. `multi`, not `thresh` or `sortedmulti`, is the
threshold form; `or_i`, not `or_b` or `or_d`, is the branch combinator, because it places an
explicit `OP_IF`/`OP_ELSE` selector in the witness that the watchtower reads (`WTC-19`). The
descriptor is hand-written from this template at the ceremony; it is never compiled from a
policy language at runtime, and no implementation MAY accept a vault descriptor that a parser of
this template refuses.

**CHN-2** The Normal branch's threshold `t` and its node count `n` are consensus facts read out
of the descriptor's `multi(t, …)`, never out of configuration. A production vault MUST have
`t ≥ 2` and exactly `n = 2t − 1`, for two reasons that only together give the constraint: any two
subsets of size `t` intersect, so no unfrozen signing quorum exists outside an armed set
(`2t > n`), and `t` honest nodes remain after every `t − 1` withholding minority
(`n − (t − 1) ≥ t`). The permitted shapes are therefore 2-of-3, 3-of-5, 4-of-7, up to 8-of-15;
`n ≤ 15` is a conservative bound under `OP_CHECKMULTISIG`'s 20-key consensus limit, not a
standardness edge: every admitted shape sits far inside P2WSH standardness, with a `34 × n +
152`-byte witness script (`CHN-34`) against the 3 600-byte limit, `t + 4` stack items (`CHN-9`)
against 100, and 72-byte signature items against 80. The template parser MUST refuse `t < 2`, `n ≠ 2t − 1` and
`n > 15` each by name, so the shape is fatal at assemble, at finalize and at node load alike
(`CNF-79`): a parser that admits a shape the channel later rejects seals a vault no node can
serve.

**CHN-3** Every key in the vault descriptor MUST be **definite**: one compressed secp256k1 public
key, 33 bytes as 66 lowercase hex characters, with no origin, no extended key, no derivation
path and no wildcard. A key expression with any derivation path is refused, wildcard or not.
Every node parses the descriptor as a concrete descriptor at startup for the witness script and
the sighash, so a ranged vault descriptor is an unbootable vault. Destination wallets are the
opposite and stay ranged (`POL-4`).

**CHN-4** The recovery branch's timelock is a **per-vault** BIP68 time-based relative lock,
chosen at the ceremony. It lives in the descriptor, so it is hash-bound through `wallet_id`
(`MAN-2`) and carried in the manifest only as `MAN-5`'s convenience field `recovery_timelock`,
holding the raw `nSequence` value. On a default vault it MUST be `older(4224679)`, which is the
BIP68 time-based relative lock of `30375` units of 512 seconds with type-flag bit 22 set
(`30375 | (1 << 22)`), that is 180 days. Every worked figure in this set uses that default. The
parser MUST require bit 22 set — `older(30375)` would be a 30375-**block** height lock and MUST
be refused by name — and MUST refuse a value above the 65535-unit field. Equality between the
descriptor's `older` argument and the manifest's `recovery_timelock` is checked wherever a
manifest is in hand — at `finalize` (`MAN-31`) and at live-vault construction (`OPR-13`) — and
not at node load, where the descriptor is the only source (`MAN-7`). There is no hard floor;
the ceremony's controls on a short lock are `OPR-78`.

**CHN-5** The recovery branch MUST be exactly 2-of-3. The recovery keys MUST be distinct from
each other, from the user key, and from every node key; every key in the descriptor MUST be
globally distinct across all roles (a duplicate silently weakens the threshold).

**CHN-6** `wallet_id` MUST be the single SHA-256 of the canonical descriptor string as UTF-8
bytes. Its body is the exact `CHN-1` template with no whitespace, `t` and the `older` argument
each in decimal without leading zeroes, and the substituted lowercase definite keys in the
canonical node order; the recovery
slots keep their descriptor order. Append `#` and the eight-character checksum calculated from
that body by [BIP380](https://github.com/bitcoin/bips/blob/master/bip-0380.mediawiki#checksum).
Hash the complete checksummed string, with no newline. A library renderer is usable only if it
produces these bytes exactly; an equivalent script with another textual spelling is not a
canonical vault descriptor. The digest is 32 raw bytes in binary preimages and 64 lowercase hex
characters in JSON (`WIR-2`). It identifies the vault in every commitment and is the
never-transmitted domain separator of coordinator signatures and the first manifest-preimage
field (`WIR-21`, `MAN-2`).

**CHN-7** Canonical node order MUST be ascending lexicographic order over the full key-expression
string, which for definite keys is byte order on the compressed encoding. A node's `node_id` is
its zero-based position in that order, a `u16`. The mapping from `node_id` to descriptor key is
therefore a total bijection computed by every party from the descriptor alone; it is never a
separate table and never a human label.

**CHN-8** A template parser MUST refuse, in this order and each with a distinct error: a
descriptor that is not `wsh`; a `wsh` whose inner is not a raw miniscript; a top level that is
not `or_i`; a Normal branch that is not `and_v(v:pk(USER), multi(…))`; a recovery branch that is
not `and_v(v:older(…), multi(…))`; an `older` other than `4224679` on a default vault — in
general, one that is height-based or above the 65535-unit field (`CHN-4`); a recovery
`multi` other than 2-of-3; any key with a derivation path; any
duplicated key; a Normal branch shape outside `CHN-2`. All of these are fatal at the ceremony
and at node startup, never a runtime refusal.

## The witness

**CHN-9** The witness of a Normal-path spend carries, in order, the `CHECKMULTISIG` dummy, `t`
federation signatures in descriptor order, the user signature, the branch selector, and the
witness script. The selector is the second-to-last element: a single `0x01` byte for the Normal
(`OP_IF`) branch, an **empty** push for the Recovery (`OP_ELSE`) branch. Both branches share one
scriptPubKey, so the selector is the only on-chain evidence of which branch was taken.

**CHN-10** A Recovery-path spend on a default vault MUST set every input's `nSequence` to
`4224679` exactly, and in general to the sealed `recovery_timelock`. `0xffffffff`
disables relative locks and does not satisfy the recovery branch. A Recovery-path transaction
carries no user signature and no federation signature.

## Signatures

**CHN-11** Every user signature and every federation partial signature MUST be ECDSA over the
BIP143 P2WSH sighash computed with `SIGHASH_ALL`, over the **whole two-branch witness script**
(the descriptor's explicit script), with the input's `witness_utxo` value. There is no
`SIGHASH_DEFAULT`: this is P2WSH, not Taproot.

**CHN-12** A node MUST verify the user's partial signature cryptographically against its own
recomputed sighash on every input before it evaluates policy (`SPN-26`). The presence of a
`partial_sigs` entry is not enough. A signature with any sighash type other than `SIGHASH_ALL`
is refused `BAD_SIGHASH`; a missing or non-verifying one is refused `USER_SIG_INVALID`. Because
the user signs first under `SIGHASH_ALL`, any later mutation of any output, input, `nVersion`,
`nLockTime` or `nSequence` invalidates the very signature the node verifies; there is no separate
"no mutation after authorization" check.

**CHN-13** Signature encoding and low-S acceptance are owned by `WIR-6`; a node MUST tolerate
valid DER length variance within that profile. PSBT signatures append their sighash byte to
the DER encoding; channel `partial_sig` carries DER alone, with its sighash type in the separate
payload field (`NCH-23`).

## The escape transaction shape

**CHN-14** An Escape MUST spend only vault outputs and MUST pay every destination output to the
escape descriptor (`CHN-30`). It MUST have `nLockTime = 0`.

**CHN-15** Every Escape MUST set every input's `nSequence` to `0xfffffffd`, on the base and
on every rung, with or without a fee ladder. This signals BIP125 replaceability while keeping
bit 31 set so BIP68 relative locks stay disabled. Signalling permits replacement; it does not
prevent relay or confirmation. The sequence decision and its full-RBF rationale are recorded
in `ADR-0016`.

**CHN-16** A fee ladder MUST have at most **3** rungs above the base. Each rung MUST have the
same `nVersion` as the base, `nLockTime = 0`, the same ordered input set, the same ordered output
script set, every output value at or below the value of the same output on the rung below, a
strictly greater total fee, and a fee increase of at least `maximum_finalized_vsize × 1 sat/vB`
over the rung below, with the maximum finalized vsize owned by `CHN-34`. Every rung is separately
user-signed over its own exact bytes.

**CHN-17** The honest composer's ladder, when the sealed ceiling admits one, MUST derive rungs
from the base at fee multipliers `4×`, `16×`, `64×`, funding each from the largest output (ties
to the lowest index), dropping any rung whose total fee exceeds `escape_bump_max_fee_pct` of
the total input value, whose funded output would fall below 10 000 satoshis, or whose increase
over the last kept rung is below `CHN-16`'s minimum. The base Escape is exempt from the
ceiling; only rungs are checked against it, so a ceiling of `0` admits no rung that pays any
fee. A vault sealed with a zero ceiling composes no rungs (`MAN-13`); a valid non-zero ceiling
that yields an empty ladder is a supported outcome (`OPR-40`).

## The unsigned transaction shape the composer produces

**CHN-18** A composed spend, Escape, or refresh MUST be transaction version 2 with
`nLockTime = 0`, every input's `scriptSig` and witness empty, and inputs in canonical outpoint
order (sorted by txid then vout, no duplicates). A hot spend pays the exact requested amount to
the destination plus one mandatory vault-change output; its Escape pays one output to the escape
descriptor at derivation index 0 of the first canonical branch. That single change output
consolidates the vault to one coin, which a claw-back sweeps as readily as many (`CHN-35`);
whether a reserve topology is still wanted is `F1`. A refresh sets every input's
`nSequence` to `0xfffffffd`, signalling BIP125 so that a higher-fee replacement of it can enter
the mempool (`WTC-25`); it has no ladder.

**CHN-19** Every output of a composed transaction MUST be at or above the dust threshold for its
own script type as Bitcoin Core's default dust policy computes it (`minimal_non_dust`).
Equality passes. A composer MUST NOT absorb value into the fee to make a shape fit.

**CHN-20** The composer's fee for the spend is `rate × maximum_finalized_vsize` (`CHN-34`) with
the rate from `WTC-16`; the Escape's fee is `max(rate, escape_feerate_floor) × its own maximum
finalized vsize`. The maximum MUST be recomputed from each actual unsigned shape and the sealed descriptor;
a fee estimate for a different input/output shape MUST be refused. After signing, the exact
finalized vsize MUST NOT exceed that maximum, but a smaller size is valid: strict-DER ECDSA
signatures vary in length. The composed absolute fee stays unchanged. Post-finalization fee checks use the exact
finalized vsize.

**CHN-21** A composed Escape MUST satisfy `sweep × 100 ≥ total_in × escape_coverage_pct` in
arithmetic that cannot overflow, with equality passing. A sealed coverage of 100 therefore
refuses any Escape that pays any fee, which is why `MAN-9` forbids that combination with a
positive feerate floor.

**CHN-22** Every input of every PSBT a user signs MUST carry its **full previous transaction**
(`non_witness_utxo`) which hashes to the input's txid with an in-bounds vout, an explicit
`sighash_type` of `SIGHASH_ALL`, and a mandatory `witness_utxo` whose script and value agree exactly
with the selected parent output. The signer MUST refuse a PSBT with a `scriptSig`, a witness, a duplicate
outpoint, a `witness_script` other than the sealed one, or an input whose `witness_utxo` script
is not the vault's.

**CHN-23** A user signer MUST validate a request's complete transaction group and build every
sighash before signing any, and MUST return no partially signed group on any error path.
A SpendRequest group consists of a `(hot, escape)` pair over the same non-empty coin set,
together with every supplied Escape ladder rung. The pair and ladder must pass their respective
shape rules (`CHN-14`–`CHN-16`). A RefreshRequest group consists of its single refresh-class
transaction (`CHN-31`), and a ClawbackRequest group of its single escape-class transaction
(`CHN-35`). Anything else is refused before signing; a failure in any rung refuses the whole
group.

## The commitment

**CHN-24** A **commitment** is the exact-transaction binding a node evaluates, signs, records and
keys its replay log by. It MUST bind: `wallet_id`; the unsigned transaction's `nVersion` and
`nLockTime`; every input's txid, vout and `nSequence` in transaction order; every output's
scriptPubKey and amount in transaction order; the absolute fee (Σ `witness_utxo` values − Σ
outputs, saturating); the coordinator-proposed `expiry`; and the node's own `policy_version`
(never the request's). Two distinct transactions MUST never share a commitment, and the
guarantee has two halves: `CHN-25`'s encoding is injective over the fields it binds, a theorem
(`BtcPolicy.Encode.encode_injective`); and two encodings have two `commitment_id`s under the
**assumption** that `CHN-26`'s SHA-256 is collision-free on the admitted domain — named, not
proved, as `ADR-0023` has it.

**CHN-25** The commitment's canonical encoding MUST be, with every integer **big-endian**:

```
wallet_id                      32 bytes raw
version                         4 bytes, i32 two's complement
lock_time                       4 bytes, u32
input count                     4 bytes, u32
  per input:  txid              32 bytes raw, INTERNAL byte order (not display order)
              vout               4 bytes, u32
              sequence           4 bytes, u32
output count                    4 bytes, u32
  per output: script length      4 bytes, u32
              script            that many bytes
              amount             8 bytes, u64
fee                             8 bytes, u64
expiry                          8 bytes, u64
policy_version                  4 bytes, u32
```

This is the ONE big-endian encoding in the system. Every tagged-hash preimage in
`08-wire-contract.md` is little-endian; do not carry either convention into the other.

**CHN-26** `commitment_id` MUST be the single, untagged SHA-256 of `CHN-25`'s bytes, rendered as
64 lowercase hex characters in forward byte order. It is what `Accepted` returns (`API-12`),
what `/pending` lists (`API-21`), and what every partial-signature message names (`NCH-30`).

**CHN-27** The replay log uses the commitment as its primary lookup, never the outpoint set;
the complete acceptance and refusal matching keys are owned by `SPN-23`. A changed transaction
or expiry gets a fresh commitment and evaluation. An identical retry follows those matching
rules; rebroadcasting identical transaction bytes does not itself change the commitment.

## The vault identity in other preimages

**CHN-28** `wallet_id` MUST be prepended, un-transmitted, to the coordinator-request preimage
(`WIR-21`), and MUST appear as the first field of the manifest (`MAN-2`), the endorsement
(`MAN-6`) and the channel envelope (`NCH-11`) preimages. A signature or hash valid at one vault
MUST NOT verify at another that reuses the same key.

## The user-signature hash

**CHN-29** Each candidate variant carries `user_sig_hash`, the tagged hash
`btc-policy/user-sig-hash/v0` over the transaction's inputs in input order. `WIR-23` owns the
bytes and states: "for each input in order, `var(DER user signature)` followed by `u8(sighash
type)` — `0x01` for `SIGHASH_ALL` — concatenated". The per-input sighash byte is part of the
preimage; a length-prefixed DER signature alone is not. A partial signature message carries the
hash as its `user_sig_hash` member (`NCH-23`) so a peer's partial cannot be applied to a variant
the user signed differently.

## Transaction classes

**CHN-30** Every spend MUST be classified by each node from the spend's own outputs; no
coordinator label, envelope hint, or peer assertion carries authority. Vault-change outputs — any
output whose script derives from the vault descriptor within the derivation bound (`POL-5`) —
are permitted in every class and EXCLUDED from the decision. Of the remaining destination
outputs:

- **escape-class** iff every destination output derives from the escape descriptor;
- **hot-class** iff every destination output derives from a hot-allowlist descriptor;
- **refresh-class** iff there are no destination outputs at all;
- a spend with destination outputs in both the escape and the hot set, or with any output that
  derives from nothing, has no class and MUST be refused `PSBT_INCONSISTENT` with check
  `transaction_class` (`POL-10`).

In EVERY class, the number of outputs that derive from the vault descriptor MUST NOT exceed the
number of inputs, refused `PSBT_INCONSISTENT` / `transaction_class`. `SPN-46` bounds refresh burn
per coin per interval, and any transaction that mints vault coins — a refresh fanning one coin
into many, or a hot or escape spend carrying many change outputs — hands the attacker the coin
count that bound is multiplied by. The count is over vault-derived outputs only, so a hot spend
with its destination plus one change output is unaffected. It is a classification input, not one
of the evaluation inputs `POL-15` excludes.

The escape test MUST run before the hot test for each output: the escape descriptor is itself an
allowlist entry, so testing allowlist membership first would read every escape output as hot.

**CHN-31** Class drives behaviour, so misclassification is a duress bypass and not a cosmetic
error: hot-class is signed at ingress, held, frozen under duress and combined at Hold expiry;
escape-class arrives only as a SpendRequest's Escape, fired at `T` under duress, or as a
pin-less ClawbackRequest, fired at ingress (`SPN-50`); refresh-class may only arrive as a
RefreshRequest. The mixed case exists to close the 99%-to-hot plus dust-to-escape spend that a
"has an escape output ⇒ escape-class" rule would let skip the Hold and the freeze. What that
bypass would defeat is the class-gated half of the safety track; the per-transaction Hot cap
(`POL-11`) and arming plus Lockdown (`DUR-3`) take no class and survive it.

**CHN-32** A SpendRequest whose spend is any class other than hot MUST be refused
`PSBT_INCONSISTENT` / `transaction_class`: a refresh arrives only as the pin-less RefreshRequest
(`SPN-43`) and a deliberate sweep only as the pin-less ClawbackRequest (`SPN-50`). A
RefreshRequest whose transaction is any class other than refresh, and a ClawbackRequest whose
transaction is any class other than escape, MUST be refused the same way. A request's Escape
that classifies as anything other than escape-class MUST be refused with check
`escape:transaction_class`.

## The claw-back

**CHN-35** A **claw-back** is one escape-class transaction (`CHN-30`) over any non-empty set of
vault coins — no minimum count, no relation to any other transaction — paying EVERY output to
the escape descriptor, with no vault-derived output and no ladder. The no-change rule is what
makes its fee bound one-shot: with vault change permitted, an attacker holding the user key
and the coordinator credential could pay a little to the escape wallet, burn `POL-12`'s ten
percent, return the rest as change, wait a block and repeat until the vault was fees; with
every output leaving, each coin can be swept once. A claw-back carrying a vault-derived output
is refused `PSBT_INCONSISTENT` / `transaction_class`. Every input's `nSequence` MUST be
`0xfffffffd`, refused the same way otherwise, so that a higher-fee claw-back over the same
coins can replace it in the mempool (`WTC-25`). `nLockTime` MUST be `0`. Its fee is
bounded by `POL-12` and by nothing tighter: an emergency sweep may need to outbid a thief
(`ADR-0022`). An unconfirmed prevout is tolerated at ingress as on a spend (`SPN-25`) and
admitted at fire time only as a vault-authorized resident parent (`WTC-24`); the composer's
confirmed-only inventory is `OPR-68`'s rule, not the node's. A one-coin vault claws back its
one coin.

## The maximum finalized vsize

**CHN-34** The **maximum finalized vsize** of an unsigned vault transaction MUST be

```
maximum_finalized_vsize = ⌊(4 × B + 2 + input_count × W_N + 3) / 4⌋
```

computed in arithmetic that cannot overflow, where:

- `B` is the byte length of the transaction's **legacy** serialization — no segwit marker, no
  flag, no per-input witness stack-count, with every `scriptSig` empty and its length prefix
  present — and `weight = 4 × B`. `CHN-18` requires the composed transaction to carry no
  witness, so the segwit framing it would occupy is restored by this rule's own `+ 2` and
  per-input `+ 1` terms; serializing the empty witness as well double-counts both.
- `input_count` is the transaction's nonzero input count.
- `W_N` is the maximum serialized weight of one Normal-path input's witness **including** its
  witness stack-count prefix:

```
W_N = 73 × t + 34 × n + 232        weight units
```

  which for the production shape `n = 2t − 1` (`CHN-2`) is `141 × t + 198`.

`W_N` is fixed by `CHN-1`'s template and nothing else. Its terms: the witness script is
`34 × n + 152` bytes — invariant across every sealed `recovery_timelock`, since bit 22 set keeps
the `older` push at three bytes (`CHN-4`) — (254 at 3-of-5's smallest sibling 2-of-3, so its CompactSize length prefix
is already three bytes at every production shape); the stack is the `t + 4` elements of `CHN-9`;
each signature stack item costs 73 bytes, being a one-byte push prefix over a **72**-byte item
that is at most 71 bytes of strict-DER ECDSA plus one `SIGHASH_ALL` byte. `S` occupies at most 32
DER integer bytes **including any sign-padding byte**: `WIR-6`'s low-S rule caps `S` at
`⌊q / 2⌋`, whose leading byte is `0x7f`, so a 32-byte `S` never needs padding, and a shorter `S`
that does need one — `0x80` encodes as `00 80` — is nowhere near the ceiling. `R` carries no such
cap and does reach 33 bytes. So `2 + (2 + 33) + (2 + 32) = 71` is the DER ceiling; `WIR-16`'s
"DER signature | at most 72 bytes" is a transport bound that includes no sighash byte and MUST
NOT be used as the DER length here.

**A library's satisfaction-weight accessor is not this value and MUST NOT be substituted by
name.** `rust-miniscript`'s current `max_weight_to_satisfy()` returns `W_N − 1`, excluding the
stack-count prefix; its deprecated `max_satisfaction_weight()` returns `W_N + 4`, additionally
counting the empty `scriptSig` and its length prefix. An implementation that reads either
accessor MUST verify which one it has against the fixture rather than against its name.

An earlier revision wrote the same quantity as
`⌊(weight + 2 + (max_satisfaction_weight + 1) × input_count + 3) / 4⌋`. That form is arithmetically
identical to the one above, but only when `max_satisfaction_weight` means `W_N − 1`; it is not
reproduced as normative here because the identifier names the deprecated accessor, which returns
a value five weight units larger.

The executable fixture is `WIR-36`, which measures the script and a maximum-length witness from
serialized bytes rather than restating this formula.
