# 09 — Manifest, configuration, and the ceremony

The immutable per-vault manifest and the preimage that seals it, the per-node configuration
schema and its load-time validation, node key derivation and PIN enrolment, and the setup
ceremony that produces all of it. The ceremony is the trust bootstrap: every state machine in
this set defends a vault whose shape the ceremony decided, and no state machine can compensate
for a setup that saw every signer secret.

## The manifest

**MAN-1** Every vault MUST have one **manifest**: the immutable record, written once at the
ceremony, hash-pinned, distributed to every node and backed up beside the descriptor, that pins
the canonical descriptor, the coordinator auth public key, every node's signing and channel
public keys with their endorsements and transport endpoints, and every federation-uniform
policy value. Any change to it is a new vault. The manifest is the root of both channel trust
and coordinator trust.

**MAN-2** The **manifest preimage** MUST be, with `WIR-18`'s little-endian encoder, exactly:

```
wallet_id                        32 bytes raw                      (CHN-6)
protocol_version                 u32                               = 4 (MAN-3)
coordinator_auth_pubkey          33 bytes raw, compressed
max_msg_bytes                    u64
hot_max_per_tx                   u64  sat
hot_max_per_window               u64  sat
hot_window_secs                  u64
hot_allowlist                    u32 count, then each descriptor as var
                                 — the node's allowlist MINUS the escape descriptor,
                                   each rendered by MAN-39, sorted, deduplicated
escape_descriptor                var, rendered by MAN-39
max_derivation_index             u32
escape_feerate_floor             u64
escape_coverage_pct              u8
escape_bump_max_fee_pct          u8
network                          u8   1 = bitcoin, 2 = the default public signet, 3 = regtest
policy_version                   u32
refresh_min_interval_secs        u64
refresh_max_feerate              u64  sat/vB
nodes                            u32 count, then per node in node_id order:
    node_id                      u16
    signing_pubkey               33 bytes raw
    channel_pubkey               33 bytes raw
    endpoints                    u32 count, then each as var (UTF-8)
```

`manifest_hash` is the tagged hash `btc-policy/manifest/v0` over these bytes (`WIR-27`
publishes the vector). Not serialised separately, because `wallet_id` binds them transitively:
the descriptor, `t`, `n`, the recovery timelock. Hashing the full allowlist, or the
un-canonicalised descriptor strings, produces a different hash and `WRONG_MANIFEST` at startup.

`policy_version` is in the preimage because `CHN-24` binds "the node's own `policy_version`
(never the request's)" into every commitment, which makes it a value the federation must agree on
byte-for-byte: two nodes configured differently compute different `commitment_id`s for identical
transaction bytes, each answers `Accepted`, and each one's partials then name a candidate the
other cannot find (`NCH-24` `UNKNOWN_CANDIDATE`, which `NCH-26` makes retriable until the sending
message's deadline lapses under `NCH-8`). Quorum forms only inside a group that happens to share a
value AND to reach `t`; across the divergence nothing completes. Arming is unaffected — not
because the Carrier identity is uniform, since `NCH-31` derives it through a memory-hard stretch
salted per boot and it is therefore node-local, but because a peer's relay is matched to a Carrier
by the coordinator nonce its memo is keyed on (`NCH-32`). So Lockdown still lands at `T` and the
failure is denial rather than theft — but it is silent and undetectable at runtime. Sealing it
makes the divergence a startup `WRONG_MANIFEST` instead.

The two **refresh bounds** are here for a different reason: not because divergence breaks
agreement — it does not, and `SPN-43` classes `REFRESH_TOO_SOON` as federation-uniform since
`ADR-0019` because the age it reads is chain state, not because the number is sealed — but
because they are shared security policy. `ADR-0006`'s correction states that the
refresh class is "pin-less AND has no Hold — so neither guard applies to it. The refresh class
therefore needs its own bounds: a **minimum refresh interval** and a **tight refresh-specific fee
cap**". They replace two missing guards, and every other burn bound in the set is already sealed
(`POL-17`, `MAN-13`). Unsealed they were not adjustable either — `OPS-1` states "Once a vault is
sealed, nothing an Operator can do reconfigures it", and `MAN-36` starts a node exactly once — so
leaving them out bought no tunability and only made the effective ceiling unreadable: a refresh
needs `t` signatures, so the operative cap was whichever value the `t`-th most permissive node
held, and under the per-node refresh log that `ADR-0019` has since withdrawn a coordinator
retrying downward could burn each node's acceptance latch without ever reaching `t`. Sealing the
number and reading the age from the chain are two separate decisions; the bound holds only with
both.

**MAN-3** `protocol_version` is the **manifest schema revision**, currently `4`. Each revision
appends to `MAN-2`'s preimage: revision `2` the `network` byte, revision `3` `policy_version`,
revision `4` the two refresh bounds. It is inside the preimage, so a revision bump is a new
manifest and a new vault; the domain tags of `WIR-20` stay `/v0` because they separate domains,
not revisions. A node MUST refuse at startup a config whose `protocol_version` is not the one it
implements, as a version error before any other schema check, and MUST send and require `4` in
every channel envelope (`NCH-18`).

**No vault was ever sealed at revision 1, 2 or 3.** Every one of them existed only inside this
specification's own history, so an implementation MUST refuse them outright rather than carry
encoders for them. `OPS-31` obliges a newer coordinator to keep operating a vault sealed under an
older revision; that obligation begins at revision 4, and stating so here is what stops a
reimplementer inferring a compatibility burden from `OPS-31` that no vault can ever call in.

**MAN-4** Every node's **endpoints** are pinned in the manifest and endorsed by that node, so
nobody — a compromised coordinator, a later config writer — can repoint one node's view of a
peer. In this release every endpoint MUST be `127.0.0.1:<port>` with a nonzero port, no two
nodes may pin the same port, and a node's bind port is its own first endpoint's. That is the
rollout stage-1 form; the routable authenticated form of `OPS-51` replaces the loopback rule
rather than coexisting with it, clearnet dynamic-IP topologies are unsupported by design, and
the mechanism is `F37`.

**MAN-5** The manifest is published as `manifest.json` (`MAN-33`) with its fields ordered so
that the file alone suffices to recompute `manifest_hash`. It carries `t`, `n` and
`recovery_timelock` as convenience fields read out of the descriptor, and each node's
`channel_endorsement`, which authenticates the manifest without appearing in its preimage
(`MAN-6`); every other field it carries is hash-bound.

**MAN-6** Each node's **channel endorsement** MUST be a strict-DER ECDSA signature by that node's
Bitcoin signing key over the tagged hash `btc-policy/channel-endorsement/v0` of:

```
wallet_id 32 raw ‖ manifest_hash 32 raw ‖ node_id u16 ‖ channel_pubkey 33 raw
‖ protocol_version u32 ‖ endpoints (u32 count, then each var)
```

It is produced in the ceremony's second round (`MAN-30`) because `manifest_hash` is not known
until every node's public key is in, and the only way to collapse the two rounds is to hand the
coordinator the node secrets. Every node verifies every member's endorsement at startup
(`MAN-11`); the wire never carries one.

## Node configuration

**MAN-7** A node's configuration is one TOML file, parsed with **unknown top-level keys refused**
as a fatal error. The top level:

| key | type | required | default | sealed in `MAN-2` |
|---|---|---|---|---|
| `listen_port` | u16 | yes | | no |
| `node_key_salt` | hex string, 16 bytes | yes | | no |
| `node_key_ops` | u32 | yes | | no |
| `node_key_mem_kib` | u32 | yes | | no |
| `descriptor` | string | yes | | via `wallet_id` |
| `allowlist` | array of string | yes | | minus escape |
| `escape_descriptor` | string | yes | | yes |
| `max_derivation_index` | u32 | yes | | yes |
| `hold_secs` | u64 | yes | | no |
| `hot_max_per_tx` | u64 | yes | | yes |
| `hot_max_per_window` | u64 | yes | | yes |
| `hot_window_secs` | u64 | yes | | yes |
| `combine_slack_secs` | u64 | no | 60 | no |
| `max_commitment_age_secs` | u64 | yes | | no |
| `refresh_min_interval_secs` | u64 | no | 2 592 000 | yes |
| `refresh_max_feerate` | u64 sat/vB | no | 100 | yes |
| `duress_delay_secs` | u64 | no | 0 | no |
| `epsilon_secs` | u64 | no | 60 | no |
| `delivery_horizon_secs` | u64 | no | 60 | no |
| `escape_coverage_pct` | u8 | no | 95 | yes |
| `escape_feerate_floor` | u64 sat/vB | no | 1 | yes |
| `protocol_version` | u32 | yes | | yes |
| `escape_bump_max_fee_pct` | u8 | yes | | yes |
| `network` | `"bitcoin"` / `"signet"` / `"regtest"` | yes | | yes |
| `policy_version` | u32 | yes | | yes |
| `pin_normal_hash` | Argon2id PHC string | yes | | no |
| `pin_duress_hash` | Argon2id PHC string | yes | | no |
| `pin_attempt_budget` | table | no | `MAN-23` | no |
| `coordinator_auth_pubkey` | 66-hex compressed pubkey | yes | | yes |
| `chain_backend` | table | required with `[channel]` | | no |
| `channel` | table | required to serve | | partly |

There is no fee-cap field (`POL-12` is a constant) and no `duress_response` toggle (duress is
one mandatory mechanism). `escape_bump_max_fee_pct` has no default so an omitted field is
reported as such rather than as an opaque manifest mismatch. `duress_delay_secs` defaults to 0,
which fires at the earliest `T`. `refresh_min_interval_secs` and `refresh_max_feerate` are
sealed (`MAN-2`, `ADR-0018`) and ceremony-written (`MAN-35`); `pin_attempt_budget` is
node-enforced, ceremony-written (`MAN-35`) and node-local by decision (`ADR-0018`).

`policy_version` is sealed in `MAN-2`'s preimage, which owns why. A node whose configured value
differs from the federation's fails the `MAN-11` hash check at startup rather than serving and
silently agreeing on nothing.

**MAN-8** `[chain_backend]` has `rpc_addr` (a `host:port` socket address) and `auth` (base64 of
`user:password` for HTTP Basic), both mandatory when present. `[channel]` has:

| key | type | required | default |
|---|---|---|---|
| `node_id` | u16 | yes | |
| `nodes` | array of `[[channel.nodes]]` | yes; all `n` members including self | |
| `expected_manifest_hash` | 64-hex | yes | |
| `max_msg_bytes` | usize | no | 1 048 576 (sealed) |
| `max_active_candidates` | usize | no | 1 024 |
| `max_candidate_store_bytes` | usize | no | 67 108 864 |
| `per_peer_quota_per_min` | u64 | no | 600 |
| `max_concurrent_channel_requests` | usize | no | 64 |
| `max_response_bytes` | usize | no | 65 536 |
| `per_send_deadline_secs` | u64 | no | 5; must be nonzero |

Each `[[channel.nodes]]` entry has `node_id`, `signing_pubkey`, `channel_pubkey`,
`channel_endorsement` (hex DER) and `endpoints` (non-empty array), all mandatory.

**MAN-9** Load-time validation MUST refuse, each with a distinct fatal error, at least:
`node_key_ops < 1`; `node_key_mem_kib < 8`; a coordinator pubkey that is not 66 hex characters
or does not parse; a descriptor that does not parse or fails `CHN-8`; `hold_secs ≥
max_commitment_age_secs`; `hot_window_secs < max_commitment_age_secs`; either hot cap zero;
`hot_max_per_tx > hot_max_per_window`; `combine_slack_secs < 20` (twice the vault cache refresh
interval); `refresh_min_interval_secs = 0`; `refresh_max_feerate = 0`, which would refuse every
refresh of even one satoshi and so silently strand the vault toward its recovery timelock; `epsilon_secs > max_commitment_age_secs`;
`duress_delay_secs > max_commitment_age_secs`; with `[channel]`: `delivery_horizon_secs = 0` or
`≥ max_commitment_age_secs`; `escape_coverage_pct` outside `51..=100` — at fifty or below two
input-disjoint Escapes could each pass `DUR-24` and both confirm, and `ADR-0020`'s guarantee that
at most one of a node's selected Escapes sweeps rests on any two admissible Escapes sharing a
coin, which the bound implies only because `DUR-22`'s denominator is never smaller than the
combined inputs of the Escapes the node had selected when it first released;
`escape_coverage_pct = 100`
with a positive `escape_feerate_floor`; `hold_secs + combine_slack_secs >
max_commitment_age_secs`; an escape descriptor absent from the allowlist; a network flavour
mismatch (`POL-8`); invalid PIN digests (`MAN-21`); an invalid attempt budget (`MAN-23`); with
`[channel]`: `t < 2`, `n ≠ 2t − 1`, or no `[chain_backend]`.

**MAN-10** Role collision MUST be refused at load, comparing curve points: the coordinator auth
key equal to the user key, to any node key, or to this node's derived channel key.

**MAN-11** With `[channel]` the node MUST additionally verify at startup, in order: the
concurrency bound is representable; `per_send_deadline_secs ≠ 0`; `listen_port ≠ 0`; the node
count equals the descriptor's; canonical node order and ids form a bijection with no gaps or
duplicates (`CHN-7`); every `signing_pubkey` equals the canonical key at its id; every
`channel_pubkey` parses and differs from the coordinator key; every endpoint is a canonical
`host:port` whose round-trip rendering is byte-identical; this node's id is in range and its
signing key is its own; the recomputed `manifest_hash` equals `expected_manifest_hash`; every
member's endorsement verifies (`MAN-6`); this node's locally derived channel key equals the
manifest's for its id; and its own endpoints include `127.0.0.1:<listen_port>`. Any failure is
fatal before any socket is bound.

**MAN-12** `max_msg_bytes` is the one `[channel]` value in the preimage. A node whose value
differs from the sealed one fails the hash check; every other `[channel]` value is per node.

**MAN-13** `escape_bump_max_fee_pct` is sealed and bounded at the ceremony — it MUST NOT exceed
the 10% fee cap, the coverage headroom `100 − escape_coverage_pct`, or one fifth of that headroom
— and nodes never enforce it: the ceremony bounds it and the user signer checks composed ladders
against it (`CHN-17`). A ceremony MUST NOT seal a non-zero ceiling for a vault whose operator
program cannot compose the rungs it promises (`OPR-40`), because a sealed host cannot be
upgraded to one; the ceiling and the timelock are asked as one question (`OPR-79`).

**MAN-14** `network` is sealed. It selects address encodings and identifies the backend chain
(`WTC-3`); it changes no key derivation and no scriptPubKey. Exactly `bitcoin`, `signet` (the
default public signet) and `regtest` are accepted; testnet3, testnet4, aliases and custom
signets are refused with the allowed set named.

## Keys on the node

**MAN-15** A node holds no signing key at rest. Its configuration carries only the PUBLIC
derivation parameters; the key is derived in RAM at startup from an **operator preimage**
read once on standard input and never stored.

**MAN-16** The preimage MUST be a 63-bit-wide value whose top bit is pinned — 62 bits of entropy,
a 2⁶² search space — presented as exactly 16 hex characters (8 bytes). Reading it MUST suppress
terminal echo when standard input is a terminal, MUST read one byte at a time into a
pre-reserved zeroizing buffer capped at 64 bytes, and MUST NOT prompt again or retry. A lost
preimage is a dead node, which reboot-death already makes routine; that is why the preimage
takes the widest form rather than a brute-force-recoverable one.

**MAN-17** The signing key MUST be derived with Argon2id version `0x13` (decimal 19), using
the decoded 8-byte preimage as password, the decoded 16-byte configured salt, `t = node_key_ops`
passes, `m = node_key_mem_kib` KiB, parallelism `p = 1`, and output length 32 bytes. The optional
secret and associated-data inputs are empty. These are the inputs of
[RFC 9106 §3](https://www.rfc-editor.org/rfc/rfc9106.html#section-3); no PHC encoding, hex text,
terminating NUL, extra hash or domain prefix enters this invocation. The output is interpreted
as an unsigned big-endian scalar, which MUST lie in `[1, q − 1]`, where
`q = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141` is the secp256k1 group
order. An invalid scalar is a fatal derivation error requiring a new node ceremony; it MUST NOT
be reduced modulo `q`, clamped, hashed again or silently retried. The signing public key is
the compressed SEC encoding of that scalar times the secp256k1 generator. The ceremony default
and the production floor are 4 passes and 262 144 KiB; a node
keygen below the floor MUST be refused unless an explicit weak-KDF flag is given, and the
ceremony records every node's cost in its evidence. The 2⁶² space is the primary barrier; the
KDF cost is defence in depth and a required floor, not a free knob.

**MAN-18** A node MUST refuse to start if its derived public key is not one of the descriptor's
federation node keys: a node holding a key no descriptor names would validate and "sign" every
request while producing partials that can never combine.

**MAN-19** The channel key is `NCH-4`, derived from the signing key, and the node's channel
public key MUST equal the manifest's entry for its id.

## PINs

**MAN-20** Two PINs are enrolled per vault as Argon2id **PHC strings**
(`$argon2id$v=19$m=…,t=…,p=…$<salt>$<hash>`), one normal and one duress, each with its own
salt. Enrolment is a separate step from the ceremony; the PINs themselves never reach any
artifact. The two MUST be deliberately distinct — never typo-neighbours — because a false
duress trigger costs a full Recovery ceremony (`ADR-0005`).

**MAN-21** Load-time validation of each digest MUST refuse: a string that is not PHC; an
algorithm other than Argon2id; an unsupported Argon2 version; `m > 262 144` KiB, `t > 10`, or
`p > 16`; a missing hash output; a salt shorter than 8 bytes; and **equal salts across the two
slots** — a shared salt would let one Argon2 evaluation answer both digests and weaken the
constant-cost compare.

**MAN-22** The Carrier KDF (`NCH-31`) MUST use the stronger of the two slots' Argon2 versions, the
element-wise maximum of their `m`, `t` and `p`, a 32-byte output, and one 32-byte random salt
drawn at process start; it MUST share one node-wide work slot with PIN evaluation so that at most
one Argon2 memory matrix exists at a time.

**MAN-23** The **PIN attempt budget** is `[pin_attempt_budget]` with `max_attempts` (default 5,
range 1..=1 024), `window_secs` (default 3 600, ≥ 1), `backoff_schedule` (default `[0]`,
non-empty), and `lockout_secs` (default 900, ≥ 1). It is RAM-only, node-lifetime, and lives under
the sign lock so check-and-charge is atomic. Charging MUST be: first clear an expired lockout;
slide the window by dropping failures older than `window_secs`; then, for a WRONG verdict only
while not locked, record the failure, apply the backoff indexed by the pre-failure count and
clamped to the schedule's last entry, and if the failure count reaches `max_attempts` set
`locked_until = now + backoff + lockout_secs`. Every branch performs the same-shaped writes with
constant-time selection so a normal and a duress PIN take an identical path. A correct PIN does
not reset the count; a wrong PIN while locked does not extend the lockout. Lockout produces
denial only (`SPN-18`), never an unfrozen signing quorum, and a valid duress PIN still records
its intent while locked out (`DUR-4`).

## The ceremony

**MAN-24** The ceremony proceeds through the following steps, in two rounds:

| step | machine | command |
|---|---|---|
| 1 | each node host | `node-keygen` |
| 2 | each escape-key device, and the user and recovery devices | `keygen --role escape` for single-sig or operator-supplied escape bundle (`MAN-26`); `keygen --role user\|recovery` |
| 3 | the coordinator | `assemble` |
| 4 | each node host | `node-endorse` |
| 5 | the coordinator | `finalize` |

The device rules are `DOM-13`: "No machine MAY ever hold two federation node secrets", and
`DOM-11`: "Each escape key MUST be generated independently on a device that holds no other
vault role."

**MAN-25** `node-keygen` MUST birth the node's key on the node's own host: generate the
preimage and salt, derive the signing and channel keys, and publish ONLY public bytes as
`node-public.json` — `signing_pubkey`, `channel_pubkey`, `node_key_salt`, `node_key_ops`,
`node_key_mem_kib`, `endpoints`. The preimage MUST be printed once, on the error stream, inside
a banner saying it is never stored, and MUST NOT be written anywhere unless an explicit
automation flag names a file, which is then written owner-only and announced loudly on every
run.

**MAN-26** `keygen` MUST draw 32 bytes from the operating system's random source and wipe them.
For `escape` it MUST require `--network` and emit `wpkh([<fingerprint>]<xpub>/*)` with the
extended key in the sealed network's flavour; for `user` and `recovery` it emits one definite
compressed public key. The secret is printed once on the error stream; for `escape` the banner
MUST state that a shared-seed escape turns duress into theft, and MUST include a line saying
that a multisig escape wallet is preferred. User and recovery bundle files carry `role` and
`pubkey`.

An escape bundle MUST carry `role: "escape"`, a `descriptor` in `MAN-39`'s grammar, and a
`cosigners` array. Each entry carries `key`, the complete public key expression as rendered by
`MAN-39` (origin, extended key, path and wildcard), and `master_fingerprint`, its eight lowercase
hex origin-fingerprint characters. The array MUST contain exactly one entry for every distinct
key expression in the descriptor, in first-occurrence order in its parsed tree; repeated uses
of the same expression name the same cosigner. Every descriptor key MUST be a ranged extended
public key with origin. The array's keys and fingerprints MUST agree with the descriptor;
missing, extra, repeated or mismatched entries MUST be refused. This is an escape-ceremony
precondition, not a restriction on the public descriptor grammar for other uses.

The Operator MAY construct this bundle using their own multisig tooling and supply it through
`MAN-27`'s bundle-path input. The ceremony adds no multisig construction command. `keygen`'s
single-sig escape output uses a one-entry `cosigners` array. For compatibility, an escape bundle
with the former top-level scalar `master_fingerprint` and no `cosigners` MUST also be accepted
when its descriptor contains exactly one distinct key expression satisfying the same
preconditions and its origin fingerprint equals the scalar. Assembly MUST normalize it to the
one-entry array before checking independence. A scalar on a descriptor with more than one
cosigner, or a bundle carrying both forms, MUST be refused. `WIR-13` supplies the artifact
examples.

**MAN-27** `assemble` MUST take a ceremony input naming bundle PATHS — never inline keys — plus
the hot descriptor, the two PIN digests, the chain backend address and credential, and the
policy values (`MAN-7`'s sealed set, `hold_secs`, the timing knobs, `policy_version`,
`max_msg_bytes`, `network`). It MUST ask for every value it seals rather than defaulting one
silently: a sealed value the Operator never chose is frozen for the vault's life by `OPS-1`,
and the refresh bounds in particular price a burn ceiling the Operator is the only party able
to size. It SHOULD ask for `pin_attempt_budget` on the same reasoning even though that one is
node-local and unsealed (`F15`). It MUST: validate the entire escape bundle against `MAN-26`,
refusing a wrong role, absent descriptor or invalid cosigner inventory; generate the coordinator
auth key here and only here; refuse any federation shape but `t ≥ 2, n = 2t − 1`; sort node bundles into canonical order and assign ids
(`CHN-7`); build and parse the descriptor against the template (`CHN-8`); compute `wallet_id`;
run the independence check (`MAN-28`) and refuse on any violation; validate endpoints (`MAN-4`);
bound the ladder ceiling (`MAN-13`) and the key flavour (`POL-8`); compute `manifest_hash`; and
write its artifacts (`MAN-29`).

**MAN-28** The **independence check** MUST cover every escape-wallet cosigner in the normalized
bundle of `MAN-26`, enforcing its precondition: "Every descriptor key MUST be a ranged extended
public key with origin." It MUST also refuse a key-less escape descriptor. One ranged key does
not excuse another definite or origin-less key. For each cosigner it MUST compare the derived
keys over the inclusive range
`0..=max_derivation_index`, on every branch of a multipath descriptor, and all available
ancestor public keys (including the supplied extended key's public key), against the user key,
every node key, every recovery key and the coordinator auth key. It MUST refuse any equality. It MUST also refuse:

- equality of the normalized escape and hot descriptor strings;
- any intersection of any escape cosigner's derived-plus-ancestor key set with the hot wallet's
  keys, derived over the same inclusive range and all multipath branches, including available
  ancestor keys and any definite keys;
- any escape cosigner's master fingerprint matching any master fingerprint in the hot
  descriptor's origins;
- two escape cosigners sharing a master fingerprint, even if their key expressions differ.

`independence.txt` MUST record every cosigner's key expression and master fingerprint, every
compared key and its role, the scanned range and branches, the per-cosigner verdict and the
overall verdict, and the residual limits of the check. The evidence MUST NOT claim seed
independence or physical device separation: same-seed keys at unrelated paths are unlinkable,
origin metadata is supplied rather than proof, undisclosed ancestor keys cannot be recovered
from an extended public key, and device separation is unverifiable. Fingerprint comparison is
defence in depth, not proof of independent custody; a collision is still refused. Vault keys
are definite (`CHN-3`: "one compressed secp256k1 public key"), so their lack of origin cannot
excuse omitting the public-key comparisons.

**MAN-29** `assemble` writes into its output directory: `descriptor.txt`, `wallet-id.txt`,
`manifest-hash.txt`, `coordinator-auth.pubkey`, `independence.txt` (all public);
`coordinator-auth.secret` and `ceremony-state.json` (owner-only, mode 0600). Its output MUST
state three things the numbers cannot: that the coordinator secret must be backed up separately
because losing it bricks the Normal path; that `duress_delay_secs` is a ceiling (`DUR-14`); and
that the ladder ceiling governs replacement rungs only, never the base Escape, whose fee cannot
exist at seal time, printed beside the recovery timelock in days because `ADR-0016` requires the
two to be reasoned about together.

**MAN-30** `node-endorse` MUST re-read the preimage on the node host, re-derive the key, refuse
if it does not equal the published `signing_pubkey`, and sign the endorsement of `MAN-6` over the
supplied `wallet_id`, `manifest_hash` and `node_id`, writing `endorsement-<node_id>.txt`.

**MAN-31** `finalize` MUST, before writing anything: parse the ids and the coordinator pubkey;
parse the descriptor and recompute `wallet_id`; read the coordinator secret and require it to
derive the pinned pubkey; re-run the ladder-ceiling and key-flavour bounds against the state it
is about to seal, because `assemble`'s gate is not the last word and no node ever bounds the
ceiling; recompute `manifest_hash` from the state's own fields and require equality, which
catches any post-assembly edit of a hash-bound field; and verify every endorsement.

**MAN-32** `finalize` MUST render the entire artifact set in memory and stage it under a
per-invocation owner-only directory (mode 0700) before ANY of it is published, then publish the
complete set with one same-filesystem rename to `sealed/`. An interrupted `finalize` therefore
exposes either no set or one complete set. It MUST refuse if `sealed/` already exists — never
accept, merge or overwrite, even byte-identical bytes — so an unsafe hand copy cannot be blessed.
A staging directory is never adopted; two overlapping runs cannot clear each other's staging;
and a retry MAY reclaim a stale one only when it is proven not to belong to a live invocation,
where a process id in the name is not proof (`OPR-80`, `F49`). The rename is not synced to
disk, so a host power loss can leave an incomplete `sealed/`; the same existing-set refusal
then requires the operator to inspect and remove it. Every artifact is re-derivable from
`ceremony-state.json`, which `finalize` never modifies. The parent namespace is `MAN-40`.

**MAN-33** The sealed set MUST be: `manifest.json` (public, `MAN-5`); one `node-<id>.toml` per
node, **owner-only**, because it carries both PIN digests and the backend credential;
`backup/descriptor.txt`, `backup/wallet-id.txt`, `backup/manifest-hash.txt`,
`backup/coordinator-auth.pubkey`, `backup/manifest.json`, `backup/independence.txt`,
`backup/README.txt` (public) and `backup/coordinator-auth.secret` (owner-only). Backups are
regenerated from the verified state, never copied from siblings, so an edited sibling is never
laundered into the backup and no secret is remade at the umask. Deliberately absent from every
artifact: the node preimages, the escape wallet secrets, the recovery keys.

**MAN-34** A secret file MUST be created owner-only from birth: an exclusively created temporary
file with mode 0600 in the same directory, written and synced, then renamed over the
destination, so an existing looser file is never written in place.

**MAN-35** Each node config MUST carry no key — only the derivation parameters — and MUST take
`listen_port` from the node's endorsed first endpoint, never from a separately stored field. The
generated TOML's `[channel]` block carries `node_id`, `expected_manifest_hash` and
`max_msg_bytes`, then every member's entry. Of `MAN-7`'s optional keys the ceremony MUST write
`refresh_min_interval_secs`, `refresh_max_feerate` and the whole `[pin_attempt_budget]` block,
identically into every node's config from one prompt, so a federation runs uniform values
rather than each host's default, and likewise every other sealed optional key whose value the
ceremony asked for (`MAN-27`: "It MUST ask for every value it seals") — `escape_coverage_pct`
and `escape_feerate_floor` among them — because a generated config that silently defaults a
sealed value fails the manifest-hash check at every node's startup (`MAN-2`); only the unsealed
optional keys are left to their defaults, and the generated file says so in a comment.

**MAN-36** A node starts **exactly once** in its life: `vault-node --config sealed/node-<id>.toml`,
the preimage on standard input, then the host is sealed (`ADR-0005`). Once the node is up and
the host sealed the operator MUST destroy the paper preimage: reprovisioning with the same key
and manifest would reset a locked node's budget for a coerced operator, which is the `/unseal`
resurrection `ADR-0007` rejects, and destroying the preimage is what removes the material for
it.

**MAN-37** The ceremony is **trusted**. The coordinator's "trusted until the wrench" applies to
the operating coordinator during ordinary spends; the ceremony is one-time, witnessed, and
precedes any funds. It is not useful to defend individual ceremony outputs against a hostile
ceremony tool: such a tool would seal a descriptor containing its own key, not forge a display.
Before funding a mainnet vault an operator SHOULD nonetheless parse the sealed descriptor with
an implementation-diverse oracle — Bitcoin Core's `getdescriptorinfo`, not a second binary on
the same descriptor library (`OPR-57`, `OPR-81`) — and read the timelock back: a correctness
check against a buggy tool, not an adversarial one.

**MAN-38** Automation flags (`--preimage-file`, `--secret-file`) exist for the regtest harness,
which has no human to type a preimage. They MUST announce themselves on every run, MUST write
owner-only, MUST refuse to alias a public artifact path, and a production ceremony MUST omit
them. The coordinator process still never reads the preimage bytes: it hands the file to each
node-side child on standard input.

## Canonical descriptor rendering

**MAN-39** Descriptor text that enters a vault or manifest hash MUST use this rendering
profile. A parser's customary display format is not protocol authority. Input MAY omit a
checksum; a supplied checksum MUST verify against the supplied body before normalization.
The output MUST contain the normalized body followed by `#` and its eight-character
[BIP380 checksum](https://github.com/bitcoin/bips/blob/master/bip-0380.mediawiki#checksum).
There is no whitespace or final newline in the hashed string.

The public descriptor grammar is `pk`, `pkh`, `wpkh`, `sh`, `wsh`, `tr`, `multi`,
`sortedmulti`, and typed Miniscript in the contexts those descriptors permit. `sh` may contain
`wpkh`, `wsh`, `sortedmulti` or legacy Miniscript; `wsh` may contain `sortedmulti` or Segwit-v0
Miniscript; `tr` contains an internal key and an optional binary brace-delimited tree of
tapscript Miniscripts. Bare descriptors contain legacy Miniscript. The Miniscript fragment
vocabulary is `0`, `1`, `pk_k`, `pk_h`, `after`, `older`, `sha256`, `hash256`, `ripemd160`,
`hash160`, `and_v`, `and_b`, `andor`, `or_b`, `or_c`, `or_d`, `or_i`, `thresh`, `multi`,
`multi_a`, with wrappers `a`, `s`, `c`, `d`, `v`, `j`, `n` and the aliases below. Context and
type validity are required; a library extension outside this grammar is not admitted merely
because that library parses it. Key expressions are public keys (including x-only keys where
the context admits them) or public extended keys with optional origin, path and wildcard,
with BIP389 multipath permitted. Private keys, `addr`, `raw`, `combo` and private library
extensions are outside this profile.

Rendering MUST apply these rules to the parsed tree:

- Emit fragment names in lowercase, parentheses and commas without spaces, integer arguments
  in unsigned decimal without leading zeros, and public-key, fingerprint and hash bytes in
  lowercase hex. Preserve a public key's compressed/uncompressed/x-only form and an extended
  key's Base58Check bytes; never derive a key or strip its origin to normalize it.
- Preserve child, key, tap-tree and multipath alternative order. In particular, do not sort
  `multi` or `sortedmulti` expressions while rendering: `sortedmulti` sorts derived keys when
  constructing a script, not the descriptor's textual key expressions.
- Render every numeric hardened path component with an apostrophe (`/0'`), both in origins
  and after extended keys, including components inside a multipath tuple. Accept the equivalent
  `h` spelling on input. Render an unhardened wildcard as `/*`, and a hardened wildcard as
  `/*h`, accepting `/*'` on input. Multipath stays `<a;b>` with its original alternative order.
  These input spellings follow [BIP380 key expressions](https://github.com/bitcoin/bips/blob/master/bip-0380.mediawiki#key-expressions)
  and [BIP389](https://github.com/bitcoin/bips/blob/master/bip-0389.mediawiki#specification).
- Recursively render `c:pk_k(K)` as `pk(K)`, `c:pk_h(K)` as `pkh(K)`, `and_v(X,1)` as
  `t:X`, `or_i(0,X)` as `l:X`, `or_i(X,0)` as `u:X`, and `andor(X,Y,0)` as `and_n(X,Y)`.
  Where both `or_i` children are zero, the `u` rewrite takes precedence. Concatenate consecutive
  wrapper letters in outermost-to-innermost order before one colon; `v:c:pk_k(K)` therefore
  renders as `v:pk(K)`. No other algebraic rewriting, branch reordering or policy compilation
  is part of normalization.

The hot allowlist's sorting and deduplication operate on the complete normalized strings,
including checksums, using ascending UTF-8 byte order. Escape exclusion uses equality of these
normalized strings. Semantically equivalent scripts whose descriptor trees differ beyond the
listed lexical/alias rewrites need not have equal strings or manifest hashes. This profile
reproduces the reference renderer while fixing the bytes independently of its language or
library version. The executable normalization fixtures are `WIR-34`.

**MAN-40** The ceremony MUST validate the directory that will CONTAIN the staging root and
`sealed/` before writing anything, and MUST refuse one that is writable by group or other,
because the owner-only modes of `MAN-32` protect entries inside the published set and not the
namespace around it: a local group member with write and execute on the parent can substitute
`independence.txt` before finalize — the one artifact that is neither re-derived nor
cryptographically re-checked — rename `sealed/` aside after a successful finalize and drop in an
attacker-authored set, or swap the staging root mid-ceremony under a successful rename. Creating
the parent with a tight mode closes nothing, since creation succeeds silently when it already
exists. The same check binds `finalize --dir` and the device directories. On a filesystem that
reports no meaningful mode bits — removable vfat or exfat media in an air-gapped ceremony — the
ceremony MUST print one warning naming the risk and proceed only under an explicit
`--allow-shared-parent` flag that is recorded in `ceremony-state.json`; it MUST NOT chmod or
delete an operator-created path.
