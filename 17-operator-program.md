# 17 — The operator program

The coordinator-side program an Operator runs: what it may and may not do, how it loads a
sealed vault, the user-signer seam that a hardware device replaces, the composer and its
read-only chain view, and each command — `spend`, `clawback`, `refresh`, `status`, `pending`,
`receive`, `balance`, `recover`, `rotate` — with its delivery and watch semantics. Node
behaviour is cited, never restated. Nothing here is interoperability-critical except what it
sends on the wire (`08-wire-contract.md`); the rest is what a coordinator must do to be safe
to hold the user key and hear the PIN.

## Program-wide

**OPR-1** The operator program is the coordinator (`DOM-3`). It composes transactions,
operates the user key, authenticates its requests to the federation, and pulls from the node
read surfaces. It MUST NOT combine partial signatures, finalize, or broadcast; no broadcast
call MAY be reachable from any production path rooted at a spend, clawback or refresh command
(`OVR-2`). Recovery is the one command that legitimately broadcasts (`OPR-75`).

**OPR-2** No HTTP response from a node is success, quorum proof, or proof that the exact
request was delivered. A command reports success only after its own chain backend observes
the node-side broadcast (`OPR-51`).

**OPR-3** Every secret path is an explicit argument with no default, adjacent-file, environment
or argv fallback. No secret byte MAY appear in `argv`, the environment, logs or CI artifacts.
The non-secret artifact directory and the coordinator credential are two separate arguments;
the credential is never formed by joining a name onto the artifact directory (`OPR-14`).

**OPR-4** Exit status is exactly: `0` — the command's own chain backend observed the exact
expected effect; `2` — grammar or usage error; `1` — a local refusal, an attributable
no-delivery, or an inconclusive watch. A preview and an exact-success report go to stdout;
prompts, warnings, refusals, the definite-no-delivery report and every inconclusive report go
to stderr. Every write is checked and every stream flushed; an unchecked write is a defect.

**OPR-5** Argument parsing MUST use the operating system's argument vector and preserve paths
as opaque OS strings. A non-UTF-8 name, a malformed socket or an unparseable scalar exits `2`
rather than crashing. IPv4 sockets are `IP:PORT`, IPv6 `[IP]:PORT`. Unknown, duplicated,
value-less or trailing positional arguments are usage errors. `<command> --help` writes the
grammar to stdout and exits `0` BEFORE any file or network access; a no-argument or
unknown-command invocation writes a synopsis to stderr and exits `2`.

**OPR-6** Confirmation text, the PIN and a node preimage MUST be read through one direct,
unbuffered file-descriptor reader, one byte at a time, wiping scratch on every exit path: no
buffered reader, no locked-stdin handle, no prefetch past the terminator into a non-zeroizing
owner. Echo control applies only when the descriptor is a terminal. The reader performs
exact-cap lookahead: only a newline or end of input is admissible at the cap, and cap+1
refuses rather than authenticating the prefix. Prompting order is echo off, checked prompt
write and flush, direct read, checked restore. No secret byte MAY be echoed before the guard
exists, and a failed UTF-8 conversion MUST recover the bytes into a zeroizing owner.

**OPR-7** A terminal-restore failure, or an empty PIN on the one command that reads a PIN
(`spend`), terminates the command before the
coordinator credential is opened, before the request or nonce is constructed, before any
node's PIN attempt budget is consumed, and before `/sign`. The read-only composition RPCs and
the user signature have by then already happened. Destructor-based restoration is only the
unwind fallback; a signal that kills the process may prevent it, and the documented recovery
is a terminal reset.

**OPR-8** Diagnostics MUST NOT reflect peer-chosen bytes. A node's refusal `check` and `detail`
MUST NOT be retained or printed — a hostile node can echo the plaintext PIN into them
(`API-16`); only the closed refusal code is retained, and the explanation beside it is locally
authored. A chain backend can place a chosen 64-hex string in a syntactically valid txid,
block hash or outpoint, so those identifiers are redacted from diagnostics too.

**OPR-9** A locally authored explanation MUST NOT imply a remedy the program cannot justify.
`PSBT_INCONSISTENT` is a broad adjudication: it MUST NOT say "recompose", MUST NOT imply
retry safety, and MUST NOT repeat a peer's `check`. `EXPIRY_TOO_SHORT` and
`COMMITMENT_EXPIRED` MUST NOT be reported as one peer stating a federation-wide setting.

## The sealed-artifact substrate

**OPR-10** A **live vault** is the only thing the program authorizes against. It is built from
one artifact directory the caller names outright: the program MUST NOT infer a ceremony root,
MUST NOT append `sealed/backup`, and MUST NOT read node configuration files. It reads exactly
`manifest.json`, `descriptor.txt`, `wallet-id.txt`, `manifest-hash.txt` and
`coordinator-auth.pubkey` (`MAN-33`), each as trimmed text. It MUST load with
`coordinator-auth.secret` absent and MUST ignore a malformed decoy of that name beside the
public artifacts, because the credential is stored elsewhere (`OPS-24`).

**OPR-11** The manifest revision MUST be checked first, from a minimal JSON envelope rather
than the decoded current schema, and MUST precede every current-field error, hash error,
sibling artifact read and socket. Only the current revision (`MAN-3`) may become a live
vault; an older manifest is never hash-authenticated under its own layout.

**OPR-12** A manifest of an older revision from `4` upward MUST still parse, syntax-tolerantly
with every field defaulting, for the cold path (`OPR-75`); revisions `1`–`3` are refused
outright (`MAN-3`: "No vault was ever sealed at revision 1, 2 or 3"). A later revision's
program keeps operating a revision-4 vault's cold path (`OPS-31`), and the descriptor alone
suffices for it (`OPR-74`).

**OPR-13** Live-vault construction MUST refuse unless all of the following hold, checked
before any network I/O: (1) `descriptor.txt` parses as a definite descriptor whose canonical
rendering equals the manifest's `vault_descriptor`; (2) it parses as a vault template
(`CHN-1`); (3) the wallet id recomputed from it (`CHN-6`) equals both `wallet-id.txt` and the
manifest's; (4) the manifest's `t`, `n`, `recovery_timelock` and node-entry count equal the
template's — the descriptor is authority, the manifest the claim; (5) `network` is one of the
three accepted values (`MAN-14`) and the escape and every hot-allowlist descriptor carry that
network's key flavour (`POL-8`); (6) `coordinator-auth.pubkey` parses as a compressed point and
equals the manifest's; (7) every node entry's `node_id` equals its index, its signing key
equals the descriptor's key at that position, and it pins at least one endpoint that parses as
a socket address; (8) the manifest hash recomputed from the manifest's own fields (`MAN-2`)
equals both `manifest-hash.txt` and the manifest's; (9) every node's channel endorsement
verifies over that hash (`MAN-6`).

**OPR-14** The **coordinator credential** is a separate type loaded from a second explicitly
named path. Loading MUST derive its public key and MUST refuse — not warn — if it differs from
the manifest-pinned key. It holds only zeroize-on-drop bytes, is not printable, and the loader
erases its own copy of the parsed key on failure as well as success. It MUST NOT be reachable
from the object the signer consumes.

**OPR-15** A live vault retains, and only retains: `wallet_id`; the recomputed `manifest_hash`;
the definite descriptor and its parsed template; the policy parameters (vault descriptor,
allowlist with the escape descriptor appended, escape descriptor, `max_derivation_index`,
`hot_max_per_tx`); `network`; `escape_bump_max_fee_pct`; `escape_feerate_floor`;
`escape_coverage_pct`; the authenticated `max_msg_bytes` through a checked width conversion;
`policy_version`, `refresh_min_interval_secs` and `refresh_max_feerate`, each hash-authenticated
by check (8) like every other preimage field (`MAN-2`); the coordinator public key; the pinned
endpoints in node and endpoint order. It holds no secret.

**OPR-16** Every secret file — the coordinator credential, the user key, the backend cookie —
MUST be opened without following a final symlink and without blocking on a FIFO, then proved a
regular file that is owner-only from the OPENED file's own metadata, so both checks describe
the bytes actually read. The text is zeroizing all the way to the caller, and a read sizes its
buffer from the open file so no reallocation leaves an un-wiped prefix. One reader serves all
three, so they cannot drift on which paths they refuse.

**OPR-17** The backend authentication **cookie** MUST be capped at 4 096 bytes: one `cap + 1`
zeroizing buffer allocated once and never grown; an interrupted read retried; exactly the cap
accepted only once end of input confirms it; cap+1 refused; non-UTF-8 refused. The selected
path appears in every diagnostic and the credential in none. The cookie is re-read per RPC and
dropped before the call returns, base64-encoded directly into a zeroizing buffer and copied
only into the zeroizing request bytes, never into an ordinary header string.

**OPR-18** A key scalar MUST live behind a non-copyable erase-on-drop guard exposing exactly
three operations — public-key derivation, signing of a supplied message, and a CONSUMING
conversion into a zeroizing 32-byte owner — and no secret-key value or reference, no
non-consuming raw view, no callback that receives the raw key, no public constructor taking a
secret key, no clone and no debug rendering. Parsing happens inside the credential and
user-key constructors, which erase the inbound copy before returning; owned temporaries are
erased on mismatch, on error, on success and on unwind. Cryptographic-library internal copies
are best-effort and MUST NOT be claimed as erased.

**OPR-19** The user key and the coordinator credential are never open at the same time: the
signer is dropped before the credential is opened (`OPR-43`), and the credential is dropped
before the first request byte (`OPR-47`).

## The user-signer seam

**OPR-20** Authorization crosses one labelled object with the arms split by request type, and
it is frozen at these three arms — no renaming, no fourth arm, no extra method, no PIN
material:

```
UserAuthorization     = Spend    { wallet_id, SpendAuthorization }
                      | Refresh  { wallet_id, RefreshAuthorization }
                      | Clawback { wallet_id, ClawbackAuthorization }
SpendAuthorization    = { spend, escape, escape_bumps[] }     // PSBTs
RefreshAuthorization  = { refresh }                            // one PSBT
ClawbackAuthorization = { clawback }                           // one PSBT
UserSigner.authorize(&UserAuthorization) -> Signed | Error
```

Every arm ships with every other even where its command does not exist yet, because an
interface missing an arm needs a method later and that retrofit is what the seam exists to
prevent. The Clawback arm was the third (`ADR-0022`): reusing the Refresh arm for a
transaction that empties the vault would have been the unlabelled-PSBT problem `OPR-40` names.

**OPR-21** No PIN and nothing PIN-dependent crosses this interface. Silence is structural
here: the seam never receives the input a signer would have to branch on.

**OPR-22** The arm tag and `wallet_id` are caller-supplied display and lookup hints carrying no
authority; no signature commits to either. A signer MUST authenticate wallet membership, the
transaction class and every role it can derive from the sealed state it loaded itself, and
MUST refuse a PSBT whose inputs are not that vault's, whatever the label says.

**OPR-23** A signer MUST validate the whole group before the first signature exists, in this
order: (1) the ladder length against the cap of 3 (`CHN-16`); (2) each member (`OPR-24`);
(3) the group shape and each member's `nSequence` form (`OPR-25`); (4) reserved — it was the
withdrawn `OPR-26`, and the numbering is kept so later steps stand; (5) the ladder
relation and the sealed ceiling (`OPR-27`); (6) the display (`OPR-29`); (7) every sighash
message for every input of every member; only then (8) the signatures. No error path returns
a partially signed group, and the caller's own PSBT objects are left untouched: only
validated clones are normalized and signed.

**OPR-24** Per-member validation, all against the full previous transaction (`CHN-22`): input
and output maps match the unsigned transaction's counts; no input carries a `scriptSig` or a
witness; no outpoint repeats; a declared sighash type is `SIGHASH_ALL`; `non_witness_utxo`
is present, hashes to the input's txid, and its `vout` is in bounds; the mandatory
`witness_utxo` equals that canonical output exactly; a supplied `witness_script` is the sealed
one; inputs
and outputs sum under checked arithmetic; outputs exceeding inputs is a refusal, not a wrap.
The member's fee, its outflow (outputs minus outputs paying the vault descriptor), its class
and its outpoint set are derived from that one canonical source, and the policy evaluation
(`03-policy-checks.md`) runs on the normalized clone.

**OPR-25** Exactly one Spend group shape is admissible:

| shape | condition | labels |
|---|---|---|
| `(Hot, Escape)` | both input sets non-empty and equal | `primary hot-destination transaction`, `escape-destination transaction` |

Anything else is refused before signing; a self-paired request — the same transaction in both
positions — and an `(Escape, Escape)` pair are refused shapes (`CHN-23`). A Refresh arm's
single member must classify `Refresh` and is labelled `vault-refresh transaction`; a Clawback
arm's single member must classify `Escape` and is labelled `claw-back transaction`. A
ladderless Escape carries `nSequence` `0xffffffff` on every input (`CHN-15`); a claw-back
carries `0xfffffffd` (`CHN-35`); the signer refuses either shape with the other's value.

**OPR-27** Ladder validation is authorization, not construction. Base and every rung: the
same `nVersion`, `nLockTime = 0`, every input `nSequence` at `0xfffffffd`. Every rung
additionally: the base's exact ordered outpoints and output scripts; no output value above the
same output on the rung below; a STRICTLY greater total fee than the rung below, named as its
own rule so an equal-fee rung is not blamed on relay; an increase of at least the
incremental-relay minimum computed from that replacement's own maximum finalized vsize; and
`rung_fee × 100 ≤ rung_total_input × escape_bump_max_fee_pct` in arithmetic wide enough that
neither side wraps, equality passing. The base Escape is ceiling-exempt (`CHN-17`); a sealed
ceiling of `0` refuses every rung that pays any fee.

**OPR-28** The ceiling check is an honest-path composition discipline, not enforcement against
a hostile coordinator, and MUST be documented as such: a validly signed over-ceiling
transaction obtained earlier as the ceiling-exempt base, as a claw-back, or in
another authorization can be replayed later as a rung, because `SIGHASH_ALL` authenticates
bytes and not the base-or-rung role. A node-verified authorization proof or node-side
ceiling MUST NOT be added; the hostile-coordinator fee bound is node-side — the 10% ingress
cap per rung (`POL-12`) and the fire-time coverage guard (`DUR-22`).

**OPR-29** One display function renders the group from the same validated canonical data the
signer signs, and MUST be callable with the sealed vault alone, before any key file is opened,
so an Operator reads what they are about to authorize without first surrendering a key and a
hardware signer reuses it. Its shape is fixed:

```
vault <wallet_id hex> authorization (caller hint; the sealed state is authority)
<label>: <fee> sat fee, <outflow> sat leaving the vault, <n> input(s)
  output <i>: <sat> sat to <payee>[ (vault change)]
```

`outflow` excludes vault change, because over one coin at one fee a small payment and a
near-total drain have identical total output value and differ only there. Every output of
every member is rendered in transaction order; the aggregate alone is not the review
`ADR-0012` requires. `payee` is an address for the sealed network, falling back to script hex
where no address encodes it; an output about to be bound by `SIGHASH_ALL` is shown, never
dropped. No output line MAY contain the word "transaction": that word is how a member is
counted, and dropping a member is the failure the count exists to catch.

**OPR-30** The software signer reads the user scalar from one explicitly named owner-only file
(`OPR-16`), proves it derives the sealed descriptor's user key, and lets those bytes reach no
log, artifact or error. It signs only inputs whose canonical output script is the sealed
vault script; an input that is not is a refusal, not a skip, because a group with an unsigned
input is the partial authorization the seam forbids. Every signature is ECDSA `SIGHASH_ALL`
over the P2WSH sighash under the sealed witness script (`CHN-11`).

**OPR-31** A **hardware signer** replaces `OPR-30` and nothing else: the program exports the
PSBTs, the device displays and signs them, the signed PSBTs come back; a per-PSBT device
iterates internally and the seam survives unchanged. The device display is the security
boundary and MUST show the destination, the amount, and that a mandatory Escape is
co-signed — a device that blind-signs what the coordinator composed defends nothing against a
compromised coordinator (`SEC-43`). The hand-off SHOULD reuse the Operator's existing
PSBT tooling rather than add a dependency (`OPS-46`). Choosing a vendor and on-device
multisig UX are out of scope; this document names no device.

## The composer and its chain view

**OPR-32** The composer's chain backend MUST be a closed, read-only set of exactly eight
calls: `getblockchaininfo`, `getbestblockhash`, `scantxoutset` over the definite vault script,
`gettxout(txid, vout, true)`, `getblockhash(height)`, block-qualified
`getrawtransaction(txid, false, blockhash)`, `estimatesmartfee(6, "CONSERVATIVE")` and
`getmempoolinfo`, through one private funnel with a fixed request id under Basic auth with no
CR or LF. No generic method string, no batch, no wallet endpoint, no mutating or broadcasting
method, no cache, no background work. A `null` result is admissible only for `gettxout`. The
design is safe only while the set stays read-only: one mutating method reopens delivery
semantics.

**OPR-33** The composer spends **every** coin of the stable confirmed inventory in canonical
outpoint order; there is no coin selection and no omission. The node's coverage denominator is
`DUR-22`'s alone, which states: "What the coordinator composes over (`OPR-33`) never changes
this denominator." The inventory is established in at most three passes with no sleep,
backoff or scheduler; each pass reads chain info, validates the backend's chain identity as a
node does (`WTC-3`), refuses during initial block download, captures a before-tip, scans,
sorts and rejects duplicates, off-script records and an empty set, runs the zero-amount
two-shape preflight, opens every candidate, resolves grouped block-qualified full parents,
closes every candidate, reads the tip again, and accepts only if every tip read agrees and
every closing value and script equals its opening read. Only observed tip movement makes a
pass retryable; every other error is terminal. A coin needs more than zero confirmations, a
coinbase at least 100.

**OPR-34** A scanned confirmed vault coin absent from the UTXO set at the same tip MUST refuse
the WHOLE inventory — never silently omit it, never diagnose "wait for confirmation", because
the conflicting spend may never confirm — and MUST tell the Operator not to reissue until
independent chain reconciliation accounts for that coin. The one exception is `clawback
--replace` (`OPR-69`), which composes over the recorded outpoints of the program's own earlier
claw-back without an inventory scan and leaves the replacement verdict to the nodes
(`WTC-25`). Composing over the remainder yields
an under-covered Escape. A coin mempool-spent by a prior vault spend is the common case, has
no protocol time bound, and lasts as long as that spend stays resident; eviction does not
prove the already-authorized bytes cannot return (`F2`).

**OPR-35** Two size bounds, both refused BEFORE allocation: the projected total of retained
full parent transactions — parent size × candidate multiplicity × both PSBT input maps, in
checked arithmetic — at most 64 MiB, equality passing, refused before retaining an over-cap
parent; and each composed shape's maximum finalized vsize at most 100 000 vB, checked in the
zero-amount preflight before any candidate or parent read.

**OPR-36** Fee signals are read only after the inventory is accepted and are a liveness
snapshot, not part of the consistency proof. The rate is `max(estimate if present,
incremental-relay floor, mempool-minimum floor)` through checked amount arithmetic, divided by
1000 rounding UP to integer sat/vB. Both floors may be zero, so an absent estimate can yield a
zero rate; that is a named non-relay residual of what the backend reported, and the composer
MUST NOT invent a positive floor it has no authority to set.

**OPR-37** Composition order: parse the destination and bind it to the sealed network BEFORE
any chain read; derive the change script from the sealed descriptor; derive the base Escape
script at derivation index 0 of the first canonical branch of the sealed escape descriptor,
with no address-index state; a caller-supplied change script is a check, not an input —
mismatch is terminal before any chain read and the internally derived value is used
thereafter.

**OPR-38** The primary's fee is `rate × its own preflighted vsize`; the Escape's rate is
`max(rate, escape_feerate_floor)` and its fee that rate × ITS OWN vsize (`CHN-20`). The
requested amount is preserved exactly; change and sweep are what is left by checked
subtraction, never absorbed into a fee (`CHN-19`). Each concrete output is checked against its
own script's default dust minimum, equality passing, which establishes nothing about a backend
with a custom dust relay fee. Coverage is `sweep × 100 ≥ total_in × escape_coverage_pct`,
widened, equality passing (`CHN-21`). Both shapes are priced at their maximum finalized vsize
(`CHN-20`); a finalized transaction that measures smaller keeps the composed absolute fee. The
full previous transaction of every input of both is attached from the
completed inventory with an explicit `SIGHASH_ALL`; that refusal names no identifier
(`OPR-8`). Finally the policy evaluation runs on both final byte sequences — the sole
authority for the 10% whole-fee cap — and the primary must classify `Hot`, the Escape
`Escape`.

**OPR-39** Composition is **confirmed-only** in this revision: it does not spend
vault-authorized unconfirmed value (`F2`). Value or floors moving afterwards can leave the pair
slow or inadmissible at fire time, which degrades to Lockdown and Recovery rather than
redirecting value. When composition over vault-authorized unconfirmed value lands it MUST
prove authorization from the vault-spend ancestry — never merely from a script paying the
vault — exclude external unconfirmed deposits, obey the node's package bounds (`WTC-24`) and
fail loudly when the package cannot fit, take one bounded internally consistent backend view,
and leave the node's coverage denominator unchanged.

**OPR-40** When the sealed ceiling admits rungs, the **ladder composer** derives them from the
base Escape's own fee at 4×, 16× and 64× (`CHN-17`), never from a second fee source, dropping
a candidate that breaches the ceiling, the 10 000-satoshi funded-output floor or the relay
increment; a valid non-zero ceiling yielding an EMPTY ladder is a supported outcome, not a
failure. Before the user signs it MUST surface how many rungs, at what fees, and what share
of the swept value the top rung pays: an Operator authorizing rungs they cannot see is the
unlabelled-PSBT problem the seam's shape was chosen to avoid.

**OPR-41** A request composed by `spend` carries the ladder of `OPR-40`; a claw-back carries no
ladder (`CHN-35`) and is fee-bumped by submitting a higher-fee claw-back over the same coins
(`OPR-69`).

## `spend` — authorize, relay, watch

**OPR-42** The grammar is exactly nine flags, in any order, each exactly once:

```
btc-vault spend --artifacts <DIR> --coordinator-credential-file <PATH>
  --user-key-file <PATH> --core-rpc-addr <IP:PORT> --core-cookie-file <PATH>
  --destination <ADDRESS> --amount-sats <U64>
  --request-ttl-secs <POSITIVE_U64> --watch-grace-secs <POSITIVE_U64>
```

A zero amount, a zero TTL or grace, an overflowing `TTL + grace`, a non-loopback backend
address, and a destination or policy refusal all exit `1` BEFORE any signing secret is opened.

**OPR-43** The command executes in exactly this order and no other:

```
parse → load secret-free artifacts → per-RPC chain snapshot and fee
→ compose primary + Escape + ladder → describe → checked preview flush
→ typed confirmation → open user key → authorize
→ bind approved display and ordered txids → drop signer
→ drop the original authorization and every full-parent PSBT
→ strip signed wire parents → worst-case preflight
→ PIN → open credential → wall-clock then monotonic sample
→ build one request with one fresh nonce → authenticate → drop credential
→ compute the local expected commitment id → actual-request preflight
→ pre-ingress warning → first /sign byte
```

Composition refusal precedes the user key, the PIN and ingress. A preview sink failure opens
no key, reads no PIN, opens no credential and reaches no ingress.

**OPR-44** Confirmation is echo-on: the program writes and flushes exactly
`Type SPEND to authorize:` and accepts only exactly `SPEND` followed by newline — no trimming,
no synonym, and end of input is NOT acceptance. The PIN is echo-off, one line of at most 64
bytes (`WIR-16`), and only the final PIN may end at newline or end of input.

**OPR-45** After authorization the program MUST require BOTH that the signer's bound display
is byte-for-byte the approved preview AND that the ordered unsigned txids
`[primary, escape, rung…]` equal those previewed; a mismatch aborts before the PIN is
collected or any signed byte is relayed. That closes substitution between preview and
authorization without a display framework. The signer, the original authorization, every
full-parent PSBT and the preview storage are then dropped, retaining only the expected change
and txid facts.

**OPR-46** Every `non_witness_utxo` is stripped from the WIRE PSBTs after verification; the
canonical `witness_utxo` is retained (`CHN-22`). Before the PIN a worst-case request shell —
maximum PIN length at six bytes per character of escape expansion, maximum expiry, fixed
nonce and signature placeholders — is encoded, and both the raw `/sign` JSON and its exact
channel-envelope expansion must fit the HTTP body cap (`API-4`) and the authenticated
`max_msg_bytes` (`API-6`); the actual request is rechecked before ingress. Oversize is a
local typed refusal, never a probe that lets a node answer 413.

**OPR-47** The wall clock is sampled first, then the monotonic clock, exactly once, with no
fallible work between. Checked arithmetic derives `expiry = wall + TTL`, the aggregate ingress
deadline `monotonic + TTL`, and the watch deadline `ingress deadline + grace`. Watch grace is
a positive deployment input that MUST be at least the maximum combine slack plus the 60-second
poll cadence; the program enforces positivity and arithmetic, the runbook proves the floor.
The request carries one fresh 32-byte nonce from the operating system's CSPRNG, is
authenticated (`WIR-31`), and the credential is dropped BEFORE the first request byte. The
expected commitment id is computed locally (`CHN-26`) from the final expiry, the sealed
identity and the exact stripped wire PSBT; a peer-returned id is never trusted or retained.

**OPR-48** **Delivery.** One caller-supplied ABSOLUTE aggregate deadline bounds the whole
ordered offer (`API-16`). The request is serialized once and every endpoint receives
byte-identical bytes and the same nonce in manifest node and endpoint order; only the `Host`
header differs. Immediately before each endpoint the client recomputes `min(now + 60 s,
aggregate)` from the clock — never rebased from a remaining duration, with the addition
checked so a clock near the representable end clamps to the aggregate — and spends that
absolute instant on the bounded exchange. An endpoint reached at or after the aggregate is
pre-connect `NotSent` and opens no socket. There is no minimum per-endpoint slice: a short or
nearly exhausted aggregate lets an earlier slow endpoint suppress later ones, and help text
and the runbook MUST state that without promising endpoint fairness.

**OPR-49** **Sticky delivery state.** The state starts "definitely not sent", advances to
"possibly delivered, exact bytes" on EVERY attempt that is not `NotSent` — BEFORE the status
line or body is decoded — and never moves backward. `400` and `413` both advance it and both
CONTINUE to the next endpoint. `NONCE_REPLAYED` stops the loop only when the state immediately
before that attempt was already possibly-delivered, so a preceding `400` counts; on a first
attempt a replay is someone else's and the loop continues. The loop otherwise stops only on a
`200` `accepted` whose `commitment_id` equals the locally computed expected id, compared while
borrowed from the bounded zeroizing response bytes, only the local string ever retained; a
mismatched `accepted` is not acceptance — it keeps that attempt's possible delivery and
continues. `NotSent` is reachable ONLY when connect fails before any request byte could be
written; once connect returns, every timeout, partial write, read or framing failure is
possible delivery. No single endpoint's `NotSent` authorizes anything (`OPR-51`).

**OPR-50** The bounded HTTP exchange creates ONE monotonic deadline before connect and spends
it across connect, writes, status line, headers and the whole body, recomputing before every
blocking operation and never resetting. It accumulates the entire raw response into one
pre-reserved zeroizing allocation of exactly `cap + 1` that never grows; crossing the cap is a
typed ambiguous failure that still preserves a valid status with an absent body. Caps: 64 KiB
for `/sign`; 16 MiB for backend reads. Deadlines: the caller's for ingress; 60 seconds for
the seven ordinary backend reads and 600 seconds for the full scan alone. A status line is
exactly `HTTP/1.0` or `HTTP/1.1` plus one three-digit code in `100..=599`. Completion is end
of stream within both bounds — a parseable JSON prefix is not completeness. After end of
stream the header block must be complete: any transfer-encoding, more than one
content-length, or a malformed content-length yields an absent body; exactly one valid
content-length must equal the received body length; field names match case-insensitively
including for duplicate detection. These are raw-wire bounds, not a bound on what decoding
costs.

**OPR-51** **Watch, and the proof.** Immediately before ingress the program writes and flushes
exactly:

> `delivery may already have happened; terminating ingress/watch is NOT proof the transaction did not/will not broadcast; the change may already be spent; NEVER reissue without an independent chain check.`

A sink failure here sends nothing. The warning repeats before the first watch poll and on
every inconclusive exit. After delivery returns, the request, the PIN and every request-owned
secret buffer are destroyed BEFORE endpoint reporting or a potentially day-long watch.

If EVERY endpoint was `NotSent`, the program does not watch: it writes and flushes exactly
`DEFINITE NO DELIVERY: no /sign request byte was written; the earlier pre-ingress warning does
not apply to this invocation`, states that a new command may be started after connectivity
repair, and exits `1`. That is the one nonzero result that does not demand an independent
chain check, and the only outcome that authorizes reissuing a signed request (`DEF-8`).

Otherwise it watches through exactly one typed call, `gettxout(txid, vout, true)`, on the
command's watched output: output 1 of the primary — its vault change — for `spend`, and
output 0 of the transaction for `clawback` and for `refresh`, neither of which has an output 1
(`OPR-68`, `OPR-65`). Success is a non-null result matching both that
output's composed value and script. Polling is sequential at a real 60-second cadence with no jitter, backoff,
concurrency or catch-up, against the pre-ingress monotonic deadline. A pre-deadline null, a
wrong value, a wrong script and a backend error are all inconclusive and CONTINUE — an abort
on any of them is a defect, because a later poll can still return the exact match. At or after
the deadline exactly one final attempt is made; only an exact match succeeds; a final null,
mismatch or error is inconclusive and exits `1`. A null or a final error does not prove no
broadcast. No generic lookup, no new backend method and no direct broadcast may be added. Once
delivery is possible, a failure to write any endpoint fact, warning or report is latched,
MUST NOT skip the final poll, and makes the exit `1` even if the backend later observes the
change. A hot TTL normally outlives the Hold plus combine slack — 24 hours by default — and
the watch is a foreground session the Operator keeps alive: there is no daemon, no signal
handler and no second ingress loop.

## `status` and `pending`

**OPR-52** `status` MUST poll every one of the `n` nodes — not a quorum, never through the
coordinator's own view — on `/healthz` for liveness, the Lockdown latch and the wallet
fallback (`API-19`), on `/pending` for accepted candidates, and on `/events` for alerts,
retaining the returned cursor per node. A node that does not answer MUST be reported as
unreachable and MUST NOT be silently dropped from the comparison, and the command MUST NOT
hang on it (`OPS-2`).

**OPR-53** `pending` presents the accepted-candidate set PER NODE and diffs it against the
authorization record (`OPR-54`). Per-node disagreement MUST be presented rather than merged
into one list: one node holding a candidate the others do not is the arm-split shape
`ADR-0012` cares about, and the divergence is itself the signal. The outcomes are: agreed
across all `n`; divergent; unrecognized — present at nodes, absent from the record.

**OPR-54** The **authorization record** is an append-only local file on the coordinator host
in which `spend`, `clawback` and `refresh` write the expected commitment id, the ordered txids,
the display and the time BEFORE the first request byte. One record serves both the `pending`
diff (`OPR-53`) and the alert correlation of `OPR-60`; a second MUST NOT be defined. Its trust
limit MUST be stated plainly: nothing protects it from a coordinator that is already hostile,
so the diff detects a stolen user key and normal PIN used from elsewhere (A3, `OPS-19`) and
not a post-wrench coordinator, whose remedy is the power switch (`OPS-11`).

**OPR-55** `/pending` exposes opaque commitment ids and nothing else (`API-21`). Help text and
the runbook MUST state that an unknown pending id is insufficient to identify coins and that
the Operator MUST NOT guess; the remedy is the known-outpoint claw-back of `OPR-67` against
coins the Operator independently knows are threatened, or a full sweep. No pending-detail
API, journal endpoint or automatic threat discovery MAY be added to close that gap.

## Funding: `receive` and `balance`

**OPR-56** `receive` renders the vault's single deposit address from the sealed definite
descriptor for the sealed network. There is no index: `CHN-3` admits "no derivation path and
no wildcard", so every deposit reuses the one script (`CHN-9`), and help text MUST say so
rather than imply a fresh address. Rendering the address MUST NOT require the federation to be live or the
coordinator to be trusted: a deposit address for a locked-down vault is a real requirement,
being the straggler deposit the Sacrificial drill depends on (`OPS-39`).

**OPR-57** Before the first deposit to a mainnet vault the derived address MUST be re-derived
and compared byte for byte by an implementation-diverse oracle: a pinned offline Bitcoin Core
`getdescriptorinfo` and `deriveaddresses` on the sealed network, compared against frozen
constants. A tool built on the same descriptor library family as the program is a separate
binary but not an independent encoder and MUST NOT be labelled independent; the release
documentation MUST carry a table naming, per verified property, the oracle, its library
family, and which failure classes it detects and cannot detect. This is a correctness check
against a buggy tool, not an adversarial one: a derivation bug sends funds somewhere
unrecoverable and is invisible until it does.

**OPR-58** `balance` lists the vault's unspent coins and their total, including each coin's
confirmation height, so the maturity computation of `OPR-62` reads it rather than recomputing.

**OPR-59** `receive` MUST support retiring the vault's address — marking it as no longer to be
used, which is retiring the vault — because a stage's deposit address is retired with the stage
(`OPS-42`) and a migration retires the predecessor's (`OPS-59`).

## Alerts and maturity

**OPR-60** Alert consumption MUST poll `/events` on EVERY node, persisting each node's consumed
events and returned cursor atomically so that a restart neither re-processes nor skips an event
the queue still holds, and reporting a gap it cannot close — `API-18` retains 1 024 events and
drops the oldest beyond that, so losslessness past a long outage cannot be promised — correlate
across nodes — one node alerting while four are silent is a different situation from all five
agreeing — correlate every `UNRECOGNIZED_SPEND` and `RECOVERY_PATH_SPEND` event (`API-18`'s
kinds; there is no sign event) against the authorization record (`OPR-54`), deliver a notification through a channel
the Operator will see when not at a terminal, document a response per alert class pointing at
`13-operations-and-rollout.md`, and state what happens when the notification channel is down
(`F45`).

**OPR-61** The trust limit MUST be stated: delivery is coordinator-pull (`ADR-0002`), so a
compromised coordinator can suppress alerts. That is accepted for the wrench case — the
coordinator is trusted before it and you already know during it — and the reasoning does NOT
extend to the recovery-key alert (`OPS-3`), which fires when there is no wrench and no reason
to suspect anything; whether that alert needs a coordinator-independent path is `F45`.

**OPR-62** Maturity MUST be computed per coin from its confirmation height and the vault's own
timelock (`CHN-4`) and reported as the earliest maturity across the unspent set — never as one
vault-level date, because the relative lock runs per coin and a straggler deposit starts its
own clock. The countdown MUST be readable without the coordinator being trusted or alive,
from the descriptor and a chain view alone, because a dead coordinator is exactly when a vault
drifts.

**OPR-63** Nags fire at thresholds expressed as fractions of the vault's own timelock — 2/3
and 5/6 — never as fixed day counts; on the 180-day default those are day 120 and day 150. On
a 90-day vault a day-120 nag fires after maturity and a day-150 nag never fires, precisely on
the vaults a short timelock makes weakest. The mandatory safety margin (`OPS-6`) is likewise a
fraction (`F46`). A stage-observation run whose Survivor vault crosses the margin MUST be
refreshed or aborted.

**OPR-64** This control protects the Operator who looks. It is not a control against a
recovery-key holder who acts, and MUST NOT be written up as one (`SEC-35`).

## Incidents and lifecycle

**OPR-65** `refresh` composes the PIN-less vault self-spend (`SPN-43`) as **one one-input,
one-output transaction per coin**, paying the coin's value less fee back to the vault script,
with every `nSequence` at `0xfffffffd` (`CHN-18`). It caps the fee at `refresh_max_feerate ×`
the transaction's maximum finalized vsize from the live vault's sealed bounds (`MAN-2`,
`SPN-47`). It does NOT pre-check `SPN-46`'s interval: that needs the confirming block's
median-time-past, which none of `OPR-32`'s eight calls returns, so `REFRESH_TOO_SOON` is
learned only from the node — and since `OPR-8` retains no refusal `detail`, a multi-input batch
refused that way could not name the input at fault, which is why the shape is one coin per
transaction. It authorizes through the Refresh arm of the seam — no Escape, no ladder — relays
under `OPR-48`–`OPR-50`, and watches under `OPR-51`, which proves node-side broadcast, not
confirmation. It handles `REFRESH_TOO_SOON`, `REFRESH_FEE_EXCEEDS_CAP` and
`REFRESH_SUBORDINATED` (`API-13`) by reporting and stopping, never by retrying into a pending
spend. Its strategy is **refresh in place, per coin**; consolidation is not offered, because a
batch refused `REFRESH_TOO_SOON` could not name the input at fault (`OPR-8`).

**OPR-66** `rotate` drives a rotation (`OPS-30`) through the migration tooling (`OPS-59`), in
the order the trigger dictates: sweep first under duress or a compromise signal, verify the
successor first for a patch or a planned key change.

**OPR-67** `clawback` is the incident sweep with a **known-outpoint** contract:

```
btc-vault clawback (--outpoint <txid:vout>... | --all | --replace <txid>)
  [--fee-rate-sat-vb <POSITIVE_U64>] --request-ttl-secs <POSITIVE_U64>
  --watch-grace-secs <POSITIVE_U64>
```

plus the artifact, credential, key and backend arguments of `OPR-42`, minus nothing: there is
no PIN (`SPN-50`). Exactly one selection mode is required; `--outpoint` is the one repeatable
flag, exempt from `OPR-5`'s duplicate rule, and a duplicate outpoint VALUE still refuses under
`OPR-68`. It is free-to-act and coordinator-still-trusted, for vault outpoints the Operator
independently knows are threatened, for the whole vault under `--all` when rotating (`OPS-30`)
or when a PIN is forgotten (`SEC-54` rows L4, L5), or under `--replace` to bump one of its own
earlier claw-backs (`OPR-69`); it does not turn an opaque pending id into coin discovery
(`OPR-55`).

**OPR-68** Against the stable confirmed inventory `U`: the named set `T` MUST be non-empty,
each entry unique, unspent and a coin of the sealed vault, `--all` names `U`, and `--replace`
names the recorded outpoints of an earlier claw-back without consulting `U` (`OPR-69`); the
transaction's inputs are exactly `T`, it pays exactly one output to the escape descriptor at
derivation index 0 of the first canonical branch (`CHN-18`), carries no vault change, sets every
`nSequence` to `0xfffffffd` and `nLockTime` to `0` (`CHN-35`), and pays `rate × its own maximum
finalized vsize` under `POL-12`'s cap. A one-coin vault and a selection covering every coin are
ordinary cases. An unknown, spent or off-vault input, an unstable scan, a dust failure and a fee
failure all refuse BEFORE signing and the network.

**OPR-69** The claw-back is composed as a ClawbackRequest (`API-24`), authorized through the
Clawback arm of the seam (`OPR-20`) with the display of `OPR-29`, and relayed under
`OPR-48`–`OPR-50` in `OPR-43`'s order with the PIN step absent: the credential is opened only
after the signer is dropped (`OPR-19`). An `accepted` response is inspected for
`remaining_secs == 0`; a nonzero anomaly is reported and can make the result nonzero only AFTER
the conservative watch, never instead of it. The watch is `OPR-51`'s on output 0. A claw-back
still unconfirmed when the Operator wants it faster is bumped with `--replace <txid>`: the
program reads that claw-back's ordered outpoints from its own authorization record (`OPR-54`),
skips the inventory scan for them — `OPR-34` would otherwise refuse the whole inventory as
mempool-spent, which is the one exception that rule admits — composes over exactly those
outpoints at the given `--fee-rate-sat-vb`, refuses unless the new absolute fee is strictly
greater than the recorded one and inside `POL-12`, and relays; the nodes are the authority on
whether it is a replacement (`WTC-25`), and answer `UNKNOWN_INPUT` if the earlier claw-back
has confirmed or was never resident. No new backend method is needed. Help text MUST describe
this bump path, and MUST state that a claw-back is pin-less.

**OPR-72** `recover` runs with NO live federation: it parses the sealed descriptor from the
cold artifacts, identifies the recovery branch and its relative timelock, verifies maturity
per coin against a chain view, composes the 2-of-3 spend with the correct `nSequence`
(`CHN-10`), and drives signature collection to broadcast. A premature attempt MUST fail at
composition with a clear message rather than being rejected by the network as non-final.

**OPR-73** The recovery signing artifact is a PSBT file carrying every input's full previous
transaction. Each recovery-key holder MUST verify, from the descriptor backup they hold
(`OPS-23`) and their own chain view: that every input is a coin of that descriptor, that the
destination is the one the Operator named to them out of band, and that the transaction pays
nothing else; a holder asked to sign anything else refuses. The flow MUST work with the three
holders on three machines exchanging the file; a rehearsal that puts all three keys on the
Operator's laptop tests the code path and not the arrangement it depends on (`OPS-58`).

**OPR-74** `recover` MUST work from a pre-current-revision manifest (`OPR-12`) AND from the
descriptor plus a chain view with no manifest at all, because the descriptor backup is
promiscuous (`OPS-23`) and the manifest is not.

**OPR-75** Recovery is the one command that broadcasts (`OPR-1`), through its own broadcast
client outside `OPR-32`'s funnel, which admits no broadcasting method; it never talks to a
node, so loopback binding does not obstruct it.

**OPR-76** Help for every incident command MUST cite the coercion procedure's ordering
(`OPS-11`–`OPS-16`): power off the coordinator first, do nothing while captive, verify
Lockdown by `/healthz` only.

**OPR-77** A vault sealed under a revision whose program lacks a live command exits through the Recovery branch
as each coin matures, not by rotation, because rotation's sweep spends through the old
vault's Normal path, which a newer program cannot reach (`OPS-31`).

## The configurable timelock

**OPR-78** The recovery timelock is per vault, chosen at the ceremony. There is NO hard floor:
the choice stays the Operator's. On mainnet a below-default value requires a typed
confirmation containing the VALUE in human units — never a fixed word, because a wrapper
pipes a constant — and the confirmation is recorded in `ceremony-state.json` (`MAN-29`) so an
auditor sees deliberateness; the manifest carries only the value, as `MAN-5`'s convenience
field. Signet and regtest warn only. The ceremony displays the duration and the earliest
expected maturity in human units, as "earliest maturity for coins confirmed now". The template
parser's check on the timelock is a range check (`CHN-4`), not equality with a constant;
equality with the manifest is checked at `finalize` and at live-vault construction (`OPR-13`),
and every arithmetic that mentions 180 days is a default, not a rule.

**OPR-79** The timelock and the ladder ceiling (`ADR-0016`) are asked as ONE ceremony question
that displays both resulting values — the lock in days and the ceiling as a percentage with
its worst-case fee on a stated sweep — while remaining two independent manifest fields; the
ceremony MUST NOT close the pair with separate prompts, because each is only meaningful
beside the other.

## Ceremony residue

**OPR-80** An interrupted finalize can leave its private staging directory behind, holding the
same coordinator key and node secrets as the sealed output. The ceremony documentation MUST
disclose that residue and tell the Operator to inspect and remove it. A retry MAY reclaim only
a staging directory proven not to belong to a live invocation; a process id in the name is
NOT proof, because ids are reused (`MAN-32`).

**OPR-81** Every property the ceremony or the program claims to have verified with an
"independent" tool MUST name the oracle per property; the word is reserved for implementation
diversity, and "separate binary" is used where that is all the evidence provides (`OPR-57`,
`MAN-37`).
