# 01 — Domain model

The entities, the roles, the keys, and the state each node holds. Definitions of the words
themselves are in `CONTEXT.md`; this document states what is REQUIRED of each thing.

## Roles

### Operator

The human who runs a vault: funds it, authorizes spends, watches alerts, and drives Recovery if
it comes to that. Distinct from the user key they hold and from the coordinator, which is
infrastructure.

**DOM-1** The Operator is the party every ceremony question is addressed to and every runbook
instruction is written for. Nothing in this set assumes a second human is available during an
incident.

### Coordinator

The program that operates the user key, composes transactions, signs requests with the
**coordinator auth key**, relays them to every node, and pulls alerts.

**DOM-2** The coordinator is **trusted until the wrench attack, untrusted after**. Requirements
that hold against a hostile coordinator are written for a coordinator that turns hostile AT the
moment of coercion, holding the coordinator auth key but no history of the normal PIN. That
history boundary depends on `SEC-10`'s "release-history premise". A coordinator compromised
BEFORE coercion is the accepted residual `SEC-42`.

**DOM-3** The coordinator MUST hold no federation key, MUST NOT assemble partial signatures,
MUST NOT hold a finalizable transaction, and MUST NOT broadcast. What it can do post-wrench is
enumerated in `SEC-21`: censor, selectively deliver, strip fee-ladder rungs and re-sign. It
cannot redirect funds, cause arbitrary bytes to be broadcast, or produce a new
attacker-authorized spend.

**DOM-4** The coordinator MUST NOT persist the PIN. It is entered per request, relayed in the
request body, and discarded (`SEC-3`).

### Vault node

A daemon holding exactly one federation signing key and one policy engine.

**DOM-5** Each node MUST independently re-run every gate on every request it sees — coordinator
authentication, freshness, the PIN, the chain preflight, the user signature, the transaction
class, the Hot budget — and MUST NOT sign because a peer or the coordinator said so. Peer
messages carry no authority over signing (`NCH-3`, the signing-oracle prohibition).

**DOM-6** Each node MUST perform watchtower duty against its own chain view (`10-watchtower-and-chain.md`).
There is no separate watchtower service.

**DOM-7** Nodes are **policy-isolated, not network-isolated**: they exchange partial signatures,
relayed requests and holder receipts over the node channel, and share no policy state — no
velocity counters, no verdict cache, no gossip. Every stateful check is computed per node from
that node's own ledger.

### Federation

The set of `n` vault nodes.

**DOM-8** The federation MUST have exactly `n = 2t − 1` members with `t ≥ 2` (`CHN-2`). The
default and recommended shape is 3-of-5.

**DOM-9** No correlation class — a hosting provider account, a network block, a physical
location, a household, an operator — MAY host `t` nodes (`ADR-0009`, `SEC-28`). Rollout stages
2–5 waive this under `ADR-0015` with capped funds.

## Keys and wallets

**DOM-10** A vault involves these key roles, and the independence relation between them is
load-bearing, not hygiene:

| Key | Holder | Count | Role |
|---|---|---|---|
| User key | Operator, hardware in production | 1 | Mandatory on every Normal-path spend |
| Federation node key | each node, RAM-only, derived at start | `n` | `t` of them on every Normal-path spend |
| Recovery key | third parties, cold | 3 | 2 of 3 spend the Recovery path after the timelock |
| Escape wallet key | Operator, single-sig, offline, its own device | 1 | Receives every sweep |
| Hot wallet key | Operator's daily wallet | 1 | Allowlisted destination; the risk budget |
| Coordinator auth key | the coordinator host | 1 | Signs every request; pinned in the manifest |
| Channel key | each node, RAM-only, derived from the node key | `n` | Signs every channel envelope |
| Node preimage | each node's operator, paper, destroyed after start | `n` | Derives the node key |

**DOM-11** The escape wallet's keys MUST be generated independently, on a device that holds no
other vault role. A shared-seed escape converts duress into theft: a post-wrench attacker holding
the user key would control the sweep's destination (`ADR-0003`, `ADR-0012`). The ceremony
refuses any detectable overlap (`MAN-28`); what code cannot detect, the procedure carries.

**DOM-12** The recovery keys MUST be distinct from every other role and from each other, and
SHOULD be distributed socially and geographically. The recovery keyset doubles as the
inheritance mechanism.

**DOM-13** No machine MAY ever hold two federation node secrets (`MAN-24`).

**DOM-14** The hot wallet carries no independence requirement. It is the declared risk budget,
and an attacker who holds its keys owns whatever the Hot budget lets through.

## The vault

**DOM-15** A vault is one descriptor (`CHN-1`), one manifest (`MAN-1`), and `n` node
configurations derived from them. Its identity is `wallet_id = SHA256(canonical descriptor
string)` (`CHN-6`). Two vaults with different descriptors are unrelated even if they share every
key but one.

**DOM-16** A vault's policy is a **closed, hardcoded set of checks parameterized by sealed
values**, not a rule engine. Adding a check means shipping code and, because sealed hosts take
no upgrade in place, a new vault.

## Requests

**DOM-17** There are exactly three request kinds a node accepts from the coordinator:

- a **SpendRequest** — `{spend, escape, escape_bumps, pin, nonce, expiry, policy_version,
  coord_sig}`: a user-signed hot spend, a user-signed **mandatory Escape** sweeping the same
  coins to the escape wallet, an optional pre-signed fee ladder for that Escape, and a PIN;
- a **RefreshRequest** — `{refresh, nonce, expiry, policy_version, coord_sig}`: a user-signed
  self-spend of vault coins back to the vault, with no PIN and no Escape;
- a **ClawbackRequest** — `{clawback, nonce, expiry, policy_version, coord_sig}`: a user-signed
  sweep of vault coins to the escape wallet, with no PIN and no Escape (`ADR-0022`).

All three are coordinator-signed and fresh (`SPN-10`). The exact shapes are `API-10` and `WIR-7`.

**DOM-18** A SpendRequest MUST carry the Escape for its spend. A request
without one is undecodable (`API-10`), so a hostile coordinator cannot strip the Escape to force
a lockdown-only outcome; it can only drop the whole request, which is total censorship.

## Transaction classes

**DOM-19** Every spend has exactly one **class**, derived by each node from the spend's outputs
and never from a coordinator label (`CHN-30`):

| Class | Predicate | Behaviour |
|---|---|---|
| **hot** | every destination output pays a hot-allowlist descriptor; vault change permitted | signed at ingress, partial held for the Hold, combined and broadcast at Hold expiry; frozen under duress |
| **escape** | every destination output pays the escape descriptor; vault change permitted | the class of every SpendRequest's mandatory Escape, and of a **claw-back** — submitted only as a ClawbackRequest; instant, pin-less, bounded by `POL-12` alone (`ADR-0022`) |
| **refresh** | every output pays the vault | submitted only as a RefreshRequest; instant, pin-less, bounded |

A spend with destination outputs of more than one class, or with any output no descriptor
recognises, has no class and is refused.

## The state a node holds

All of it is RAM-only (`STO-1`). Named here so later documents can cite the container rather
than re-describe it.

**DOM-20** A node holds, under one **sign lock**:

- the **replay log** — verdicts indexed by commitment id, with matching keys owned by `SPN-23`;
- the **coordinator nonce log** — every accepted nonce with its wall expiry and, for
  channel-mode spends, its monotonic Carrier deadline `D`; a non-decreasing high-water mark
  (`SPN-11`–`SPN-14`);
- the **pending log** — commitment id → expiry for every accepted hot-class spend still waiting
  out its Hold (`SPN-30`);
- the **PIN attempt budget** (`MAN-23`);
- the **in-flight spend marker** consulted by refresh subordination (`SPN-31`).

**DOM-21** A node holds, under one **channel store lock**:

- the **candidate registry** — every signed-but-withheld spend, escape, refresh and claw-back, each with its
  fire window, its ladder, its partials and its flags (`SPN-36`);
- the **Armed overlay** — whether the node is armed, the deadline `T`, the selected sweeps
  (`DUR-10`);
- the **arm intents** and **Carrier memos** keyed by carrier id and coordinator nonce
  (`NCH-32`);
- the **Hot-budget ledger** of reservations (`POL-21`);
- the **ingress guards** — the freshness high-water, seen envelope nonces, per-peer quotas
  (`NCH-12`–`NCH-15`).

**DOM-22** A node holds, independently of both locks: the **alert queue** (`WTC-20`), the
**vault-authorized txid set** the watchtower recognises (`WTC-18`), the **Lockdown latch**
(`DUR-7`), the **deadline heartbeat** (`API-19`), and the **vault-unspent cache** (`WTC-5`).

**DOM-23** Nothing in `DOM-20`–`DOM-22` MAY be written to durable storage. The one exception is
the two extended attributes on the tmpfs config inode that carry the process-generation marker
and the Lockdown latch, which have exactly the RAM disk's durability (`STO-4`).

## Time

**DOM-24** Three clocks exist and MUST NOT be confused:

- **wall time** — unix seconds from the host clock; the authority for signed expiries and for
  every deadline compared against a coordinator-signed instant;
- **effective time** — `max(nonce-log high-water, wall)`; the rollback-guarded lower bound every
  freshness decision uses (`SPN-13`);
- **monotonic time** — elapsed seconds since the channel was constructed, the **HotClock**; the
  authority for the Hot-budget window and for Carrier residency (`POL-22`, `NCH-33`).

A wall reading may refuse an attempt; only monotonic time may retire Carrier state
(`NCH-35`).
