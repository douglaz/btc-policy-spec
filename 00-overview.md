# 00 — Overview

## Problem

Bitcoin self-custody has no good answer to "what happens when my key is stolen, or when I am
made to sign" short of covenants that are not activated. The existing answers either trust a
single company's off-chain policy, trust a single self-hosted policy server that is one host
compromise away from useless, or accept the operational weight of a presigned reactive vault.
Conventional 2-of-3 "policy multisig" has a structural flaw: any two user-held keys bypass the
policy key entirely.

The system specified here is a **soft vault**: coins sit in a standard P2WSH Miniscript
descriptor with two branches. The **Normal path** needs the user's key plus a threshold `t` of
`n` federation nodes, each of which holds one key and one policy engine and independently
refuses to sign any transaction outside the vault's immutable policy. The **Recovery path**
needs 2-of-3 cold recovery keys after a relative timelock, and is the only exit once the
federation has locked down. A spend is relayed to the nodes by a **coordinator** that operates
the user key and is trusted only until the moment the user is coerced; from that moment the
nodes trust nothing it says. A second, distinct **duress PIN** entered under coercion looks
identical to the normal one and silently arms a sweep of the whole vault to an independent
escape wallet, followed by an unconditional, irreversible lockdown of the federation.

Everything runs on today's consensus rules. There is no covenant, and no covenant upgrade
path.

## Design goals

**OVR-1** The system MUST enforce spending policy at a `t`-of-`n` threshold of independent
policy engines, not at a single co-signer. No signature path MAY bypass the policy checks
(`POL-1`), and the theft cases the design accepts, with their prerequisites, are owned by
`SEC-54`; an implementation MUST NOT claim stronger protection than that matrix states.

**OVR-2** The coordinator MUST be a relay. It composes transactions, operates the user key,
authenticates its requests, and pulls alerts; it MUST NOT combine partial signatures, finalize,
or broadcast, and it MUST NOT be able to cause any transaction to be broadcast that the user did
not sign (`ADR-0010`, `ADR-0012`; the mechanism is `SPN-1` and `NCH-1`).

**OVR-3** The federation MUST assemble and broadcast every spend itself, over an authenticated
node-to-node channel that carries signatures and assembly and never policy (`ADR-0011`,
`06-node-channel.md`).

**OVR-4** A spend to the hot wallet MUST wait out a node-driven **Hold** before it can complete,
during which every node names it on a pull surface and a claw-back of the same coins is its
implicit cancellation (`ADR-0004`, `SPN-30`, `API-21`, `CHN-35`).

**OVR-5** The duress response MUST be **silent** across every observable a node emits — response
bytes, timing class, every read surface, peer effects — and MUST be **unconditional**: once the
federation has armed, Lockdown at the deadline `T` depends on no chain view, no sweep outcome,
and no further authorization (`ADR-0012`; `DUR-1`, `DUR-7`, `SEC-10`). This is the single most
important pair of requirements in the set.

**OVR-6** Every mutable node state that bears on safety MUST be RAM-only and die with the
process; a rebooted node is a dead node and never rejoins its vault (`ADR-0007`,
`11-state-and-persistence.md`).

**OVR-7** Every parameter that decides what the federation will sign MUST be fixed once, at a
witnessed setup ceremony, sealed into an immutable manifest, and verified by every node at
startup. A change to any of them is a new vault (`ADR-0005`, `ADR-0013`,
`09-manifest-config-ceremony.md`).

**OVR-8** Loss that the design cannot prevent MUST be named with the limits actually proven.
The hot wallet is the declared risk budget, with sealed per-transaction and admission controls.
`POL-20` states: "The Hot budget provides an **acceptance-time admission bound**, not a rolling
completion-loss bound." Every residual belongs in `12-security-requirements.md`.

**OVR-9** Every honest node MUST reach the same verdict, and select the same fee-bump rung, from
the same chain state. Policy evaluation is pure (`POL-1`); fee signals are consensus-observable
and quantised (`DUR-30`); nothing a node decides may depend on its mempool, its wall clock's
opinion of another node, or a peer's assertion. The scope is "from the same chain state": which
duress Escapes a node has confirmed is a fact of delivery order, not of the chain, so `DUR-10`
does not ask nodes to agree on it — every confirmed Escape is selected and gated on its own
(`ADR-0020`), and the verdict this requirement binds is each Escape's admissibility, which every
honest node does compute identically from the same tip.

**OVR-10** The system MUST fail closed. An unreadable chain, a poisoned lock, a panic, a
malformed input, an unknown state: each refuses or locks down, and funds route to the Recovery
path rather than moving (`DUR-9`, `STO-10`).

## System context

```
                 user key (hardware in production; software in every current driver)
                              │
                              ▼
   ┌──────────────────────────────────────┐        pulls alerts, pending ids, liveness
   │  COORDINATOR (vault-cli)             │◄──────────────────────────────────────────┐
   │  composes spend + mandatory escape,  │                                           │
   │  user signs both, coordinator signs  │   POST /sign  {spend | refresh | clawback}│
   │  the request, offers it to nodes in  ├──────────────────────────────────────────►│
   │  order until one accepts; the nodes  │                                           │
   │  fan it out. Trusted until wrench.   │                                           │
   └──────────────────────────────────────┘                                           │
                                                                                      │
        ┌──────────── n = 2t − 1 VAULT NODES, each on its own host ─────────────┐     │
        │                                                                       │     │
        │   ┌─────────────┐   POST /channel    ┌─────────────┐                  │     │
        │   │ node 0      │◄──────────────────►│ node 1      │ ...  node n−1    │◄────┘
        │   │ one key     │  request relay,    │ one key     │                  │
        │   │ one policy  │  partial sigs,     │ one policy  │                  │
        │   │ engine      │  holder receipts   │ engine      │                  │
        │   │ watchtower  │                    │ watchtower  │                  │
        │   └──────┬──────┘                    └──────┬──────┘                  │
        │          │ own bitcoind                     │ own bitcoind            │
        └──────────┼─────────────────────────────────┼──────────────────────────┘
                   ▼                                  ▼
                              Bitcoin (signet / mainnet / regtest)
```

Every node implements this set and holds the same sealed manifest; the code need not be the
same, and a federation of more than one implementation is the intent (`OVR-16`, `OVR-17`). A
node signs its partial at
ingress, keeps it until the candidate's authorized fire event, then releases it to peers; the
first node holding `t` partials combines and broadcasts through its own chain backend. Every
node watches the chain for spends it never authorized.

## Vocabulary

Terms are defined once, in `CONTEXT.md`. The ones this document uses without definition:
**vault**, **Normal path**, **Recovery path**, **federation**, **vault node**, **coordinator**,
**user key**, **escape wallet**, **recovery keyset**, **Hold**, **duress PIN**, **Lockdown**,
**Carrier**, **candidate**, **transaction class**, **manifest**, **sealed host**.

## Non-goals

**OVR-11** Covenants are out of scope. There is no covenant backend seam and no
covenant-readiness requirement; this is a soft vault on today's consensus rules.

**OVR-12** Dynamic policy is out of scope, permanently. Once a vault is sealed there is no
mechanism to change its allowlist, caps, timelock, keys or membership. Changing any of them
means provisioning a successor vault and moving the coins through the Normal path
(`13-operations-and-rollout.md` §Upgrade and rotation).

**OVR-13** Silence against a compromised node is out of scope. A node sees the submitted PIN in
plaintext and can tell which one was used; the guarantee is silence against an adversary who
holds the coordinator and the physical scene but no node (`SEC-10`). Hiding the duress bit from
nodes would need threshold cryptography and is explicitly not attempted.

**OVR-14** Preventing a coordinator compromised BEFORE coercion from substituting the normal PIN
is out of scope. It is an accepted conditional-theft residual, constrained by the Hot-budget
admission controls and the Hold, with no rolling completion-loss guarantee (`POL-20`: "No
replacement rolling completion-loss formula is specified."). Its only true prevention is a
device-bound PIN that no supported hardware offers (`SEC-42`).

**OVR-15** Restart of a node is out of scope. A node starts exactly once in its life; a reboot
leaves a bare machine (`STO-1`). Whether that model survives operational attrition is an open
question the rollout ladder is designed to answer (`16-open-findings.md` `F8`).

**OVR-16** Any transport other than the one this set fixes is out of scope for interoperability.
A node in another language interoperates if and only if it reproduces the byte encodings and
tagged hashes of `08-wire-contract.md`, the JSON field names and status codes of
`07-node-api.md`, and the descriptor template of `02-onchain-contract.md`.

## Implementations

**OVR-17** This set specifies the system and does not track which implementation has built
which part of it. Every implementation — the Rust reference at `btc-policy-rust`, and any other —
records its own status, gaps and defects in its own repository, against the identifiers here.
An implementer MUST NOT read a requirement's presence as evidence that any implementation
satisfies it; that evidence is a conformance run (`15-conformance-checklist.md`) recorded by the
implementation. The spec is meant to stay ahead of every implementation; where building one
shows the spec is missing a rule, the rule is added here first, then built.
