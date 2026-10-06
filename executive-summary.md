# btc-policy — Executive Summary

*A single-file orientation to the specification set, for a reader who has never seen it.
Written 2026-09-09 against the initial extraction; re-derive any count before quoting it.*

---

## 1. What this is

`btc-policy` is a **specification for a self-hosted Bitcoin soft vault**, and it contains no code
by design. A single **Operator** holds a hardware **user key** and runs a federation of `n = 2t − 1`
**vault nodes** — five by default — each with one key and one policy engine. Coins sit in a
standard P2WSH Miniscript descriptor with two branches: the **Normal path**, the user key plus `t`
node signatures, every one of them policy-checked; and the **Recovery path**, 2-of-3 cold keys
after a 180-day relative timelock. A **coordinator** program composes transactions, operates the
user key, and relays signed requests to the nodes; the nodes assemble the signatures among
themselves and broadcast. An **escape wallet** is where every sweep goes. `DOM-11` recommends:
"The escape wallet SHOULD be multisig; single-sig is accepted." Its per-key rule is "Each escape
key MUST be generated independently on a device that holds no other vault role."

The problem it answers is that self-custody has no good answer to "what if my key is stolen, or
I am made to sign" short of covenants that do not exist. Conventional 2-of-3 policy multisig has a
structural flaw — any two user-held keys bypass the policy key — and single policy servers are one
host compromise from useless. Here, no signature path skips the checks, and the cases in which
theft remains possible are enumerated in `SEC-54`'s matrix rather than claimed away. For escape
custody it defines `E` as "spending authority under the supplied escape descriptor".

The set was extracted on 2026-09-09 from a running Rust reference implementation and then
written ahead of it, so that any implementation in any language can be built from the set
alone. The set does not track what any implementation has built; each implementation's own
repository does. Where an implementation and the set disagree, one of them is wrong.

## 2. The three decisions everything follows from

**The coordinator is trusted until the wrench and untrusted after** (`ADR-0010`, `ADR-0012`). It
never holds a federation key, never assembles, never broadcasts. What a hostile-at-wrench
coordinator can do is enumerated — censor, selectively deliver, strip fee-ladder rungs — and none
of it produces a spend the user did not sign. What a coordinator compromised BEFORE the wrench can
do is also stated, and it is the design's one accepted conditional-theft residual (§5).

**Every spend is a two-transaction ceremony** (`ADR-0008`). The user signs the spend AND a
mandatory **Escape** — a sweep of the same coins to the escape wallet — every time, as routine, so
that signing the Escape under coercion raises no suspicion. A **PIN** entered at submission
decides which one the nodes complete. The normal PIN completes the spend after a **Hold**; the
**duress PIN** silently arms the Escape.

**Duress is two independent tracks** (`ADR-0012`). The **safety track** is keyed on the duress PIN
alone plus confirmation that `t` nodes hold the request: it freezes hot-class completion and enters
**Lockdown** at a deadline `T` unconditionally — no chain view, no sweep outcome, no further
authorization can skip it. The **sweep track** is best-effort: the Escape fires at `T` if it is
admissible, and if it is not the coins stay frozen and exit through Recovery. Lockdown is
irreversible by anyone, including the Operator; the only exit is the timelocked Recovery path. The
victim can truthfully say "I cannot stop it, nobody can."

## 3. Why silence is the centrepiece, and what it costs

Under coercion an observable countermeasure endangers the person. Subject to the scope below,
**SILENCE** — a duress ceremony indistinguishable from a normal one across every observable a
node emits — is the design's load-bearing invariant, and most of the set's difficulty is its
consequences:

- both PIN digests are evaluated on every SpendRequest, in fixed order, with a constant-time verdict,
  because a short-circuit costs the duress PIN one extra Argon2 evaluation, which is measurable;
- ingress does identical work under both PINs: validate both transactions, sign both partials,
  write a same-shaped schedule record, stage for peers — the PIN flips one internal bit;
- arming happens off the response path, on the peer-receipt path, once `t` nodes hold the
  request, and the commit does identical store work whether or not it arms;
- every read surface — `/healthz`, `/pending`, `/events` — carries nothing a pre-`T` duress
  request could change, and that byte-identity is asserted by tests;
- the deadline `T` is pulled earlier by any pending hot spend, so a frozen spend never becomes
  visibly late under one PIN and on time under the other.

This guarantee is conditional on `SEC-10`'s "release-history premise": "no node has run a
compromised release while the current PINs were in use". Under that premise, silence holds
against a coordinator that turns hostile AT the wrench, across the listed observables. A
compromised node sees the PIN. End-to-end wall-clock timing has no hard gate, because the
measurement noise exceeded the effect it was meant to detect.

## 4. What is genuinely hard

**The release gate, not the holder count, is the safety proof.** With `n = 2t − 1` a set of `t`
holders can contain one honest member, so counting receipts proves nothing about who froze. What
holds is that no partial signature leaves a node before its candidate's authorized fire event,
every gate that blocks arming also blocks signing, and a hot partial releases only when the node
is not armed — under the same lock that sets the freeze. No honest node ever releases a coerced
partial; only `t − 1` compromised ones can; that is never a quorum.

**Clocks.** Three of them: wall time for signed expiries, a rollback-guarded effective time for
freshness, and a process-monotonic clock for residency. A forward wall-clock step once erased a
node's own arm intent on an untrusted peer receipt (`DEF-1`); the repair fixes every Carrier
deadline at acceptance from the monotonic clock and makes wall readings attempt signals only. A
receiver's freshness high-water that latches forward can still blackhole an honest peer for
unbounded real time (`F3`).

**Determinism across the honest set.** Every node must pick the same fee-bump rung from the same
chain, or partials cover different transactions and no rung reaches `t`. The one fee signal is the
median of the block at `tip − (tip mod 6)`, quantised down to 5 sat/vB; no mempool reading may
enter it.

**Reboot-death.** Every node runs from tmpfs and starts exactly once; a reboot leaves a bare
machine. That single decision is load-bearing for five separate RAM-only security states, and
whether it survives operational attrition is the open question the rollout ladder is designed to
answer (`F8`).

## 5. What a builder must validate, and what stays open

**The conformance checklist** (`15-conformance-checklist.md`) is tiered: the BLOCKING items gate
the first sealed vault, PRE-SCALE gates a second vault or a second implementation, and DEFERRED
gates the lift of the dust caps and the alpha. A harness can be blind to a fault it does not
construct (`DEF-15`); read any green scorecard as evidence about what its scenarios construct.

**The rollout ladder** (`13-operations-and-rollout.md`) moves value last: ten stages from five
daemons on one machine to a public alpha, every mainnet rung dust-capped with an independent
observer, and one external human review at stage 9 gating the lift of the caps (`F18`).

**The accepted residuals a reader must know before trusting anything:** a coordinator compromised
before the wrench reads the normal PIN and nullifies duress — its mitigations are a dedicated
coordinator host, reproducible builds and hardware user signing, and none addresses a wrench
that begins mid-spend (`SEC-42`); `t` compromised nodes plus the user key is theft by
construction; escape-destination theft follows `SEC-54`'s authority boundary: "if the attacker
retains `E`, a sweep is Theft even when the Operator has lost `E`"; a pending hot
spend censored from `t` nodes can complete, within the
acceptance-time admission bound of `POL-20`, which is not a rolling completion-loss bound; the
delay before Lockdown at `T` has no finite bound, only a bounded consequence (`F13`); no
external human has reviewed the system (`F18`).

## 6. How to read the set

Start with `00-overview.md`, `01-domain-model.md`, then `05-duress-and-lockdown.md` and
`06-node-channel.md`. Read `ADR-0012` before `05`. Read `16-open-findings.md` before building
anything, and `17-operator-program.md` before building the coordinator side. The byte-exact
contract an implementation in any language must reproduce is
`02-onchain-contract.md`, `07-node-api.md` and `08-wire-contract.md`; the vectors in the last are
executed by `tools/check_vectors.py`, so the specification itself is what a reimplementation is
checked against.
