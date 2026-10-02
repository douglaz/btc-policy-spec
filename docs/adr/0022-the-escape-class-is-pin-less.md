# The escape class is pin-less, and the two-leg shape goes

Status: accepted 2026-09-14, decided with the Operator in one session. Specification-repository
decision; moves `SEC-54` row 6 to Theft as accepted by `ADR-0021` and repairs rows L4 and L5. The
requirement edits landed the same day: `CHN-35`, `SPN-50`, `SPN-51`, `DUR-36`, `API-24`,
`CNF-146`, and the withdrawal of `CHN-33`, `SPN-40`, `DUR-17`, `OPR-26`, `OPR-70` and `OPR-71`.

An escape-class spend today is a full SpendRequest: it carries a PIN, goes through the Carrier,
and pairs with a mandatory Escape that `CHN-33` forces to be a distinct, input-disjoint residual.
`ADR-0012` calls it "the one remaining instant-class pin ceremony" and its two-slot record "a
self-defeating exception". The PIN on it defended one thing — the vault-to-escape-wallet path
against an attacker holding the user key and the coordinator credential but no PIN — and bought
one thing — a single request meaning "sweep these now, lock down at `T`". `ADR-0021` accepted
giving up the first. The second is worth less than it costs: the residual that made it work
almost never fires (`F55`), and the shape carries a role-swap residual (`OPR-70`), an open
ladder question (`F44`), and a claw-back that a one-coin vault cannot perform (`OPR-71`).

The Operator's framing: an escape-class transaction is a sweep to the escape wallet. It is not a
normal spend, so it needs no PIN. It is refresh's sibling.

## Decisions

**1. The escape class inherits none of refresh's four guards.** (Decided 2026-09-14.)
Not subordination (`SPN-45`): the claw-back of `OPS-19` is "an unauthorized spend is pending,
spend its inputs first", which a subordinated request could never do, and a sweep that spends
the armed Escape's inputs pays the same wallet, so it is the sweep firing early. Not the age
interval (`SPN-46`): coins that leave the vault cannot be swept again. Not the sealed feerate
cap (`SPN-47`): refresh needs it because the burn repeats every interval; a sweep is one-shot,
an attacker with the user key and the credential burns at most `POL-12`'s 10% once and hands the
rest to the Operator's escape wallet, and an emergency sweep may need to outbid a thief. Not the
24-input cap (`SPN-44`): it exists because a per-vsize fee cap let the attacker choose the vsize,
and a percentage cap does not. It keeps everything else refresh has: pin-less, no Carrier hold,
fires at ingress, born open, `t` partials, combined and broadcast by the nodes, relayed to
peers, its txid in the vault-authorized set, never touching the PIN budget or the Armed overlay,
so it cannot be a duress probe (`SPN-49`).

**2. It is called the claw-back, on the wire `clawback`.** (Decided 2026-09-14.) The glossary's
**Claw-back** already named the normal-PIN escape-class spend this request replaces, so the word
moves with the thing. On the wire it is a third variant beside `spend` and `refresh`, with a
refresh's fields — the PSBT, nonce, expiry, `policy_version`, coordinator signature — under a
new class byte in the coordinator-signature preimage. The operator command `escape` becomes
`clawback`; its known-outpoint contract stays, minus the residual. `sweep` was rejected because
it would make one word mean the request and the firing at `T`; `escape` because it would make
one word mean the request and the transaction paired with a hot spend. The hot spend's
mandatory Escape and the duress path are untouched.

**3. Its transaction is any set of vault coins paying every output to the escape descriptor,
with NO vault change, under `POL-12`'s cap, signalling BIP125.** (Decided 2026-09-14; corrected
the same day by review.) No minimum input count and no disjointness: a one-coin vault claws
back its one coin, which deletes `OPR-71`'s limitation and closes the consolidation half of
`F1`. The decision as first taken permitted vault change as "legal, pointless"; a reviewer
showed it was neither: with change permitted, an attacker holding the user key and the
credential pays a little to the escape wallet, burns `POL-12`'s ten percent, returns the rest
as change, waits a block and repeats, so the "one-shot" burn on which decision 1 rests was
false. `CHN-35` therefore refuses any vault-derived output, and the burn is one-shot because
every swept coin leaves. "Confirmed" in the first draft bound the node; it now binds only the
composer's inventory (`OPR-68`) — the node tolerates an unconfirmed prevout at ingress as on any
spend (`SPN-25`) and admits it at fire time only as a vault-authorized resident parent
(`WTC-24`), which is the existing spend machinery and no new check. Every input sets
`nSequence` to `0xfffffffd` and `WTC-25` admits a higher-fee claw-back over a resident one of
the same coins as a replacement, exactly as `ADR-0019` gave refresh; the operator program's
bump path is `clawback --replace` over its own recorded outpoints (`OPR-69`), since its
inventory rule (`OPR-34`) would otherwise refuse the mempool-spent coins.

**4. It crosses the user-signer seam as a third arm, and the seam's freeze becomes three
arms.** (Decided 2026-09-14.) `OPR-20` froze the seam at Spend and Refresh so a hardware signer
never needs a retrofit. A claw-back is one PSBT like a refresh, but a signer must display "this
pays the escape wallet", and `OPR-22` already requires it to derive the class from sealed state
rather than trust the label. `Clawback { wallet_id, ClawbackAuthorization { clawback } }` is
the smallest change that keeps the label truthful. Reusing the Refresh arm was rejected because
an arm named Refresh would carry a transaction that empties the vault — the unlabelled-PSBT
problem `OPR-40` names. A generic single-PSBT arm was rejected because it renames an arm the
freeze protects for no gain over a third one.

## Consequences

**A hot spend's mandatory Escape and the whole duress path are untouched.** Every SpendRequest is
now exactly a hot spend plus its Escape; the `(escape, escape)` group of `CHN-23` goes, and with
it `CHN-33`, the residual, `SPN-40`, `DUR-17`'s two-slot record, `DUR-22`'s escape-class clause,
`OPR-25`'s second shape, `OPR-26`, `OPR-70`'s role-swap residual, the swap in `SEC-21`'s list of
a post-wrench coordinator's powers, `OPR-71`, and `OPS-15`'s definition. `F44` and `F55` close:
there is no residual to ladder or to window. The consolidation half of `F1` closes.

**The armed node signs a claw-back.** Between arm and `T` the node is frozen for hot-class
finalization only (`DUR-11`); a claw-back fires at ingress under both the armed and the idle
state, so it is pin-uniform. After Lockdown it is refused like everything else (`SPN-43` runs the
Lockdown checks first). A claw-back that spends the armed Escape's inputs during the window is
the sweep firing early to the same wallet.

**One combination is lost: "sweep these now, lock down at `T`" as one request.** An Operator who
wants both claws back everything, after which Lockdown guards nothing, or submits a hot spend
under the duress PIN. Accepted: the combination was carried by a residual that fired only by
luck of block timing (`F55`).

**A refresh and a claw-back are the two pin-less classes, and the class table says which guards
each carries.** Refresh: subordination, age interval, sealed feerate cap, 24-input cap, because
the coins return to the vault and the burn repeats. Claw-back: `POL-12` only, because the coins
leave.

**On the wire, a third request variant and a third class byte in the coordinator-signature
preimage.** No published vector changes, so this is not a manifest revision (`MAN-3`); the new
vector is published beside the refresh one. A node that does not implement the variant refuses
it as an unknown variant (`API-10`), which is the correct behaviour in a federation that has
never existed below the current revision.

**`SEC-54` row 6 moves to Theft**, as `ADR-0021` accepted, and rows L4 and L5 gain their
same-day remedy: a forgotten PIN is cured by a claw-back and a new ceremony, with neither PIN
and without the recovery holders.

## Alternatives rejected

**Keep the two-leg shape and fix the residual's window** (`F55`'s second and third candidates).
Rejected: every fix kept a residual that exists only to satisfy a pairing rule the claw-back has
no use for, and kept the role-swap residual, the ladder question and the one-coin limitation
with it. Deleting the residual removed four open items at once.

**Keep the PIN on the claw-back and make only the residual optional.** Rejected: the PIN on this
path defended one cell of `SEC-54` against an attacker who had already defeated escape-key
custody, and cost the Operator the same-day remedy for a forgotten PIN.

**Subordinate the claw-back to pending spends, as refresh is.** Rejected: it would make the
claw-back unable to claw back. The reverse holds, though: a claw-back claims `SPN-31`'s
in-flight marker like a spend, so a refresh cannot register during its preflight and consume
its input (`SPN-45`); a reviewer found that race, `DEF-7`'s, reopened for the emergency path.

**Enforce "confirmed inputs" at the node with a new lookup and refusal code.** Proposed by one
reviewer and rejected in favour of the other's: the spend path's existing tolerance at ingress
and ancestry check at fire time already decide the case, and a claw-back chaining off a
resident refresh's output is a legitimate emergency sweep.
