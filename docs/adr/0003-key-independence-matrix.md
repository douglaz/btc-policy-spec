# Key-independence matrix, enforced best-effort

The escape wallet receives the funds precisely when the user key may be stolen. If an attacker
can derive a signing threshold of escape keys from the user's seed, the sweep delivers the
vault to them. Independence is therefore a load-bearing assumption for the duress guarantee,
not key hygiene. Each escape key needs that independence even when compromise of one key alone
would not give spending authority. The same separation from recovery keys matters because the
escape wallet is the race destination against stolen recovery keys. Recovery keys must survive
user-key loss and each other's failure domains; the hot wallet is the declared risk budget.

Historically the reference ceremony added its own single-sig generation step and a separate
escape bundle to prevent the honest-lazy one-device-exported-both case. The 2026-10-05 amendment
accepts an operator-supplied multisig bundle without weakening per-key independence. The current
owners are `DOM-11`: "Each escape key MUST be generated independently on a device that holds no
other vault role", and `MAN-26`: "The Operator MAY construct this bundle using their own
multisig tooling". The bundle format and single-sig compatibility path live in `MAN-26`.

The ceremony's check is a refusal, not a warning: `MAN-27` requires it to "run the independence
check (`MAN-28`) and refuse on any violation". `MAN-28` requires the check to "cover every
escape-wallet cosigner" and records "every compared key and its role". Public-key equality is
what can catch the user's key at a scanned escape index when definite vault keys carry no
origin. A fingerprint comparison against a bare public key cannot detect that relationship.
Fingerprint comparisons between ranged wallets are defence in depth; they are not proof that
seeds or custody are independent.

The procedure carries what code cannot check. `MAN-28` states: "same-seed keys at unrelated
paths are unlinkable" and "device separation is unverifiable". Origin metadata cannot establish
truth about the source seed, and a public extended key cannot reveal undisclosed ancestors.
The report exposes those limits instead of turning a passed check into a seed-independence
claim. Threshold custody and loss are separate questions, owned by `OPS-60` and `SEC-54`, with
the accepted decision recorded in `ADR-0021`.
