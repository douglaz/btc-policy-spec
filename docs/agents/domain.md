# Domain Docs

How the engineering skills should consume this repo's domain documentation when exploring it.

## Before exploring, read these

- **`CONTEXT.md`** at the repo root: the glossary, single context.
- **`docs/adr/`**: read ADRs that touch the area you're about to work in. `ADR-0012` consolidates
  the design decisions; read it before `05-duress-and-lockdown.md`.

## Use the glossary's vocabulary

When your output names a domain concept (in a bead title, a theorem name, a finding), use the term
as defined in `CONTEXT.md`. Don't drift to synonyms the glossary explicitly avoids, and don't use a
word from its banned list.

If the concept you need isn't in the glossary yet, that's a signal: either you're inventing language
the project doesn't use (reconsider) or there's a real gap (note it for `/domain-modeling`).

## Flag ADR conflicts

If your output contradicts an existing ADR, surface it explicitly rather than silently overriding:

> _Contradicts ADR-0020 (every confirmed duress Escape is selected), but worth reopening because…_
