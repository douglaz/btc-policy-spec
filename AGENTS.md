# AGENTS.md

Specifications only. `tools/` holds the gates that check them; `.github/workflows/` runs the same
script. Nothing that implements the specified system belongs here. The Rust reference
implementation lives in a separate repository (`btc-policy-rust`), and this set is written so that an
implementation in any language can be checked against it without reading that one.

## Gates

`nix develop --command bash tools/check-all.sh`, before you start and again before you report
done. Run it unpiped — a pipe reports the pipeline's status, not the gate's, which is why
`check-all.sh` captures each exit code directly. The shell is required: the formal gate needs
Lean, the vector gate needs two Python libraries, and a missing toolchain is a red gate, not a
skipped one.

A formalized clause's home is its Lean declaration in `tools/formal/`, tagged `@[req "SPN-38"]`
(`ADR-0023`). Change the declaration and the Markdown together; a theorem that stops proving is
the gate telling you the amendment contradicts a property the set claims — read the theorem
before weakening it, since weakening a statement to make a proof pass is a semantic change like
any other. A figure inline in a sentence is held to the value its declaration emits by
`check_copies.py`; a table between `<!-- formal: … -->` markers is rewritten from its declaration
by `check_regions.py --write`. Every semantic choice a dated amendment changed is a guard
parameter with a `current` value; the module that owns the parameter holds the trace under each
value, and `Exhibits.lean` holds every theorem over `current`, so a flip goes red there and
nowhere else. Never put a `CNF` identifier in `tools/formal/`.

Green is evidence only because the workflow breaks a document on every run and asserts the gates
reject it — one negative-control step per gate that has one, and `.github/workflows/gates.yml`
holds the list rather than this sentence. The reference implementation's launch gate once ran red
for dozens of consecutive runs without anyone noticing, which is why.

Two gates are executable specification rather than text checks: `check_vectors.py` recomputes
every published digest from its published preimage, and the formal layer derives every stated
figure from the rule that produces it, over every input where the rule admits one. A vector or a
number that lives only in prose is one that can be wrong without anything failing.

## Writing a requirement

The rule and the record are two edits with two different failure rates. Land the rule; write the
record after.

**Quote the sentence.** A claim about what another requirement says carries that requirement's own
words. `` `NCH-12` says "the window is [now − 300, now + 60]" `` is checkable; "`NCH-12` forbids a
wider window" is an assertion.

**Cite the owner.** One rule, one home; everywhere else points at it. The reference project's
bead `btc-policy-0ip` is the record of what happens otherwise: the manifest preimage field list was
copied into eight documents and drifted in three of them, one of which was two fields short while
instructing reimplementers to work from it. **Arguments have owners too** — re-explaining a rule in
a second document is how a second normative copy gets written.

**Cite the list; let it hold the number.** A count written into prose is wrong the first time either
end moves.

**Cite the code by identifier, never by line.** The reference implementation is named by crate,
module and function (`vault-node`, `channel::confirm_carrier`), never by `file.rs:NNN` — line
numbers went stale in the reference repository's own ADRs within days.

**Completion:** every sentence asserting what another requirement says carries its quote, and every
list or count names its source instead of restating it.

## Agent skills

### Issue tracker

Beads (`br`), local-first in `.beads/`, committed with the specs, prefix `bps`. See
`docs/agents/issue-tracker.md`. Findings in `16-open-findings.md` are not beads.

### Triage labels

The five default roles as `br` labels. See `docs/agents/triage-labels.md`.

### Domain docs

Single-context: `CONTEXT.md` and `docs/adr/` at the root. See `docs/agents/domain.md`.

## Conventions with a home already

- Identifiers, retention, withdrawn ids → `README.md`, *Requirement conventions*.
- Vocabulary, overloaded and banned words → `CONTEXT.md`.
- Decisions and what was rejected to reach them → `docs/adr/`.
- What an implementation must demonstrate → `15-conformance-checklist.md`.
- What the reference implementation got wrong, as prohibitions → `14-known-defects.md`.
