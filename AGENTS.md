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
nowhere else. A planted mutation's control asserts errors in `Exhibits.lean` only, stubbing any
owning proof the plant breaks first. Never put a `CNF` identifier in `tools/formal/`.

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

**Name the premises.** A claim that a property holds — silence, a bound, a floor — carries, beside
it, the premises its theorem takes, in the theorem's words; a claim no theorem carries says so.
`SEC-10` says it for silence: "The **scope of SILENCE** MUST be stated wherever it is claimed".
This is the same rule for every claim. Beads `bps-id2`, `bps-xyu` and `bps-amt` are the record of
what happens otherwise: a bound whose theorem is stated over releases alone, two silence claims
drawn at a boundary the matrix row beside them disclaims, and a matrix cell promising a Lockdown
that another requirement rules out. A premise another requirement owns is cited, not restated.

**Completion:** every sentence asserting what another requirement says carries its quote, every
list or count names its source instead of restating it, and every claim of a property names the
premises its theorem takes.

## When the set blocks the work

A brief that a theorem, an ADR decision or a requirement it leaves alone contradicts is a stop,
not a puzzle: the theorem stops proving and the way through is a new premise, a weaker statement
or a value read from somewhere else; the ADR rejected what the brief asks for; two requirements
the brief does not touch disagree. Stop that part, finish every part that does not depend on it,
and report the conflict in a few sentences with the texts quoted and the words "needs an owner
decision". Do not research alternatives, draft the change under one reading, or weaken the
theorem to see whether the proof goes through. The HARD STOPS a brief lists are instances of this
rule, not its extent: `bps-xrv`'s review raised its HARD STOP 2, and the owner's decision, not a
breach, is on the bead. An editorial or mechanical fix the brief already asks for is not a stop.

**An ADR decision is the owner's.** It changes only on an owner decision recorded on the bead
that lands the change, naming the ADR and the decision number. A brief that contradicts a
decision without naming it, a reviewer finding, a Reviewer majority, or a theorem that would
prove more easily under the other choice is a stop under the rule above, never an authorization.
`docs/agents/domain.md` says how to flag the conflict.

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
