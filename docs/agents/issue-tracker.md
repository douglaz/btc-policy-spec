# Issue tracker: beads (`br`)

Work items for this repo live in beads: `.beads/issues.jsonl`, committed, with `.beads/beads.db`
as the local working copy. Issue prefix `bps`, so an id never reads as a reference-project bead
(`btc-policy-xxx`, cited from `16-open-findings.md`).

A bead is a work item. A finding in `16-open-findings.md` is an open design question with an
owner, append-only, `F`-numbered. A bead may cite the finding it works and a finding may cite the
bead that works it; neither replaces the other.

## Conventions

- A plan is one issue of type `epic`; its tickets are issues created with `--parent <epic>`.
- Blocking is native: `br dep add <ticket> <blocker>`. `br ready` lists open, unblocked, undeferred
  work; it is the frontier, worked in id order.
- Triage state is a label (see `triage-labels.md`): `br label add <id> <label>`.
- Never hand-edit `issues.jsonl`: `updated_at` goes stale and the next `br update` or `br close`
  silently reverts the edit. Every change goes through `br`.
- Before committing, `br sync --flush-only` so the JSONL matches the database; commit
  `.beads/issues.jsonl` with the change it tracks. `beads.db` is not committed.

## When a skill says "publish to the issue tracker"

A plan: `br create --type epic --title "<plan title>" --description-file <plan.md>
--labels ready-for-agent`. A ticket: `br create --parent <epic> --deps <blocker,...> --title ...
--description-file <ticket.md>`. Then `br sync --flush-only`.

## When a skill says "fetch the relevant ticket"

`br show <id>`. The user will normally pass the id.
