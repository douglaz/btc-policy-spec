#!/usr/bin/env python3
"""Orphaned-obligation gate.

A requirement that assigns a duty to ANOTHER requirement's subject -- "`LDG-62`
MUST conditional-write that row guarded on `destroy_committed IS NULL`" -- states
that duty in the wrong document. Nobody implementing `LDG-62` from
`12-billing-and-ledger.md` ever reads `OPS-42`, so the duty is never built, and
the requirement that depends on it is quietly false.

That is not a hypothetical in the sibling provisiond specification, where the
gate was written: a fence requirement stated another requirement's half of a
contention and the other requirement never mentioned it, and two full-set
cross-model reviews read past it. Ported here unchanged because btc-policy's
own history (bead btc-policy-0ip) is the same failure in prose form.

The other gates cannot see this class. `check_ids.py` is satisfied -- the
citation resolves. `check_coverage.py` is satisfied -- both requirements have
conformance items. The text reads correctly in both places. Only the RELATIONSHIP
is broken, and only a check that follows it can tell.

THE RULE: where requirement A says "`B` MUST <clause>" and the clause names
concrete machinery in backticks -- a column, a field, a state -- B's own body
must mention at least one of those names. B is free to phrase its duty however it
likes; it is not free to be silent about it.

Deliberately conservative. It fires only when the target mentions NONE of the
clause's identifiers, because a partial match is usually a requirement that
discharges its duty in its own vocabulary. The negative control lives in
.github/workflows/gates.yml rather than in a historical commit of this repo.

Exit 0 = clean, 1 = at least one orphaned obligation.
"""

import glob
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NS = "OVR|DOM|CHN|POL|SPN|DUR|NCH|API|WIR|MAN|WTC|STO|SEC|OPS|DEF|CNF|OPR"

HEAD_RE = re.compile(
    r"^(?:[-*]\s+(?:\[[ x]\]\s+)?)?\*\*((?:%s)-\d+[a-z]?)\*\*"
    r"|^#{1,6}\s+\**((?:%s)-\d+[a-z]?)\**" % (NS, NS)
)
OBLIG_RE = re.compile(r"`((?:%s)-\d+[a-z]?)`\s+(?:MUST|SHOULD)\b([^.]{0,300})" % NS)

# An identifier-shaped token inside a backtick span: `destroy_committed IS NULL`
# yields destroy_committed. Requiring the WHOLE span to be a bare identifier
# misses exactly that case -- which is the case this gate exists for.
TOKEN_RE = re.compile(r"\b([a-z][a-z_0-9]{4,})\b")

# Words that appear in prose as often as in schemas; a target "mentioning" one of
# these proves nothing.
NOISE = {
    "where", "which", "there", "these", "those", "while", "would", "should",
    "about", "after", "every", "other", "under", "being", "their", "whether",
    "because", "within", "against", "though", "rather", "cannot", "already",
    "before", "during", "however", "instead", "itself", "either", "neither",
}


def bodies(text):
    out, cur, buf = {}, None, []
    for line in text.splitlines(True):
        m = HEAD_RE.match(line)
        if m:
            if cur:
                out.setdefault(cur, "".join(buf))
            cur, buf = (m.group(1) or m.group(2)), [line]
        elif cur:
            buf.append(line)
    if cur:
        out.setdefault(cur, "".join(buf))
    return out


def load(rev=None):
    os.chdir(ROOT)
    all_bodies = {}
    for f in sorted(glob.glob("*.md")):
        if rev:
            text = subprocess.run(
                ["git", "show", f"{rev}:{f}"], capture_output=True, text=True
            ).stdout
        else:
            text = open(f).read()
        for k, v in bodies(text).items():
            all_bodies.setdefault(k, (f, v))
    return all_bodies


def find(all_bodies):
    hits = []
    for rid, (f, body) in sorted(all_bodies.items()):
        for m in OBLIG_RE.finditer(body):
            target, clause = m.group(1), m.group(2)
            if target == rid or target not in all_bodies:
                continue
            toks = set()
            for span in re.findall(r"`([^`]+)`", clause):
                toks.update(TOKEN_RE.findall(span))
            toks -= NOISE
            toks = {t for t in toks if not re.match(r"^(?:%s)-" % NS.lower(), t)}
            if not toks:
                continue
            tf, tbody = all_bodies[target]
            missing = {t for t in toks if t not in tbody}
            if missing == toks:
                hits.append((rid, f, target, tf, sorted(missing),
                             " ".join(clause.split())[:120]))
    return hits


def main():
    hits = find(load())
    for rid, f, tgt, tf, miss, clause in hits:
        print(f"  {rid} ({f})")
        print(f"      says {tgt} MUST … {clause}")
        print(f"      but {tgt} ({tf}) mentions none of: {', '.join(miss)}")
    if hits:
        print(f"\nFAIL: {len(hits)} orphaned obligation(s). Either write the duty into "
              f"the requirement that owns the actor, or state it in terms that "
              f"requirement already uses.")
        return 1
    print("OK: no orphaned obligations "
          "(every cross-requirement duty is reflected in its target)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
