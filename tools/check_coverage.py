#!/usr/bin/env python3
"""Conformance-coverage gate.

The conformance checklist IS this project's test suite -- there is no code. So
the question "which requirements does nothing ever demonstrate?" is the same
question as "what is untested?", and it is not answerable by reading: a
requirement with no conformance item contradicts nothing, so every review pass
walks straight past it.

This gate measures it. A requirement is COVERED when at least one CNF item
cites it. Coverage may not fall below the recorded baseline.

The baseline exists because the sibling provisiond specification recorded this
failure twice: a session adding requirements faster than conformance items,
noticed only when somebody counted. A specification that grows faster than its
checklist is getting less testable, not more finished.

Two namespaces are excluded from the ratchet and reported separately:

  SEC -- 12-security-requirements.md's own scope note makes it cite rules owned
         elsewhere rather than restate them, so an uncited SEC requirement is
         usually the convention working.
  WIR -- one conformance item blanket-covers every fixture and vector, so per-id
         citation understates wire coverage.

Both are still printed, because "usually" is not "always".

Exit status 0 = at or above baseline, 1 = regression.
"""

import collections
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "tools", "coverage-baseline.json")

NAMESPACES = ["OVR", "DOM", "CHN", "POL", "SPN", "DUR", "NCH", "API", "WIR", "MAN", "WTC", "STO", "SEC", "OPS", "DEF", "OPR"]
NS = "|".join(NAMESPACES + ["CNF"])

DEF_RE = re.compile(
    r"^(?:[-*]\s+(?:\[[ x]\]\s+)?)?\*\*((?:%s)-\d+[a-z]?)\*\*"
    r"|^#{1,6}\s+\**((?:%s)-\d+[a-z]?)\**" % (NS, NS),
    re.M,
)
CITE_RE = re.compile(r"`((?:%s)-\d+[a-z]?)`" % NS)
CNF_ITEM_RE = re.compile(r"\*\*(CNF-\d+[a-z]?)\*\*")
# A checklist item citing `DUR-23`-`DUR-25` demonstrates DUR-24 as surely as the two it names.
# Without this the interior of every cited range reads as uncovered, which inflated the figure
# by eleven and buried the requirements that genuinely have no conformance item in the noise.
# Ranges are credited only within one namespace and only when the endpoints ascend.
RANGE_RE = re.compile(r"`((?:%s))-(\d+)`\s*[–—-]\s*`(?:%s)-(\d+)`" % (NS, NS))


def cited(line):
    found = {m.group(1) for m in CITE_RE.finditer(line)}
    for namespace, low, high in RANGE_RE.findall(line):
        if int(low) < int(high):
            found.update(f"{namespace}-{n}" for n in range(int(low), int(high) + 1))
    return found


def measure():
    os.chdir(ROOT)

    defined = {}
    for f in sorted(glob.glob("*.md")):
        for m in DEF_RE.finditer(open(f).read()):
            rid = m.group(1) or m.group(2)
            defined.setdefault(rid, f)

    # Attribute every line of the checklist to the CNF item it belongs to, then
    # collect what that item cites.
    #
    # `current` MUST be cleared at every heading. Without that reset it stays
    # set after the final item in a section, so every subsequent line — the tier
    # assignments, "Before production", the blocking-count discussion — is
    # credited to whichever item happened to precede it, and a requirement named
    # only in prose counts as demonstrated. That bug shipped on 2026-08-31 and
    # inflated the reported figure by eight points; found by a cross-model review
    # the same day. A gate that overstates coverage is worse than no gate,
    # because the ratchet then guards a number nobody earned.
    covered, current = set(), None
    for line in open("15-conformance-checklist.md"):
        if line.startswith("#"):
            current = None
        m = CNF_ITEM_RE.search(line)
        if m and (line.lstrip().startswith(("- [ ]", "- [x]", "- **"))):
            current = m.group(1)
        if current:
            covered.update(cited(line))

    reqs = {k for k in defined if not k.startswith("CNF-")}
    uncovered = sorted(k for k in reqs if k not in covered)
    return reqs, uncovered


def main():
    reqs, uncovered = measure()
    ratcheted = [k for k in uncovered if not k.startswith(("SEC-", "WIR-"))]
    excluded = [k for k in uncovered if k.startswith(("SEC-", "WIR-"))]

    total = len(reqs)
    cov = total - len(uncovered)
    pct = 100 * cov // total if total else 0

    print(f"requirements: {total} | covered by >=1 CNF item: {cov} ({pct}%)")
    print(f"uncovered (ratcheted): {len(ratcheted)}")
    print(f"uncovered (SEC/WIR, reported only): {len(excluded)}")

    by_ns = collections.Counter(k.split("-")[0] for k in ratcheted)
    for ns in NAMESPACES:
        if by_ns.get(ns):
            items = sorted(
                (k for k in ratcheted if k.startswith(ns + "-")),
                key=lambda s: (len(s), s),
            )
            print(f"  {ns}: {' '.join(items)}")

    if not os.path.exists(BASELINE):
        print(f"\nno baseline at {BASELINE} -- run with --write-baseline to create one")
        return 1

    base = json.load(open(BASELINE))
    limit = base["max_uncovered_ratcheted"]
    if len(ratcheted) > limit:
        print(
            f"\nFAIL: {len(ratcheted)} uncovered exceeds baseline {limit} "
            f"(set {base['recorded']}). New requirements need conformance items, "
            f"or raise the baseline deliberately and say why."
        )
        return 1

    print(f"\nOK: {len(ratcheted)} uncovered, at or below baseline {limit} "
          f"(set {base['recorded']})")
    return 0


if __name__ == "__main__":
    if "--write-baseline" in sys.argv:
        reqs, uncovered = measure()
        ratcheted = [k for k in uncovered if not k.startswith(("SEC-", "WIR-"))]
        stamp = sys.argv[sys.argv.index("--write-baseline") + 1]
        json.dump(
            {
                "max_uncovered_ratcheted": len(ratcheted),
                "recorded": stamp,
                "note": "Lower is better. Raise only deliberately, with a reason.",
            },
            open(BASELINE, "w"),
            indent=2,
        )
        open(BASELINE, "a").write("\n")
        print(f"baseline written: {len(ratcheted)} uncovered, {stamp}")
        sys.exit(0)
    sys.exit(main())
