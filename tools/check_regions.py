#!/usr/bin/env python3
"""Rendering gate (ADR-0023): a marked region in a document is what its declaration emits.

`ADR-0023` moved a formalized clause's calculation, predicate or table into a Lean
declaration and promised that the copy in the Markdown is either generated from
the declaration or diffed against it. Two hand-kept copies drift, so drift here is
a red gate.

A region is the lines between two markers, each on a line of its own (indented
alike when the region sits inside a list item; the declaration then emits the indent):

    <!-- formal: BtcPolicy.Render.spn38Table -->
    | peer quota | ... |
    <!-- /formal -->

The name is a declaration `lake exe gate` indexed (so it is tagged with the
requirement it formalizes), and `lake exe render` emits its text together with
its `home`: the requirement whose body must hold the region, or an ADR
(`ADR-0014`) when the requirement's owner keeps the table there. Two kinds:

  render  Pure computation -- a worked table, a diagram. Compared line for line;
          `--write` rewrites the region from the declaration. Every arithmetic
          table is this kind: a `match` region compares tokens, not numbers.

  match   A table whose cells carry prose the declaration does not emit. The first
          column is the row's key: its emitted tokens must appear in the
          document's cell, in order, and a key cell with no tokens must equal
          the document's cell. Every other column is compared on the
          backticked and bold tokens drawn from the vocabulary the emitted table
          uses, which must match exactly. What this does NOT catch: the header
          row, a bare number, and prose in an outcome cell that contradicts the
          tokens beside it.

Refusals, each `DEF-16`'s green check in another form: a region naming a
declaration the index does not carry; a region whose declaration is tagged with
one requirement sitting in another; a region whose `home` is an ADR sitting in a
different file, or naming an ADR that does not exist; and a region the
declarations emit that no document renders.

Reads the files `tools/check_formal.sh` writes, so `check-all.sh` runs that gate
first. A missing index is a red gate, not a skipped one (`AGENTS.md`).

Exit 0 = every region is what its declaration emits, 1 = drift or a structural
refusal, 2 = the formal build's output is missing.
"""

import difflib
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGIONS = os.path.join(ROOT, "tools", "formal", ".lake", "regions.jsonl")

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_ids import DEF_RE  # noqa: E402  -- one requirement-head regex, not two
from check_citations import read_index  # noqa: E402  -- one index reader, not two

BEGIN = re.compile(r"^(\s*)<!-- formal: (BtcPolicy\.[A-Za-z0-9_.]+) -->\s*$")
END = "<!-- /formal -->"
TOKEN = re.compile(r"`[^`\n]+`|\*\*[^*\n]+\*\*")
ADR_FILE = re.compile(r"^docs/adr/(\d{4})-.*\.md$")


def load_formal():
    index = read_index()
    if not os.path.exists(REGIONS):
        print(f"FAIL: {REGIONS} missing -- run tools/check_formal.sh first "
              f"(check-all.sh orders it before this gate)")
        sys.exit(2)
    regions = {}
    for line in open(REGIONS):
        if line.strip():
            row = json.loads(line)
            regions[row["decl"]] = (row["kind"], row["home"], row["text"].split("\n"))
    return index, regions


def find_regions(lines):
    """Yield (decl, begin_index, end_index) for each marked region; end is the END line."""
    open_at = None
    for i, line in enumerate(lines):
        m = BEGIN.match(line.rstrip("\n"))
        if m:
            if open_at is not None:
                raise ValueError(f"line {i + 1}: region opened inside the one at line {open_at[1] + 1}")
            open_at = (m.group(2), i, m.group(1))
        elif line.strip() == END:
            if open_at is None:
                raise ValueError(f"line {i + 1}: '{END}' with no open region")
            # Both markers carry the region's own indent: a column-0 comment ends the list item
            # a nested region sits in, so dedenting the markers changes what renders while the
            # table between them still matches.
            if line[:len(line) - len(line.lstrip())] != open_at[2]:
                raise ValueError(f"line {i + 1}: '{END}' is not indented like its opening marker at line {open_at[1] + 1}")
            yield open_at[0], open_at[1], i, open_at[2]
            open_at = None
    if open_at is not None:
        raise ValueError(f"line {open_at[1] + 1}: region {open_at[0]} never closed")


HEADING = re.compile(r"^#{1,6}\s")


def requirement_at(lines, i):
    """The requirement whose body holds line i, or None (inside an ADR, always None). A section
    heading ends a requirement's body: a region moved below the next heading is in nobody's.
    A heading-form requirement (`### DEF-1 — …`) is a head, not a boundary, so it is tested first."""
    for j in range(i, -1, -1):
        m = DEF_RE.match(lines[j])
        if m:
            return m.group(1) or m.group(2)
        if HEADING.match(lines[j]):
            return None
    return None


def self_check():
    """`requirement_at` on every head shape `DEF_RE` accepts: a heading-form requirement
    (`### DEF-1 — …`, how `14-known-defects.md` defines every DEF) holds its body like a
    bold-form one does, while a heading that is not a requirement still ends the body."""
    doc = ["## Section", "**API-7** body", "", "table", "### DEF-1 — title", "table",
           "## An unrelated section", "table", "- [ ] **CNF-1** item", "table"]
    assert requirement_at(doc, 3) == "API-7"
    assert requirement_at(doc, 5) == "DEF-1"
    assert requirement_at(doc, 7) is None
    assert requirement_at(doc, 9) == "CNF-1"


def cells(row):
    parts = [c.strip() for c in row.strip().split("|")]
    return parts[1:-1] if len(parts) >= 2 else parts


def table_body(lines):
    rows = [l for l in lines if l.lstrip().startswith("|")]
    for k, r in enumerate(rows):
        if re.fullmatch(r"\|(?:\s*:?-+:?\s*\|)+", r.strip()):
            return rows[k + 1:]
    return rows


def match_table(doc_lines, emitted_lines):
    stray = [l for l in doc_lines if l.strip() and not l.lstrip().startswith("|")]
    if stray:
        return [f"a line that is not a table row: {stray[0].strip()[:80]!r}"]
    doc, want = table_body(doc_lines), [l for l in emitted_lines if l.strip()]
    if len(doc) != len(want):
        return [f"{len(doc)} row(s) in the document, {len(want)} emitted"]
    vocab = {t for row in want for c in cells(row)[1:] for t in TOKEN.findall(c)}
    out = []
    for n, (d, w) in enumerate(zip(doc, want), 1):
        dc, wc = cells(d), cells(w)
        if len(dc) != len(wc):
            out.append(f"row {n}: {len(dc)} cell(s), {len(wc)} emitted")
            continue
        # A key with no tokens (SPN-5's gate numbers) is its whole cell, or the check is vacuous.
        key, dkey = TOKEN.findall(wc[0]) or [wc[0]], TOKEN.findall(dc[0]) or [dc[0]]
        it = iter(dkey)
        if not all(any(t == k for t in it) for k in key):
            out.append(f"row {n}, key column: expected {key} in order, document has {dkey}")
        for col in range(1, len(wc)):
            got = [t for t in TOKEN.findall(dc[col]) if t in vocab]
            exp = TOKEN.findall(wc[col])
            if got != exp:
                out.append(f"row {n}, column {col + 1}: declaration says {exp}, document says {got}")
    return out


def placement_ok(f, lines, b, home, req):
    """Where a region may sit: under its declaration's requirement, or in the ADR its
    `home` names. Returns a message on refusal, None when placed correctly."""
    adr = ADR_FILE.match(f)
    if home.startswith("ADR-"):
        wanted = home[4:]
        if not any(os.path.basename(p).startswith(wanted + "-") for p in glob.glob("docs/adr/*.md")):
            return f"home {home} names an ADR that does not exist"
        if not adr or adr.group(1) != wanted:
            return f"home is {home} but the region sits in {f}"
        return None
    if adr:
        return f"sits in an ADR but its home is {home}"
    holder = requirement_at(lines, b)
    if holder != req:
        return f"is tagged {req} but sits in {holder}"
    if home != req:
        return f"home is {home} but the declaration is tagged {req}"
    return None


def main(write=False):
    self_check()
    os.chdir(ROOT)
    index, regions = load_formal()
    seen, failures = {}, 0
    for f in sorted(glob.glob("*.md")) + sorted(glob.glob("docs/adr/*.md")):
        lines = open(f).read().split("\n")
        try:
            found = list(find_regions(lines))
        except ValueError as exc:
            print(f"  {f}: {exc}")
            failures += 1
            continue
        rewritten = False
        for decl, b, e, indent in reversed(found):  # reversed: rewriting keeps earlier offsets valid
            body = lines[b + 1:e]
            where = f"{f}:{b + 1}"
            if decl not in regions:
                print(f"  {where}: region names {decl}, which the declarations do not emit")
                failures += 1
                continue
            if decl in seen:
                print(f"  {where}: region {decl} already rendered at {seen[decl]}")
                failures += 1
            seen[decl] = where
            kind, home, emitted = regions[decl]
            first = next((l for l in emitted if l.strip()), "")
            if first[:len(first) - len(first.lstrip())] != indent:
                print(f"  {where}: {decl}'s markers are indented {indent!r} but its declaration emits {first[:len(first) - len(first.lstrip())]!r}")
                failures += 1
            req = index.get(decl)
            if req is None:
                print(f"  {where}: {decl} is not in the index -- a region's declaration is tagged")
                failures += 1
            else:
                problem = placement_ok(f, lines, b, home, req)
                if problem:
                    print(f"  {where}: {decl} {problem}")
                    failures += 1
            if kind == "render":
                doc = [l.rstrip() for l in body]
                want = [l.rstrip() for l in emitted]
                if doc != want:
                    if write:
                        lines[b + 1:e] = emitted
                        rewritten = True
                        print(f"  {where}: rewrote {decl}")
                    else:
                        print(f"  {where}: {decl} drifted from its declaration:")
                        for d in difflib.unified_diff(doc, want, "document", "declaration", lineterm="", n=0):
                            print(f"      {d}")
                        failures += 1
            elif kind == "match":
                for msg in match_table(body, emitted):
                    print(f"  {where}: {decl}: {msg}")
                    failures += 1
            else:
                print(f"  {where}: {decl} has unknown kind {kind!r}")
                failures += 1
        if rewritten:
            open(f, "w").write("\n".join(lines))
    for decl in sorted(set(regions) - set(seen)):
        print(f"  {decl} is emitted but no document renders it")
        failures += 1
    if failures:
        print(f"\nFAIL: {failures} rendering failure(s). A marked region is what its declaration "
              f"emits; change the declaration, then `--write` the render regions.")
        return 1
    print(f"rendered regions: {len(seen)}, each what its declaration emits")
    return 0


if __name__ == "__main__":
    sys.exit(main(write="--write" in sys.argv))
