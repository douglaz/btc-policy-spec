#!/usr/bin/env python3
"""Citation-attribution gate.

A requirement that reports what another requirement SAYS is making a checkable
claim about a specific span of text. On 2026-09-03 several of those claims were
false, in both directions: `WIR-20` and `WIR-35` attributed this set's
wire-contract precedence rule to `WIR-1`, which carries the JSON, money and
timestamp conventions and says nothing of the kind; `DOM-30` reported that
`WIR-30` forbids what `WIR-30` in fact mandates. Two full review passes at
`high` effort read past all of them. See `ddd3df0` and `254fc24`.

The other gates cannot see this class. `check_ids.py` is satisfied -- the
citation resolves to a real identifier. `check_obligations.py` is satisfied --
no duty is being assigned. The sentence reads fluently. Only the relationship
between the claim and the cited text is broken.

TWO RULES, deliberately narrow.

  QUOTED   A quoted phrase attributed to `X` must appear in X's own body.
           Hard failure: the quote either occurs there or it does not, so a
           finding is provable and needs no judgement.

  UNQUOTED "`X` says/states/reads ..." with no quote of its own, after it and
           before the next attribution, is unverifiable by construction.
           Ratcheted against `citation-baseline.json` rather than failed
           outright, because such sentences already exist and a gate that
           fails a clean tree is a gate someone deletes. New ones are refused;
           the standing ones come down as their requirements are next edited.
           The count lives in that file and nowhere else -- a number written
           into prose is wrong the first time either end moves, which this set
           has now learned in `ADR-0003`, `ADR-0011` and the blocking count.

An attribution takes the verb form ("`WIR-1` says ..."), a possessive form
("`WIR-1`'s rule that ..." or "`WIR-1`'s \"...\"") or the colon form
("`OPR-49`: \"...\"", the quote directly after the colon). Direct possessives
and colons introduce either straight or curly quotation marks. A chunk -- what
SPLIT cuts: a sentence, a list item, a paragraph -- may carry several, and each quote belongs
to the last attribution that starts before it, never to the chunk's first merely
because it is first. A bare backticked id is not an attribution and takes no
quote: "`STO-43` says `STO-14` "..."" is STO-43's claim. Nor is an
attribution-shaped phrase inside a span an earlier attribution introduced, which
is being quoted, not made: `MAN-2`'s body carries "`OPS-1` states", so a
quotation of that span is MAN-2's, and the inner phrase takes no quote and is
never counted as unquoted. A span no earlier attribution introduced -- one a
stray unpaired straight quote opened -- suppresses nothing, so the attribution
inside it is still read and, lacking a quote of its own, reported. A quote
before the first attribution belongs to no one.

Summary verbs are deliberately OUT OF SCOPE. "`OPS-12` forbids automatic retry"
is a correct, useful paraphrase, and most attributions in the set are of that
shape. Demanding a quote there would fire on legitimate prose, which is how a
checklist item ends up unsatisfiable by every conforming implementation
(`CNF-224`).

WHAT THIS DOES NOT CATCH, stated plainly because a gate's limits are part of its
contract: a wrong SUMMARY. "`WIR-30` forbids the server resolving eligibility
that way" reverses `WIR-30`'s meaning, uses a summary verb, and carries no
quote -- no lexical signal separates it from a correct summary. That one was the
worst defect of 2026-09-03 and it stays a review problem. Nor does it check a
colon or direct-possessive attribution whose quote is under four words
("`MAN-3`: "currently `4`"") or runs past a sentence end, where SPLIT cuts it ("`NCH-25`: "The store
holds ... `(rung, input, signer)`."): the attribution is skipped, neither
checked nor counted as unquoted, since these forms carry a quote by
construction and never enter the UNQUOTED rule. Nor does it read whole a
quotation with nested or unpaired straight quotes: QUOTE pairs straight quotes
alternately, cutting it into alternating spans, and the nested quotations
themselves fall BETWEEN those spans, where nothing checks them -- "definitely
not sent" in a straight-quoted `OPR-49` line lies in no span at all, and the
verified count does not move. The common case is detected: when a checked
attribution (one owning at least one quote of four or more words, so a
colon-form quotation cut into all-short spans is missed by both arms) owns two
or more raw spans, find() reads them outer quote to outer quote as one text
and, if that text is in the owner's body, fails the chunk as a quotation cut by
nested straight quotes -- a match proves the spans were one quotation nesting
straight quotes. The declared limit: a nested quote whose outer-to-outer text
does NOT match the body is still checked by nothing. Either way the fix is to
write the inner quotes curly, as the `DUR-30` quotation in `Cursor.lean` and
the `OPR-49` one in `Delivery.lean` do: norm() folds curly to straight, so the
quotation is one span and matches a body that nests straight quotes.

A chunk quoting wording that was deliberately removed (HISTORICAL) is skipped
whole, as is one TEACHING this rule by showing the mistake it forbids.
HISTORICAL reads only the prose OUTSIDE the chunk's quotes, so a chunk quoting
withdrawn wording says so in its own words. That closes a silent skip: a marker
inside the quotation used to exempt the chunk, so a quoted body containing a
HISTORICAL word went unchecked -- `POL-18`'s own "a retry keeps the original
reservation time" exempted the `Ledger.lean` docstring quoting it.

Both rules read the Lean docstrings under `tools/formal/` -- `/-- ... -/` and
`/-! ... -/`, not `--` comments -- as they read the Markdown, because a docstring
quoting a requirement drifts from it the same way. Requirement bodies come from
the Markdown alone: a docstring owns no requirement. A docstring nesting a
`/- -/` block comment is REFUSED, not read past: the extractor is a regex, not
Lean's lexer, so it would end the docstring at the inner `-/` and never see a
quote after it.

Exit 0 = clean, 1 = an unverifiable quote, a quotation cut by nested straight
quotes, a docstring nesting a block comment, or a rise above the baseline.
"""

import glob
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "citation-baseline.json")
NS = "OVR|DOM|CHN|POL|SPN|DUR|NCH|API|WIR|MAN|WTC|STO|SEC|OPS|DEF|CNF|OPR"

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_obligations import bodies  # noqa: E402  -- one span-splitter, not two

# Direct-speech attribution only. Summary verbs (forbids, requires, mandates,
# calls, makes) are out of scope by design -- see the module docstring.
#
# The 2026-09-03 miscitations used the first two patterns, one each: the verb
# form ("`WIR-1` says ...") and the possessive form ("`WIR-1`'s rule that ..."), which
# claims what a requirement contains just as directly. The last pattern introduces
# a quote directly, with either a colon (`OPR-49`: "...") or a possessive
# (`SPN-29`'s "..."). Group 5 is set only by these quote-introducing forms.
SPEECH = r"says|said|states|stated|reads|read"
NOUN = r"rule|claim|wording|statement|sentence|words|text"
ATTRIB = re.compile(
    r"`((?:%s)-\d+[a-z]?)`(?:'s)?\s+(?:own\s+)?(%s)\b"
    r"|`((?:%s)-\d+[a-z]?)`'s\s+(?:own\s+)?(%s)\s+that\b"
    r"|`((?:%s)-\d+[a-z]?)`(?::\s*|'s\s+)(?=[\"“])" % (NS, SPEECH, NS, NOUN, NS)
)

# "reads" is two verbs. "`WIR-9` reads \"...\"" attributes text; "`LDG-74` reads
# it" and "`LDG-38` reads both from this record" mean CONSULTS, and consulting
# never carries a quote -- so the unquoted rule would fire on every one of them.
# Checked when a quote is present, ignored when one is not.
CONSULTS = {"reads", "read"}
# A bullet whose items end in ";" is one sentence to any splitter, which lets
# one item's attribution collect the next item's quote. Break on list markers
# and blank lines as well as sentence enders.
SPLIT = re.compile(r"(?<=[.!?])\s+|\n\s*[-*]\s+|\n\s*\n|\n(?=\|)")

# Paired quotes only. An unpaired quote character makes every span between two
# of them look like a quotation, which reports the prose BETWEEN two real
# quotes as a failed one; nested straight quotes pair alternately the same way,
# so inner quotes are written curly. find() reads the raw spans three times: an
# attribution inside a span an earlier attribution introduced is not an attribution,
# HISTORICAL reads around them, and two or more owned by one attribution are read
# outer to outer for a quotation nesting straight quotes.
QUOTE = re.compile(r'“([^”]{8,400})”|"((?:[^"\n]|\n(?!\s*\n)){8,400})"')
# Non-greedy, so a docstring nesting a `/- -/` comment ends at the inner `-/`. load()
# reports every one that does and main() refuses it: a quote past that point is unread.
DOCSTRING = re.compile(r"/-[-!](.*?)-/", re.S)
DOC = re.compile(r"`(\d\d-[a-z-]+\.md|README\.md|CONTEXT\.md|AGENTS\.md|executive-summary\.md)`")
# A backticked `BtcPolicy.*` name is a citation of a Lean declaration and must resolve
# against the index `lake exe gate` writes (ADR-0023): a tagged declaration, a namespace
# or module holding one, or `BtcPolicy.Explore`, the namespace that may hold untagged scratch. A renamed
# declaration leaves a dangling citation, and this is where it goes red.
LEAN = re.compile(r"`(BtcPolicy\.[A-Za-z0-9_.]+)`(?<!\.lean`)")  # `BtcPolicy.lean` is a file
INDEX = os.path.join(ROOT, "tools", "formal", ".lake", "index.jsonl")
MODULES = os.path.join(ROOT, "tools", "formal", "BtcPolicy.lean")

# A quotation of wording that was deliberately removed cannot be found in the
# body, and this set retains such quotations on purpose (README, "Identifiers
# are append-only. Text is not."). Recognise the sentence, do not check it --
# by its prose outside the quotes: a marker inside a quotation is the quoted
# body's own word, and "the original reservation time" is current `POL-18`.
HISTORICAL = re.compile(
    r"withdraw|withdrew|until 20|previously|the original|first draft|old (?:item|text|wording)"
    r"|earlier (?:draft|version|text|wording|revision|note|phrasing)|stood (?:here|there)"
    r"|used to|no longer|superseded|retired|amended|version one|version two|rewritten"
    r"|this said|it said|it read|had said|once (?:said|read|contained)|corrected|described it as|merged into|split into|the claim that did not",
    re.I,
)

# A document teaching this rule must be able to show the mistake it forbids.
TEACHING = re.compile(r"is an assertion|is a claim, and|checkable;|for example", re.I)


def norm(s):
    s = (s.replace("“", '"').replace("”", '"')
          .replace("’", "'").replace("‘", "'")
          .replace("—", "-").replace("–", "-"))
    s = re.sub(r"[*`~]", "", s)
    return re.sub(r"\s+", " ", s).lower().strip(" .,;:")


def load(rev=None):
    os.chdir(ROOT)
    def read(f):
        if rev:
            return subprocess.run(["git", "show", f"{rev}:{f}"],
                                  capture_output=True, text=True).stdout
        return open(f).read()
    docs = {f: read(f) for f in sorted(glob.glob("*.md"))}
    adr = " ".join(read(f) for f in sorted(glob.glob("docs/adr/*.md")))
    reqs = {}
    for f, t in docs.items():
        for k, v in bodies(t).items():
            reqs.setdefault(k, (f, v))
    lean, nested = {}, []
    for f in sorted(glob.glob("tools/formal/**/*.lean", recursive=True)):
        src = read(f)
        found = list(DOCSTRING.finditer(src))
        # A blank line between docstrings, so SPLIT never joins two of them.
        lean[f] = "\n\n".join(m.group(1) for m in found)
        # The closer too: in `a /-/` Lean nests on the `/-` whose `-/` the regex stops at.
        nested += [(f, src.count("\n", 0, m.start()) + 1)
                   for m in found if "/-" in m.group(1) + "-/"]
    return docs, adr, reqs, lean, nested


def find(docs, adr, reqs):
    """Return (unverified_quotes, cut_quotations, unquoted_attributions,
    files_of_checked_attributions)."""
    bad, cut, unquoted, checked = [], [], [], []
    nadr = norm(adr)
    for f, text in docs.items():
        for sent in SPLIT.split(text):
            qms = list(QUOTE.finditer(sent))
            spans = [qm.span() for qm in qms]
            # An attribution-shaped phrase inside a span an earlier attribution introduced
            # is being quoted, not made. The owner must itself sit outside every span, so
            # a quoted pseudo-attribution introduces nothing; and a span no attribution
            # introduced -- one a stray unpaired straight quote opened -- suppresses nothing.
            ams = list(ATTRIB.finditer(sent))
            owners = [a for a in ams if not any(s < a.start() < e for s, e in spans)]
            ms = [m for m in ams
                  if not any(s < m.start() < e and any(a.end() <= s for a in owners)
                             for s, e in spans)]
            # A historical marker counts only in the prose outside the quotes.
            prose = sent
            for s, e in spans:
                prose = prose[:s] + " " * (e - s) + prose[e:]
            if not ms or HISTORICAL.search(prose) or TEACHING.search(sent):
                continue
            quotes = [(qm.start(), qm.group(1) or qm.group(2)) for qm in qms]
            quotes = [(p, q) for p, q in quotes if len(norm(q).split()) >= 4]
            docpool = [norm(docs[d]) for d in DOC.findall(sent) if d in docs]
            # Each quote belongs to the last attribution that starts before it,
            # NOT to the nearest citation before it: "`STO-43` says `STO-14`
            # 'reaches settled operations'" is STO-43's sentence about STO-14,
            # and blaming STO-14 for it inverts the claim -- a bare backticked id
            # is not an attribution. A quote before the first attribution belongs
            # to whatever introduced it: CNF-6's merge marker quotes its own
            # withdrawn text and then CNF-107's, in that order, in one chunk.
            ends = [n.start() for n in ms[1:]] + [len(sent)]
            for m, end in zip(ms, ends):
                owner = m.group(1) or m.group(3) or m.group(5)
                mine = [q for p, q in quotes if m.start() < p < end]
                if not mine:
                    # Direct possessives and colons carry a quote by construction;
                    # short or split ones are skipped, never counted as unquoted.
                    if not m.group(5) and (m.group(2) or "").lower() not in CONSULTS:
                        unquoted.append((f, owner, " ".join(sent.split())[:100]))
                    continue
                checked.append(f)
                pool = [norm(reqs[owner][1])] if owner in reqs else []
                pool += docpool + [nadr]
                def quoted(q):
                    frags = [x for x in
                             (p.strip() for p in re.split(r"\.\.\.|…", norm(q))) if x]
                    return bool(frags) and any(all(fr in p for fr in frags) for p in pool)
                for q in mine:
                    if not quoted(q):
                        bad.append((f, owner, norm(q)[:95]))
                # Two or more raw spans read outer quote to outer quote, interior quote
                # characters left in place: a match is one quotation that nests straight
                # quotes, which QUOTE cut and whose nested text nothing above checked.
                raw = [qm for qm in qms if m.start() < qm.start() < end]
                if len(raw) >= 2 and quoted(sent[raw[0].start() + 1:raw[-1].end() - 1]):
                    cut.append((f, owner))
    return bad, cut, unquoted, checked


def read_index():
    """The index `lake exe gate` writes, as {declaration: requirement id}. Shared with
    check_regions.py and check_ids.py -- one reader, not three. Missing = exit 2, never a skip."""
    if not os.path.exists(INDEX):
        print(f"FAIL: {INDEX} missing -- run tools/check_formal.sh first "
              "(check-all.sh orders it before this gate)")
        sys.exit(2)
    rows = [json.loads(l) for l in open(INDEX) if l.strip()]
    return {r["decl"]: r["req"] for r in rows}


def lean_names():
    """Every name a document may cite: tagged declarations, their namespaces, the
    modules the build imports, and `BtcPolicy.Explore`, which holds untagged scratch.
    Not caught: a declaration renamed and a new one tagged under the old name."""
    names = {"BtcPolicy.Explore"}
    for decl in read_index():
        parts = decl.split(".")
        names.update(".".join(parts[:k]) for k in range(1, len(parts) + 1))
    for line in open(MODULES):
        if line.startswith("import "):
            names.add(line.split()[1])
    return names


def unresolved(docs, adr):
    names = lean_names()
    texts = list(docs.items()) + [("docs/adr/*.md", adr)]
    return [(f, n) for f, t in texts for n in LEAN.findall(t) if n not in names]


def main():
    docs, adr, reqs, lean, nested = load()
    for f, line in nested:
        print(f"  {f}:{line}: a docstring nests a /- -/ block comment, which the "
              "extractor does not support")
    if nested:
        print(f"\nFAIL: {len(nested)} Lean docstring(s) nest a block comment. Refused rather "
              "than read past: the docstring would end at the inner -/ and a quote after it "
              "go unchecked. Move the comment out of the docstring.")
        return 1
    bad, cut, unquoted, checked = find({**docs, **lean}, adr, reqs)
    for f, rid, q in bad:
        print(f"  {f} attributes to {rid} a phrase {rid} does not contain:")
        print(f'      "{q}"')
    if bad:
        print(f"\nFAIL: {len(bad)} unverifiable quoted attribution(s). Quote the "
              "requirement's own words, or cite it without quoting.")
    for f, rid in cut:
        print(f"  {f} quotation after `{rid}` is cut by nested straight quotes; "
              "write the inner quotes curly")
    if cut:
        print(f"\nFAIL: {len(cut)} quotation(s) cut by nested straight quotes. QUOTE pairs "
              "straight quotes alternately, so the nested text falls between spans and is "
              "checked by nothing.")
    if bad or cut:
        return 1
    in_lean = sum(f.endswith(".lean") for f in checked)
    print(f"quoted attributions verified: {len(checked)}, {in_lean} of them "
          "in Lean docstrings: clean")

    dangling = unresolved(docs, adr)
    for f, n in dangling:
        print(f"  {f} cites `{n}`, which the index does not carry")
    if dangling:
        print(f"\nFAIL: {len(dangling)} BtcPolicy.* name(s) do not resolve against "
              "tools/formal/.lake/index.jsonl. Cite the tagged declaration by its current name.")
        return 1
    print(f"BtcPolicy.* names resolved: {len(LEAN.findall(adr)) + sum(len(LEAN.findall(t)) for t in docs.values())}")

    sigs = sorted({f"{f}:{rid}" for f, rid, _ in unquoted})
    try:
        base = set(json.load(open(BASELINE))["unquoted_attributions"])
    except Exception:
        base = set(sigs)
        json.dump({"unquoted_attributions": sigs,
                   "note": "Sentences reporting what a requirement SAYS with no quote to "
                           "check, as file:id signatures rather than a count -- a count "
                           "cannot name which one is new. Ratchet: may shrink, never grow."},
                  open(BASELINE, "w"), indent=2)
        print(f"baseline written: {len(sigs)} signature(s)")
    new = [x for x in sigs if x not in base]
    if new:
        for sig in new:
            f, rid = sig.split(":", 1)
            ex = next(s for g, r, s in unquoted if g == f and r == rid)
            print(f"  {f} reports what {rid} says without quoting it:")
            print(f"      {ex}")
        print(f"\nFAIL: {len(new)} new unquoted attribution(s). Carry the "
              "requirement's own words, or use a summary verb and drop the claim "
              "to report what it says.")
        return 1
    print(f"unquoted attributions: {len(sigs)}, none new against baseline {len(base)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
