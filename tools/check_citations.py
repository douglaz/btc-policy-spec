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
stray unpaired straight quote opened -- suppresses nothing. Each attribution
outside an earlier introduced quotation restarts pairing after its attribution
text, including consults and forms whose opening quote does not directly follow.
Pairing re-scans the segment since the preceding such attribution and the text
after this one, preserving completed earlier spans. Quotations have no upper
length bound. A mark directly after an attribution, allowing whitespace, counts
as its opener for the stray-span test where ANCHORED_QUOTE can match at it.
A quote before the first attribution belongs to no one.

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
colon or direct-possessive attribution whose quotes all fall short of
MIN_WORDS ("`MAN-3`: "currently `4`"") or runs past a sentence end, where SPLIT cuts it ("`NCH-25`: "The store
holds ... `(rung, input, signer)`."): the attribution is skipped, neither
checked nor counted as unquoted, since these forms carry a quote by
construction and never enter the UNQUOTED rule. Nor does it read whole a
quotation with nested or unpaired straight quotes: QUOTE pairs straight quotes
alternately, cutting it into alternating spans, and the nested quotations
themselves fall BETWEEN those spans, where nothing checks them -- "definitely
not sent" in a straight-quoted `OPR-49` line lies in no span at all, and the
verified count does not move. The common case is detected: when a checked
attribution (one owning at least one quote of MIN_WORDS words or more, so a
colon-form quotation cut into all-short spans is missed by both arms) owns two
or more raw spans, find() reads them outer quote to outer quote as one text
and, if that text is in the owner's body, fails the chunk as a quotation cut by
nested straight quotes -- a match proves the spans were one quotation nesting
straight quotes. The declared limit: a nested quote whose outer-to-outer text
does NOT match the body is still checked by nothing. Either way the fix is to
write the inner quotes curly, as the `DUR-30` quotation in `Cursor.lean` and
the `OPR-49` one in `Delivery.lean` do: norm() folds curly to straight, so the
quotation is one span and matches a body that nests straight quotes.

No history marker exempts a quote. Every quote of MIN_WORDS words or more an
attribution owns is checked against its owner, and so is the outer-to-outer
reading of a quotation cut by nested straight quotes, whatever history marker
the prose around them carries. A marker once skipped the whole chunk, and the
list matched inside words, so current prose turned the check off: "whose close
it reads" in `NCH-41` let a corruption planted in its `SPN-30` quotation pass.
How withdrawn wording is quoted, where a trap justifies keeping it inline at
all, is README.md's "Requirement conventions": in a form ATTRIB does not read,
where no earlier attribution in the chunk owns the quote. That is a declared
limit: nothing checks such a quote. After another attribution in the same
chunk, the quote is that attribution's and is checked against it. No history
marker keeps an attribution owning no quote out of the unquoted count either.
Report old wording using README.md's "Quoting withdrawn wording" forms,
`X` once said "…" or `X`'s withdrawn wording "…", which ATTRIB does not read,
or use a summary verb, out of scope by design. TEACHING reads the
chunk's prose outside its QUOTE spans: a teaching phrase inside a quotation
QUOTE reads is the quoted body's and exempts nothing. "for example" is not a
teaching phrase. A chunk whose prose carries "is an assertion", "is a claim, and"
or "checkable;" is still skipped whole, its quotes and unquoted attributions
included; nor does "for example" keep an unquoted attribution out of the
count.

Teaching limits remain. Ordinary prose carrying one of those phrases still
exempts the chunk: `OVR-1` says "<a false phrase>" is checkable; ... leaves the
false quote unchecked. Text QUOTE does not pair reads as prose. A stray straight
quote after an attribution can mis-pair its quotation, leaving its teaching
phrase in the prose and exempting the chunk: `OVR-1` says the " mark is wide,
and "x checkable; y <a false phrase>" stays green.

An accepted false red: a stray straight quote after an attribution and far from
its quotation can pair with that quotation's opener, blaming the intervening
prose. For example, `OVR-1` says the " mark, followed by more than 400 characters
of prose, then "No signature path MAY bypass the policy checks" can fail on that prose
even though the intended quotation is genuine.
A near stray can instead open a span below MIN_WORDS: `OVR-1` reads x " yy zz,
"<a false phrase>" stays green because the short span is skipped and `reads`
without a quote is a consult; with `says`, it is counted as unquoted.

Another pairing limit involves a delayed opener and a quotation ending in an
attribution-shaped phrase, followed by another quotation in the same chunk:
`OVR-1` reads, in full, "<a false phrase> when `DOM-1` reads" and later
"some other words of it here" is a false quotation the gate before 2026-10-15
rejected but now leaves green. When the later quotation has its own
attribution, as in `OVR-1` reads that "<a false phrase> when `DOM-1` reads" and
`POL-18` says "<a false phrase>", that attribution reads as quoted and its
quotation goes unchecked too. Its genuine twin, `MAN-2` says that "Unsealed
they were not adjustable either — `OPS-1` states" and, later in the text,
"The manifest preimage MUST be", instead goes red blaming OPS-1, where the
gate before 2026-10-15 was green; `reads, in full,` has the same false red.
In these examples, the delayed quotation's straight closer can open a span
toward the later quotation's opener, so the outer span is dropped as stray.
This needs at least eight characters between those marks. The genuine twin
stays green with a direct `says "…"` opener, or with just ` and ` between the
quotations.

Both rules read root Markdown, `docs/adr/*.md`, and the Lean docstrings under
`tools/formal/` -- `/-- ... -/` and `/-! ... -/`, not `--` comments -- because a docstring
quoting a requirement drifts from it the same way. Requirement bodies come from
root Markdown alone: neither an ADR nor a docstring owns a requirement. ADRs
are attribution sources, never alternative quotation evidence. The existing
exception for an explicitly cited root document uses only that document's text.
A docstring nesting a
`/- -/` block comment is REFUSED, not read past: the extractor is a regex, not
Lean's lexer, so it would end the docstring at the inner `-/` and never see a
quote after it.

NAMES. In the same texts a backticked `BtcPolicy.*` name cites a Lean declaration,
and so does a short form: a backticked dotted name whose first component is a
module the build imports, read as `BtcPolicy.` plus the name, so `Kernel.prune`
cites `BtcPolicy.Kernel.prune` (`Kernel.lean` is a file, not a citation). Only
that exact prefix is tried, never a suffix. Each must resolve against the
declaration list `lake exe gate` writes (ADR-0023 decision 1 states what it
holds), a namespace or module holding one, or
`BtcPolicy.Explore`, the namespace that may hold untagged scratch. A renamed
declaration leaves a dangling citation, and this is where it goes red.
TEACHING skips quotes, never a name. Not caught:
a name with a character outside letters, digits, `_` and `.`, such as a `?` or
a `'`, which neither pattern reads.

Exit 0 = clean, 1 = an unverifiable quote, a quotation cut by nested straight
quotes, a docstring nesting a block comment, a name that does not resolve, or a
rise above the baseline. 2 = the declaration list is missing.
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

# Paired quotes without an upper length bound. An unpaired quote character makes
# the span between two marks look like a quotation, reporting prose BETWEEN real
# quotes as a failed one; nested straight quotes pair alternately the same way,
# so inner quotes are written curly. find() uses the raw spans as follows: an
# attribution inside a span an earlier attribution introduced is not an attribution,
# TEACHING reads around them through quote-blanked prose,
# and two or more owned by one attribution are read outer to outer for a quotation
# nesting straight quotes. Pairing restarts outside introduced quotations at
# verb, noun, colon and direct possessive attributions, including consults.
QUOTE = re.compile(r'“([^”]{8,})”|"((?:[^"\n]|\n(?!\s*\n)){8,})"')
# When an attribution repairs pairing, a measurement mark following a digit
# cannot open a quotation. Re-scan its prefix too: merely retaining completed
# raw spans can keep an inch-mark-to-opener span and mask prose. Stray marks
# after the attribution can still mis-pair its quotation.
ANCHORED_QUOTE = re.compile(r'(?!(?<=\d)")(?:' + QUOTE.pattern + ')')
# Non-greedy, so a docstring nesting a `/- -/` comment ends at the inner `-/`. load()
# reports every one that does and main() refuses it: a quote past that point is unread.
DOCSTRING = re.compile(r"/-[-!](.*?)-/", re.S)
DOC = re.compile(r"`(\d\d-[a-z-]+\.md|README\.md|CONTEXT\.md|AGENTS\.md|executive-summary\.md)`")
# A backticked `BtcPolicy.*` name, in a document or a docstring, is a citation of a Lean
# declaration and must resolve against the declaration list `lake exe gate` writes (ADR-0023
# decision 1 states what it holds): a name in it; a namespace or module
# holding one; or `BtcPolicy.Explore`, the namespace that may hold untagged scratch. A short
# form, `Kernel.prune`, is one too: citations() builds its pattern from the modules. A renamed
# declaration leaves a dangling citation, and this is where it goes red.
LEAN = re.compile(r"`(BtcPolicy\.[A-Za-z0-9_.]+)`(?<!\.lean`)")  # `BtcPolicy.lean` is a file
INDEX = os.path.join(ROOT, "tools", "formal", ".lake", "index.jsonl")
DECLARATIONS = os.path.join(ROOT, "tools", "formal", ".lake", "declarations.txt")
MODULES = os.path.join(ROOT, "tools", "formal", "BtcPolicy.lean")

# A quote shorter than this, in words, is too short to check and is skipped.
MIN_WORDS = 4

# A document teaching this rule must be able to show the mistake it forbids.
# Read the prose outside QUOTE spans; a phrase inside a QUOTE span exempts nothing.
TEACHING = re.compile(r"is an assertion|is a claim, and|checkable;", re.I)


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
    reqs = {}
    for f, t in docs.items():
        for k, v in bodies(t).items():
            reqs.setdefault(k, (f, v))
    docs.update({f: read(f) for f in sorted(glob.glob("docs/adr/*.md"))})
    lean, nested = {}, []
    for f in sorted(glob.glob("tools/formal/**/*.lean", recursive=True)):
        src = read(f)
        found = list(DOCSTRING.finditer(src))
        # A blank line between docstrings, so SPLIT never joins two of them.
        lean[f] = "\n\n".join(m.group(1) for m in found)
        # The closer too: in `a /-/` Lean nests on the `/-` whose `-/` the regex stops at.
        nested += [(f, src.count("\n", 0, m.start()) + 1)
                   for m in found if "/-" in m.group(1) + "-/"]
    return docs, reqs, lean, nested


def find(docs, reqs):
    """Return (unverified_quotes, cut_quotations, unquoted_attributions,
    files_of_checked_attributions)."""
    bad, cut, unquoted, checked = [], [], [], []
    for f, text in docs.items():
        for sent in SPLIT.split(text):
            qms = list(QUOTE.finditer(sent))
            ams = list(ATTRIB.finditer(sent))
            direct_openers = set()
            for a in ams:
                opener = a.end() + len(sent[a.end():]) - len(sent[a.end():].lstrip())
                if (sent[opener:opener + 1] in {'"', '“'}
                        and ANCHORED_QUOTE.match(sent, opener)):
                    direct_openers.add(opener)
            introduced = []
            anchor = 0
            for i, a in enumerate(ams):
                # Resolve introducers left to right; quoted attribution-shaped
                # text must not restart pairing inside an established quotation.
                quoted_attribution = any(s < a.start() < e for s, e in introduced)
                opener = a.end() + len(sent[a.end():]) - len(sent[a.end():].lstrip())
                if not quoted_attribution:
                    # Repair the segment since the preceding outside attribution,
                    # preserving earlier pairing decisions. Short spans still
                    # mask a TEACHING phrase from the prose.
                    qms = [qm for qm in qms if qm.end() <= anchor]
                    qms += list(ANCHORED_QUOTE.finditer(sent, anchor, a.start()))
                    qms += list(ANCHORED_QUOTE.finditer(sent, a.end()))
                    anchor = a.end()
                next_start = ams[i + 1].start() if i + 1 < len(ams) else len(sent)
                # A direct opener is a mark immediately after an attribution,
                # allowing whitespace, where ANCHORED_QUOTE can match.
                # A span that consumes a later direct opener as its closer is
                # stray, unless this attribution explicitly opened that span.
                # Other spans remain owned, including a second genuine quotation
                # with an attribution-shaped phrase inside it.
                # A skipped inner attribution extends the preceding owner's
                # protection to the next boundary; it does not end ownership.
                introduced += [qm.span() for qm in qms
                               if a.end() <= qm.start() < next_start
                               and (qm.start() == opener or qm.end() - 1 not in direct_openers)]
            spans = [qm.span() for qm in qms]
            # An attribution-shaped phrase inside a span an earlier attribution introduced
            # is being quoted, not made. The owner must itself sit outside every span, so
            # a quoted pseudo-attribution introduces nothing; and a span no attribution
            # introduced -- one a stray unpaired straight quote opened -- suppresses nothing.
            owners = [a for a in ams if not any(s < a.start() < e for s, e in spans)]
            ms = [m for m in ams
                  if not any(s < m.start() < e and any(a.end() <= s for a in owners)
                             for s, e in spans)]
            # TEACHING reads the prose outside the quotes.
            prose = sent
            for s, e in spans:
                prose = prose[:s] + " " * (e - s) + prose[e:]
            if not ms or TEACHING.search(prose):
                continue
            quotes = [(qm.start(), qm.group(1) or qm.group(2)) for qm in qms]
            quotes = [(p, q) for p, q in quotes if len(norm(q).split()) >= MIN_WORDS]
            docpool = [norm(docs[d]) for d in DOC.findall(sent) if d in docs]
            # Each quote belongs to the last attribution that starts before it,
            # NOT to the nearest citation before it: "`STO-43` says `STO-14`
            # 'reaches settled operations'" is STO-43's sentence about STO-14,
            # and blaming STO-14 for it inverts the claim -- a bare backticked id
            # is not an attribution. A quote before the first attribution belongs
            # to no one.
            ends = [n.start() for n in ms[1:]] + [len(sent)]
            for m, end in zip(ms, ends):
                owner = m.group(1) or m.group(3) or m.group(5)
                mine = [q for p, q in quotes if m.start() < p < end]
                if not mine:
                    # Direct possessives and colons carry a quote by construction;
                    # short or split ones are skipped, never counted as unquoted.
                    if (not m.group(5)
                            and (m.group(2) or "").lower() not in CONSULTS):
                        unquoted.append((f, owner, " ".join(sent.split())[:100]))
                    continue
                checked.append(f)
                pool = [norm(reqs[owner][1])] if owner in reqs else []
                pool += docpool
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
    """The index `lake exe gate` writes, as {declaration: requirement id}. Defined here and
    imported by check_ids.py, check_copies.py and check_regions.py, the gates that read the
    index -- one reader, not one per gate; this gate does not read it. Missing = exit 2,
    never a skip."""
    if not os.path.exists(INDEX):
        print(f"FAIL: {INDEX} missing -- run tools/check_formal.sh first "
              "(check-all.sh runs it before every gate that reads the index)")
        sys.exit(2)
    rows = [json.loads(l) for l in open(INDEX) if l.strip()]
    return {r["decl"]: r["req"] for r in rows}


def modules():
    """The modules the build imports, as `BtcPolicy.lean` lists them."""
    return [line.split()[1] for line in open(MODULES) if line.startswith("import ")]


def lean_names():
    """Every name a document or docstring may cite: each name in the declaration list
    (ADR-0023 decision 1 states what it holds) and its namespaces; the modules the build imports;
    and `BtcPolicy.Explore`, which holds untagged scratch. Not caught: a declaration
    renamed and a new one declared under the old name. Missing = exit 2, never a skip."""
    if not os.path.exists(DECLARATIONS):
        print(f"FAIL: {DECLARATIONS} missing -- run tools/check_formal.sh first "
              "(check-all.sh orders it before this gate)")
        sys.exit(2)
    names = {"BtcPolicy.Explore", *modules()}
    for decl in open(DECLARATIONS).read().split():
        parts = decl.split(".")
        names.update(".".join(parts[:k]) for k in range(1, len(parts) + 1))
    return names


def citations(docs):
    """Every name each text cites, as (file, as written, as resolved): a `BtcPolicy.*`
    name as it stands, a short form with `BtcPolicy.` in front. A short form starts at the
    backtick with a module's name and a dot, so `Node.lockedDown` is no citation."""
    short = re.compile(r"`((?:%s)\.[A-Za-z0-9_.]+)`(?<!\.lean`)" % "|".join(
        re.escape(m.removeprefix("BtcPolicy.")) for m in modules() if m.startswith("BtcPolicy.")))
    return ([(f, n, n) for f, t in docs.items() for n in LEAN.findall(t)]
            + [(f, n, "BtcPolicy." + n) for f, t in docs.items() for n in short.findall(t)])


def unresolved(cited):
    names = lean_names()
    return [c for c in cited if c[2] not in names]


def main():
    docs, reqs, lean, nested = load()
    for f, line in nested:
        print(f"  {f}:{line}: a docstring nests a /- -/ block comment, which the "
              "extractor does not support")
    if nested:
        print(f"\nFAIL: {len(nested)} Lean docstring(s) nest a block comment. Refused rather "
              "than read past: the docstring would end at the inner -/ and a quote after it "
              "go unchecked. Move the comment out of the docstring.")
        return 1
    bad, cut, unquoted, checked = find({**docs, **lean}, reqs)
    for f, rid, q in bad:
        print(f"  {f} attributes to {rid} a phrase {rid} does not contain:")
        print(f'      "{q}"')
    if bad:
        print(f"\nFAIL: {len(bad)} unverifiable quoted attribution(s). Quote the "
              "requirement's own words, or cite it without quoting. To quote withdrawn "
              "wording, see README.md, Requirement conventions.")
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

    # A docstring's citation dangles the same way a document's does.
    cited = citations({**docs, **lean})
    dangling = unresolved(cited)
    for f, n, full in dangling:
        read_as = "" if n == full else f" (read as `{full}`)"
        print(f"  {f} cites `{n}`{read_as}, which the declaration list does not carry")
    if dangling:
        print(f"\nFAIL: {len(dangling)} BtcPolicy name(s) do not resolve against "
              "tools/formal/.lake/declarations.txt. Cite the declaration by its current name.")
        return 1
    short = sum(n != full for _, n, full in cited)
    in_lean = sum(f.endswith(".lean") for f, _, _ in cited)
    print(f"BtcPolicy names resolved: {len(cited)}, {short} of them short forms, "
          f"{in_lean} in Lean docstrings")

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
