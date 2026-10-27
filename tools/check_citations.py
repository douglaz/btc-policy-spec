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
           Hard failure when a span read as a quote does not occur there;
           stray straight marks can make that span unintended (see below).

  UNQUOTED "`X` says/states ..." with no quote of its own, after it and
           before the next attribution, is unverifiable by construction.
           Hard failure when find() reports it; no exemption list is kept.
           Unquoted `reads` or `read` is a consult and is not counted.

A forward attribution takes the verb form ("`WIR-1` says ..."), a possessive form
("`WIR-1`'s rule that ..." or "`WIR-1`'s \"...\"") or the colon form
("`OPR-49`: \"...\"", the quote directly after the colon). In the verb form one
word in KNOWN may stand between the id (with or without `'s`) and its verb,
read like the bare verb (`bps-68a`): `OVR-1` also says "<a false phrase>" goes
red naming OVR-1, `OVR-1` now says "<good>" verifies the quote, and `OVR-1`
still says the rule applies counts as unquoted. The noun form takes `own`
alone. Direct possessives and colons introduce either straight or curly
quotation marks. A chunk -- what
SPLIT cuts: a sentence, a list item, a paragraph -- may carry several, and each quote belongs
to the last attribution that starts before it, never to the chunk's first merely
because it is first. A bare backticked id before a quote is not a forward attribution
and takes no quote under either forward reading: "`STO-43` says `STO-14` "..."" is STO-43's claim. Nor is an
attribution-shaped phrase inside a span an earlier attribution introduced, which
is being quoted, not made: `MAN-2`'s body carries "`OPS-1` states", so a
quotation of that span is MAN-2's, and the inner phrase takes no quote and is
never counted as unquoted. A span no earlier attribution introduced suppresses
nothing within that reading. An
attribution introduces a span that opens after it and before the next attribution when the
span opens directly after it, or when a stray straight quote opens it and its closing mark is
not one the stray-span test below counts as a later attribution's opener. Such a span
suppresses the attribution-shaped phrases it holds even under MIN_WORDS words, where it is
skipped, so nothing checks the quotation a suppressed phrase opens: `OVR-1`'s "<good>", "
`DOM-1` says that "<a false phrase>" and `OVR-1`'s " `DOM-1` says "<a false phrase>" both stay
green (`bps-6m5`), the second although the span's closing mark is DOM-1's opener. With
MIN_WORDS words or more in such a span, the chunk goes red naming OVR-1.
A quote before the first attribution belongs to no forward attribution. A separate
suffix pass checks a paired straight or curly quotation immediately followed by whitespace
and one parenthesized backticked requirement id, such as "carries the plaintext PIN"
(`OPS-50`). It uses the landed QUOTE matcher within the same chunk, the same MIN_WORDS,
normalization, requirement bodies and explicitly cited root-document exception. This pass
adds a check without changing either forward reading: if a quote has both forms, both
claims must verify. A qualifying suffix claims the current body's wording even beside
withdrawn wording or a forward attribution to another owner; it is not merely a cross-reference.
Only the paired quote immediately before the suffix is checked by this pass. Multiple-id or
qualified parentheses, words between quote and parenthesis, no intervening whitespace,
quotes below MIN_WORDS, and quotes crossing chunks are not covered. Nested or stray marks
can cause misses or new false reds: an inch-mark pair immediately before a suffix can be
read as a quotation. Write inch marks as ″ and avoid nested quotation marks of the same kind.


Between an id and its speech verb, KNOWN and UNREAD match case-sensitively.
KNOWN is `own|now|also|still|itself|only|explicitly|currently`; UNREAD is
`once|is|are|was|were|be|been|being`. One UNREAD word after an id without a
possessive leaves the phrase no attribution: `OVR-1` once said "<a false phrase>"
stays green, as does the passive `DUR-21` through `DUR-31` are stated for one
Escape. Any other single word after an id without a possessive, or `no longer`,
is refused with a quote or without, naming the id and word. A word is letters
in any case and script with internal hyphens and apostrophes: `plainly`,
`Plainly`, `NOW`, `ONCE`, `naïvely`, `self-evidently`, `doesn't` and `never`.
Thus `OVR-1` plainly says "<good>" and `OVR-1` no longer says the rule applies
are refused. A refused phrase pairs as an attribution and owns the quotes after
it, so they never fall to an earlier attribution. Inside an introduced span it
is suppressed like any attribution-shaped phrase.

An unknown word, or `no longer`, before an unquoted `reads` or `read` is a
consult. The chunk is read again as if the phrase matched no attribution
pattern, so it neither pairs quotes nor hides a later attribution: `OVR-1`
plainly reads x " `DOM-1` says that "<a false phrase>" goes red naming DOM-1.
`SPN-46` then reads the coin age from the chain and `OVR-1` no longer reads the
register stay green. "Unquoted" holds under both pairings: `SPN-46` plainly
reads a 3" pipe and the long 5" line is refused, since the earlier pairing
pairs the inch marks as a quote.

Every chunk is read under both pairings: the landed pairing and the one before
2026-10-15 (`bps-6cz`). Both use MIN_QUOTE_CHARS as the minimum span length. In the landed
pairing, quotations have no upper length bound, and each attribution outside an
introduced quotation restarts pairing after its attribution text, including
consults and delayed openers, but not a consult after an unknown word or
`no longer`, which the re-read above drops from the chunk's attributions. The
earlier pairing bounds spans at
EARLIER_MAX_QUOTE_CHARS characters and restarts only at a colon or direct
possessive outside an introduced quotation.
Each restart re-scans the segment since the preceding restart and the text after
the attribution, preserving completed earlier spans. For the stray-span test,
the landed pairing counts a mark directly after any attribution, allowing
whitespace, where ANCHORED_QUOTE matches; the earlier pairing counts only the
explicit opener after a colon or direct possessive (ATTRIB's group 5).
ANCHORED_QUOTE rejects a straight opener directly after a digit; a curly opener
there still pairs. This applies when restarting after any attribution in the
landed pairing, but only after a colon or direct possessive in the earlier pairing.

The gate is red if either reading finds an unverifiable quote, a cut quotation,
a refused word or an unquoted attribution, or the landed reading refuses an
unclosed quotation. For each chunk, a landed unverifiable, cut or refused
quotation, or a landed refused word, selects all the landed findings.
Otherwise the chunk contributes the landed unquoted attributions and all the
earlier findings, listing each unquoted file:id signature once. Fixing one red
can therefore reveal the other reading's findings. The verified-attribution
count is the landed reading's checked-attribution count plus one for each qualifying
suffix span checked, even when a forward attribution also checks that quote. The script prints quotation faults and
refused words first and returns before the names and unquoted checks if any
remain anywhere in the tree.
For example, `DOM-1` requires "the coordinator `POL-18` reads first"; `OVR-1`
says that "this phrase OVR-1 does not contain at all"; `DOM-1` says the rule applies
prints one diagnostic, naming OVR-1.

In the landed reading, a colon or direct-possessive quotation with no closing
mark in its chunk is refused, naming its owner: words past a SPLIT boundary (a
sentence end, list marker, blank line or table row) are checked by nothing. Join
quoted fragments with … (U+2026), keeping the quotation closed within one chunk;
do not use three full stops followed by whitespace, which SPLIT reads as a
sentence end. This refusal follows the exemption for the AGENTS.md example
described below. An attribution-shaped phrase inside a span an earlier
attribution introduced is not refused. The earlier reading has no
unclosed-quotation refusal.

Summary verbs are deliberately OUT OF SCOPE. "`OPS-12` forbids automatic retry"
is a correct, useful paraphrase, and most attributions in the set are of that
shape. Demanding a quote there would fire on legitimate prose, which is how a
checklist item ends up unsatisfiable by every conforming implementation
(`CNF-224`).

WHAT THIS DOES NOT CATCH, stated plainly because a gate's limits are part of its
contract: a wrong SUMMARY. "`WIR-30` forbids the server resolving eligibility
that way" reverses `WIR-30`'s meaning, uses a summary verb, and carries no quote
-- no lexical signal separates it from a correct summary. That one was the worst
defect of 2026-09-03 and it stays a review problem. Two or more words between
the id and its verb, other than lower-case `no longer`, leave the phrase unread,
neither checked nor counted (`bps-68a`): `OVR-1` now also says "<a false phrase>",
`OVR-1` No longer says "<a false phrase>" and `OVR-1` NO LONGER says "<a false
phrase>" all stay green. A word outside KNOWN after a possessive names a part
of the requirement, neither read nor refused: `DUR-14`'s update reads the
resident register stays green. A combining mark is not a letter, so decomposed
`naïvely` (`nai`, U+0308, `vely`) leaves the phrase unread too, and so does a
token holding a decimal digit, or a comma or parenthesis, between the id and its
verb: `OVR-1` v2 says "<a false phrase>" and `OVR-1`, also, says "<a false
phrase>" stay green. Nor does it check
a colon or direct-possessive attribution whose quotes all fall short of MIN_WORDS
("`MAN-3`: "currently `4`""): the attribution is skipped, neither checked nor
counted as unquoted, since these forms carry a quote by construction and never
enter the UNQUOTED rule. A verb or noun attribution whose quotation runs past a
sentence end is not refused: with `says`, or a noun form such as "`NCH-25`'s
rule that", it counts as unquoted; with `reads` or `read`, the cut leaves no
quote, so it reads as a consult and nothing checks it. For example, `NCH-25`
reads "The store holds at most two partials. A duplicate is fine" stays green.
Nor does it read whole a quotation with nested or unpaired straight quotes:
QUOTE pairs straight quotes alternately, cutting it into alternating spans, and
the nested quotations themselves fall BETWEEN those spans, where nothing checks
them -- "definitely not sent" in a straight-quoted `OPR-49` line lies in no span
at all, and the verified count does not move. The common case is detected: when
a checked attribution (one owning at least one quote of MIN_WORDS words or more,
so a colon-form quotation cut into all-short spans is missed by both arms) owns
two or more raw spans, find() reads them outer quote to outer quote as one text
and, if that text is in the owner's body, fails the chunk as a quotation cut by
nested straight quotes -- a match proves the spans were one quotation nesting
straight quotes. The declared limit: a nested quote whose outer-to-outer text
does NOT match the body is still checked by nothing. Either way the fix is to
write the inner quotes curly, as the `DUR-30` quotation in `Cursor.lean` and the
`OPR-49` one in `Delivery.lean` do: norm() folds curly to straight, so the
quotation is one span and matches a body that nests straight quotes.

An otherwise genuine `says`, `said`, `states`, `stated` or noun-form quotation
over EARLIER_MAX_QUOTE_CHARS characters, alone in its chunk, is unread by the
earlier reading and counts as unquoted. Shorten it with … within one chunk, or
attribute it with `reads` or a colon. When another quotation follows in the same
chunk, see the long-quotation false red below; `reads` and a colon do not fix it.

No history marker exempts a quote. Every quote of MIN_WORDS words or more an
attribution owns is checked against its owner unless the attribution is refused,
and so is the outer-to-outer reading of a quotation cut by nested straight
quotes, whatever history marker
the prose around them carries. A marker once skipped the whole chunk, and the
list matched inside words, so current prose turned the check off: "whose close
it reads" in `NCH-41` let a corruption planted in its `SPN-30` quotation pass.
Nor does a history marker keep an attribution owning no quote out of the
unquoted count when the attribution is read. Between the id and its verb,
KNOWN is read, UNREAD leaves the phrase unread, and any other single word is
refused, subject to the consult and possessive rules above. For withdrawn
wording, follow README.md's "Quoting withdrawn wording" under "Requirement
conventions". Neither withdrawn-wording form creates a forward attribution. A qualifying
suffix nevertheless checks its paired span against the suffix owner's current body,
subject to the same explicitly cited root-document exception. To leave historical wording
outside that check, omit the qualifying suffix and use no earlier forward attribution
that owns it. Neither form proves the wording ever existed; other reported faults can
still fail the command.

The teaching exemption is kept for the AGENTS.md example under "Quote the sentence".
It requires the file name AGENTS.md, chunk text exactly equal to TEACHING_EXAMPLE
(including whitespace), and a TEACHING match in that reading's quote-blanked prose.
A byte-identical copy elsewhere in AGENTS.md is exempt too. Other chunks follow
the quotation, unquoted-attribution and refusal rules above even when their prose
carries "is an assertion", "is a claim, and" or "checkable;". A phrase inside a
paired span exempts nothing. "for example" is not a teaching phrase.

Stray straight marks paired across a quotation can cause a red naming prose
between quotations, or counting a quoted attribution as unquoted. Write the stray
as ″ (U+2033) or drop it, and write the quotation's marks curly. Curly marks
alone do not help when strays sit on both sides. An inch mark (`6"`) near an
attribution can make it red as unquoted again: Field is 6" wide and `OVR-1`
says "No signature path MAY bypass the policy checks" goes red as unquoted.
Curly quotation marks fix that example, but adding another `6"` after its
curly quotation makes it red again; writing both strays as ″ fixes it.

A straight quotation over EARLIER_MAX_QUOTE_CHARS characters followed by another
quotation in the same chunk can also blame the intervening prose, without a
stray mark: the earlier reading pairs the long quotation's closer with the next
opener. Write both quotations' marks curly, or the long one's, or shorten the
long quotation with … within one chunk. Changing `says` to `reads` or a colon
does not fix this false red. For quotations cut at a sentence end and counted
as unquoted instead, see WHAT THIS DOES NOT CATCH; join the sentences with …
within one chunk.

An accepted false red: a stray straight quote after an attribution and far from
its quotation can pair with that quotation's opener, blaming the intervening
prose. For example, `OVR-1` says the " mark, followed by more than
EARLIER_MAX_QUOTE_CHARS characters of prose, then
"No signature path MAY bypass the policy checks" can fail on that prose
even though the intended quotation is genuine.
A near stray can instead open a span below MIN_WORDS: `OVR-1` reads x " yy zz,
"<a false phrase>" stays green because the short span is skipped and `reads`
without a quote is a consult; with `says`, it is counted as unquoted.

Another accepted false red is a genuine delayed quotation ending in an
attribution-shaped phrase, followed by another quotation in the same chunk:
`MAN-2` says that "Unsealed they were not adjustable either — `OPS-1` states"
and, later in the text, "The manifest preimage MUST be" prints only a diagnostic
blaming OPS-1 and exits before the unquoted check, although find() also counts
MAN-2 as unquoted. The landed reading keeps this false red even
though the earlier reading is green; `reads, in full,` also blames OPS-1.
The delayed quotation's straight closer can open a span toward the later
quotation's opener, so the outer span is dropped as stray.
This needs at least MIN_QUOTE_CHARS characters between those marks. Write the
quotation marks curly, use a direct `says "…"` opener, or leave just ` and `
between the quotations to keep this example green.

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
The AGENTS.md example's teaching exemption skips quotes, never a name. Not caught:
a name with a character outside letters, digits, `_` and `.`, such as a `?` or
a `'`, which neither pattern reads.

Exit 0 = clean, 1 = an unverifiable quote, a colon or direct-possessive quotation
with no closing mark in its chunk, a quotation cut by nested straight
quotes, a refused word between an id and its verb, a docstring nesting a block
comment, a name that does not resolve, or an unquoted attribution. 2 = the
declaration list is missing.
"""

import glob
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NS = "OVR|DOM|CHN|POL|SPN|DUR|NCH|API|WIR|MAN|WTC|STO|SEC|OPS|DEF|CNF|OPR"

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_obligations import bodies  # noqa: E402  -- one span-splitter, not two

# Direct-speech attribution only. Summary verbs (forbids, requires, mandates,
# calls, makes) are out of scope by design -- see the module docstring.
#
# The 2026-09-03 miscitations used the first two patterns, one each: the verb
# form ("`WIR-1` says ...") and the possessive form ("`WIR-1`'s rule that ..."), which
# claims what a requirement contains just as directly. The third pattern introduces
# a quote directly, with either a colon (`OPR-49`: "...") or a possessive
# (`SPN-29`'s "..."). Group 5 is set only by these quote-introducing forms.
SPEECH = r"says|said|states|stated|reads|read"
NOUN = r"rule|claim|wording|statement|sentence|words|text"
# One KNOWN word in the verb form is read like the bare verb (`bps-68a`), with or without
# a possessive; the noun form keeps `own` alone. KNOWN and UNREAD are case-sensitive.
# The fourth pattern catches another single word, or `no longer`, without a possessive:
# groups 6-8 hold the id, intervening words and speech verb. WORD admits letters in any case
# and script with internal hyphens and apostrophes, but no combining marks. scan_chunk()
# refuses the words unless an unquoted `reads`/`read` makes the phrase a consult.
# UNREAD leaves the phrase no attribution: `once` is README.md's withdrawn-wording form;
# after a passive auxiliary the id is what is spoken of ("`DUR-31` are stated").
KNOWN = r"own|now|also|still|itself|only|explicitly|currently"
UNREAD = r"once|is|are|was|were|be|been|being"
WORD = r"[^\W\d_]+(?:[-'’][^\W\d_]+)*"
ATTRIB = re.compile(
    r"`((?:%s)-\d+[a-z]?)`(?:'s)?\s+(?:(?:%s)\s+)?(%s)\b"
    r"|`((?:%s)-\d+[a-z]?)`'s\s+(?:own\s+)?(%s)\s+that\b"
    r"|`((?:%s)-\d+[a-z]?)`(?::\s*|'s\s+)(?=[\"“])"
    r"|`((?:%s)-\d+[a-z]?)`\s+(?!(?:%s)\s)(no\s+longer|%s)\s+(%s)\b"
    % (NS, KNOWN, SPEECH, NS, NOUN, NS, NS, UNREAD, WORD, SPEECH)
)

# "reads" is two verbs. "`WIR-9` reads \"...\"" attributes text; "`LDG-74` reads
# it" and "`LDG-38` reads both from this record" mean CONSULTS, and consulting
# never carries a quote -- so the unquoted rule would fire on every one of them.
# Checked when a quote is present, ignored when one is not.
CONSULTS = {"reads", "read"}
# Single-id suffix only; no words or additional ids inside the parenthesis.
SUFFIX_ID = re.compile(r"\s+\(`((?:%s)-\d+[a-z]?)`\)" % NS)
# A bullet whose items end in ";" is one sentence to any splitter, which lets
# one item's attribution collect the next item's quote. Break on list markers
# and blank lines as well as sentence enders.
SPLIT = re.compile(r"(?<=[.!?])\s+|\n\s*[-*]\s+|\n\s*\n|\n(?=\|)")

# A quote shorter than this, in words, is too short to check and is skipped.
MIN_WORDS = 4
# A paired span's length in characters: at least this in both pairings ...
MIN_QUOTE_CHARS = 8
# ... and at most this in the earlier one.
EARLIER_MAX_QUOTE_CHARS = 400

# The landed pairing has no upper length bound; the earlier pairing bounds spans
# at EARLIER_MAX_QUOTE_CHARS characters. An unpaired quote character makes
# the span between two marks look like a quotation, reporting prose BETWEEN real
# quotes as a failed one; nested straight quotes pair alternately the same way,
# so inner quotes are written curly. find() uses the raw spans as follows: an
# attribution inside a span an earlier attribution introduced is not an attribution,
# TEACHING reads quote-blanked prose for the AGENTS.md example; and two or more
# spans owned by one attribution are read outer to outer for a quotation
# nesting straight quotes. The landed pairing restarts outside introduced
# quotations at all attributions, consults included; the earlier pairing restarts
# only at colons and direct possessives.
QUOTE_PATTERN = r'“([^”]{%s})”|"((?:[^"\n]|\n(?!\s*\n)){%s})"'
QUOTE = re.compile(QUOTE_PATTERN % ((f"{MIN_QUOTE_CHARS},",) * 2))
# At a pairing restart (every attribution in the landed reading, only a colon
# or direct possessive in the earlier one), a straight mark following a digit is
# rejected as an opener; a curly mark there still pairs. Re-scan its prefix too:
# merely retaining completed raw spans can keep an inch-mark-to-opener span and mask prose. Stray marks
# after the attribution can still mis-pair its quotation.
ANCHORED_QUOTE = re.compile(r'(?!(?<=\d)")(?:' + QUOTE.pattern + ')')
# The pairing before bps-6cz bounded both straight and curly spans.
EARLIER_QUOTE = re.compile(QUOTE_PATTERN % (
    (f"{MIN_QUOTE_CHARS},{EARLIER_MAX_QUOTE_CHARS}",) * 2))
EARLIER_ANCHORED_QUOTE = re.compile(r'(?!(?<=\d)")(?:' + EARLIER_QUOTE.pattern + ')')
# Closing-mark existence is independent of MIN_QUOTE_CHARS and MIN_WORDS.
CLOSED_QUOTE = re.compile(r'“[^”]*”|"(?:[^"\n]|\n(?!\s*\n))*"')
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

# Keep the AGENTS.md example under "Quote the sentence" able to show the mistake
# it forbids. Match its complete chunk, including whitespace, and file name;
# read the phrase outside each reading's paired spans.
TEACHING = re.compile(r"is an assertion|is a claim, and|checkable;", re.I)
TEACHING_EXAMPLE = (
    '`` `NCH-12` says "the window is [now − 300, now + 60]" `` is checkable; '
    '"`NCH-12` forbids a\nwider window" is an assertion.'
)


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


def scan_chunk(docs, reqs, f, sent, earlier_pairing=False, unread=()):
    """Read one chunk; earlier_pairing selects the pairing before bps-6cz. unread holds the
    starts of attributions read again as none: a refused word's consult."""
    bad, cut, refused, unquoted, checked = [], [], [], [], []
    quote = EARLIER_QUOTE if earlier_pairing else QUOTE
    anchored_quote = EARLIER_ANCHORED_QUOTE if earlier_pairing else ANCHORED_QUOTE
    qms = list(quote.finditer(sent))
    ams = [a for a in ATTRIB.finditer(sent) if a.start() not in unread]
    if earlier_pairing:
        direct_openers = {a.end() for a in ams if a.group(5)}
    else:
        direct_openers = set()
        for a in ams:
            opener = a.end() + len(sent[a.end():]) - len(sent[a.end():].lstrip())
            if (sent[opener:opener + 1] in {'"', '“'}
                    and anchored_quote.match(sent, opener)):
                direct_openers.add(opener)
    introduced = []
    anchor = 0
    for i, a in enumerate(ams):
        # Resolve introducers left to right; quoted attribution-shaped
        # text must not restart pairing inside an established quotation.
        quoted_attribution = any(s < a.start() < e for s, e in introduced)
        opener = a.end() + len(sent[a.end():]) - len(sent[a.end():].lstrip())
        if (not earlier_pairing or a.group(5)) and not quoted_attribution:
            # Repair since the preceding restart: any outside attribution
            # in the landed pairing, only a direct one in the earlier pairing,
            # preserving earlier pairing decisions. Short spans still mask
            # a TEACHING phrase from the AGENTS.md example's prose.
            qms = [qm for qm in qms if qm.end() <= anchor]
            qms += list(anchored_quote.finditer(sent, anchor, a.start()))
            qms += list(anchored_quote.finditer(sent, a.end()))
            anchor = a.end()
        next_start = ams[i + 1].start() if i + 1 < len(ams) else len(sent)
        # The landed pairing counts a mark after any attribution, allowing
        # whitespace, where anchored_quote matches; the earlier pairing
        # counts only the explicit opener of a colon or direct possessive.
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
    # introduced suppresses nothing (a stray span an attribution introduced does).
    owners = [a for a in ams if not any(s < a.start() < e for s, e in spans)]
    ms = [m for m in ams
          if not any(s < m.start() < e and any(a.end() <= s for a in owners)
                     for s, e in spans)]
    # For the AGENTS.md example, TEACHING reads the prose outside the quotes.
    prose = sent
    for s, e in spans:
        prose = prose[:s] + " " * (e - s) + prose[e:]
    if not ms or (f == "AGENTS.md" and sent == TEACHING_EXAMPLE and TEACHING.search(prose)):
        return bad, cut, refused, unquoted, checked
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
        owner = m.group(1) or m.group(3) or m.group(5) or m.group(6)
        if not earlier_pairing and m.group(5) and not CLOSED_QUOTE.match(sent, m.end()):
            refused.append((f, owner, None))
            continue
        mine = [q for p, q in quotes if m.start() < p < end]
        if m.group(6):
            # A word the gate does not read is refused. Unquoted `reads` or `read` after it is a
            # consult, which claims nothing: the chunk is read again without the phrase, as if
            # the word were in no pattern, so it neither pairs nor hides a later attribution.
            if not mine and m.group(8) in CONSULTS:
                return scan_chunk(docs, reqs, f, sent, earlier_pairing, (*unread, m.start()))
            refused.append((f, owner, " ".join(m.group(7).split())))
            continue
        if not mine:
            # Direct possessives and colons carry a quote by construction;
            # short ones are skipped, never counted as unquoted.
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
    return bad, cut, refused, unquoted, checked


def scan_suffix_chunk(docs, reqs, f, sent):
    """Check a closed quote followed immediately by one parenthesized requirement id.

    This is additional evidence: it never changes ownership under the existing two
    forward readings. A quote with both attributions must satisfy both.
    """
    bad, checked = [], []
    docpool = [norm(docs[d]) for d in DOC.findall(sent) if d in docs]
    for qm in QUOTE.finditer(sent):
        suffix = SUFFIX_ID.match(sent, qm.end())
        if not suffix:
            continue
        q = qm.group(1) or qm.group(2)
        if len(norm(q).split()) < MIN_WORDS:
            continue
        owner = suffix.group(1)
        pool = ([norm(reqs[owner][1])] if owner in reqs else []) + docpool
        frags = [x for x in (p.strip() for p in re.split(r"\.\.\.|…", norm(q))) if x]
        checked.append(f)
        if not frags or not any(all(fr in body for fr in frags) for body in pool):
            bad.append((f, owner, norm(q)[:95]))
    return bad, checked


def find(docs, reqs):
    """Return (unverified_quotes, cut_quotations, refusals, unquoted_attributions,
    files_of_checked_attributions). A refusal is (file, id, words): the words between the id and
    its verb the gate does not read, or None for a quotation with no closing mark in its chunk."""
    bad, cut, refused, unquoted, checked = [], [], [], [], []
    for f, text in docs.items():
        for sent in SPLIT.split(text):
            landed = scan_chunk(docs, reqs, f, sent)
            earlier = scan_chunk(docs, reqs, f, sent, earlier_pairing=True)
            # Combine readings by the module docstring's per-chunk reporting rule.
            if any(landed[:3]):
                b, c, r, u, _ = landed
            else:
                b, c, r, earlier_unquoted, _ = earlier
                by_signature = {}
                for entry in landed[3] + earlier_unquoted:
                    by_signature.setdefault(entry[:2], entry)
                u = list(by_signature.values())
            bad.extend(b)
            cut.extend(c)
            refused.extend(r)
            unquoted.extend(u)
            checked.extend(landed[4])
            suffix_bad, suffix_checked = scan_suffix_chunk(docs, reqs, f, sent)
            bad.extend(suffix_bad)
            checked.extend(suffix_checked)
    return bad, cut, refused, unquoted, checked


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
    bad, cut, refused, unquoted, checked = find({**docs, **lean}, reqs)
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
    unclosed = [(f, rid) for f, rid, words in refused if words is None]
    worded = [(f, rid, words) for f, rid, words in refused if words is not None]
    for f, rid in unclosed:
        print(f"  {f} quotation after `{rid}` has no closing mark in its chunk; "
              "join quoted fragments with … within one chunk")
    if unclosed:
        print(f"\nFAIL: {len(unclosed)} quotation(s) without a closing mark in their chunk. "
              "The gate reads one chunk at a time, so words past the cut are checked by "
              "nothing. Join quoted fragments with … (U+2026), not three full stops "
              "followed by whitespace, and close the quotation within one chunk.")
    for f, rid, words in worded:
        print(f"  {f} puts “{words}” between `{rid}` and its verb, which the gate does not read")
    if worded:
        print(f"\nFAIL: {len(worded)} attribution(s) with a word between the id and its verb "
              "that the gate does not read. Between them it reads only "
              f"{KNOWN.replace('|', ', ')}. Drop the word and carry the requirement's own "
              "words, or use a summary verb; to quote withdrawn wording, see README.md, "
              "Requirement conventions.")
    if bad or cut or refused:
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
    if sigs:
        for sig in sigs:
            f, rid = sig.split(":", 1)
            ex = next(s for g, r, s in unquoted if g == f and r == rid)
            print(f"  {f} reports what {rid} says without quoting it:")
            print(f"      {ex}")
        print(f"\nFAIL: {len(sigs)} unquoted attribution(s). Carry the "
              "requirement's own words, or use a summary verb and drop the claim "
              "to report what it says.")
        return 1
    print("unquoted attributions: 0: clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
