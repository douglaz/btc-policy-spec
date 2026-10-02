#!/usr/bin/env python3
"""Copies gate (ADR-0023 decision 5): every figure inline in a requirement is what its
declaration emits.

The formal layer proves the rules; this gate keeps the DOCUMENT bound to them. A
theorem over Lean-side constants reads nothing of the Markdown, so without this
gate `CHN-4` could say `older(4224680)` while `bip68Time 30375 = 4224679` stayed
green. It reads every operand and stated result from the owning requirement --
and from every copy of it in another requirement -- with the regexes
`check_arithmetic.py` used until 2026-09-16, and compares what it reads to the
value `lake exe values` emitted for the declaration named. A second, corpus-wide
scan (ANYWHERE) binds the figures the set restates in many places -- a README
row, an ADR, a conformance item -- wherever they appear, with a hit-count
baseline (tools/copies-baseline.json) so a copy that stops matching is red, and
a new copy is red until `--write` records it in the same commit. Missing owners or
unrecognised wording fail closed, so a prose edit cannot silently disable a
check.

Two kinds of comparison. A NUMBER: the regex's groups, as integers, equal the
named values. A TEXT: the emitted string appears verbatim in the owner's body
(a formula, a sentence whose wording the declaration determines).

Reads the file `tools/check_formal.sh` writes, so `check-all.sh` runs that gate
first. A missing values file is a red gate, not a skipped one.

Exit 0 = every inline figure matches, 1 = a mismatch, an unparseable owner or a
missing owner, 2 = the formal build's output is missing.
"""

import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VALUES = ROOT / "tools" / "formal" / ".lake" / "values.jsonl"

V = "BtcPolicy."

ADR_0024 = "docs/adr/0024-the-wallet-import-settles-ten-blocks-below-the-scan.md"

# (file, requirement or None for a whole ADR, regex, emitted value names for the groups[, the
# owner this entry copies -- absent when the requirement IS the owner])
NUMBERS = [
    ("02-onchain-contract.md", "CHN-4", r"MUST be `older\((\d+)\)`", [V + "Timelock.defaultNSequence"]),
    ("02-onchain-contract.md", "CHN-4", r"lock of `(\d+)` units of (\d+) seconds",
     [V + "Timelock.defaultUnits", V + "Timelock.secondsPerUnit"]),
    ("02-onchain-contract.md", "CHN-4", r"type-flag bit (\d+) set", [V + "Timelock.typeFlagBit"]),
    ("02-onchain-contract.md", "CHN-4", r"that is (\d+) days", [V + "Timelock.defaultDays"]),
    ("02-onchain-contract.md", "CHN-4", r"`(\d+) \| \(1 << (\d+)\)`",
     [V + "Timelock.defaultUnits", V + "Timelock.typeFlagBit"]),
    # The default's copies: CHN-1's rendering, CHN-8's refusal, CHN-10's recovery spend. A copy
    # entry's fifth element names the owner whose declaration it reads.
    ("02-onchain-contract.md", "CHN-1", r"`RECOVERY_TIMELOCK` renders as `(\d+)`", [V + "Timelock.defaultNSequence"], "CHN-4"),
    ("02-onchain-contract.md", "CHN-8", r"an `older` other than `(\d+)`", [V + "Timelock.defaultNSequence"], "CHN-4"),
    ("02-onchain-contract.md", "CHN-10", r"`nSequence` to `(\d+)` exactly", [V + "Timelock.defaultNSequence"], "CHN-4"),
    ("02-onchain-contract.md", "CHN-2", r"MUST have `t ≥ (\d+)`", [V + "Shapes.minT"]),
    # Every occurrence of the shape formula in CHN-2, not only the first: both figures.
    ("02-onchain-contract.md", "CHN-2", r"`n = (\d+)t − (\d+)`", [V + "Shapes.coefficient", V + "Shapes.offset"]),
    ("02-onchain-contract.md", "CHN-34", r"`n = (\d+)t − (\d+)`", [V + "Shapes.coefficient", V + "Shapes.offset"], "CHN-2"),
    ("02-onchain-contract.md", "CHN-2", r"up to (\d+)-of-(\d+)", [V + "Shapes.maxT", V + "Shapes.maxN"]),
    ("02-onchain-contract.md", "CHN-2", r"`n ≤ (\d+)`", [V + "Shapes.nodeLimit"]),
    ("03-policy-checks.md", "POL-20", r"`(\d+) × cap`", [V + "Budget.upperMultiple"]),
    ("05-duress-and-lockdown.md", "DUR-30", r"anchor = tip − \(tip mod (\d+)\)", [V + "BumpTarget.anchorStep"]),
    ("05-duress-and-lockdown.md", "DUR-30", r"target = ⌊median / (\d+)⌋ × (\d+)",
     [V + "BumpTarget.quantum", V + "BumpTarget.quantum"]),
    ("06-node-channel.md", "NCH-12", r"\[now − (\d+), now \+ (\d+)\]", [V + "Freshness.past", V + "Freshness.future"]),
    ("08-wire-contract.md", "WIR-16", r"\[now − (\d+), now \+ (\d+)\]", [V + "Freshness.past", V + "Freshness.future"], "NCH-12"),
    ("06-node-channel.md", "NCH-13", r"below `now − (\d+)`", [V + "Freshness.pruneOffset"]),
    ("09-manifest-config-ceremony.md", "MAN-16",
     r"(\d+)-bit-wide value whose top bit is pinned — (\d+) bits of entropy",
     [V + "Preimage.width", V + "Preimage.publishedEntropy"]),
    ("09-manifest-config-ceremony.md", "MAN-16", r"a 2(\d+) search space", [V + "Preimage.publishedEntropy"]),
    ("09-manifest-config-ceremony.md", "MAN-16", r"exactly (\d+) hex characters \((\d+) bytes\)",
     [V + "Preimage.publishedHex", V + "Preimage.publishedBytes"]),
    ("09-manifest-config-ceremony.md", "MAN-9", r"`escape_coverage_pct` outside `(\d+)\.\.=(\d+)`",
     [V + "Coverage.floorPct", V + "Coverage.ceilingPct"]),
    ("04-spend-lifecycle.md", "SPN-38",
     r"rung_budget = max\(saturating_sub\(per_peer_quota_per_min, (\d+)\), (\d+)\)",
     [V + "Cursor.reserve", V + "Cursor.minimum"]),
    ("10-watchtower-and-chain.md", "WTC-6", r"delta walk of at most (\d+) blocks",
     [V + "VaultUnspent.deltaWindow"]),
    ("10-watchtower-and-chain.md", "WTC-6", r"and (\d+) blocks above that anchor",
     [V + "VaultUnspent.deltaWindow"]),
    ("10-watchtower-and-chain.md", "WTC-7", r"\*\*settled depth\*\* — (\d+) blocks",
     [V + "VaultUnspent.settledDepth"]),
    # ADR-0024's copies of the two figures. An ADR entry is checked against ADR_OWNERS' one
    # requirement; this ADR restates two requirements' figures, so each entry names its owner.
    (ADR_0024, None, r"The settled depth is (\d+) blocks", [V + "VaultUnspent.settledDepth"], "WTC-7"),
    (ADR_0024, None, r"the block (\d+) below it", [V + "VaultUnspent.settledDepth"], "WTC-7"),
    (ADR_0024, None, r"A reorg no deeper than (\d+) leaves", [V + "VaultUnspent.settledDepth"], "WTC-7"),
    (ADR_0024, None, r"and (\d+) blocks above its anchor", [V + "VaultUnspent.deltaWindow"], "WTC-6"),
    (ADR_0024, None, r"and (\d+) blocks above that anchor", [V + "VaultUnspent.deltaWindow"], "WTC-6"),
    (ADR_0024, None, r"carry the cache (\d+) blocks further", [V + "VaultUnspent.deltaWindow"], "WTC-6"),
    (ADR_0024, None, r"more than (\d+) blocks behind", [V + "VaultUnspent.deltaWindow"], "WTC-6"),
    (ADR_0024, None, r"at most (\d+) blocks each", [V + "VaultUnspent.deltaWindow"], "WTC-6"),
    # ADR-0014's prose around its rendered table (the table itself is a region).
    ("docs/adr/0014-hot-spend-bound.md", None, r"take a (\d+)-of-(\d+) federation with no compromised node",
     [V + "Budget.params.t", V + "Budget.params.n"]),
    ("docs/adr/0014-hot-spend-bound.md", None, r"hot_window_secs = max_commitment_age_secs = (\d+)", [V + "Budget.params.window"]),
    ("docs/adr/0014-hot-spend-bound.md", None, r"hold_secs = (\d+)", [V + "Budget.params.hold"]),
    ("docs/adr/0014-hot-spend-bound.md", None, r"combine_slack_secs = (\d+)", [V + "Budget.params.slack"]),
    ("docs/adr/0014-hot-spend-bound.md", None, r"delivery_horizon_secs = (\d+)", [V + "Budget.params.horizon"]),
    ("docs/adr/0014-hot-spend-bound.md", None, r"`\[(\d+), (\d+)\)` has length (\d+) and contains `(\d+)V`",
     [V + "Budget.intervalStart", V + "Budget.intervalEnd", V + "Budget.statedLength", V + "Budget.statedTotalV"]),
    ("docs/adr/0014-hot-spend-bound.md", None, r"withdrawn `(\d+)/(\d+) × V` bound",
     [V + "Budget.withdrawnNumerator", V + "Budget.withdrawnDenominator"]),
]

# (file, owner id, emitted text name): the emitted string must appear in the owner's body.
TEXTS = [
    ("03-policy-checks.md", "POL-20", V + "Budget.c0Formula"),
    ("03-policy-checks.md", "POL-20", V + "Budget.coefFormula"),
    ("03-policy-checks.md", "POL-20", V + "Budget.fullToleranceFormula"),
    ("04-spend-lifecycle.md", "SPN-38", V + "Cursor.affordableFormula"),
    ("04-spend-lifecycle.md", "SPN-38", V + "Cursor.saturatingFormula"),
    ("04-spend-lifecycle.md", "SPN-38", V + "Cursor.zeroRule"),
    ("04-spend-lifecycle.md", "SPN-38", V + "Cursor.startFormula"),
    ("04-spend-lifecycle.md", "SPN-38", V + "Cursor.capFormula"),
    ("04-spend-lifecycle.md", "SPN-38", V + "Cursor.anchorSentence"),
]

# (regex, per-group admissible emitted values): scanned over EVERY document, every match must
# agree. The owner registry above binds a figure where it is stated; this binds every place the
# set restates it -- DOM-8's and POL-20's `n = 2t − 1`, CNF-6's timelock figures, CNF-61's
# window -- without a registry that a new copy could silently miss. Only patterns whose every
# occurrence means the same thing belong here; `hold_secs = 20` does not (configs carry other
# values), `2-of-3` does not (the recovery keyset is 2-of-3 for its own reason).
ANYWHERE = [
    # The equality (the rule) and the refusal (`n ≠`) are separate patterns with separate
    # baselines, so turning one into the other in a copy is a fall in one of them.
    (r"n = (\d+)t − (\d+)", [[V + "Shapes.coefficient"], [V + "Shapes.offset"]]),
    (r"n ≠ (\d+)t − (\d+)", [[V + "Shapes.coefficient"], [V + "Shapes.offset"]]),
    # `older(…)` means the default everywhere EXCEPT the two trap phrasings CHN-4 and CNF-6 use
    # for the bare-units height lock, which are matched separately so each context has one value.
    (r"older\((\d+)\)(?!` (?:would be|by name))", [[V + "Timelock.defaultNSequence"]]),
    (r"older\((\d+)\)` (?:would be|by name)", [[V + "Timelock.defaultUnits"]]),
    (r"\((\d+) − (\d+)/t\)", [[V + "Budget.upperMultiple"], [V + "Budget.c0Numerator"]]),
    (r"(\d+) \| \(1 << (\d+)\)", [[V + "Timelock.defaultUnits"], [V + "Timelock.typeFlagBit"]]),
    (r"(\d+) = (\d+) \| \(1 << (\d+)\)",
     [[V + "Timelock.defaultNSequence"], [V + "Timelock.defaultUnits"], [V + "Timelock.typeFlagBit"]]),
    (r"`?(\d+)`? units of (\d+) seconds", [[V + "Timelock.defaultUnits"], [V + "Timelock.secondsPerUnit"]]),
    (r"(\d+)-day default", [[V + "Timelock.defaultDays"]]),
    (r"\b(\d+) days\b", [[V + "Timelock.defaultDays"]]),   # every "N days" in the set is the default
    (r"\[now − (\d+), now \+ (\d+)\]", [[V + "Freshness.past"], [V + "Freshness.future"]]),
    (r"(\d+) bits of entropy", [[V + "Preimage.publishedEntropy"]]),
    (r"2(\d+) (?:search )?space", [[V + "Preimage.publishedEntropy"]]),
    # CHN-2's bounds as the set restates them. `t ≥ N` is NOT here: 08-wire-contract.md's `t ≥ 8`
    # is a different bound, so that one stays owner-only.
    (r"\bt < (\d+)", [[V + "Shapes.minT"]]),
    (r"\bn ≤ (\d+)", [[V + "Shapes.nodeLimit"]]),
    (r"\bn > (\d+)", [[V + "Shapes.nodeLimit"]]),
    (r"up to (\d+)-of-(\d+)", [[V + "Shapes.maxT"], [V + "Shapes.maxN"]]),
]

# The corpus scan fails closed on ZERO hits; a known copy that stops matching while another
# still hits would otherwise vanish from validation silently. So the hit count per pattern is
# a ratchet against this baseline: it may rise (a new copy, recorded), never fall.
BASELINE = ROOT / "tools" / "copies-baseline.json"

# A count cannot see a SWAP: one copy made unrecognisable and a valid one added in the same
# file leaves the per-file count unchanged. So every corpus-wide pattern is also scanned with
# its operands wildcarded to a word (its SHAPE), and a shape hit the exact pattern does not
# match at the same place is a malformed copy, red by name. Two patterns are exempt because
# their shape is ordinary prose or a named constant, not a copy: `within days` / `fifteen days`
# (an ADR about a different duration) and `older(RECOVERY_TIMELOCK)` (CHN-1's name for it).
SHAPE_EXEMPT = {r"\b(\d+) days\b", r"older\((\d+)\)(?!` (?:would be|by name))"}


def shape_of(pattern):
    return pattern.replace(r"(\d+)", r"(\w+)")

SUPERSCRIPT = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")


sys.path.insert(0, str(ROOT / "tools"))
from check_citations import read_index  # noqa: E402  -- one index reader, not two


# An ADR that hosts a requirement's worked figures: the declarations it reads are tagged with
# that requirement, and an entry against the ADR file is checked against this tag.
ADR_OWNERS = {"docs/adr/0014-hot-spend-bound.md": "POL-20"}


def values():
    """{decl or decl.part: value}, and {decl: tag}. Every decl must be a tagged declaration: an
    emitted value is "a scalar or formula string a tagged declaration owns" (ADR-0023 decision
    5), and a refusal must name a declaration a reader can open."""
    if not VALUES.exists():
        print(f"FAIL: {VALUES} missing -- run tools/check_formal.sh first "
              f"(check-all.sh orders it before this gate)")
        sys.exit(2)
    index = read_index()
    out = {}
    for row in map(json.loads, VALUES.read_text().splitlines()):
        if row["decl"] not in index:
            raise ValueError(f"emitted value {row['decl']} is not a tagged declaration")
        if row["req"] != index[row["decl"]]:
            raise ValueError(f"emitted value {row['decl']} claims {row['req']} but the declaration "
                             f"is tagged {index[row['decl']]}")
        out[row["decl"] + ("." + row["part"] if row["part"] else "")] = row["value"]
    return out, index


def owner_of(name):
    return name.rsplit(".", 1)[0] if name.count(".") > 2 and name.split(".")[-1] in (
        "t", "n", "window", "hold", "slack", "horizon") else name


def requirement(file, rid):
    """The owner's body, whitespace-normalised; the whole file for an ADR."""
    text = (ROOT / file).read_text()
    if rid is None:
        return " ".join(text.split()).translate(SUPERSCRIPT)
    match = re.search(r"^\*\*" + re.escape(rid) + r"\*\*.*?(?=^\*\*[A-Z]+-\d+\*\*|\Z)",
                      text, re.M | re.S)
    if not match:
        raise ValueError(f"{file}: missing {rid}")
    return " ".join(match.group().split()).translate(SUPERSCRIPT)


def main():
    emitted, index = values()
    failures = 0

    def tagged_with(names, expected, where):
        """Each declaration an entry reads must be tagged with the entry's owner: a retagged
        declaration, retagged consistently in Render.values, is otherwise still compared to
        the old owner's prose (one rule, one home)."""
        nonlocal failures
        for name in names:
            decl = owner_of(name)
            if index.get(decl) != expected:
                print(f"  {where} reads {decl}, tagged {index.get(decl)}, as if it were {expected}'s")
                failures += 1

    for entry in NUMBERS:
        file, rid, pattern, names = entry[:4]
        copied = entry[4] if len(entry) > 4 else None
        owner = rid or os.path.basename(file)
        tagged_with(names, copied or rid or ADR_OWNERS[file], owner)
        body = requirement(file, rid)
        matches = list(re.finditer(pattern, body))
        if not matches:
            raise ValueError(f"{owner}: cannot parse published arithmetic: {pattern}")
        # EVERY occurrence in the owner's body, not the first: a formula the requirement
        # states twice can drift in its second statement.
        for match in matches:
            for group, name in zip(match.groups(), names):
                if name not in emitted:
                    raise ValueError(f"{owner}: {name} is not an emitted value")
                if int(group) != int(emitted[name]):
                    print(f"  {owner} publishes {group} where {name} emits {emitted[name]} ({pattern})")
                    failures += 1
                else:
                    print(f"OK {owner} {name.removeprefix(V)} = {group}")
    # CHN-2's published shapes are a subset of the declaration's list.
    body = requirement("02-onchain-contract.md", "CHN-2")
    shapes = set(emitted[V + "Shapes.shapes"].split(", "))
    for t, n in re.findall(r"(\d+)-of-(\d+)", body):
        if f"{t}-of-{n}" not in shapes:
            print(f"  CHN-2 publishes {t}-of-{n}, which {V}Shapes.shapes does not emit")
            failures += 1
    print(f"OK CHN-2 published shapes ⊆ {sorted(shapes)}")
    import glob
    try:
        baseline = json.loads(BASELINE.read_text())["hits"]
    except OSError:
        baseline = {}
    except (KeyError, ValueError):
        raise ValueError(f"{BASELINE.name} is unreadable -- regenerate it with --write")
    if not all(isinstance(v, dict) for v in baseline.values()):
        raise ValueError(f"{BASELINE.name} is not per-file -- regenerate it with --write")
    counts = {}
    for pattern, groups in ANYWHERE:
        hits = 0
        counts[pattern] = {}
        for file in sorted(glob.glob(str(ROOT / "*.md"))) + sorted(glob.glob(str(ROOT / "docs/adr/*.md"))):
            body = " ".join(open(file).read().split()).translate(SUPERSCRIPT)
            for match in re.finditer(pattern, body):
                hits += 1
                rel = os.path.relpath(file, ROOT)
                counts[pattern][rel] = counts[pattern].get(rel, 0) + 1
                for group, names in zip(match.groups(), groups):
                    admissible = {int(emitted[n]) for n in names}
                    if int(group) not in admissible:
                        print(f"  {os.path.basename(file)} publishes {group} where "
                              f"{' or '.join(n.removeprefix(V) for n in names)} emits {sorted(admissible)} ({pattern})")
                        failures += 1
            if pattern not in SHAPE_EXEMPT:
                exact = re.compile(pattern)
                for match in re.finditer(shape_of(pattern), body):
                    if not exact.match(body, match.start()):
                        print(f"  {os.path.basename(file)} carries {match.group()!r}, shaped like "
                              f"{pattern} but not matching it -- a malformed copy")
                        failures += 1
        if hits == 0:
            raise ValueError(f"corpus-wide pattern matched nothing: {pattern}")
        # Per FILE, not an aggregate: a copy that stops matching in one file while a new one
        # appears in another must not net to zero.
        fell = {f: (n, counts[pattern].get(f, 0)) for f, n in baseline.get(pattern, {}).items()
                if counts[pattern].get(f, 0) < n}
        if fell:
            print(f"  copies of {pattern} stopped matching: {fell} (recorded, found) -- edit the "
                  f"copy back, or its owner's declaration, together")
            failures += 1
        else:
            print(f"OK {hits} occurrence(s) of {pattern} agree")
    removed = [pattern for pattern in baseline if pattern not in counts]
    for pattern in removed:
        print(f"  pattern {pattern} is in the baseline but no longer scanned -- removing a "
              f"pattern removes a check; record it with --write if that is meant")
    if counts != baseline:
        # A rise is a new copy and must be RECORDED, in the same commit, or CI only ever
        # rewrites an ephemeral checkout and the ratchet never persists; a fall was reported
        # above. `--write` regenerates, as the regions gate's does -- and a removed pattern is
        # exactly what `--write` is for, so it does not block the write.
        if "--write" in sys.argv and not failures:
            BASELINE.write_text(json.dumps({"hits": counts, "note": "Hit count per corpus-wide "
                "pattern, per file. Ratchet: may rise (a new copy, recorded with `check_copies.py --write`), "
                "never fall (a copy that stopped matching)."}, indent=2, ensure_ascii=False) + "\n")
            print(f"baseline written: {len(counts)} pattern(s)")
        else:
            risen = {k: {f: (baseline.get(k, {}).get(f, 0), n) for f, n in v.items()
                         if n > baseline.get(k, {}).get(f, 0)} for k, v in counts.items()}
            risen = {k: v for k, v in risen.items() if v}
            if risen:
                print(f"  new copies found, not recorded: {risen} -- run tools/check_copies.py --write "
                      f"and commit tools/copies-baseline.json with the copy")
                failures += 1
            failures += len(removed)
    for file, rid, name in TEXTS:
        tagged_with([name], rid, rid)
        body = requirement(file, rid)
        text = " ".join(emitted[name].split())
        if text not in body:
            print(f"  {rid} missing the text {name} emits: {text}")
            failures += 1
        else:
            print(f"OK {rid} carries {name.removeprefix(V)}")
    if failures:
        print(f"\nFAIL: {failures} inline figure(s) differ from what the declarations emit. "
              f"Change the declaration and the sentence together.")
        return 1
    print("All inline figures match their declarations.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print(f"FAIL: {error}")
        sys.exit(1)
