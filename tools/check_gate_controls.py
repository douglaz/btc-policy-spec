#!/usr/bin/env python3
"""Run document mutations against a gate in disposable copies.

A clean positive control must pass first. Each negative control must exit 1 and
name its intended failure; a crash or an unrelated failure is not evidence.
"""

import argparse
import base64
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def replace_once(path, old, new):
    text = path.read_text()
    if text.count(old) != 1:
        raise ValueError(f"control needs exactly one {old!r} in {path.name}")
    path.write_text(text.replace(old, new))


def text_control(file, old, new):
    return lambda root: replace_once(root / file, old, new)


def psbt_control(kind):
    def mutate(root):
        path = root / "08-wire-contract.md"
        text = path.read_text()
        start = text.index("**WIR-7**")
        match = re.search(r"```json\n(.*?)\n```", text[start:], re.S)
        doc = json.loads(match.group(1))
        binary = base64.b64decode(doc["spend"]["spend"])
        if kind == "truncated":
            binary = binary[:-1]
        elif kind == "trailing":
            binary += b"\x00"
        elif kind == "duplicate":
            # WIR-7's single global key/value has a one-byte transaction length.
            end = 8 + binary[7]
            binary = binary[:end] + binary[5:end] + binary[end:]
        elif kind == "transaction":
            # The unsigned transaction's first CompactSize is its input count.
            binary = binary[:12] + b"\xfc" + binary[13:]
        elif kind == "compact":
            binary = binary[:5] + b"\xfd\x01\x00" + binary[6:]
        else:
            raise ValueError(f"unknown mutation {kind}")
        doc["spend"]["spend"] = base64.b64encode(binary).decode()
        text = text[:start + match.start(1)] + json.dumps(doc) + text[start + match.end(1):]
        path.write_text(text)
    return mutate


def corrupt_node_key(root):
    path = root / "tools/protocol-vectors.json"
    doc = json.loads(path.read_text())
    secret = doc["node_key"]["signing_secret"]
    doc["node_key"]["signing_secret"] = ("0" if secret[0] != "0" else "1") + secret[1:]
    path.write_text(json.dumps(doc, indent=2) + "\n")


def corrupt_descriptor(root):
    path = root / "tools/protocol-vectors.json"
    doc = json.loads(path.read_text())
    entry = doc["descriptor_manifest"]["descriptors"][0]
    text = entry["canonical"]
    entry["canonical"] = text[:-1] + ("q" if text[-1] != "q" else "p")
    path.write_text(json.dumps(doc, indent=2) + "\n")


def corrupt_sealed_field(field):
    """A sealed value is only uniform because MAN-2 covers it (F50, F15)."""
    def mutate(root):
        path = root / "tools/protocol-vectors.json"
        doc = json.loads(path.read_text())
        doc["descriptor_manifest"]["manifest"][field] += 1
        path.write_text(json.dumps(doc, indent=2) + "\n")
    return mutate


def remove_fenced_vectors(root):
    pattern = re.compile(r"^```vector\s*\n.*?^```\s*\n?", re.M | re.S)
    removed = 0
    for path in list(root.glob("*.md")) + list((root / "docs/adr").glob("*.md")):
        text, count = pattern.subn("", path.read_text())
        if count:
            path.write_text(text)
            removed += count
    if not removed:
        raise ValueError("control needs published fenced vectors to remove")


COPIES = [
    # Each is an edit to an OWNING sentence or one of its copies; the copies gate reads the
    # figure back and compares it to what the declaration emits (ADR-0023 decision 5).
    ("release quota rule", text_control("04-spend-lifecycle.md", "saturating_sub(per_peer_quota_per_min, 2)", "saturating_sub(per_peer_quota_per_min, 3)"), "SPN-38 publishes 3 where BtcPolicy.Cursor.reserve emits 2"),
    # The cursor-anchored cap livelocks a candidate whose lowest admissible rung is above it (F51).
    ("cursor-anchored cap", text_control("04-spend-lifecycle.md", "`quota_rung_cap = min(last_rung_index, F + affordable_rungs − 1)`", "`quota_rung_cap = min(last_rung_index, release_floor + affordable_rungs − 1)`"), "SPN-38 missing the text BtcPolicy.Cursor.capFormula"),
    ("timelock value", text_control("02-onchain-contract.md", "MUST be `older(4224679)`", "MUST be `older(4224680)`"), "CHN-4 publishes 4224680 where BtcPolicy.Timelock.defaultNSequence emits 4224679"),
    ("timelock copy in CHN-8", text_control("02-onchain-contract.md", "an `older` other than `4224679`", "an `older` other than `4224678`"), "CHN-8 publishes 4224678"),
    ("timelock days", text_control("02-onchain-contract.md", "that is 180 days", "that is 181 days"), "CHN-4 publishes 181 where BtcPolicy.Timelock.defaultDays emits 180"),
    ("missing owner", text_control("02-onchain-contract.md", "**CHN-4**", "**CHN-404**"), "missing CHN-4"),
    ("unrecognised owner wording", text_control("02-onchain-contract.md", "that is 180 days", "that is six months"), "CHN-4: cannot parse"),
    ("federation shape", text_control("02-onchain-contract.md", "up to 8-of-15", "up to 8-of-14"), "CHN-2 publishes 14 where BtcPolicy.Shapes.maxN emits 15"),
    ("shape formula", text_control("02-onchain-contract.md", "`t ≥ 2` and exactly `n = 2t − 1`", "`t ≥ 2` and exactly `n = 3t − 1`"), "CHN-2 publishes 3 where BtcPolicy.Shapes.coefficient emits 2"),
    ("shape formula copy in CHN-34", text_control("02-onchain-contract.md", "production shape `n = 2t − 1` (`CHN-2`)", "production shape `n = 2t − 2` (`CHN-2`)"), "CHN-34 publishes 2 where BtcPolicy.Shapes.offset emits 1"),
    ("admission coefficient", text_control("03-policy-checks.md", "`(2 − 1/t)`", "`(3 − 1/t)`"), "POL-20 missing the text BtcPolicy.Budget.c0Formula"),
    ("quantisation multiplier", text_control("05-duress-and-lockdown.md", "`target = ⌊median / 5⌋ × 5`", "`target = ⌊median / 5⌋ × 6`"), "DUR-30 publishes 6 where BtcPolicy.BumpTarget.quantum emits 5"),
    ("freshness width", text_control("06-node-channel.md", "`timestamp ∈ [now − 300, now + 60]`", "`timestamp ∈ [now − 301, now + 60]`"), "NCH-12 publishes 301 where BtcPolicy.Freshness.past emits 300"),
    ("freshness copy in WIR-16", text_control("08-wire-contract.md", "| freshness window | `[now − 300, now + 60]` seconds |", "| freshness window | `[now − 300, now + 61]` seconds |"), "WIR-16 publishes 61 where BtcPolicy.Freshness.future emits 60"),
    ("entropy", text_control("09-manifest-config-ceremony.md", "pinned — 62 bits of entropy", "pinned — 61 bits of entropy"), "MAN-16 publishes 61 where BtcPolicy.Preimage.publishedEntropy emits 62"),
    ("delayed-holder parameter", text_control("docs/adr/0014-hot-spend-bound.md", "`hold_secs = 20`", "`hold_secs = 21`"), "0014-hot-spend-bound.md publishes 21 where BtcPolicy.Budget.params.hold emits 20"),
    ("settled depth copy in ADR-0024", text_control("docs/adr/0024-the-wallet-import-settles-ten-blocks-below-the-scan.md", "The settled depth is 10 blocks", "The settled depth is 11 blocks"), "0024-the-wallet-import-settles-ten-blocks-below-the-scan.md publishes 11 where BtcPolicy.VaultUnspent.settledDepth emits 10"),
    ("delta window copy in ADR-0024", text_control("docs/adr/0024-the-wallet-import-settles-ten-blocks-below-the-scan.md", "carry the cache 32 blocks further", "carry the cache 33 blocks further"), "0024-the-wallet-import-settles-ten-blocks-below-the-scan.md publishes 33 where BtcPolicy.VaultUnspent.deltaWindow emits 32"),
]
COPIES += [
    # Restatements away from the owner, caught by the corpus-wide scan.
    ("shape formula copy in DOM-8", text_control("01-domain-model.md", "exactly `n = 2t − 1` members", "exactly `n = 2t − 2` members"), "01-domain-model.md publishes 2 where Shapes.offset emits [1]"),
    ("timelock figures copy in CNF-6", text_control("15-conformance-checklist.md", "`4224679 = 30375 | (1 << 22)`", "`4224679 = 30376 | (1 << 22)`"), "15-conformance-checklist.md publishes 30376 where Timelock.defaultUnits emits [30375]"),
    ("freshness copy in CNF-61", text_control("15-conformance-checklist.md", "An envelope one second outside `[now − 300, now + 60]`", "An envelope one second outside `[now − 300, now + 61]`"), "15-conformance-checklist.md publishes 61 where Freshness.future emits [60]"),
]


COPIES += [
    ("c0 figure copy in README", text_control("README.md", "`POL-20`'s `(2 − 1/t)`", "`POL-20`'s `(3 − 1/t)`"), "README.md publishes 3 where Budget.upperMultiple emits [2]"),
    ("default timelock example turned into the trap", text_control("08-wire-contract.md", "older(4224679)", "older(30375)"), "08-wire-contract.md publishes 30375 where Timelock.defaultNSequence emits [4224679]"),
]


COPIES += [
    ("encoded value in CNF-6's equation", text_control("15-conformance-checklist.md", "`4224679 = 30375 | (1 << 22)`", "`4224680 = 30375 | (1 << 22)`"), "15-conformance-checklist.md publishes 4224680 where Timelock.defaultNSequence emits [4224679]"),
    ("inequality-form shape copy in MAN-9", text_control("09-manifest-config-ceremony.md", "n ≠ 2t − 1", "n ≠ 2t − 2"), "09-manifest-config-ceremony.md publishes 2 where Shapes.offset emits [1]"),
]
def dedent_both_markers(root):
    path = root / "docs/adr/0014-hot-spend-bound.md"
    text = path.read_text()
    old_b, old_e = "  <!-- formal: BtcPolicy.Render.adr0014Timeline -->", "  <!-- /formal -->"
    if text.count(old_b) != 1 or text.count(old_e) != 1:
        raise ValueError("control needs exactly one indented ADR-0014 region")
    path.write_text(text.replace(old_b, old_b.strip()).replace(old_e, old_e.strip()))


REGIONS_EXTRA = [
    ("one dedented marker around the ADR-0014 table", text_control("docs/adr/0014-hot-spend-bound.md", "  <!-- formal: BtcPolicy.Render.adr0014Timeline -->", "<!-- formal: BtcPolicy.Render.adr0014Timeline -->"), "is not indented like its opening marker"),
    ("both markers dedented around the ADR-0014 table", dedent_both_markers, "markers are indented '' but its declaration emits '  '"),
]


COPIES += [
    ("node limit copy in CNF-79", text_control("15-conformance-checklist.md", "`t ≥ 2, n = 2t − 1, n ≤ 15`", "`t ≥ 2, n = 2t − 1, n ≤ 16`"), "15-conformance-checklist.md publishes 16 where Shapes.nodeLimit emits [15]"),
    ("a copy with a wrong operand", text_control("README.md", "`POL-20`'s `(2 − 1/t)`", "`POL-20`'s `(2 − 2/t)`"), "README.md publishes 2 where Budget.c0Numerator emits [1]"),
    ("a copy that stops matching", text_control("README.md", "`POL-20`'s `(2 − 1/t)`", "`POL-20`'s `(2 − one/t)`"), "stopped matching: {'README.md': (1, 0)}"),
    ("a malformed new copy", text_control("00-overview.md", "**OVR-11** Covenants are out of scope.", "**OVR-11** Covenants are out of scope; the coefficient is `(2 − 2/t)`."), "00-overview.md publishes 2 where Budget.c0Numerator emits [1]"),
]


def swap_copy(root):
    """One copy made unrecognisable and a valid one added in the same file: the per-file hit
    count is unchanged, so only the shape scan can see it."""
    path = root / "README.md"
    replace_once(path, "`POL-20`'s `(2 − 1/t)`", "`POL-20`'s `(3 − one/t)`")
    path.write_text(path.read_text() + "\nThe coefficient is `(2 − 1/t)`.\n")


COPIES += [
    ("a malformed copy swapped for a valid one in the same file", swap_copy, "README.md carries '(3 − one/t)', shaped like \\((\\d+) − (\\d+)/t\\) but not matching it"),
]


COPIES += [
    ("a new copy without the baseline", text_control("00-overview.md", "**OVR-11** Covenants are out of scope.", "**OVR-11** Covenants are out of scope; the federation is `n = 2t − 1`."), "new copies found, not recorded"),
]


COPIES += [
    ("equality turned into a refusal in DOM-8", text_control("01-domain-model.md", "exactly `n = 2t − 1` members", "exactly `n ≠ 2t − 1` members"), "copies of n = (\\d+)t − (\\d+) stopped matching"),
]


COPIES += [
    ("days copy in CNF-6", text_control("15-conformance-checklist.md", "is a time-based relative lock of 180\n      days;", "is a time-based relative lock of 181\n      days;"), "15-conformance-checklist.md publishes 181 where Timelock.defaultDays emits [180]"),
]


def untagged_value(root):
    path = root / "tools/formal/.lake/values.jsonl"
    path.write_text(path.read_text() + json.dumps(
        {"decl": "BtcPolicy.Nowhere.stray", "req": "CHN-4", "part": "", "value": "1"}) + "\n")


COPIES.append(("emitted value with no tagged declaration", untagged_value,
               "emitted value BtcPolicy.Nowhere.stray is not a tagged declaration"))

REGIONS = [
    # Each is a hand edit inside or around a rendered region; the regions gate diffs it against
    # the declaration. The three table controls the arithmetic gate carried live here, plus more.
    ("release quota boundary", text_control("04-spend-lifecycle.md", "| 3 | 2 | 0 | 0 | 3 | none | none |", "| 3 | 2 | 0 | 0 | 3 | 0 | none |"), "BtcPolicy.Render.spn38Table drifted"),
    ("dropped a>0 boundary rows", text_control("04-spend-lifecycle.md", "| 3 | 1 | 0 | 1 | 3 | 1 | 0 |\n| 3 | 1 | 0 | 3 | 3 | 3 | 0 |\n| 600 | 1 | 0 | 2 | 3 | 3 | 3 |", "| 3 | 1 | 0 | 0 | 3 | 0 | 0 |"), "BtcPolicy.Render.spn38Table drifted"),
    ("delayed-holder completion", text_control("docs/adr/0014-hot-spend-bound.md", "| 141 | The second Hold ends", "| 142 | The second Hold ends"), "BtcPolicy.Render.adr0014Timeline drifted"),
]
REGIONS += REGIONS_EXTRA
REGIONS += [
    ("a heading between SPN-38 and its table", text_control("04-spend-lifecycle.md", "\n<!-- formal: BtcPolicy.Render.spn38Table -->", "\n## An unrelated section\n\n<!-- formal: BtcPolicy.Render.spn38Table -->"), "is tagged SPN-38 but sits in None"),
    # SPN-5's three decided columns are a `match` region: a staging cell flipped in the document
    # (gate 13, body row 15 counting the marker rows) is red against Gates.rows.
    ("gate 13 no longer staging", text_control("04-spend-lifecycle.md", "| `consumed` | `yes` | `yes` |\n| 14 |", "| `consumed` | `yes` | `no` |\n| 14 |"), "spn5Gates: row 15, column 6: declaration says ['`yes`'], document says ['`no`']"),
    # The key column is the plain gate number: a renumbered row is red too.
    ("gate 14 renumbered", text_control("04-spend-lifecycle.md", "| 14 | PIN attempt budget", "| 41 | PIN attempt budget"), "spn5Gates: row 16, key column: expected ['14'] in order, document has ['41']"),
    # ADR-0023's published trace is a rendered region: one hex digit of the preimage flipped in the
    # document is drift against BtcPolicy.Trace.encode of the published trace.
    ("trace preimage digit", text_control("docs/adr/0023-a-formalized-clause-lives-in-lean-and-the-markdown-renders-it.md", "0000050000000264000000", "0000050000000264000001"), "BtcPolicy.Render.traceVector drifted"),
]

def corrupt_witness_weight(field):
    def mutate(root):
        path = root / "tools/protocol-vectors.json"
        doc = json.loads(path.read_text())
        if field == "shape_table":
            doc["witness_weight"]["shape_table"][3]["max_witness_weight_per_input"] -= 1
        elif field == "drop_row":
            del doc["witness_weight"]["shape_table"][3]
        elif field == "worked":
            doc["witness_weight"]["worked_transaction"]["maximum_finalized_vsize"] -= 1
        else:
            doc["witness_weight"][field] -= 1
        path.write_text(json.dumps(doc, indent=2) + "\n")
    return mutate


FIXTURES = [
    ("truncated PSBT", psbt_control("truncated"), "truncated PSBT"),
    ("PSBT trailing byte", psbt_control("trailing"), "trailing bytes"),
    ("duplicate PSBT map key", psbt_control("duplicate"), "duplicate PSBT map key"),
    ("nonminimal CompactSize", psbt_control("compact"), "noncanonical CompactSize"),
    ("malformed unsigned transaction", psbt_control("transaction"), "truncated PSBT field or unsigned transaction"),
    # A descriptor string smuggles keys and a checksum past every field-name check (F50).
    ("bad descriptor checksum", text_control("08-wire-contract.md", "))))#6rzn6n8d", "))))#6rzn6n8e"), "does not verify"),
    ("off-curve descriptor key", text_control("08-wire-contract.md", "multi(2,02531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337", "multi(2,03b0a1c2d3e4f5061728394a5b6c7d8e9fa0b1c2d3e4f5061728394a5b6c7d8e9f"), "not a point on secp256k1"),
    ("non-canonical node order", text_control("08-wire-contract.md", "multi(2,02531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337,031b84c5", "multi(2,03b8039cfb1e7998e2bcc12b50abffbbadffe815486af0b82c118d0f62e35863ed,031b84c5"), "not in ascending order"),
    ("malformed pubkey field", text_control("08-wire-contract.md", "{\"node_id\": 0, \"signing_pubkey\": \"031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f\"", "{\"node_id\": 0, \"signing_pubkey\": \"031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd07\""), "must be a 33-byte compressed pubkey"),
    ("off-curve pubkey field", text_control("08-wire-contract.md", "{\"node_id\": 0, \"signing_pubkey\": \"031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f\"", "{\"node_id\": 0, \"signing_pubkey\": \"03b0a1c2d3e4f5061728394a5b6c7d8e9fa0b1c2d3e4f5061728394a5b6c7d8e9f\""), "not a point on secp256k1"),
    # WIR-13/WIR-14 once carried an extended key that decoded to 63 bytes (F50).
    ("truncated extended key", text_control("08-wire-contract.md", "tpubD9B2uSXfMA5WjnUHQ12QD8joJPQYmnZBULNcx7KD8gSDGhQiGJyvvAYLUKkMz2ZiB61EmvWfrdZntfTAyxFkFtphnf9sEAeLtLerypGCvte/*)\", \"master_fingerprint", "tpubD9B2uSXfMA5WjnUHQ12QD8joJPQYmnZBULNcx7KD8gSDGhQiGJyvvAYLUKkMz2ZiB61EmvWfrdZntfTAyxFkFtphnf9sEAeLtLerypGCvt/*)\", \"master_fingerprint"), "Base58Check"),
]
VECTORS = [
    ("node-key derivation result", corrupt_node_key, "node-key signing_secret"),
    ("canonical descriptor result", corrupt_descriptor, "canonical descriptor"),
    ("missing fenced vectors", remove_fenced_vectors, "no ```vector blocks found"),
    ("sealed policy_version", corrupt_sealed_field("policy_version"), "manifest preimage differs"),
    ("sealed refresh interval", corrupt_sealed_field("refresh_min_interval_secs"), "manifest preimage differs"),
    ("sealed refresh feerate", corrupt_sealed_field("refresh_max_feerate"), "manifest preimage differs"),
    ("published Argon2 parallelism", text_control("09-manifest-config-ceremony.md", "parallelism `p = 1`", "parallelism `p = 2`"), "node-key signing_secret"),
    ("published Argon2 version", text_control("09-manifest-config-ceremony.md", "version `0x13` (decimal 19)", "version `0x10` (decimal 16)"), "node-key signing_secret"),
    # CHN-34 must be measured from serialized bytes, so both halves have to be breakable (F51).
    ("published W_N", corrupt_witness_weight("max_witness_weight_per_input"), "serialized witness measures"),
    ("published witness script size", corrupt_witness_weight("witness_script_bytes"), "serialized witness script differs"),
    ("published worked vsize", corrupt_witness_weight("worked"), "worked transaction vsize differs"),
    ("published shape table row", corrupt_witness_weight("shape_table"), "witness measures"),
    # A shape table missing a CHN-2 shape passed the gate (F56).
    ("dropped shape table row", corrupt_witness_weight("drop_row"), "shape table covers"),
    ("CHN-34 outer framing term", text_control("02-onchain-contract.md", "⌊(4 × B + 2 + input_count × W_N + 3) / 4⌋", "⌊(4 × B + 1 + input_count × W_N + 3) / 4⌋"), "worked transaction weight measures"),
    ("CHN-34 W_N constant", text_control("02-onchain-contract.md", "W_N = 73 × t + 34 × n + 232", "W_N = 73 × t + 34 × n + 233"), "measured witness disagrees"),
    ("CHN-34 DER ceiling", text_control("02-onchain-contract.md", "at most 71 bytes of strict-DER", "at most 72 bytes of strict-DER"), "maximum DER measures"),
    ("CHN-34 script-size term", text_control("02-onchain-contract.md", "witness script is\n`34 × n + 152` bytes", "witness script is\n`34 × n + 153` bytes"), "witness script measures"),
    # The first `sha256 =` block in any document, ADR-0023's published trace: the gate's plain-SHA-256
    # branch must go red when one digit of the published digest is flipped.
    ("trace digest digit", text_control("docs/adr/0023-a-formalized-clause-lives-in-lean-and-the-markdown-renders-it.md", "sha256 = 044512aa477ac903226ee0c1fc346101d8d95f20dbd7c1e24238c037c8b79fe1", "sha256 = 144512aa477ac903226ee0c1fc346101d8d95f20dbd7c1e24238c037c8b79fe1"), "document says"),
]


def skip_build(directory, names):
    """The Python gates read only the three .jsonl files under tools/formal/.lake; the
    441 MB build tree beside them is never opened, so it is not copied 22 times per run."""
    skip = {".git", "__pycache__", ".venv"}
    if Path(directory).name == ".lake":
        skip.add("build")
    return [n for n in names if n in skip]


def run_gate(root, gate):
    return subprocess.run([sys.executable, str(root / "tools" / f"check_{gate}.py")],
                          cwd=root, text=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gate", choices=("copies", "regions", "fixtures", "vectors"))
    gate = parser.parse_args().gate
    controls = {"copies": COPIES, "regions": REGIONS, "fixtures": FIXTURES, "vectors": VECTORS}[gate]
    with tempfile.TemporaryDirectory(prefix=f"btc-spec-{gate}-controls-") as directory:
        pristine = Path(directory) / "pristine"
        shutil.copytree(ROOT, pristine, ignore=skip_build)
        positive = run_gate(pristine, gate)
        if positive.returncode != 0:
            raise ValueError(f"positive control failed:\n{positive.stdout}{positive.stderr}")
        for name, mutate, expected in controls:
            scratch = Path(directory) / "mutant"
            shutil.copytree(pristine, scratch)
            mutate(scratch)
            result = run_gate(scratch, gate)
            shutil.rmtree(scratch)
            if result.returncode != 1 or "FAIL" not in result.stdout or expected not in result.stdout:
                raise ValueError(f"{name}: expected named refusal {expected!r}; exit={result.returncode}\n{result.stdout}{result.stderr}")
            print(f"OK {gate} rejects {name}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print(f"FAIL: {error}")
        sys.exit(1)
