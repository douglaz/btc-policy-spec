#!/usr/bin/env python3
"""Fixture gate -- enforces WIR-1 (the JSON profile) and WIR-3 (fixtures are test
inputs, not illustrations) on every JSON example in the set.

WIR-1 fixes the JSON profile as I-JSON with bounded numbers: a body MUST reject a
duplicate object member at any depth, MUST be valid UTF-8, and every JSON number
MUST be an integer within +/-(2^53-1) with no exponent or fraction -- satoshi
amounts, unix timestamps, counts and versions are all integers.

WIR-3 says every JSON example parses with real-shaped values (64-hex ids, 66-hex
compressed pubkeys, base64 PSBTs) and that a `...` placeholder inside an object
is prohibited.

It also structurally checks every ```mermaid block: a declared diagram type,
balanced brackets, balanced quotes. Mermaid renders on GitHub but there is no
offline parser here, so a broken diagram would look fine in source and fail in
the browser.

So this gate checks, for every fenced ```json block in the set:

  * it parses
  * it contains no duplicate object member at any depth
  * every number is an integer within +/-(2^53-1)
  * it contains no `...` placeholder
  * 32-byte identifier fields are exactly 64 lowercase hex characters (WIR-2)
  * compressed-pubkey fields are 66 lowercase hex characters starting 02/03 (WIR-2)
  * PSBT fields decode as BIP174 v0: a complete unsigned transaction, unique map
    keys, exactly one map per input/output, and no trailing bytes (WIR-5)

A fixture that fails here is a fixture an implementation cannot use. Structural
PSBT checks do not assert signatures, prevout provenance or policy acceptance.

Exit status 0 = clean, 1 = failures.
"""

import base64
import binascii
import glob
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAX_INT = 2 ** 53 - 1
# 32-byte identifiers and hashes travel as 64 lowercase hex characters; compressed
# secp256k1 public keys as 66 (WIR-2).
HEX32_FIELDS = {"wallet_id", "manifest_hash", "commitment_id", "txid", "manifest_hash_hex"}
HEX33_FIELDS = {"coordinator_auth_pubkey", "signing_pubkey", "channel_pubkey"}

FENCE_RE = re.compile(r"^```json\s*\n(.*?)^```", re.M | re.S)
TS_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(Z|[+-]\d{2}:\d{2})$")


class ByteReader:
    """Bounded binary reader; lengths never allocate or loop past the input."""

    def __init__(self, data):
        self.data = data
        self.pos = 0

    def take(self, size):
        if size > len(self.data) - self.pos:
            raise ValueError("truncated PSBT field or unsigned transaction")
        value = self.data[self.pos:self.pos + size]
        self.pos += size
        return value

    def compact(self):
        prefix = self.take(1)[0]
        if prefix < 253:
            return prefix
        size, minimum = {253: (2, 253), 254: (4, 65536), 255: (8, 4294967296)}[prefix]
        value = int.from_bytes(self.take(size), "little")
        if value < minimum:
            raise ValueError("noncanonical CompactSize in PSBT")
        return value

    def var(self):
        return self.take(self.compact())

    def finish(self):
        if self.pos != len(self.data):
            raise ValueError("trailing bytes in PSBT or unsigned transaction")


def psbt_map(reader):
    entries = {}
    while True:
        key = reader.var()
        if not key:
            return entries
        if key in entries:
            raise ValueError("duplicate PSBT map key")
        entries[key] = reader.var()


def unsigned_counts(data):
    tx = ByteReader(data)
    tx.take(4)  # nVersion
    inputs = tx.compact()
    if not inputs:
        raise ValueError("PSBT unsigned transaction has no inputs or uses witness encoding")
    for _ in range(inputs):
        tx.take(36)  # txid, vout
        if tx.var():
            raise ValueError("PSBT unsigned transaction scriptSig must be empty")
        tx.take(4)  # nSequence
    outputs = tx.compact()
    if not outputs:
        raise ValueError("PSBT unsigned transaction has no outputs")
    for _ in range(outputs):
        tx.take(8)  # amount
        tx.var()  # scriptPubKey
    tx.take(4)  # nLockTime
    tx.finish()
    return inputs, outputs


def check_psbt(text):
    """Validate fixture framing, not the specified vault's policy or cryptography."""
    try:
        binary = base64.b64decode(text.strip(), validate=True)
    except (ValueError, binascii.Error) as error:
        raise ValueError(f"invalid PSBT base64: {error}") from error
    if base64.b64encode(binary).decode() != text.strip():
        raise ValueError("PSBT must use canonical padded base64")
    psbt = ByteReader(binary)
    if psbt.take(5) != b"psbt\xff":
        raise ValueError("invalid PSBT magic")
    globals_ = psbt_map(psbt)
    if b"\x00" not in globals_:
        raise ValueError("BIP174 PSBT needs a global unsigned transaction")
    for key in globals_:
        if key[0] == 0 and key != b"\x00":
            raise ValueError("unsigned-transaction key must have no key data")
    if b"\xfb" in globals_ and globals_[b"\xfb"] != b"\x00" * 4:
        raise ValueError("fixture is not a BIP174 v0 PSBT")
    inputs, outputs = unsigned_counts(globals_[b"\x00"])
    for _ in range(inputs + outputs):
        psbt_map(psbt)
    psbt.finish()


def no_duplicate_keys(pairs):
    seen = {}
    for k, v in pairs:
        if k in seen:
            raise ValueError(f"duplicate object member {k!r}")
        seen[k] = v
    return seen


def walk(node, path, problems):
    if isinstance(node, dict):
        for k, v in node.items():
            walk(v, f"{path}.{k}", problems)
    elif isinstance(node, list):
        for i, v in enumerate(node):
            walk(v, f"{path}[{i}]", problems)
    elif isinstance(node, bool):
        pass
    elif isinstance(node, int):
        if abs(node) > MAX_INT:
            problems.append(f"{path}: integer {node} exceeds 2^53-1 (WIR-1)")
    elif isinstance(node, float):
        problems.append(f"{path}: non-integer number {node} (WIR-1)")
    elif isinstance(node, str):
        m = TS_RE.match(node)
        if m and m.group(1) != "Z":
            problems.append(f"{path}: timestamp {node!r} must end in Z (WIR-1)")
        leaf = path.rsplit(".", 1)[-1].split("[", 1)[0]
        if leaf in {"spend", "escape", "refresh", "clawback", "escape_bumps"}:
            try:
                check_psbt(node)
            except ValueError as error:
                problems.append(f"{path}: {error} (WIR-5)")
        if leaf in HEX32_FIELDS and not re.fullmatch(r"[0-9a-f]{64}", node):
            problems.append(f"{path}: {leaf} must be exactly 64 lowercase hex chars (WIR-2)")
        if leaf in HEX33_FIELDS:
            if not re.fullmatch(r"0[23][0-9a-f]{64}", node):
                problems.append(f"{path}: {leaf} must be a 33-byte compressed pubkey in lowercase hex (WIR-2)")
            elif not on_curve(node):
                problems.append(f"{path}: {leaf} is not a point on secp256k1 (CHN-3)")
        if leaf in DESCRIPTOR_FIELDS and "(" in node:
            for problem in check_descriptor(node):
                problems.append(f"{path}: {problem}")


# Descriptor-bearing fields. A descriptor string smuggles keys and a checksum past every
# field-name check above, which is how WIR-12 carried a wrong BIP380 checksum, two keys that
# were not even byte-aligned hex, and two that were not on the curve, through a green gate.
# Kept stdlib-only on purpose: this gate must still run when the vector gate's pinned
# cryptography dependencies are absent.
DESCRIPTOR_FIELDS = {"vault_descriptor", "escape_descriptor", "descriptor", "hot_descriptor"}
INPUT_CHARSET = "0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ "
CHECKSUM_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
SECP256K1_P = 2 ** 256 - 2 ** 32 - 977


def descriptor_checksum(body):
    """BIP380 checksum. Returns None if the body holds a character outside the charset."""
    symbols, groups = [], []
    for char in body:
        index = INPUT_CHARSET.find(char)
        if index < 0:
            return None
        symbols.append(index & 31)
        groups.append(index >> 5)
        if len(groups) == 3:
            symbols.append(groups[0] * 9 + groups[1] * 3 + groups[2])
            groups = []
    if groups:
        symbols.append(groups[0] if len(groups) == 1 else groups[0] * 3 + groups[1])
    state = 1
    generators = (0xF5DEE51989, 0xA9FDCA3312, 0x1BAB10E32D, 0x3706B1677A, 0x644D626FFD)
    for symbol in symbols + [0] * 8:
        top = state >> 35
        state = ((state & 0x7FFFFFFFF) << 5) ^ symbol
        for bit, generator in enumerate(generators):
            if (top >> bit) & 1:
                state ^= generator
    state ^= 1
    return "".join(CHECKSUM_CHARSET[(state >> (5 * (7 - i))) & 31] for i in range(8))


def on_curve(compressed):
    """secp256k1 membership from the x coordinate alone; p = 3 mod 4, so one exponentiation."""
    x = int(compressed[2:], 16)
    if not 0 < x < SECP256K1_P:
        return False
    y_squared = (pow(x, 3, SECP256K1_P) + 7) % SECP256K1_P
    return pow(y_squared, (SECP256K1_P + 1) // 4, SECP256K1_P) ** 2 % SECP256K1_P == y_squared


BASE58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
XKEY_VERSIONS = {"0488b21e": "xpub", "043587cf": "tpub"}


def extended_key_problem(text):
    """Base58Check an extended key. WIR-13/WIR-14 once carried one that decoded to 63 bytes."""
    number = 0
    for char in text:
        index = BASE58.find(char)
        if index < 0:
            return f"contains {char!r}, which is not a Base58 character"
        number = number * 58 + index
    raw = number.to_bytes((number.bit_length() + 7) // 8, "big")
    raw = b"\x00" * (len(text) - len(text.lstrip("1"))) + raw
    if len(raw) != 82:
        return f"decodes to {len(raw)} bytes, not the 78 + 4 of a Base58Check extended key"
    if hashlib.sha256(hashlib.sha256(raw[:-4]).digest()).digest()[:4] != raw[-4:]:
        return "fails its Base58Check checksum"
    if raw[:4].hex() not in XKEY_VERSIONS:
        return f"carries version bytes {raw[:4].hex()}, which is no known xpub/tpub prefix"
    return None


def check_descriptor(text):
    """WIR-3 says fixtures are test inputs; a descriptor a parser refuses is not one."""
    problems = []
    for token in re.findall(r"(?<![0-9A-Za-z])[xt]pub[1-9A-HJ-NP-Za-km-z]+", text):
        problem = extended_key_problem(token)
        if problem:
            problems.append(f"extended key {token[:12]}... {problem} (MAN-39)")
    body, marker, supplied = text.partition("#")
    expected = descriptor_checksum(body)
    if expected is None:
        return [f"descriptor holds a character outside the BIP380 input charset: {text[:48]!r}"]
    if marker and supplied != expected:
        problems.append(f"BIP380 checksum {supplied!r} does not verify; body checksums to "
                        f"{expected!r} (MAN-39)")
    for token in re.findall(r"(?<![0-9a-zA-Z])0[23][0-9a-zA-Z]*", body):
        if not re.fullmatch(r"0[23][0-9a-f]{64}", token):
            problems.append(f"key {token[:14]}... is {len(token)} chars, not 66 lowercase hex "
                            f"(CHN-3, WIR-2)")
        elif not on_curve(token):
            problems.append(f"key {token[:14]}... is not a point on secp256k1 (CHN-3)")
    branch = re.search(r"multi\(\d+,((?:0[23][0-9a-f]{64},?)+)\)\),and_v", body)
    if branch:
        keys = branch.group(1).split(",")
        if keys != sorted(keys):
            problems.append("Normal-branch multi keys are not in ascending order, so node_id "
                            "cannot be the position in canonical node order (CHN-7)")
    return problems


MERMAID_RE = re.compile(r"^```mermaid\s*\n(.*?)^```", re.M | re.S)
MERMAID_KINDS = (
    "flowchart", "graph", "sequenceDiagram", "stateDiagram-v2", "stateDiagram",
    "erDiagram", "classDiagram", "journey", "gantt", "pie", "mindmap", "timeline",
)


def check_mermaid():
    """A structural sanity check, not a parser.

    Mermaid renders on GitHub but there is no offline parser here, so a broken
    diagram would ship looking fine in source and fail in the browser. This
    catches the two errors that actually happen: a block that declares no
    diagram type, and unbalanced brackets or quotes in a label.
    """
    problems = 0
    count = 0
    for f in sorted(glob.glob("*.md")) + sorted(glob.glob("docs/adr/*.md")):
        text = open(f).read()
        for m in MERMAID_RE.finditer(text):
            count += 1
            line = text[: m.start()].count("\n") + 1
            body = m.group(1)
            first = next((l.strip() for l in body.splitlines() if l.strip()), "")
            if not first.startswith(MERMAID_KINDS):
                print(f"FAIL {f}:{line}: mermaid block declares no known diagram "
                      f"type (starts {first[:40]!r})")
                problems += 1
            # erDiagram's crow's-foot notation (||--o{, }o--o|) uses braces as
            # syntax rather than as pairs, so brace balance is meaningless there.
            pairs = [("[", "]"), ("(", ")")]
            if not first.startswith("erDiagram"):
                pairs.append(("{", "}"))
            for open_c, close_c in pairs:
                if body.count(open_c) != body.count(close_c):
                    print(f"FAIL {f}:{line}: unbalanced {open_c}{close_c} "
                          f"({body.count(open_c)} vs {body.count(close_c)})")
                    problems += 1
            if body.count('"') % 2:
                print(f"FAIL {f}:{line}: odd number of double quotes")
                problems += 1
    print(f"mermaid diagrams checked: {count} | failures: {problems}")
    return problems


def main():
    os.chdir(ROOT)
    mermaid_failures = check_mermaid()
    failures = 0
    blocks = 0

    for f in sorted(glob.glob("*.md")) + sorted(glob.glob("docs/adr/*.md")):
        text = open(f).read()
        for i, m in enumerate(FENCE_RE.finditer(text), 1):
            blocks += 1
            body = m.group(1)
            line = text[: m.start()].count("\n") + 1
            where = f"{f}:{line} (json block {i})"

            if "..." in body:
                print(f"FAIL {where}: contains a `...` placeholder (WIR-3)")
                failures += 1
                continue

            try:
                doc = json.loads(body, object_pairs_hook=no_duplicate_keys)
            except ValueError as e:
                print(f"FAIL {where}: {e}")
                failures += 1
                continue

            problems = []
            walk(doc, "$", problems)
            for p in problems:
                print(f"FAIL {where}: {p}")
            failures += len(problems)

    print(f"json fixtures checked: {blocks} | failures: {failures}")
    return 1 if (failures or mermaid_failures) else 0


if __name__ == "__main__":
    sys.exit(main())
