#!/usr/bin/env python3
"""Vector gate -- every published digest is recomputed from its published preimage.

`08-wire-contract.md` publishes the byte vectors an independent implementation
reproduces (WIR-25 onward). The reference implementation pins them in its own
tests, but a specification that merely SAYS "this preimage hashes to that digest"
can drift in either half without anything noticing: the reference tests compare
against the constants in the reference tree, not against this document.

So this gate executes the specification. For every fenced ```vector block:

    tag = "btc-policy/manifest/v0"
    preimage =
    2222...   (hex, whitespace and comments after `#` ignored, across lines)
    digest = 4a3b...

it computes SHA256(SHA256(tag) || SHA256(tag) || preimage) -- the BIP340-style
tagged hash WIR-19 fixes -- and requires it to equal `digest`. A block may also
carry `sha256 = <hex>` (plain single-SHA256 of the preimage, no tag) for the
one encoding that is not a tagged hash, the commitment id (CHN-26).

Framing is checked separately from hashing. tools/protocol-vectors.json adds
field-to-preimage, descriptor-normalization and independently derived key vectors.
Run under `nix develop` (flake.nix provides argon2-cffi and cryptography) before running this gate.

Exit 0 = every vector reproduces, 1 = a mismatch or a malformed block.
"""

import glob
import hashlib
import json
import os
import re
import sys

try:
    from vector_profiles import (check_commitment, check_descriptor_manifest, check_node_key,
                                 check_witness_weight, validate_preimage)
except ImportError as error:
    sys.exit(f"FAIL: vector dependencies unavailable ({error}); run under nix develop (flake.nix)")

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FENCE_RE = re.compile(r"^```vector\s*\n(.*?)^```", re.M | re.S)


def tagged_hash(tag: bytes, msg: bytes) -> bytes:
    th = hashlib.sha256(tag).digest()
    return hashlib.sha256(th + th + msg).digest()


def parse(block):
    tag, digest, sha, pre = None, None, None, []
    mode = None
    for raw in block.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        m = re.match(r'^tag\s*=\s*"([^"]*)"$', line)
        if m:
            tag = m.group(1)
            mode = None
            continue
        m = re.match(r"^digest\s*=\s*([0-9a-fA-F]{64})$", line)
        if m:
            digest = m.group(1).lower()
            mode = None
            continue
        m = re.match(r"^sha256\s*=\s*([0-9a-fA-F]{64})$", line)
        if m:
            sha = m.group(1).lower()
            mode = None
            continue
        if re.match(r"^preimage\s*=\s*$", line):
            mode = "pre"
            continue
        if mode == "pre":
            hexpart = re.sub(r"\s+", "", line)
            if not re.fullmatch(r"[0-9a-fA-F]*", hexpart):
                raise ValueError(f"non-hex preimage line: {raw.strip()!r}")
            pre.append(hexpart.lower())
            continue
        raise ValueError(f"unrecognised line: {raw.strip()!r}")
    preimage = "".join(pre)
    if len(preimage) % 2:
        raise ValueError("preimage has an odd number of hex digits")
    return tag, bytes.fromhex(preimage), digest, sha


def main():
    os.chdir(ROOT)
    checked, fenced, failures = 0, 0, 0
    for f in sorted(glob.glob("*.md")) + sorted(glob.glob("docs/adr/*.md")):
        text = open(f).read()
        for m in FENCE_RE.finditer(text):
            fenced += 1
            line = text[: m.start()].count("\n") + 1
            where = f"{f}:{line}"
            try:
                tag, pre, digest, sha = parse(m.group(1))
                if tag is not None:
                    validate_preimage(tag, pre)
            except ValueError as e:
                print(f"FAIL {where}: {e}")
                failures += 1
                continue
            if digest is None and sha is None:
                print(f"FAIL {where}: block declares no digest")
                failures += 1
                continue
            checked += 1
            if digest is not None:
                if tag is None:
                    print(f"FAIL {where}: digest without a tag")
                    failures += 1
                    continue
                got = tagged_hash(tag.encode(), pre).hex()
                if got != digest:
                    print(f"FAIL {where}: tagged_hash({tag!r}) = {got}, document says {digest}")
                    failures += 1
            if sha is not None:
                got = hashlib.sha256(pre).hexdigest()
                if got != sha:
                    print(f"FAIL {where}: sha256 = {got}, document says {sha}")
                    failures += 1
    try:
        with open("tools/protocol-vectors.json") as source:
            profiles = json.load(source)
        for name, validator in (("node_key", check_node_key),
                                ("descriptor_manifest", check_descriptor_manifest),
                                ("commitment", check_commitment),
                                ("witness_weight", check_witness_weight)):
            validator(profiles[name])
            checked += 1
    except (ValueError, KeyError, TypeError, OSError) as error:
        print(f"FAIL tools/protocol-vectors.json: {error}")
        failures += 1
    print(f"vectors checked: {checked} | failures: {failures}")
    if fenced == 0:
        print("FAIL: no ```vector blocks found -- the gate would pass vacuously")
        return 1
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
