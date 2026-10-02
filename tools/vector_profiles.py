"""Executable checks for the published key and descriptor/manifest fixtures.

This is not a general descriptor implementation. The normalization probe accepts
only the wpkh public-key expressions used by the published MAN-39 fixtures.
Cryptographic operations use the independent libraries flake.nix pins (argon2-cffi, cryptography).
"""

import hashlib
from pathlib import Path
import re
import struct

from argon2.low_level import Type, hash_secret_raw
from argon2.exceptions import HashingError
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat

ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
INPUT_CHARSET = "0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ "
CHECKSUM_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"


def tagged_hash(tag, message):
    tag_hash = hashlib.sha256(tag.encode("ascii")).digest()
    return hashlib.sha256(tag_hash + tag_hash + message).digest()


def public_key(secret):
    scalar = int.from_bytes(secret, "big")
    if not 1 <= scalar < ORDER:
        raise ValueError("invalid secp256k1 scalar")
    return ec.derive_private_key(scalar, ec.SECP256K1()).public_key().public_bytes(
        Encoding.X962, PublicFormat.CompressedPoint
    ).hex()


def node_key_profile():
    """Read only MAN-17's concrete invocation, refusing unrecognized wording.

    The known-answer result stays in the independent JSON fixture: changing the
    owning parameters cannot change both the invocation and its expected answer.
    """
    document = (Path(__file__).resolve().parent.parent / "09-manifest-config-ceremony.md").read_text()
    match = re.search(r"^\*\*MAN-17\*\*(.*?)(?=^\*\*MAN-\d+\*\*|\Z)", document, re.M | re.S)
    if not match:
        raise ValueError("MAN-17: missing node-key derivation owner")
    text = " ".join(match.group(1).split())
    pattern = (r"Argon2id version `0x([0-9a-f]+)` \(decimal (\d+)\), using "
               r"the decoded (\d+)-byte preimage as password, the decoded (\d+)-byte configured salt, "
               r"`t = node_key_ops` passes, `m = node_key_mem_kib` KiB, parallelism `p = (\d+)`, "
               r"and output length (\d+) bytes\.")
    values = re.search(pattern, text)
    if not values:
        raise ValueError("MAN-17: cannot parse node-key invocation")
    version = int(values[1], 16)
    if version != int(values[2]):
        raise ValueError("MAN-17: hexadecimal and decimal versions disagree")
    for phrase in (
        "The optional secret and associated-data inputs are empty.",
        "no PHC encoding, hex text, terminating NUL, extra hash or domain prefix enters this invocation.",
        "as an unsigned big-endian scalar",
        "it MUST NOT be reduced modulo `q`, clamped, hashed again or silently retried.",
    ):
        if phrase not in text:
            raise ValueError("MAN-17: unsupported node-key input or scalar semantics")
    order = re.search(r"`q = 0x([0-9a-f]+)`", text)
    if not order or int(order[1], 16) != ORDER:
        raise ValueError("MAN-17: secp256k1 group order differs")
    return version, *(int(values[i]) for i in (3, 4, 5, 6))


def check_node_key(vector):
    version, password_bytes, salt_bytes, parallelism, output_bytes = node_key_profile()
    preimage = bytes.fromhex(vector["preimage"])
    salt = bytes.fromhex(vector["salt"])
    if len(preimage) != password_bytes or not 2**62 <= int.from_bytes(preimage, "big") < 2**63:
        raise ValueError("node preimage is not the MAN-16 width")
    if len(salt) != salt_bytes:
        raise ValueError("node salt width differs from MAN-17")
    try:
        secret = hash_secret_raw(preimage, salt, vector["ops"], vector["mem_kib"],
                                 parallelism=parallelism, hash_len=output_bytes, type=Type.ID, version=version)
    except HashingError as error:
        raise ValueError(f"MAN-17: invalid node-key invocation: {error}") from error
    channel = tagged_hash("btc-policy/channel-key/v0", secret)
    for counter in range(256):
        if 1 <= int.from_bytes(channel, "big") < ORDER:
            break
        channel = tagged_hash("btc-policy/channel-key/v0", secret + bytes([counter]))
    expected = {
        "signing_secret": secret.hex(), "signing_pubkey": public_key(secret),
        "channel_secret": channel.hex(), "channel_pubkey": public_key(channel),
    }
    for field, actual in expected.items():
        if vector[field] != actual:
            raise ValueError(f"node-key {field}: computed {actual}, published {vector[field]}")


def checksum(body):
    """BIP380 checksum over the descriptor body (not a script hash)."""
    symbols, groups = [], []
    for char in body:
        index = INPUT_CHARSET.index(char)
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


def fixture_descriptor(text):
    body, marker, supplied = text.partition("#")
    if marker and supplied != checksum(body):
        raise ValueError("invalid descriptor checksum")
    match = re.fullmatch(r"wpkh\((\[[^\]]+\])?([A-Za-z0-9]+)((?:/[^()]*)?)\)", body)
    if not match:
        raise ValueError("descriptor fixture outside the verifier's wpkh subset")
    origin, key, path = match.groups()

    def step(value):
        if value.startswith("<") and value.endswith(">"):
            return "<" + ";".join(step(v) for v in value[1:-1].split(";")) + ">"
        if value in ("*", "*h", "*'"):
            return "*" if value == "*" else "*h"
        parsed = re.fullmatch(r"([0-9]+)([h']?)", value)
        if not parsed or int(parsed[1]) >= 2**31:
            raise ValueError("invalid child index")
        return str(int(parsed[1])) + ("'" if parsed[2] else "")

    def path_text(value):
        return "".join("/" + step(v) for v in value.split("/")[1:])

    if origin:
        fingerprint, _, tail = origin[1:-1].partition("/")
        if not re.fullmatch(r"[0-9a-fA-F]{8}", fingerprint):
            raise ValueError("invalid fingerprint")
        origin = "[" + fingerprint.lower() + (path_text("/" + tail) if tail else "") + "]"
    if re.fullmatch(r"[0-9a-fA-F]{66}", key):
        ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256K1(), bytes.fromhex(key))
        key = key.lower()
    normalized = "wpkh(" + (origin or "") + key + path_text(path) + ")"
    return normalized + "#" + checksum(normalized)


def var(value):
    if isinstance(value, str):
        value = value.encode("utf-8")
    return struct.pack("<I", len(value)) + value


def strings(values):
    return struct.pack("<I", len(values)) + b"".join(var(v) for v in values)


def manifest_preimage(fields, hot, escape):
    raw = bytes.fromhex(fields["wallet_id"]) + struct.pack("<I", fields["protocol_version"])
    raw += bytes.fromhex(fields["coordinator_auth_pubkey"])
    for field in ("max_msg_bytes", "hot_max_per_tx", "hot_max_per_window", "hot_window_secs"):
        raw += struct.pack("<Q", fields[field])
    raw += strings(sorted(set(hot) - {escape})) + var(escape)
    raw += struct.pack("<IQBBB", fields["max_derivation_index"], fields["escape_feerate_floor"],
                       fields["escape_coverage_pct"], fields["escape_bump_max_fee_pct"], fields["network"])
    raw += struct.pack("<I", fields["policy_version"])
    raw += struct.pack("<QQ", fields["refresh_min_interval_secs"], fields["refresh_max_feerate"])
    raw += struct.pack("<I", len(fields["nodes"]))
    for node in sorted(fields["nodes"], key=lambda n: n["node_id"]):
        raw += struct.pack("<H", node["node_id"])
        raw += bytes.fromhex(node["signing_pubkey"]) + bytes.fromhex(node["channel_pubkey"])
        raw += strings(node["endpoints"])
    return raw


def check_descriptor_manifest(vector):
    vault = vector["manifest"]["vault_descriptor"]
    body, marker, supplied = vault.partition("#")
    if not marker or supplied != checksum(body):
        raise ValueError("vault descriptor checksum does not reproduce")
    if hashlib.sha256(vault.encode("ascii")).hexdigest() != vector["manifest"]["wallet_id"]:
        raise ValueError("vault descriptor does not reproduce wallet_id")
    hot = []
    for group in vector["descriptors"]:
        for spelling in group["inputs"]:
            got = fixture_descriptor(spelling)
            if got != group["canonical"]:
                raise ValueError(f"canonical descriptor: computed {got}, published {group['canonical']}")
        hot.append(group["canonical"])
    escape = hot.pop()
    for allowlist in (hot + [escape] + hot, list(reversed(hot)) + [escape]):
        preimage = manifest_preimage(vector["manifest"], allowlist, escape)
        if preimage.hex() != vector["preimage"]:
            raise ValueError("normalized manifest preimage differs from published bytes")
        if tagged_hash("btc-policy/manifest/v0", preimage).hex() != vector["manifest_hash"]:
            raise ValueError("normalized manifest hash differs from published digest")


class Reader:
    def __init__(self, data):
        self.data, self.offset = data, 0

    def take(self, size):
        end = self.offset + size
        if end > len(self.data):
            raise ValueError("length prefix or fixed field exceeds preimage")
        value, self.offset = self.data[self.offset:end], end
        return value

    def number(self, size=4):
        return int.from_bytes(self.take(size), "little")

    def variable(self):
        return self.take(self.number())

    def strings(self):
        for _ in range(self.number()):
            self.variable()

    def finish(self):
        if self.offset != len(self.data):
            raise ValueError("unconsumed preimage bytes")


def validate_preimage(tag, data):
    """Check each published tag's positional field framing, independently of its hash."""
    reader = Reader(data)
    if tag == "btc-policy/channel-key/v0":
        reader.take(32)
    elif tag == "btc-policy/coord-request/v0":
        reader.take(32)
        kind = reader.number(1)
        reader.variable()
        if kind == 1:
            reader.variable()
            reader.strings()
            reader.variable()
        elif kind not in (2, 3):
            raise ValueError("invalid coordinator request tag")
        reader.variable()
        reader.take(8 + 4)
    elif tag == "btc-policy/manifest/v0":
        reader.take(32 + 4 + 33 + 8 * 4)
        reader.strings()
        reader.variable()
        reader.take(4 + 8 + 1 + 1 + 1 + 4 + 8 + 8)
        for _ in range(reader.number()):
            reader.take(2 + 33 + 33)
            reader.strings()
    elif tag == "btc-policy/channel-endorsement/v0":
        reader.take(32 + 32 + 2 + 33 + 4)
        reader.strings()
    elif tag == "btc-policy/channel-envelope/v0":
        reader.variable()
        reader.take(4 + 32 + 32 + 2 + 2)
        reader.variable()
        if len(reader.variable()) != 16:
            raise ValueError("envelope nonce must decode to 16 bytes")
        reader.take(8)
    elif tag == "btc-policy/user-sig-hash/v0":
        while reader.offset < len(data):
            reader.variable()
            reader.take(1)
    else:
        raise ValueError(f"no framing schema for vector tag {tag!r}")
    reader.finish()


def witness_weight_profile():
    """Read CHN-34's own numbers, refusing wording the builder below does not implement."""
    document = (Path(__file__).resolve().parent.parent / "02-onchain-contract.md").read_text()
    match = re.search(r"^\*\*CHN-34\*\*(.*?)(?=^\*\*CHN-\d+\*\*|\Z)", document, re.M | re.S)
    if not match:
        raise ValueError("CHN-34: missing maximum-finalized-vsize owner")
    text = " ".join(match.group(1).split())
    formula = re.search(r"W_N = (\d+) × t \+ (\d+) × n \+ (\d+)", text)
    script = re.search(r"witness script is `(\d+) × n \+ (\d+)` bytes", text)
    item = re.search(r"each signature stack item costs (\d+) bytes, being a one-byte push prefix "
                     r"over a \*\*(\d+)\*\*-byte item that is at most (\d+) bytes of strict-DER", text)
    # The OUTER framing terms are read from the published expression too. Hardcoding them let a
    # mutation of CHN-34's own `+ 2` (marker/flag) pass the gate unnoticed (F51).
    outer = re.search(r"maximum_finalized_vsize = ⌊\(4 × B \+ (\d+) \+ input_count × W_N \+ (\d+)\) / 4⌋",
                      text)
    if not (formula and script and item and outer):
        raise ValueError("CHN-34: cannot parse the published witness-size terms")
    for phrase in ("`weight = 4 × B`", "the `t + 4` elements of `CHN-9`",
                   "MUST NOT be substituted by name"):
        if phrase not in text:
            raise ValueError("CHN-34: unsupported framing or accessor semantics")
    return (tuple(int(g) for g in formula.groups()), tuple(int(g) for g in script.groups()),
            tuple(int(g) for g in item.groups()), tuple(int(g) for g in outer.groups()))


def _synthetic_key(index):
    return ec.derive_private_key(index, ec.SECP256K1()).public_key().public_bytes(
        Encoding.X962, PublicFormat.CompressedPoint).hex()


def admitted_shapes():
    """CHN-2's admitted thresholds, read from its own 'up to t-of-n' sentence."""
    document = (Path(__file__).resolve().parent.parent / "02-onchain-contract.md").read_text()
    match = re.search(r"up to (\d+)-of-(\d+)", document)
    if not match or int(match.group(2)) != 2 * int(match.group(1)) - 1:
        raise ValueError("CHN-2: cannot read the maximum n = 2t - 1 shape")
    return set(range(2, int(match.group(1)) + 1))


def measure_shape(threshold, nodes, timelock=4224679):
    """Serialize a shape's script and maximum witness and return their measured lengths."""
    keys = [_synthetic_key(i) for i in range(2, 2 + nodes + 4)]
    descriptor = (f"wsh(or_i(and_v(v:pk({keys[0]}),multi({threshold},{','.join(keys[1:1 + nodes])}))"
                  f",and_v(v:older({timelock}),multi(2,{','.join(keys[1 + nodes:])}))))")
    script, parsed_t, parsed_n = vault_witness_script(descriptor)
    if (parsed_t, parsed_n) != (threshold, nodes):
        raise ValueError("synthetic shape did not round-trip through the template parser")
    signature = max_der_signature() + b"\x01"
    stack = [b""] + [signature] * threshold + [signature, b"\x01", script]
    witness = compact_size(len(stack)) + b"".join(compact_size(len(e)) + e for e in stack)
    return len(script), len(witness)


def max_der_signature():
    """A maximum-length low-S strict-DER signature: r may need a leading zero, s never does."""
    return (b"\x30" + bytes([4 + 33 + 32]) + b"\x02\x21" + b"\x00" + (ORDER - 1).to_bytes(32, "big")
            + b"\x02\x20" + (ORDER // 2).to_bytes(32, "big"))


def compact_size(value):
    if value < 253:
        return bytes([value])
    if value <= 0xFFFF:
        return b"\xfd" + struct.pack("<H", value)
    raise ValueError("fixture CompactSize beyond the published range")


def _push(payload):
    if len(payload) >= 76:
        raise ValueError("fixture push beyond a single-byte opcode")
    return bytes([len(payload)]) + payload


def vault_witness_script(descriptor):
    """Serialize CHN-1's template from its own keys; never a length formula."""
    body = descriptor.split("#")[0]
    shape = re.fullmatch(
        r"wsh\(or_i\(and_v\(v:pk\((0[23][0-9a-f]{64})\),multi\((\d+),((?:0[23][0-9a-f]{64},?)+)\)\),"
        r"and_v\(v:older\((\d+)\),multi\(2,((?:0[23][0-9a-f]{64},?){3})\)\)\)\)", body)
    if not shape:
        raise ValueError("witness-weight descriptor is not the CHN-1 template")
    user, threshold, nodes, timelock, recovery = shape.groups()
    nodes, recovery = nodes.split(","), recovery.split(",")
    threshold = int(threshold)
    if not (1 << 22) <= int(timelock) <= 0x40FFFF:
        raise ValueError("CHN-4 timelock is not a time-based BIP68 lock within the 65535-unit field")
    if len(set([user] + nodes + recovery)) != 1 + len(nodes) + 3:
        raise ValueError("CHN-5 requires globally distinct keys")
    raw = b"\x63" + _push(bytes.fromhex(user)) + b"\xad"
    raw += bytes([0x50 + threshold]) + b"".join(_push(bytes.fromhex(k)) for k in nodes)
    raw += bytes([0x50 + len(nodes)]) + b"\xae"
    raw += b"\x67" + _push(int(timelock).to_bytes(3, "little")) + b"\xb2\x69"
    raw += b"\x52" + b"".join(_push(bytes.fromhex(k)) for k in recovery) + b"\x53\xae"
    return raw + b"\x68", threshold, len(nodes)


def check_witness_weight(vector):
    ((w_t, w_n, w_c), (s_n, s_c), (item_bytes, sig_bytes, der_bytes),
     (outer_framing, outer_round)) = witness_weight_profile()
    script, threshold, nodes = vault_witness_script(vector["vault_descriptor"])
    if (threshold, nodes) != (vector["t"], vector["n"]):
        raise ValueError("witness-weight shape differs from the descriptor's")
    if script.hex() != vector["witness_script"] or len(script) != vector["witness_script_bytes"]:
        raise ValueError("serialized witness script differs from the published bytes")
    if len(script) != s_n * nodes + s_c:
        raise ValueError(f"witness script measures {len(script)}, CHN-34 says {s_n * nodes + s_c}")

    der = max_der_signature()
    if len(der) != der_bytes or len(der) + 1 != sig_bytes:
        raise ValueError(f"maximum DER measures {len(der)}, CHN-34 says {der_bytes}")
    signature = der + b"\x01"
    stack = [b""] + [signature] * threshold + [signature, b"\x01", script]
    if len(stack) != vector["witness_items"] or len(stack) != threshold + 4:
        raise ValueError("witness stack is not CHN-9's t + 4 elements")
    witness = compact_size(len(stack)) + b"".join(compact_size(len(e)) + e for e in stack)
    if len(compact_size(len(signature)) + signature) != item_bytes:
        raise ValueError("signature stack item differs from CHN-34's per-item cost")
    published = vector["max_witness_weight_per_input"]
    if len(witness) != published:
        raise ValueError(f"serialized witness measures {len(witness)} WU, published {published}")
    if len(witness) != w_t * threshold + w_n * nodes + w_c:
        raise ValueError("measured witness disagrees with CHN-34's W_N")

    worked = vector["worked_transaction"]
    raw = bytes.fromhex(worked["unsigned_serialization"])
    if len(raw) != worked["base_bytes"]:
        raise ValueError("worked transaction length differs from its published legacy size")
    if raw[4] != worked["input_count"]:
        raise ValueError("worked transaction input count differs")
    weight = 4 * len(raw) + outer_framing + worked["input_count"] * len(witness)
    if weight != worked["maximum_weight"]:
        raise ValueError(f"worked transaction weight measures {weight}, published "
                         f"{worked['maximum_weight']}")
    if (weight + outer_round) // 4 != worked["maximum_finalized_vsize"]:
        raise ValueError("worked transaction vsize differs from CHN-34")

    # Every shape is MEASURED by serializing a synthetic vault of that shape. Checking the rows
    # against the formula instead would agree with a framing error rather than catch it (F51).
    # The table must cover exactly CHN-2's shapes: a dropped row passed unnoticed (F56).
    thresholds = [row["t"] for row in vector["shape_table"]]
    if sorted(thresholds) != sorted(admitted_shapes()) or len(set(thresholds)) != len(thresholds):
        raise ValueError(f"shape table covers t={sorted(thresholds)}, CHN-2 admits "
                         f"t={sorted(admitted_shapes())}")
    for row in vector["shape_table"]:
        if row["n"] != 2 * row["t"] - 1:
            raise ValueError("shape table row is not CHN-2's n = 2t - 1")
        measured_script, measured_witness = measure_shape(row["t"], row["n"])
        # CHN-34 claims the script length is invariant across every sealed CHN-4 lock; measure
        # both ends of the field rather than trust the claim (F56).
        for timelock in ((1 << 22) | 1, 0x40FFFF):
            other_script, other_witness = measure_shape(row["t"], row["n"], timelock)
            if (other_script, other_witness) != (measured_script, measured_witness):
                raise ValueError(f"shape t={row['t']}: lock {timelock:#x} measures "
                                 f"{other_script}/{other_witness}, default {measured_script}/"
                                 f"{measured_witness}; CHN-34's invariance claim fails")
        if measured_script != row["witness_script_bytes"]:
            raise ValueError(f"shape t={row['t']}: script measures {measured_script}, published "
                             f"{row['witness_script_bytes']}")
        if measured_witness != row["max_witness_weight_per_input"]:
            raise ValueError(f"shape t={row['t']}: witness measures {measured_witness}, published "
                             f"{row['max_witness_weight_per_input']}")
        if (measured_script != s_n * row["n"] + s_c
                or measured_witness != w_t * row["t"] + w_n * row["n"] + w_c):
            raise ValueError(f"shape table row t={row['t']} differs from CHN-34's formula")


def check_commitment(vector):
    f = vector["fields"]
    raw = bytes.fromhex(f["wallet_id"]) + struct.pack(">iII", f["version"], f["lock_time"], len(f["inputs"]))
    for entry in f["inputs"]:
        raw += bytes.fromhex(entry["txid"])[::-1] + struct.pack(">II", entry["vout"], entry["sequence"])
    raw += struct.pack(">I", len(f["outputs"]))
    for output in f["outputs"]:
        script = bytes.fromhex(output["script"])
        raw += struct.pack(">I", len(script)) + script + struct.pack(">Q", output["amount"])
    raw += struct.pack(">QQI", f["fee"], f["expiry"], f["policy_version"])
    if raw.hex() != vector["preimage"]:
        raise ValueError("commitment fields do not reproduce the published preimage")
    if hashlib.sha256(raw).hexdigest() != vector["commitment_id"]:
        raise ValueError("single-SHA256 commitment id differs from the published digest")
