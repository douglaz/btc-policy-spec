#!/usr/bin/env python3
"""Hold .github/workflows/gates.yml to its shard layout.

The gates job runs once per matrix shard, and a step runs only on the shard its
`if:` names. A step with no `if:` would run on every shard; one naming a shard
outside the matrix would run on none, and a control that never runs proves
nothing. So: the shard list is 0..N-1, the checkout and install-nix steps are
unconditional, the full gate runs on shard 0 with its replay, the other shards
build the formal layer instead, and every other step names exactly one shard.
"""

from pathlib import Path
import re
import sys

import yaml

ROOT = Path(__file__).resolve().parent.parent
ALL_GATES = "Run all gates"
ALL_GATES_BODY = "nix develop --command bash tools/check-all.sh"
FORMAL_SETUP = "Build the formal layer the controls copy"
UNCONDITIONAL = ("actions/checkout@", "cachix/install-nix-action@")


def main():
    job = yaml.safe_load((ROOT / ".github/workflows/gates.yml").read_text())["jobs"]["gates"]
    shards = job.get("strategy", {}).get("matrix", {}).get("shard")
    if not isinstance(shards, list) or not shards or shards != list(range(len(shards))):
        print(f"FAIL: the matrix shard list is {shards!r}, not [0, 1, ..., N-1]")
        return 1
    errors = []

    seen = set()
    for step in job["steps"]:
        name = step.get("name") or step.get("uses") or "(unnamed)"
        cond = step.get("if")
        seen.add(name)
        if step.get("uses", "").startswith(UNCONDITIONAL):
            if cond is not None:
                errors.append(f"step '{name}' has an if: and must run on every shard")
        elif name == ALL_GATES:
            if cond != "matrix.shard == 0":
                errors.append(f"step '{name}' has if: {cond!r}, not 'matrix.shard == 0'")
            if step.get("run", "").strip() != ALL_GATES_BODY:
                errors.append(f"step '{name}' does not run exactly '{ALL_GATES_BODY}'")
        elif name == FORMAL_SETUP:
            if cond != "matrix.shard != 0":
                errors.append(f"step '{name}' has if: {cond!r}, not 'matrix.shard != 0'")
        else:
            m = re.fullmatch(r"matrix\.shard == (\d+)", cond) if isinstance(cond, str) else None
            if m is None or int(m.group(1)) not in shards:
                errors.append(f"step '{name}' has if: {cond!r}, not 'matrix.shard == N' with N in the shard list")
    for prefix in UNCONDITIONAL:
        if not any(n.startswith(prefix) for n in seen):
            errors.append(f"step '{prefix}...' is missing")
    for name in (ALL_GATES, FORMAL_SETUP):
        if name not in seen:
            errors.append(f"step '{name}' is missing")

    if "--no-replay" in (ROOT / "tools/check-all.sh").read_text():
        errors.append("tools/check-all.sh contains --no-replay: the full gate always replays")

    for e in errors:
        print(f"FAIL: {e}")
    if errors:
        return 1
    print(f"shards: every step of gates.yml runs on exactly the shards it should, over {len(shards)} shards")
    return 0


if __name__ == "__main__":
    sys.exit(main())
