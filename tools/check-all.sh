#!/usr/bin/env bash
# Run every gate that guards this specification set.
#
# Ported from the provisiond specification set on 2026-09-09, where they were
# first written after living in a scratch directory that was cleaned by age.
# They are committed here so the checks guarding the specifications outlive
# the machine that ran them last.
#
# Each gate runs to completion and its exit status is captured directly -- never
# through a pipe, which would report the status of the last command in the
# pipeline rather than the gate's own.
#
# Exit status 0 = every gate passed.

set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

declare -a NAMES=()
declare -a CODES=()
overall=0

run() {
  local name="$1"; shift
  echo
  echo "=============================================================="
  echo "  $name"
  echo "=============================================================="
  "$@"
  local rc=$?
  NAMES+=("$name")
  CODES+=("$rc")
  [ "$rc" -ne 0 ] && overall=1
  return 0
}

# The formal gate runs first: the identifier, citation, copies and regions gates read
# the index, values and regions it writes, and a stale index is a gate reading last
# week's truth.
run "formal       (Lean build, axiom policy, kernel replay, @[req] index, regions, values)" bash tools/check_formal.sh
run "identifiers  (append-only, dangling, gaps, ADR refs, @[req] tags)" python3 tools/check_ids.py
run "fixtures     (WIR-1 JSON profile, hex ids, mermaid)"   python3 tools/check_fixtures.py
run "obligations  (a duty assigned to another requirement)" python3 tools/check_obligations.py
run "coverage     (requirements exercised by CNF items)"   python3 tools/check_coverage.py
run "citations    (a claim about what another requirement says; BtcPolicy.* names)" python3 tools/check_citations.py
run "vectors      (every published digest recomputed)"     python3 tools/check_vectors.py
run "copies       (every inline figure is what its declaration emits)" python3 tools/check_copies.py
run "regions      (a marked region is what its declaration emits)" python3 tools/check_regions.py

echo
echo "=============================================================="
echo "  SUMMARY"
echo "=============================================================="
for i in "${!NAMES[@]}"; do
  if [ "${CODES[$i]}" -eq 0 ]; then status="PASS"; else status="FAIL"; fi
  printf '  %-4s  %s\n' "$status" "${NAMES[$i]}"
done
echo

if [ "$overall" -eq 0 ]; then
  echo "All gates passed."
else
  echo "One or more gates FAILED."
fi
exit "$overall"
