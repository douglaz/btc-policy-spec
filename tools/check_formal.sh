#!/usr/bin/env bash
# The formal layer's gate (ADR-0023): build every Lean module, then run `lake exe gate`,
# which, over every constant of every project module, tagged or not, refuses a
# dependency on an axiom outside propext / Classical.choice / Quot.sound -- so
# `sorry` and `native_decide` are red anywhere, an untagged @[csimp] lemma included --
# an `axiom` written or minted, and an `implemented_by` or `extern`
# attribute; it also refuses a tagged declaration in Explore, a tag that is not an
# identifier or names a CNF item, and an empty index. Then replay every
# declaration through the kernel from a fresh environment (`leanchecker --fresh`),
# which checks the .olean files the build wrote rather than trusting them. Then
# `lake exe render` and `lake exe values` write the marked regions and the emitted
# values; the citations, copies and regions gates read what this script writes, so
# check-all.sh runs it first.
#
# Also refuses a module under BtcPolicy/ (recursively) that the build never
# imports: a proof file the build never reads is DEF-16's green check with a
# .lean suffix. A module is reached if BtcPolicy.lean imports it or another
# reached module does.
#
# `--no-replay` skips the kernel replay and nothing else, for a caller that needs
# only the files this script writes; check-all.sh never passes it.
#
# Needs `lake`, `lean` and `leanchecker` on PATH: run under `nix develop`
# (flake.nix). A missing tool is a failure, not a skip.
set -uo pipefail
replay=1
case "$#:${1-}" in
  0:) ;;
  1:--no-replay) replay=0 ;;
  *) echo "usage: check_formal.sh [--no-replay]" >&2; exit 2 ;;
esac
cd "$(dirname "$0")/formal" || exit 2

for tool in lake lean leanchecker; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "FAIL: $tool not on PATH -- run under 'nix develop' (see flake.nix)"
    exit 1
  fi
done

# The regions and values gates hold the Markdown to what the compiled emitters print. An
# `implemented_by` or `extern` attribute anywhere in the chain would let the compiled code differ
# from the term the kernel proved about; decision 3 refused native_decide for exactly that trust
# in compiled evaluation, so the attributes are refused here, and `csimp` with them: it too
# replaces what the compiler runs. `-z` reads each file as one
# record, so an attribute written over several lines is seen too. The load-bearing check is
# the gate's axiom walk over every constant, which no source form escapes.
if grep -rlzE '(@\[|attribute \[)[^]]*\b(implemented_by|extern|csimp)\b' --include='*.lean' --exclude-dir=.lake . ; then
  echo "FAIL: implemented_by / extern / csimp in tools/formal/ -- the emitters must print what the kernel proved about (ADR-0023 decision 3)"
  exit 1
fi

# One declaration, one identifier: a second `req` in the same bracket is accepted by Lean and the
# attribute keeps only the last, silently, and `attribute [req …] name` could retag a declaration
# after the fact. Neither is a form this set uses; both are refused at the source. Lean accepts
# either written over several lines, so both greps read each file as one record (`-z`, as the
# implemented_by check above does) and tolerate any whitespace between `req` and its string.
if grep -rlzE '@\[[^]]*\breq\s*"[^"]*"[^]]*\breq\s*"' --include='*.lean' --exclude-dir=.lake . ; then
  echo "FAIL: a declaration tagged @[req] twice -- one declaration, one identifier (ADR-0023 decision 1)"
  exit 1
fi
if grep -rlzE 'attribute \[[^]]*\breq\b' --include='*.lean' --exclude-dir=.lake . ; then
  echo "FAIL: attribute [req …] applied after the declaration -- a tag goes on the declaration it formalizes"
  exit 1
fi

# A theorem is never conformance (ADR-0023 decision 2): no CNF identifier anywhere in the
# formal tree, docstrings included.
if grep -rnE 'CNF-[0-9]+' --exclude-dir=.lake . ; then
  echo "FAIL: a CNF identifier in tools/formal/ -- a theorem is never conformance (ADR-0023 decision 2)"
  exit 1
fi

# "the project declares no `axiom`" (ADR-0023 decision 3) is enforced by `lake exe gate`, which
# walks every constant of the library — gate and emitters included, since they live in
# BtcPolicy.Exe. An executable root cannot be imported by the gate, so each of the three is held
# to exactly one import and one main; anything else there is content the walk cannot see.
# Every Lean source in the tree is either under BtcPolicy/ (reached from BtcPolicy.lean, checked
# below) or one of the four roots. A file anywhere else is never built, indexed or replayed.
while IFS= read -r f; do
  case "$f" in ./BtcPolicy/*|./Gate.lean|./Render.lean|./Values.lean|./BtcPolicy.lean) ;; *)
    echo "FAIL: $f is a Lean file outside BtcPolicy/ and the four roots -- the gate cannot walk it"
    exit 1;;
  esac
done < <(find . -name '*.lean' -not -path './.lake/*' | sort)

for exe in Gate Render Values; do
  case "$exe" in Gate) fn=gateMain; kw="unsafe def";; Render) fn=renderMain; kw=def;; Values) fn=valuesMain; kw=def;; esac
  if ! printf 'import BtcPolicy.Exe\n%s main : IO UInt32 := BtcPolicy.Exe.%s\n' "$kw" "$fn" | cmp -s - "$exe.lean"; then
    echo "FAIL: $exe.lean is not the one-line executable root -- content there escapes the gate's walk; put it in BtcPolicy/Exe.lean"
    exit 1
  fi
done

lake build || exit 1

# Every module under BtcPolicy/ must be reachable from BtcPolicy.lean through imports, read by
# Lean itself (`lean --deps`), not by a grep that a commented-out `import` line would fool. After
# the build, because `lean --deps` resolves imports through the built .olean files and reports
# nothing on a fresh checkout; a resolver failure is a red gate, never an empty import list.
reached="BtcPolicy"
queue="BtcPolicy.lean"
while [ -n "$queue" ]; do
  next=""
  for f in $queue; do
    deps="$(lake env lean --deps "$f")" || { echo "FAIL: lean --deps $f failed: $deps"; exit 1; }
    for olean in $(echo "$deps" | grep -oE 'BtcPolicy(/[A-Za-z0-9_]+)*\.olean$'); do
      m="$(echo "${olean%.olean}" | tr / .)"
      case " $reached " in *" $m "*) ;; *) reached="$reached $m"; next="$next $(echo "$m" | tr . /).lean";; esac
    done
  done
  queue="$next"
done
while IFS= read -r f; do
  m="$(echo "${f%.lean}" | tr / .)"
  case " $reached " in *" $m "*) ;; *)
    echo "FAIL: $f exists but nothing imports $m from BtcPolicy.lean -- the build never reads it"
    exit 1;;
  esac
done < <(find BtcPolicy -name '*.lean' | sort)

lake exe gate > .lake/index.jsonl
rc=$?
echo "index: $(wc -l < .lake/index.jsonl) tagged declarations -> tools/formal/.lake/index.jsonl"
[ "$rc" -eq 0 ] || exit "$rc"
# Kernel replay of every declaration from a fresh environment (ADR-0023 decision 3).
if [ "$replay" -eq 1 ]; then
  lake env leanchecker --fresh BtcPolicy
  rc=$?
  [ "$rc" -eq 0 ] || { echo "FAIL: leanchecker --fresh BtcPolicy exited $rc"; exit "$rc"; }
  echo "replay: leanchecker --fresh BtcPolicy accepted every declaration"
else
  echo "replay: skipped (--no-replay)"
fi
# The marked regions and emitted values (check_regions.py and check_copies.py read these).
lake exe render > .lake/regions.jsonl || exit 1
echo "regions: $(wc -l < .lake/regions.jsonl) marked regions -> tools/formal/.lake/regions.jsonl"
lake exe values > .lake/values.jsonl || exit 1
echo "values: $(wc -l < .lake/values.jsonl) emitted values -> tools/formal/.lake/values.jsonl"
