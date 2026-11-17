#!/usr/bin/env bash
# Run prototype checks against the dependency versions pinned by this repository.
# This is a local check; GitHub Actions are intentionally not used.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo "Lean Lake is required; see lean-toolchain for the pinned version" >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "Python 3 is required for the axiom-audit parser" >&2
  exit 2
fi

lake build BANANA
python3 scripts/check_lean_module_graph.py

for file in \
  prototypes/BananaBilinearMapBridge.lean \
  prototypes/BananaMatrixBilinearBridge.lean
do
  result="$(mktemp)"
  if ! lake env lean "$file" >"$result" 2>&1; then
    cat "$result" >&2
    rm -f "$result"
    echo "Failed Lean prototype: $file" >&2
    exit 1
  fi
  if ! python3 scripts/check_axiom_report.py "$file" "$result"; then
    cat "$result" >&2
    rm -f "$result"
    echo "Failed transitive axiom check: $file" >&2
    exit 1
  fi
  rm -f "$result"
  echo "Checked $file (Lean + permitted transitive axioms)"
done

python3 scripts/check_banana_bilinear_bridge_small.py
