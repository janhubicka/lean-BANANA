#!/usr/bin/env bash
# CI-only focused Lean gate for isolated BANANA mathlib prototypes.
# Unlike audit_mathlib_prototypes_local.sh, this avoids the full root
# build: the ordinary repository CI checks the production modules.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build BANANA.NonPrecompact.BananaLimitBilinearity BANANA.NonPrecompact.BananaArbitraryAmalgamTools

for file in \
  prototypes/BananaBilinearMapBridge.lean \
  prototypes/BananaMatrixBilinearBridge.lean
do
  output="$(mktemp)"
  if ! lake env lean "$file" >"$output" 2>&1; then
    cat "$output"
    rm -f "$output"
    echo "Lean elaboration failed in $file"
    exit 1
  fi
  cat "$output"
  python3 scripts/check_axiom_report.py "$file" "$output"
  rm -f "$output"
  echo "PASS: Lean and transitive axiom audit for $file"
done
