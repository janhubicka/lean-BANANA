#!/usr/bin/env bash
# Track C exact-head verification. Runs locally; never dispatches GitHub Actions.
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 EXACT_PR_HEAD_SHA" >&2
  exit 2
fi
expected="$1"
actual="$(git rev-parse HEAD)"
if [[ "$actual" != "$expected" ]]; then
  echo "Refusing to validate a different commit: expected $expected, actual $actual" >&2
  exit 2
fi
if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
  echo "Refusing to validate with modified tracked files" >&2
  exit 2
fi
for tool in lake python3; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "Missing required local executable: $tool" >&2
    exit 2
  fi
done

echo "=== Track C: exact commit $actual ==="
python3 scripts/check_lean_module_graph.py
lake build BANANA
bash scripts/audit_all_axioms_local.sh

# These are semantic regressions, not substitutes for the Lean build.
regressions=(
  scripts/check_folkman_tuple_profiles_small.py
  scripts/check_folkman_tuple_term_completeness_small.py
  scripts/check_folkman_nonunital_normalisation.py
  scripts/check_folkman_native_term_coordinate_bridge.py
  scripts/check_folkman_native_presentation_profiles.py
  scripts/check_folkman_presented_embedding_naturality.py
  scripts/check_folkman_profile_common_extension.py
  scripts/check_folkman_stage_generated_closures.py
)
for script in "${regressions[@]}"; do
  python3 "$script"
  # Every assert-driven check must refuse -O/PYTHONOPTIMIZE rather
  # than becoming a silent success when assertions are disabled.
  if optimised_output="$(python3 -O "$script" 2>&1)"; then
    echo "Unsafe optimised PASS (assertions skipped): $script" >&2
    exit 1
  fi
  if [[ "$optimised_output" != *"Regression checks require assertions"* ]]; then
    echo "Optimised test did not fail via the expected assertion guard: $script" >&2
    printf '%s\n' "$optimised_output" >&2
    exit 1
  fi
done

echo "PASS: local build and regression commands completed at $actual"
echo "Manually inspect the transitive #print axioms reports and obtain independent proof reviews."
