#!/usr/bin/env bash
# Verify the exact tracked release snapshot using the committed dependency pins.
# The same strict gate runs on PRs, main and tags, or in a clean local checkout.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo "Lean Lake is required; use the pinned lean-toolchain" >&2
  exit 2
fi
git diff --exit-code HEAD --
if test -n "$(git ls-files --others --exclude-standard)"; then
  echo "Untracked files in the release checkout; verify a clean clone." >&2
  exit 1
fi
head=$(git rev-parse HEAD)
export PYTHONDONTWRITEBYTECODE=1
logdir=".lake/banana-release-audit/$head"
export BANANA_AXIOM_LOGDIR="$logdir/axioms"
mkdir -p "$logdir"
{
  git rev-parse HEAD
  cat lean-toolchain
  lake env lean --version
  sha256sum lean-toolchain lakefile.toml lake-manifest.json
  git diff --exit-code HEAD -- lean-toolchain lakefile.toml lake-manifest.json
  python3 scripts/check_project_source_integrity.py --root-only
  python3 scripts/check_lean_module_graph.py
  python3 -m unittest discover -s scripts -p 'test_*.py'
  # Fail early on the newly strengthened gates before the 387-module audit loop.
  lake build BANANA
  python3 scripts/check_project_source_integrity.py
  if ! lake env lean scripts/CheckAllProjectAxioms.lean >"$logdir/project-axioms.log" 2>&1; then
    tail -n 100 "$logdir/project-axioms.log" >&2
    exit 1
  fi
  python3 scripts/check_project_axiom_inventory.py "$logdir/project-axioms.log"
  python3 scripts/check_manuscript_linked_declarations.py "$logdir/project-axioms.log"
  # Unlike an incremental build, this replays the complete imported environment.
  lake env leanchecker --fresh --verbose BANANA 2>&1 | tee "$logdir/kernel-replay.log"
  bash scripts/audit_all_axioms_local.sh
  # Preserve the non-Lean regression checks from the previous workflow.
  for check in prebanana_fibrewise_allocation prebanana_fiveary_extension \
      strong_amalgam_arbitrary omega_tuple_signature finite_block_pair_lift \
      nested_banana_gl perfect_orthogonal_complements folkman_pivot \
      folkman_atom_matrix folkman_partial_owner folkman_pairing_extension; do
    python3 "scripts/check_${check}_small.py"
  done
  git diff --exit-code HEAD --
  test "$(git rev-parse HEAD)" = "$head"
  echo "STRICT RELEASE AUDIT PASSED: $head"
} 2>&1 | tee "$logdir/verification.log"
