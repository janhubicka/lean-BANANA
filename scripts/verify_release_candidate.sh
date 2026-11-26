#!/usr/bin/env bash
# Verify the exact tracked release snapshot, using the committed dependency pins.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo "Lean Lake is required; use the pinned lean-toolchain" >&2
  exit 2
fi
git diff --exit-code HEAD --
head=$(git rev-parse HEAD)
export BANANA_AXIOM_LOGDIR=".lake/banana-release-audit/$head/axioms"
logdir=".lake/banana-release-audit/$head"
mkdir -p "$logdir"
{
  git rev-parse HEAD
  cat lean-toolchain
  lake env lean --version
  sha256sum lean-toolchain lakefile.toml lake-manifest.json
  git diff --exit-code HEAD -- lean-toolchain lakefile.toml lake-manifest.json
  bash scripts/audit_all_axioms_local.sh
  python3 -m unittest discover -s scripts -p 'test_*.py'
  git diff --exit-code HEAD -- lean-toolchain lakefile.toml lake-manifest.json
  test "$(git rev-parse HEAD)" = "$head"
} 2>&1 | tee "$logdir/verification.log"
