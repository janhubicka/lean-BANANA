#!/usr/bin/env bash
# Run only with the pinned Lean toolchain in an exact-head local checkout.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo "BLOCKED: install the pinned Lean toolchain from lean-toolchain" >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "BLOCKED: python3 is required for strict audit checks" >&2
  exit 2
fi
printf 'Pinned toolchain: '
cat lean-toolchain
if ! command -v git >/dev/null 2>&1; then
  echo "BLOCKED: git is required for exact-head verification" >&2
  exit 2
fi
if [[ -n "$(git status --porcelain --untracked-files=normal)" ]]; then
  echo "BLOCKED: checkout is not clean; verification must use exact committed sources" >&2
  exit 2
fi
expected_version="$(sed -n 's@^leanprover/lean4:v@@p' lean-toolchain)"
if [[ -z "$expected_version" ]]; then
  echo "BLOCKED: unrecognised lean-toolchain pin" >&2
  exit 2
fi
actual_version="$(lake env lean --version)"
if [[ "$actual_version" != *"$expected_version"* ]]; then
  echo "BLOCKED: Lean version does not match pinned $expected_version" >&2
  echo "Found: $actual_version" >&2
  exit 2
fi
printf 'Verified pinned Lean: %s\n' "$actual_version"
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_lean_module_graph.py
for script in \
  check_folkman_edgecount_cast_small.py \
  check_folkman_partial_owner_parity_small.py \
  check_folkman_owner_composition_small.py \
  check_folkman_embedding_composition_small.py \
  check_folkman_embedding_associativity_small.py \
  check_folkman_owner_category_laws_small.py \
  check_folkman_owner_category_surjective_small.py; do
  python3 "scripts/$script"
done
lake build BANANA.NonPrecompact.FolkmanPartialOwnerComposition \
  BANANA.NonPrecompact.FolkmanPartialOwnerCompositionAxiomAudit \
  BANANA.NonPrecompact.FolkmanNativeFiniteCodeEmbedding \
  BANANA.NonPrecompact.FolkmanNativeFiniteCodeEmbeddingAxiomAudit \
  BANANA.NonPrecompact.FolkmanTupleProfilesPairingTransport \
  BANANA.NonPrecompact.FolkmanTupleProfilesPairingTransportAxiomAudit
lake build BANANA
bash scripts/audit_all_axioms_local.sh
printf 'Track A source and axiom verification completed on: '
git rev-parse HEAD
