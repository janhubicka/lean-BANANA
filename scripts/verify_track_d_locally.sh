#!/usr/bin/env bash
# Local-only verification for BANANA coherent EPPA Track D.
# This script NEVER starts GitHub Actions or changes manuscript files.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v git >/dev/null 2>&1 || ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo 'Run this script from an exact-head Git checkout.' >&2
  exit 2
fi
HEAD_SHA="$(git rev-parse HEAD)"
if [[ -n "${EXPECTED_HEAD_SHA:-}" && "$HEAD_SHA" != "$EXPECTED_HEAD_SHA" ]]; then
  echo "Wrong checkout SHA: $HEAD_SHA (expected $EXPECTED_HEAD_SHA)" >&2
  exit 2
fi
if [[ -n "$(git status --porcelain)" ]]; then
  echo 'Working tree is not clean: cannot certify an exact-head run.' >&2
  exit 2
fi
printf 'Verifying Track D on commit %s\n' "$HEAD_SHA"

if ! command -v python3 >/dev/null 2>&1; then
  echo 'Python 3 is required.' >&2
  exit 2
fi
python3 scripts/test_check_axiom_report.py
python3 scripts/test_check_lean_module_graph.py
python3 scripts/check_lean_module_graph.py
python3 scripts/check_banana_actual_coordinate_functor.py
python3 -O scripts/check_banana_actual_coordinate_functor.py
python3 scripts/check_banana_coherent_choices.py
python3 scripts/check_banana_coherent_choice_variants.py
python3 -O scripts/check_banana_coherent_choice_variants.py
python3 scripts/check_banana_coherent_choices_dimension4.py
python3 -O scripts/check_banana_coherent_choices_dimension4.py
python3 scripts/check_banana_zero_pairing_witness_bound.py
python3 scripts/check_banana_presented_subpair_classes.py
python3 scripts/check_banana_finite_aut_completion_group.py
python3 scripts/check_coherent_eppa_small_pairings.py
python3 scripts/check_coherent_representative_core.py
python3 scripts/check_coherent_representative_transport.py

probe="$(mktemp)"
trap 'rm -f "$probe"' EXIT
for mode in ordinary optimised; do
  if [[ "$mode" == ordinary ]]; then
    args=(python3)
  else
    args=(python3 -O)
  fi
  if "${args[@]}" scripts/check_banana_actual_coordinate_functor.py --probe-guard >"$probe" 2>&1; then
    echo "ERROR: negative guard probe unexpectedly succeeded ($mode)." >&2
    exit 1
  fi
  if ! grep -q 'CHECK_GUARD_ACTIVE' "$probe"; then
    echo "ERROR: negative guard probe failed for the wrong reason ($mode)." >&2
    cat "$probe" >&2
    exit 1
  fi
done

if ! command -v lake >/dev/null 2>&1; then
  echo 'Lean/Lake is missing. Python checks passed, but no proof is kernel verified.' >&2
  exit 2
fi
if [[ ! -f lean-toolchain || ! -f lakefile.toml ]]; then
  echo 'Pinned Lean project files are missing.' >&2
  exit 2
fi
lake build +BANANA.NonPrecompact.BananaActualSubpairUnindexedCoherenceAxiomAudit
lake env lean BANANA/NonPrecompact/BananaActualSubpairUnindexedCoherenceAxiomAudit.lean
lake build BANANA
bash scripts/audit_all_axioms_local.sh
printf 'Local kernel build and transitive-axiom audit passed on %s\n' "$HEAD_SHA"
echo 'Independent mathematical statement-fidelity and counterexample reviews remain required.'
