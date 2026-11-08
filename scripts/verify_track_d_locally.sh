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
# The expected revision must come from the PR's GitHub head, not from
# git rev-parse HEAD in this checkout (which would prove nothing).
if [[ -z "${EXPECTED_HEAD_SHA:-}" ]]; then
  echo 'EXPECTED_HEAD_SHA is required; copy the 40-hex SHA from PR #310.' >&2
  exit 2
fi
if [[ ! "$EXPECTED_HEAD_SHA" =~ ^[0-9a-f]{40}$ ]]; then
  echo 'EXPECTED_HEAD_SHA must be a full 40-character lowercase Git SHA.' >&2
  exit 2
fi
if [[ "$HEAD_SHA" != "$EXPECTED_HEAD_SHA" ]]; then
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
# Prevent finite-test imports from creating untracked scripts/__pycache__ files.
# The checkout is required to be clean both before and after local verification;
# without this setting a successful first run could block its own rerun.
export PYTHONDONTWRITEBYTECODE=1
# Several older finite regressions use Python assert statements. An ambient
# PYTHONOPTIMIZE setting would silently skip those assertions even for
# commands invoking "python3" without -O. Fail closed instead.
if ! python3 -c 'import sys; sys.exit(0 if sys.flags.optimize == 0 else 1)'; then
  echo 'Python optimisation is active: standard-mode assertions are disabled.' >&2
  echo 'Unset PYTHONOPTIMIZE and rerun the exact-head verification.' >&2
  exit 2
fi
python3 scripts/test_check_axiom_report.py
python3 scripts/test_check_lean_module_graph.py
python3 scripts/test_verify_track_d_driver.py
python3 scripts/check_lean_module_graph.py
python3 scripts/check_banana_actual_coordinate_functor.py
python3 -O scripts/check_banana_actual_coordinate_functor.py
python3 scripts/check_banana_coherent_choices.py
python3 scripts/check_banana_coherent_choice_variants.py
python3 -O scripts/check_banana_coherent_choice_variants.py
python3 scripts/check_banana_coherent_choice_variants.py --mixed4
python3 -O scripts/check_banana_coherent_choice_variants.py --mixed4
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
# The final theorem imports 13 of the 15 new production modules. Two more
# modules are standalone, imported only by their audit files. Building just
# the end-to-end theorem would silently omit those two auxiliary modules.
# Explicitly build and parse ALL nine Track D axiom-audit entry points.
# Dependency-respecting order, from small independent lemmas to the
# full actual-subpair coherent-EPPA theorem. Stop at the first failure.
track_d_audit_modules=(
  BananaMatrixAutGroupAxiomAudit
  CoherentRepresentativeCoreAxiomAudit
  CoherentEppaRepresentativeTransportAxiomAudit
  BananaMatrixCompletionActionHomAxiomAudit
  BananaMatrixCoherentTransportAxiomAudit
  BananaMatrixCoherentOneClassAxiomAudit
  BananaPresentedSubpairAtlasAxiomAudit
  BananaActualSubpairCoordinatesAxiomAudit
  BananaActualSubpairUnindexedCoherenceAxiomAudit
)
for module in "${track_d_audit_modules[@]}"; do
  file="BANANA/NonPrecompact/${module}.lean"
  if [[ ! -f "$file" ]]; then
    echo "Missing Track D axiom audit module: $file" >&2
    exit 1
  fi
  lake build "+BANANA.NonPrecompact.${module}"
  result="$(mktemp)"
  if ! lake env lean "$file" >"$result" 2>&1; then
    cat "$result" >&2
    rm -f "$result"
    echo "Track D Lean elaboration failed: $file" >&2
    exit 1
  fi
  if ! python3 scripts/check_axiom_report.py "$file" "$result"; then
    cat "$result" >&2
    rm -f "$result"
    echo "Unexpected Track D axiom dependency: $file" >&2
    exit 1
  fi
  rm -f "$result"
done
lake build BANANA
bash scripts/audit_all_axioms_local.sh
# Source fidelity must hold after the build as well as before it.
if [[ -n "$(git status --porcelain)" ]]; then
  echo 'Verification changed the Git worktree; refusing an exact-head sign-off.' >&2
  git status --porcelain >&2
  exit 1
fi
printf 'Local kernel build and transitive-axiom audit passed on %s\n' "$HEAD_SHA"
echo 'Independent mathematical statement-fidelity and counterexample reviews remain required.'
