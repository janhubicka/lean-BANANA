#!/usr/bin/env bash
# Local Lean gate for the symplectic circulation draft; no GitHub Actions.
set -euo pipefail
if ! command -v lake >/dev/null 2>&1; then
  echo "BLOCKED: local lake unavailable; no kernel claim made" >&2
  exit 2
fi
modules=(
  SymplecticAlternatingStrongAmalgam
  SymplecticAlternatingBilinPreservation
  SymplecticAlternatingCoordinateTransport
  SymplecticAlternatingAdaptedCoordinates
  SymplecticAlternatingMatrixCertificate
  SymplecticAlternatingIsometryCoordinates
)
for m in "${modules[@]}"; do
  echo "BUILD: BANANA.NonPrecompact.${m}"
  lake build "BANANA.NonPrecompact.${m}"
  echo "AXIOMS: ${m}"
  lake env lean "BANANA/NonPrecompact/${m}AxiomAudit.lean"
done
python3 scripts/check_symplectic_alternating_strong_ap_small.py
python3 scripts/check_symplectic_alternating_basis_change_small.py
python3 scripts/check_symplectic_adapted_coordinates_small.py
python3 scripts/check_symplectic_alternating_matrix_criterion_small.py
lake build BANANA
echo "Build and finite regressions completed. Independently inspect axiom output and theorem statements."
