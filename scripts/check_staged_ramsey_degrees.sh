#!/usr/bin/env bash
# Local-only kernel and transitive-axiom audit for staged BANANA Ramsey proofs.
# Never use GitHub Actions for this project. No success is reported unless Lean runs.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake is not installed; no Lean proof has been checked.' >&2
  exit 2
fi

logdir="${BANANA_LEAN_AUDIT_LOGDIR:-.lake/banana-audit}"
mkdir -p "$logdir"
modules=(
  BANANA.NonPrecompact.LinePairDegreeAxiomAudit
  BANANA.NonPrecompact.BananaCopyDegreeAxiomAudit
  BANANA.NonPrecompact.BananaOneSidedAxiomAudit
  BANANA.NonPrecompact.BananaOneSidedSubspaceEquivAxiomAudit
  BANANA.NonPrecompact.BananaCopyFunctorAxiomAudit
  BANANA.NonPrecompact.FinitePerfectGLAxiomAudit
)

for module in "${modules[@]}"; do
  file="${module//.//}.lean"
  log="$logdir/${module##*.}.log"
  echo "Checking $file"
  lake build "$module"
  lake env lean "$file" 2>&1 | tee "$log"
  python3 scripts/check_axiom_report.py "$file" "$log"
done

echo 'All staged degree modules built and their transitive axiom outputs checked.'
