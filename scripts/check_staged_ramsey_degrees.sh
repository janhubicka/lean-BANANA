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
  python3 - "$file" "$log" <<'PY'
import pathlib
import re
import sys
source = pathlib.Path(sys.argv[1]).read_text()
log = pathlib.Path(sys.argv[2]).read_text()
expected = len(re.findall(r'^\s*#print axioms\s+', source, re.MULTILINE))
assert expected > 0, 'No transitive axiom checks requested'
axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
no_axioms = re.findall(r'does not depend on any axioms', log)
if len(axioms) + len(no_axioms) < expected:
    raise SystemExit(f'Missing Lean axiom output: expected {expected}, saw {len(axioms)+len(no_axioms)}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for item in axioms:
    observed = {x.strip() for x in item.split(',') if x.strip()}
    unexpected = observed - allowed
    if unexpected:
        raise SystemExit(f'Unexpected axioms: {sorted(unexpected)}')
if 'sorryAx' in log:
    raise SystemExit('Lean output mentions sorryAx')
print(f'AUDITED: {expected} declarations; only standard Lean axioms')
PY
done

echo 'All staged degree modules built and their transitive axiom outputs checked.'
