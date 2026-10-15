#!/usr/bin/env bash
# Build the library and audit all printed transitive Lean axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo "Lean Lake is required; use the pinned lean-toolchain" >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "Python 3 is required for strict axiom parsing" >&2
  exit 2
fi
python3 scripts/check_lean_module_graph.py
lake build BANANA
count=0
while IFS= read -r -d '' file; do
  result="$(mktemp)"
  if ! lake env lean "$file" >"$result" 2>&1; then
    cat "$result" >&2
    rm -f "$result"
    echo "Failed axiom audit: $file" >&2
    exit 1
  fi
  if ! python3 - "$result" <<'PY'
import pathlib
import re
import sys

output = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
matches = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.S)
no_axioms = re.findall(r"does not depend on (?:any )?axioms", output)
if not matches and not no_axioms:
    sys.exit("Axiom audit produced no '#print axioms' result")
allowed = {"propext", "Classical.choice", "Quot.sound"}
unexpected = sorted({name.strip()
                     for group in matches for name in group.split(",")
                     if name.strip() and name.strip() not in allowed})
if "sorryAx" in output or unexpected:
    sys.exit("Non-standard proof axiom(s): " +
             ", ".join(unexpected or ["sorryAx"]))
PY
  then
    cat "$result" >&2
    rm -f "$result"
    echo "Unexpected axiom dependency in: $file" >&2
    exit 1
  fi
  rm -f "$result"
  count=$((count + 1))
done < <(find BANANA -type f -name '*AxiomAudit.lean' -print0 | sort -z)
echo "Passed $count axiom-audit modules: only propext, Classical.choice and Quot.sound."
