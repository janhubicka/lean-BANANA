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
audit_files=()
audit_deps=()
while IFS= read -r -d '' file; do
  audit_files+=("$file")
  audit_deps+=("$file:deps")
done < <(find BANANA -type f -name '*AxiomAudit.lean' -print0 | sort -z)

# Compile imports that are only reachable from audit entry points as well.
lake build BANANA "${audit_deps[@]}"
for file in "${audit_files[@]}"; do
  result="$(mktemp)"
  if ! lake env lean "$file" >"$result" 2>&1; then
    cat "$result" >&2
    rm -f "$result"
    echo "Failed axiom audit: $file" >&2
    exit 1
  fi
  if ! python3 scripts/check_axiom_report.py "$file" "$result"; then
    cat "$result" >&2
    rm -f "$result"
    echo "Unexpected axiom dependency in: $file" >&2
    exit 1
  fi
  rm -f "$result"
done
echo "Passed ${#audit_files[@]} axiom-audit modules: only propext, Classical.choice and Quot.sound."
