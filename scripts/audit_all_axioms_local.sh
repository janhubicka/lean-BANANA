#!/usr/bin/env bash
# Build the library locally and check every transitive Lean axiom-audit entry.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo "Lean Lake is required; install the toolchain from lean-toolchain" >&2
  exit 2
fi
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
  if grep -Fq "sorryAx" "$result"; then
    cat "$result" >&2
    rm -f "$result"
    echo "Axiom audit found sorryAx: $file" >&2
    exit 1
  fi
  rm -f "$result"
  count=$((count + 1))
done < <(find BANANA -type f -name '*AxiomAudit.lean' -print0 | sort -z)
echo "Passed $count Lean axiom-audit modules (no sorryAx)."
