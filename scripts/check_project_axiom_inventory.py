#!/usr/bin/env python3
"""Check the direct project declaration inventory and its completion record.

The Lean audit command checks each declaration itself; this parser verifies
the archived inventory is complete, unique and uses only allowed axioms.
The manuscript marker-to-inventory correspondence is a separate review.
"""
from pathlib import Path
import sys

from check_axiom_report import ALLOWED

PREFIXES = {"BANANA"}


def check_inventory(text: str) -> dict[str, set[str]]:
    seen = {}
    done = []
    for line in text.splitlines():
        if line.startswith("PROJECT_AXIOMS\t"):
            fields = line.split("\t")
            if len(fields) != 4:
                raise ValueError(f"malformed inventory row: {line}")
            _, module, name, dependencies = fields
            if not name or module.split(".")[0] not in PREFIXES or name in seen:
                raise ValueError(f"unexpected module or duplicate name: {line}")
            deps = set(dependencies.split(",")) if dependencies else set()
            if deps - ALLOWED:
                raise ValueError(f"forbidden axioms for {name}: {deps - ALLOWED}")
            seen[name] = module
        elif line.startswith("PROJECT_AXIOMS_DONE\t"):
            done.append(line.split("\t"))
    if len(done) != 1 or len(done[0]) != 4:
        raise ValueError("missing or duplicated completion record")
    checked, unavailable, total = map(int, done[0][1:])
    if checked <= 0 or unavailable < 0 or len(seen) != checked or checked + unavailable != total:
        raise ValueError("incomplete project axiom inventory")
    by_module = {}
    for name, module in seen.items():
        by_module.setdefault(module, set()).add(name)
    for prefix in ("BANANA",):
        if not any(m.split(".")[0] == prefix for m in by_module):
            raise ValueError(f"no visible declarations audited for {prefix}")
    print(f"PASS: {checked} directly audited declarations in {len(by_module)} modules; "
          f"{unavailable} inaccessible private constants excluded")
    return by_module


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("Usage: check_project_axiom_inventory.py <inventory.log>")
    check_inventory(Path(sys.argv[1]).read_text(encoding="utf-8"))
