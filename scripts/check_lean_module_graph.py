#!/usr/bin/env python3
"""Check local Lean import reachability and missing modules.

This is a source graph audit, not a Lean kernel proof.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
files = sorted((ROOT / "BANANA").rglob("*.lean"))
entry = ROOT / "BANANA.lean"
if not entry.is_file():
    sys.exit("Missing BANANA.lean entry point")
files.insert(0, entry)
sources = {p.relative_to(ROOT).as_posix(): p for p in files}


def local_imports(file):
    out = set()
    for line in file.read_text(encoding="utf-8").splitlines():
        match = re.match(r"\s*import\s+(.+)$", line)
        if not match:
            continue
        for name in match.group(1).split():
            if name == "BANANA":
                out.add("BANANA.lean")
            elif name.startswith("BANANA."):
                out.add(name.replace(".", "/") + ".lean")
    return out


graph = {name: local_imports(file) for name, file in sources.items()}
missing = sorted((name, dep) for name, deps in graph.items()
                 for dep in deps if dep not in sources)
audits = {name for name in sources if name.endswith("AxiomAudit.lean")}
production = set(sources) - audits
empty_audits = sorted(name for name in audits
                      if "#print axioms " not in
                      sources[name].read_text(encoding="utf-8"))
visited = set()
active = set()
cycles = []


def visit(name):
    if name in visited or name not in graph:
        return
    if name in active:
        cycles.append(name)
        return
    active.add(name)
    for dep in sorted(graph[name]):
        visit(dep)
    active.remove(name)
    visited.add(name)


visit("BANANA.lean")
root_reachable = len(production & visited)
for name in sorted(audits):
    visit(name)
dead = sorted(production - visited)
print(f"Lean files: {len(sources)} ({len(production)} production, "
      f"{len(audits)} axiom audits)")
print(f"Reachable production modules from BANANA.lean: {root_reachable}")
print(f"Unreachable production modules: {len(dead)}")
for name, dep in missing:
    print(f"MISSING IMPORT: {name} -> {dep}", file=sys.stderr)
for name in cycles:
    print(f"IMPORT CYCLE: {name}", file=sys.stderr)
for name in empty_audits:
    print(f"EMPTY AXIOM AUDIT: {name}", file=sys.stderr)
for name in dead:
    print(f"DEAD MODULE CANDIDATE: {name}", file=sys.stderr)
if missing or cycles or empty_audits or dead:
    sys.exit(1)
