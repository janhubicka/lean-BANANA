#!/usr/bin/env python3
"""Check exact source identities and direct axiom coverage of manuscript links."""
import json
from pathlib import Path
import subprocess
import sys

from check_project_axiom_inventory import check_inventory

ROOT = Path(__file__).resolve().parents[1]


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def blobs(root):
    found = {}
    for row in git(root, "ls-tree", "-r", "-z", "HEAD").split(b"\0"):
        if not row:
            continue
        meta, path = row.split(b"\t", 1)
        _, kind, sha = meta.decode().split()
        if kind == "blob":
            found[path.decode()] = sha
    return found


def check_requirements(requirements, inventory, banana, successor):
    """Resolve by defining module and exact or unique qualified suffix."""
    seen = set()
    resolved = set()
    for req in requirements:
        module, name, path, blob = (req[k] for k in ("module", "name", "path", "blob"))
        key = (module, name)
        if key in seen:
            raise ValueError(f"duplicate requirement: {key}")
        seen.add(key)
        if module != path.removesuffix(".lean").replace("/", "."):
            raise ValueError(f"inconsistent module and source path: {key}")
        tree = successor if module.startswith("SuccessorTree.") else banana
        if tree.get(path) != blob:
            raise ValueError(f"linked source changed; review the declaration crosswalk: {path}")
        source_name = name.removeprefix("_root_.")
        matches = sorted(n for n in inventory.get(module, ())
                         if n == source_name or n.endswith("." + source_name))
        if len(matches) != 1:
            raise ValueError(f"{key}: expected one directly audited declaration, found {matches}")
        resolved.add(matches[0])
    if not seen:
        raise ValueError("empty manuscript declaration requirements")
    return len(seen), len(resolved)


def main():
    if len(sys.argv) != 2:
        sys.exit("Usage: check_manuscript_linked_declarations.py <project-axioms.log>")
    data = json.loads((ROOT / "scripts/manuscript_linked_declarations.json").read_text())
    # The imported upstream proof modules are now part of the archived source tree.
    tree = blobs(ROOT)
    inventory = check_inventory(Path(sys.argv[1]).read_text(encoding="utf-8"))
    count, distinct = check_requirements(data["required"], inventory, tree, tree)
    print(f"PASS: {count} manuscript source declaration references resolve uniquely "
          f"to {distinct} directly audited compiled declarations at the checked source blobs")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        sys.exit(f"FAIL: {exc}")
