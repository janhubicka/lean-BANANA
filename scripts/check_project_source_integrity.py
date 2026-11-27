#!/usr/bin/env python3
"""Supplement kernel/axiom checks with a fail-closed project source hygiene scan."""
from pathlib import Path
import argparse
import json
import re
import subprocess

from check_axiom_report import lexical_code

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(
    r"(?<![\w'])(?:sorryAx|sorry|admit|axiom|constant|opaque|unsafe|"
    r"implemented_by|extern|csimp|native_decide|ofReduceBool|ofReduceNat|"
    r"trustCompiler|skipKernelTC|elab|macro|syntax)(?![\w'])|"
    r"#exit\b|(?<![\w'])partial\s+def\b"
)


def findings(source: str) -> list[tuple[int, str]]:
    code = lexical_code(source, mask_literals=True)
    return [(code.count("\n", 0, m.start()) + 1, m.group())
            for m in FORBIDDEN.finditer(code)]


def git(directory: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(directory), *args], text=True
    )


def source_files(directory: Path, module: str) -> list[Path]:
    entry = directory / (module + ".lean")
    if not entry.is_file():
        raise ValueError(f"missing proof root {entry}")
    return [entry, *sorted((directory / module).rglob("*.lean"))]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root-only", action="store_true",
                    help="run before Lake materialises the pinned dependencies")
    args = ap.parse_args()
    sources = source_files(ROOT, "BANANA")
    if not args.root_only:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        packages = ROOT / manifest["packagesDir"]
        # Version 1 has only mathlib and its pinned dependency ecosystem.
        allowed_urls = ["https://github.com/leanprover-community/mathlib4","https://github.com/leanprover-community/plausible","https://github.com/leanprover-community/LeanSearchClient","https://github.com/leanprover-community/import-graph","https://github.com/leanprover-community/ProofWidgets4","https://github.com/leanprover-community/aesop","https://github.com/leanprover-community/quote4","https://github.com/leanprover-community/batteries","https://github.com/leanprover/lean4-cli"]
        seen = set()
        for pkg in manifest["packages"]:
            if pkg["type"] != "git":
                raise ValueError(f"non-Git dependency is not release-pinned: {pkg['name']}")
            path = packages / pkg["name"].strip("«»")
            actual = git(path, "rev-parse", "HEAD").strip()
            if actual != pkg["rev"]:
                raise ValueError(f"dependency SHA mismatch: {path}: {actual} != {pkg['rev']}")
            if git(path, "status", "--porcelain", "--untracked-files=no"):
                raise ValueError(f"modified tracked dependency source: {path}")
            untracked = git(path, "ls-files", "--others", "--exclude-standard", "-z")
            if any(p.endswith(".lean") for p in untracked.split("\0")):
                raise ValueError(f"untracked Lean source in dependency: {path}")
            if pkg["url"] not in allowed_urls:
                raise ValueError(f"unexpected dependency: {pkg['url']}")
            seen.add(pkg["url"])
            print(f"PIN {pkg['name']} {actual}")
        if seen != set(allowed_urls):
            raise ValueError(f"unexpected dependency closure: {seen}")
    errors = []
    for file in sources:
        try:
            errors.extend(f"{file.relative_to(ROOT)}:{line}: {word}"
                          for line, word in findings(file.read_text(encoding="utf-8")))
        except ValueError as exc:
            errors.append(f"{file}: {exc}")
    if errors:
        raise SystemExit("FAIL: project source integrity:\n" + "\n".join(errors))
    print(f"PASS: project proof source hygiene ({len(sources)} Lean files)")


if __name__ == "__main__":
    main()
