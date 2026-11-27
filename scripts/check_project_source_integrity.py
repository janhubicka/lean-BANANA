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
    sources = [p for module in ("BANANA", "SuccessorTree", "RamseySpace")
               for p in source_files(ROOT, module)]
    provenance = json.loads((ROOT / "docs/vendored-provenance.json").read_text())
    expected = {x["path"]: x["blob"] for x in provenance["upstream_files"]}
    actual = {p.relative_to(ROOT).as_posix() for module in ("SuccessorTree", "RamseySpace")
              for p in (ROOT / module).rglob("*.lean")}
    if actual != set(expected):
        raise ValueError("vendored source closure changed")
    import hashlib
    for path, blob in expected.items():
        content = (ROOT / path).read_bytes()
        digest = hashlib.sha1(f"blob {len(content)}\0".encode() + content).hexdigest()
        if digest != blob:
            raise ValueError(f"vendored source changed: {path}")
    if not args.root_only:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        packages = ROOT / manifest["packagesDir"]
        allowed = {'https://github.com/leanprover-community/mathlib4': '5bd58ac291422a21f412ae354c91e7d172255a2c', 'https://github.com/leanprover-community/plausible': 'b7fb2b866d25bd937a2069931f9733197521cb27', 'https://github.com/leanprover-community/LeanSearchClient': 'c35806f43135ab3f254429d0c00bd13fc0123f77', 'https://github.com/leanprover-community/import-graph': '103cd9a46972ee39d9defb2f54ae49823b1228eb', 'https://github.com/leanprover-community/ProofWidgets4': '87dfe779d5dfd03142ee4fe158911b8eb553ec98', 'https://github.com/leanprover-community/aesop': 'a92ed98e694702934d40d12f24a1a449144db43e', 'https://github.com/leanprover-community/quote4': '37b0ba0b26109cf9f9c541f0f9557e50cfa1a3b9', 'https://github.com/leanprover-community/batteries': '950339ce0fd0cc0673a22d87036075737586aed2', 'https://github.com/leanprover/lean4-cli': '843844fa601dd56767b1eb22b7ada5b64d5e567a'}
        seen = {}
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
            if pkg["url"] in seen or allowed.get(pkg["url"]) != actual:
                raise ValueError(f"unexpected dependency: {pkg['url']} at {actual}")
            seen[pkg["url"]] = actual
            print(f"PIN {pkg['name']} {actual}")
        if seen != allowed:
            raise ValueError("unexpected mathlib dependency closure")
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
