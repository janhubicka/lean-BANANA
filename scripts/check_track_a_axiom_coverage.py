#!/usr/bin/env python3
"""Check exact transitive-axiom query coverage for the Track A API.

A source-level check only: it neither elaborates Lean nor proves any theorem.
"""
from pathlib import Path
import re

from check_axiom_report import axiom_commands, strip_lean_comments

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "BANANA/NonPrecompact/FolkmanPartialOwnerComposition.lean"
AUDIT = ROOT / "BANANA/NonPrecompact/FolkmanPartialOwnerCompositionAxiomAudit.lean"
TUPLE_AUDIT = ROOT / "BANANA/NonPrecompact/FolkmanTupleProfilesPairingTransportAxiomAudit.lean"
NATIVE_AUDIT = ROOT / "BANANA/NonPrecompact/FolkmanNativeFiniteCodeEmbeddingAxiomAudit.lean"
NS = "SuccessorTree.NonPrecompact."


def check() -> int:
    source = strip_lean_comments(SRC.read_text(encoding="utf-8"))
    names = re.findall(
        r"(?m)^\s*(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z_][\w'.]*)\b",
        source,
    )
    expected = {NS + name for name in names}
    declared = axiom_commands(AUDIT.read_text(encoding="utf-8"))
    actual = set(declared)
    if len(expected) != len(names) or len(actual) != len(declared):
        raise ValueError("Duplicate declaration or axiom-audit command")
    if expected != actual:
        raise ValueError(f"Audit mismatch: missing={sorted(expected-actual)}, "
                         f"extra={sorted(actual-expected)}")
    users = {
        TUPLE_AUDIT: {"folkmanEdgeCount_cast", "folkmanTuple_edgeCount_cast"},
        NATIVE_AUDIT: {"folkmanNativeFin_edgeCount_cast"},
    }
    for file, needed in users.items():
        found = set(axiom_commands(file.read_text(encoding="utf-8")))
        missing = {NS + name for name in needed} - found
        if missing:
            raise ValueError(f"{file.name}: missing {sorted(missing)}")
    print(f"Track A axiom queries cover all {len(expected)} API declarations "
          "and all three shared/native/tuple cast entries")
    return len(expected)


if __name__ == "__main__":
    check()
