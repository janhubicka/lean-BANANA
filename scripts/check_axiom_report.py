#!/usr/bin/env python3
"""Check that *every* active Lean '#print axioms' has a safe report.

This validates a completed Lean invocation's output; it does not run Lean.
"""
from pathlib import Path
from collections import Counter
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def strip_lean_comments(source: str) -> str:
    """Remove nested block and line comments, preserving line boundaries."""
    out = []
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    out.append("\n")
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out.extend(source[i:i + 2])
                i += 2
            else:
                out.append(source[i])
                if source[i] == '"':
                    in_string = False
                i += 1
        elif source.startswith("--", i):
            i = source.find("\n", i)
            if i == -1:
                break
        elif source.startswith("/-", i):
            # A block comment is lexical whitespace, not token concatenation.
            out.append(" ")
            depth = 1
            i += 2
        else:
            out.append(source[i])
            if source[i] == '"':
                in_string = True
            i += 1
    return "".join(out)


def axiom_commands(source: str) -> list[str]:
    """Get active, line-initial '#print axioms' targets (not comments)."""
    cleaned = strip_lean_comments(source)
    return re.findall(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+([^\s]+)", cleaned)


def check_report(source: str, output: str) -> None:
    """Reject incomplete reports and forbidden transitive axioms."""
    commands = axiom_commands(source)
    if not commands:
        raise ValueError("Axiom-audit source has no active #print axioms")

    # A count-only check silently accepts two reports for A while
    # missing B. Compare qualified declaration names as a multiset.
    dependencies = re.findall(
        r"'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S
    )
    no_axioms = re.findall(
        r"'([^'\n]+)' does not depend on (?:any )?axioms\b", output
    )
    expected = Counter(commands)
    observed = Counter(name for name, _ in dependencies)
    observed.update(no_axioms)
    if observed != expected:
        missing = list((expected - observed).elements())
        extra = list((observed - expected).elements())
        raise ValueError(
            "Incomplete or mismatched axiom report: "
            f"missing={missing!r}, unexpected_or_duplicate={extra!r}"
        )
    unexpected = {name.strip()
                  for _, group in dependencies for name in group.split(",")
                  if name.strip() and name.strip() not in ALLOWED}
    if "sorryAx" in output:
        unexpected.add("sorryAx")
    if unexpected:
        raise ValueError("Unexpected transitive axioms: " + ", ".join(sorted(unexpected)))


def main() -> int:
    if len(sys.argv) != 3:
        print("Usage: check_axiom_report.py <audit.lean> <lean-output.txt>", file=sys.stderr)
        return 2
    source = Path(sys.argv[1]).read_text(encoding="utf-8")
    output = Path(sys.argv[2]).read_text(encoding="utf-8")
    try:
        check_report(source, output)
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
