#!/usr/bin/env python3
"""Check that *every* active Lean '#print axioms' has a safe report.

This validates a completed Lean invocation's output; it does not run Lean.
"""
from pathlib import Path
from collections import Counter
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


# A quote at the end of a Lean identifier (e.g. f') is not a character literal.
_CHAR = re.compile(r"'(?:[^'\\\n]|\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|[^\n]))'")

def lexical_code(source: str, *, mask_literals: bool = False) -> str:
    """Mask comments, and optionally strings/chars, retaining line positions.

    This is a source hygiene lexer, not an implementation of Lean's parser.
    Nested block comments, escaped quotes and character literals are handled.
    """
    out = []
    i = 0
    depth = 0
    in_string = False

    def masked(chunk: str) -> str:
        return "".join("\n" if c == "\n" else " " for c in chunk)

    while i < len(source):
        c = source[i]
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append(masked(c))
                i += 1
        elif in_string:
            if c == "\\" and i + 1 < len(source):
                chunk = source[i:i + 2]
                out.append(masked(chunk) if mask_literals else chunk)
                i += 2
            else:
                out.append(masked(c) if mask_literals else c)
                if c == '"':
                    in_string = False
                i += 1
        elif pair == "--":
            stop = source.find("\n", i)
            stop = len(source) if stop < 0 else stop
            out.append(masked(source[i:stop]))
            i = stop
        elif pair == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" " if mask_literals else c)
            i += 1
        elif c == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            literal = _CHAR.match(source, i)
            if literal:
                chunk = literal.group()
                out.append(masked(chunk) if mask_literals else chunk)
                i = literal.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    if depth or in_string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(out)


def strip_lean_comments(source: str) -> str:
    """Mask comments, retaining literals and line positions."""
    return lexical_code(source)


def axiom_commands(source: str) -> list[str]:
    """Get active, line-initial '#print axioms' targets (not comments)."""
    cleaned = lexical_code(source, mask_literals=True)
    return re.findall(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+([^\s]+)", cleaned)


def check_report(source: str, output: str) -> None:
    """Reject incomplete reports and forbidden transitive axioms."""
    commands = axiom_commands(source)
    if not commands:
        raise ValueError("Axiom-audit source has no active #print axioms")

    # A count-only check silently accepts two reports for A while
    # missing B. Compare qualified declaration names as a multiset.
    dependencies = re.findall(
        r"'([^\n]+?)' depends on axioms:\s*\[([^\]]*)\]", output, re.S
    )
    no_axioms = re.findall(
        r"'([^\n]+?)' does not depend on (?:any )?axioms\b", output
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
