#!/usr/bin/env python3
"""Fixture tests for root, audit-only and unreachable Lean module detection."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent


class LeanModuleGraphTests(unittest.TestCase):
    def test_audit_only_is_not_dead_and_comments_are_not_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "BANANA").mkdir()
            (root / "scripts").mkdir()
            for script in ("check_axiom_report.py", "check_lean_module_graph.py"):
                shutil.copyfile(SCRIPTS / script, root / "scripts" / script)
            (root / "BANANA.lean").write_text(
                "import BANANA.A\n/-! import BANANA.Nonexistent -/\n",
                encoding="utf-8",
            )
            (root / "BANANA" / "A.lean").write_text(
                "import BANANA.B\n", encoding="utf-8"
            )
            (root / "BANANA" / "B.lean").write_text("", encoding="utf-8")
            (root / "BANANA" / "C.lean").write_text("", encoding="utf-8")
            (root / "BANANA" / "CAxiomAudit.lean").write_text(
                "import BANANA.C\n#print axioms Example.check\n", encoding="utf-8"
            )
            dead = root / "BANANA" / "Dead.lean"
            dead.write_text("", encoding="utf-8")

            def graph():
                return subprocess.run(
                    [sys.executable, str(root / "scripts" / "check_lean_module_graph.py")],
                    capture_output=True, text=True, check=False,
                )

            first = graph()
            self.assertNotEqual(first.returncode, 0)
            self.assertIn("Audit-only proof modules (review before deletion): 1", first.stdout)
            self.assertIn("AUDIT-ONLY PROOF MODULE: BANANA/C.lean", first.stderr)
            self.assertIn("DEAD MODULE CANDIDATE: BANANA/Dead.lean", first.stderr)
            self.assertNotIn("MISSING IMPORT", first.stderr)

            dead.unlink()
            second = graph()
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertIn("Unreachable production modules: 0", second.stdout)


if __name__ == "__main__":
    unittest.main()
