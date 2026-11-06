#!/usr/bin/env python3
"""Local regression tests for the strict axiom-audit parser (no Lean required)."""
import unittest

from check_axiom_report import axiom_commands, check_report, strip_lean_comments


class AxiomReportTests(unittest.TestCase):
    def test_nested_comments_are_not_commands(self):
        source = """/-! text
# print not relevant
/- #print axioms hidden2 -/
#print axioms hidden1
-/
-- #print axioms hidden3
#print axioms Real.theorem
"""
        self.assertEqual(axiom_commands(source), ["Real.theorem"])

    def test_comments_do_not_create_spurious_imports(self):
        source = "import Real.Theorem\n/- import Missing.Fake -/\n"
        self.assertNotIn("Missing.Fake", strip_lean_comments(source))

    def test_every_command_has_a_report(self):
        source = "#print axioms foo\n#print axioms bar\n"
        with self.assertRaisesRegex(ValueError, "Incomplete"):
            check_report(source, "'foo' depends on axioms: [propext]\n")

    def test_whitelisted_and_no_axioms(self):
        check_report(
            "#print axioms foo\n#print axioms bar\n",
            "'foo' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'bar' does not depend on any axioms\n",
        )

    def test_extra_report_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Incomplete"):
            check_report("#print axioms foo\n", "'foo' does not depend on any axioms\n"
                         "'bar' depends on axioms: [propext]\n")

    def test_duplicate_report_does_not_mask_missing_declaration(self):
        src = "#print axioms A.check\n#print axioms B.check\n"
        out = ("'A.check' depends on axioms: [propext]\n"
               "'A.check' depends on axioms: [propext]\n")
        with self.assertRaisesRegex(ValueError, "mismatched"):
            check_report(src, out)

    def test_wrong_declaration_name_rejected_despite_matching_count(self):
        src = "#print axioms Actual.theorem\n"
        out = "'Different.theorem' does not depend on any axioms\n"
        with self.assertRaisesRegex(ValueError, "mismatched"):
            check_report(src, out)

    def test_fully_qualified_axiom_report(self):
        src = "#print axioms SuccessorTree.NonPrecompact.someTheorem\n"
        out = ("info: file.lean:12:0: "
               "'SuccessorTree.NonPrecompact.someTheorem' "
               "depends on axioms: [propext, Classical.choice, Quot.sound]\n")
        check_report(src, out)

    def test_sorry_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "sorryAx"):
            check_report("#print axioms foo", "'foo' depends on axioms: [sorryAx]\n")

    def test_custom_axiom_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "My.axiom"):
            check_report("#print axioms foo", "'foo' depends on axioms: [My.axiom]\n")

    def test_no_active_commands_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "no active"):
            check_report("-- #print axioms foo\n", "'foo' does not depend on any axioms\n")


if __name__ == "__main__":
    unittest.main()
