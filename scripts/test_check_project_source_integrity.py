import unittest

from check_project_source_integrity import findings


class SourceIntegrityTests(unittest.TestCase):
    def test_comments_strings_chars_and_primed_identifiers(self):
        src = """-- sorry
/-! unsafe /- axiom -/ native_decide -/
def f' := "sorry axiom"
def c : Char := '"'
theorem ok : True := by trivial
"""
        self.assertEqual(findings(src), [])

    def test_after_character_literal(self):
        self.assertEqual(findings("def c : Char := '\"'\ntheorem bad : False := by sorry\n"),
                         [(2, "sorry")])

    def test_forbidden_declarations_and_tactics(self):
        src = "private axiom a : False\nunsafe def f := 0\nexample : True := by native_decide\n"
        self.assertEqual(findings(src), [(1, "axiom"), (2, "unsafe"), (3, "native_decide")])

    def test_nested_comment_does_not_hide_code(self):
        self.assertEqual(findings("/- /- admit -/ -/ theorem x : False := by admit"),
                         [(1, "admit")])


if __name__ == "__main__":
    unittest.main()
