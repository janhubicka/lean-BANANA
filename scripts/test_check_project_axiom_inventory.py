import unittest

from check_project_axiom_inventory import check_inventory


GOOD = ("PROJECT_AXIOMS\tBANANA.Example\tExample.foo\tpropext,Quot.sound\n"
        "PROJECT_AXIOMS\tSuccessorTree.Example\tExample.bar\t\n"
        "PROJECT_AXIOMS_DONE\t2\t0\t2\n")


class ProjectInventoryTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(check_inventory(GOOD)["BANANA.Example"], {"Example.foo"})

    def test_missing_or_duplicate_completion(self):
        with self.assertRaisesRegex(ValueError, "completion"):
            check_inventory(GOOD.split("PROJECT_AXIOMS_DONE")[0])
        with self.assertRaisesRegex(ValueError, "completion"):
            check_inventory(GOOD + "PROJECT_AXIOMS_DONE\t2\t0\t2\n")

    def test_duplicate_declaration(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            check_inventory(GOOD.replace("Example.bar", "Example.foo"))

    def test_forbidden_axiom(self):
        with self.assertRaisesRegex(ValueError, "forbidden"):
            check_inventory(GOOD.replace("propext", "sorryAx"))

    def test_wrong_count(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            check_inventory(GOOD.replace("DONE\t2\t0\t2", "DONE\t3\t0\t3"))


if __name__ == "__main__":
    unittest.main()
