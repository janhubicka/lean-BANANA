import unittest

from check_manuscript_linked_declarations import check_requirements


class ManuscriptDeclarationTests(unittest.TestCase):
    def setUp(self):
        self.req = [{"module": "BANANA.Example", "name": "foo",
                     "path": "BANANA/Example.lean", "blob": "blob"},
                    {"module": "BANANA.Other", "name": "bar",
                     "path": "BANANA/Other.lean", "blob": "dep"}]
        self.inv = {"BANANA.Example": {"A.foo"}, "BANANA.Other": {"S.bar"}}
        self.root = {"BANANA/Example.lean": "blob", "BANANA/Other.lean": "dep"}

    def check(self):
        return check_requirements(self.req, self.inv, self.root)

    def test_complete(self):
        self.assertEqual(self.check(), (2, 2))

    def test_missing(self):
        self.inv["BANANA.Example"].clear()
        with self.assertRaisesRegex(ValueError, "expected one"):
            self.check()

    def test_ambiguous(self):
        self.inv["BANANA.Example"].add("B.foo")
        with self.assertRaisesRegex(ValueError, "expected one"):
            self.check()

    def test_changed_source(self):
        self.root["BANANA/Example.lean"] = "different"
        with self.assertRaisesRegex(ValueError, "linked source changed"):
            self.check()

    def test_dependency_changed(self):
        del self.root["BANANA/Other.lean"]
        with self.assertRaisesRegex(ValueError, "linked source changed"):
            self.check()

    def test_external_project_module(self):
        self.req[1].update(module="SuccessorTree.Example",
                           path="SuccessorTree/Example.lean")
        with self.assertRaisesRegex(ValueError, "unexpected external"):
            self.check()

    def test_duplicate(self):
        self.req.append(self.req[0])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.check()


if __name__ == "__main__":
    unittest.main()
