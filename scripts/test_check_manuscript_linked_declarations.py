import unittest

from check_manuscript_linked_declarations import check_requirements


class ManuscriptDeclarationTests(unittest.TestCase):
    def setUp(self):
        self.req = [{"module": "BANANA.Example", "name": "foo",
                     "path": "BANANA/Example.lean", "blob": "blob"},
                    {"module": "SuccessorTree.Example", "name": "bar",
                     "path": "SuccessorTree/Example.lean", "blob": "dep"}]
        self.inv = {"BANANA.Example": {"A.foo"}, "SuccessorTree.Example": {"S.bar"}}
        self.root = {"BANANA/Example.lean": "blob"}
        self.dep = {"SuccessorTree/Example.lean": "dep"}

    def check(self):
        return check_requirements(self.req, self.inv, self.root, self.dep)

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
        self.dep.clear()
        with self.assertRaisesRegex(ValueError, "linked source changed"):
            self.check()

    def test_duplicate(self):
        self.req.append(self.req[0])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.check()


if __name__ == "__main__":
    unittest.main()
