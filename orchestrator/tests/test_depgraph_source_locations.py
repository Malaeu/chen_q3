import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("depgraph", ROOT / "docs/cartographer/depgraph.py")
depgraph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(depgraph)


class SourceLocationTests(unittest.TestCase):
    def test_multiline_comment_preserves_declaration_line(self):
        raw = "/- comment\nmentions helper\n-/\n\ntheorem target : True := by\n  exact helper\n\ntheorem helper : True := by trivial\n"
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            path = Path(directory) / "Test.lean"
            path.write_text(raw)
            decls, bodies = depgraph.collect(Path(directory))
        self.assertEqual(decls["target"][1], 5)
        self.assertEqual(decls["helper"][1], 8)
        self.assertIn("helper", depgraph.build_edges(decls, bodies)["target"])

    def test_long_line_comment_preserves_offsets(self):
        raw = "-- " + "x" * 200 + "\ntheorem alpha : True := by trivial\ntheorem bravo : True := by trivial\n"
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            (Path(directory) / "Test.lean").write_text(raw)
            decls, _ = depgraph.collect(Path(directory))
        self.assertEqual(decls["alpha"][1], 2)
        self.assertEqual(decls["bravo"][1], 3)

    def test_comment_only_mention_does_not_create_edge(self):
        text = "theorem target : True := by trivial /- helper -/"
        self.assertNotIn("helper", depgraph.strip_comments(text))

if __name__ == "__main__":
    unittest.main()
