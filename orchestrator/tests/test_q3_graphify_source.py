"""Regression tests for the tracked Q3 Graphify source adapter."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts import q3_graphify_source


class Q3GraphifySourceTests(unittest.TestCase):
    def _repo(self, directory: Path) -> None:
        subprocess.run(["git", "init", "-q"], cwd=directory, check=True)
        subprocess.run(["git", "config", "user.name", "Graphify Test"], cwd=directory, check=True)
        subprocess.run(
            ["git", "config", "user.email", "graphify-test@example.invalid"],
            cwd=directory,
            check=True,
        )

    def _write(self, root: Path, relative: str, content: str) -> Path:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def _commit(self, root: Path) -> None:
        subprocess.run(["git", "add", "-A"], cwd=root, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=root, check=True)

    def test_lean_imports_resolve_by_module_path_and_external_remains_unresolved(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._repo(root)
            self._write(
                root,
                "q3.lean.aristotle/Q3/Main.lean",
                "/- import Q3.FalseOuter /- import Q3.FalseNested -/ -/\n"
                "import Q3.Model Mathlib.Data.Nat.Prime\n"
                'def note := "import Q3.FalseString"\n'
                "-- import Q3.FalseLine\n",
            )
            model = self._write(root, "q3.lean.aristotle/Q3/Model.lean", "namespace Q3\nend Q3\n")
            self._write(root, "q3.lean.aristotle/Other/Model.lean", "namespace Other\nend Other\n")
            self._write(
                root,
                "q3.lean.aristotle/Archive/Old.lean",
                "namespace Archive\nend Archive\n",
            )
            self._write(
                root,
                "q3.lean.aristotle/.lake/packages/mathlib/Mathlib/Data/Nat/Prime.lean",
                "namespace Mathlib\nend Mathlib\n",
            )
            self._commit(root)
            model.write_text("namespace Q3\n-- changed after commit\nend Q3\n", encoding="utf-8")

            graph, coverage = q3_graphify_source.build_graph(root)

            main_links = [
                edge for edge in graph["links"]
                if edge["source"] == "q3.lean.aristotle/Q3/Main.lean"
            ]
            local_import = next(
                edge for edge in main_links
                if edge["target"] == "q3.lean.aristotle/Q3/Model.lean"
            )
            self.assertEqual(local_import["relation"], "imports_module")
            self.assertEqual(local_import["module"], "Q3.Model")
            self.assertNotIn("q3.lean.aristotle/Other/Model.lean", {
                edge["target"] for edge in main_links
            })
            unresolved_targets = {
                row["target"] for row in coverage["unresolved_references"]
            }
            self.assertNotIn("Q3.FalseOuter", unresolved_targets)
            self.assertNotIn("Q3.FalseNested", unresolved_targets)
            self.assertNotIn("Q3.FalseString", unresolved_targets)
            self.assertNotIn("Q3.FalseLine", unresolved_targets)
            external = next(
                node for node in graph["nodes"]
                if node["id"] == "external-module::Mathlib.Data.Nat.Prime"
            )
            self.assertEqual(external["resolution"], "external_unresolved")
            self.assertTrue(external["external"])
            self.assertEqual(graph["graph"]["boundary"], q3_graphify_source.BOUNDARY)
            self.assertIn("q3.lean.aristotle/Archive/Old.lean", {
                node["id"] for node in graph["nodes"]
            })
            historical = next(
                node for node in graph["nodes"]
                if node["id"] == "q3.lean.aristotle/Archive/Old.lean"
            )
            self.assertTrue(historical["historical"])
            self.assertIn("q3.lean.aristotle/Q3/Model.lean", graph["graph"]["dirty_tracked_paths"])
            model_node = next(
                node for node in graph["nodes"]
                if node["id"] == str(model.relative_to(root))
            )
            self.assertTrue(model_node["dirty"])
            self.assertGreaterEqual(coverage["counts"]["sources_by_type"]["lean"], 4)

    def test_tex_includes_try_relative_context_then_document_roots(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._repo(root)
            self._write(
                root,
                "full/main.tex",
                "\\input{sections/start}\n\\include{shared}\n"
                "\\input{\\sectionPath}\n% \\input{missing}\n",
            )
            self._write(root, "full/sections/start.tex", "\\input{shared}\n")
            self._write(root, "full/shared.tex", "Full shared section\n")
            self._write(root, "full/sections/Notation/qstar_contract.tex", "Full qstar contract\n")
            self._write(
                root,
                "full/sections/A3/main.tex",
                "\\input{sections/Notation/qstar_contract}\n",
            )
            self._write(
                root,
                "full/sections/A3/calibration.tex",
                "\\input{sections/Notation/qstar_contract}\n",
            )
            self._write(root, "paper_weil/main.tex", "\\input{sections/start}\n")
            self._write(root, "paper_weil/sections/start.tex", "\\input{shared}\n")
            self._write(root, "paper_weil/shared.tex", "Paper shared section\n")
            self._commit(root)

            graph, coverage = q3_graphify_source.build_graph(root)

            edges = [edge for edge in graph["links"] if edge["relation"] == "includes_tex"]
            self.assertIn(
                ("full/main.tex", "full/sections/start.tex"),
                {(edge["source"], edge["target"]) for edge in edges},
            )
            root_fallback = next(
                edge for edge in edges
                if edge["source"] == "full/sections/start.tex"
            )
            self.assertEqual(root_fallback["target"], "full/shared.tex")
            self.assertEqual(root_fallback["resolution_base"], "document_root")
            self.assertIn(
                ("paper_weil/main.tex", "paper_weil/sections/start.tex"),
                {(edge["source"], edge["target"]) for edge in edges},
            )
            paper_root_fallback = next(
                edge for edge in edges
                if edge["source"] == "paper_weil/sections/start.tex"
            )
            self.assertEqual(paper_root_fallback["target"], "paper_weil/shared.tex")
            self.assertEqual(paper_root_fallback["resolution_base"], "document_root")
            qstar_fallback = next(
                edge for edge in edges
                if edge["source"] == "full/sections/A3/calibration.tex"
            )
            self.assertEqual(
                qstar_fallback["target"],
                "full/sections/Notation/qstar_contract.tex",
            )
            self.assertEqual(qstar_fallback["resolution_base"], "document_root")
            self.assertFalse(any(
                row["target"] == "missing" for row in coverage["unresolved_references"]
            ))
            macro = next(
                row for row in coverage["unresolved_references"]
                if row["target"] == "\\sectionPath"
            )
            self.assertEqual(macro["status"], "macro_computed_path")
            self.assertGreaterEqual(coverage["counts"]["sources_by_type"]["tex"], 9)
            self.assertEqual(coverage["graphify_projection"]["input_edge_records"], len(edges))
            for edge in edges:
                self.assertEqual(edge["source_file"], edge["source"])
                self.assertEqual(edge["confidence"], "EXTRACTED")
                self.assertEqual(edge["confidence_score"], 1.0)
                self.assertEqual(edge["_origin"], "literal_reference_scan")

    def test_markdown_relative_absolute_line_anchor_and_broken_links(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._repo(root)
            self._write(root, "q3.lean.aristotle/Q3/Model.lean", "namespace Q3\nend Q3\n")
            self._write(root, "q3.lean.aristotle/Q3/Main.lean", "import Q3.Model\n")
            self._write(
                root,
                "docs/references.md",
                "[relative](../q3.lean.aristotle/Q3/Model.lean:17#L21)\n"
                "[query](../q3.lean.aristotle/Q3/Model.lean?plain=1#L24)\n"
                "[absolute](/q3.lean.aristotle/Q3/Main.lean#L8)\n"
                "[broken](missing.md#L9)\n"
                "[web](https://example.invalid/page)\n"
                "`[inline code](ignored.md)`\n"
                "    [indented code](also-ignored.md) and [x](1+u)\n",
            )
            self._commit(root)

            graph, coverage = q3_graphify_source.build_graph(root)

            links = [edge for edge in graph["links"] if edge["relation"] == "links_document"]
            self.assertIn(
                ("docs/references.md", "q3.lean.aristotle/Q3/Model.lean"),
                {(edge["source"], edge["target"]) for edge in links},
            )
            relative = next(edge for edge in links if edge["target"].endswith("Model.lean"))
            self.assertEqual(relative["target_line"], 17)
            self.assertEqual(relative["line_anchor"], "L21")
            query_link = next(
                edge for edge in links
                if edge["reference"].endswith("?plain=1#L24")
            )
            self.assertEqual(query_link["target_line"], 24)
            absolute = next(edge for edge in links if edge["target"].endswith("Main.lean"))
            self.assertEqual(absolute["target_line"], 8)
            unresolved = next(
                row for row in coverage["unresolved_references"]
                if row["target"] == "missing.md#L9"
            )
            self.assertEqual(unresolved["status"], "broken_local_reference")
            self.assertEqual(unresolved["line"], 4)
            self.assertEqual(unresolved["target_line"], 9)
            self.assertFalse(any(
                "example.invalid" in str(row) for row in coverage["unresolved_references"]
            ))
            self.assertFalse(any(
                row["target"] in {"ignored.md", "also-ignored.md", "1+u"}
                for row in coverage["unresolved_references"]
            ))
            self.assertEqual(coverage["counts"]["sources_by_type"]["markdown"], 1)
            projection = coverage["graphify_projection"]
            self.assertEqual(projection["input_edge_records"], len(graph["links"]))
            self.assertGreater(projection["collapsed_parallel_edge_records"], 0)
            for edge in graph["links"]:
                self.assertEqual(edge["source_file"], edge["source"])
                self.assertEqual(edge["confidence"], "EXTRACTED")

    def test_output_refuses_to_replace_existing_graphify_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            graph_path = out / "graph.json"
            graph_path.write_text("existing", encoding="utf-8")

            with self.assertRaisesRegex(
                q3_graphify_source.GraphifySourceError,
                "refusing to replace",
            ):
                q3_graphify_source.write_outputs(out, {}, {})

            self.assertEqual(graph_path.read_text(encoding="utf-8"), "existing")
            self.assertFalse((out / "coverage.json").exists())

    def test_unavailable_sources_are_coverage_not_parser_errors(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._repo(root)
            missing = self._write(root, "docs/missing.md", "will be removed after commit\n")
            bad_encoding = root / "docs/bad.md"
            bad_encoding.parent.mkdir(parents=True, exist_ok=True)
            bad_encoding.write_bytes(b"\xffnot utf-8\n")
            link = root / "docs/link.md"
            link.symlink_to("missing-target.md")
            self._commit(root)
            missing.unlink()

            _graph, coverage = q3_graphify_source.build_graph(root)

            self.assertEqual(coverage["counts"]["missing_sources"], 1)
            self.assertEqual(coverage["counts"]["symlink_sources"], 1)
            self.assertEqual(coverage["counts"]["unavailable_sources"], 2)
            self.assertEqual(coverage["counts"]["parser_errors"], 1)
            self.assertEqual(coverage["parser_errors"][0]["path"], "docs/bad.md")


if __name__ == "__main__":
    unittest.main()
