"""Tests for the fast shared Q3 source scanner."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts import q3_sensor_scan


class SourceScannerTests(unittest.TestCase):
    def test_sorry_scan_rejects_comments_strings_and_excluded_dirs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            (q3 / "Clean").mkdir(parents=True)
            (q3 / "Live").mkdir()
            (q3 / "Clean" / "Old.lean").write_text("theorem x : True := by sorry\n")
            (q3 / "Live" / "A.lean").write_text(
                '/- sorry -/\ndef note := "sorry"\ntheorem live : True := by sorry\n',
                encoding="utf-8",
            )
            rows = q3_sensor_scan.scan_sorry_sites(q3)
            self.assertEqual(rows, [{"file": "Q3/Live/A.lean", "lines": [3], "count": 1}])

    def test_import_closure_uses_only_internal_live_modules(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            q3.mkdir()
            (q3 / "Root.lean").write_text("import Q3.Middle Mathlib\nnamespace X\n")
            (q3 / "Middle.lean").write_text("import Q3.Leaf\n")
            (q3 / "Leaf.lean").write_text("theorem ok : True := by trivial\n")
            graph, unresolved = q3_sensor_scan.scan_import_graph(q3)
            self.assertEqual(unresolved, [])
            self.assertEqual(
                q3_sensor_scan.dependency_closure(graph, "Q3/Root.lean"),
                {"Q3/Root.lean": 0, "Q3/Middle.lean": 1, "Q3/Leaf.lean": 2},
            )

    def test_import_of_excluded_module_is_reported_not_fabricated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            (q3 / "Clean").mkdir(parents=True)
            (q3 / "Live.lean").write_text("import Q3.Clean.Old\n")
            (q3 / "Clean" / "Old.lean").write_text("axiom old : True\n")
            graph, unresolved = q3_sensor_scan.scan_import_graph(q3)
            self.assertEqual(graph["Q3/Live.lean"]["dependencies"], [])
            self.assertEqual(unresolved[0]["status"], "EXCLUDED_TARGET")

    def test_import_scan_stops_at_header_and_masks_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            q3.mkdir()
            path = q3 / "Root.lean"
            path.write_text(
                "/- import Q3.Fake -/\n"
                "import Q3.Real Mathlib\n"
                "def payload := \"import Q3.StringFake\"\n"
                "import Q3.TooLate\n",
                encoding="utf-8",
            )
            self.assertEqual(q3_sensor_scan.read_import_modules(path), ["Q3.Real", "Mathlib"])

    def test_dependency_aware_plan_protects_roots_and_allowlist(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            prime = q3 / "Proofs" / "PrimeCert"
            prime.mkdir(parents=True)
            (q3 / "Root.lean").write_text("import Q3.Proofs.PrimeCert.Required\n")
            (prime / "Required.lean").write_text(
                "theorem required : True := by sorry\n" + "-- generated\n" * 20
            )
            (prime / "Allow.lean").write_text(
                "import Q3.Proofs.PrimeCert.AllowDependency\n"
                "theorem allow : True := by sorry\n" + "-- generated\n" * 20
            )
            (prime / "AllowDependency.lean").write_text(
                "theorem supplier : True := by trivial\n" + "-- generated\n" * 20
            )
            (prime / "Museum.lean").write_text(
                "theorem museum : True := by sorry\n" + "-- generated\n" * 20
            )
            graph, _unresolved = q3_sensor_scan.scan_import_graph(q3)
            plan = q3_sensor_scan.build_content_scan_plan(
                q3,
                graph,
                root_entries=["Q3/Root.lean"],
                allowlist_entries=["Q3/Proofs/PrimeCert/Allow.lean"],
                threshold_bytes=100,
            )
            self.assertIn("Q3/Proofs/PrimeCert/Required.lean", plan.content_scanned_file_ids)
            self.assertIn("Q3/Proofs/PrimeCert/Allow.lean", plan.content_scanned_file_ids)
            self.assertIn(
                "Q3/Proofs/PrimeCert/AllowDependency.lean",
                plan.content_scanned_file_ids,
            )
            self.assertEqual(
                plan.skipped_generated_file_ids,
                frozenset({"Q3/Proofs/PrimeCert/Museum.lean"}),
            )
            rows = q3_sensor_scan.scan_sorry_sites(q3, plan.content_scanned_file_ids)
            self.assertEqual(
                {str(row["file"]) for row in rows},
                {
                    "Q3/Proofs/PrimeCert/Allow.lean",
                    "Q3/Proofs/PrimeCert/Required.lean",
                },
            )

    def test_missing_allowlist_entry_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            q3.mkdir()
            (q3 / "Root.lean").write_text("theorem ok : True := by trivial\n")
            graph, _unresolved = q3_sensor_scan.scan_import_graph(q3)
            with self.assertRaisesRegex(ValueError, "allowlist entry missing"):
                q3_sensor_scan.build_content_scan_plan(
                    q3,
                    graph,
                    root_entries=["Q3/Root.lean"],
                    allowlist_entries=["Q3/Missing.lean"],
                    threshold_bytes=100,
                )


if __name__ == "__main__":
    unittest.main()
