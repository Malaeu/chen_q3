"""Semantic plants for source-hole propagation."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts import build_taint_graph


class TaintSensorTests(unittest.TestCase):
    def test_sorry_propagates_but_numeric_fail_is_evidence_only(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            q3.mkdir()
            (q3 / "Root.lean").write_text("import Q3.Leaf\n")
            (q3 / "Leaf.lean").write_text("theorem hole : True := by sorry\n")
            sorry = {
                "files": [{"file": "Q3/Leaf.lean", "lines": [1], "count": 1}],
                "root_closures": [{
                    "root_id": "ROOT",
                    "entry_file": "Q3/Root.lean",
                    "files": [
                        {"file": "Q3/Root.lean", "depth": 0},
                        {"file": "Q3/Leaf.lean", "depth": 1},
                    ],
                }],
            }
            numeric = {"checks": [{"id": "Q3/Root.lean", "status": "FAIL"}]}
            taint, sources = build_taint_graph.build_payloads(
                q3_dir=q3,
                sorry_data=sorry,
                numeric_data=numeric,
                generated_at="2026-08-05T22:30:00+00:00",
            )
            by_id = {node["id"]: node for node in taint["nodes"]}
            self.assertEqual(by_id["Q3/Leaf.lean"]["propagation_status"], "DIRECT_SORRY")
            self.assertEqual(by_id["Q3/Root.lean"]["propagation_status"], "TRANSITIVE_TAINT")
            self.assertEqual(by_id["Q3/Root.lean"]["numeric_check"], "FAIL")
            self.assertFalse(by_id["Q3/Root.lean"]["is_doomed"])
            self.assertEqual(sources["roots_by_file"]["Q3/Root.lean"], ["Q3/Leaf.lean"])

    def test_skipped_generated_nonroot_is_explicit_unknown_not_green(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            q3.mkdir()
            (q3 / "Root.lean").write_text("theorem root : True := by trivial\n")
            (q3 / "Museum.lean").write_text("theorem old : True := by sorry\n")
            sorry = {
                "files": [],
                "scope": {"content_scan": {"skipped_file_ids": ["Q3/Museum.lean"]}},
                "root_closures": [{
                    "root_id": "ROOT",
                    "entry_file": "Q3/Root.lean",
                    "files": [{"file": "Q3/Root.lean", "depth": 0}],
                }],
            }
            taint, sources = build_taint_graph.build_payloads(
                q3_dir=q3,
                sorry_data=sorry,
                numeric_data={"checks": []},
                generated_at="2026-08-06T00:00:00+00:00",
            )
            by_id = {node["id"]: node for node in taint["nodes"]}
            self.assertEqual(
                by_id["Q3/Museum.lean"]["propagation_status"],
                "CONTENT_SCAN_SKIPPED_GENERATED_NONROOT",
            )
            self.assertEqual(
                by_id["Q3/Museum.lean"]["content_scan_status"],
                "SKIPPED_GENERATED_NONROOT",
            )
            self.assertEqual(by_id["Q3/Root.lean"]["propagation_status"], "NO_OBSERVED_ISSUE")
            self.assertEqual(sources["content_scan_skipped"], ["Q3/Museum.lean"])

    def test_skipping_a_root_dependency_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q3 = Path(tmp) / "Q3"
            q3.mkdir()
            (q3 / "Root.lean").write_text("import Q3.Required\n")
            (q3 / "Required.lean").write_text("theorem hole : True := by sorry\n")
            sorry = {
                "files": [],
                "scope": {"content_scan": {"skipped_file_ids": ["Q3/Required.lean"]}},
                "root_closures": [{
                    "root_id": "ROOT",
                    "entry_file": "Q3/Root.lean",
                    "files": [
                        {"file": "Q3/Root.lean", "depth": 0},
                        {"file": "Q3/Required.lean", "depth": 1},
                    ],
                }],
            }
            with self.assertRaisesRegex(ValueError, "skipped live root dependencies"):
                build_taint_graph.build_payloads(
                    q3_dir=q3,
                    sorry_data=sorry,
                    numeric_data={"checks": []},
                    generated_at="2026-08-06T00:00:00+00:00",
                )


if __name__ == "__main__":
    unittest.main()
