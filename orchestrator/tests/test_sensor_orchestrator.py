"""Cross-source invariants for the sensor refresh transaction."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from orchestrator import sensors


class SensorBundleTests(unittest.TestCase):
    def write(self, root: Path, name: str, value: dict) -> None:
        (root / name).write_text(json.dumps(value), encoding="utf-8")

    def test_root_identity_mismatch_fails_before_publish(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.write(root, "DEPS_TREE_MAIN.json", {"roots": [{"id": "A", "deps": []}]})
            self.write(root, "SORRY_FRONTIER.json", {
                "total_sorries": 0,
                "scope": {"included_files": 0},
                "root_closures": [{"root_id": "B"}],
            })
            self.write(root, "NUMERIC_CHECKS_REPORT.json", {
                "coverage_status": "EMPTY_CONFIG",
                "boundary": {"not_taint_input": True},
            })
            self.write(root, "TAINT_GRAPH.json", {
                "nodes": [], "root_status": [{"root_id": "A"}],
                "semantics": {"numeric_checks": "EVIDENCE_ONLY_NOT_PROPAGATED"},
            })
            self.write(root, "TAINT_SOURCES.json", {"roots_by_file": {}})
            self.write(root, "PROOF_GRAPH.json", {
                "roots": [{"id": "A"}], "boundary": {"not_proof_verdict": True},
            })
            self.write(root, "AUTOPSY_MAP.json", {
                "schema": "q3_autopsy_map.v1",
                "authority": "DERIVED_NONCANONICAL_OBSERVABILITY",
                "events": [], "walls": [], "namewatch_candidates": [],
            })
            with self.assertRaisesRegex(ValueError, "root identity mismatch"):
                sensors.validate_bundle(root)


if __name__ == "__main__":
    unittest.main()
