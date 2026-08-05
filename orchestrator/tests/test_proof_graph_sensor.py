"""Plants for the compact root-to-axiom projection."""

from __future__ import annotations

import unittest

from scripts import build_proof_graph


class ProofGraphSensorTests(unittest.TestCase):
    def test_two_roots_and_project_axiom_status_are_preserved(self) -> None:
        dependency_data = {
            "roots": [
                {"id": "ROOT_A", "deps": [
                    {
                        "name": "propext",
                        "classification": "STANDARD_LEAN_AXIOM",
                        "mapping_status": "STANDARD",
                        "file": None,
                    },
                    {
                        "name": "Q3.ax",
                        "classification": "PROJECT_AXIOM",
                        "mapping_status": "FOUND",
                        "file": "Q3/A.lean",
                    },
                ]},
                {"id": "ROOT_B", "deps": [{
                    "name": "Q3.ax",
                    "classification": "PROJECT_AXIOM",
                    "mapping_status": "FOUND",
                    "file": "Q3/A.lean",
                }]},
            ],
        }
        taint_data = {"nodes": [{
            "id": "Q3/A.lean",
            "root_ids": ["ROOT_A", "ROOT_B"],
            "direct_status": "CLEAR",
            "propagation_status": "NO_OBSERVED_ISSUE",
            "integrity_status": "NO_OBSERVED_ISSUE",
            "numeric_check": "FAIL",
        }]}
        data = build_proof_graph.build_payload(
            dependency_data, taint_data, {}, generated_at="fixed",
        )
        self.assertEqual(len(data["roots"]), 2)
        self.assertEqual(data["roots"][0]["status"], "PROJECT_AXIOMS_PRESENT")
        self.assertEqual(data["roots"][1]["status"], "PROJECT_AXIOMS_PRESENT")
        self.assertFalse(data["roots"][1]["nodes"][0]["is_doomed"])
        self.assertEqual(data["roots"][1]["nodes"][0]["numeric_check"], "FAIL")


if __name__ == "__main__":
    unittest.main()
