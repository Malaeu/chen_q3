"""Tests for evidence-only numeric diagnostics."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

from scripts import numeric_sanity_check


class NumericSensorTests(unittest.TestCase):
    def test_empty_config_is_zero_coverage_not_pass(self) -> None:
        report = numeric_sanity_check.run_config({}, generated_at="fixed")
        self.assertEqual(report["coverage_status"], "EMPTY_CONFIG")
        self.assertEqual(report["summary"], {
            "configured": 0, "PASS": 0, "FAIL": 0, "TIMEOUT": 0,
        })

    def test_fail_is_recorded_as_evidence_without_proof_authority(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            report = numeric_sanity_check.run_config(
                {"checks": [{
                    "id": "DIAGNOSTIC",
                    "command": [sys.executable, "-c", "raise SystemExit(3)"],
                    "expect_exit_code": 0,
                }]},
                root=root,
                generated_at="fixed",
            )
            result = report["checks"][0]
            self.assertEqual(result["status"], "FAIL")
            self.assertEqual(result["evidence_class"], "NUMERIC_EVIDENCE_ONLY")
            self.assertTrue(report["boundary"]["not_taint_input"])

    def test_duplicate_ids_fail_closed(self) -> None:
        item = {"id": "DUP", "command": [sys.executable, "-c", "pass"]}
        with self.assertRaisesRegex(ValueError, "duplicate"):
            numeric_sanity_check.run_config({"checks": [item, item]})


if __name__ == "__main__":
    unittest.main()
