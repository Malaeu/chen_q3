from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import constructor as cp


class CertifiedPolynomialTests(unittest.TestCase):
    def test_contract_candidate_and_exact_optimality(self):
        report = cp.build_report()
        self.assertEqual(report["contract"], cp.CONTRACT)
        candidate = report["candidate"]
        self.assertEqual(candidate["coefficients"], {"a": "1", "b": "-3/4", "c": "1/4"})
        self.assertEqual(candidate["verification"]["status"], "VERIFIED")
        self.assertTrue(candidate["verification"]["factorization_verified"])
        self.assertEqual(candidate["verification"]["bernstein_coefficients"], ["1/4", "0"])
        self.assertEqual(candidate["verification"]["objective"], "8/5")
        self.assertTrue(candidate["verification"]["optimality"]["candidate_is_optimal"])

    def test_bad_candidate_has_exact_supplied_counterexample(self):
        result = cp.verify_coefficients(
            1, "-19/25", "13/50", counterexample_x="49/50")
        self.assertEqual(result["status"], "REFUTED")
        self.assertEqual(result["counterexample"], {
            "x": "49/50", "gap_p_minus_target": "-288328887/1531562500000"})

    def test_family_certificates_and_boundary(self):
        impossible, cannot = cp.build_report()["families"]
        self.assertEqual(impossible["status"], "INFEASIBLE")
        self.assertEqual(impossible["certificate"]["uniform_x"], "49/50")
        self.assertEqual(impossible["certificate"]["gap_at_lower"], "-288328887/1531562500000")
        self.assertEqual(cannot["status"], "CANNOT_IMPROVE")
        self.assertEqual(cannot["certificate"]["objective_lower_bound"], "121/75")
        self.assertEqual(cp.verify_coefficients(1, "-3/4", "1/4")["status"], "VERIFIED")
        crossing = cp.certify_family(0, "1/2", name="crosses_boundary")
        self.assertEqual(crossing["status"], "UNRESOLVED")

    def test_narrow_infeasible_interval_needs_a_valid_witness(self):
        lower, upper = Fraction(251, 1000), Fraction(3, 10)
        wrong_fixed_point = cp.certify_family(
            lower, upper, name="narrow", counterexample_x=Fraction(49, 50))
        self.assertEqual(wrong_fixed_point["status"], "UNRESOLVED")
        certified = cp.certify_family(lower, upper, name="narrow")
        self.assertEqual(certified["status"], "INFEASIBLE")
        witness = Fraction(certified["certificate"]["uniform_x"])
        self.assertLess(cp._gap(1, -Fraction(1, 2) - lower, lower, witness), 0)

    def test_invalid_contacts_never_claim_the_upper_bound(self):
        result = cp.verify_coefficients(2, -2, "1/2")
        self.assertEqual(result["status"], "REFUTED")
        self.assertFalse(result["contacts"]["valid"])
        self.assertIsNone(result["upper_bound"])

    def test_cli_writes_exclusive_json(self):
        script = Path(cp.__file__).resolve()
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "report.json"
            run = subprocess.run(
                [sys.executable, str(script), "--output", str(output)],
                check=False, capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            data = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(data["candidate"]["verification"]["status"], "VERIFIED")
            second = subprocess.run(
                [sys.executable, str(script), "--output", str(output)],
                check=False, capture_output=True, text=True)
            self.assertNotEqual(second.returncode, 0)
            self.assertIn("refusing to overwrite", second.stderr)


if __name__ == "__main__":
    unittest.main()
