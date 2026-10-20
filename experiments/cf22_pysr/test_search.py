"""Negative controls for acceptance only; these data never train PySR."""
import copy
from decimal import Decimal
import unittest

from flint import arb, ctx
import search


def row(identifier, scale, split, qlo="0", qhi="1"):
    return {
        "id": identifier, "U": str(scale), "split": split,
        "features": {"logU": "2", "r": "1.12", "ell": "1.11"},
        "feature_intervals": {
            "logU": {"lower": "2", "upper": "2"},
            "r": {"lower": "1.12", "upper": "1.12"},
            "ell": {"lower": "1.11", "upper": "1.11"},
        },
        "q_lower": qlo, "q_upper": qhi,
    }


class AcceptanceControls(unittest.TestCase):
    def setUp(self):
        ctx.prec = 256

    def test_delayed_spike_refutes_previously_fitting_constant(self):
        data = {"provenance": "SYNTHETIC_NEGATIVE_CONTROL_ONLY", "rows": [
            row("train", 8, "train", "0.8", "0.9"),
            row("spike", 64, "test", "10", "11"),
        ]}
        rows, _ = search.validate_dataset(data)
        expression, error = search._sympy_parse("1")
        self.assertIsNone(error)
        self.assertEqual(search.evaluate_candidate_on_row(expression, rows[0])["status"], "ACCEPT")
        self.assertEqual(search.evaluate_candidate_on_row(expression, rows[1])["status"], "REFUTE")

    def test_overlap_is_unresolved_not_zero(self):
        status, _, _ = search.classify_interval(arb("0 +/- 1"), Decimal("-0.5"), Decimal("0.5"))
        self.assertEqual(status, "UNRESOLVED")

    def test_equal_scale_spellings_cannot_cross_split(self):
        data = {"provenance": "SYNTHETIC_NEGATIVE_CONTROL_ONLY", "rows": [
            row("a", "8", "train"), row("b", "8.0", "test")]}
        with self.assertRaisesRegex(ValueError, "share U"):
            search.validate_dataset(data)

    def test_cancelled_denominator_still_invalid(self):
        expression, error = search._sympy_parse("logU / logU")
        self.assertIsNone(error)
        with self.assertRaises(ZeroDivisionError):
            search.evaluate_sympy_expression(expression, {
                "logU": arb("0 +/- 1"), "r": arb(1), "ell": arb(1)})

    def test_missing_source_interval_rejected(self):
        data = {"provenance": "SYNTHETIC_NEGATIVE_CONTROL_ONLY", "rows": [
            row("a", 8, "train"), row("b", 64, "test")]}
        bad = copy.deepcopy(data)
        del bad["rows"][1]["feature_intervals"]
        with self.assertRaises(ValueError):
            search.validate_dataset(bad)

    def test_decimal_candidate_constants_have_exact_declared_meaning(self):
        from flint import fmpq
        import sympy
        expression, error = search._sympy_parse("0.1")
        self.assertIsNone(error)
        self.assertEqual(expression, sympy.Rational(1, 10))
        result = search.evaluate_sympy_expression(expression, {})
        self.assertTrue(result.contains(fmpq(1, 10)))


if __name__ == "__main__":
    unittest.main()
