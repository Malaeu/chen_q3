"""Focused checks for the saved finite CF22 panel pruning tool."""
from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from flint import arb, ctx

import prune

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "experiments/cf22_pysr"


def load_data():
    return (
        json.loads((BASE / "nonunit/main.json").read_text()),
        json.loads((BASE / "nonunit/heldout.json").read_text()),
        json.loads((BASE / "correlation/summary.json").read_text()),
        json.loads((BASE / "nonunit/plan.json").read_text()),
        prune._sha256_file(BASE / "correlation/decomposition.json.gz"),
    )


class PanelPruningTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192

    def test_full_panel_reassembles_and_expected_boxes_are_refuted(self):
        report = prune.load_and_analyze(ROOT)
        self.assertEqual(report["status"], "PASS_FINITE_PANEL_ONLY")
        self.assertEqual(len(report["panel"]["rows"]), 20)
        self.assertTrue(report["panel"]["all_rows_use_saved_full_C"])
        self.assertTrue(report["panel"]["all_rows_reassemble_from_RR_plus_cross_plus_AA"])
        self.assertGreater(report["panel"]["mixed_cross_nonzero_rows"], 0)
        boxes = {box["name"]: box for box in report["coefficient_boxes"]}
        self.assertEqual(boxes["independent_P_alpha_le_1e-2_kappa_le_3e-3"]["witness"]["id"],
                         "U64_P13_o1")
        self.assertEqual(boxes["all_panel_alpha_le_1e-2_kappa_le_19e-3"]["witness"]["id"],
                         "U64_Pproduction_o1")
        self.assertEqual(boxes["negative_control_alpha_le_1e-1_kappa_le_1e-1"]["status"],
                         "NOT_REFUTED_ON_PANEL")

    def test_wrong_full_source_is_rejected(self):
        main, heldout, groups, plan, digest = load_data()
        main = copy.deepcopy(main)
        main["rows"][0]["full_C"]["lower"] = "1e100"
        with self.assertRaises((ArithmeticError, ValueError)):
            prune.analyze_data(main, heldout, groups, digest, plan)

    def test_omitted_cross_group_is_rejected(self):
        main, heldout, groups, plan, digest = load_data()
        groups = copy.deepcopy(groups)
        groups["rows"][0]["groups"].pop("cross")
        with self.assertRaises(ValueError):
            prune.analyze_data(main, heldout, groups, digest, plan)

    def test_group_sum_must_directly_overlap_full_source(self):
        group_row = {
            "groups": {
                "rough_rough": {"C_contribution": {"lower": "0", "upper": "0"}},
                "cross": {"C_contribution": {"lower": "0", "upper": "0"}},
                "affected_affected": {"C_contribution": {"lower": "0", "upper": "0"}},
            },
            "C_pair_sum": {"lower": "0", "upper": "2"},
            "saved_C": {"lower": "0", "upper": "2"},
            "reassembly_residual": {"lower": "-2", "upper": "0"},
        }
        with self.assertRaisesRegex(ArithmeticError, "directly overlap"):
            prune._group_checks(arb("2").union(arb("3")), group_row, "transitivity-control")

    def test_reversed_interval_is_rejected_before_hulling(self):
        with self.assertRaises(ValueError):
            prune._interval({"lower": "2", "upper": "1"}, "reversed")

    def test_box_helper_rejects_invalid_parameter_domains(self):
        row = {"id": "boundary", "configuration": {"U": 2, "P": 1}}
        prepared = {"boundary": {"C": arb(1), "PU": arb(1), "S": arb(1),
                                  "U": 2, "group_check": {}}}
        with self.assertRaises(ValueError):
            prune._box_check("negative", [row], prepared,
                             alpha_cap=prune.Fraction(-1, 10),
                             kappa_cap=prune.Fraction(1),
                             delta_lo=prune.Fraction(0),
                             delta_hi=prune.Fraction(1, 100))
        with self.assertRaises(ValueError):
            prune._box_check("reversed-delta", [row], prepared,
                             alpha_cap=prune.Fraction(0),
                             kappa_cap=prune.Fraction(1),
                             delta_lo=prune.Fraction(1, 100),
                             delta_hi=prune.Fraction(0))

    def test_box_exclusion_requires_strict_interval_separation(self):
        row = {"id": "boundary", "configuration": {"U": 2, "P": 1}}
        prepared = {"boundary": {"C": arb(1), "PU": arb(1), "S": arb(1),
                                  "U": 2, "group_check": {}}}
        result = prune._box_check("touching", [row], prepared,
                                  alpha_cap=prune.Fraction(0),
                                  kappa_cap=prune.Fraction(1),
                                  delta_lo=prune.Fraction(0),
                                  delta_hi=prune.Fraction(1, 100))
        self.assertEqual(result["status"], "NOT_REFUTED_ON_PANEL")
        self.assertIsNone(result["witness"])

    def test_threshold_for_fixed_row_is_monotone_in_delta(self):
        report = prune.load_and_analyze(ROOT)
        rows = report["subsets"]["all_20"]["necessary_thresholds"]["thresholds"]
        selected = [x for x in rows if x["alpha"] == "1/100"]
        ordered = sorted(selected, key=lambda x: prune.Fraction(x["delta"]))
        lower_bounds = [prune.Fraction(item["necessary_kappa_threshold_interval"]["lower"])
                        for item in ordered]
        self.assertEqual([item["delta"] for item in ordered], ["0", "1/200", "1/100"])
        self.assertLessEqual(lower_bounds[0], lower_bounds[1])
        self.assertLessEqual(lower_bounds[1], lower_bounds[2])


if __name__ == "__main__":
    unittest.main(verbosity=2)
