from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit


def _column(index: int, generator: tuple[int, int]) -> dict:
    return {
        "index": index,
        "mu": -1,
        "ideal": {
            "norm": 7,
            "factors": [{
                "prime_generator": list(generator),
                "prime_ideal_norm": 7,
                "exponent": 1,
            }],
        },
    }


def _pair(i: int, j: int, lower: str, upper: str, *, group: str = "cross") -> dict:
    return {
        "i": i,
        "j": j,
        "group": group,
        "left_column": _column(i, (1, 2)),
        "right_column": _column(j, (-1, 2)),
        "shared_zero_mask_gcd": {"norm": 1, "factors": []},
        "primitive_quotient_conductor": {"norm": 49, "factors": []},
        "full_period_lcm_norm_Q": 49,
        "A_exact": 5,
        "A_P_exact": 4,
        "C_signed_contribution": {"lower": lower, "upper": upper},
    }


def _row(*pairs: dict) -> dict:
    return {
        "id": "toy",
        "configuration": {
            "U": 48,
            "P": "13",
            "r": "113/100",
            "ell": "113/100",
            "orientation": 1,
        },
        "pairs": list(pairs),
    }


class FeatureAuditTests(unittest.TestCase):
    def test_pair_features_are_canonical_under_swap(self) -> None:
        row = _row(_pair(1, 2, "1", "1"))
        pair = row["pairs"][0]
        swapped = dict(pair)
        swapped["left_column"], swapped["right_column"] = pair["right_column"], pair["left_column"]
        swapped["i"], swapped["j"] = pair["j"], pair["i"]
        self.assertEqual(
            audit.feature_key(row, pair, strong=True),
            audit.feature_key(row, swapped, strong=True),
        )

    def test_overlapping_target_intervals_are_not_a_collision(self) -> None:
        result = audit._analyze_profile(
            [_row(_pair(1, 2, "1", "2"), _pair(3, 4, "3/2", "5/2"))],
            strong=False,
        )
        self.assertEqual(result["repeated_feature_groups"], 1)
        self.assertEqual(result["disjoint_target_groups"], 0)
        self.assertTrue(result["no_certified_collision_on_panel"])
        self.assertIsNone(result["largest_disjoint_target_gap"])

    def test_disjoint_target_collision_keeps_original_generators(self) -> None:
        result = audit._analyze_profile(
            [_row(_pair(1, 2, "1", "11/10"), _pair(3, 4, "2", "21/10"))],
            strong=True,
        )
        self.assertEqual(result["disjoint_target_groups"], 1)
        witness = result["largest_disjoint_target_gap"]
        self.assertEqual(witness["separation_exact"], "9/10")
        self.assertEqual(
            witness["upper_target_pair"]["left_ideal_with_generators"]["factors"][0]["prime_generator"],
            [1, 2],
        )
        self.assertEqual(
            witness["lower_target_pair"]["right_ideal_with_generators"]["factors"][0]["prime_generator"],
            [-1, 2],
        )

    def test_cross_sign_separation_is_reported(self) -> None:
        result = audit._analyze_profile(
            [_row(_pair(1, 2, "3/2", "8/5"), _pair(3, 4, "-3/5", "-1/2"))],
            strong=True,
        )
        witness = result["largest_cross_positive_negative_gap"]
        self.assertEqual(witness["separation_exact"], "2")
        self.assertEqual(witness["upper_target_pair"]["group"], "cross")
        self.assertEqual(witness["lower_target_pair"]["group"], "cross")

    def test_wrong_source_hash_is_rejected_before_reading_as_data(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "decomposition.json"
            path.write_text(json.dumps({}), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "source hash mismatch"):
                audit.load_and_audit(path)
        with self.assertRaisesRegex(ValueError, "pinned full-pair source hash"):
            audit.audit_payload({}, source_sha256="0" * 64)


if __name__ == "__main__":
    unittest.main()
