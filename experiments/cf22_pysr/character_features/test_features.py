from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import features


class ArithmeticCharacterFeatureTests(unittest.TestCase):
    def test_pair_swap_is_one_global_conjugation(self) -> None:
        forward = features._canonical_phase_codes((0, 1, 2, -1, 5))
        swapped = features._canonical_phase_codes((0, 5, 4, -1, 1))
        self.assertEqual(forward, swapped)
        self.assertEqual(forward, (0, 1, 2, -1, 5))

    def test_zero_sentinel_and_root_coordinates_have_injective_encoding(self) -> None:
        encoded = [features._phase_channels(k) for k in (-1, 0, 1, 2, 3, 4, 5)]
        self.assertEqual(len(set(encoded)), 7)
        self.assertEqual(encoded[0], (1, 0, 0))
        self.assertEqual(encoded[1:], [
            (0, 2, 0), (0, 1, 1), (0, -1, 1), (0, -2, 0),
            (0, -1, -1), (0, 1, -1),
        ])

    def test_real_phase_evaluator_marks_a_probe_zero(self) -> None:
        factors = (((3, 1), 1),)
        self.assertIsNone(features._phase(factors, (3, 1), 1))

    def test_frozen_full_panel_has_no_collisions_in_final_numeric_inputs(self) -> None:
        data = features.build_dataset()
        metadata = data["metadata"]
        self.assertEqual(len(data["rows"]), 13_434)
        self.assertEqual(len(data["feature_names"]), 41)
        self.assertEqual(metadata["source"]["group_counts"], {
            "affected_affected": 1_006,
            "cross": 4_038,
            "rough_rough": 8_390,
        })
        self.assertEqual(metadata["split"]["train_pairs"], 4_428)
        self.assertEqual(metadata["split"]["test_pairs"], 9_006)
        self.assertEqual(metadata["collision_audit"]["strong_prior_features_plus_character_prefixes"]["1"]["disjoint_target_groups"], 322)
        self.assertEqual(metadata["collision_audit"]["strong_prior_features_plus_character_prefixes"]["3"]["disjoint_target_groups"], 202)
        self.assertEqual(metadata["collision_audit"]["strong_prior_features_plus_character_prefixes"]["5"]["disjoint_target_groups"], 12)
        self.assertEqual(metadata["collision_audit"]["strong_prior_features_plus_character_prefixes"]["9"]["disjoint_target_groups"], 0)
        final_audit = metadata["collision_audit"]["exact_final_numeric_feature_vector"]
        self.assertEqual(final_audit["distinct_keys"], 13_380)
        self.assertEqual(final_audit["repeated_key_groups"], 54)
        self.assertEqual(final_audit["pairs_in_repeated_key_groups"], 108)
        self.assertEqual(final_audit["disjoint_target_groups"], 0)
        self.assertEqual(metadata["collision_audit"]["admission"], "READY_FOR_BOUNDED_PYSR_ON_FINITE_PANEL")
        resolution = metadata["resolved_prior_witness"]
        self.assertTrue(resolution["same_previous_strong_key"])
        self.assertTrue(resolution["same_base_numeric_features"])
        self.assertEqual(resolution["differing_probe_indices_zero_based"], [2, 3, 4, 5, 6, 8])
        self.assertNotIn("pair_group", data["feature_names"])
        self.assertNotIn("i", data["feature_names"])
        self.assertNotIn("j", data["feature_names"])
        for row in data["rows"]:
            self.assertEqual(len(row["features"]), len(row["feature_intervals"]))
            self.assertEqual(len(row["arithmetic_character_codes"]), len(features.PROBES))


if __name__ == "__main__":
    unittest.main()
