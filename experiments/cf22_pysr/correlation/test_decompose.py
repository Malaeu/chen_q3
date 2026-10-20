from __future__ import annotations

import sys
import unittest
import json
from pathlib import Path

from flint import arb


HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import decompose


class PairDecompositionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan, cls.main, cls.heldout, cls.freeze, cls.manifest = decompose.load_frozen_inputs()
        cls.source, cls.evaluator = decompose._modules()
        cls.config = next(
            config for config in cls.plan["configs"]
            if config["id"] == "U48_P49_o1"
        )
        cls.saved_row = next(
            row for row in cls.heldout["rows"]
            if row["id"] == "U48_P49_o1"
        )
        cls.result = decompose.decompose_config(
            cls.config,
            cls.saved_row,
            cls.plan,
            source=cls.source,
            evaluator=cls.evaluator,
        )

    def test_pair_partition_is_exhaustive_and_disjoint(self) -> None:
        self.assertEqual(decompose.pair_category(True, True), "rough_rough")
        self.assertEqual(decompose.pair_category(True, False), "cross")
        self.assertEqual(decompose.pair_category(False, True), "cross")
        self.assertEqual(decompose.pair_category(False, False), "affected_affected")
        groups = self.result["groups"]
        self.assertEqual(
            sum(groups[name]["pair_count"] for name in groups),
            self.result["counts"]["pair_count"],
        )
        self.assertTrue(self.result["group_reassembly_checks"]["group_C_overlaps_pair_sum"])
        self.assertEqual(self.result["counts"]["P_rough_columns"], 14)
        self.assertEqual(self.result["counts"]["P_affected_columns"], 7)

    def test_shared_prime_is_full_period_zero_mask_not_quotient_conductor(self) -> None:
        split7 = self.source.split_generators(7)
        split13 = self.source.split_generators(13)
        common, left_only = split7
        right_only = split13[0]
        left = tuple(sorted(((common, 1), (left_only, 1))))
        right = tuple(sorted(((common, 1), (right_only, 1))))

        metadata = decompose.pair_ideal_metadata(self.source, left, right, 1)
        full_period = metadata["full_period_lcm_norm_Q"]
        conductor = metadata["primitive_quotient_conductor"]["norm"]
        shared = metadata["shared_zero_mask_gcd"]
        self.assertEqual(full_period, self.source.norm(common) * self.source.norm(left_only) * self.source.norm(right_only))
        self.assertEqual(conductor, self.source.norm(left_only) * self.source.norm(right_only))
        self.assertGreater(full_period, conductor)
        self.assertEqual(shared["norm"], self.source.norm(common))
        self.assertEqual(shared["factors"][0]["prime_generator"], [common[0], common[1]])
        self.assertTrue(metadata["shared_primes_remain_zero_mask"])
        self.assertEqual(
            {factor["quotient_local_exponent"] for factor in metadata["primitive_quotient_character"]["local_factors"]},
            {-1, 1},
        )

    def test_coefficient_two_matches_direct_physical_energy_expansion(self) -> None:
        root0 = self.source.ROOT[0]
        root1 = self.source.ROOT[1]
        direct_energy = self.source.phase_norm((
            arb(root0[0] + root1[0]),
            arb(root0[1] + root1[1]),
        ))
        diagonal_energy = (
            self.source.phase_norm((arb(root0[0]), arb(root0[1])))
            + self.source.phase_norm((arb(root1[0]), arb(root1[1])))
        )
        direct_pair = direct_energy - diagonal_energy
        pair_kernel = decompose.two_re_character_value(self.source, 0, 1)
        self.assertEqual(pair_kernel, 1)
        self.assertEqual(direct_pair, self.source.arb_fraction(pair_kernel))

    def test_saved_pair_sum_matches_existing_full_c_and_h49(self) -> None:
        self.assertTrue(self.result["pair_sum_overlaps_old_C"])
        self.assertTrue(self.result["pair_minus_full_C_residual_contains_zero"])
        self.assertTrue(self.result["physical_subtotal_overlaps_old"])
        self.assertTrue(self.result["raw_subtotal_overlaps_old"])
        self.assertTrue(self.result["h49_pair_formula_check"]["interval_residual_contains_zero"])
        self.assertTrue(self.result["interval_width_checks"]["max_pair_C_contribution_width_within_limit"])

        rough_rough = [
            pair for pair in self.result["pairs"]
            if pair["group"] == "rough_rough"
        ]
        self.assertTrue(rough_rough)
        self.assertTrue(all(pair["A_P_exact"] == pair["A_exact"] for pair in rough_rough))
        self.assertTrue(all(pair["inclusion_exclusion"]["equals_direct_A_P"] for pair in self.result["pairs"]))
        self.assertTrue(all("mask_correction" in group for group in self.result["groups"].values()))
        json.dumps(self.result, sort_keys=True)


if __name__ == "__main__":
    unittest.main()
