from __future__ import annotations

import copy
import gzip
import json
import tempfile
import unittest
from unittest.mock import patch
from fractions import Fraction
from pathlib import Path

import split


class GcdSplitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data, _ = split.load_panel()

    def test_full_panel_splits_exhaustively_at_all_pinned_thresholds(self) -> None:
        report = split.analyze_panel(self.data)
        self.assertEqual(report["input"]["rows"], 20)
        self.assertEqual(report["input"]["pairs"], 13434)
        for row in report["rows"]:
            for result in row["thresholds"]:
                self.assertTrue(result["partition_exhaustive"])
                self.assertTrue(result["reassembled_C_overlaps_saved_full_C"])
                self.assertTrue(result["reassembled_C_overlaps_saved_pair_sum"])
                self.assertTrue(all(result["group_C_reassembly_overlaps_saved"][g]
                                    for g in split.GROUPS))
                self.assertEqual(result["sides"]["main"]["total"]["pair_count"]
                                 + result["sides"]["remainder"]["total"]["pair_count"],
                                 row["pair_count"])
                for side in ("main", "remainder"):
                    self.assertEqual(set(split.GROUPS) & set(result["sides"][side]), set(split.GROUPS))

    def test_gcd_threshold_boundary_is_inclusive(self) -> None:
        row = next(r for r in self.data["rows"] if r["id"] == "U48_P7_o1")
        for threshold in (1, 7, 13, 19, 31):
            at_boundary = [p for p in row["pairs"]
                           if split.verify_pair_gcd(p) == threshold]
            if at_boundary:
                result = split._accumulate(row["pairs"], threshold)
                self.assertEqual(sum(result["sides"]["main"][g]["pair_count"] for g in split.GROUPS),
                                 sum(split.verify_pair_gcd(p) <= threshold for p in row["pairs"]))
                self.assertGreater(sum(result["sides"]["main"][g]["pair_count"] for g in split.GROUPS), 0)

    def test_dropping_cross_pairs_is_rejected(self) -> None:
        changed = copy.deepcopy(self.data)
        row = next(r for r in changed["rows"] if any(p["group"] == "cross" for p in r["pairs"]))
        row["pairs"] = [p for p in row["pairs"] if p["group"] != "cross"]
        with self.assertRaisesRegex(ValueError, "pair count mismatch"):
            split.analyze_panel(changed)

    def test_tampered_gcd_identity_is_rejected(self) -> None:
        changed = copy.deepcopy(self.data)
        row = next(r for r in changed["rows"] if r["pairs"])
        changed_pair = row["pairs"][0]
        changed_pair["full_period_lcm_norm_Q"] += 1
        with self.assertRaisesRegex(ValueError, "lcm factors|ideal norms"):
            split.verify_pair_gcd(changed_pair)

    def test_opposite_sign_split_records_positive_part_penalty(self) -> None:
        main = (Fraction(2), Fraction(2))
        remainder = (Fraction(-1), Fraction(-1))
        full = split._add(main, remainder)
        penalty = split._sub(
            split._add(split._positive_part(main), split._positive_part(remainder)),
            split._positive_part(full),
        )
        self.assertEqual(penalty, (Fraction(1), Fraction(1)))

    def test_interval_separation_enclosure_respects_known_nonnegativity(self) -> None:
        # Dependency loss can put the raw interval below zero although the
        # identity (M+R)_+ <= M_+ + R_+ proves the actual penalty nonnegative.
        self.assertEqual(split._nonnegative_enclosure((Fraction(-1, 10), Fraction(2))),
                         (Fraction(0), Fraction(2)))

    def test_trivial_g_above_panel_max_leaves_empty_remainder(self) -> None:
        row = self.data["rows"][0]
        gmax = max(split.verify_pair_gcd(p) for p in row["pairs"])
        result = split._accumulate(row["pairs"], gmax + 1)
        self.assertEqual(result["sides"]["main"]["total"]["pair_count"], len(row["pairs"]))
        self.assertEqual(result["sides"]["remainder"]["total"]["pair_count"], 0)

    def test_source_mutation_fails_sha_pin(self) -> None:
        original = split.INPUT.read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            mutated = Path(directory) / "decomposition.json.gz"
            mutated.write_bytes(original + b"x")
            with self.assertRaisesRegex(ValueError, "SHA256 mismatch"):
                split.load_panel(mutated)

    def test_output_path_is_created_exclusively(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "result.json"
            output.write_text("owner data", encoding="utf-8")
            with patch("sys.argv", ["split.py", "--output", str(output)]):
                with self.assertRaises(FileExistsError):
                    split.main()
            self.assertEqual(output.read_text(encoding="utf-8"), "owner data")


if __name__ == "__main__":
    unittest.main()
