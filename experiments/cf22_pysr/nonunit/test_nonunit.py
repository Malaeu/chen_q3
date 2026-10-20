"""Independent finite checks for full source assembly and ideal masks."""
from fractions import Fraction
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import evaluate as ev
from nonunit import periodic
from nonunit.test_periodic import brute_pair


class NonunitIntegrationTests(unittest.TestCase):
    def test_all_good_ideal_pairs_small_disks(self):
        rows = [n for n in ev.ideals_up_to(49) if ev.good_ideal(n.factors)]
        for record in periodic.raw_sums(rows, [19, 64]):
            for i, left in enumerate(rows):
                for j in range(i, len(rows)):
                    self.assertEqual(record['pair_2re'][i][j],
                                     brute_pair(left.factors, rows[j].factors, record['B']))

    def test_amplifier_counts_include_powers(self):
        for limit, expected in [(7, 3), (13, 5), (49, 17)]:
            rows = [n for n in ev.ideals_up_to(limit) if ev.good_ideal(n.factors)]
            self.assertEqual(len(rows), expected)
        self.assertEqual(sum(n.q == 49 for n in rows), 3)

    def test_full_C_production_matches_direct_enumeration(self):
        from nonunit import evaluate_nonunit as diagnostic
        row = diagnostic.evaluate_config(
            dict(id='test_P0', U=48, P='production', r='113/100',
                 ell='113/100', orientation=1, stage='main'),
            192, Fraction(1, 10**30), periodic)
        self.assertTrue(row['legacy_P0_comparison']['old_evaluator_C_overlap_verified'])
        self.assertTrue(row['formula_checks']['C_formula_4_overlaps_direct_C'])
        self.assertEqual(row['counts']['amp'], 1)


if __name__ == '__main__':
    unittest.main()
