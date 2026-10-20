"""Small exact checks for the periodic-character disk counter."""
from fractions import Fraction
from math import isqrt
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import evaluate as ev
from nonunit import periodic


def brute_pair(left, right, bound, orientation=1):
    if bound == 0:
        return 0
    y_max = isqrt((4 * bound) // 3)
    x_max = 2 * isqrt(bound) + 3
    total = 0
    for y in range(-y_max, y_max + 1):
        for x in range(-x_max, x_max + 1):
            z = (x, y)
            if not 0 < ev.norm(z) <= bound:
                continue
            left_phase = ev.phase_index(left, z, orientation)
            right_phase = ev.phase_index(right, z, orientation)
            if left_phase is not None and right_phase is not None:
                total += int(2 * ev.ROOT_REAL[(left_phase - right_phase) % 6])
    return total


def row_for_factors(factors):
    return ev.Ideal(ev.ideal_norm(factors), factors, ev.ideal_generator(factors))


class PeriodicCharacterTests(unittest.TestCase):
    def setUp(self):
        self.unit = ev.ideals_up_to(1)[0]
        self.prime7 = next(row for row in ev.ideals_up_to(7) if row.q == 7)
        self.prime13 = next(row for row in ev.ideals_up_to(13) if row.q == 13)

    def test_hnf_shift_and_negative_y_disk_rows(self):
        period = periodic._principal_period(self.prime7.factors, self.prime7.factors)
        self.assertGreater(period.b_hnf, 0)
        self.assertEqual(period.h2, 1)
        bounds = [0, 1, 2, 7, 8, 19, 49]
        actual = periodic.raw_sums([self.prime7], bounds)
        for result in actual:
            self.assertEqual(
                result["pair_2re"][0][0],
                brute_pair(self.prime7.factors, self.prime7.factors, result["B"]),
            )
            self.assertEqual(result["N"], brute_pair((), (), result["B"]) // 2)

    def test_inert_square_uses_full_hnf_period(self):
        square = ((ev.INERT_2, 2),)
        row = row_for_factors(square)
        period = periodic._principal_period(square, square)
        self.assertEqual((period.h1, period.h2, period.b_hnf, period.norm), (4, 4, 0, 16))
        results = periodic.raw_sums([row], [1, 4, 8, 16, 25])
        for result in results:
            self.assertEqual(
                result["pair_2re"][0][0],
                brute_pair(square, square, result["B"]),
            )

    def test_shared_prime_zero_mask_differs_from_conductor_one(self):
        self.assertIsNone(ev.phase_index(self.prime7.factors, self.prime7.gen, 1))
        result = periodic.raw_sums([self.unit, self.prime7], [7])[0]
        self.assertEqual(result["N"], 30)
        self.assertEqual(result["pair_2re"][0][0], 60)
        self.assertEqual(result["pair_2re"][1][1], 48)
        self.assertEqual(result["pair_2re"][0][1], 0)
        self.assertLess(result["pair_2re"][1][1], result["pair_2re"][0][0])

    def test_all_six_unit_translates_and_exact_unit_cancellation(self):
        z = (2, 1)
        for factors in (self.prime7.factors, self.prime13.factors):
            base = ev.phase_index(factors, z, 1)
            self.assertIsNotNone(base)
            for unit in ev.UNITS:
                translated = ev.em(unit, z)
                self.assertEqual(ev.norm(translated), ev.norm(z))
                translated_phase = ev.phase_index(factors, translated, 1)
                unit_phase = ev.phase_index(factors, unit, 1)
                self.assertEqual(translated_phase, (base + unit_phase) % 6)

        results = periodic.raw_sums([self.prime7, self.prime13], [1, 7, 49, 64])
        self.assertTrue(all(result["pair_2re"][0][1] == 0 for result in results))
        self.assertNotEqual(
            periodic._unit_phase(self.prime7.factors, 1),
            periodic._unit_phase(self.prime13.factors, 1),
        )
        plus = periodic.raw_sums([self.unit, self.prime7, self.prime13], [7, 49], 1)
        minus = periodic.raw_sums([self.unit, self.prime7, self.prime13], [7, 49], -1)
        self.assertEqual(
            [result["pair_2re"] for result in plus],
            [result["pair_2re"] for result in minus],
        )

    def test_explicit_radius_and_period_limits_fail_without_truncation(self):
        with self.assertRaisesRegex(ValueError, "no disk was truncated"):
            periodic.raw_sums([self.unit], [periodic.MAX_BOUND + 1])
        oversized = ((ev.INERT_2, 10),)  # norm 4^10 exceeds the declared period cap.
        with self.assertRaisesRegex(ValueError, "no period was truncated"):
            periodic.raw_sums([row_for_factors(oversized)], [1])

    def test_weighted_energy_uses_diagonal_half_and_upper_triangle(self):
        matrix = [[10, -4], [-4, 6]]
        weights = [Fraction(2, 3), Fraction(-1, 5)]
        expected = (
            Fraction(10, 2) * weights[0] ** 2
            + Fraction(6, 2) * weights[1] ** 2
            - 4 * weights[0] * weights[1]
        )
        self.assertEqual(periodic.raw_energy(matrix, weights), expected)


if __name__ == "__main__":
    unittest.main()
