"""Independent finite-source checks; not cofinal certificates."""
from fractions import Fraction
import unittest
from flint import ctx
import evaluate as ev


class SourceChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192

    def test_complete_element_ball_matches_lattice(self):
        for bound in (7, 64, 256):
            actual = {row.z for row in ev.elements_up_to(bound)}
            expected = {
                (a, b) for a in range(-2*bound, 2*bound+1)
                for b in range(-2*bound, 2*bound+1)
                if 0 < ev.norm((a, b)) <= bound
            }
            self.assertEqual(actual, expected)

    def test_symbol_multiplicativity_and_zero_masks(self):
        for prime in [*ev.split_generators(7), *ev.split_generators(13), (-5, 0)]:
            for x in [(1, 0), (0, 1), (2, 1), prime]:
                for y in [(1, 1), (3, 2), prime]:
                    self.assertEqual(ev.cp(prime, ev.em(x, y)),
                                     ev.rm(ev.cp(prime, x), ev.cp(prime, y)))
            self.assertEqual(ev.cp(prime, prime), ev.ZERO)
            self.assertEqual(ev.cp(prime, ev.ONE), ev.ONE)

    def test_mask_mutation_changes_support_hash(self):
        n = next(n for n in ev.ideals_up_to(7) if n.q == 7)
        a = ev.ideals_up_to(1)[0]
        u = ev.elements_up_to(1)[0]
        args = ([n], [a], [u], [u], [[0]], [[0]], [[True]], [[True]])
        original = ev.canonical_support_hash(*args)
        changed = ev.canonical_support_hash(*args[:-1], [[False]])
        self.assertNotEqual(original, changed)

    def test_sixthfree_uses_ideal_exponents(self):
        self.assertTrue(ev.sixthfree(((ev.INERT_2, 3),)))
        self.assertFalse(ev.sixthfree(((ev.INERT_2, 6),)))
        self.assertEqual(ev.norm(ev.ep(ev.INERT_2, 6)), 4096)

    def test_two_full_C_sums_and_precision_stability(self):
        config = {"id": "control", "U": 8, "r": "28/25",
                  "ell": "111/100", "orientation": 1, "split": "train"}
        lo = ev.evaluate_config(config, 192, Fraction("1e-35"))
        hi = ev.evaluate_config(config, 256, Fraction("1e-35"))
        from flint import arb
        a = arb(lo["q_lower"]).union(arb(lo["q_upper"]))
        b = arb(hi["q_lower"]).union(arb(hi["q_upper"]))
        self.assertTrue(a.overlaps(b))
        self.assertTrue(lo["components"]["C_overlap_verified"])
        self.assertTrue(lo["components"]["E_M_Omega_overlap_verified"])


if __name__ == "__main__":
    unittest.main()
