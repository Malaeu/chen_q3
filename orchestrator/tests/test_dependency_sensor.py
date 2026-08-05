"""Fail-closed plants for the Lean axiom dependency supplier."""

from __future__ import annotations

import unittest

from scripts import build_dependency_tree


class DependencyOutputParserTests(unittest.TestCase):
    def test_all_print_axioms_roots_are_preserved(self) -> None:
        output = """\
'Q3.Main.RH_of_Weil_and_Q3' depends on axioms: [propext,
 Q3.Weil_criterion,
 Quot.sound]
'Q3.RH_of_shifted_atom_route' depends on axioms: [Classical.choice,
 Q3.prime_term_le_at_t_critical_axiom]
"""
        roots = build_dependency_tree.parse_axiom_dependency_output(output)
        self.assertEqual(
            [root["id"] for root in roots],
            ["Q3.Main.RH_of_Weil_and_Q3", "Q3.RH_of_shifted_atom_route"],
        )
        self.assertEqual(roots[0]["axioms"][1], "Q3.Weil_criterion")
        self.assertEqual(len(roots[1]["axioms"]), 2)

    def test_duplicate_root_fails_closed(self) -> None:
        block = "'ROOT' depends on axioms: [propext]\n"
        with self.assertRaisesRegex(ValueError, "duplicate"):
            build_dependency_tree.parse_axiom_dependency_output(block + block)

    def test_missing_dependency_block_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "no #print axioms"):
            build_dependency_tree.parse_axiom_dependency_output("clean build, no report")


if __name__ == "__main__":
    unittest.main()
