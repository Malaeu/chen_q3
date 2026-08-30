from __future__ import annotations

import hashlib
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
PROMPTS = (
    REPO / "docs" / "routeB_bus" / "PROSHKA_SYSTEM_PROMPT_v2.md",
    REPO / "docs" / "routeB_bus" / "proshka" / "PROSHKA_SYSTEM_PROMPT_v2.md",
    REPO
    / "q3.lean.aristotle"
    / "ACTIVE"
    / "requests"
    / "routeB_lamport_rh_closure"
    / "proshka"
    / "PROSHKA_SYSTEM_PROMPT_v2.md",
)


class ProshkaSystemPromptContractPlants(unittest.TestCase):
    def test_all_active_mirrors_are_byte_identical(self) -> None:
        digests = {hashlib.sha256(path.read_bytes()).hexdigest() for path in PROMPTS}
        self.assertEqual(1, len(digests))

    def test_consumer_first_kill_boundary_and_verdict_grammar_are_pinned(self) -> None:
        text = PROMPTS[0].read_text(encoding="utf-8")
        self.assertIn("K8A. CONSUMER-FIRST DEPENDENCY CONTRACT", text)
        self.assertIn("KILL_SCOPE` as `ATTEMPT`, `THEOREM_SHAPE`, or", text)
        self.assertIn("A counterexample to the originally named X alone kills", text)
        self.assertIn("across the admissible\nweaker-interface class", text)
        self.assertIn("# STATUS: TRY_<route_id>", text)
        self.assertIn("# STATUS: KILL_<route_or_family_id>", text)
        self.assertIn("# STATUS: RUN_<test_id>", text)
        self.assertIn("Do not return\n`SOURCE_WRITTEN`, `PROVED`", text)
        self.assertIn("1. OPERATIVE CLASS", text)
        self.assertLess(text.index("1. OPERATIVE CLASS"), text.index("2. ROUTE MAP"))


if __name__ == "__main__":
    unittest.main()
