from __future__ import annotations

import hashlib
import unittest

from orchestrator import research_debt_challenge
from orchestrator import session_briefing


DEBT_ID = "SELECTED_FERRERS_EVEN_SECTOR_FLOOR_CURRENT_SOURCE_SHELF"
REQUEST_ID = "REQ-TEST-DEBT"
BOUNDARY_ID = "BOUNDARY-TEST-DEBT"


class ResearchDebtChallengePlants(unittest.TestCase):
    def test_packet_is_deterministic_utf8_with_final_lf(self) -> None:
        first = research_debt_challenge.render(session_briefing.REPO, DEBT_ID, REQUEST_ID, BOUNDARY_ID)
        second = research_debt_challenge.render(session_briefing.REPO, DEBT_ID, REQUEST_ID, BOUNDARY_ID)
        self.assertEqual(first, second)
        self.assertTrue(first.endswith(b"\n"))
        text = first.decode("utf-8")
        self.assertIn(f"REQUEST_ID: {REQUEST_ID}", text)
        self.assertIn(f"BOUNDARY_ID: {BOUNDARY_ID}", text)
        self.assertIn("PACKET_SUBTYPE: RESEARCH_DEBT_CHALLENGE", text)
        self.assertIn("CALL_CLASS: EXPLORATION_REVIEW", text)
        self.assertIn("EXISTING_CONTROL_V9_GATE_REQUIRED", text)
        self.assertIn("ACTUAL_CONSUMER_REQUIREMENT", text)
        debt = next(
            row
            for row in session_briefing.validate_registry(session_briefing.REPO)["debts"]
            if row["id"] == DEBT_ID
        )
        self.assertIn(f"ORIGINAL_OBJECT_IS: {debt['original_object_is']}", text)
        self.assertIn("WEAKER_INTERFACE_PROBE", text)
        self.assertIn("CONSUMER_IMPLICATION", text)
        self.assertIn("NO_SOURCE research debt, never mathematical death", text)
        self.assertIn("NOVELTY_REQUIREMENT", text)
        self.assertIn("ALLOWED_RESEARCH_OUTCOMES", text)
        self.assertIn("TRY_, KILL_, or RUN_", text)
        self.assertIn("KILL_SCOPE as ATTEMPT, THEOREM_SHAPE, or ROUTE_FAMILY", text)
        self.assertIn("counterexample to original X kills only X's exact theorem shape", text)
        self.assertIn("ROUTE_FAMILY death additionally requires consumer-wide evidence", text)
        self.assertIn("every admissible weaker interface Z", text)
        self.assertNotIn("proving the route mathematically dead", text)

    def test_manifest_binds_exact_bytes(self) -> None:
        payload = research_debt_challenge.render(session_briefing.REPO, DEBT_ID, REQUEST_ID, BOUNDARY_ID)
        result = research_debt_challenge.manifest(payload, DEBT_ID)
        self.assertEqual(result["sha256"], hashlib.sha256(payload).hexdigest())
        self.assertEqual(result["bytes"], len(payload))
        self.assertEqual(result["lines"], payload.count(b"\n"))
        self.assertIs(result["final_newline"], True)

    def test_unknown_debt_fails_closed(self) -> None:
        with self.assertRaisesRegex(
            session_briefing.SessionBriefingError, "RESEARCH_DEBT_UNKNOWN"
        ):
            research_debt_challenge.render(session_briefing.REPO, "NO_SUCH_DEBT", REQUEST_ID, BOUNDARY_ID)

    def test_request_binding_is_mandatory(self) -> None:
        with self.assertRaisesRegex(
            session_briefing.SessionBriefingError, "REQUEST_BINDING_INVALID"
        ):
            research_debt_challenge.render(session_briefing.REPO, DEBT_ID, "bad", "")


if __name__ == "__main__":
    unittest.main()
