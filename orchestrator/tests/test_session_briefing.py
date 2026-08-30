from __future__ import annotations

import datetime as dt
import json
import tempfile
import unittest
from pathlib import Path

import yaml

from orchestrator import session_briefing


class SessionBriefingPlants(unittest.TestCase):
    def test_checkpoint_bytes_are_deterministic_and_have_no_clock(self) -> None:
        payload = {
            "schema": session_briefing.SCHEMA,
            "head": "a" * 40,
            "route": {"goal": "058"},
            "totals": {"completed_bus_goals": 1},
        }
        first = session_briefing.checkpoint_bytes(payload)
        second = session_briefing.checkpoint_bytes(payload)
        self.assertEqual(first, second)
        self.assertNotIn(b"created_at", first)
        self.assertTrue(first.endswith(b"\n"))

    def test_delta_is_monotone_and_fails_closed_on_counter_rewrite(self) -> None:
        self.assertEqual(
            session_briefing._delta({"x": 4}, {"x": 2}),
            {"x": 2},
        )
        self.assertEqual(
            session_briefing._delta({"x": 1}, {"x": 2}),
            {"x": None},
        )

    def test_priority_age_buckets_and_signal_override(self) -> None:
        today = dt.date(2026, 8, 30)
        row = {"status": "KILLED_RECHECKABLE", "last_external_check": "2026-08-30"}
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "RECENT_PASSIVE")
        row["last_external_check"] = "2026-08-20"
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "NORMAL")
        row["last_external_check"] = "2026-07-01"
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "HIGHLIGHT_30_PLUS")
        row["status"] = "REOPEN_CANDIDATE"
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "HIGH_NEW_SIGNAL")

    def test_lifecycle_never_skips_source_verification(self) -> None:
        self.assertTrue(
            session_briefing.transition_allowed("KILLED_RECHECKABLE", "REOPEN_CANDIDATE")
        )
        self.assertFalse(
            session_briefing.transition_allowed("KILLED_RECHECKABLE", "READY_FOR_RERANK")
        )
        self.assertFalse(
            session_briefing.transition_allowed("REOPEN_CANDIDATE", "READY_FOR_RERANK")
        )
        self.assertTrue(
            session_briefing.transition_allowed("SOURCE_VERIFIED", "READY_FOR_RERANK")
        )

    def test_later_unselected_root_is_control_plane_drift(self) -> None:
        self.assertTrue(
            session_briefing.control_plane_drift(
                {
                    "dependency_root": "OLD_ROOT",
                    "latest_named_unselected_root": "NEW_ROOT",
                }
            )
        )
        self.assertFalse(
            session_briefing.control_plane_drift(
                {
                    "dependency_root": "SAME_ROOT",
                    "latest_named_unselected_root": "SAME_ROOT",
                }
            )
        )

    def test_checkpoint_loader_rejects_parallel_state_shape(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "checkpoint.json"
            path.write_text(json.dumps({"schema": "wrong", "totals": {}}) + "\n")
            with self.assertRaisesRegex(
                session_briefing.SessionBriefingError,
                "SESSION_BRIEFING_CHECKPOINT_INVALID",
            ):
                session_briefing.load_checkpoint(path)

            path.write_text(
                json.dumps(
                    {
                        "schema": session_briefing.SCHEMA,
                        "head": "a" * 40,
                        "route": {},
                        "totals": {
                            "completed_bus_goals": 1,
                            "kill_outcome_artifacts": 1,
                            "answered_requests": 1,
                            "proved_verdict_artifacts": 1,
                        },
                        "selected_dependency_root": "FORBIDDEN_PARALLEL_STATE",
                    }
                )
                + "\n"
            )
            with self.assertRaisesRegex(
                session_briefing.SessionBriefingError,
                "SESSION_BRIEFING_CHECKPOINT_INVALID",
            ):
                session_briefing.load_checkpoint(path)

    def test_briefing_and_checkpoint_are_registered_tools(self) -> None:
        manifest = yaml.safe_load(
            (session_briefing.REPO / "docs/cartographer/TOOLS.yaml").read_text(
                encoding="utf-8"
            )
        )
        tools = {
            tool["id"]: tool
            for family in manifest["tool_families"].values()
            for tool in family["tools"]
        }
        self.assertFalse(tools["routeb-session-briefing"]["writes"])
        self.assertTrue(tools["routeb-session-checkpoint"]["writes"])
        self.assertFalse(tools["research-debt-challenge"]["writes"])

    def test_registry_distinguishes_research_debt_from_dead(self) -> None:
        registry = session_briefing.validate_registry(session_briefing.REPO)
        self.assertTrue(registry["debts"])
        for row in registry["debts"]:
            self.assertEqual(row["classification"], "RESEARCH_DEBT")
            self.assertIs(row["not_disproved"], True)
            self.assertTrue(row["novelty_requirement"])

    def test_rank_prefers_even_high_unlock_unknown_over_satz9_high(self) -> None:
        registry = session_briefing.validate_registry(session_briefing.REPO)
        ranked = session_briefing.ranked_debts(
            registry["debts"], dt.date(2026, 8, 30)
        )
        self.assertEqual(
            ranked[0]["id"],
            "SELECTED_FERRERS_EVEN_SECTOR_FLOOR_CURRENT_SOURCE_SHELF",
        )


if __name__ == "__main__":
    unittest.main()
