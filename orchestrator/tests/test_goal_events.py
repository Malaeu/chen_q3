from __future__ import annotations

import hashlib
import json
import sqlite3
import tempfile
import unittest
from pathlib import Path

from orchestrator import goal_events


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_db(path: Path) -> None:
    conn = sqlite3.connect(path)
    conn.executescript(
        """
        CREATE TABLE journal_entry (
          id TEXT PRIMARY KEY, date TEXT, kind TEXT, title TEXT,
          workstream TEXT, state TEXT, channel TEXT, target TEXT,
          validation TEXT, artifact_sha TEXT, boundary TEXT,
          next_target TEXT, body TEXT, source_file TEXT NOT NULL
        );
        CREATE VIRTUAL TABLE journal_fts USING fts5(
          title, body, target, boundary,
          content='journal_entry', content_rowid='rowid'
        );
        """
    )
    conn.close()


class GoalEventTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.goal = self.root / "docs/routeB_bus/058_test.goal.md"
        self.goal.parent.mkdir(parents=True)
        self.goal.write_text("STATUS: OPEN\nGOAL: '058'\n", encoding="utf-8")
        self.evidence = self.root / "evidence.md"
        self.evidence.write_text("checked evidence\n", encoding="utf-8")
        self.db = self.root / "knowledge.db"
        make_db(self.db)
        self.insights = self.root / "INSIGHTS.md"
        self.insights.write_text("# Insights\n", encoding="utf-8")

    def tearDown(self) -> None:
        self.temp.cleanup()

    def provenance(self) -> list[dict[str, str]]:
        return [
            {
                "path": "evidence.md",
                "sha256": sha256(self.evidence),
                "role": "validation",
                "locator": "line 1",
            }
        ]

    def attempt(self) -> dict[str, object]:
        return {
            "schema": "q3_goal_attempt.v1",
            "attempt_id": "ATTEMPT_GOAL058_001",
            "goal_run_id": "GOAL058-20260813T120000Z",
            "goal_file": "docs/routeB_bus/058_test.goal.md",
            "goal_sha256": sha256(self.goal),
            "recorded_date": "2026-08-13",
            "cycle_index": 1,
            "registered_prediction": "the discriminator changes the blocker",
            "cheapest_killer": "run the isolated plant",
            "blocker_fingerprint_before": "a" * 64,
            "blocker_fingerprint_after": "b" * 64,
            "delta_id": "DELTA_058_001",
            "progress_class": "GAP_SHRINK",
            "cognitive_operator": "MINIMAL_LEMMA",
            "next_action": "CONTINUE_STEP",
            "source_provenance": self.provenance(),
            "extra": {"note": "non-authoritative"},
        }

    def insight(self) -> dict[str, object]:
        return {
            "schema": "q3_goal_insight.v1",
            "insight_id": "INSIGHT_GOAL058_TEST",
            "recorded_date": "2026-08-13",
            "title": "The exact source has a smaller consumer",
            "workstream": "Goal 058",
            "target": "G2 bridge",
            "summary": "The existing consumer spends the normalized supplier directly.",
            "validation": "source and consumer inspected byte-exactly",
            "boundary": "This is retrieval evidence, not a Lean proof.",
            "next_target": "compile the exact receiver",
            "source_provenance": self.provenance(),
        }

    def test_attempt_retry_is_idempotent_and_searchable(self) -> None:
        payload = self.attempt()
        first = goal_events.record_attempt(payload, db_path=self.db, repo_root=self.root)
        second = goal_events.record_attempt(payload, db_path=self.db, repo_root=self.root)
        self.assertEqual(first.status, "RECORDED")
        self.assertEqual(second.status, "ALREADY_RECORDED")
        conn = sqlite3.connect(self.db)
        self.assertEqual(
            conn.execute("SELECT COUNT(*) FROM journal_entry").fetchone()[0], 1
        )
        self.assertEqual(
            conn.execute(
                "SELECT COUNT(*) FROM journal_fts WHERE journal_fts MATCH 'discriminator'"
            ).fetchone()[0],
            1,
        )
        conn.close()

    def test_attempt_id_collision_fails_closed(self) -> None:
        payload = self.attempt()
        goal_events.record_attempt(payload, db_path=self.db, repo_root=self.root)
        payload["registered_prediction"] = "different bytes"
        with self.assertRaisesRegex(goal_events.GoalEventError, "ATTEMPT_ID_COLLISION"):
            goal_events.record_attempt(payload, db_path=self.db, repo_root=self.root)

    def test_attempt_rejects_controller_field_in_extra(self) -> None:
        payload = self.attempt()
        payload["extra"] = {"cycle_index": 12}
        with self.assertRaisesRegex(
            goal_events.GoalEventError, "GOAL_ATTEMPT_SCHEMA_INVALID"
        ):
            goal_events.validate_attempt(payload, repo_root=self.root)

    def test_attempt_rejects_provenance_drift(self) -> None:
        payload = self.attempt()
        self.evidence.write_text("changed\n", encoding="utf-8")
        with self.assertRaisesRegex(
            goal_events.GoalEventError, "GOAL_EVENT_PROVENANCE_INVALID"
        ):
            goal_events.validate_attempt(payload, repo_root=self.root)

    def test_attempt_progress_and_delta_cannot_disagree(self) -> None:
        payload = self.attempt()
        payload["delta_id"] = "NONE"
        with self.assertRaisesRegex(
            goal_events.GoalEventError, "progress requires a named delta"
        ):
            goal_events.validate_attempt(payload, repo_root=self.root)
        payload["progress_class"] = "NO_PROGRESS"
        with self.assertRaisesRegex(
            goal_events.GoalEventError, "preserve the blocker fingerprint"
        ):
            goal_events.validate_attempt(payload, repo_root=self.root)

    def test_invalid_calendar_date_is_rejected(self) -> None:
        payload = self.attempt()
        payload["recorded_date"] = "2026-02-31"
        with self.assertRaisesRegex(goal_events.GoalEventError, "recorded_date invalid"):
            goal_events.validate_attempt(payload, repo_root=self.root)

    def test_insight_retry_and_semantic_duplicate_are_deduplicated(self) -> None:
        payload = self.insight()
        first = goal_events.record_insight(
            payload, insights_path=self.insights, repo_root=self.root
        )
        second = goal_events.record_insight(
            payload, insights_path=self.insights, repo_root=self.root
        )
        duplicate = dict(payload)
        duplicate["insight_id"] = "INSIGHT_GOAL058_DUPLICATE_ID"
        third = goal_events.record_insight(
            duplicate, insights_path=self.insights, repo_root=self.root
        )
        self.assertEqual(first.status, "RECORDED")
        self.assertEqual(second.status, "ALREADY_RECORDED")
        self.assertEqual(third.status, "ALREADY_RECORDED")
        text = self.insights.read_text(encoding="utf-8")
        self.assertEqual(text.count("```json q3_goal_insight"), 1)
        self.assertIn("This is retrieval evidence, not a Lean proof.", text)

    def test_insight_id_collision_fails_closed(self) -> None:
        payload = self.insight()
        goal_events.record_insight(payload, insights_path=self.insights, repo_root=self.root)
        payload["summary"] = "Different semantic content."
        with self.assertRaisesRegex(goal_events.GoalEventError, "INSIGHT_ID_COLLISION"):
            goal_events.record_insight(
                payload, insights_path=self.insights, repo_root=self.root
            )

    def test_cli_rejects_duplicate_json_keys(self) -> None:
        payload = self.root / "payload.json"
        payload.write_text('{"schema":"x","schema":"y"}', encoding="utf-8")
        with self.assertRaisesRegex(
            goal_events.GoalEventError, "GOAL_EVENT_PAYLOAD_INVALID"
        ):
            goal_events._load_unique_json(payload)

    def test_machine_payload_is_canonical_json(self) -> None:
        payload = self.insight()
        receipt = goal_events.record_insight(
            payload, insights_path=self.insights, repo_root=self.root
        )
        text = self.insights.read_text(encoding="utf-8")
        raw = text.split("```json q3_goal_insight\n", 1)[1].split("\n```", 1)[0]
        machine = json.loads(raw)
        self.assertEqual(machine["payload_sha256"], receipt.payload_sha256)
        self.assertEqual(machine["semantic_sha256"], receipt.semantic_sha256)
