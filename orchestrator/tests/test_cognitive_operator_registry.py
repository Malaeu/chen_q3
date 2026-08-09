"""Lossless plants for the M2 and legacy control-action registry."""

from __future__ import annotations

import hashlib
import sqlite3
import tempfile
import unittest
from pathlib import Path

from orchestrator import kb, kb_migrate_kills, spine


class CognitiveOperatorRegistryTests(unittest.TestCase):
    def test_registry_has_exact_closed_counts(self) -> None:
        payload = kb.load_operator_registry()
        self.assertEqual(len(payload["canonical_enum"]["operators"]), 8)
        self.assertEqual(len(payload["legacy_enum"]["operators"]), 9)
        self.assertEqual(len(payload["crosswalk"]), 9)
        counts = {}
        for row in payload["crosswalk"]:
            counts[row["relation"]] = counts.get(row["relation"], 0) + 1
        self.assertEqual(counts, {
            "DIRECT_ALIAS": 2,
            "RELATED_NOT_EQUIVALENT": 2,
            "LEGACY_ONLY": 5,
        })

    def test_temporary_database_materialization_and_strict_validation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            db_path = Path(tmp) / "knowledge.db"
            conn = sqlite3.connect(db_path)
            conn.execute("PRAGMA foreign_keys = ON")
            conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
            kb.materialize_operator_registry(conn)
            conn.commit()
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM cognitive_operator_registry "
                "WHERE vocabulary='PROSHKA_M2'").fetchone()[0], 8)
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM cognitive_operator_registry "
                "WHERE vocabulary='LEGACY_CONTROL_ACTION'").fetchone()[0], 9)
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM cognitive_operator_crosswalk").fetchone()[0], 9)
            related = conn.execute(
                "SELECT canonical_token FROM cognitive_operator_crosswalk "
                "WHERE legacy_token='ReceiverMinimize' AND relation='RELATED_NOT_EQUIVALENT'"
            ).fetchone()
            self.assertEqual(related[0], "MINIMAL_LEMMA")
            conn.close()
            result = spine.validate_cognitive_operator_registry(
                db_path=db_path, live_tokens=["UNIT_AUDIT", "MINIMAL_LEMMA"])
            self.assertEqual(result, {
                "schema": "q3_cognitive_operator_registry.v1",
                "canonical": 8, "legacy": 9, "crosswalk": 9,
            })

    def test_dual_field_failed_strategies_remain_distinct(self) -> None:
        rows, evidence = kb_migrate_kills.from_yaml()
        by_id = {row["id"]: row for row in rows}
        self.assertIn("RADIUS_DRIVEN_CERTIFICATE_CUTOFF_AND_TOOTH_ALIGNED_TRANSITIO", by_id)
        pairs = {(kill_id, kind, ref) for kill_id, kind, ref in evidence}
        self.assertIn((
            "RADIUS_DRIVEN_CERTIFICATE_CUTOFF_AND_TOOTH_ALIGNED_TRANSITIO",
            "legacy_control_action", "RepresentationShift",
        ), pairs)
        self.assertIn((
            "RADIUS_DRIVEN_CERTIFICATE_CUTOFF_AND_TOOTH_ALIGNED_TRANSITIO",
            "cognitive_operator", "MINIMAL_LEMMA",
        ), pairs)
        self.assertIn((
            "FULL_PACKET_SEARCH_WITH_MULTIPLE_INDEPENDENT_FRONTS",
            "legacy_control_action", "ReceiverMinimize",
        ), pairs)
        self.assertIn((
            "FULL_PACKET_SEARCH_WITH_MULTIPLE_INDEPENDENT_FRONTS",
            "cognitive_operator", "MINIMAL_LEMMA",
        ), pairs)

    def test_unknown_live_operator_fails_closed(self) -> None:
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.validate_cognitive_operator_tokens(
                ["MINIMAL_LEMMA", "NOT_A_REAL_OPERATOR"], {"MINIMAL_LEMMA"})
        self.assertEqual(
            caught.exception.code,
            "COGNITIVE_OPERATOR_REGISTRY_UNAVAILABLE_OR_INVALID",
        )

    def test_tests_do_not_mutate_production_database(self) -> None:
        before = hashlib.sha256(kb.DB_PATH.read_bytes()).hexdigest()
        kb.load_operator_registry()
        after = hashlib.sha256(kb.DB_PATH.read_bytes()).hexdigest()
        self.assertEqual(before, after)


if __name__ == "__main__":
    unittest.main()
