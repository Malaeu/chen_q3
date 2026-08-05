"""Plants for the disposable observability projection."""

from __future__ import annotations

import hashlib
import json
import sqlite3
import tempfile
import unittest
from pathlib import Path

from orchestrator import observability


class TimingParserTests(unittest.TestCase):
    def test_lower_bound_and_phase_fields_are_preserved(self) -> None:
        text = """# Timing

### 2026-08-05 — test

```yaml
proof_address: G5
front: G5/S1
transaction: TX_1
wall_seconds: \">=42\"
answer_now_clicked: false
notes: >-
  compact note
```
"""
        rows = observability.parse_timing_log(text)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["transaction"], "TX_1")
        self.assertEqual(rows[0]["wall_seconds_int"], 42)
        self.assertEqual(rows[0]["wall_is_lower_bound"], 1)
        self.assertEqual(rows[0]["notes"], "compact note")

    def test_duplicate_transaction_fails_closed(self) -> None:
        block = """### run

```yaml
transaction: DUP
wall_seconds: 1
```
"""
        with self.assertRaisesRegex(ValueError, "duplicate timing transaction"):
            observability.parse_timing_log(block + "\n" + block)


class ObservabilityRebuildTests(unittest.TestCase):
    def test_current_sources_rebuild_without_touching_knowledge(self) -> None:
        knowledge = observability.REPO / "q3.lean.aristotle/aristotle_db/knowledge.db"
        before = hashlib.sha256(knowledge.read_bytes()).hexdigest()
        with tempfile.TemporaryDirectory() as tmp:
            db_path = Path(tmp) / "observability.db"
            data = observability.rebuild_database(
                db_path,
                generated_at="2026-08-05T22:30:00+00:00",
                source_commit="fixture",
            )
            self.assertEqual(len(data["sources"]), 8)
            self.assertTrue(all("stale" in source for source in data["sources"]))
            self.assertGreaterEqual(data["proshka_runs"], 15)
            self.assertEqual(data["answer_now_clicked"], 0)
            self.assertEqual(data["numeric_checks"], 0)
            self.assertGreaterEqual(data["autopsy_events"], 0)
            conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
            self.assertEqual(conn.execute("PRAGMA integrity_check").fetchone()[0], "ok")
            conn.close()
            rendered = "\n".join(observability.summary_lines(db_path))
            self.assertIn("DERIVED_NONCANONICAL_OBSERVABILITY", rendered)
            self.assertNotIn("request_message_id", rendered)
        after = hashlib.sha256(knowledge.read_bytes()).hexdigest()
        self.assertEqual(before, after)

    def test_multiroot_dependency_inventory_is_not_flattened(self) -> None:
        payload = {
            "schema_version": "2.0",
            "generated_at": "2026-08-05T22:30:00+00:00",
            "root": "ROOT_A",
            "deps": [],
            "roots": [
                {"id": "ROOT_A", "deps": [
                    {"name": "propext", "file": None},
                    {"name": "Q3.A", "file": "Q3/A.lean"},
                ]},
                {"id": "ROOT_B", "deps": [
                    {"name": "Classical.choice", "file": None},
                    {"name": "Q3.B", "file": "Q3/B.lean"},
                ]},
            ],
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "deps.json"
            source.write_text(json.dumps(payload), encoding="utf-8")
            db_path = root / "observability.db"
            observability.rebuild_database(
                db_path,
                sources={"dependency_tree": source},
                generated_at="2026-08-05T22:30:00+00:00",
                source_commit="fixture",
            )
            conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
            rows = conn.execute(
                "SELECT root_id,COUNT(*) FROM axiom_dependency GROUP BY root_id ORDER BY root_id"
            ).fetchall()
            count = conn.execute(
                "SELECT record_count FROM source_state WHERE source_id='dependency_tree'"
            ).fetchone()[0]
            conn.close()
            self.assertEqual(rows, [("ROOT_A", 2), ("ROOT_B", 2)])
            self.assertEqual(count, 4)

    def test_failed_rebuild_preserves_previous_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            db_path = root / "observability.db"
            observability.rebuild_database(
                db_path,
                generated_at="2026-08-05T22:30:00+00:00",
                source_commit="fixture",
            )
            before = hashlib.sha256(db_path.read_bytes()).hexdigest()
            bad_timing = root / "bad_timing.md"
            block = """### bad

```yaml
transaction: DUP
wall_seconds: 1
```
"""
            bad_timing.write_text(block + "\n" + block, encoding="utf-8")
            sources = dict(observability.DEFAULT_SOURCES)
            sources["proshka_timing"] = bad_timing
            with self.assertRaisesRegex(ValueError, "duplicate timing transaction"):
                observability.rebuild_database(
                    db_path,
                    sources=sources,
                    generated_at="2026-08-05T22:31:00+00:00",
                    source_commit="fixture",
                )
            after = hashlib.sha256(db_path.read_bytes()).hexdigest()
            self.assertEqual(before, after)


if __name__ == "__main__":
    unittest.main()
