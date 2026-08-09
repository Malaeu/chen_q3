"""Plants for the MANIFEST_V2 startup, retrieval, and durable-memory wiring."""

from __future__ import annotations

import importlib.util
import sqlite3
import subprocess
import tempfile
import unittest
from pathlib import Path

from orchestrator import kb_migrate_progress_log, spine


REPO = Path(__file__).resolve().parents[2]


def load_refresh_module():
    path = REPO / "q3.lean.aristotle" / "scripts" / "refresh_q3_docs.py"
    spec = importlib.util.spec_from_file_location("refresh_q3_docs_under_test", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load refresh_q3_docs.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ToolManifestMemoryPlants(unittest.TestCase):
    def test_manifest_schema_contract_and_mirror(self) -> None:
        data = spine.validate_tool_manifest()
        self.assertEqual(data["schema"], "q3_tool_manifest.v2")
        self.assertGreaterEqual(data["family_count"], 6)
        self.assertGreaterEqual(data["tool_count"], 20)
        self.assertGreaterEqual(data["writer_count"], 8)
        self.assertRegex(str(data["sha256"]), r"^[0-9a-f]{64}$")

    def test_q3_docs_contains_branch_memory_and_excludes_claude_policy(self) -> None:
        refresh = load_refresh_module()
        rels = {str(path.relative_to(REPO)) for path in refresh.collect_sources()}
        required = {
            "docs/GENEALOGY.md",
            "docs/Progress_Log.md",
            "docs/RECORDING_RULES.md",
            "docs/GLOSSARY.md",
            "docs/cartographer/TOOLS.yaml",
        }
        self.assertTrue(required <= rels)
        self.assertNotIn("q3.lean.aristotle/CLAUDE.md", rels)

    def test_progress_log_parser_requires_and_reads_branch_fields(self) -> None:
        rows = kb_migrate_progress_log.parse_entries()
        self.assertGreaterEqual(len(rows), 6)
        self.assertTrue(all(row["kind"] == "branch_decision" for row in rows))
        self.assertTrue(all(row["target"] and row["boundary"] for row in rows))
        self.assertTrue(any(row["channel"] == "external" for row in rows))

    def test_progress_log_parser_fails_on_incomplete_branch(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Progress_Log.md"
            path.write_text(
                "## 2026-08-09 — incomplete\n\n"
                "**Развилка:** A или B\n\n"
                "**Выбрали:** A\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "missing fields"):
                kb_migrate_progress_log.parse_entries(path)

    def test_progress_log_projection_is_idempotent(self) -> None:
        rows = kb_migrate_progress_log.parse_entries()
        with tempfile.TemporaryDirectory() as td:
            db = Path(td) / "knowledge.db"
            conn = sqlite3.connect(db)
            conn.executescript(
                """
                CREATE TABLE journal_entry (
                  id TEXT PRIMARY KEY, date TEXT, kind TEXT, title TEXT,
                  workstream TEXT, state TEXT, channel TEXT, target TEXT,
                  validation TEXT, artifact_sha TEXT, boundary TEXT,
                  next_target TEXT, body TEXT, source_file TEXT NOT NULL
                );
                CREATE TABLE source_ledger (
                  source_file TEXT PRIMARY KEY, expected_rows INTEGER NOT NULL,
                  migrated_at TEXT NOT NULL, note TEXT
                );
                CREATE VIRTUAL TABLE journal_fts USING fts5(
                  title, body, target, boundary,
                  content='journal_entry', content_rowid='rowid'
                );
                """
            )
            kb_migrate_progress_log.migrate(conn, rows)
            kb_migrate_progress_log.migrate(conn, rows)
            count = conn.execute(
                "SELECT COUNT(*) FROM journal_entry WHERE kind='branch_decision'"
            ).fetchone()[0]
            ledger = conn.execute(
                "SELECT expected_rows FROM source_ledger WHERE source_file=?",
                (kb_migrate_progress_log.SOURCE_FILE,),
            ).fetchone()[0]
            searchable = conn.execute(
                "SELECT COUNT(*) FROM journal_fts WHERE journal_fts MATCH 'манифест'"
            ).fetchone()[0]
            conn.close()
        self.assertEqual(count, len(rows))
        self.assertEqual(ledger, len(rows))
        self.assertGreaterEqual(searchable, 1)

    def test_ask_shelf_finds_branch_rationale(self) -> None:
        proc = subprocess.run(
            ["./ask.sh", "манифест соединён с обратным поиском"],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=20,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("docs/Progress_Log.md", proc.stdout)

    def test_spine_view_exposes_recent_branch_decisions(self) -> None:
        view = spine.build()
        self.assertIn("Recent branch decisions (Progress_Log.md)", view)
        self.assertIn("манифест соединён с обратным поиском", view)
        self.assertIn("q3_tool_manifest.v2", view)

    def test_control_routes_commands_to_live_manifest(self) -> None:
        control = (REPO / "docs" / "CODEX_CONTROL.md").read_text(encoding="utf-8")
        self.assertIn("CONTROL_VERSION: 4", control)
        self.assertIn("docs/cartographer/TOOLS.yaml", control)
        self.assertIn("specs_docs/TOOLS_SPEC.md` is a historical", control)

    def test_session_start_counts_untracked_files_individually(self) -> None:
        script = (REPO / "specs_docs" / "session_start.sh").read_text(encoding="utf-8")
        self.assertIn("git status --porcelain=v1 -uall", script)


if __name__ == "__main__":
    unittest.main()
