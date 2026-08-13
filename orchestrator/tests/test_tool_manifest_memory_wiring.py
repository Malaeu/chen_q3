"""Plants for the MANIFEST_V2 startup, retrieval, and durable-memory wiring."""

from __future__ import annotations

import importlib.util
import sqlite3
import subprocess
import tempfile
import unittest
from pathlib import Path

from orchestrator import kb_migrate_progress_log, spine, tools_census

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
    def test_manifest_schema_contract_and_repo_authority(self) -> None:
        data = spine.validate_tool_manifest()
        self.assertEqual(data["schema"], "q3_tool_manifest.v2")
        self.assertGreaterEqual(data["family_count"], 6)
        self.assertGreaterEqual(data["tool_count"], 20)
        self.assertGreaterEqual(data["writer_count"], 8)
        self.assertRegex(str(data["sha256"]), r"^[0-9a-f]{64}$")

    def test_codex_cartography_routes_only_to_repo_local_tools(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        family = data["tool_families"]["cartography_and_property_descent"]
        codex_tools = [
            tool for tool in family["tools"]
            if "CODEX" in tool["audience"] and tool["mode"] != "EXTERNAL"
        ]
        declared = [
            str(path)
            for tool in codex_tools
            for path in ([tool["path"]] if "path" in tool else tool["paths"])
        ]
        self.assertTrue(declared)
        self.assertTrue(all(path.startswith("docs/cartographer/") for path in declared))
        self.assertFalse(any("codex_specs" in path for path in declared))

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
        self.assertFalse(any("/.lake/" in rel for rel in rels))

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

    def test_ask_shelf_multiword_query_does_not_false_negative_live_lean(self) -> None:
        proc = subprocess.run(
            ["./ask.sh", "SelectedTrialNormalizerBounded", "uniform", "lower", "bound"],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=20,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("SelectedTrialNormalizerBounded", proc.stdout)
        self.assertNotIn("НЕ НАЙДЕНО НИГДЕ", proc.stdout)

    def test_spine_view_exposes_recent_branch_decisions(self) -> None:
        view = spine.build()
        self.assertIn("Recent branch decisions (Progress_Log.md)", view)
        self.assertIn("манифест соединён с обратным поиском", view)
        self.assertIn("q3_tool_manifest.v2", view)

    def test_control_routes_commands_to_live_manifest(self) -> None:
        control = (REPO / "docs" / "CODEX_CONTROL.md").read_text(encoding="utf-8")
        self.assertIn("CONTROL_VERSION: 6", control)
        self.assertIn("CODEX_LINUX", control)
        self.assertIn("GOAL_RUN", control)
        self.assertIn("GOAL_SCOPED_OPERATIONAL_GRANT", control)
        self.assertIn("docs/cartographer/TOOLS.yaml", control)
        self.assertIn("specs_docs/TOOLS_SPEC.md` is a historical", control)

    def test_session_start_counts_untracked_files_individually(self) -> None:
        script = (REPO / "specs_docs" / "session_start.sh").read_text(encoding="utf-8")
        self.assertIn("git status --porcelain=v1 -uall", script)

    def test_session_entry_has_one_startup_front_door(self) -> None:
        entry = (
            REPO / "q3.lean.aristotle" / "ACTIVE" / "SESSION_ENTRY.md"
        ).read_text(encoding="utf-8")
        startup = entry.split("## Карта знаний по триггеру", 1)[0]
        self.assertIn("bash specs_docs/session_start.sh", startup)
        self.assertNotIn(
            "python3 orchestrator/spine.py --strict --stdout --reason session-start",
            startup,
        )

    def test_tool_census_help_does_not_run_the_census(self) -> None:
        proc = subprocess.run(
            ["python3", "orchestrator/tools_census.py", "--help"],
            cwd=REPO, capture_output=True, text=True, timeout=3,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("usage: tools_census.py", proc.stdout)
        self.assertNotIn("wrote", proc.stdout)

    def test_tool_census_excludes_rebuildable_and_exhaust_trees(self) -> None:
        self.assertTrue({"venv_djo", "aristotle_output"} <= tools_census.SKIP_DIRS)

    def test_tool_census_does_not_call_tests_migrations_or_goal_probes_tools(self) -> None:
        self.assertEqual(
            tools_census.classify(Path("orchestrator/tests/test_spine.py")), "TEST"
        )
        self.assertEqual(
            tools_census.classify(Path("orchestrator/kb_migrate_moves.py")), "MIGRATION"
        )
        self.assertEqual(
            tools_census.classify(
                Path("docs/routeB_bus/phase4_scripts/glower_beta_cocycle_check.py")
            ),
            "PROBE",
        )

    def test_routeb_declaration_catalog_is_synchronized(self) -> None:
        proc = subprocess.run(
            ["python3", "orchestrator/backfill_db.py", "--check"],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=20,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("Missing declaration rows: 0", proc.stdout)
        self.assertIn("Stale declaration rows: 0", proc.stdout)
        spine_source = (REPO / "orchestrator" / "spine.py").read_text(encoding="utf-8")
        self.assertIn('"orchestrator/backfill_db.py", "--sync"', spine_source)
        self.assertIn('"docs/cartographer/atoms_RouteB.json"', spine_source)

    def test_optional_erdos_refresh_never_forces_all_qmd_embeddings(self) -> None:
        script = (
            REPO / "q3.lean.aristotle" / "scripts" / "refresh_erdos_overlap_kb.py"
        ).read_text(encoding="utf-8")
        self.assertIn("STABLE_STAGE_ROOT", script)
        self.assertNotIn('run_qmd([qmd, "embed", "-f"])', script)

    def test_proshka_tight_pack_uses_live_repo_paths(self) -> None:
        proc = subprocess.run(
            ["python3", "scripts/build_proshka_brief.py", "--mode", "tight"],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=20,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        execution_state_path = (
            "File: q3.lean.aristotle/ACTIVE/requests/"
            "routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
        )
        self.assertIn(execution_state_path, proc.stdout)
        self.assertNotIn(
            "File: docs/routeB_bus/057_unified_chain_program_delegated_review.goal.md",
            proc.stdout,
        )
        self.assertIn(
            "File: docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md",
            proc.stdout,
        )
        self.assertNotIn("File: full/q3.lean.aristotle", proc.stdout)


if __name__ == "__main__":
    unittest.main()
