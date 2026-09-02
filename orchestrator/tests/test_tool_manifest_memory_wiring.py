"""Plants for the MANIFEST_V2 startup, retrieval, and durable-memory wiring."""

from __future__ import annotations

import importlib.util
import re
import sqlite3
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

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

    def test_autopilot_event_writer_is_registered_with_write_scope(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        tools = [
            tool
            for family in data["tool_families"].values()
            for tool in family.get("tools", [])
            if tool["id"] == "goal-event-writer"
        ]
        self.assertEqual(len(tools), 1)
        self.assertEqual(tools[0]["mode"], "WRITES_CANONICAL")
        self.assertTrue(tools[0]["writes"])
        self.assertIn("GOAL_SCOPED_OPERATIONAL_GRANT", tools[0]["approval"])
        self.assertEqual(
            set(tools[0]["records_to"]),
            {"knowledge.db", "q3.lean.aristotle/docs/INSIGHTS.md"},
        )

    def test_workflow_runtime_registers_review_plan_transport(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        tools = {
            tool["id"]: tool
            for family in data["tool_families"].values()
            for tool in family.get("tools", [])
        }
        runtime = tools["workflow-runtime"]
        alternatives = "\n".join(runtime["alternatives"])
        self.assertIn("workflow_runtime.py review-plan", alternatives)
        self.assertIn("--expected-sha256 <sha256>", alternatives)
        self.assertIn("review-plan byte-binding", runtime["validation"])
        self.assertEqual(runtime["mode"], "READ_ONLY")
        self.assertFalse(runtime["writes"])
        close_node = tools["workflow-close-node"]
        self.assertEqual(close_node["mode"], "WRITES_CANONICAL")
        self.assertTrue(close_node["writes"])
        self.assertIn("run --through close-node", close_node["invoke"])

    def test_production_plan_does_not_route_legacy_selectors_or_v9_gate(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        tools = {
            tool["id"]: tool
            for family in data["tool_families"].values()
            for tool in family.get("tools", [])
        }
        self.assertEqual(tools["routeb-status"]["status"], "AVAILABLE")
        self.assertIn("never calls", tools["routeb-status"]["trigger"])
        self.assertEqual(tools["goal-run-selector"]["status"], "AVAILABLE")
        self.assertIn("legacy-v9", tools["goal-run-selector"]["trigger"])

        from orchestrator import proof_loop

        routed = {
            tool
            for suppliers in proof_loop.TOOL_SUPPLIERS.values()
            for tool in suppliers
        }
        self.assertNotIn("goal-run-selector", routed)
        self.assertNotIn("three-body-loop", routed)

    def test_cross_host_operator_card_inventory_matches_manifest(self) -> None:
        manifest = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        expected = {
            tool["id"]
            for family in manifest["tool_families"].values()
            for tool in family.get("tools", [])
        }
        card = (
            REPO / "docs/Codex/CARD_CROSS_HOST_Q3_WORKFLOW_AND_TOOL_INVENTORY.md"
        ).read_text(encoding="utf-8")
        match = re.search(
            r"```yaml registered_tool_ids\n(.*?)\n```", card, flags=re.DOTALL
        )
        self.assertIsNotNone(match)
        registered = spine.yaml.safe_load(match.group(1))
        self.assertEqual(set(registered), expected)
        self.assertEqual(len(registered), len(set(registered)))

    def test_absence_event_routes_through_unified_supplier_preflight(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        self.assertEqual(
            data["memory_event_routes"]["ABSENCE_OR_NEW_OBJECT"]["run"],
            ["supplier-preflight"],
        )
        family = data["tool_families"]["retrieval_and_memory"]
        self.assertEqual(family["front_door"], "supplier-preflight")
        tools = {tool["id"]: tool for tool in family["tools"]}
        self.assertEqual(tools["supplier-preflight"]["mode"], "READ_ONLY")
        self.assertIn("EXACT_FIT", tools["supplier-preflight"]["outcomes"])

    def test_search_intent_literature_and_blueprint_v2_are_wired(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        self.assertEqual(
            data["memory_event_routes"]["LITERATURE_DISCOVERY"]["run"],
            ["literature-discovery"],
        )
        self.assertIn(
            "stdout only",
            data["memory_event_routes"]["LITERATURE_DISCOVERY"]["record"],
        )
        tools = {
            tool["id"]: tool
            for family in data["tool_families"].values()
            for tool in family.get("tools", [])
        }
        literature = tools["literature-discovery"]
        self.assertEqual(literature["classification"], "AUTOMATIC")
        self.assertEqual(literature["mode"], "NETWORK_WRITE")
        self.assertFalse(literature["writes"])
        self.assertIn("independently", literature["trigger"])
        self.assertIn("24 globally", literature["budgets"])
        writer = tools["workflow-search-evidence"]
        self.assertEqual(writer["classification"], "AUTOMATIC")
        self.assertEqual(writer["mode"], "WRITES_CANONICAL")
        self.assertTrue(writer["writes"])
        self.assertIn("EXACT_ORACLE_CARD_OWNERSHIP", writer["approval"])
        self.assertIn("q3_search_intent.v1", tools["semantic-preflight"]["search_intent_contract"])
        blueprint = tools["blueprint-skeleton-generator"]
        self.assertIn("q3_blueprint.v2", blueprint["authority"])
        self.assertIn("NODE_REGISTRY_V10", blueprint["trigger"])

    def test_blueprint_registry_declares_all_generated_outputs(self) -> None:
        registry = spine.yaml.safe_load(
            (REPO / "docs/cartographer/DERIVED_ARTIFACTS.yaml").read_text(encoding="utf-8")
        )
        artifact = next(
            row for row in registry["artifacts"]
            if row["id"] == "routeb-publication-blueprint"
        )
        self.assertEqual(len(artifact["outputs"]), 12)
        self.assertIn("orchestrator/state/NODE_REGISTRY_V10.json", artifact["inputs"])
        self.assertFalse(any("*.goal-close" in item for item in artifact["inputs"]))
        self.assertNotIn("docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md", artifact["inputs"])
        self.assertIn("selected_bus_goal_path", artifact["dynamic_inputs"]["selector"])

    def test_all_tools_have_one_explicit_routing_classification(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        allowed = {"AUTOMATIC", "MANUAL", "DISPLAY_ONLY", "RETIRED"}
        tools = [
            tool
            for family in data["tool_families"].values()
            for tool in family.get("tools", [])
        ]
        self.assertEqual(len(tools), 59)
        self.assertEqual(data["tool_contract"]["required_fields"][1], "classification")
        self.assertTrue(all(tool.get("classification") in allowed for tool in tools))
        self.assertTrue(all(
            (tool["classification"] == "RETIRED") == (tool["status"] == "RETIRED")
            for tool in tools
        ))
        self.assertEqual(
            data["memory_event_routes"]["GOAL_DISPATCH"]["run"],
            ["workflow-runtime"],
        )
        self.assertEqual(
            data["memory_event_routes"]["REGISTERED_CYCLE"]["run"],
            ["workflow-close-node"],
        )
        self.assertEqual(
            data["memory_event_routes"]["REUSABLE_INSIGHT"]["run"],
            ["workflow-close-node"],
        )
        self.assertEqual(
            data["memory_event_routes"]["GOAL_CLOSE"]["run"],
            ["workflow-close-node"],
        )

    def test_retrieval_contract_distinguishes_shelf_from_source_absence(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        tools = {
            tool["id"]: tool
            for tool in data["tool_families"]["retrieval_and_memory"]["tools"]
        }
        ask = tools["ask-shelf"]
        self.assertEqual(
            ask["outcomes"],
            [
                "HITS",
                "INCOMPLETE_FAST_REQUIRES_DEEP",
                "SHELF_ABSENCE",
                "INCOMPLETE",
            ],
        )
        self.assertIn("never rendered as global semantic absence", ask["note"])
        supplier = tools["supplier-preflight"]
        self.assertIn("SOURCE_DECLARATION_ABSENCE", supplier["failure_mode"])
        self.assertIn("only EXACT_FIT clears", supplier["failure_mode"])

    def test_retrieval_contract_has_bounded_zero_retry_qmd_queries(self) -> None:
        data = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        tools = {
            tool["id"]: tool
            for tool in data["tool_families"]["retrieval_and_memory"]["tools"]
        }
        budgets = tools["research-oracle"]["budgets"]
        self.assertIn("3 seconds", budgets)
        self.assertIn("15 seconds", budgets)
        self.assertIn("retries are zero", budgets)
        external = tools["semantic-preflight"]["external_search_contract"]
        self.assertIn("one monotonic-budget process", external)
        self.assertIn("uncapped exact explicit-source declaration lookup", external)

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
        self.assertIn("all enabled external Lean bases", proc.stdout)

    def test_fast_shelf_miss_requires_deep_and_never_claims_global_absence(self) -> None:
        proc = subprocess.run(
            ["./ask.sh", "q3_phasec_fast_absence_needle_91f6"],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=20,
        )
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
        self.assertIn("ASK_STATUS: INCOMPLETE_FAST_REQUIRES_DEEP", proc.stdout)
        self.assertNotIn("НЕ НАЙДЕНО НИГДЕ", proc.stdout)

    def test_spine_view_exposes_recent_branch_decisions(self) -> None:
        validated_gate = {
            "schema": "q3_semantic_quarantine.v1",
            "control_version": 9,
            "entries": [],
            "active_lease": None,
        }
        with mock.patch.object(
            spine._three_body_loop,
            "validate_historical_repository_gate",
            return_value=validated_gate,
        ):
            view = spine.build()
        self.assertIn("Recent branch decisions (Progress_Log.md)", view)
        self.assertIn("манифест соединён с обратным поиском", view)
        self.assertIn("q3_tool_manifest.v2", view)

    def test_control_routes_commands_to_live_manifest(self) -> None:
        control = (REPO / "docs" / "CODEX_CONTROL.md").read_text(encoding="utf-8")
        self.assertIn("CONTROL_VERSION: 10", control)
        self.assertIn("HONESTY_STATE: CHALLENGER_NOT_RH", control)
        self.assertIn("OWNER_ONLY_BOUNDARY: PX_RH_CLAIM", control)
        self.assertIn("scripts/supplier_preflight.py", control)
        self.assertIn("CODEX_LINUX", control)
        self.assertIn("GOAL_RUN", control)
        self.assertIn("GOAL_SCOPED_OPERATIONAL_GRANT", control)
        self.assertIn("docs/cartographer/TOOLS.yaml", control)
        self.assertIn("specs_docs/TOOLS_SPEC.md` is a historical", control)

    def test_session_start_is_manual_legacy_diagnostic_only(self) -> None:
        script = (REPO / "specs_docs" / "session_start.sh").read_text(encoding="utf-8")
        executable_lines = [
            line.strip()
            for line in script.splitlines()
            if line.strip() and not line.lstrip().startswith("#")
        ]
        self.assertTrue(
            any("DEPRECATED_LEGACY_V9_MAINTENANCE" in line for line in executable_lines)
        )
        self.assertFalse(
            any(
                re.match(
                    r"^(?:exec\s+)?python3\s+orchestrator/workflow_runtime\.py\b",
                    line,
                )
                for line in executable_lines
            )
        )
        self.assertNotIn("--shadow-v10", script)
        self.assertIn("git status --porcelain=v1 -uall", script)

    def test_session_entry_has_one_startup_front_door(self) -> None:
        entry = (
            REPO / "q3.lean.aristotle" / "ACTIVE" / "SESSION_ENTRY.md"
        ).read_text(encoding="utf-8")
        startup = entry.split("## Как читать plan", 1)[0]
        self.assertEqual(
            startup.count("python3 orchestrator/workflow_runtime.py plan"), 1
        )
        self.assertNotIn("--shadow-v10", startup)
        self.assertIn("ручной legacy-диагностический", startup)

    def test_bootstrap_does_not_require_large_preplan_manual_reads(self) -> None:
        control = (REPO / "docs/CODEX_CONTROL.md").read_text(encoding="utf-8")
        header = control.split("```", 2)[1]
        self.assertNotIn("COGNITIVE_OPERATORS.md", header)

        entry = (
            REPO / "q3.lean.aristotle" / "ACTIVE" / "SESSION_ENTRY.md"
        ).read_text(encoding="utf-8")
        preplan = entry.split("python3 orchestrator/workflow_runtime.py plan", 1)[0]
        self.assertNotIn("COGNITIVE_OPERATORS.md", preplan)
        self.assertNotIn("docs/cartographer/TOOLS.yaml", preplan)

        manifest = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        order = manifest["startup_contract"]["order"]
        self.assertNotIn("q3.lean.aristotle/COGNITIVE_OPERATORS.md", order)
        self.assertNotIn("docs/cartographer/TOOLS.yaml", order)

    def test_v9_transport_is_available_historical_compatibility_only(self) -> None:
        manifest = spine.yaml.safe_load(
            (REPO / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")
        )
        tools = {
            tool["id"]: tool
            for family in manifest["tool_families"].values()
            for tool in family.get("tools", [])
        }
        for tool_id in ("three-body-loop", "semantic-attestation-broker"):
            tool = tools[tool_id]
            self.assertEqual(tool["status"], "AVAILABLE")
            self.assertEqual(tool["mode"], "READ_ONLY")
            self.assertFalse(tool["writes"])
            contract = " ".join(
                str(tool.get(key, ""))
                for key in ("trigger", "approval", "authority", "validation")
            )
            self.assertIn("v9", contract.lower())
            self.assertIn("histor", contract.lower())
            self.assertIn("v10", contract.lower())
        self.assertEqual(tools["semantic-admit"]["status"], "RETIRED")
        self.assertEqual(tools["codex-watch-read-only"]["status"], "RETIRED")

    def test_routeb_conductor_names_control_v10_and_bare_front_door(self) -> None:
        conductor = (
            REPO / ".agents/skills/routeb-conductor/SKILL.md"
        ).read_text(encoding="utf-8")
        self.assertIn("Control v10", conductor)
        self.assertIn("python3 orchestrator/workflow_runtime.py plan", conductor)
        self.assertNotIn("--shadow-v10", conductor)

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

    def test_routeb_declaration_catalog_reports_document_coverage_honestly(self) -> None:
        proc = subprocess.run(
            ["python3", "orchestrator/backfill_db.py", "--check"],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=20,
        )
        self.assertIn("Missing declaration rows: 0", proc.stdout)
        self.assertIn("Stale declaration rows: 0", proc.stdout)
        missing_docs = next(
            int(line.rsplit(":", 1)[1])
            for line in proc.stdout.splitlines()
            if line.startswith("Missing document rows:")
        )
        self.assertEqual(proc.returncode, 0 if missing_docs == 0 else 1)
        if missing_docs:
            self.assertIn("MISSING_DOC", proc.stdout)
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
