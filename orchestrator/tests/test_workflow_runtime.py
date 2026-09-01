from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from orchestrator import workflow_runtime
from orchestrator.startup_runtime import StartupSnapshot


def tool_index() -> dict[str, dict[str, object]]:
    ids = set(workflow_runtime.COMMON_TOOLS)
    for values in workflow_runtime.ACTION_TOOLS.values():
        ids.update(values)
    return {
        item: {
            "id": item,
            "status": "ENABLED",
            "mode": "READ_ONLY",
            "writes": False,
        }
        for item in ids
    }


def plan(action: str, *, host: str = "CODEX_MAC", tools=None):
    return workflow_runtime.compile_plan(
        goal_binding={"action": action, "selected_goal_id": "058"},
        selector_hold=None,
        tool_index=tools or tool_index(),
        derived_status=[{"artifact_id": "inventory", "status": "FRESH"}],
        assembly_debt=["CHAIN:4:OPEN"],
        owned_dirty=[],
        foreign_dirty=["foreign.txt"],
        fingerprints={"control": "abc"},
        host_executor=host,
        through="close-node",
    )


PHASE_KEY = {
    "route_id": "ROUTE_B",
    "front_id": "FRONT",
    "source_object_family_id": "SOURCE",
    "terminal_consumer_id": "CONSUMER",
    "honesty_state": "CHALLENGER_NOT_RH",
    "convention_lock_id": "LOCK",
}


def exploration_runtime(*, no_progress_streak: int = 6, review_count: int = 0):
    return {
        "schema": "q3_channel_runtime.v1",
        "control_status": "ACTIVE",
        "active_proshka_phase": {
            "status": "ACTIVE",
            "phase_id": "PHASE-1",
            "phase_key": PHASE_KEY,
            "conversation_id": "living-chat",
        },
        "active_exploration": {
            "exploration_id": "EXP-1",
            "phase_key": PHASE_KEY,
            "blocker_fingerprint": "b" * 64,
            "candidates": [],
            "cycles": [],
            "no_progress_streak": no_progress_streak,
            "total_cycles": 6,
            "active_reasoning_seconds": 0,
            "proshka_review_count": review_count,
        },
        "last_exploration_close": None,
        "mathematical_authority_mode": "CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM",
        "px_rh_claim_state": "NOT_READY",
        "operational_action_pending": None,
        "meter": {
            "phases_opened": 1,
            "fresh_chats_opened": 1,
            "delegated_strategic_review_calls": 0,
            "exploration_review_calls": review_count,
            "px_rh_claim_requests": 0,
            "ordinary_goal_close_calls": 0,
            "mathematical_owner_deferral_violations": 0,
            "fanout_violations": 0,
            "forced_rollovers": 0,
        },
    }


def dependency_contract() -> dict[str, object]:
    return {
        "original_requested_object": "Q3.RouteB.candidate",
        "downstream_consumer": "Q3.RouteB.target",
        "actual_consumer_requirement": "the exact target type",
        "consumer_implication": "the candidate directly inhabits the target type",
        "weaker_interface_probe": "check a weaker declaration against the same target",
        "original_object_is": "UNKNOWN",
        "necessity_evidence": [],
        "known_weaker_interfaces": ["a declaration with the same target type"],
        "failure_type": "NO_SOURCE",
        "failure_scope": "current supplier shelf only",
        "epistemic_status": "RESEARCH_DEBT",
        "death_evidence": [],
        "reopen_triggers": ["NEW_SOURCE"],
    }


def shadow_snapshot(**overrides: object) -> StartupSnapshot:
    fields: dict[str, object] = {
        "schema": "q3_startup_snapshot.v10.shadow.v1",
        "mode": "SHADOW_NOT_AUTHORITY",
        "control_sha256": "a" * 64,
        "control_version": 9,
        "control_status": "ACTIVE",
        "git_head": "b" * 40,
        "git_origin_head": "b" * 40,
        "git_tree": "c" * 40,
        "git_dirty": False,
        "selected_goal": "docs/routeB_bus/058.goal.md",
        "honesty_state": "CHALLENGER_NOT_RH",
        "exact_node_pin": "NODE-058",
        "exact_source_pin": "SOURCE-058",
        "exact_theorem_pin": "THEOREM-058",
        "exact_consumer_pin": "CONSUMER-058",
        "fatal_errors": [],
        "blocked_features": ("RUN", "DISPATCH", "MINT", "STATE_WRITE"),
        "warnings": [],
        "next_action": "READ_ONLY_OBSERVE",
        "run_authorized": False,
    }
    fields.update(overrides)
    return StartupSnapshot(**fields)


def node_registry_summary(*, status: str = "PASS") -> dict[str, object]:
    return {
        "schema": "q3_node_registry_gate_summary.v1",
        "status": status,
        "code": "PASS" if status == "PASS" else "NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID",
        "registry_hash": "d" * 64,
        "node_count": 2,
        "edge_count": 1,
        "historical_v9_unmapped": 0,
        "consumption_status": "SCOPED_PASS",
    }


class WorkflowRuntimePlants(unittest.TestCase):
    def _review_fixture(
        self,
        repo: Path,
        *,
        call_class: str | None,
        packet_subtype: str | None = None,
        runtime: dict | None = None,
    ) -> tuple[Path, str, str]:
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
        subprocess.run(
            ["git", "config", "user.email", "plant@example.invalid"],
            cwd=repo,
            check=True,
        )
        subprocess.run(["git", "config", "user.name", "Workflow Plant"], cwd=repo, check=True)
        lines = ["REQUEST_ID: REQ-PLANT", "BOUNDARY_ID: boundary"]
        if packet_subtype is not None:
            lines.append(f"PACKET_SUBTYPE: {packet_subtype}")
        if call_class is not None:
            lines.append(f"CALL_CLASS: {call_class}")
        lines.append("exact request")
        request = repo / "request.txt"
        request.write_text("\n".join(lines) + "\n", encoding="utf-8")
        queue = repo / "docs/routeB_bus/PROSHKA_QUEUE.md"
        queue.parent.mkdir(parents=True)
        queue.write_text("## REQ-PLANT · plant\n\n- `STATUS: OPEN`\n", encoding="utf-8")
        runtime_path = repo / "orchestrator/state/CHANNEL_RUNTIME.json"
        runtime_path.parent.mkdir(parents=True)
        runtime_path.write_text(
            json.dumps(runtime or exploration_runtime()) + "\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "."], cwd=repo, check=True)
        subprocess.run(["git", "commit", "-qm", "plant"], cwd=repo, check=True)
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=repo, check=True,
            capture_output=True, text=True,
        ).stdout.strip()
        digest = workflow_runtime.hashlib.sha256(request.read_bytes()).hexdigest()
        return request, commit, digest

    def test_three_closure_shapes_compile_without_second_selector(self) -> None:
        exact = plan("SELECT_EXACT_GOAL")
        mint = plan("MINT_READY")
        phase = plan("PHASE_TRANSITION_REQUIRED")
        self.assertEqual([exact["status"], mint["status"], phase["status"]], ["READY"] * 3)
        self.assertIn(
            "workflow-session-close",
            [item["id"] for item in exact["logical_plan"]["selected_tools"]],
        )
        self.assertIn(
            "workflow-phase-close",
            [item["id"] for item in phase["logical_plan"]["selected_tools"]],
        )
        self.assertFalse(exact["logical_plan"]["proshka"]["dispatch_performed"])
        self.assertEqual(
            exact["logical_plan"]["proshka"]["transport_owner"],
            "CURRENT_CODEX_BODY",
        )
        self.assertFalse(
            exact["logical_plan"]["proshka"]["repository_owner_confirmation_required"]
        )
        self.assertIsNone(exact["logical_plan"]["proshka"]["eligible_class"])
        self.assertEqual(
            phase["logical_plan"]["proshka"]["eligible_class"],
            "DELEGATED_STRATEGIC_REVIEW",
        )
        loop = exact["logical_plan"]["proof_loop"]
        self.assertEqual(loop["schema"], "q3_proof_loop.v1")
        self.assertEqual(loop["mode"], "CONSUMER_FIRST")
        self.assertEqual(loop["next_joint"]["status"], "CONTRACT_REQUIRED")
        self.assertTrue(loop["recompute_after_close"])
        self.assertEqual(loop["PX_RH_CLAIM"], "NOT_MADE")
        self.assertEqual(
            loop["roof_port_ledger"]["proof_percentage_interpretation"],
            "REJECTED",
        )

    def test_invalid_roof_ledger_holds_runtime_fail_closed(self) -> None:
        result = workflow_runtime.compile_plan(
            goal_binding={"action": "SELECT_EXACT_GOAL"},
            selector_hold=None,
            tool_index=tool_index(),
            derived_status=[{"artifact_id": "inventory", "status": "FRESH"}],
            assembly_debt=[],
            owned_dirty=[],
            foreign_dirty=[],
            fingerprints={},
            host_executor="CODEX_MAC",
            roof_ledger_snapshot={
                "integrity_status": "INVALID",
                "integrity_reasons": ["ROOF_SIGNATURE_DRIFT"],
            },
        )
        self.assertEqual(result["status"], "HOLD")
        self.assertIn(
            "ROOF_PORT_LEDGER_INVALID:ROOF_SIGNATURE_DRIFT", result["holds"]
        )

    def test_host_changes_executor_not_logical_plan(self) -> None:
        mac = plan("SELECT_EXACT_GOAL", host="CODEX_MAC")
        linux = plan("SELECT_EXACT_GOAL", host="CODEX_LINUX")
        self.assertEqual(mac["logical_plan"], linux["logical_plan"])
        self.assertNotEqual(mac["host_executor"], linux["host_executor"])

    def test_missing_tool_and_dirty_derived_artifact_hold_fail_closed(self) -> None:
        tools = tool_index()
        del tools["lean-validation"]
        result = workflow_runtime.compile_plan(
            goal_binding={"action": "SELECT_EXACT_GOAL"},
            selector_hold=None,
            tool_index=tools,
            derived_status=[{"artifact_id": "routeb-inventory", "status": "STALE"}],
            assembly_debt=[],
            owned_dirty=[],
            foreign_dirty=[],
            fingerprints={},
            host_executor="CODEX_MAC",
        )
        self.assertEqual(result["status"], "HOLD")
        self.assertIn("REQUIRED_TOOL_UNREGISTERED:lean-validation", result["holds"])
        self.assertIn("DERIVED_ARTIFACT_NOT_FRESH:routeb-inventory:STALE", result["holds"])
        self.assertEqual(
            result["logical_plan"]["proof_loop"]["next_joint"]["status"],
            "BLOCKED",
        )
        self.assertIsNone(
            result["logical_plan"]["proof_loop"]["next_joint"]["address"]
        )

    def test_repeated_plan_is_identical_and_never_claims_delivery(self) -> None:
        first = plan("SELECT_EXACT_GOAL")
        second = plan("SELECT_EXACT_GOAL")
        self.assertEqual(first, second)
        logical = first["logical_plan"]
        self.assertEqual(logical["expected_writes"], [])
        self.assertFalse(logical["scoped_delivery"]["performed"])
        self.assertFalse(logical["scoped_delivery"]["repository_owner_confirmation_required"])
        self.assertEqual(logical["PX_RH_CLAIM"], "NOT_MADE")
        self.assertEqual(logical["foreign_dirty_preserved"], ["foreign.txt"])

    def test_shadow_v10_builds_one_snapshot_and_reuses_selected_goal(self) -> None:
        snapshot = shadow_snapshot()
        with (
            mock.patch.object(
                workflow_runtime, "build_shadow_snapshot", return_value=snapshot
            ) as build,
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "startup_gate_summary",
                return_value=node_registry_summary(),
            ) as registry,
        ):
            result = workflow_runtime.live_shadow_plan_v10(
                Path("/repo"), owned_paths=["owned.md"]
            )
        build.assert_called_once_with(Path("/repo"), owned_paths=("owned.md",))
        registry.assert_called_once_with(
            Path("/repo"),
            snapshot.selected_goal,
            owned_paths=("owned.md",),
            exact_node_pin=snapshot.exact_node_pin,
            exact_theorem_pin=snapshot.exact_theorem_pin,
            exact_consumer_pin=snapshot.exact_consumer_pin,
        )
        self.assertEqual(result["schema"], "q3_workflow_plan.v2")
        self.assertEqual(result["selected_goal"], snapshot.selected_goal)
        self.assertFalse(result["run_authorized"])
        self.assertFalse(result["writes_performed"])

    def test_shadow_v10_hot_path_never_enters_legacy_or_subprocess_startup(self) -> None:
        snapshot = shadow_snapshot()
        with (
            mock.patch.object(
                workflow_runtime, "build_shadow_snapshot", return_value=snapshot
            ),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "startup_gate_summary",
                return_value=node_registry_summary(),
            ),
            mock.patch.object(
                workflow_runtime.subprocess,
                "run",
                side_effect=AssertionError("shadow hot path invoked subprocess"),
            ),
            mock.patch.object(
                workflow_runtime, "startup_receipt", side_effect=AssertionError
            ),
            mock.patch.object(
                workflow_runtime, "selector_binding", side_effect=AssertionError
            ),
        ):
            result = workflow_runtime.live_shadow_plan_v10(Path("/repo"), owned_paths=[])
        self.assertEqual(result["status"], "READY")
        self.assertEqual(
            result["startup"]["blocked_features"],
            ["RUN", "DISPATCH", "MINT", "STATE_WRITE"],
        )
        self.assertEqual(result["holds"], [])

    def test_shadow_v10_cli_imports_no_legacy_runtime_modules(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        entry = repo / "orchestrator/workflow_runtime.py"
        blocked = (
            "orchestrator.proof_loop",
            "orchestrator.roof_port_ledger",
            "orchestrator.session_briefing",
            "orchestrator.spine",
            "orchestrator.three_body_loop",
            "specs_docs.phase_close",
            "specs_docs.session_close",
        )
        program = (
            "import runpy,sys\n"
            f"blocked={blocked!r}\n"
            "for name in blocked: sys.modules[name] = None\n"
            f"sys.argv=[{str(entry)!r},'--root',{str(repo)!r},'plan','--shadow-v10']\n"
            f"runpy.run_path({str(entry)!r}, run_name='__main__')\n"
        )

        proc = subprocess.run(
            [sys.executable, "-c", program],
            cwd=repo,
            check=False,
            capture_output=True,
            text=True,
        )

        self.assertIn(proc.returncode, {0, 2}, proc.stderr)
        self.assertNotIn("ModuleNotFoundError", proc.stderr)
        payload = json.loads(proc.stdout)
        self.assertEqual(payload["schema"], "q3_workflow_plan.v2")
        self.assertFalse(payload["run_authorized"])

    def test_compile_plan_imports_proof_loop_only_on_legacy_call(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        blocked = (
            "orchestrator.proof_loop",
            "orchestrator.spine",
            "orchestrator.three_body_loop",
        )
        program = (
            "import json,sys\n"
            "from orchestrator import workflow_runtime\n"
            f"blocked={blocked!r}\n"
            "before={name:name in sys.modules for name in blocked}\n"
            "ids=set(workflow_runtime.COMMON_TOOLS)\n"
            "for values in workflow_runtime.ACTION_TOOLS.values(): ids.update(values)\n"
            "tools={item:{'id':item,'status':'ENABLED','mode':'READ_ONLY',"
            "'writes':False} for item in ids}\n"
            "result=workflow_runtime.compile_plan("
            "goal_binding={'action':'SELECT_EXACT_GOAL'},selector_hold=None,"
            "tool_index=tools,derived_status=[],assembly_debt=[],owned_dirty=[],"
            "foreign_dirty=[],fingerprints={},host_executor='CODEX_LINUX')\n"
            "after={name:name in sys.modules for name in blocked}\n"
            "print(json.dumps({'before':before,'after':after,"
            "'schema':result['schema']}))\n"
        )

        proc = subprocess.run(
            [sys.executable, "-c", program],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        )

        payload = json.loads(proc.stdout)
        self.assertEqual(payload["schema"], "q3_workflow_plan.v1")
        self.assertFalse(payload["before"]["orchestrator.proof_loop"])
        self.assertTrue(payload["after"]["orchestrator.proof_loop"])
        self.assertFalse(payload["after"]["orchestrator.spine"])
        self.assertFalse(payload["after"]["orchestrator.three_body_loop"])

    def test_shadow_v10_partial_physical_pins_stay_scoped_hold(self) -> None:
        snapshot = shadow_snapshot(
            exact_theorem_pin=None,
            exact_consumer_pin=None,
            blocked_features=(
                "BLOCKED_FEATURE:EXACT_THEOREM_EDGE_UNSELECTED",
                "BLOCKED_FEATURE:EXACT_CONSUMER_EDGE_UNSELECTED",
                "RUN",
                "DISPATCH",
                "MINT",
                "STATE_WRITE",
            ),
        )
        summary = node_registry_summary(status="HOLD")
        summary["code"] = "NODE_REGISTRY_EXACT_EDGE_REQUIRED"
        with (
            mock.patch.object(
                workflow_runtime, "build_shadow_snapshot", return_value=snapshot
            ),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "startup_gate_summary",
                return_value=summary,
            ) as registry,
        ):
            result = workflow_runtime.live_shadow_plan_v10(
                Path("/repo"), owned_paths=[]
            )

        registry.assert_called_once_with(
            Path("/repo"),
            snapshot.selected_goal,
            owned_paths=(),
            exact_node_pin=None,
            exact_theorem_pin=None,
            exact_consumer_pin=None,
        )
        self.assertEqual(result["status"], "HOLD")
        self.assertEqual(
            result["node_registry"]["code"], "NODE_REGISTRY_EXACT_EDGE_REQUIRED"
        )

    def test_shadow_v10_output_is_bounded_and_never_authorizes_run(self) -> None:
        result = workflow_runtime.compile_shadow_plan_v10(
            startup_snapshot=shadow_snapshot(
                warnings=["w" * 500] * 20,
                blocked_features=["blocked"],
            ),
            node_registry_summary=node_registry_summary(status="HOLD"),
            host_executor="CODEX_LINUX",
        )
        rendered = workflow_runtime.render_shadow_plan_v10(result)
        startup_rendered = json.dumps(
            result["startup"], ensure_ascii=False, indent=2, sort_keys=True
        )
        self.assertLessEqual(len(rendered.encode("utf-8")), 8 * 1024)
        self.assertLessEqual(len(rendered.splitlines()), 150)
        self.assertLessEqual(len(startup_rendered.encode("utf-8")), 4 * 1024)
        self.assertLessEqual(len(startup_rendered.splitlines()), 60)
        self.assertFalse(result["run_authorized"])
        self.assertEqual(result["status"], "HOLD")
        self.assertEqual(result["startup"]["warnings_omitted"], 12)
        self.assertIn(
            {
                "feature": "RUN_CLOSE_NODE",
                "scope": "NODE_REGISTRY_V10_CONSUMPTION",
                "code": "NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID",
            },
            result["blocked_features"],
        )

    def test_shadow_v10_preserves_validation_required_as_scoped_hold(self) -> None:
        registry = node_registry_summary(status="VALIDATION_REQUIRED")
        registry["code"] = "NODE_REGISTRY_COMMITTED_VALIDATION_STALE"
        result = workflow_runtime.compile_shadow_plan_v10(
            startup_snapshot=shadow_snapshot(),
            node_registry_summary=registry,
            host_executor="CODEX_LINUX",
        )
        self.assertEqual(result["status"], "HOLD")
        self.assertEqual(result["holds"], [])
        self.assertEqual(result["node_registry"]["status"], "VALIDATION_REQUIRED")
        self.assertIn(
            {
                "feature": "RUN_CLOSE_NODE",
                "scope": "NODE_REGISTRY_V10_CONSUMPTION",
                "code": "NODE_REGISTRY_COMMITTED_VALIDATION_STALE",
            },
            result["blocked_features"],
        )

    def test_shadow_v10_rejects_malformed_snapshot_and_registry_identity(self) -> None:
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError,
            "SHADOW_V10_STARTUP_SNAPSHOT_INVALID",
        ):
            workflow_runtime.compile_shadow_plan_v10(
                startup_snapshot=shadow_snapshot(mode="BATTLE_V10"),
                node_registry_summary=node_registry_summary(),
                host_executor="CODEX_LINUX",
            )
        malformed = node_registry_summary()
        malformed["schema"] = "q3_node_registry_gate_summary.v0"
        result = workflow_runtime.compile_shadow_plan_v10(
            startup_snapshot=shadow_snapshot(),
            node_registry_summary=malformed,
            host_executor="CODEX_LINUX",
        )
        self.assertEqual(result["status"], "FATAL")
        self.assertIn("NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID", result["holds"])

    def test_default_plan_cli_remains_on_legacy_v9_path(self) -> None:
        legacy = {"schema": "q3_workflow_plan.v1", "status": "READY"}
        argv = ["workflow_runtime.py", "--root", "/repo", "plan"]
        with (
            mock.patch.object(workflow_runtime.sys, "argv", argv),
            mock.patch.object(workflow_runtime, "live_plan", return_value=legacy) as live,
            mock.patch.object(
                workflow_runtime,
                "live_shadow_plan_v10",
                side_effect=AssertionError("default plan entered shadow"),
            ),
            mock.patch("builtins.print") as emit,
        ):
            status = workflow_runtime.main()
        self.assertEqual(status, 0)
        live.assert_called_once()
        emit.assert_called_once_with(
            json.dumps(legacy, ensure_ascii=False, indent=2, sort_keys=True)
        )

    def test_shadow_v10_close_node_cannot_enter_startup_or_deep_gate(self) -> None:
        shadow = workflow_runtime.compile_shadow_plan_v10(
            startup_snapshot=shadow_snapshot(),
            node_registry_summary=node_registry_summary(),
            host_executor="CODEX_LINUX",
        )
        with (
            mock.patch.object(
                workflow_runtime, "startup_receipt", side_effect=AssertionError
            ),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "verify_consumption",
                side_effect=AssertionError,
            ),
        ):
            result = workflow_runtime.execute_close_node(
                Path("/repo"),
                plan=shadow,
                owned_paths=[],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=None,
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )
        self.assertEqual(result["status"], "HOLD")
        self.assertIn("SHADOW_V10_RUN_AUTHORITY_FORBIDDEN", result["holds"])

    def test_fabricated_battle_v10_authority_cannot_bypass_shadow_block(self) -> None:
        battle = {
            "schema": workflow_runtime.SHADOW_PLAN_SCHEMA,
            "mode": "BATTLE_V10",
            "status": "READY",
            "holds": [],
            "selected_goal": "docs/routeB_bus/058.goal.md",
            "run_authorized": True,
        }
        with (
            mock.patch.object(
                workflow_runtime, "startup_receipt", side_effect=AssertionError
            ),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "verify_consumption",
                side_effect=AssertionError("fabricated authority entered deep gate"),
            ),
        ):
            result = workflow_runtime.execute_close_node(
                Path("/repo"),
                plan=battle,
                owned_paths=[],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=None,
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )
        self.assertIn("SHADOW_V10_RUN_AUTHORITY_FORBIDDEN", result["holds"])

    def test_run_holds_on_red_startup_before_any_writer(self) -> None:
        compiled = plan("SELECT_EXACT_GOAL")
        red = {"label": "session-start", "exit": 1, "output_tail": "red"}
        with mock.patch.object(workflow_runtime, "startup_receipt", return_value=red):
            result = workflow_runtime.execute_close_node(
                Path("."),
                plan=compiled,
                owned_paths=["owned.txt"],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=Path("attempt.json"),
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )
        self.assertEqual(result["status"], "HOLD")
        self.assertIn("START_GATE_FAILED:1", result["holds"])

    def test_run_requires_owned_scope_and_attempt_event(self) -> None:
        compiled = plan("SELECT_EXACT_GOAL")
        green = {"label": "session-start", "exit": 0, "output_tail": "green"}
        with mock.patch.object(workflow_runtime, "startup_receipt", return_value=green):
            result = workflow_runtime.execute_close_node(
                Path("."),
                plan=compiled,
                owned_paths=[],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=None,
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )
        self.assertIn("OWNED_SCOPE_REQUIRED", result["holds"])
        self.assertIn("GOAL_ATTEMPT_EVENT_REQUIRED", result["holds"])

    def test_green_run_executes_step_and_session_close(self) -> None:
        compiled = plan("SELECT_EXACT_GOAL")
        compiled["logical_plan"]["startup_receipt"] = {
            "label": "session-start", "exit": 0, "output_tail": "green"
        }
        def ok(label: str) -> dict[str, object]:
            return {"label": label, "exit": 0, "output_tail": "ok"}

        with (
            mock.patch.object(workflow_runtime, "_git", return_value=""),
            mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "verify_consumption",
                side_effect=AssertionError("v1 run entered v10 deep gate"),
            ),
            mock.patch.object(
                workflow_runtime,
                "command_receipt",
                side_effect=lambda _repo, _command, label: ok(label),
            ) as command,
        ):
            result = workflow_runtime.execute_close_node(
                Path("."),
                plan=compiled,
                owned_paths=["docs/Codex/x.md"],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=Path("attempt.json"),
                insight_payload=None,
                run_kernel=False,
                protocol_out=Path("protocol.md"),
            )
        self.assertEqual(result["status"], "CLOSED_NODE")
        self.assertEqual(
            [item["label"] for item in result["receipts"]],
            ["session-start", "step-close", "session-close"],
        )
        self.assertEqual(command.call_count, 2)

    def test_review_plan_binds_bytes_commit_blob_and_living_chat(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(
                ["git", "config", "user.email", "plant@example.invalid"],
                cwd=repo,
                check=True,
            )
            subprocess.run(["git", "config", "user.name", "Workflow Plant"], cwd=repo, check=True)
            request = repo / "docs/routeB_bus/proshka/request.txt"
            request.parent.mkdir(parents=True)
            request.write_bytes(
                b"REQUEST_ID: REQ-PLANT\nBOUNDARY_ID: new-boundary\n"
                b"CALL_CLASS: DELEGATED_STRATEGIC_REVIEW\nexact request\n"
            )
            queue = repo / "docs/routeB_bus/PROSHKA_QUEUE.md"
            queue.write_text(
                "## REQ-PLANT · plant\n\n- `STATUS: OPEN`\n",
                encoding="utf-8",
            )
            runtime = repo / "orchestrator/state/CHANNEL_RUNTIME.json"
            runtime.parent.mkdir(parents=True)
            runtime.write_text(
                json.dumps({
                    "active_proshka_phase": {
                        "status": "ACTIVE",
                        "conversation_id": "living-chat",
                        "last_boundary_id": "older-boundary",
                    }
                }) + "\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "plant"], cwd=repo, check=True)
            commit = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                capture_output=True, text=True,
            ).stdout.strip()
            digest = workflow_runtime.hashlib.sha256(request.read_bytes()).hexdigest()

            result = workflow_runtime.compile_review_dispatch(
                repo,
                attachment=request,
                request_commit=commit,
                request_id="REQ-PLANT",
                boundary_id="new-boundary",
                expected_sha256=digest,
            )

            self.assertEqual(result["status"], "REVIEW_DISPATCH_READY")
            self.assertEqual(result["call_class"], "DELEGATED_STRATEGIC_REVIEW")
            self.assertEqual(result["conversation_id"], "living-chat")
            self.assertFalse(result["transport"]["repository_owner_confirmation_required"])
            self.assertEqual(
                result["transport"]["host_safety_confirmation"],
                "ENFORCED_BY_ACTIVE_UI_RUNTIME",
            )
            self.assertFalse(result["transport"]["delivery_performed"])
            self.assertEqual(
                result["attachment_manifest"]["git_blob"],
                result["attachment_manifest"]["commit_blob"],
            )

    def test_review_plan_rejects_mutation_and_duplicate_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(
                ["git", "config", "user.email", "plant@example.invalid"],
                cwd=repo,
                check=True,
            )
            subprocess.run(["git", "config", "user.name", "Workflow Plant"], cwd=repo, check=True)
            request = repo / "request.txt"
            request.write_bytes(
                b"REQUEST_ID: REQ-PLANT\nBOUNDARY_ID: same-boundary\n"
                b"CALL_CLASS: DELEGATED_STRATEGIC_REVIEW\ncommitted\n"
            )
            queue = repo / "docs/routeB_bus/PROSHKA_QUEUE.md"
            queue.parent.mkdir(parents=True)
            queue.write_text(
                "## REQ-PLANT · plant\n\n- `STATUS: ANSWERED`\n",
                encoding="utf-8",
            )
            runtime = repo / "orchestrator/state/CHANNEL_RUNTIME.json"
            runtime.parent.mkdir(parents=True)
            runtime.write_text(
                json.dumps({
                    "active_proshka_phase": {
                        "status": "ACTIVE",
                        "conversation_id": "living-chat",
                        "last_boundary_id": "same-boundary",
                    }
                }) + "\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "plant"], cwd=repo, check=True)
            commit = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                capture_output=True, text=True,
            ).stdout.strip()
            request.write_bytes(b"mutated without final newline")

            result = workflow_runtime.compile_review_dispatch(
                repo,
                attachment=request,
                request_commit=commit,
                request_id="REQ-PLANT",
                boundary_id="same-boundary",
                expected_sha256="0" * 64,
            )

            self.assertEqual(result["status"], "HOLD")
            self.assertIn("PROSHKA_ATTACHMENT_FINAL_LF_MISSING", result["holds"])
            self.assertIn("PROSHKA_ATTACHMENT_SHA256_MISMATCH", result["holds"])
            self.assertIn("PROSHKA_ATTACHMENT_COMMIT_BLOB_MISMATCH", result["holds"])
            self.assertIn(
                "PROSHKA_REVIEW_BOUNDARY_ALREADY_RECORDED:same-boundary",
                result["holds"],
            )
            self.assertIn(
                "PROSHKA_REQUEST_NOT_OPEN:REQ-PLANT:ANSWERED",
                result["holds"],
            )

    def test_research_debt_challenge_requires_eligible_exploration_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            request, commit, digest = self._review_fixture(
                repo,
                call_class="EXPLORATION_REVIEW",
                packet_subtype="RESEARCH_DEBT_CHALLENGE",
            )
            result = workflow_runtime.compile_review_dispatch(
                repo,
                attachment=request,
                request_commit=commit,
                request_id="REQ-PLANT",
                boundary_id="boundary",
                expected_sha256=digest,
            )
        self.assertEqual(result["status"], "REVIEW_DISPATCH_READY")
        self.assertEqual(result["call_class"], "EXPLORATION_REVIEW")
        self.assertEqual(
            result["eligibility_receipt"]["result"],
            "EXPLORATION_REVIEW_ALLOWED",
        )

    def test_research_debt_challenge_rejects_wrong_or_ineligible_call(self) -> None:
        cases = (
            (None, exploration_runtime(), "PROSHKA_CALL_CLASS_MISSING"),
            (
                "DELEGATED_STRATEGIC_REVIEW",
                exploration_runtime(),
                "RESEARCH_DEBT_CHALLENGE_CALL_CLASS_MISMATCH",
            ),
            (
                "EXPLORATION_REVIEW",
                exploration_runtime(no_progress_streak=5),
                "EXPLORATION_REVIEW_OUTSIDE_GATE",
            ),
            (
                "EXPLORATION_REVIEW",
                dict(exploration_runtime(), active_exploration=None),
                "EXPLORATION_RUNTIME_MISSING",
            ),
        )
        for call_class, runtime, expected in cases:
            with self.subTest(call_class=call_class, expected=expected):
                with tempfile.TemporaryDirectory() as tmp:
                    repo = Path(tmp)
                    request, commit, digest = self._review_fixture(
                        repo,
                        call_class=call_class,
                        packet_subtype="RESEARCH_DEBT_CHALLENGE",
                        runtime=runtime,
                    )
                    result = workflow_runtime.compile_review_dispatch(
                        repo,
                        attachment=request,
                        request_commit=commit,
                        request_id="REQ-PLANT",
                        boundary_id="boundary",
                        expected_sha256=digest,
                    )
                self.assertEqual(result["status"], "HOLD")
                self.assertIn(expected, result["holds"])

    def test_review_plan_rejects_noncanonical_or_ambiguous_call_class(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            request, commit, digest = self._review_fixture(
                repo,
                call_class="RESEARCH_DEBT_CHALLENGE",
            )
            invalid = workflow_runtime.compile_review_dispatch(
                repo,
                attachment=request,
                request_commit=commit,
                request_id="REQ-PLANT",
                boundary_id="boundary",
                expected_sha256=digest,
            )
        self.assertEqual(invalid["status"], "HOLD")
        self.assertIn(
            "PROSHKA_CALL_CLASS_INVALID:RESEARCH_DEBT_CHALLENGE",
            invalid["holds"],
        )

        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            request, _, _ = self._review_fixture(
                repo,
                call_class="DELEGATED_STRATEGIC_REVIEW",
            )
            request.write_text(
                request.read_text(encoding="utf-8")
                + "CALL_CLASS: EXPLORATION_REVIEW\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "ambiguous class"], cwd=repo, check=True)
            commit = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                capture_output=True, text=True,
            ).stdout.strip()
            digest = workflow_runtime.hashlib.sha256(request.read_bytes()).hexdigest()
            ambiguous = workflow_runtime.compile_review_dispatch(
                repo,
                attachment=request,
                request_commit=commit,
                request_id="REQ-PLANT",
                boundary_id="boundary",
                expected_sha256=digest,
            )
        self.assertEqual(ambiguous["status"], "HOLD")
        self.assertIn("PROSHKA_CALL_CLASS_AMBIGUOUS", ambiguous["holds"])

    def test_named_supplier_preflight_requires_valid_consumer_contract_receipt(self) -> None:
        compiled = plan("SELECT_EXACT_GOAL")
        compiled["logical_plan"]["startup_receipt"] = {
            "label": "session-start", "exit": 0, "output_tail": "green"
        }
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            missing = workflow_runtime.execute_close_node(
                repo,
                plan=compiled,
                owned_paths=["owned.md"],
                query="supplier",
                candidate="Q3.RouteB.candidate",
                target="Q3.RouteB.target",
                attempt_payload=Path("attempt.json"),
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )
            self.assertIn("CONSUMER_FIRST_CONTRACT_RECEIPT_REQUIRED", missing["holds"])

            receipt = repo / "contract.json"
            receipt.write_text(json.dumps({
                "schema": workflow_runtime.DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
                "candidate": "Q3.RouteB.candidate",
                "target": "Q3.RouteB.target",
                "contract": dependency_contract(),
            }) + "\n", encoding="utf-8")
            def ok(label: str) -> dict[str, object]:
                return {"label": label, "exit": 0, "output_tail": "ok"}

            with (
                mock.patch.object(workflow_runtime, "_git", return_value=""),
                mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
                mock.patch.object(
                    workflow_runtime,
                    "command_receipt",
                    side_effect=lambda _repo, _command, label: ok(label),
                ),
            ):
                result = workflow_runtime.execute_close_node(
                    repo,
                    plan=compiled,
                    owned_paths=["owned.md"],
                    query="supplier",
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                    attempt_payload=Path("attempt.json"),
                    insight_payload=None,
                    run_kernel=False,
                    protocol_out=None,
                    dependency_contract_receipt=receipt,
                )
        self.assertEqual(result["status"], "CLOSED_NODE")
        self.assertEqual(result["receipts"][1]["label"], "consumer-first-contract")

    def test_supplier_contract_receipt_binds_candidate_and_valid_contract(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            receipt = repo / "contract.json"
            payload = {
                "schema": workflow_runtime.DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
                "candidate": "wrong",
                "target": "Q3.RouteB.target",
                "contract": dependency_contract(),
            }
            receipt.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CONSUMER_FIRST_CONTRACT_CANDIDATE_MISMATCH",
            ):
                workflow_runtime._dependency_contract_receipt(
                    repo,
                    receipt,
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                )
            payload["candidate"] = "Q3.RouteB.candidate"
            payload["contract"]["actual_consumer_requirement"] = ""
            receipt.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID",
            ):
                workflow_runtime._dependency_contract_receipt(
                    repo,
                    receipt,
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                )


if __name__ == "__main__":
    unittest.main()
