from __future__ import annotations

from pathlib import Path
import json
import subprocess
import tempfile
from unittest import mock
import unittest

from orchestrator import workflow_runtime


def tool_index() -> dict[str, dict[str, object]]:
    ids = set(workflow_runtime.COMMON_TOOLS)
    for values in workflow_runtime.ACTION_TOOLS.values():
        ids.update(values)
    return {item: {"id": item, "status": "ENABLED", "mode": "READ_ONLY", "writes": False} for item in ids}


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


class WorkflowRuntimePlants(unittest.TestCase):
    def test_three_closure_shapes_compile_without_second_selector(self) -> None:
        exact = plan("SELECT_EXACT_GOAL")
        mint = plan("MINT_READY")
        phase = plan("PHASE_TRANSITION_REQUIRED")
        self.assertEqual([exact["status"], mint["status"], phase["status"]], ["READY"] * 3)
        self.assertIn("workflow-session-close", [item["id"] for item in exact["logical_plan"]["selected_tools"]])
        self.assertIn("workflow-phase-close", [item["id"] for item in phase["logical_plan"]["selected_tools"]])
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
        ok = lambda label: {"label": label, "exit": 0, "output_tail": "ok"}
        with (
            mock.patch.object(workflow_runtime, "_git", return_value=""),
            mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
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
            subprocess.run(["git", "config", "user.email", "plant@example.invalid"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.name", "Workflow Plant"], cwd=repo, check=True)
            request = repo / "docs/routeB_bus/proshka/request.txt"
            request.parent.mkdir(parents=True)
            request.write_bytes(b"exact request\n")
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
                boundary_id="new-boundary",
                expected_sha256=digest,
            )

            self.assertEqual(result["status"], "REVIEW_DISPATCH_READY")
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
            subprocess.run(["git", "config", "user.email", "plant@example.invalid"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.name", "Workflow Plant"], cwd=repo, check=True)
            request = repo / "request.txt"
            request.write_bytes(b"committed\n")
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


if __name__ == "__main__":
    unittest.main()
