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
        subprocess.run(["git", "config", "user.email", "plant@example.invalid"], cwd=repo, check=True)
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
            subprocess.run(["git", "config", "user.email", "plant@example.invalid"], cwd=repo, check=True)
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
            ok = lambda label: {"label": label, "exit": 0, "output_tail": "ok"}
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
