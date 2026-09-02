from __future__ import annotations

import fcntl
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
from unittest import mock

from orchestrator import workflow_runtime
from orchestrator.benchmarks import control_v10_benchmark as benchmark
from orchestrator.startup_runtime import StartupSnapshot


class _FakeEpochGuard:
    def __init__(
        self, events: list[str] | None = None, *, recheck_error: str | None = None
    ) -> None:
        self.events = events if events is not None else []
        self.recheck_error = recheck_error
        self.open = False

    def recheck(self) -> str | None:
        self.events.append("recheck")
        return self.recheck_error


@contextmanager
def _fake_startup_epoch(
    guard: _FakeEpochGuard, lock_error: str | None = None
):
    guard.events.append("lock")
    guard.open = True
    try:
        yield guard, lock_error
    finally:
        guard.open = False
        guard.events.append("close")


class _FakeWriterEpoch:
    def __init__(self, events: list[str] | None = None) -> None:
        self.events = events if events is not None else []
        self.open = False

    def recheck(self) -> None:
        if not self.open:
            raise workflow_runtime.WorkflowRuntimeError("fake lock not held")
        self.events.append("lock-recheck")


@contextmanager
def _fake_writer_epoch(epoch: _FakeWriterEpoch):
    epoch.open = True
    epoch.events.append("lock-open")
    try:
        epoch.recheck()
        yield epoch
        epoch.recheck()
    finally:
        epoch.events.append("lock-close")
        epoch.open = False


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


def supplier_payload(
    status: str, *, candidate_provenance: str = "SOURCE_DECLARED"
) -> dict[str, object]:
    payload = {field: None for field in workflow_runtime.SUPPLIER_PAYLOAD_FIELDS}
    payload.update(
        {
            "schema": workflow_runtime.SUPPLIER_PREFLIGHT_SCHEMA,
            "query": "supplier",
            "candidate_requested": "Q3.RouteB.candidate",
            "target_requested": "Q3.RouteB.target",
            "candidate_provenance": candidate_provenance,
            "shelf": {"status": "HITS", "returncode": 0},
            "external_lean": {"schema": "q3_external_lean_search.v2"},
            "environment": {"status": "PASS"},
            "status": status,
            "reason": "plant",
            "boundary": "candidate-is-not-proof",
            "candidate": {},
            "comparison": {"status": status} if status == "EXACT_FIT" else None,
            "foreign_candidate": [],
            "source_candidates": [],
            "prose_candidates_present": False,
            "source_absence_scope": None,
        }
    )
    if status == "COMPLETE_ABSENCE":
        payload["reason"] = "SOURCE_DECLARATION_ABSENCE: plant"
        payload["source_absence_scope"] = "SOURCE_DECLARATION_ABSENCE"
    return payload


def supplier_receipt(status: str) -> dict[str, object]:
    return {
        "label": "supplier-preflight",
        "command": ["supplier"],
        "exit": workflow_runtime.SUPPLIER_STATUS_EXIT[status],
        "duration_ms": 1,
        "output_sha256": "a" * 64,
        "output_tail": "plant",
        "payload": supplier_payload(status),
        "validation_error": None,
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


def production_snapshot(**overrides: object) -> StartupSnapshot:
    fields: dict[str, object] = {
        "schema": "q3_startup_snapshot.v10.v1",
        "mode": "PRODUCTION_V10_READ_ONLY",
        "control_sha256": "a" * 64,
        "control_version": 10,
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
        "blocked_features": (),
        "warnings": [],
        "next_action": "RUN_SELECTED_GOAL",
        "run_authorized": True,
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
        self.assertEqual(
            loop["next_joint"]["candidate_details_ref"], "cords.open_joints"
        )
        self.assertEqual(
            loop["next_joint"]["candidates"],
            [joint["address"] for joint in loop["cords"]["open_joints"]],
        )
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
        timing: dict[str, object] = {}
        events: list[str] = []
        guard = _FakeEpochGuard(events)

        def build_snapshot(*_args: object, **kwargs: object) -> StartupSnapshot:
            self.assertTrue(guard.open)
            self.assertIs(kwargs["_epoch_guard"], guard)
            self.assertIsNone(kwargs["_epoch_lock_error"])
            events.append("snapshot")
            return snapshot

        def registry_summary(*_args: object, **_kwargs: object) -> dict[str, object]:
            self.assertTrue(guard.open)
            events.append("registry")
            return node_registry_summary()

        with (
            mock.patch.object(
                workflow_runtime,
                "_startup_read_epoch",
                return_value=_fake_startup_epoch(guard),
            ),
            mock.patch.object(
                workflow_runtime, "build_shadow_snapshot", side_effect=build_snapshot
            ) as build,
            mock.patch.object(
                workflow_runtime.time,
                "perf_counter",
                side_effect=[10.0, 10.125],
            ),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "startup_gate_summary",
                side_effect=registry_summary,
            ) as registry,
        ):
            result = workflow_runtime.live_shadow_plan_v10(
                Path("/repo"),
                owned_paths=["owned.md"],
                _benchmark_timing_sink=timing,
            )
        build.assert_called_once_with(
            Path("/repo"),
            owned_paths=("owned.md",),
            _epoch_guard=guard,
            _epoch_lock_error=None,
        )
        registry.assert_called_once_with(
            Path("/repo"),
            snapshot.selected_goal,
            owned_paths=("owned.md",),
            exact_node_pin=snapshot.exact_node_pin,
            exact_source_pin=snapshot.exact_source_pin,
            exact_theorem_pin=snapshot.exact_theorem_pin,
            exact_consumer_pin=snapshot.exact_consumer_pin,
        )
        self.assertEqual(result["schema"], "q3_workflow_plan.v2")
        self.assertEqual(result["selected_goal"], snapshot.selected_goal)
        self.assertFalse(result["run_authorized"])
        self.assertFalse(result["writes_performed"])
        self.assertEqual(events, ["lock", "snapshot", "registry", "recheck", "close"])
        self.assertEqual(
            timing,
            {
                "schema": "q3_shadow_startup_timing.v1",
                "startup_duration_ms": 125.0,
                "snapshot_constructor_calls": 1,
            },
        )

    def test_production_v10_builds_proof_loop_inside_the_single_startup_epoch(
        self,
    ) -> None:
        events: list[str] = []
        guard = _FakeEpochGuard(events)
        snapshot = production_snapshot()
        logical = {
            "proof_loop": {"schema": "q3_proof_loop.v1"},
            "denominator_statuses": {
                "assembly": {"fixed": 51, "total": 69},
                "roof_port_ledger": {
                    "semantic_slot_count": 6,
                    "direct_proof_input_count": 7,
                    "jointly_bound": 0,
                },
                "node_registry": {"status": "PASS"},
            },
        }

        def build(*_args, **_kwargs):
            self.assertTrue(guard.open)
            events.append("snapshot")
            return snapshot

        def registry(*_args, **_kwargs):
            self.assertTrue(guard.open)
            events.append("registry")
            return node_registry_summary()

        def compile_logical(*_args, **_kwargs):
            self.assertTrue(guard.open)
            events.append("proof-loop")
            return logical

        with (
            mock.patch.object(
                workflow_runtime,
                "_startup_read_epoch",
                return_value=_fake_startup_epoch(guard),
            ),
            mock.patch.object(
                workflow_runtime, "build_startup_snapshot", side_effect=build
            ) as startup,
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "startup_gate_summary",
                side_effect=registry,
            ) as gate,
            mock.patch.object(
                workflow_runtime,
                "_compile_production_logical_plan",
                side_effect=compile_logical,
            ) as proof,
        ):
            result = workflow_runtime.live_plan_v10(Path("/repo"), owned_paths=[])

        startup.assert_called_once()
        gate.assert_called_once_with(
            Path("/repo"),
            snapshot.selected_goal,
            owned_paths=(),
            exact_node_pin="NODE-058",
            exact_source_pin="SOURCE-058",
            exact_theorem_pin="THEOREM-058",
            exact_consumer_pin="CONSUMER-058",
        )
        proof.assert_called_once()
        self.assertEqual(
            events,
            ["lock", "snapshot", "registry", "recheck", "proof-loop", "close"],
        )
        self.assertEqual(result["logical_plan"], logical)

    def test_production_logical_plan_labels_assembly_as_bookkeeping(self) -> None:
        assembly = {
            "status": "AVAILABLE",
            "global": {
                "total": 69,
                "fixed": 51,
                "proved": 48,
                "validation": 3,
                "open": 18,
            },
            "selected_chain": None,
            "open_joints": [],
            "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
        }
        roof = {
            "schema": "q3_roof_port_supplier_ledger.v1",
            "integrity_status": "HEAD_LOCKED",
            "integrity_reasons": [],
            "honesty_state": "CHALLENGER_NOT_RH",
            "semantic_slot_count": 6,
            "direct_proof_input_count": 7,
            "port_summary": {"jointly_bound": 0, "total": 7},
            "assembly_bookkeeping": {
                "status": "AVAILABLE",
                "global": {"total": 69, "fixed": 51, "open": 18},
                "quarantined_edges": [],
            },
        }
        from orchestrator import proof_loop

        with (
            mock.patch.object(proof_loop, "goal_assembly_chain", return_value=None),
            mock.patch.object(proof_loop, "assembly_snapshot", return_value=assembly),
            mock.patch.object(
                workflow_runtime, "_build_compact_roof_ledger", return_value=roof
            ),
        ):
            logical = workflow_runtime._compile_production_logical_plan(
                Path("/repo"),
                snapshot=production_snapshot(),
                registry_summary=node_registry_summary(),
                holds=[],
            )

        loop = logical["proof_loop"]
        self.assertEqual(loop["schema"], "q3_proof_loop.v1")
        self.assertEqual(loop["roof_port_ledger"]["semantic_slot_count"], 6)
        self.assertEqual(loop["roof_port_ledger"]["direct_proof_input_count"], 7)
        self.assertEqual(loop["roof_port_ledger"]["port_summary"]["jointly_bound"], 0)
        denominator = logical["denominator_statuses"]["assembly"]
        self.assertEqual((denominator["fixed"], denominator["total"]), (51, 69))
        self.assertEqual(
            denominator["interpretation"],
            "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
        )

    def test_compact_roof_ledger_batches_git_and_rejects_unknown_queries(self) -> None:
        from orchestrator import roof_port_ledger

        tracked_paths = {
            roof_port_ledger.ROOF_SOURCE.as_posix(),
            *(
                path
                for spec in roof_port_ledger.PORT_SPECS
                for path, _declaration, _target in spec["candidates"]
            ),
        }
        batch_lines = "\n".join(
            f"{'a' * 40} blob 1" for _path in sorted(tracked_paths)
        )
        batch = subprocess.CompletedProcess(
            args=["git", "cat-file", "--batch-check"],
            returncode=0,
            stdout=f"{batch_lines}\n",
            stderr="",
        )

        def canonical_build(repo: Path, database: Path) -> dict[str, object]:
            self.assertEqual(repo, Path("/repo"))
            self.assertEqual(database, Path("/repo/knowledge.db"))
            self.assertEqual(roof_port_ledger._git(repo, "rev-parse", "HEAD"), "b" * 40)
            self.assertEqual(
                roof_port_ledger._git(
                    repo,
                    "rev-parse",
                    f"HEAD:{roof_port_ledger.ROOF_SOURCE.as_posix()}",
                ),
                "a" * 40,
            )
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "WORKFLOW_ROOF_GIT_QUERY_OUTSIDE_BATCH",
            ):
                roof_port_ledger._git(repo, "rev-parse", "HEAD:unexpected.lean")
            return {
                "schema": roof_port_ledger.SCHEMA,
                "integrity_status": "HEAD_LOCKED",
                "integrity_reasons": [],
                "honesty_state": "CHALLENGER_NOT_RH",
                "semantic_slot_count": 6,
                "direct_proof_input_count": 7,
                "port_summary": {"jointly_bound": 0, "total": 7},
                "assembly_bookkeeping": {
                    "status": "AVAILABLE",
                    "global": {"total": 69, "fixed": 51, "open": 18},
                    "quarantined_edges": [],
                },
            }

        with (
            mock.patch.object(workflow_runtime.subprocess, "run", return_value=batch) as run,
            mock.patch.object(roof_port_ledger, "build", side_effect=canonical_build),
        ):
            compact = workflow_runtime._build_compact_roof_ledger(
                Path("/repo"),
                git_head="b" * 40,
                database=Path("/repo/knowledge.db"),
            )

        run.assert_called_once()
        self.assertEqual(compact["integrity_status"], "HEAD_LOCKED")
        self.assertEqual(compact["semantic_slot_count"], 6)
        self.assertEqual(compact["direct_proof_input_count"], 7)
        self.assertEqual(compact["port_summary"]["jointly_bound"], 0)

    def test_shadow_v10_registry_epoch_drift_fails_closed(self) -> None:
        error = "FATAL:WRITER_LOCK_IDENTITY_CHANGED"
        guard = _FakeEpochGuard(recheck_error=error)
        snapshot = shadow_snapshot()
        with (
            mock.patch.object(
                workflow_runtime,
                "_startup_read_epoch",
                return_value=_fake_startup_epoch(guard),
            ),
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
                Path("/repo"), owned_paths=[]
            )

        build.assert_called_once()
        registry.assert_called_once()
        self.assertEqual(result["status"], "FATAL")
        self.assertIsNone(result["selected_goal"])
        self.assertIn(error, result["holds"])
        self.assertIn("NODE_REGISTRY_STARTUP_EPOCH_DRIFT", result["holds"])
        self.assertFalse(result["run_authorized"])
        self.assertEqual(guard.events, ["lock", "recheck", "close"])

    def test_shadow_v10_lock_failure_skips_unprotected_registry_read(self) -> None:
        lock_error = "FATAL:WRITER_LOCK_COLLISION"
        guard = _FakeEpochGuard()
        with (
            mock.patch.object(
                workflow_runtime,
                "_startup_read_epoch",
                return_value=_fake_startup_epoch(guard, lock_error),
            ),
            mock.patch.object(
                workflow_runtime,
                "build_shadow_snapshot",
                return_value=shadow_snapshot(fatal_errors=(lock_error,)),
            ) as build,
            mock.patch.object(
                workflow_runtime.node_registry_v10, "startup_gate_summary"
            ) as registry,
        ):
            result = workflow_runtime.live_shadow_plan_v10(
                Path("/repo"), owned_paths=[]
            )

        build.assert_called_once()
        registry.assert_not_called()
        self.assertEqual(result["status"], "FATAL")
        self.assertIn(lock_error, result["holds"])
        self.assertIn("NODE_REGISTRY_WRITER_EPOCH_UNAVAILABLE", result["holds"])
        self.assertFalse(result["run_authorized"])
        self.assertEqual(guard.events, ["lock", "close"])

    def test_shadow_v10_hot_path_never_enters_legacy_or_subprocess_startup(self) -> None:
        snapshot = shadow_snapshot()
        guard = _FakeEpochGuard()
        with (
            mock.patch.object(
                workflow_runtime,
                "_startup_read_epoch",
                return_value=_fake_startup_epoch(guard),
            ),
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
                workflow_runtime, "selector_binding", side_effect=AssertionError
            ),
            mock.patch.object(
                workflow_runtime.time,
                "perf_counter",
                side_effect=AssertionError("default shadow path timed"),
            ),
        ):
            result = workflow_runtime.live_shadow_plan_v10(Path("/repo"), owned_paths=[])
        self.assertEqual(result["status"], "READY")
        self.assertEqual(
            result["startup"]["blocked_features"],
            ["RUN", "DISPATCH", "MINT", "STATE_WRITE"],
        )
        self.assertEqual(result["holds"], [])

    def test_default_v10_cli_imports_no_legacy_runtime_modules(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        entry = repo / "orchestrator/workflow_runtime.py"
        blocked = (
            "orchestrator.goal_runtime",
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
            f"sys.argv=[{str(entry)!r},'--root',{str(repo)!r},'plan']\n"
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
        self.assertEqual(payload["mode"], "PRODUCTION_V10")
        self.assertEqual(
            payload["logical_plan"]["proof_loop"]["schema"],
            "q3_proof_loop.v1",
        )

    def test_production_v10_benchmark_timing_keeps_stdout_identical(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        command = [
            sys.executable,
            str(repo / "orchestrator/workflow_runtime.py"),
            "--root",
            str(repo),
            "plan",
        ]
        normal = subprocess.run(
            command,
            cwd=repo,
            check=False,
            capture_output=True,
            text=True,
        )
        timed = subprocess.run(
            [*command, "--benchmark-startup-timing"],
            cwd=repo,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(normal.returncode, timed.returncode)
        self.assertEqual(normal.stdout, timed.stdout)
        self.assertNotIn(workflow_runtime._BENCHMARK_TIMING_PREFIX, normal.stderr)
        timing = benchmark._parse_production_startup_timing(timed.stderr)
        self.assertEqual(timing["snapshot_constructor_calls"], 1)
        self.assertGreaterEqual(timing["startup_duration_ms"], 0)

    def test_benchmark_timing_flag_is_supported_on_bare_production_plan(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        proc = subprocess.run(
            [
                sys.executable,
                str(repo / "orchestrator/workflow_runtime.py"),
                "--root",
                str(repo),
                "plan",
                "--benchmark-startup-timing",
            ],
            cwd=repo,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertIn(proc.returncode, {0, 2}, proc.stderr)
        payload = json.loads(proc.stdout)
        self.assertEqual(payload["schema"], "q3_workflow_plan.v2")
        self.assertEqual(payload["mode"], "PRODUCTION_V10")
        timing = benchmark._parse_production_startup_timing(proc.stderr)
        self.assertEqual(timing["snapshot_constructor_calls"], 1)

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
        guard = _FakeEpochGuard()
        with (
            mock.patch.object(
                workflow_runtime,
                "_startup_read_epoch",
                return_value=_fake_startup_epoch(guard),
            ),
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
            exact_source_pin=None,
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

    def test_default_plan_cli_uses_production_v10_path(self) -> None:
        production = workflow_runtime.compile_plan_v10(
            startup_snapshot=production_snapshot(),
            node_registry_summary=node_registry_summary(),
            host_executor="CODEX_LINUX",
        )
        argv = ["workflow_runtime.py", "--root", "/repo", "plan"]
        with (
            mock.patch.object(workflow_runtime.sys, "argv", argv),
            mock.patch.object(
                workflow_runtime, "live_plan_v10", return_value=production
            ) as live,
            mock.patch.object(
                workflow_runtime,
                "live_plan",
                side_effect=AssertionError("default plan entered legacy v9"),
            ),
            mock.patch.object(
                workflow_runtime,
                "live_shadow_plan_v10",
                side_effect=AssertionError("default plan entered diagnostic shadow"),
            ),
            mock.patch("builtins.print") as emit,
        ):
            status = workflow_runtime.main()
        self.assertEqual(status, 0)
        live.assert_called_once_with(Path("/repo"), owned_paths=[])
        emit.assert_called_once_with(workflow_runtime.render_plan_v10(production))

    def test_legacy_v9_flag_is_not_exposed_by_workflow_cli(self) -> None:
        argv = [
            "workflow_runtime.py",
            "--root",
            "/repo",
            "plan",
            "--legacy-v9-maintenance",
        ]
        with (
            mock.patch.object(workflow_runtime.sys, "argv", argv),
            mock.patch.object(workflow_runtime, "live_plan") as legacy,
            mock.patch.object(workflow_runtime, "live_plan_v10") as production,
            self.assertRaises(SystemExit) as raised,
        ):
            workflow_runtime.main()
        self.assertEqual(raised.exception.code, 2)
        legacy.assert_not_called()
        production.assert_not_called()

    def test_workflow_runtime_has_no_session_start_wrapper_call(self) -> None:
        source = Path(workflow_runtime.__file__).read_text(encoding="utf-8")
        self.assertNotIn("specs_docs/session_start.sh", source)
        self.assertNotIn("--legacy-v9-maintenance", source)

    def test_legacy_v9_run_requires_embedded_manual_startup_receipt(self) -> None:
        compiled = plan("SELECT_EXACT_GOAL")
        with mock.patch.object(workflow_runtime, "command_receipt") as command:
            result = workflow_runtime.execute_close_node(
                Path("/repo"),
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
        self.assertIn("LEGACY_V9_STARTUP_RECEIPT_REQUIRED", result["holds"])
        command.assert_not_called()

    def test_run_rejects_non_v1_plan_before_startup_or_writers(self) -> None:
        shadow = workflow_runtime.compile_shadow_plan_v10(
            startup_snapshot=shadow_snapshot(),
            node_registry_summary=node_registry_summary(),
            host_executor="CODEX_LINUX",
        )
        with (
            mock.patch.object(workflow_runtime, "_exists_at_head") as exists,
            mock.patch.object(workflow_runtime, "command_receipt") as command,
        ):
            result = workflow_runtime.execute_close_node(
                Path("/repo"),
                plan=shadow,
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
        self.assertEqual(result["holds"], ["WORKFLOW_RUN_PLAN_SCHEMA_UNSUPPORTED"])
        self.assertEqual(result["receipts"], [])
        exists.assert_not_called()
        command.assert_not_called()

    def test_production_v10_run_requires_deep_consumption_before_writers(self) -> None:
        compiled = workflow_runtime.compile_plan_v10(
            startup_snapshot=production_snapshot(),
            node_registry_summary=node_registry_summary(),
            host_executor="CODEX_LINUX",
        )
        failed = {
            "schema": "q3_node_registry_consumption.v1",
            "status": "HOLD",
            "code": "NODE_REGISTRY_HISTORICAL_V9_UNMAPPED",
        }
        epoch = _FakeWriterEpoch()
        with (
            mock.patch.object(
                workflow_runtime,
                "_execution_writer_epoch",
                return_value=_fake_writer_epoch(epoch),
            ),
            mock.patch.object(
                workflow_runtime,
                "_recheck_production_identity",
                return_value=None,
            ),
            mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "verify_consumption",
                return_value=failed,
            ) as verify,
            mock.patch.object(workflow_runtime, "command_receipt") as writer,
        ):
            result = workflow_runtime.execute_close_node(
                Path("/repo"),
                plan=compiled,
                owned_paths=["docs/Codex/owned.md"],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=Path("attempt.json"),
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )
        verify.assert_called_once_with(
            Path("/repo"),
            selected_goal_path="docs/routeB_bus/058.goal.md",
            owned_paths=["docs/Codex/owned.md"],
            exact_node_pin="NODE-058",
            exact_source_pin="SOURCE-058",
            exact_theorem_pin="THEOREM-058",
            exact_consumer_pin="CONSUMER-058",
            writer_lock_held=True,
        )
        self.assertFalse(epoch.open)
        writer.assert_not_called()
        self.assertEqual(result["status"], "HOLD")
        self.assertIn(
            "NODE_REGISTRY_V10_CONSUMPTION_FAILED:"
            "NODE_REGISTRY_HISTORICAL_V9_UNMAPPED",
            result["holds"],
        )

    def test_production_v10_holds_one_exclusive_lock_through_all_writers(self) -> None:
        compiled = workflow_runtime.compile_plan_v10(
            startup_snapshot=production_snapshot(),
            node_registry_summary=node_registry_summary(),
            host_executor="CODEX_LINUX",
        )
        events: list[str] = []
        epoch = _FakeWriterEpoch(events)

        def verify(*_args, **kwargs):
            self.assertTrue(epoch.open)
            self.assertTrue(kwargs["writer_lock_held"])
            events.append("consume")
            return {"status": "PASS", "code": "PASS"}

        def identity(*_args, **_kwargs):
            self.assertTrue(epoch.open)
            events.append("identity")
            return None

        def writer(_repo, _command, *, label):
            self.assertTrue(epoch.open)
            events.append(label)
            return {"label": label, "exit": 0, "output_tail": "ok"}

        with (
            mock.patch.object(
                workflow_runtime,
                "_execution_writer_epoch",
                return_value=_fake_writer_epoch(epoch),
            ),
            mock.patch.object(
                workflow_runtime,
                "_recheck_production_identity",
                side_effect=identity,
            ),
            mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
            mock.patch.object(workflow_runtime, "_git", return_value=""),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "verify_consumption",
                side_effect=verify,
            ) as consumption,
            mock.patch.object(
                workflow_runtime, "command_receipt", side_effect=writer
            ),
        ):
            result = workflow_runtime.execute_close_node(
                Path("/repo"),
                plan=compiled,
                owned_paths=["docs/Codex/owned.md"],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=Path("attempt.json"),
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )

        self.assertEqual(result["status"], "CLOSED_NODE")
        consumption.assert_called_once_with(
            Path("/repo"),
            selected_goal_path="docs/routeB_bus/058.goal.md",
            owned_paths=["docs/Codex/owned.md"],
            exact_node_pin="NODE-058",
            exact_source_pin="SOURCE-058",
            exact_theorem_pin="THEOREM-058",
            exact_consumer_pin="CONSUMER-058",
            writer_lock_held=True,
        )
        self.assertFalse(epoch.open)
        self.assertLess(events.index("consume"), events.index("step-close"))
        self.assertLess(events.index("step-close"), events.index("session-close"))
        self.assertEqual(events[-1], "lock-close")

    def test_production_v10_toctou_drift_stops_before_child_writers(self) -> None:
        compiled = workflow_runtime.compile_plan_v10(
            startup_snapshot=production_snapshot(),
            node_registry_summary=node_registry_summary(),
            host_executor="CODEX_LINUX",
        )
        epoch = _FakeWriterEpoch()
        with (
            mock.patch.object(
                workflow_runtime,
                "_execution_writer_epoch",
                return_value=_fake_writer_epoch(epoch),
            ),
            mock.patch.object(
                workflow_runtime,
                "_recheck_production_identity",
                side_effect=[None, "WORKFLOW_EXECUTION_EPOCH_HEAD_DRIFT"],
            ),
            mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "verify_consumption",
                return_value={"status": "PASS", "code": "PASS"},
            ),
            mock.patch.object(workflow_runtime, "command_receipt") as writer,
        ):
            result = workflow_runtime.execute_close_node(
                Path("/repo"),
                plan=compiled,
                owned_paths=["docs/Codex/owned.md"],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=Path("attempt.json"),
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
            )

        self.assertEqual(result["status"], "HOLD")
        self.assertIn("WORKFLOW_EXECUTION_EPOCH_HEAD_DRIFT", result["holds"])
        writer.assert_not_called()
        self.assertFalse(epoch.open)

    def test_execution_writer_epoch_is_exclusive_and_stable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            lock_path = repo / ".git/q3-three-body.writer.lock"
            lock_path.write_text("", encoding="utf-8")
            contender = lock_path.open("rb")
            try:
                with workflow_runtime._execution_writer_epoch(repo) as epoch:
                    epoch.recheck()
                    with self.assertRaises(BlockingIOError):
                        fcntl.flock(
                            contender.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB
                        )
                fcntl.flock(contender.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
                fcntl.flock(contender.fileno(), fcntl.LOCK_UN)
            finally:
                contender.close()

    def test_execution_identity_recheck_detects_control_and_goal_toctou(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(
                ["git", "config", "user.email", "plant@example.invalid"],
                cwd=repo,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Workflow Plant"],
                cwd=repo,
                check=True,
            )
            control = repo / "docs/CODEX_CONTROL.md"
            goal = repo / "docs/routeB_bus/058.goal.md"
            control.parent.mkdir(parents=True)
            goal.parent.mkdir(parents=True)
            control.write_text("control-v10\n", encoding="utf-8")
            goal.write_text("goal-058\n", encoding="utf-8")
            subprocess.run(["git", "add", "docs"], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "plant"], cwd=repo, check=True)
            lock_path = repo / ".git/q3-three-body.writer.lock"
            lock_path.write_text("", encoding="utf-8")
            startup = production_snapshot(
                control_sha256=workflow_runtime._sha256(control),
                git_head=workflow_runtime._git(repo, "rev-parse", "HEAD"),
                git_tree=workflow_runtime._git(repo, "rev-parse", "HEAD^{tree}"),
            )
            compiled = workflow_runtime.compile_plan_v10(
                startup_snapshot=startup,
                node_registry_summary=node_registry_summary(),
                host_executor="CODEX_LINUX",
            )

            with workflow_runtime._execution_writer_epoch(repo) as epoch:
                self.assertIsNone(
                    workflow_runtime._recheck_production_identity(
                        repo, plan=compiled, epoch=epoch
                    )
                )
                control.write_text("control-drift\n", encoding="utf-8")
                self.assertEqual(
                    workflow_runtime._recheck_production_identity(
                        repo, plan=compiled, epoch=epoch
                    ),
                    "WORKFLOW_EXECUTION_EPOCH_CONTROL_DRIFT",
                )
                control.write_text("control-v10\n", encoding="utf-8")
                goal.write_text("goal-drift\n", encoding="utf-8")
                self.assertEqual(
                    workflow_runtime._recheck_production_identity(
                        repo, plan=compiled, epoch=epoch
                    ),
                    "WORKFLOW_EXECUTION_EPOCH_SELECTED_GOAL_DRIFT",
                )

    def test_run_holds_on_red_startup_before_any_writer(self) -> None:
        compiled = plan("SELECT_EXACT_GOAL")
        red = {"label": "session-start", "exit": 1, "output_tail": "red"}
        compiled["logical_plan"]["startup_receipt"] = red
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
        compiled["logical_plan"]["startup_receipt"] = green
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
                "candidate_provenance": "SOURCE_DECLARED",
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
                mock.patch.object(
                    workflow_runtime,
                    "_supplier_preflight_receipt",
                    return_value=supplier_receipt("EXACT_FIT"),
                ) as supplier,
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
        supplier.assert_called_once_with(
            repo,
            query="supplier",
            candidate="Q3.RouteB.candidate",
            target="Q3.RouteB.target",
            candidate_provenance="SOURCE_DECLARED",
        )

    def test_only_exact_fit_clears_supplier_gate(self) -> None:
        compiled = plan("SELECT_EXACT_GOAL")
        compiled["logical_plan"]["startup_receipt"] = {
            "label": "session-start", "exit": 0, "output_tail": "green"
        }
        for status in workflow_runtime.SUPPLIER_STATUS_EXIT:
            with self.subTest(status=status), tempfile.TemporaryDirectory() as tmp:
                repo = Path(tmp)
                receipt = repo / "contract.json"
                receipt.write_text(json.dumps({
                    "schema": workflow_runtime.DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
                    "candidate": "Q3.RouteB.candidate",
                    "target": "Q3.RouteB.target",
                    "candidate_provenance": "SOURCE_DECLARED",
                    "contract": dependency_contract(),
                }) + "\n", encoding="utf-8")
                with (
                    mock.patch.object(workflow_runtime, "_git", return_value=""),
                    mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
                    mock.patch.object(
                        workflow_runtime,
                        "_supplier_preflight_receipt",
                        return_value=supplier_receipt(status),
                    ),
                    mock.patch.object(
                        workflow_runtime,
                        "command_receipt",
                        side_effect=lambda _repo, _command, label: {
                            "label": label, "exit": 0, "output_tail": "ok"
                        },
                    ) as writer,
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
                if status == "EXACT_FIT":
                    self.assertEqual(result["status"], "CLOSED_NODE")
                    self.assertEqual(writer.call_count, 2)
                else:
                    self.assertEqual(result["status"], "HOLD")
                    self.assertIn(
                        f"SUPPLIER_PREFLIGHT_NOT_EXACT_FIT:{status}",
                        result["holds"],
                    )
                    writer.assert_not_called()

    def test_supplier_output_parser_rejects_malformed_and_exit_mismatch(self) -> None:
        malformed = subprocess.CompletedProcess(
            args=["supplier"], returncode=0, stdout="{} trailing", stderr=""
        )
        with mock.patch.object(workflow_runtime.subprocess, "run", return_value=malformed):
            result = workflow_runtime._supplier_preflight_receipt(
                Path("/repo"),
                query="supplier",
                candidate="Q3.RouteB.candidate",
                target="Q3.RouteB.target",
                candidate_provenance="SOURCE_DECLARED",
            )
        self.assertIn("SUPPLIER_PREFLIGHT_OUTPUT_INVALID", result["validation_error"])

        payload = supplier_payload("EXACT_FIT")
        mismatch = subprocess.CompletedProcess(
            args=["supplier"], returncode=2, stdout=json.dumps(payload), stderr=""
        )
        with mock.patch.object(workflow_runtime.subprocess, "run", return_value=mismatch):
            result = workflow_runtime._supplier_preflight_receipt(
                Path("/repo"),
                query="supplier",
                candidate="Q3.RouteB.candidate",
                target="Q3.RouteB.target",
                candidate_provenance="SOURCE_DECLARED",
            )
        self.assertEqual(
            result["validation_error"], "SUPPLIER_PREFLIGHT_EXIT_STATUS_MISMATCH"
        )

    def test_supplier_contract_receipt_binds_candidate_and_valid_contract(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            receipt = repo / "contract.json"
            payload = {
                "schema": workflow_runtime.DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
                "candidate": "wrong",
                "target": "Q3.RouteB.target",
                "candidate_provenance": "SOURCE_DECLARED",
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

    def test_supplier_contract_receipt_binds_nested_object_and_consumer(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            receipt = repo / "contract.json"
            payload = {
                "schema": workflow_runtime.DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
                "candidate": "Q3.RouteB.candidate",
                "target": "Q3.RouteB.target",
                "candidate_provenance": "SOURCE_DECLARED",
                "contract": dependency_contract(),
            }
            payload["contract"]["original_requested_object"] = "Q3.RouteB.other"
            receipt.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CONSUMER_FIRST_CONTRACT_ORIGINAL_OBJECT_MISMATCH",
            ):
                workflow_runtime._dependency_contract_receipt(
                    repo,
                    receipt,
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                )
            payload["contract"] = dependency_contract()
            payload["contract"]["downstream_consumer"] = "Q3.RouteB.other"
            receipt.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CONSUMER_FIRST_CONTRACT_DOWNSTREAM_CONSUMER_MISMATCH",
            ):
                workflow_runtime._dependency_contract_receipt(
                    repo,
                    receipt,
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                )

    def test_supplier_contract_receipt_binds_active_exact_edge(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            receipt = repo / "contract.json"
            receipt.write_text(json.dumps({
                "schema": workflow_runtime.DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
                "candidate": "Q3.RouteB.candidate",
                "target": "Q3.RouteB.target",
                "candidate_provenance": "SOURCE_DECLARED",
                "contract": dependency_contract(),
            }) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CONSUMER_FIRST_CONTRACT_ACTIVE_THEOREM_EDGE_MISMATCH",
            ):
                workflow_runtime._dependency_contract_receipt(
                    repo,
                    receipt,
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                    exact_theorem_pin="Q3.RouteB.other",
                    exact_consumer_pin="Q3.RouteB.target",
                )
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CONSUMER_FIRST_CONTRACT_ACTIVE_CONSUMER_EDGE_MISMATCH",
            ):
                workflow_runtime._dependency_contract_receipt(
                    repo,
                    receipt,
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                    exact_theorem_pin="Q3.RouteB.candidate",
                    exact_consumer_pin="Q3.RouteB.other",
                )
class ControlV10BenchmarkPlants(unittest.TestCase):
    @staticmethod
    def _shadow_plan(**overrides: object) -> dict[str, object]:
        payload: dict[str, object] = {
            "schema": workflow_runtime.SHADOW_PLAN_SCHEMA,
            "mode": workflow_runtime.PRODUCTION_PLAN_MODE,
            "status": "HOLD",
            "holds": ["NODE_REGISTRY_EXACT_EDGE_REQUIRED"],
            "blocked_features": [
                {"feature": feature}
                for feature in sorted(benchmark.REQUIRED_BLOCKED_FEATURES)
            ],
            "startup": {
                "schema": "q3_startup_snapshot.v10.v1",
                "mode": "PRODUCTION_V10_READ_ONLY",
                "fatal_errors": [],
                "honesty_state": "CHALLENGER_NOT_RH",
                "selected_goal": benchmark.EXPECTED_GOAL,
                "exact_node_pin": benchmark.EXPECTED_NODE,
                "exact_source_pin": benchmark.EXPECTED_SOURCE_PIN,
                "exact_theorem_pin": None,
                "exact_consumer_pin": None,
            },
            "run_authorized": False,
            "writes_performed": False,
            "legacy_v9_authority_unchanged": False,
            "PX_RH_CLAIM": "NOT_MADE",
            "node_registry": {"detail": "same"},
        }
        payload.update(overrides)
        return payload

    @staticmethod
    def _timing_stderr(
        duration_ms: float = 0.0, *, constructor_calls: int = 1
    ) -> str:
        payload = {
            "schema": workflow_runtime._BENCHMARK_TIMING_SCHEMA,
            "startup_duration_ms": duration_ms,
            "snapshot_constructor_calls": constructor_calls,
        }
        return workflow_runtime._BENCHMARK_TIMING_PREFIX + json.dumps(
            payload, separators=(",", ":"), sort_keys=True
        )

    @classmethod
    def _runtime_records(
        cls,
        *,
        direct_argv: list[list[str]] | None = None,
        observed_runtime_argv: list[list[str]] | None = None,
        production_payload: dict[str, object] | None = None,
        direct_payload: dict[str, object] | None = None,
        audited_payload: dict[str, object] | None = None,
        opened_repo_paths: list[str] | None = None,
    ) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
        production_repo = Path("/tmp/production")
        direct_repo = Path("/tmp/direct")
        audited_repo = Path("/tmp/audited")
        commands = direct_argv or [["git", "status"]]
        observed = observed_runtime_argv or [list(command) for command in commands]
        production_plan = production_payload or cls._shadow_plan()
        direct_plan = direct_payload or json.loads(json.dumps(production_plan))
        audited_plan = audited_payload or json.loads(json.dumps(production_plan))
        direct_counts = {
            "subprocess": len(commands),
            "git": sum(
                bool(command) and Path(command[0]).name == "git"
                for command in commands
            ),
            "path": 1,
            "repo_path": 1,
            "scandir": 0,
            "open": 1,
            "opened_repo_paths": 1,
        }
        descendant_counts = {
            "subprocess": len(observed),
            "git": sum(
                bool(command) and Path(command[0]).name == "git"
                for command in observed
            ),
            "path": 1,
            "repo_path": 1,
            "scandir": 0,
            "open": 1,
            "opened_repo_paths": len(opened_repo_paths or []),
        }
        direct_audit = benchmark._functional_plan_audit(direct_plan)
        audited_audit = benchmark._functional_plan_audit(audited_plan)
        production_audit = benchmark._functional_plan_audit(production_plan)
        direct_sample = {
            "payload": direct_plan,
            "startup": {"duration_ms": 2.0, "counts": dict(direct_counts)},
            "plan": {"duration_ms": 1.0, "counts": dict(direct_counts)},
            "total": {"duration_ms": 3.0, "counts": dict(direct_counts)},
            "result": {},
            "budgets": {"pass": True},
            "snapshot_constructor_calls": 1,
            "runtime_subprocess_argv": [list(command) for command in commands],
            "functional_audit": direct_audit,
        }
        production = {
            "repo": str(production_repo),
            "command": benchmark._workflow_plan_command(production_repo),
            "returncode": 2,
            "duration_ms": 5.0,
            "startup_timing": {
                "schema": workflow_runtime._BENCHMARK_TIMING_SCHEMA,
                "startup_duration_ms": 3.0,
                "snapshot_constructor_calls": 1,
            },
            "payload": production_plan,
            "functional_audit": production_audit,
            "write_audit": {"pass": True},
        }
        direct = {"repo": str(direct_repo), "sample": direct_sample}
        successful = [
            benchmark._workflow_plan_command(audited_repo),
            *[list(command) for command in observed],
        ]
        opened = list(opened_repo_paths or [])
        audited_sample = {
            "payload": audited_plan,
            "startup": {"duration_ms": 4.0, "counts": dict(descendant_counts)},
            "plan": {"duration_ms": 1.0, "counts": dict(descendant_counts)},
            "total": {"duration_ms": 5.0, "counts": dict(descendant_counts)},
            "result": {},
            "budgets": {"pass": True},
            "snapshot_constructor_calls": 1,
            "runtime_subprocess_argv": [list(command) for command in observed],
            "functional_audit": audited_audit,
        }
        audited = {
            "repo": str(audited_repo),
            "command": ["strace", "--", *benchmark._workflow_plan_command(audited_repo)],
            "runtime_command": benchmark._workflow_plan_command(audited_repo),
            "returncode": 2,
            "duration_ms": 6.0,
            "sample": audited_sample,
            "trace_audit": {
                "execve_argv": successful,
                "successful_execve_argv": successful,
                "runtime_execve_argv": [list(command) for command in observed],
                "runtime_subprocess_count": len(observed),
                "runtime_git_count": descendant_counts["git"],
                "opened_repo_paths": opened,
                "opened_repo_paths_count": len(opened),
                "write_events": [],
                "write_free_pass": True,
                "trace_coverage": {"all": True},
                "trace_coverage_pass": True,
                "sentinels_before": {},
                "sentinels_after": {},
                "sentinels_unchanged": True,
                "ignored_repo_paths_in_scope": True,
            },
        }
        return production, direct, audited

    def test_production_timing_parser_fails_closed(self) -> None:
        valid = self._timing_stderr(123.0)
        self.assertEqual(
            benchmark._parse_production_startup_timing(valid)[
                "startup_duration_ms"
            ],
            123.0,
        )
        invalid_cases = (
            ("", "BENCHMARK_STARTUP_TIMING_MISSING"),
            (valid + "\n" + valid, "BENCHMARK_STARTUP_TIMING_DUPLICATE"),
            (
                workflow_runtime._BENCHMARK_TIMING_PREFIX + "{",
                "BENCHMARK_STARTUP_TIMING_INVALID_JSON",
            ),
            (
                workflow_runtime._BENCHMARK_TIMING_PREFIX
                + json.dumps(
                    {
                        "schema": workflow_runtime._BENCHMARK_TIMING_SCHEMA,
                        "startup_duration_ms": -1,
                        "snapshot_constructor_calls": 1,
                    }
                ),
                "BENCHMARK_STARTUP_TIMING_DURATION_INVALID",
            ),
            (
                workflow_runtime._BENCHMARK_TIMING_PREFIX
                + json.dumps(
                    {
                        "schema": workflow_runtime._BENCHMARK_TIMING_SCHEMA,
                        "startup_duration_ms": True,
                        "snapshot_constructor_calls": 1,
                    }
                ),
                "BENCHMARK_STARTUP_TIMING_DURATION_INVALID",
            ),
            (
                workflow_runtime._BENCHMARK_TIMING_PREFIX
                + json.dumps(
                    {
                        "schema": workflow_runtime._BENCHMARK_TIMING_SCHEMA,
                        "startup_duration_ms": 1,
                        "snapshot_constructor_calls": 1,
                        "unknown": "field",
                    }
                ),
                "BENCHMARK_STARTUP_TIMING_FIELDS_INVALID",
            ),
            (
                self._timing_stderr(1.0, constructor_calls=2),
                "BENCHMARK_STARTUP_TIMING_SNAPSHOT_COUNT_INVALID",
            ),
        )
        for stderr, code in invalid_cases:
            with self.subTest(code=code), self.assertRaisesRegex(
                RuntimeError, code
            ):
                benchmark._parse_production_startup_timing(stderr)

    def test_functional_audit_rejects_unexpected_hold_and_unavailable(self) -> None:
        unexpected = benchmark._functional_plan_audit(
            self._shadow_plan(status="FATAL", holds=["FUTURE_FATAL"])
        )
        unavailable = benchmark._functional_plan_audit(
            self._shadow_plan(
                status="HOLD",
                holds=["PRODUCTION_V10_UNAVAILABLE:RuntimeError:boom"],
            )
        )
        expected = benchmark._functional_plan_audit(
            self._shadow_plan()
        )
        self.assertFalse(unexpected["pass"])
        self.assertIn("PLAN_UNEXPECTED_HOLD:FUTURE_FATAL", unexpected["errors"])
        self.assertFalse(unavailable["pass"])
        self.assertIn("PRODUCTION_V10_UNAVAILABLE", unavailable["errors"])
        self.assertTrue(expected["pass"])
        self.assertEqual(
            expected["expected_live_holds"],
            ["NODE_REGISTRY_EXACT_EDGE_REQUIRED"],
        )

    def test_functional_audit_requires_exact_live_hold_contract(self) -> None:
        for mutation in (
            {"status": "READY", "holds": []},
            {"status": "FATAL", "holds": []},
            {
                "status": "FATAL",
                "holds": [
                    "STARTUP_SOURCE_COMMIT_PIN_DRIFT",
                    "STARTUP_SOURCE_COMMIT_PIN_DRIFT",
                ],
            },
            {"startup": {"fatal_errors": [], "honesty_state": "CHALLENGER_NOT_RH"}},
            {
                "startup": {
                    "fatal_errors": ["STARTUP_SOURCE_COMMIT_PIN_DRIFT"],
                    "honesty_state": "NOT_RH",
                }
            },
            {"legacy_v9_authority_unchanged": True},
            {"PX_RH_CLAIM": "MADE"},
        ):
            with self.subTest(mutation=mutation):
                self.assertFalse(
                    benchmark._functional_plan_audit(
                        self._shadow_plan(**mutation)
                    )["pass"]
                )
        accepted = benchmark._functional_plan_audit(self._shadow_plan())
        self.assertTrue(accepted["pass"])
        for field in (
            "exact_live_hold_status_pass",
            "exact_live_hold_set_pass",
            "startup_fatal_set_pass",
            "startup_honesty_state_pass",
            "legacy_v9_not_authority_pass",
            "px_rh_claim_not_made_pass",
        ):
            self.assertTrue(accepted[field], field)

    def test_functional_audit_enforces_exact_identity_and_safety_fields(self) -> None:
        for mutation in (
            {"schema": "wrong"},
            {"mode": "wrong"},
            {"run_authorized": True},
            {"writes_performed": True},
            {"blocked_features": []},
        ):
            with self.subTest(mutation=mutation):
                self.assertFalse(
                    benchmark._functional_plan_audit(
                        self._shadow_plan(**mutation)
                    )["pass"]
                )

    def test_runtime_environment_disables_optional_git_locks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            temp_root = Path(tmp) / "isolated"
            environment = benchmark._runtime_environment(temp_root)
            self.assertEqual(environment["GIT_OPTIONAL_LOCKS"], "0")
            self.assertEqual(environment["PYTHONDONTWRITEBYTECODE"], "1")
            self.assertEqual(Path(environment["TMPDIR"]), temp_root)
            self.assertEqual(
                Path(environment["XDG_CACHE_HOME"]), temp_root / "cache"
            )
            self.assertTrue(temp_root.is_dir())
            self.assertTrue((temp_root / "cache").is_dir())

    def test_instrumented_once_forwards_exact_source_pin(self) -> None:
        guard = _FakeEpochGuard()
        observed: dict[str, object] = {}

        def summarize(
            repo: Path,
            selected_goal_path: object,
            owned_paths: object = (),
            *,
            exact_node_pin: str | None = None,
            exact_source_pin: str | None = None,
            exact_theorem_pin: str | None = None,
            exact_consumer_pin: str | None = None,
        ) -> dict[str, object]:
            observed.update(
                {
                    "repo": repo,
                    "selected_goal_path": selected_goal_path,
                    "owned_paths": owned_paths,
                    "exact_node_pin": exact_node_pin,
                    "exact_source_pin": exact_source_pin,
                    "exact_theorem_pin": exact_theorem_pin,
                    "exact_consumer_pin": exact_consumer_pin,
                }
            )
            return node_registry_summary(status="HOLD")

        with (
            mock.patch.object(
                workflow_runtime,
                "_startup_read_epoch",
                return_value=_fake_startup_epoch(guard),
            ),
            mock.patch.object(
                workflow_runtime,
                "build_startup_snapshot",
                return_value=production_snapshot(),
            ),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "startup_gate_summary",
                side_effect=summarize,
            ),
            mock.patch.object(
                workflow_runtime,
                "_compile_production_logical_plan",
                return_value={"schema": "q3_proof_loop.v1"},
            ),
        ):
            sample = benchmark._instrumented_once(Path("/repo"))

        self.assertEqual(sample["payload"]["schema"], workflow_runtime.SHADOW_PLAN_SCHEMA)
        self.assertEqual(observed["exact_node_pin"], "NODE-058")
        self.assertEqual(observed["exact_source_pin"], "SOURCE-058")
        self.assertEqual(observed["exact_theorem_pin"], "THEOREM-058")
        self.assertEqual(observed["exact_consumer_pin"], "CONSUMER-058")
        self.assertEqual(sample["snapshot_constructor_calls"], 1)

    def test_forbidden_runtime_argv_rejects_heavy_and_legacy_tools(self) -> None:
        commands = [
            ["/opt/bin/lake", "build"],
            ["/opt/bin/lean", "Check.lean"],
            ["bash", "/repo/specs_docs/session_start.sh"],
            ["python3", "/repo/orchestrator/spine.py"],
            ["python3", "/repo/orchestrator/three_body_loop.py"],
            ["bash", "-lc", "cd /repo && lake build Q3"],
        ]
        audit = benchmark._forbidden_argv_audit(commands)
        self.assertFalse(audit["pass"])
        self.assertEqual(
            {item["forbidden"] for item in audit["findings"]},
            benchmark.FORBIDDEN_RUNTIME_COMMANDS,
        )
        self.assertTrue(
            benchmark._forbidden_argv_audit([["git", "rev-parse", "HEAD"]])[
                "pass"
            ]
        )

    def test_descendant_lfs_helper_fanout_consumes_trace_budget(self) -> None:
        direct = [["git", "status", str(index)] for index in range(5)]
        observed = [
            *direct,
            *[["git-lfs", "filter-process", str(index)] for index in range(4)],
            *[["git", "lfs-helper", str(index)] for index in range(16)],
        ]
        production, direct_record, audited = self._runtime_records(
            direct_argv=direct,
            observed_runtime_argv=observed,
            opened_repo_paths=["/tmp/audited/docs/CODEX_CONTROL.md"],
        )
        result = benchmark._combine_runtime_sample(
            production, direct_record, audited
        )
        self.assertEqual(result["total"]["counts"]["subprocess"], 25)
        self.assertEqual(result["total"]["counts"]["git"], 21)
        self.assertFalse(result["operation_count_budget"]["pass"])
        self.assertEqual(
            result["descendant_process_diagnostics"]["subprocess_count"], 25
        )
        self.assertEqual(
            result["descendant_process_diagnostics"]["git_count"], 21
        )
        self.assertTrue(
            result["descendant_process_diagnostics"]["budget_authority"]
        )
        self.assertTrue(result["process_count_crosscheck"]["pass"])

    def test_sixth_direct_git_call_breaks_operation_budget(self) -> None:
        direct = [["git", "status", str(index)] for index in range(6)]
        production, direct_record, audited = self._runtime_records(
            direct_argv=direct,
            observed_runtime_argv=direct,
        )
        result = benchmark._combine_runtime_sample(
            production, direct_record, audited
        )
        self.assertEqual(result["total"]["counts"]["git"], 6)
        self.assertFalse(result["operation_count_budget"]["pass"])

    def test_direct_argv_crosscheck_requires_duplicate_multiplicity(self) -> None:
        command = ["git", "cat-file", "--batch-check", "-Z"]
        audit = benchmark._argv_multiset_containment(
            [command, command],
            [command],
        )
        self.assertFalse(audit["pass"])
        self.assertEqual(
            audit["missing"],
            [
                {
                    "argv": command,
                    "required": 2,
                    "observed": 1,
                    "missing": 1,
                }
            ],
        )

    def test_descendant_lake_helper_breaks_forbidden_audit(self) -> None:
        direct = [["git", "status"]]
        production, direct_record, audited = self._runtime_records(
            direct_argv=direct,
            observed_runtime_argv=[*direct, ["lake", "build", "Q3"]],
        )
        result = benchmark._combine_runtime_sample(
            production, direct_record, audited
        )
        self.assertFalse(result["forbidden_argv_audit"]["pass"])
        self.assertFalse(result["runtime_acceptance"]["forbidden_argv_pass"])
        self.assertIn(
            "lake",
            {
                finding["forbidden"]
                for finding in result["forbidden_argv_audit"]["findings"]
            },
        )

    @staticmethod
    def _trace_sentinels(tag: str) -> dict[str, dict[str, object]]:
        return {
            relative: {"bytes": len(tag), "sha256": tag}
            for relative in benchmark.TRACE_SENTINEL_PATHS
        }

    @staticmethod
    def _covered_trace(repo: Path, root_argv: list[str]) -> str:
        lines = [
            "1 execve(\"/usr/bin/python3\", "
            + json.dumps(root_argv)
            + ", 0x0 /* 0 vars */) = 0"
        ]
        for fd, relative in enumerate(benchmark.TRACE_SENTINEL_PATHS, start=3):
            path = repo / relative
            lines.append(
                f'1 openat(AT_FDCWD, "{path}", O_RDONLY|O_CLOEXEC) = {fd}<{path}>'
            )
        return "\n".join(lines)

    def test_strace_parser_counts_only_unique_repo_paths(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            repo.mkdir()
            trace = "\n".join(
                (
                    f'1 openat(AT_FDCWD, "a", O_RDONLY) = 3<{repo / "a"}>',
                    f'1 openat(AT_FDCWD, "a", O_RDONLY) = 4<{repo / "a"}>',
                    f'1 open("b", O_RDONLY) = 5<{repo / "b"}>',
                    '1 open("x", O_RDONLY) = 6</etc/ld.so.cache>',
                    f'1 open("c", O_RDONLY) = 7<{repo}x/c>',
                )
            )
            opened = benchmark._parse_strace_opened_repo_paths(trace, repo)
        self.assertEqual(opened, sorted((str(repo / "a"), str(repo / "b"))))

    def test_strace_unavailable_fails_closed_before_subprocess(self) -> None:
        with (
            mock.patch.object(benchmark.sys, "platform", "linux"),
            mock.patch.object(benchmark.shutil, "which", return_value=None),
            mock.patch.object(benchmark.subprocess, "run") as run,
            self.assertRaisesRegex(RuntimeError, "STRACE_UNAVAILABLE_FAIL_CLOSED"),
        ):
            benchmark._run_audited_process(
                Path("/repo"), {}, Path("/tmp/control-v10.strace")
            )
        run.assert_not_called()

    def test_strace_runs_the_exact_production_workflow_cli(self) -> None:
        repo = Path("/repo")
        runtime_command = benchmark._workflow_plan_command(repo)
        payload = self._shadow_plan()
        completed = subprocess.CompletedProcess(
            args=[],
            returncode=2,
            stdout=json.dumps(payload),
            stderr=self._timing_stderr(10.0),
        )
        sentinels = self._trace_sentinels("same")
        with tempfile.TemporaryDirectory() as tmp:
            trace_path = Path(tmp) / "runtime.strace"
            trace_path.write_text(
                self._covered_trace(repo, runtime_command), encoding="utf-8"
            )
            with (
                mock.patch.object(benchmark.shutil, "which", return_value="/usr/bin/strace"),
                mock.patch.object(
                    benchmark.subprocess, "run", return_value=completed
                ) as run,
                mock.patch.object(
                    benchmark,
                    "_sentinel_manifest",
                    side_effect=[sentinels, sentinels],
                ),
                mock.patch.object(benchmark.time, "perf_counter", side_effect=[0.0, 0.02]),
            ):
                audited = benchmark._run_audited_process(
                    repo, {}, trace_path
                )
        self.assertEqual(audited["runtime_command"], runtime_command)
        self.assertEqual(audited["sample"]["payload"], payload)
        traced_command = run.call_args.args[0]
        self.assertEqual(traced_command[-len(runtime_command) :], runtime_command)
        self.assertNotIn("--single", traced_command)

    def test_strace_empty_and_unparsed_fail_closed(self) -> None:
        sentinels = self._trace_sentinels("same")
        for trace, error in (
            ("", "STRACE_TRACE_EMPTY_FAIL_CLOSED"),
            ("not a syscall", "STRACE_TRACE_UNPARSED_FAIL_CLOSED"),
        ):
            with self.subTest(error=error), self.assertRaisesRegex(
                RuntimeError, error
            ):
                benchmark._analyze_strace(
                    trace,
                    Path("/repo"),
                    expected_root_argv=["python3", "benchmark.py", "--single"],
                    sentinels_before=sentinels,
                    sentinels_after=sentinels,
                )

    def test_strace_coalesces_unfinished_and_rejects_orphan_fragments(self) -> None:
        repo = Path("/repo")
        root_argv = ["python3", "/repo/benchmark.py", "--single"]
        lines = [
            "1 execve(\"/usr/bin/python3\", "
            + json.dumps(root_argv)
            + ", 0x0 /* 0 vars */) = 0"
        ]
        first, *remaining = benchmark.TRACE_SENTINEL_PATHS
        first_path = repo / first
        lines.extend(
            (
                f'1 openat(AT_FDCWD, "{first_path}", O_RDONLY|O_CLOEXEC '
                "<unfinished ...>",
                f'1 <... openat resumed>) = 3<{first_path}>',
            )
        )
        for fd, relative in enumerate(remaining, start=4):
            path = repo / relative
            lines.append(
                f'1 openat(AT_FDCWD, "{path}", O_RDONLY|O_CLOEXEC) = {fd}<{path}>'
            )
        sentinels = self._trace_sentinels("same")
        audit = benchmark._analyze_strace(
            "\n".join(lines),
            repo,
            expected_root_argv=root_argv,
            sentinels_before=sentinels,
            sentinels_after=sentinels,
        )
        self.assertTrue(audit["trace_coverage_pass"])
        with self.assertRaisesRegex(RuntimeError, "STRACE_FRAGMENT_GAP:ORPHAN_RESUMED"):
            benchmark._analyze_strace(
                self._covered_trace(repo, root_argv)
                + "\n1 <... openat resumed>) = 9</repo/orphan>",
                repo,
                expected_root_argv=root_argv,
                sentinels_before=sentinels,
                sentinels_after=sentinels,
            )

    def test_strace_copy_syscalls_use_ordered_destination_fd(self) -> None:
        repo = Path("/repo")
        trace = "\n".join(
            (
                "1 copy_file_range(3</repo/source-a>, NULL, "
                "4</repo/destination-a>, NULL, 1, 0) = 1",
                "1 sendfile(5</repo/destination-b>, "
                "6</repo/source-b>, NULL, 1) = 1",
            )
        )
        events = benchmark._strace_write_events(trace, repo)
        self.assertEqual(
            [event["path"] for event in events],
            ["/repo/destination-a", "/repo/destination-b"],
        )
        self.assertTrue(
            all(event["kind"] == "COPY_DESTINATION" for event in events)
        )

    def test_strace_quoted_sentinel_without_successful_open_is_red(self) -> None:
        repo = Path("/repo")
        root_argv = ["python3", "/repo/benchmark.py", "--single"]
        lines = [
            "1 execve(\"/usr/bin/python3\", "
            + json.dumps(root_argv)
            + ", 0x0 /* 0 vars */) = 0"
        ]
        for fd, relative in enumerate(benchmark.TRACE_SENTINEL_PATHS[:2], start=3):
            path = repo / relative
            lines.append(
                f'1 openat(AT_FDCWD, "{path}", O_RDONLY|O_CLOEXEC) = {fd}<{path}>'
            )
        missing = repo / benchmark.TRACE_SENTINEL_PATHS[2]
        lines.append(f'1 write(1</dev/null>, "{missing}", 1) = 1')
        sentinels = self._trace_sentinels("same")
        with self.assertRaisesRegex(
            RuntimeError,
            "STRACE_TRACE_COVERAGE_INCOMPLETE:all_sentinels_successfully_opened",
        ):
            benchmark._analyze_strace(
                "\n".join(lines),
                repo,
                expected_root_argv=root_argv,
                sentinels_before=sentinels,
                sentinels_after=sentinels,
            )

    def test_strace_counts_only_successful_runtime_execve(self) -> None:
        repo = Path("/repo")
        root_argv = ["python3", "/repo/benchmark.py", "--single"]
        trace = "\n".join(
            (
                self._covered_trace(repo, root_argv),
                '2 execve("/missing/git", ["git", "status"], 0x0) = -2 ENOENT',
                '2 execve("/usr/bin/git", ["git", "status"], 0x0) = 0',
            )
        )
        sentinels = self._trace_sentinels("same")
        audit = benchmark._analyze_strace(
            trace,
            repo,
            expected_root_argv=root_argv,
            sentinels_before=sentinels,
            sentinels_after=sentinels,
        )
        self.assertEqual(audit["runtime_subprocess_count"], 1)
        self.assertEqual(audit["runtime_git_count"], 1)
        self.assertEqual(audit["runtime_execve_argv"], [["git", "status"]])

    def test_strace_counts_repeated_root_argv_as_runtime_execve(self) -> None:
        repo = Path("/repo")
        root_argv = ["python3", "/repo/benchmark.py", "--single"]
        trace = self._covered_trace(repo, root_argv) + (
            "\n2 execve(\"/usr/bin/python3\", "
            + json.dumps(root_argv)
            + ", 0x0 /* 0 vars */) = 0"
        )
        sentinels = self._trace_sentinels("same")
        audit = benchmark._analyze_strace(
            trace,
            repo,
            expected_root_argv=root_argv,
            sentinels_before=sentinels,
            sentinels_after=sentinels,
        )
        self.assertEqual(audit["runtime_subprocess_count"], 1)
        self.assertEqual(audit["runtime_git_count"], 0)
        self.assertEqual(audit["runtime_execve_argv"], [root_argv])

    def test_strace_write_audit_includes_ignored_lake_paths(self) -> None:
        repo = Path("/repo")
        root_argv = ["python3", "/repo/benchmark.py", "--single"]
        trace = self._covered_trace(repo, root_argv) + (
            '\n1 openat(AT_FDCWD, "/repo/.lake/build/new.bin", '
            'O_WRONLY|O_CREAT|O_TRUNC, 0666) = 8</repo/.lake/build/new.bin>'
            '\n1 write(9</repo/.lake/build/cache.bin>, "x", 1) = 1'
        )
        sentinels = self._trace_sentinels("same")
        audit = benchmark._analyze_strace(
            trace,
            repo,
            expected_root_argv=root_argv,
            sentinels_before=sentinels,
            sentinels_after=sentinels,
        )
        self.assertTrue(audit["trace_coverage_pass"])
        self.assertFalse(audit["write_free_pass"])
        self.assertEqual(
            audit["write_events"],
            [
                {
                    "line": 5,
                    "syscall": "openat",
                    "kind": "WRITE_CAPABLE_OPEN",
                    "path": "/repo/.lake/build/new.bin",
                },
                {
                    "line": 6,
                    "syscall": "write",
                    "kind": "FD_WRITE_OR_TRUNCATE",
                    "path": "/repo/.lake/build/cache.bin",
                }
            ],
        )

    def test_git_lfs_tmp_write_is_detected_inside_dot_git(self) -> None:
        repo = Path("/repo")
        root_argv = ["python3", "/repo/workflow_runtime.py", "plan"]
        lfs_tmp = repo / ".git/lfs/tmp/object.part"
        trace = self._covered_trace(repo, root_argv) + (
            '\n2 execve("/usr/bin/git-lfs", '
            '["git-lfs", "filter-process"], 0x0) = 0'
            f'\n2 openat(AT_FDCWD, "{lfs_tmp}", '
            f'O_WRONLY|O_CREAT|O_TRUNC, 0666) = 8<{lfs_tmp}>'
            f'\n2 write(8<{lfs_tmp}>, "x", 1) = 1'
        )
        sentinels = self._trace_sentinels("same")
        audit = benchmark._analyze_strace(
            trace,
            repo,
            expected_root_argv=root_argv,
            sentinels_before=sentinels,
            sentinels_after=sentinels,
        )
        self.assertFalse(audit["write_free_pass"])
        self.assertIn(
            str(lfs_tmp),
            {event["path"] for event in audit["write_events"]},
        )

    def test_git_index_lock_write_and_rename_are_detected(self) -> None:
        repo = Path("/repo")
        root_argv = ["python3", "/repo/workflow_runtime.py", "plan"]
        index_lock = repo / ".git/index.lock"
        index = repo / ".git/index"
        trace = self._covered_trace(repo, root_argv) + (
            f'\n2 openat(AT_FDCWD, "{index_lock}", '
            f'O_WRONLY|O_CREAT|O_EXCL, 0666) = 8<{index_lock}>'
            f'\n2 rename("{index_lock}", "{index}") = 0'
        )
        sentinels = self._trace_sentinels("same")
        audit = benchmark._analyze_strace(
            trace,
            repo,
            expected_root_argv=root_argv,
            sentinels_before=sentinels,
            sentinels_after=sentinels,
        )
        self.assertFalse(audit["write_free_pass"])
        events = audit["write_events"]
        self.assertIn(str(index_lock), {event["path"] for event in events})
        self.assertTrue(
            any(
                event["syscall"] == "rename" and event["path"] == str(index)
                for event in events
            )
        )

    def test_cold_sparse_checkout_uses_minimal_runtime_surface(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp) / "checkout"
            (destination / ".git").mkdir(parents=True)
            for relative in benchmark.COLD_REQUIRED_PATHS:
                path = destination / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fixture\n", encoding="utf-8")
            goal = destination / "docs/routeB_bus/058_fixture.goal.md"
            goal.parent.mkdir(parents=True, exist_ok=True)
            goal.write_text("fixture\n", encoding="utf-8")
            source_relative = "docs/routeB_bus/proshka/fixture-source.md"
            source = destination / source_relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("fixture\n", encoding="utf-8")
            completed = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="", stderr=""
            )
            with mock.patch.object(
                benchmark.subprocess, "run", return_value=completed
            ) as run:
                result = benchmark._isolated_checkout(
                    Path("/repo"),
                    destination,
                    extra_sparse_paths=(source_relative,),
                )
        self.assertEqual(result, destination)
        sparse_set = next(
            call.args[0]
            for call in run.call_args_list
            if call.args[0][:3]
            == ["git", "sparse-checkout", "set"]
        )
        self.assertIn("/docs/routeB_bus/*.goal.md", sparse_set)
        self.assertIn("/docs/routeB_bus/*.answer.md", sparse_set)
        self.assertNotIn("/docs/routeB_bus/**/*.goal.md", sparse_set)
        self.assertNotIn("/docs/routeB_bus/**/*.answer.md", sparse_set)
        self.assertIn("/" + source_relative, sparse_set)
        self.assertIn("/orchestrator/proof_loop.py", sparse_set)
        for relative in benchmark.COLD_REQUIRED_PATHS:
            self.assertIn("/" + relative, sparse_set)
        for broad_pattern in (
            "/docs/cartographer/",
            "/docs/routeB_bus/",
            "/orchestrator/",
            "/scripts/",
            "/specs_docs/",
            "/q3.lean.aristotle/Q3/Benchmarks/",
            "/q3.lean.aristotle/Q3/Proofs/RouteB/",
        ):
            self.assertNotIn(broad_pattern, sparse_set)

    def test_cold_required_paths_cover_production_logical_plan_surface(self) -> None:
        required = set(benchmark.COLD_REQUIRED_PATHS)
        candidate = set(benchmark.PHASE_A_CANDIDATE_PATHS)
        self.assertTrue(
            {
                "docs/CODEX_CONTROL.md",
                "docs/cartographer/TOOLS.yaml",
                "orchestrator/proof_loop.py",
            }
            <= candidate
        )
        self.assertTrue(
            {
                "docs/cartographer/TOOLS.yaml",
                "docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md",
                "orchestrator/proof_loop.py",
                "orchestrator/roof_port_ledger.py",
                "orchestrator/state/CHANNEL_RUNTIME.json",
                "q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean",
                "q3.lean.aristotle/Q3/Proofs/RouteB/D0CanonicalApproximation.lean",
                "q3.lean.aristotle/Q3/Proofs/RouteB/D0PostAnchorMontel.lean",
                "q3.lean.aristotle/Q3/Proofs/RouteB/D0StripMontelRefinement.lean",
                (
                    "q3.lean.aristotle/Q3/Proofs/RouteB/"
                    "G6N1SelectedFerrersN2CompactDecayAssembly.lean"
                ),
                "q3.lean.aristotle/aristotle_db/knowledge.db",
            }
            <= required
        )

    def test_clean_goal_058_production_plan_fits_output_budget(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory(prefix="q3-v10-output-budget-") as tmp:
            candidate = benchmark._candidate_checkout(repo, Path(tmp) / "candidate")
            plan = workflow_runtime.live_plan_v10(candidate, owned_paths=[])
            rendered = workflow_runtime.render_plan_v10(plan)

        payload = json.loads(rendered)
        self.assertLessEqual(
            len(rendered.encode("utf-8")), workflow_runtime.SHADOW_PLAN_MAX_BYTES
        )
        self.assertEqual(payload["status"], "HOLD")
        self.assertEqual(
            payload["selected_goal"], benchmark.EXPECTED_GOAL
        )
        self.assertNotIn("PRODUCTION_V10_OUTPUT_LIMIT_EXCEEDED", payload["holds"])
        self.assertEqual(
            payload["logical_plan"]["proof_loop"]["next_joint"][
                "candidate_details_ref"
            ],
            "cords.open_joints",
        )

    def test_cold_sparse_checkout_rejects_any_forbidden_payload(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp) / "checkout"
            (destination / ".git").mkdir(parents=True)
            for relative in benchmark.COLD_REQUIRED_PATHS:
                path = destination / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fixture\n", encoding="utf-8")
            goal = destination / "docs/routeB_bus/058_fixture.goal.md"
            goal.parent.mkdir(parents=True, exist_ok=True)
            goal.write_text("fixture\n", encoding="utf-8")
            rogue = (
                destination
                / "docs/routeB_bus/litreview/pdfs/rogue-uppercase.PDF"
            )
            rogue.parent.mkdir(parents=True, exist_ok=True)
            rogue.write_text("fixture\n", encoding="utf-8")
            completed = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="", stderr=""
            )
            with mock.patch.object(
                benchmark.subprocess, "run", return_value=completed
            ), self.assertRaisesRegex(
                RuntimeError, "COLD_CHECKOUT_NON_STARTUP_LFS_PAYLOAD_PRESENT"
            ):
                benchmark._isolated_checkout(Path("/repo"), destination)

    def test_materialized_cold_checkout_contains_no_filter_lfs_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source"
            destination = root / "checkout"
            subprocess.run(
                ["git", "init", "--quiet", str(source)],
                check=True,
                capture_output=True,
            )
            tracked: list[str] = []
            for relative in benchmark.COLD_REQUIRED_PATHS:
                path = source / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fixture\n", encoding="utf-8")
                tracked.append(relative)
            goal_relative = "docs/routeB_bus/058_fixture.goal.md"
            goal = source / goal_relative
            goal.parent.mkdir(parents=True, exist_ok=True)
            goal.write_text("fixture\n", encoding="utf-8")
            tracked.append(goal_relative)
            attributes = source / ".gitattributes"
            attributes.write_text(
                "payloads/*.bin filter=lfs diff=lfs merge=lfs -text\n",
                encoding="utf-8",
            )
            tracked.append(".gitattributes")
            subprocess.run(
                ["git", "add", "--", *tracked],
                cwd=source,
                check=True,
                capture_output=True,
            )
            blob = subprocess.run(
                ["git", "hash-object", "-w", "--stdin"],
                cwd=source,
                check=True,
                capture_output=True,
                text=True,
                input="lfs payload excluded from sparse checkout\n",
            ).stdout.strip()
            subprocess.run(
                [
                    "git",
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    "100644",
                    blob,
                    "payloads/rogue.bin",
                ],
                cwd=source,
                check=True,
                capture_output=True,
            )
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Q3 Benchmark",
                    "-c",
                    "user.email=q3-benchmark.invalid",
                    "commit",
                    "--quiet",
                    "-m",
                    "fixture",
                ],
                cwd=source,
                check=True,
                capture_output=True,
            )
            checkout = benchmark._isolated_checkout(source, destination)
            self.assertFalse((checkout / "payloads/rogue.bin").exists())
            self.assertEqual(
                benchmark._materialized_lfs_filter_paths(checkout),
                (),
            )

    def test_physical_goal_source_paths_are_exact_and_unanswered_only(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            bus = repo / "docs/routeB_bus"
            bus.mkdir(parents=True)
            source_relative = "docs/routeB_bus/proshka/exact-source.md"
            direct_goal = bus / "058_fixture.goal.md"
            direct_goal.write_text(
                "```yaml\nGOAL: 058\nSTATUS: OPEN\n"
                f"SOURCE: {source_relative}\n```\n",
                encoding="utf-8",
            )
            nested_goal = bus / "nested/059_ignored.goal.md"
            nested_goal.parent.mkdir(parents=True)
            nested_goal.write_text(
                "```yaml\nGOAL: 059\nSTATUS: OPEN\n"
                "SOURCE: docs/routeB_bus/proshka/ignored-nested.md\n```\n",
                encoding="utf-8",
            )
            (bus / "057_answered.goal.md").write_text(
                "```yaml\nGOAL: 057\nSTATUS: OPEN\n"
                "SOURCE: docs/routeB_bus/proshka/ignored.md\n```\n",
                encoding="utf-8",
            )
            (bus / "057_answered.answer.md").write_text(
                "answered\n", encoding="utf-8"
            )
            self.assertEqual(
                benchmark._physical_goal_source_paths(repo),
                (source_relative,),
            )

    def test_extra_sparse_path_validation_fails_closed(self) -> None:
        for invalid in (
            "",
            "/absolute",
            "../escape",
            "a/../escape",
            "a\\b",
            "docs/**",
            "docs/file?.md",
            "docs/[ab].md",
            "docs/file.md\n/rogue/**",
            "docs/file.md\r/rogue/**",
        ):
            with self.subTest(invalid=invalid), self.assertRaisesRegex(
                RuntimeError, "COLD_CHECKOUT_EXTRA_SPARSE_PATH_INVALID"
            ):
                benchmark._canonical_sparse_paths((invalid,))

    def test_active_current_task_is_an_exact_dynamic_sparse_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            current = repo / "docs/Codex/CURRENT.md"
            current.parent.mkdir(parents=True)
            current.write_text(
                "```yaml\nstatus: ACTIVE\n"
                "task_file: docs/Codex/TASK_exact.md\n```\n",
                encoding="utf-8",
            )
            self.assertEqual(
                benchmark._active_current_task_paths(repo),
                ("docs/Codex/TASK_exact.md",),
            )

    def test_every_direct_production_run_audits_ignored_tree_writes(self) -> None:
        payload = json.dumps(self._shadow_plan())
        completed = subprocess.CompletedProcess(
            args=[],
            returncode=2,
            stdout=payload,
            stderr=self._timing_stderr(),
        )
        stable = {
            "sha256": "stable",
            "entry_count": 1,
            "entries": {".lake/cache.bin": {"sha256": "before"}},
            "scope": "FULL_REPO_TREE_EXCLUDING_DOT_GIT_INCLUDES_IGNORED_PATHS",
        }
        mutated = {
            **stable,
            "sha256": "mutated",
            "entries": {".lake/cache.bin": {"sha256": "after"}},
        }
        with (
            mock.patch.object(
                benchmark,
                "_non_git_tree_manifest",
                side_effect=[stable, stable, stable, mutated],
            ),
            mock.patch.object(
                benchmark.subprocess, "run", return_value=completed
            ) as run,
        ):
            first = benchmark._run_production_cli(Path("/repo"), {})
            with self.assertRaisesRegex(
                RuntimeError,
                "BENCHMARK_DIRECT_PRODUCTION_REPO_WRITE:.lake/cache.bin",
            ):
                benchmark._run_production_cli(Path("/repo"), {})
        self.assertTrue(first["write_audit"]["pass"])
        self.assertTrue(
            first["write_audit"]["measurement_excludes_manifest_wall"]
        )
        self.assertEqual(run.call_count, 2)
        self.assertEqual(
            run.call_args_list[0].args[0],
            [
                benchmark.sys.executable,
                "/repo/orchestrator/workflow_runtime.py",
                "--root",
                "/repo",
                "plan",
                "--benchmark-startup-timing",
            ],
        )

    def test_cold_runs_production_before_separate_audited_checkout(self) -> None:
        events: list[str] = []
        environments: list[tuple[str, str]] = []

        def checkout(_repo: Path, destination: Path) -> Path:
            events.append("checkout:" + destination.name)
            return destination

        def production(repo: Path, environment: dict[str, str]) -> object:
            events.append("production:" + repo.name)
            environments.append(("production", environment["TMPDIR"]))
            return object()

        def direct(repo: Path, environment: dict[str, str]) -> object:
            events.append("direct:" + repo.name)
            environments.append(("direct", environment["TMPDIR"]))
            return object()

        def audited(
            repo: Path, environment: dict[str, str], _trace_path: Path
        ) -> object:
            events.append("audited:" + repo.name)
            environments.append(("audited", environment["TMPDIR"]))
            return object()

        with (
            tempfile.TemporaryDirectory() as tmp,
            mock.patch.object(
                benchmark, "_isolated_checkout", side_effect=checkout
            ),
            mock.patch.object(
                benchmark, "_run_production_cli", side_effect=production
            ),
            mock.patch.object(
                benchmark, "_run_direct_instrumentation", side_effect=direct
            ),
            mock.patch.object(
                benchmark, "_run_audited_process", side_effect=audited
            ),
            mock.patch.object(
                benchmark, "_combine_runtime_sample", return_value={}
            ),
            mock.patch.object(benchmark, "_plant_production_shape"),
        ):
            result = benchmark._cold_once(Path("/source"), Path(tmp))
        self.assertEqual(
            events,
            [
                "checkout:production-checkout",
                "production:production-checkout",
                "checkout:audited-checkout",
                "direct:audited-checkout",
                "audited:audited-checkout",
            ],
        )
        self.assertEqual(len(set(result["cold_checkout_paths"].values())), 2)
        self.assertEqual(
            [name for name, _path in environments],
            ["production", "direct", "audited"],
        )
        self.assertEqual(len({path for _name, path in environments}), 3)

    def test_prime_is_exactly_one_production_workflow_run(self) -> None:
        production_result = {"prime": True, "write_audit": {"pass": True}}
        with (
            tempfile.TemporaryDirectory() as tmp,
            mock.patch.object(
                benchmark, "_run_production_cli", return_value=production_result
            ) as production,
        ):
            result = benchmark._prime_runtime_measurement(
                Path("/repo"), Path(tmp) / "prime"
            )
        self.assertIs(result["production"], production_result)
        self.assertEqual(result["write_audit"], {"pass": True})
        production.assert_called_once()

    def test_prime_rejects_ignored_lake_mutation(self) -> None:
        completed = subprocess.CompletedProcess(
            args=[],
            returncode=2,
            stdout=json.dumps(self._shadow_plan()),
            stderr="",
        )
        before = {
            "sha256": "before",
            "entry_count": 1,
            "entries": {".lake/cache.bin": {"sha256": "before"}},
            "scope": "FULL_REPO_TREE_EXCLUDING_DOT_GIT_INCLUDES_IGNORED_PATHS",
        }
        after = {
            **before,
            "sha256": "after",
            "entries": {".lake/cache.bin": {"sha256": "after"}},
        }
        with tempfile.TemporaryDirectory() as tmp:
            with (
                mock.patch.object(
                    benchmark,
                    "_non_git_tree_manifest",
                    side_effect=[before, after],
                ),
                mock.patch.object(
                    benchmark.subprocess, "run", return_value=completed
                ) as run,
                self.assertRaisesRegex(
                    RuntimeError,
                    "BENCHMARK_DIRECT_PRODUCTION_REPO_WRITE:.lake/cache.bin",
                ),
            ):
                benchmark._prime_runtime_measurement(
                    Path("/repo"), Path(tmp) / "prime"
                )
        run.assert_called_once()

    def test_warm_uses_per_run_audited_counts_after_one_prime(self) -> None:
        events: list[str] = []
        environments: list[tuple[str, str]] = []
        prime = {"prime": True, "write_audit": {"pass": True}}

        def production(
            _repo: Path, environment: dict[str, str]
        ) -> dict[str, int]:
            index = len([name for name, _path in environments if name == "production"])
            events.append(f"production:{index}")
            environments.append(("production", environment["TMPDIR"]))
            return {"run": index + 1}

        def direct(
            _repo: Path, environment: dict[str, str]
        ) -> dict[str, int]:
            index = len([name for name, _path in environments if name == "direct"])
            events.append(f"direct:{index}")
            environments.append(("direct", environment["TMPDIR"]))
            return {"direct": index + 21}

        def audited(
            _repo: Path, environment: dict[str, str], _trace_path: Path
        ) -> dict[str, int]:
            index = len([name for name, _path in environments if name == "audited"])
            events.append(f"audited:{index}")
            environments.append(("audited", environment["TMPDIR"]))
            return {"count": index + 11}

        with (
            tempfile.TemporaryDirectory() as tmp,
            mock.patch.object(
                benchmark, "_prime_runtime_measurement", return_value=prime
            ) as prime_call,
            mock.patch.object(
                benchmark,
                "_run_production_cli",
                side_effect=production,
            ) as production,
            mock.patch.object(
                benchmark,
                "_run_audited_process",
                side_effect=audited,
            ) as audited,
            mock.patch.object(
                benchmark,
                "_run_direct_instrumentation",
                side_effect=direct,
            ) as direct_call,
            mock.patch.object(
                benchmark,
                "_combine_runtime_sample",
                side_effect=lambda current, direct_record, audit: {
                    "run": current["run"],
                    "direct": direct_record["direct"],
                    "count": audit["count"],
                },
            ) as combine,
        ):
            observed_prime, rows = benchmark._warm_samples(
                Path("/repo"), Path(tmp), runs=3
            )
        self.assertIs(observed_prime, prime)
        prime_call.assert_called_once_with(Path("/repo"), Path(tmp) / "prime")
        self.assertEqual(production.call_count, 3)
        self.assertEqual(direct_call.call_count, 3)
        self.assertEqual(audited.call_count, 3)
        self.assertEqual(combine.call_count, 3)
        self.assertEqual(
            rows,
            [
                {"run": 1, "direct": 21, "count": 11},
                {"run": 2, "direct": 22, "count": 12},
                {"run": 3, "direct": 23, "count": 13},
            ],
        )
        self.assertEqual(
            events,
            [
                "production:0",
                "direct:0",
                "audited:0",
                "production:1",
                "direct:1",
                "audited:1",
                "production:2",
                "direct:2",
                "audited:2",
            ],
        )
        for index in range(3):
            run_environments = environments[index * 3 : index * 3 + 3]
            self.assertEqual(
                {name for name, _path in run_environments},
                {"production", "direct", "audited"},
            )
            self.assertEqual(
                len({path for _name, path in run_environments}),
                3,
            )

    def test_full_payload_mismatch_is_red(self) -> None:
        production_payload = self._shadow_plan()
        audited_payload = json.loads(json.dumps(production_payload))
        audited_payload["node_registry"]["detail"] = "different"
        production_record, direct_record, audited_record = self._runtime_records(
            production_payload=production_payload,
            direct_payload=production_payload,
            audited_payload=audited_payload,
        )
        production_record["duration_ms"] = 377.0
        production_record["startup_timing"]["startup_duration_ms"] = 123.0
        direct_record["sample"]["startup"]["duration_ms"] = 1775.0
        audited_record["sample"]["startup"]["duration_ms"] = 2775.0
        result = benchmark._combine_runtime_sample(
            production_record, direct_record, audited_record
        )
        self.assertFalse(
            result["payload_parity"]["production_matches_audited"]
        )
        self.assertFalse(
            result["runtime_acceptance"]["full_payload_parity_pass"]
        )
        self.assertFalse(result["runtime_acceptance"]["pass"])
        self.assertEqual(result["startup"]["duration_ms"], 123.0)
        self.assertEqual(
            result["startup"]["measurement"],
            "DIRECT_PRODUCTION_BUILD_STARTUP_SNAPSHOT_WALL",
        )
        self.assertEqual(result["startup"]["audited_twin_duration_ms"], 2775.0)
        self.assertEqual(result["plan"]["duration_ms"], 254.0)
        self.assertEqual(result["total"]["duration_ms"], 377.0)
        self.assertTrue(
            result["runtime_acceptance"]["snapshot_count_parity_pass"]
        )
        self.assertNotEqual(
            result["startup"]["duration_ms"], result["total"]["duration_ms"]
        )
        production_record["payload"] = audited_payload
        direct_record["sample"]["payload"] = audited_payload
        matched = benchmark._combine_runtime_sample(
            production_record, direct_record, audited_record
        )
        self.assertEqual(matched["startup"]["duration_ms"], 123.0)
        self.assertEqual(
            matched["startup"]["audited_twin_duration_ms"], 2775.0
        )
        self.assertTrue(matched["runtime_acceptance"]["pass"])

    def test_authoritative_benchmark_requires_exact_20_by_3_matrix(self) -> None:
        with self.assertRaisesRegex(
            ValueError, "BENCHMARK_AUTHORITATIVE_MATRIX_REQUIRES_20_WARM_3_COLD"
        ):
            benchmark.benchmark(Path("/repo"), warm_runs=1, cold_runs=1)

    def test_proof_body_plant_targets_exact_registered_theorem(self) -> None:
        source = (
            b"namespace Other\n"
            b"theorem target : True := by\n  trivial\n"
            b"end Other\n\n"
            b"namespace Q3.RouteB\n"
            b"theorem first : True := by\n  trivial\n\n"
            b"theorem target : True := by\n"
            b"  have nested : True := by trivial\n"
            b"  exact nested\n\n"
            b"theorem last : True := by\n  trivial\n"
            b"end Q3.RouteB\n"
        )
        theorem_id = "Q3.RouteB.target"
        planted = benchmark._proof_body_plant_bytes(source, theorem_id)
        assignment = benchmark._proof_body_assignment_offset(source, theorem_id)
        marker = planted.index(benchmark.PROOF_BODY_PLANT_MARKER)
        q3_namespace = planted.index(b"namespace Q3.RouteB")
        target = planted.index(b"theorem target", q3_namespace)
        last = planted.index(b"theorem last")
        self.assertGreater(marker, assignment + len(b":= by"))
        self.assertGreater(marker, target)
        self.assertLess(marker, last)
        self.assertNotIn(benchmark.PROOF_BODY_PLANT_MARKER, planted[:target])
        self.assertEqual(planted.count(benchmark.PROOF_BODY_PLANT_MARKER), 1)

    def test_proof_body_plant_rejects_ambiguous_exact_leaf(self) -> None:
        source = (
            b"namespace Q3.RouteB\n"
            b"theorem target : True := by trivial\n"
            b"theorem target : True := by trivial\n"
            b"end Q3.RouteB\n"
        )
        with self.assertRaisesRegex(
            RuntimeError, "PROOF_BODY_PLANT_EXACT_DECLARATION_COUNT:2"
        ):
            benchmark._proof_body_plant_bytes(source, "Q3.RouteB.target")

    def test_proof_body_plant_skips_binder_default_proof_assignment(self) -> None:
        source = (
            b"namespace Q3.RouteB\n"
            b"theorem target (h : True := by trivial) : True := by\n"
            b"  have nested : True := by trivial\n"
            b"  exact h\n"
            b"end Q3.RouteB\n"
        )
        first_assignment = source.index(b":= by")
        outer_assignment = source.index(b":= by", first_assignment + 1)
        assignment = benchmark._proof_body_assignment_offset(
            source, "Q3.RouteB.target"
        )
        planted = benchmark._proof_body_plant_bytes(
            source, "Q3.RouteB.target"
        )
        marker = planted.index(benchmark.PROOF_BODY_PLANT_MARKER)
        self.assertEqual(assignment, outer_assignment)
        self.assertGreater(marker, outer_assignment + len(b":= by"))
        self.assertNotIn(
            benchmark.PROOF_BODY_PLANT_MARKER,
            planted[:outer_assignment],
        )


if __name__ == "__main__":
    unittest.main()
