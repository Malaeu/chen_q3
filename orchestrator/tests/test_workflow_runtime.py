from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from contextlib import contextmanager
from pathlib import Path
from unittest import mock

from orchestrator import workflow_runtime
from orchestrator import team_records
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
    "terminal_consumer_id": "CONSUMER-058",
    "honesty_state": "CHALLENGER_NOT_RH",
    "convention_lock_id": "LOCK",
}

BLUEPRINT_OUTPUTS = (
    "full/blueprint/blueprint.md",
    "q3.lean.aristotle/blueprint/blueprint_manifest.json",
    "q3.lean.aristotle/blueprint/src/content.tex",
    "q3.lean.aristotle/blueprint/src/print.tex",
    "q3.lean.aristotle/blueprint/src/web.tex",
    "q3.lean.aristotle/blueprint/src/blueprint.sty",
    "q3.lean.aristotle/blueprint/src/plastex.cfg",
    "q3.lean.aristotle/blueprint/src/latexmkrc",
    "q3.lean.aristotle/blueprint/src/macros/common.tex",
    "q3.lean.aristotle/blueprint/src/macros/print.tex",
    "q3.lean.aristotle/blueprint/src/macros/web.tex",
    "q3.lean.aristotle/blueprint/src/extra_styles.css",
)


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


def command_stage(label: str, *, exit_code: int = 0) -> dict[str, object]:
    return {
        "label": label,
        "exit": exit_code,
        "duration_ms": 1,
        "output_sha256": "a" * 64,
    }


def phase_close_output() -> dict[str, object]:
    return {
        "schema": "q3_phase_close.v1",
        "derived_executed": ["routeb-publication-blueprint"],
        "derived_status": [
            {"id": "routeb-publication-blueprint", "status": "CURRENT_WORKTREE"}
        ],
        "gates": [{"path": "gate.sh", "exit": 0}],
        "verdict_migration": {"exit": 0, "pending": False},
        "blueprint_exit": 0,
        "manual_debt": {
            "assembly_review_required": [],
            "insight_required": [],
            "cards": [],
        },
        "commit_push_performed": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }


def close_git_identity(_repo: Path, *args: str) -> str:
    return "a" * 40 if args == ("rev-parse", "HEAD") else "b" * 40


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
    def test_supplier_search_intent_runs_through_canonical_front_door(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            lock = repo / ".git/q3-three-body.writer.lock"
            lock.write_text("lock\n", encoding="utf-8")
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            card = repo / "oracle.md"
            card.write_text("card\n", encoding="utf-8")
            supplier_script = repo / "scripts/supplier_preflight.py"
            supplier_script.parent.mkdir()
            supplier_script.write_text(
                """import argparse, fcntl, json, os
p = argparse.ArgumentParser()
p.add_argument('--search-intent')
a = p.parse_args()
with open('.git/q3-three-body.writer.lock', 'rb') as lock:
    fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    fcntl.flock(lock.fileno(), fcntl.LOCK_UN)
print(json.dumps({'schema': 'q3_search_evidence.v1', 'status': 'PASS',
                  'observed_at': '2026-09-02T12:00:00+00:00'}))
""",
                encoding="utf-8",
            )
            evidence_payload = {
                "schema": "q3_search_evidence.v1",
                "status": "PASS",
                "observed_at": "2026-09-02T12:00:00+00:00",
            }
            observation_id = hashlib.sha256(
                workflow_runtime._canonical_json_bytes({
                    "observed_at": evidence_payload["observed_at"],
                    "evidence": evidence_payload,
                })[:-1]
            ).hexdigest()
            oracle_script = repo / "q3.lean.aristotle/scripts/oracle_questions.py"
            oracle_script.parent.mkdir(parents=True)
            oracle_script.write_text(
                f"""import argparse, hashlib, json, os
p = argparse.ArgumentParser()
p.add_argument('command')
p.add_argument('--card')
p.add_argument('--intent')
p.add_argument('--evidence')
p.add_argument('--inherited-writer-lock-fd', type=int)
a = p.parse_args()
assert a.command == 'record-evidence'
assert a.card == 'oracle.md'
os.fstat(a.inherited_writer_lock_fd)
intent = json.load(open(a.intent, encoding='utf-8'))
evidence = json.load(open(a.evidence, encoding='utf-8'))
assert intent['node_id'] == 'NODE-058'
assert evidence['schema'] == 'q3_search_evidence.v1'
canonical = lambda value: json.dumps(value, sort_keys=True, separators=(',', ':'))
intent_id = hashlib.sha256(canonical(intent).encode()).hexdigest()
stored = dict(evidence, observation_id='{observation_id}')
block = ('<!-- Q3_SEARCH_EVIDENCE_V1_BEGIN intent_id=' + intent_id
         + ' observation_id={observation_id} -->\\n```json\\n' + canonical(stored)
         + '\\n```\\n<!-- Q3_SEARCH_EVIDENCE_V1_END -->\\n')
with open(a.card, 'a', encoding='utf-8') as handle:
    handle.write(block)
print(json.dumps({{'schema':'q3_search_evidence_write.v1','status':'RECORDED','observation_id':'{observation_id}'}}))
""",
                encoding="utf-8",
            )
            intent = {
                "goal_file": "docs/routeB_bus/058.goal.md",
                "node_id": "NODE-058",
                "source_pin": "SOURCE-058",
                "admission": {
                    "theorem": "THEOREM-058",
                    "consumer": "CONSUMER-058",
                },
            }
            startup_payload = production_snapshot().to_dict()
            compiled = {
                "status": "HOLD",
                "selected_goal": startup_payload["selected_goal"],
                "startup": startup_payload,
            }
            argv = [
                "workflow_runtime.py", "--root", str(repo), "run", "--through",
                "supplier-preflight", "--search-intent", str(intent_path),
                "--record-evidence", "--oracle-card", "oracle.md",
                "--owned-path", "oracle.md",
            ]
            with (
                mock.patch.object(workflow_runtime.sys, "argv", argv),
                mock.patch.object(workflow_runtime, "_team_enabled", return_value=False),
                mock.patch.object(
                    workflow_runtime, "live_plan_v10", return_value=compiled
                ) as startup,
                mock.patch.object(
                    workflow_runtime, "_recheck_production_identity", return_value=None
                ),
                mock.patch(
                    "scripts.supplier_preflight.validate_search_intent_runtime",
                    return_value=intent,
                    create=True,
                ),
            ):
                status = workflow_runtime.main()
            self.assertEqual(status, 0)
            self.assertEqual(startup.call_count, 2)
            startup.assert_called_with(repo, owned_paths=["oracle.md"])
            self.assertIn(
                f"observation_id={observation_id}", card.read_text(encoding="utf-8")
            )

    def test_supplier_search_fatal_or_binding_mismatch_never_starts_child(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            startup_payload = production_snapshot().to_dict()
            valid_intent = {
                "goal_file": startup_payload["selected_goal"],
                "node_id": startup_payload["exact_node_pin"],
                "source_pin": startup_payload["exact_source_pin"],
                "admission": None,
            }
            cases = (
                {
                    "status": "FATAL", "selected_goal": startup_payload["selected_goal"],
                    "startup": dict(startup_payload, fatal_errors=["fatal"]),
                },
                {
                    "status": "HOLD", "selected_goal": "docs/routeB_bus/other.goal.md",
                    "startup": startup_payload,
                },
            )
            for compiled in cases:
                with self.subTest(status=compiled["status"]), (
                    mock.patch.object(
                        workflow_runtime, "live_plan_v10", return_value=compiled
                    )
                ), mock.patch(
                    "scripts.supplier_preflight.validate_search_intent_runtime",
                    return_value=valid_intent,
                    create=True,
                ), mock.patch.object(workflow_runtime.subprocess, "run") as child, (
                    mock.patch("builtins.print")
                ):
                    status = workflow_runtime._supplier_search_dispatch(
                        repo,
                        search_intent=intent_path,
                        owned_paths=[],
                        record_evidence=False,
                        oracle_card=None,
                    )
                self.assertEqual(status, 2)
                child.assert_not_called()

    def test_supplier_search_read_only_preserves_child_argv_and_exit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            startup_payload = production_snapshot().to_dict()
            compiled = {
                "status": "HOLD",
                "selected_goal": startup_payload["selected_goal"],
                "startup": startup_payload,
            }
            intent = {
                "goal_file": startup_payload["selected_goal"],
                "node_id": startup_payload["exact_node_pin"],
                "source_pin": startup_payload["exact_source_pin"],
                "admission": None,
            }
            completed = subprocess.CompletedProcess(args=[], returncode=7)
            with (
                mock.patch.object(
                    workflow_runtime, "live_plan_v10", return_value=compiled
                ),
                mock.patch(
                    "scripts.supplier_preflight.validate_search_intent_runtime",
                    return_value=intent,
                ),
                mock.patch.object(
                    workflow_runtime.subprocess, "run", return_value=completed
                ) as child,
            ):
                status = workflow_runtime._supplier_search_dispatch(
                    repo,
                    search_intent=intent_path,
                    owned_paths=[],
                    record_evidence=False,
                    oracle_card=None,
                )
            self.assertEqual(status, 7)
            child.assert_called_once_with(
                [
                    sys.executable,
                    str(repo / "scripts/supplier_preflight.py"),
                    "--search-intent",
                    str(intent_path),
                ],
                cwd=repo,
            )

    def test_supplier_search_record_fails_on_writer_lock_collision(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            lock = repo / ".git/q3-three-body.writer.lock"
            lock.write_text("lock\n", encoding="utf-8")
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            card = repo / "oracle.md"
            card.write_text("card\n", encoding="utf-8")
            startup_payload = production_snapshot().to_dict()
            compiled = {
                "status": "HOLD",
                "selected_goal": startup_payload["selected_goal"],
                "startup": startup_payload,
            }
            intent = {
                "goal_file": startup_payload["selected_goal"],
                "node_id": startup_payload["exact_node_pin"],
                "source_pin": startup_payload["exact_source_pin"],
                "admission": None,
            }
            with lock.open("rb") as contender:
                fcntl.flock(contender.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                with (
                    mock.patch.object(
                        workflow_runtime, "live_plan_v10", return_value=compiled
                    ),
                    mock.patch(
                        "scripts.supplier_preflight.validate_search_intent_runtime",
                        return_value=intent,
                    ),
                    mock.patch.object(
                        workflow_runtime.subprocess,
                        "run",
                        return_value=subprocess.CompletedProcess(
                            args=[],
                            returncode=0,
                            stdout=json.dumps({
                                "schema": "q3_search_evidence.v1",
                                "status": "PASS",
                                "observed_at": "2026-09-02T12:00:00+00:00",
                            }),
                            stderr="",
                        ),
                    ) as child,
                    mock.patch("builtins.print"),
                ):
                    status = workflow_runtime._supplier_search_dispatch(
                        repo,
                        search_intent=intent_path,
                        owned_paths=["oracle.md"],
                        record_evidence=True,
                        oracle_card="oracle.md",
                    )
            self.assertEqual(status, 2)
            self.assertEqual(child.call_count, 1)
            self.assertEqual(card.read_text(encoding="utf-8"), "card\n")

    def test_supplier_search_record_rejects_plan_pin_mutation_before_writer(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            card = repo / "oracle.md"
            card.write_text("card\n", encoding="utf-8")
            startup_payload = production_snapshot().to_dict()
            compiled = {
                "status": "HOLD",
                "selected_goal": startup_payload["selected_goal"],
                "startup": startup_payload,
            }
            mutated = json.loads(json.dumps(compiled))
            mutated["startup"]["exact_source_pin"] = "MUTATED"
            intent = {
                "goal_file": startup_payload["selected_goal"],
                "node_id": startup_payload["exact_node_pin"],
                "source_pin": startup_payload["exact_source_pin"],
                "admission": None,
            }
            with (
                mock.patch.object(
                    workflow_runtime,
                    "live_plan_v10",
                    side_effect=[compiled, mutated],
                ),
                mock.patch(
                    "scripts.supplier_preflight.validate_search_intent_runtime",
                    return_value=intent,
                ),
                mock.patch.object(
                    workflow_runtime.subprocess,
                    "run",
                    return_value=subprocess.CompletedProcess(
                        args=[],
                        returncode=0,
                        stdout=json.dumps({
                            "schema": "q3_search_evidence.v1",
                            "status": "PASS",
                            "observed_at": "2026-09-02T12:00:00+00:00",
                        }),
                        stderr="",
                    ),
                ) as child,
                mock.patch("builtins.print"),
            ):
                status = workflow_runtime._supplier_search_dispatch(
                    repo,
                    search_intent=intent_path,
                    owned_paths=["oracle.md"],
                    record_evidence=True,
                    oracle_card="oracle.md",
                )
            self.assertEqual(status, 2)
            self.assertEqual(child.call_count, 1)

    def test_supplier_search_record_rejects_intent_mutation_after_search(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            (repo / ".git/q3-three-body.writer.lock").write_text(
                "lock\n", encoding="utf-8"
            )
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            card = repo / "oracle.md"
            card.write_text("card\n", encoding="utf-8")
            supplier_script = repo / "scripts/supplier_preflight.py"
            supplier_script.parent.mkdir()
            supplier_script.write_text(
                "import argparse, json\n"
                "p=argparse.ArgumentParser(); p.add_argument('--search-intent'); a=p.parse_args()\n"
                "open(a.search_intent, 'w', encoding='utf-8').write('{\\\"mutated\\\":true}\\n')\n"
                "print(json.dumps({'schema':'q3_search_evidence.v1','status':'PASS',"
                "'observed_at':'2026-09-02T12:00:00+00:00'}))\n",
                encoding="utf-8",
            )
            startup_payload = production_snapshot().to_dict()
            compiled = {
                "status": "HOLD",
                "selected_goal": startup_payload["selected_goal"],
                "startup": startup_payload,
            }
            intent = {
                "goal_file": startup_payload["selected_goal"],
                "node_id": startup_payload["exact_node_pin"],
                "source_pin": startup_payload["exact_source_pin"],
                "admission": None,
            }
            with (
                mock.patch.object(
                    workflow_runtime, "live_plan_v10", return_value=compiled
                ),
                mock.patch.object(
                    workflow_runtime, "_recheck_production_identity", return_value=None
                ),
                mock.patch(
                    "scripts.supplier_preflight.validate_search_intent_runtime",
                    return_value=intent,
                ),
                mock.patch("builtins.print"),
            ):
                status = workflow_runtime._supplier_search_dispatch(
                    repo,
                    search_intent=intent_path,
                    owned_paths=["oracle.md"],
                    record_evidence=True,
                    oracle_card="oracle.md",
                )
            self.assertEqual(status, 2)
            self.assertEqual(card.read_text(encoding="utf-8"), "card\n")

    def test_supplier_search_record_rejects_supplier_card_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            (repo / ".git/q3-three-body.writer.lock").write_text(
                "lock\n", encoding="utf-8"
            )
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            card = repo / "oracle.md"
            card.write_text("card\n", encoding="utf-8")
            supplier_script = repo / "scripts/supplier_preflight.py"
            supplier_script.parent.mkdir()
            supplier_script.write_text(
                "import json\n"
                "open('oracle.md', 'a', encoding='utf-8').write('fake-write\\n')\n"
                "print(json.dumps({'schema':'q3_search_evidence.v1','status':'PASS',"
                "'observed_at':'2026-09-02T12:00:00+00:00'}))\n",
                encoding="utf-8",
            )
            startup_payload = production_snapshot().to_dict()
            compiled = {
                "status": "HOLD",
                "selected_goal": startup_payload["selected_goal"],
                "startup": startup_payload,
            }
            intent = {
                "goal_file": startup_payload["selected_goal"],
                "node_id": startup_payload["exact_node_pin"],
                "source_pin": startup_payload["exact_source_pin"],
                "admission": None,
            }
            with (
                mock.patch.object(
                    workflow_runtime, "live_plan_v10", return_value=compiled
                ),
                mock.patch.object(
                    workflow_runtime, "_recheck_production_identity", return_value=None
                ),
                mock.patch(
                    "scripts.supplier_preflight.validate_search_intent_runtime",
                    return_value=intent,
                ),
                mock.patch("builtins.print"),
            ):
                status = workflow_runtime._supplier_search_dispatch(
                    repo,
                    search_intent=intent_path,
                    owned_paths=["oracle.md"],
                    record_evidence=True,
                    oracle_card="oracle.md",
                )
            self.assertEqual(status, 2)
            self.assertEqual(card.read_text(encoding="utf-8"), "card\nfake-write\n")

    def test_search_writer_receipt_and_noop_postconditions_are_exact(self) -> None:
        observation_id = "e" * 64
        evidence_payload = {
            "schema": "q3_search_evidence.v1",
            "status": "PASS",
            "observed_at": "2026-09-02T12:00:00+00:00",
        }
        frozen_evidence = workflow_runtime._canonical_json_bytes(evidence_payload)
        expected_intent_id = "d" * 64
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError,
            "WRITER_RECEIPT_INVALID",
        ):
            workflow_runtime._parse_search_writer_receipt(
                json.dumps({"schema": "q3_search_evidence.v1", "status": "PASS"}),
                0,
                expected_observation_id=observation_id,
            )
        wrong_observation_id = "f" * 64
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError,
            "WRITER_RECEIPT_INVALID",
        ):
            workflow_runtime._parse_search_writer_receipt(
                json.dumps({
                    "schema": "q3_search_evidence_write.v1",
                    "status": "RECORDED",
                    "observation_id": wrong_observation_id,
                }),
                0,
                expected_observation_id=observation_id,
            )
        with tempfile.TemporaryDirectory() as tmp:
            card = Path(tmp) / "card.md"
            card.write_text(
                "<!-- Q3_SEARCH_EVIDENCE_V1_BEGIN "
                f"intent_id={expected_intent_id} observation_id={observation_id} -->\n"
                "```json\n"
                + json.dumps(
                    dict(evidence_payload, observation_id=observation_id),
                    sort_keys=True,
                    separators=(",", ":"),
                )
                + "\n```\n<!-- Q3_SEARCH_EVIDENCE_V1_END -->\n",
                encoding="utf-8",
            )
            raw = card.read_bytes()
            info = card.stat()
            state = (
                (
                    info.st_dev,
                    info.st_ino,
                    info.st_mode,
                    info.st_size,
                    info.st_mtime_ns,
                    info.st_uid,
                    info.st_gid,
                ),
                hashlib.sha256(raw).hexdigest(),
            )
            workflow_runtime._validate_search_card_postcondition(
                card,
                before=state,
                after=state,
                writer_receipt={
                    "schema": "q3_search_evidence_write.v1",
                    "status": "NOOP",
                    "observation_id": observation_id,
                },
                expected_intent_id=expected_intent_id,
                expected_observation_id=observation_id,
                frozen_evidence=frozen_evidence,
            )
            substituted = workflow_runtime._canonical_json_bytes(
                {"schema": "q3_search_evidence.v1", "status": "INCOMPLETE"}
            )
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "EVIDENCE_BINDING_FAILED",
            ):
                workflow_runtime._validate_search_card_postcondition(
                    card,
                    before=state,
                    after=state,
                    writer_receipt={
                        "schema": "q3_search_evidence_write.v1",
                        "status": "NOOP",
                        "observation_id": observation_id,
                    },
                    expected_intent_id=expected_intent_id,
                    expected_observation_id=observation_id,
                    frozen_evidence=substituted,
                )
            changed = (state[0], "f" * 64)
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CARD_POSTCONDITION_FAILED",
            ):
                workflow_runtime._validate_search_card_postcondition(
                    card,
                    before=state,
                    after=changed,
                    writer_receipt={
                        "schema": "q3_search_evidence_write.v1",
                        "status": "NOOP",
                        "observation_id": observation_id,
                    },
                    expected_intent_id=expected_intent_id,
                    expected_observation_id=observation_id,
                    frozen_evidence=frozen_evidence,
                )
            ownership_changed = (
                (*state[0][:5], state[0][5] + 1, state[0][6]),
                state[1],
            )
            recorded_before = (state[0], "0" * 64)
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "CARD_POSTCONDITION_FAILED",
            ):
                workflow_runtime._validate_search_card_postcondition(
                    card,
                    before=recorded_before,
                    after=ownership_changed,
                    writer_receipt={
                        "schema": "q3_search_evidence_write.v1",
                        "status": "RECORDED",
                        "observation_id": observation_id,
                    },
                    expected_intent_id=expected_intent_id,
                    expected_observation_id=observation_id,
                    frozen_evidence=frozen_evidence,
                )

    def test_search_evidence_tool_is_selected_exactly_once(self) -> None:
        self.assertEqual(
            workflow_runtime.ACTION_TOOLS["SELECT_EXACT_GOAL"].count(
                "workflow-search-evidence"
            ),
            1,
        )

    def test_supplier_search_record_fails_closed_on_writer_failure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            (repo / ".git/q3-three-body.writer.lock").write_text(
                "lock\n", encoding="utf-8"
            )
            intent_path = repo / "intent.json"
            intent_path.write_text("{}\n", encoding="utf-8")
            card = repo / "oracle.md"
            card.write_text("card\n", encoding="utf-8")
            supplier_script = repo / "scripts/supplier_preflight.py"
            supplier_script.parent.mkdir()
            supplier_script.write_text(
                "import json\n"
                "print(json.dumps({'schema':'q3_search_evidence.v1','status':'PASS',"
                "'observed_at':'2026-09-02T12:00:00+00:00'}))\n",
                encoding="utf-8",
            )
            oracle_script = repo / "q3.lean.aristotle/scripts/oracle_questions.py"
            oracle_script.parent.mkdir(parents=True)
            oracle_script.write_text("import sys\nsys.exit(7)\n", encoding="utf-8")
            startup_payload = production_snapshot().to_dict()
            compiled = {
                "status": "HOLD",
                "selected_goal": startup_payload["selected_goal"],
                "startup": startup_payload,
            }
            intent = {
                "goal_file": startup_payload["selected_goal"],
                "node_id": startup_payload["exact_node_pin"],
                "source_pin": startup_payload["exact_source_pin"],
                "admission": None,
            }
            with (
                mock.patch.object(
                    workflow_runtime, "live_plan_v10", return_value=compiled
                ),
                mock.patch.object(
                    workflow_runtime, "_recheck_production_identity", return_value=None
                ),
                mock.patch(
                    "scripts.supplier_preflight.validate_search_intent_runtime",
                    return_value=intent,
                ),
                mock.patch("builtins.print"),
            ):
                status = workflow_runtime._supplier_search_dispatch(
                    repo,
                    search_intent=intent_path,
                    owned_paths=["oracle.md"],
                    record_evidence=True,
                    oracle_card="oracle.md",
                )
            self.assertEqual(status, 2)
            self.assertEqual(card.read_text(encoding="utf-8"), "card\n")

    def _goal_close_files(self, repo: Path) -> dict[str, Path]:
        goal = repo / "docs/routeB_bus/058_live.goal.md"
        goal.parent.mkdir(parents=True)
        goal.write_text(
            "```yaml\nGOAL_ID: '058'\nSTATUS: OPEN\nNODE: NODE-058\n"
            "SOURCE_PIN: SOURCE-058\nTHEOREM: THEOREM-058\n"
            "TERMINAL_CONSUMER: CONSUMER-058\n```\n",
            encoding="utf-8",
        )
        answer = goal.with_name("058_live.answer.md")
        answer.write_text("answer\n", encoding="utf-8")
        attempt = repo / "attempt.json"
        attempt.write_text(json.dumps({"next_action": "CLOSE_GOAL"}) + "\n", encoding="utf-8")
        channel = repo / "orchestrator/state/CHANNEL_RUNTIME.json"
        channel.parent.mkdir(parents=True)
        channel.write_text(json.dumps(exploration_runtime()) + "\n", encoding="utf-8")
        control = repo / "docs/CODEX_CONTROL.md"
        control.write_text("control\n", encoding="utf-8")
        derived = repo / "derived.out"
        derived.write_text("derived\n", encoding="utf-8")
        registry = repo / "docs/cartographer/DERIVED_ARTIFACTS.yaml"
        registry.parent.mkdir(parents=True, exist_ok=True)
        registry.write_text(
            "schema: q3_derived_artifact_registry.v1\nartifacts:\n"
            "  - id: routeb-publication-blueprint\n"
            "    detector: COMMAND_CHECK\n"
            "    inputs: [input.txt]\n"
            "    outputs:\n"
            + "".join(f"      - {path}\n" for path in BLUEPRINT_OUTPUTS)
            + "    authority: INTERNAL_EVIDENCE_BLUEPRINT_NOT_PROOF_OR_EXTERNAL_PUBLICATION\n"
            "    cost_tier: MEDIUM\n"
            "    consumers: [phase-close-publication]\n",
            encoding="utf-8",
        )
        for relative in BLUEPRINT_OUTPUTS:
            output = repo / relative
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(relative + "\n", encoding="utf-8")
        next_spec = repo / "next.json"
        next_spec.write_text("{}\n", encoding="utf-8")
        return {
            "goal": goal, "answer": answer, "attempt": attempt,
            "channel": channel, "derived": derived, "next_spec": next_spec,
        }

    def test_goal_close_receipt_precedes_terminalization_and_retry_is_writer_free(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
                git_head="a" * 40,
                git_tree="b" * 40,
            ).to_dict()
            compiled = {"startup": startup, "selected_goal": startup["selected_goal"]}
            epoch = _FakeWriterEpoch()
            epoch.open = True
            writes: list[str] = []
            real_atomic = workflow_runtime._atomic_bytes

            def crash_after_receipt(path: Path, payload: bytes) -> None:
                writes.append(path.name)
                if path.name.endswith(".goal.md"):
                    raise OSError("crash plant")
                real_atomic(path, payload)

            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": PHASE_KEY, "phase_key_change": False,
                }),
                mock.patch.object(workflow_runtime, "_execution_epoch_hold", return_value=False),
                mock.patch.object(workflow_runtime, "_git", side_effect=close_git_identity),
                mock.patch.object(
                    workflow_runtime,
                    "command_receipt",
                    return_value=command_stage("goal-close"),
                ),
                mock.patch.object(
                    workflow_runtime,
                    "_atomic_bytes",
                    side_effect=crash_after_receipt,
                ),
                self.assertRaises(OSError),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan=compiled,
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=paths["next_spec"],
                    current_phase_key=None,
                    receipts=[],
                )
            self.assertEqual(writes, ["058_live.goal-close.json", "058_live.goal.md"])
            self.assertIn("STATUS: OPEN", paths["goal"].read_text(encoding="utf-8"))

            original_attempt = paths["attempt"].read_bytes()
            real_validate_receipt = workflow_runtime.validate_goal_close_receipt
            validation_calls = 0

            def mutate_attempt_after_receipt_validation(*args, **kwargs):
                nonlocal validation_calls
                result = real_validate_receipt(*args, **kwargs)
                validation_calls += 1
                if validation_calls == 2:
                    paths["attempt"].write_bytes(original_attempt + b" ")
                return result

            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": PHASE_KEY, "phase_key_change": False,
                }),
                mock.patch.object(workflow_runtime, "_git", side_effect=close_git_identity),
                mock.patch.object(
                    workflow_runtime,
                    "validate_goal_close_receipt",
                    side_effect=mutate_attempt_after_receipt_validation,
                ),
                mock.patch.object(
                    workflow_runtime.node_registry_v10,
                    "verify_consumption",
                    return_value={"status": "PASS"},
                ),
                self.assertRaisesRegex(
                    workflow_runtime.WorkflowRuntimeError,
                    "WORKFLOW_CLOSE_INPUT_DRIFT:attempt",
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan=compiled,
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=paths["next_spec"],
                    current_phase_key=None,
                    receipts=[],
                )
            self.assertIn("STATUS: OPEN", paths["goal"].read_text(encoding="utf-8"))
            paths["attempt"].write_bytes(original_attempt)

            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": PHASE_KEY, "phase_key_change": False,
                }),
                mock.patch.object(workflow_runtime, "_git", side_effect=close_git_identity),
                mock.patch.object(
                    workflow_runtime.node_registry_v10,
                    "verify_consumption",
                    side_effect=workflow_runtime.node_registry_v10.NodeRegistryError(
                        "NODE_REGISTRY_SOURCE_BYTES_DRIFT"
                    ),
                ),
                self.assertRaisesRegex(
                    workflow_runtime.WorkflowRuntimeError,
                    "GOAL_CLOSE_RECOVERY_CONSUMPTION_IDENTITY_DRIFT:"
                    "NODE_REGISTRY_SOURCE_BYTES_DRIFT",
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan=compiled,
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=paths["next_spec"],
                    current_phase_key=None,
                    receipts=[],
                    owned_paths=["owned.lean"],
                )
            self.assertIn("STATUS: OPEN", paths["goal"].read_text(encoding="utf-8"))

            def git_identity(_repo: Path, *args: str) -> str:
                return "a" * 40 if args == ("rev-parse", "HEAD") else "b" * 40

            retry_receipts: list[dict[str, object]] = []
            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": PHASE_KEY, "phase_key_change": False,
                }),
                mock.patch.object(workflow_runtime, "_git", side_effect=git_identity),
                mock.patch.object(
                    workflow_runtime.node_registry_v10,
                    "verify_consumption",
                    return_value={"status": "PASS"},
                ),
                mock.patch.object(workflow_runtime, "command_receipt") as writer,
            ):
                status = workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan=compiled,
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=paths["next_spec"],
                    current_phase_key=None,
                    receipts=retry_receipts,
                )
            self.assertEqual(status, "CLOSED_GOAL")
            self.assertIn("STATUS: CLOSED", paths["goal"].read_text(encoding="utf-8"))
            self.assertEqual(retry_receipts[0]["status"], "ALREADY_CLOSED")
            writer.assert_not_called()

    def test_answer_without_receipt_runs_full_node_transaction(self) -> None:
        repo = Path("/repo")
        startup = production_snapshot(next_action="CLOSE_RETRY_PENDING").to_dict()
        epoch = _FakeWriterEpoch()
        epoch.open = True
        with (
            mock.patch.object(
                workflow_runtime,
                "_execute_goal_and_phase_close",
                return_value="CLOSED_GOAL",
            ) as close,
            mock.patch.object(workflow_runtime, "_exists_at_head", return_value=True),
            mock.patch.object(workflow_runtime, "_execution_epoch_hold", return_value=False),
            mock.patch.object(workflow_runtime, "_git", return_value=""),
            mock.patch.object(
                workflow_runtime.node_registry_v10, "verify_consumption",
                return_value={"status": "HOLD", "code": "PLANT_FULL_TRANSACTION"},
            ) as consumption,
            mock.patch.object(workflow_runtime, "command_receipt") as writer,
        ):
            result = workflow_runtime._execute_close_node_transaction(
                repo,
                plan={"startup": startup, "selected_goal": startup["selected_goal"]},
                production_v10=True,
                startup=startup,
                epoch=epoch,
                owned_paths=["owned.md"],
                query=None,
                candidate=None,
                target=None,
                attempt_payload=Path("attempt.json"),
                attempt={"next_action": "CLOSE_GOAL"},
                insight_payload=None,
                run_kernel=False,
                protocol_out=None,
                contract_receipt=None,
                receipts=[],
                holds=[],
            )
        self.assertEqual(result["status"], "HOLD")
        close.assert_not_called()
        consumption.assert_called_once()
        writer.assert_not_called()

    def test_goal_close_rejects_child_goal_mutation_before_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
                git_head="a" * 40,
                git_tree="b" * 40,
            ).to_dict()
            epoch = _FakeWriterEpoch()
            epoch.open = True

            def mutate_goal(
                _repo: Path, _command: list[str], *, label: str, writer_epoch=None
            ) -> dict[str, object]:
                paths["goal"].write_bytes(paths["goal"].read_bytes() + b"\n")
                return command_stage(label)

            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": PHASE_KEY, "phase_key_change": False,
                }),
                mock.patch.object(workflow_runtime, "_execution_epoch_hold", return_value=False),
                mock.patch.object(workflow_runtime, "command_receipt", side_effect=mutate_goal),
                self.assertRaisesRegex(
                    workflow_runtime.WorkflowRuntimeError,
                    "GOAL_CLOSE_GOAL_BYTES_DRIFT",
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan={"startup": startup, "selected_goal": startup["selected_goal"]},
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=paths["next_spec"],
                    current_phase_key=None,
                    receipts=[],
                )
            self.assertFalse(workflow_runtime.goal_close_receipt_path(paths["goal"]).exists())

    def test_goal_close_rechecks_epoch_after_goal_child(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
            ).to_dict()
            epoch = _FakeWriterEpoch()
            epoch.open = True
            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": PHASE_KEY, "phase_key_change": False,
                }),
                mock.patch.object(
                    workflow_runtime,
                    "_execution_epoch_hold",
                    side_effect=[False, True],
                ),
                mock.patch.object(
                    workflow_runtime,
                    "command_receipt",
                    return_value=command_stage("goal-close"),
                ),
                self.assertRaisesRegex(
                    workflow_runtime.WorkflowRuntimeError,
                    "WORKFLOW_CLOSE_EPOCH_DRIFT",
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan={"startup": startup, "selected_goal": startup["selected_goal"]},
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=paths["next_spec"],
                    current_phase_key=None,
                    receipts=[],
                )
            self.assertFalse(workflow_runtime.goal_close_receipt_path(paths["goal"]).exists())

    def test_goal_close_receipt_rejects_epoch_edge_and_stage_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                exact_source_pin="SOURCE-058",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
            ).to_dict()
            epoch = _FakeWriterEpoch()
            epoch.open = True
            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": PHASE_KEY, "phase_key_change": False,
                }),
                mock.patch.object(workflow_runtime, "_execution_epoch_hold", return_value=False),
                mock.patch.object(
                    workflow_runtime,
                    "command_receipt",
                    return_value=command_stage("goal-close"),
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan={"startup": startup, "selected_goal": startup["selected_goal"]},
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=paths["next_spec"],
                    current_phase_key=None,
                    receipts=[],
                )
            marker = workflow_runtime.goal_close_receipt_path(paths["goal"])
            original = json.loads(marker.read_text())
            mutations = {
                "epoch": lambda row: row.__setitem__("control_sha256", "bad"),
                "edge": lambda row: row["exact_edge"].__setitem__("node", ""),
                "explicit-consumer-mismatch": lambda row: row["exact_edge"].__setitem__(
                    "consumer", "OTHER-CONSUMER"
                ),
                "stage": lambda row: row["stages"][0].__setitem__("exit", 2),
                "missing-next-spec": lambda row: row.update({
                    "next_goal_spec_path": None,
                    "next_goal_spec_sha256": None,
                    "phase_close_required": False,
                    "current_phase_key": None,
                    "next_phase_key": None,
                }),
            }
            for label, mutate in mutations.items():
                with self.subTest(label=label):
                    planted = json.loads(json.dumps(original))
                    mutate(planted)
                    marker.write_text(json.dumps(planted) + "\n")
                    with self.assertRaises(workflow_runtime.StartupRuntimeError):
                        workflow_runtime.validate_goal_close_receipt(
                            paths["goal"], paths["answer"], marker
                        )
            marker.write_text(json.dumps(original) + "\n")

    def test_changed_six_field_phase_key_runs_phase_close_once(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            next_spec = repo / "next.json"
            next_spec.write_text("{}\n", encoding="utf-8")
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
                git_head="a" * 40,
                git_tree="b" * 40,
            ).to_dict()
            compiled = {"startup": startup, "selected_goal": startup["selected_goal"]}
            epoch = _FakeWriterEpoch()
            epoch.open = True
            next_phase = dict(PHASE_KEY, front_id="NEXT")
            labels: list[str] = []

            def stage(_repo: Path, _command: list[str], *, label: str, writer_epoch=None) -> dict[str, object]:
                self.assertIs(writer_epoch, epoch)
                labels.append(label)
                if label == "phase-close":
                    output = Path(_command[_command.index("--json-out") + 1])
                    output.write_text(json.dumps(phase_close_output()) + "\n")
                return command_stage(label)

            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch.object(workflow_runtime, "_execution_epoch_hold", return_value=False),
                mock.patch.object(workflow_runtime, "_git", side_effect=close_git_identity),
                mock.patch.object(workflow_runtime, "command_receipt", side_effect=stage),
                mock.patch.object(
                    workflow_runtime,
                    "_phase_output_fingerprints",
                    return_value={
                        relative: workflow_runtime._sha256(repo / relative)
                        for relative in BLUEPRINT_OUTPUTS
                    },
                ),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": next_phase, "phase_key_change": True,
                }),
                mock.patch("orchestrator.spine.validate_runtime"),
                mock.patch(
                    "orchestrator.spine.validate_phase_key",
                    side_effect=lambda value: value,
                ),
                mock.patch("orchestrator.spine.phase_keys_equal", return_value=False),
                mock.patch.object(
                    workflow_runtime.node_registry_v10,
                    "verify_consumption",
                    return_value={"status": "PASS"},
                ),
            ):
                status = workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan=compiled,
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=next_spec,
                    current_phase_key=None,
                    receipts=[],
                )
            self.assertEqual(status, "CLOSED_GOAL_PHASE")
            self.assertEqual(labels, ["goal-close", "phase-close"])
            phase_marker = repo / "docs/routeB_bus/058_live.phase-close.json"
            self.assertTrue(phase_marker.is_file())
            validated = workflow_runtime.validate_phase_close_receipt(
                paths["goal"],
                workflow_runtime.goal_close_receipt_path(paths["goal"]),
                phase_marker,
            )
            self.assertEqual(validated["phase_evidence"], phase_close_output())
            phase_payload = json.loads(phase_marker.read_text())
            for label, mutate in (
                (
                    "missing",
                    lambda payload: payload["derived_output_fingerprints"].pop(
                        BLUEPRINT_OUTPUTS[0]
                    ),
                ),
                (
                    "extra",
                    lambda payload: payload["derived_output_fingerprints"].update(
                        {"unexpected.out": "a" * 64}
                    ),
                ),
            ):
                with self.subTest(output_set=label):
                    planted = json.loads(json.dumps(phase_payload))
                    mutate(planted)
                    phase_marker.write_text(json.dumps(planted) + "\n")
                    with self.assertRaises(workflow_runtime.StartupRuntimeError):
                        workflow_runtime.validate_phase_close_receipt(
                            paths["goal"],
                            workflow_runtime.goal_close_receipt_path(paths["goal"]),
                            phase_marker,
                        )
            phase_marker.write_text(json.dumps(phase_payload) + "\n")
            phase_payload["goal_path"] = "docs/routeB_bus/other.goal.md"
            phase_marker.write_text(json.dumps(phase_payload) + "\n")
            with self.assertRaises(workflow_runtime.StartupRuntimeError):
                workflow_runtime.validate_phase_close_receipt(
                    paths["goal"],
                    workflow_runtime.goal_close_receipt_path(paths["goal"]),
                    phase_marker,
                )
            phase_payload["goal_path"] = "docs/routeB_bus/058_live.goal.md"
            phase_marker.write_text(json.dumps(phase_payload) + "\n")
            target = repo / "phase-receipt-target.json"
            target.write_bytes(phase_marker.read_bytes())
            phase_marker.unlink()
            phase_marker.symlink_to(target)
            with self.assertRaises(workflow_runtime.StartupRuntimeError):
                workflow_runtime.validate_phase_close_receipt(
                    paths["goal"],
                    workflow_runtime.goal_close_receipt_path(paths["goal"]),
                    phase_marker,
                )

    def test_restart_after_phase_failure_runs_phase_repair_only(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            next_spec = repo / "next.json"
            next_spec.write_text("{}\n", encoding="utf-8")
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
                git_head="a" * 40,
                git_tree="b" * 40,
            ).to_dict()
            compiled = {"startup": startup, "selected_goal": startup["selected_goal"]}
            epoch = _FakeWriterEpoch()
            epoch.open = True
            next_phase = dict(PHASE_KEY, front_id="NEXT")
            labels: list[str] = []

            def first_stage(
                _repo: Path, _command: list[str], *, label: str, writer_epoch=None
            ) -> dict[str, object]:
                labels.append(label)
                return command_stage(
                    label, exit_code=2 if label == "phase-close" else 0
                )

            common = (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch.object(workflow_runtime, "_execution_epoch_hold", return_value=False),
                mock.patch.object(workflow_runtime, "_git", side_effect=close_git_identity),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": next_phase, "phase_key_change": True,
                }),
                mock.patch("orchestrator.spine.validate_runtime"),
                mock.patch(
                    "orchestrator.spine.validate_phase_key",
                    side_effect=lambda value: value,
                ),
                mock.patch("orchestrator.spine.phase_keys_equal", return_value=False),
            )
            with common[0], common[1], common[2], common[3], common[4], common[5], common[6], (
                mock.patch.object(workflow_runtime, "command_receipt", side_effect=first_stage)
            ), self.assertRaises(workflow_runtime.WorkflowRuntimeError):
                workflow_runtime._execute_goal_and_phase_close(
                    repo, plan=compiled, startup=startup, epoch=epoch,
                    attempt_payload=paths["attempt"], attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=next_spec, current_phase_key=None, receipts=[],
                )
            self.assertEqual(labels, ["goal-close", "phase-close"])
            self.assertTrue(workflow_runtime.goal_close_receipt_path(paths["goal"]).is_file())
            self.assertFalse(workflow_runtime.phase_close_receipt_path(paths["goal"]).exists())

            labels.clear()
            def git_identity(_repo: Path, *args: str) -> str:
                return "a" * 40 if args == ("rev-parse", "HEAD") else "b" * 40

            def retry_stage(
                _repo: Path, command: list[str], *, label: str, writer_epoch=None
            ) -> dict[str, object]:
                labels.append(label)
                output = Path(command[command.index("--json-out") + 1])
                output.write_text(json.dumps(phase_close_output()) + "\n")
                return command_stage(label)

            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch.object(workflow_runtime, "_git", side_effect=git_identity),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": next_phase, "phase_key_change": True,
                }),
                mock.patch("orchestrator.spine.validate_runtime"),
                mock.patch(
                    "orchestrator.spine.validate_phase_key",
                    side_effect=lambda value: value,
                ),
                mock.patch("orchestrator.spine.phase_keys_equal", return_value=False),
                mock.patch.object(
                    workflow_runtime,
                    "command_receipt",
                    side_effect=retry_stage,
                ),
                mock.patch.object(
                    workflow_runtime,
                    "_phase_output_fingerprints",
                    return_value={
                        relative: workflow_runtime._sha256(repo / relative)
                        for relative in BLUEPRINT_OUTPUTS
                    },
                ),
                mock.patch.object(
                    workflow_runtime.node_registry_v10,
                    "verify_consumption",
                    side_effect=workflow_runtime.node_registry_v10.NodeRegistryError(
                        "NODE_REGISTRY_CONSUMER_BYTES_DRIFT"
                    ),
                ),
                self.assertRaisesRegex(
                    workflow_runtime.WorkflowRuntimeError,
                    "GOAL_CLOSE_RECOVERY_CONSUMPTION_IDENTITY_DRIFT:"
                    "NODE_REGISTRY_CONSUMER_BYTES_DRIFT",
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo, plan=compiled, startup=startup, epoch=epoch,
                    attempt_payload=paths["attempt"], attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=None, current_phase_key=None, receipts=[],
                    owned_paths=["owned.lean"],
                )
            self.assertFalse(workflow_runtime.phase_close_receipt_path(paths["goal"]).exists())
            self.assertEqual(labels, ["phase-close"])
            labels.clear()

            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch.object(workflow_runtime, "_git", side_effect=git_identity),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": next_phase, "phase_key_change": True,
                }),
                mock.patch("orchestrator.spine.validate_runtime"),
                mock.patch(
                    "orchestrator.spine.validate_phase_key",
                    side_effect=lambda value: value,
                ),
                mock.patch("orchestrator.spine.phase_keys_equal", return_value=False),
                mock.patch.object(
                    workflow_runtime,
                    "command_receipt",
                    side_effect=retry_stage,
                ),
                mock.patch.object(
                    workflow_runtime,
                    "_phase_output_fingerprints",
                    return_value={
                        relative: workflow_runtime._sha256(repo / relative)
                        for relative in BLUEPRINT_OUTPUTS
                    },
                ),
                mock.patch.object(
                    workflow_runtime.node_registry_v10,
                    "verify_consumption",
                    return_value={"status": "PASS"},
                ),
            ):
                status = workflow_runtime._execute_goal_and_phase_close(
                    repo, plan=compiled, startup=startup, epoch=epoch,
                    attempt_payload=paths["attempt"], attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=None, current_phase_key=None, receipts=[],
                )
            self.assertEqual(status, "CLOSED_GOAL_PHASE")
            self.assertEqual(labels, ["phase-close"])

    def test_phase_close_rejects_non_green_output_and_post_child_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "phase.json"
            bad = phase_close_output()
            bad["blueprint_exit"] = 1
            output.write_text(json.dumps(bad) + "\n")
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "PHASE_CLOSE_OUTPUT_NOT_GREEN",
            ):
                workflow_runtime._validate_phase_close_output(output)

            bad = phase_close_output()
            bad["manual_debt"]["cards"] = ["CARD-OPEN"]
            output.write_text(json.dumps(bad) + "\n")
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "PHASE_CLOSE_OUTPUT_NOT_GREEN",
            ):
                workflow_runtime._validate_phase_close_output(output)

    def test_close_goal_requires_validated_next_goal_spec(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
            ).to_dict()
            epoch = _FakeWriterEpoch()
            epoch.open = True
            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                self.assertRaisesRegex(
                    workflow_runtime.WorkflowRuntimeError,
                    "NEXT_GOAL_SPEC_REQUIRED_FOR_CLOSE_GOAL",
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan={"startup": startup, "selected_goal": startup["selected_goal"]},
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=None,
                    current_phase_key=None,
                    receipts=[],
                )

            for label, payload in (
                ("attempt", '{"next_action":"CLOSE_GOAL","next_action":"CLOSE_GOAL"}\n'),
                ("next-spec", '{"phase_key":{},"phase_key":{}}\n'),
                (
                    "runtime",
                    '{"schema":"q3_channel_runtime.v1",'
                    '"schema":"q3_channel_runtime.v1"}\n',
                ),
            ):
                with self.subTest(duplicate_key_surface=label):
                    duplicate = repo / f"duplicate-{label}.json"
                    duplicate.write_text(payload, encoding="utf-8")
                    with self.assertRaisesRegex(
                        workflow_runtime.WorkflowRuntimeError,
                        "duplicate key",
                    ):
                        workflow_runtime._load_closed_json(
                            duplicate, code="CLOSE_JSON_INVALID"
                        )

        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            paths = self._goal_close_files(repo)
            next_spec = repo / "next.json"
            next_spec.write_text("{}\n")
            startup = production_snapshot(
                selected_goal="docs/routeB_bus/058_live.goal.md",
                control_sha256=workflow_runtime._sha256(repo / "docs/CODEX_CONTROL.md"),
                git_head="a" * 40,
                git_tree="b" * 40,
            ).to_dict()
            epoch = _FakeWriterEpoch()
            epoch.open = True
            next_phase = dict(PHASE_KEY, front_id="NEXT")

            def stage(
                _repo: Path, command: list[str], *, label: str, writer_epoch=None
            ) -> dict[str, object]:
                if label == "phase-close":
                    output_path = Path(command[command.index("--json-out") + 1])
                    output_path.write_text(json.dumps(phase_close_output()) + "\n")
                return command_stage(label)

            fingerprints = [
                {"derived.out": "a" * 64},
                {"derived.out": "b" * 64},
            ]
            with (
                mock.patch.object(workflow_runtime, "_validate_modern_answer"),
                mock.patch.object(workflow_runtime, "_execution_epoch_hold", return_value=False),
                mock.patch.object(workflow_runtime, "_git", side_effect=close_git_identity),
                mock.patch.object(workflow_runtime, "command_receipt", side_effect=stage),
                mock.patch.object(
                    workflow_runtime,
                    "_phase_output_fingerprints",
                    side_effect=fingerprints,
                ),
                mock.patch("orchestrator.goal_runtime.validate_next_goal_spec", return_value={
                    "phase_key": next_phase, "phase_key_change": True,
                }),
                mock.patch("orchestrator.spine.validate_runtime"),
                mock.patch(
                    "orchestrator.spine.validate_phase_key",
                    side_effect=lambda value: value,
                ),
                mock.patch("orchestrator.spine.phase_keys_equal", return_value=False),
                self.assertRaisesRegex(
                    workflow_runtime.WorkflowRuntimeError,
                    "PHASE_CLOSE_DERIVED_OUTPUT_DRIFT",
                ),
            ):
                workflow_runtime._execute_goal_and_phase_close(
                    repo,
                    plan={"startup": startup, "selected_goal": startup["selected_goal"]},
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=paths["attempt"],
                    attempt={"next_action": "CLOSE_GOAL"},
                    next_goal_spec=next_spec,
                    current_phase_key=None,
                    receipts=[],
                )
            self.assertFalse(
                workflow_runtime.phase_close_receipt_path(paths["goal"]).exists()
            )

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
        phase = (runtime or exploration_runtime())["active_proshka_phase"]
        lines.extend(f"{key.upper()}: {value}" for key, value in phase["phase_key"].items())
        lines.append(f"PHASE_ID: {phase['phase_id']}")
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
        self.assertEqual(payload["schema"], workflow_runtime.TEAM_PLAN_SCHEMA)
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
        self.assertEqual(payload["schema"], workflow_runtime.TEAM_PLAN_SCHEMA)
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
            mock.patch.object(workflow_runtime, "_team_enabled", return_value=False),
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

        def writer(_repo, _command, *, label, writer_epoch=None):
            self.assertIs(writer_epoch, epoch)
            self.assertTrue(epoch.open)
            events.append(label)
            return {"label": label, "exit": 0, "output_tail": "ok"}

        with (
            mock.patch.object(workflow_runtime, "_team_enabled", return_value=False),
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
            mock.patch.object(workflow_runtime, "_team_enabled", return_value=False),
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
                side_effect=lambda _repo, _command, label, writer_epoch=None: ok(label),
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
            request.write_text(
                "REQUEST_ID: REQ-PLANT\nBOUNDARY_ID: new-boundary\n"
                "CALL_CLASS: DELEGATED_STRATEGIC_REVIEW\nPHASE_ID: PHASE-1\n"
                + "".join(f"{key.upper()}: {value}\n" for key, value in PHASE_KEY.items())
                + "exact request\n", encoding="utf-8",
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
                        "phase_id": "PHASE-1",
                        "phase_key": PHASE_KEY,
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

    def test_review_plan_rejects_each_phase_header_mismatch_missing_and_duplicate(self) -> None:
        from orchestrator import spine

        for field in (*spine.PHASE_KEY_FIELDS, "phase_id"):
            for defect in ("mismatch", "missing", "duplicate"):
                with self.subTest(field=field, defect=defect), tempfile.TemporaryDirectory() as tmp:
                    repo = Path(tmp)
                    request, _, _ = self._review_fixture(
                        repo, call_class="DELEGATED_STRATEGIC_REVIEW"
                    )
                    lines = request.read_text().splitlines()
                    prefix = field.upper() + ":"
                    line = next(row for row in lines if row.startswith(prefix))
                    if defect == "missing":
                        lines.remove(line)
                    elif defect == "duplicate":
                        lines.append(line)
                    else:
                        lines[lines.index(line)] = prefix + " foreign"
                    request.write_text("\n".join(lines) + "\n")
                    subprocess.run(["git", "add", "request.txt"], cwd=repo, check=True)
                    subprocess.run(["git", "commit", "-qm", "phase defect"], cwd=repo, check=True)
                    commit = subprocess.check_output(
                        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
                    ).strip()
                    result = workflow_runtime.compile_review_dispatch(
                        repo,
                        attachment=request,
                        request_commit=commit,
                        request_id="REQ-PLANT",
                        boundary_id="boundary",
                        expected_sha256=workflow_runtime.hashlib.sha256(
                            request.read_bytes()
                        ).hexdigest(),
                    )
                    suffix = {
                        "missing": "MISSING",
                        "duplicate": "AMBIGUOUS",
                        "mismatch": "MISMATCH",
                    }[defect]
                    self.assertEqual(result["status"], "HOLD")
                    self.assertIn(f"PROSHKA_{field.upper()}_{suffix}", result["holds"])

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
                    side_effect=lambda _repo, _command, label, writer_epoch=None: ok(label),
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
                        side_effect=lambda _repo, _command, label, writer_epoch=None: {
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
            receipt.write_text(
                '{"schema":"q3_dependency_contract_receipt.v1",'
                '"schema":"q3_dependency_contract_receipt.v1"}\n',
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "duplicate key",
            ):
                workflow_runtime._dependency_contract_receipt(
                    repo,
                    receipt,
                    candidate="Q3.RouteB.candidate",
                    target="Q3.RouteB.target",
                )
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


class ResumeCheckpointTests(unittest.TestCase):
    """Crash/replay/corruption acceptance for the existing workflow front door."""

    def setUp(self):
        startup = mock.patch.object(workflow_runtime, "live_plan_v10", return_value={
            "status": "HOLD", "startup": {"fatal_errors": []}, "holds": ["EXACT_EDGE_REQUIRED"],
        })
        self.startup = startup.start()
        self.addCleanup(startup.stop)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        (self.repo / ".git/q3-three-body.writer.lock").touch()
        for rel in (workflow_runtime.RESUME_PATH, workflow_runtime.TOOLS):
            (self.repo / rel).parent.mkdir(parents=True, exist_ok=True)
        self.original = b"# Original goal\r\nHistorical ``` commands\nNo final newline"
        self.goal = self.repo / "docs/Codex/GOAL.md"
        self.goal.write_bytes(self.original)
        _, entry = workflow_runtime._resume_history_record("goal", 0, self.original)
        self.history = self.repo / workflow_runtime.RESUME_HISTORY_PATH
        self.history.write_bytes(workflow_runtime.RESUME_HISTORY_HEADER + entry)
        self.current = self.repo / workflow_runtime.RESUME_PATH
        self.candidate = self.repo / "candidate.md"
        (self.repo / "docs/CODEX_CONTROL.md").write_text(
            "```yaml\nCONTROL_ID: Q3_EXECUTOR_CONTROL\nCONTROL_VERSION: 10\nSTATUS: ACTIVE\n"
            "HONESTY_STATE: CHALLENGER_NOT_RH\nOWNER_ONLY_BOUNDARY: PX_RH_CLAIM\n```\n")
        (self.repo / workflow_runtime.TOOLS).write_text(
            "tool_families:\n  workflow:\n    tools:\n"
            "      - id: workflow-resume-checkpoint\n        status: ENABLED\n"
            "        writes: true\n        write_paths:\n"
            "          - docs/Codex/RESUME.md\n          - docs/Codex/GOAL_HISTORY.md\n")

    def document(self, revision=1, previous="ABSENT", **changes):
        data = {
            "schema": "q3_resume.v1", "revision": revision,
            "observed_at": "2026-09-11T10:00:00+02:00", "previous_sha256": previous,
            "owner_thread_id": "01a084f4-7498-7021-bac2-91d184d58dc7",
            "owner_host_id": "local",
            "reconciliation_pending": False, "recovery_from": None,
            "pins": dict(head="a" * 40, physical_goal="docs/goal.md", source_commit="b" * 40,
                         request_id="REQ-EXISTING", phase_id="PHASE-EXISTING"),
            "stages": {name: "PENDING" for name in
                       ("receipt", "independent_review", "parent_check", "acceptance", "publication")},
            "operation": dict(kind="DISPATCH", state="INTENT", id="existing-request", evidence=[]),
        }
        data.update(changes)
        body = "\n".join("## " + name + "\nObserved evidence; reconcile before acting.\n"
                         for name in workflow_runtime.RESUME_SECTIONS)
        return ("---\n" + workflow_runtime.yaml.safe_dump(data, sort_keys=False)
                + "---\n" + body).encode()

    def save(self, raw=None, expected="ABSENT", **options):
        self.candidate.write_bytes(raw or self.document())
        return workflow_runtime.resume_checkpoint(
            self.repo, candidate=self.candidate, expected_sha256=expected, **options)

    def test_original_bytes_dry_run_save_and_lost_receipt_noop(self):
        history = self.history.read_bytes()
        self.assertEqual(self.save(dry_run=True)["status"], "DRY_RUN")
        self.assertFalse(self.current.exists())
        self.assertEqual(self.history.read_bytes(), history)
        self.assertEqual(self.save()["status"], "SAVED")
        saved = self.history.read_bytes()
        with mock.patch.object(workflow_runtime, "_resume_sync", wraps=workflow_runtime._resume_sync) as sync:
            self.assertEqual(self.save()["status"], "NOOP")
            self.assertEqual(sync.call_count, 2)
        self.assertEqual(self.history.read_bytes(), saved)
        self.assertEqual(self.goal.read_bytes(), self.original)
        self.assertEqual(next(iter(workflow_runtime._resume_history(saved).values()))[2], self.original)

    def test_archive_predecessor_and_version_collision(self):
        self.save()
        first = self.current.read_bytes()
        expected = workflow_runtime._resume_digest(first)
        second = self.document(2, expected)
        self.save(second, expected)
        records = workflow_runtime._resume_history(self.history.read_bytes())
        self.assertIn(("resume", 1, first), records.values())
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "REVISION_CONFLICT"):
            self.save(second.replace(b"Observed evidence", b"Changed evidence"), expected)
        self.assertEqual(self.current.read_bytes(), second)

    def test_stale_preimage_rejected_without_archive_change(self):
        self.save()
        before = self.history.read_bytes()
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PREIMAGE_CHANGED"):
            self.save(self.document(2, "a" * 64), "a" * 64)
        self.assertEqual(self.history.read_bytes(), before)

    def test_format_size_duplicate_key_and_revision_rejected(self):
        for raw in (self.document().replace(b"revision: 1", b"revision: 1\nrevision: 2"),
                    self.document() + b"x" * 8192, self.document(0),
                    self.document().replace(b"2026-09-11T10:00:00+02:00", b"yesterday")):
            with self.subTest(raw=raw[:30]), self.assertRaises(workflow_runtime.WorkflowRuntimeError):
                self.save(raw)
            self.assertFalse(self.current.exists())

    def test_corrupt_recovery_exact_archive_preserves_bad_bytes_and_requires_reconcile(self):
        self.save()
        first = self.current.read_bytes()
        self.save(self.document(2, workflow_runtime._resume_digest(first)), workflow_runtime._resume_digest(first))
        key, _ = workflow_runtime._resume_history_record("resume", 1, first)
        for corrupted in (b"\xfftruncated", first.replace(b"Observed evidence", b"bit-flipped text")):
            with self.subTest(corrupted=corrupted[:20]):
                history = self.history.read_bytes()
                self.current.write_bytes(corrupted)
                expected = workflow_runtime._resume_digest(corrupted)
                next_revision = max(v for k, v, _ in workflow_runtime._resume_history(history).values()
                                    if k in {"resume", "intent"}) + 1
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "CORRUPT_REQUIRES_RECOVERY"):
                    self.save(self.document(next_revision, expected), expected)
                recovered = self.document(next_revision, expected, reconciliation_pending=True, recovery_from=key)
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "CONTENT_MISMATCH"):
                    self.save(recovered.replace(b"Observed evidence", b"Invented evidence"), expected, recover_from=key)
                self.assertEqual(self.history.read_bytes(), history)
                self.assertEqual(self.save(recovered, expected, recover_from=key)["status"], "SAVED")
                self.assertEqual(self.save(recovered, expected, recover_from=key)["status"], "NOOP")
                self.assertIn(("corrupt", 0, corrupted), workflow_runtime._resume_history(self.history.read_bytes()).values())

    def test_writer_lock_collision_and_symlink_hold(self):
        with (self.repo / ".git/q3-three-body.writer.lock").open("rb") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "LOCK_COLLISION"):
                self.save()
        self.current.symlink_to(self.goal)
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "UNSAFE_PATH"):
            self.save()
        self.assertEqual(self.goal.read_bytes(), self.original)

    def test_interruption_at_each_durable_stage_replays_exactly(self):
        for stage, after_write in (("history", False), ("history", True), ("resume", False), ("resume", True)):
            with self.subTest(stage=stage, after_write=after_write):
                self.setUp()
                self.save()
                first = self.current.read_bytes()
                expected = workflow_runtime._resume_digest(first)
                second = self.document(2, expected)
                atomic = workflow_runtime._atomic_bytes
                target = self.history if stage == "history" else self.current
                def crash(path, payload):
                    if path == target and not after_write:
                        raise OSError("simulated power loss")
                    atomic(path, payload)
                    if path == target:
                        raise OSError("simulated power loss")
                with mock.patch.object(workflow_runtime, "_atomic_bytes", side_effect=crash):
                    with self.assertRaisesRegex(OSError, "power loss"):
                        self.save(second, expected)
                result = self.save(second, expected)
                self.assertIn(result["status"], {"SAVED", "NOOP"})
                self.assertEqual(self.current.read_bytes(), second)
                records = workflow_runtime._resume_history(self.history.read_bytes())
                self.assertEqual(sum(k == "resume" for k, _, _ in records.values()), 1)

    def test_goal_migration_cas_keeps_foreign_change(self):
        with workflow_runtime._execution_writer_epoch(self.repo) as epoch:
            changed = self.original + b"\nAnother executor's update\n"
            self.goal.write_bytes(changed)
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PREIMAGE_CHANGED"):
                workflow_runtime._resume_cas_bytes(
                    self.repo, Path("docs/Codex/GOAL.md"), self.original, b"short goal\n", epoch)
        self.assertEqual(self.goal.read_bytes(), changed)

    def test_drift_between_archive_and_replace_preserves_foreign_resume(self):
        self.save()
        first = self.current.read_bytes()
        expected = workflow_runtime._resume_digest(first)
        atomic = workflow_runtime._atomic_bytes
        def drift(path, payload):
            atomic(path, payload)
            if path == self.history:
                self.current.write_bytes(b"foreign modification\n")
        with mock.patch.object(workflow_runtime, "_atomic_bytes", side_effect=drift):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PREIMAGE_CHANGED"):
                self.save(self.document(2, expected), expected)
        self.assertEqual(self.current.read_bytes(), b"foreign modification\n")

    def test_bad_history_disabled_tool_and_inactive_control_fail_closed(self):
        for path, payload in ((self.history, self.history.read_bytes().replace(b"Historical ```", b"Modified ```")),
                              (self.repo / workflow_runtime.TOOLS, b"tool_families: {}\n"),
                              (self.repo / "docs/CODEX_CONTROL.md", b"inactive control\n")):
            before = path.read_bytes()
            path.write_bytes(payload)
            with self.assertRaises((workflow_runtime.WorkflowRuntimeError, workflow_runtime.StartupRuntimeError)):
                self.save()
            self.assertFalse(self.current.exists())
            path.write_bytes(before)

    def test_checkpoint_never_dispatches_selects_or_accepts_unknown_operation(self):
        with mock.patch.object(workflow_runtime, "execute_close_node", side_effect=AssertionError("execution")), \
             mock.patch.object(workflow_runtime, "compile_review_dispatch", side_effect=AssertionError("dispatch")):
            self.save(self.document(operation=dict(kind="DISPATCH", state="UNKNOWN", id="same-request", evidence=[])))
        data, _ = workflow_runtime._resume_document(self.current.read_bytes())
        self.assertEqual(data["operation"]["state"], "UNKNOWN")
        self.assertEqual(data["stages"]["acceptance"], "PENDING")

    def test_startup_fatal_never_writes_but_scoped_hold_does(self):
        before = self.history.read_bytes()
        self.startup.return_value = {"status": "FATAL", "startup": {"fatal_errors": ["BAD_RUNTIME"]}}
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "STARTUP_FATAL"):
            self.save()
        self.assertEqual(self.history.read_bytes(), before)
        self.assertFalse(self.current.exists())
        self.startup.return_value = {"status": "HOLD", "startup": {"fatal_errors": []}}
        self.assertEqual(self.save()["status"], "SAVED")

    def test_first_checkpoint_recovers_from_reserved_bytes_not_completion(self):
        self.save()
        first = self.current.read_bytes()
        key, _ = workflow_runtime._resume_history_record("intent", 1, first)
        corrupt = b"first checkpoint corrupted\xff"
        self.current.write_bytes(corrupt)
        digest = workflow_runtime._resume_digest(corrupt)
        recovered = self.document(2, digest, recovery_from=key, reconciliation_pending=True)
        self.assertEqual(self.save(recovered, digest, recover_from=key)["status"], "SAVED")
        self.assertEqual(self.save(recovered, digest, recover_from=key)["status"], "NOOP")
        data, _ = workflow_runtime._resume_document(self.current.read_bytes())
        self.assertTrue(data["reconciliation_pending"])
        self.assertEqual(data["operation"]["state"], "INTENT")

    def test_future_orphan_intent_holds_without_replacement(self):
        for initial, future in ((False, 3), (True, 10), (True, 3)):
            with self.subTest(initial=initial, future=future):
                self.setUp()
                if initial:
                    self.save()
                current = self.current.read_bytes() if initial else None
                previous = workflow_runtime._resume_digest(current)
                if initial and future == 3:
                    _, pending = workflow_runtime._resume_history_record("intent", 2, self.document(2, previous))
                    self.history.write_bytes(self.history.read_bytes() + pending)
                _, foreign = workflow_runtime._resume_history_record("intent", future, self.document(future, previous))
                history = self.history.read_bytes() + foreign
                self.history.write_bytes(history)
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "HISTORY_INVALID|ORPHAN_INTENT"):
                    self.save(self.document(2 if initial else 1, previous), previous)
                self.assertEqual(self.history.read_bytes(), history)
                self.assertEqual(self.current.read_bytes() if initial else None, current)


class TeamRuntimeTests(unittest.TestCase):
    """Recovery, cross-installation fencing and first-step acceptance fixtures."""

    def setUp(self):
        self.fixture = ResumeCheckpointTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.repo = self.fixture.repo
        (self.repo / workflow_runtime.TOOLS).write_bytes(
            (Path(__file__).resolve().parents[2] / workflow_runtime.TOOLS).read_bytes())
        self.registered = mock.patch.object(workflow_runtime, "_team_registered")
        self.registered.start()
        self.addCleanup(self.registered.stop)
        import os
        self.actor = mock.patch.dict(os.environ, {"CODEX_THREAD_ID": "01a084f4-7498-7021-bac2-91d184d58dc7", "Q3_OWNER_EPOCH": "1"})
        self.actor.start()
        self.addCleanup(self.actor.stop)
        self.identity = workflow_runtime.team_local_init(self.repo)["installation_ref"]
        self.source = self.repo / "docs/source.md"
        self.source.write_bytes(b"exact source\n")
        (self.repo / workflow_runtime.TEAM_ISSUES).write_bytes(b"# Fixture issues\n")
        (self.repo / workflow_runtime.TEAM_ASSIGNMENTS).write_bytes(b"# Fixture assignments\n")

    def data(self):
        data, _ = workflow_runtime._resume_document(self.fixture.document())
        request = {"kind": "REQUEST", "id": "REQ-EXISTING", "sha256": "a" * 64}
        verdict = {"kind": "VERDICT", "id": "VERDICT-EXISTING", "sha256": "b" * 64}
        data.update(schema="q3_resume.v2", source_manifest={"docs/source.md": workflow_runtime._resume_digest(self.source.read_bytes())},
                    ownership={"installation_ref": self.identity, "epoch": 1, "state": "ACTIVE", "transfer": None})
        data["pins"].update(phase_key=PHASE_KEY, request={"path": "docs/request.txt", "commit": "a" * 40, "blob": "b" * 40,
                                                       "sha256": "a" * 64, "boundary_id": "BOUNDARY", "conversation_id": "chat"})
        data["stages"] = {name: {"subject": dict(request if index < 3 else verdict), "state": "NOT_STARTED", "evidence": {},
                                 "source_sha256": workflow_runtime._resume_digest(workflow_runtime._team_json(data["source_manifest"])), "checked_by": None}
                          for index, name in enumerate(workflow_runtime.TEAM_STAGES)}
        data["operation"].update(subject=request, command="dispatch-proshka", inputs=data["source_manifest"])
        return data

    def document(self, data):
        _, body = workflow_runtime._resume_document(self.fixture.document())
        return ("---\n" + workflow_runtime.yaml.safe_dump(data, sort_keys=False) + "---\n" + body).encode()

    def install(self, data):
        raw = self.document(data)
        self.fixture.current.write_bytes(raw)
        _, intent = workflow_runtime._resume_history_record("intent", data["revision"], raw)
        self.fixture.history.write_bytes(self.fixture.history.read_bytes() + intent)
        return raw

    def local(self, **fields):
        with workflow_runtime._execution_writer_epoch(self.repo) as epoch:
            before = workflow_runtime._team_local(self.repo)
            workflow_runtime._team_local_save(self.repo, before, {**before, **fields}, epoch)

    def native_report_fixture(self, *, role="independent-checker", subject=None, state="COMPLETED"):
        """Real registry/files with explicitly simulated native provider observations."""
        env = {**workflow_runtime.os.environ, "GIT_AUTHOR_NAME": "Fixture", "GIT_COMMITTER_NAME": "Fixture",
               "GIT_AUTHOR_EMAIL": "fixture@example.invalid", "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
        subprocess.run(["git", "add", "docs/source.md"], cwd=self.repo, env=env, check=True)
        subprocess.run(["git", "commit", "-qm", "Fixture source"], cwd=self.repo, env=env, check=True)
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.repo).decode().strip()
        data = self.data()
        source = {"locator": "docs/source.md", "sha256": data["source_manifest"]["docs/source.md"]}
        report = TeamRecordsTests.report()
        report.update(reporter_task="native-worker", reporter_host="local", base_commit=head,
                      input_paths=[{"path": source["locator"], "sha256": source["sha256"]}],
                      evidence=[source], expected_rule_source=source)
        assignment = TeamRecordsTests.assignment(assignment_id=report["assignment_id"])
        assignment.update(owner_task=data["owner_thread_id"], owner_host="local", owner_epoch=1,
                          owner_installation_ref=self.identity, assignee=report["reporter_task"],
                          role=role, subject=subject or report["subject_id"], base_commit=head,
                          input_hashes=report["input_paths"])
        data["operation"].update(id="launch-fixture", command="agent-launch",
            subject={"kind": "ASSIGNMENT", "id": assignment["assignment_id"],
                     "sha256": team_records._assignment_binding_sha(assignment)})
        self.install(data)
        self.fixture.candidate.write_bytes(team_records.canonical_json(assignment))
        assignment_raw = (self.repo / workflow_runtime.TEAM_ASSIGNMENTS).read_bytes()
        workflow_runtime.team_record(self.repo, kind="assignment", candidate=self.fixture.candidate,
            expected_sha256=workflow_runtime._resume_digest(assignment_raw))
        self.local(operations={"launch-fixture": {"state": "RESERVED", "actor": data["owner_thread_id"], "epoch": 1}})
        context = TeamRecordsTests.provenance_context(assignment, report=report, result_state=state)
        observations = context.observations[assignment["assignment_id"]]
        for observation in observations:
            phase = observation["phase"]
            observation["operation_id"] = "launch-fixture" if phase == "LAUNCH" else "result-fixture"
            for prefix, content in (("output", b"fixture launch\n" if phase == "LAUNCH" else team_records.canonical_json(report)),
                                    ("provider_receipt", b'{"simulated_provider":true}\n')):
                locator = "docs/" + prefix + "-" + phase + ".json"
                (self.repo / locator).write_bytes(content)
                observation[prefix + "_locator"] = locator
                observation[prefix + "_sha256"] = workflow_runtime._resume_digest(content)
            observation["evidence_sha256"] = workflow_runtime._resume_digest(team_records.canonical_json([
                {"locator": observation[prefix + "_locator"], "sha256": observation[prefix + "_sha256"]}
                for prefix in ("output", "provider_receipt")]))
            self.fixture.candidate.write_bytes(team_records.canonical_json(observation))
            workflow_runtime.team_observe_native(self.repo, candidate=self.fixture.candidate,
                expected_sha256=workflow_runtime._resume_digest(self.fixture.candidate.read_bytes()))
            self.assertEqual(workflow_runtime.team_observe_native(self.repo, candidate=self.fixture.candidate,
                expected_sha256=workflow_runtime._resume_digest(self.fixture.candidate.read_bytes()))["status"], "NOOP")
        return data, report, assignment, observations

    def test_report_intake_requires_native_output_and_recovers_lost_receipt(self):
        with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
            _, report, _, _ = self.native_report_fixture(state="RUNNING")
            raw = (self.repo / workflow_runtime.TEAM_ISSUES).read_bytes()
            expected = workflow_runtime._resume_digest(raw)
            forged = {**report, "actual_behavior": "unobserved different result"}
            self.fixture.candidate.write_bytes(team_records.canonical_json(forged))
            with self.assertRaisesRegex(team_records.TeamRecordError, "NATIVE_OBSERVATION_MISSING"):
                workflow_runtime.team_record(self.repo, kind="report", candidate=self.fixture.candidate, expected_sha256=expected)
            self.assertEqual((self.repo / workflow_runtime.TEAM_ISSUES).read_bytes(), raw)
            self.fixture.candidate.write_bytes(team_records.canonical_json(report))
            real = workflow_runtime._resume_cas_bytes
            def crash_after_event(repo, relative, before, after, epoch):
                real(repo, relative, before, after, epoch)
                if relative == workflow_runtime.TEAM_ISSUES:
                    raise RuntimeError("fixture receipt loss")
            with mock.patch.object(workflow_runtime, "_resume_cas_bytes", side_effect=crash_after_event):
                with self.assertRaisesRegex(RuntimeError, "fixture receipt loss"):
                    workflow_runtime.team_record(self.repo, kind="report", candidate=self.fixture.candidate, expected_sha256=expected)
            receipt = workflow_runtime.team_record(self.repo, kind="report", candidate=self.fixture.candidate, expected_sha256=expected)
            self.assertEqual(receipt["status"], "NOOP")
            self.assertTrue((self.repo / receipt["receipt_path"]).is_file())
            self.assertFalse(receipt["mathematical_acceptance"])

    def test_independent_stage_needs_exact_completed_assignment(self):
        with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
            data, _, _, observations = self.native_report_fixture(subject="VERDICT-EXISTING", state="RUNNING")
            after = json.loads(json.dumps(data))
            result = observations[1]
            evidence = {result["output_locator"]: result["output_sha256"]}
            for name in ("receipt", "independent_review"):
                after["stages"][name].update(state="DONE", evidence=evidence, checked_by="native-worker")
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INDEPENDENT_COMPLETED_ASSIGNMENT"):
                workflow_runtime._team_owner_transition(self.repo, data, after)
            completed = {**result, "state": "COMPLETED", "operation_id": "result-completed"}
            self.fixture.candidate.write_bytes(team_records.canonical_json(completed))
            workflow_runtime.team_observe_native(self.repo, candidate=self.fixture.candidate,
                expected_sha256=workflow_runtime._resume_digest(self.fixture.candidate.read_bytes()))
            # A repeated output's completed observation supersedes its interim state.
            workflow_runtime._team_owner_transition(self.repo, data, after)
            (self.repo / result["output_locator"]).write_text("changed result")
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "TEAM_SOURCE_CHANGED"):
                workflow_runtime._team_owner_transition(self.repo, data, after)

    def integration_fixture(self, *, intake=False, verdict="SOURCE_INTEGRATION_APPROVED",
                             include_untracked_destination=False, include_executable=False):
        """Real Git/files/reservation, explicitly simulated native provider and engine."""
        import base64
        env = {**workflow_runtime.os.environ, "GIT_AUTHOR_NAME": "Fixture", "GIT_COMMITTER_NAME": "Fixture",
               "GIT_AUTHOR_EMAIL": "fixture@example.invalid", "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
        (self.repo / "docs/target.md").write_bytes(b"old target\n")
        baseline_paths = ["docs/source.md", "docs/target.md"]
        candidate_paths = list(baseline_paths)
        if include_executable:
            executable = self.repo / "docs/executable.sh"
            executable.write_bytes(b"#!/bin/sh\necho old\n")
            executable.chmod(0o755)
            baseline_paths.append("docs/executable.sh")
            candidate_paths.append("docs/executable.sh")
        if include_untracked_destination:
            untracked = self.repo / "docs/new-target.md"
            untracked.write_bytes(b"untracked destination collision\n")
            candidate_paths.append("docs/new-target.md")

        def git(*args, input=None, index=None):
            result = subprocess.run(["git", *args], cwd=self.repo, env={**env, **({"GIT_INDEX_FILE": index} if index else {})},
                                    input=input, capture_output=True, check=True)
            return result.stdout.decode().strip()
        git("add", *baseline_paths)
        git("commit", "-qm", "Integration fixture baseline")
        base = git("rev-parse", "HEAD")
        data = self.data()
        assignments = []
        for role, assignee in (("implementation", "producer"), ("independent-checker", "checker")):
            assignment = TeamRecordsTests.assignment(assignment_id="integration-" + assignee)
            assignment.update(owner_task=data["owner_thread_id"], owner_host="local", owner_epoch=1,
                owner_installation_ref=self.identity, assignee=assignee, role=role, base_commit=base,
                subject="bounded integration", input_hashes=[{"path": "docs/source.md", "sha256": data["source_manifest"]["docs/source.md"]}],
                permitted_paths=sorted(candidate_paths))
            registry = self.repo / workflow_runtime.TEAM_ASSIGNMENTS
            updated, _ = team_records.prepare_assignment(registry.read_bytes(), assignment,
                workflow_runtime._resume_digest(registry.read_bytes()))
            registry.write_bytes(updated)
            assignments.append(assignment)
        producer, checker = assignments
        if intake:
            content = b'Raw first provider response, not yet accepted.\n'
            digest = workflow_runtime._resume_digest(content)
            files = [{"path": "docs/session_protocols/team-evidence-" + digest + ".bin", "before_sha256": "ABSENT",
                      "sha256": digest, "content_base64": base64.b64encode(content).decode()}]
            commit = None
        else:
            index = str(self.repo / "candidate.index")
            git("read-tree", base, index=index)
            files = []
            for path in producer["permitted_paths"]:
                before = None if (include_untracked_destination and path == "docs/new-target.md") else (self.repo / path).read_bytes()
                after = b"checked replacement for " + path.encode() + b"\n"
                blob = git("hash-object", "-w", "--stdin", input=after)
                mode = "100755" if (include_executable and path == "docs/executable.sh") else "100644"
                update_index = ["update-index"]
                if before is None:
                    update_index.append("--add")
                git(*update_index, "--cacheinfo", mode + "," + blob + "," + path, index=index)
                files.append({"path": path, "source_path": path, "before_sha256": workflow_runtime._resume_digest(before),
                              "sha256": workflow_runtime._resume_digest(after)})
            commit = git("commit-tree", git("write-tree", index=index), "-p", base, input=b"Isolated fixture candidate\n")
        manifest = {"schema": "q3_team_integration.v1", "mode": "EVIDENCE_INTAKE" if intake else "REVIEWED_SOURCE",
                    "operation_id": "integration-fixture", "owner_task": data["owner_thread_id"],
                    "installation_ref": self.identity, "epoch": 1, "expected_head": base,
                    "implementer_assignment": producer["assignment_id"],
                    "assignment_sha256": workflow_runtime._resume_digest(team_records.canonical_json(team_records._assignment_immutable_view(producer))),
                    "checker_assignment": None if intake else checker["assignment_id"], "candidate_commit": commit, "files": files}
        data["operation"].update(id=manifest["operation_id"], command="workflow-team-integrate-candidate",
            subject={"kind": "REPAIR", "id": manifest["operation_id"], "sha256": workflow_runtime._resume_digest(team_records.canonical_json(manifest))})
        raw = self.install(data)
        operations = {}
        if not intake:
            artifact = {"schema": "q3_team_integration_review.v1", "manifest_sha256": data["operation"]["subject"]["sha256"],
                        "base_commit": base, "candidate_commit": commit,
                        "files": [{"path": row["path"], "sha256": row["sha256"]} for row in files],
                        "implementer_assignment": producer["assignment_id"], "checker_assignment": checker["assignment_id"], "verdict": verdict}
            observations = TeamRecordsTests.provenance_context(checker).observations[checker["assignment_id"]]
            for observation in observations:
                phase = observation["phase"]
                for prefix, content in (("output", b"simulated launch\n" if phase == "LAUNCH" else team_records.canonical_json(artifact)),
                                        ("provider_receipt", b'{"simulated_provider":true}\n')):
                    path = "docs/integration-" + prefix + "-" + phase + ".json"
                    (self.repo / path).write_bytes(content)
                    observation[prefix + "_locator"] = path
                    observation[prefix + "_sha256"] = workflow_runtime._resume_digest(content)
                observation["evidence_sha256"] = workflow_runtime._resume_digest(team_records.canonical_json([
                    {"locator": observation[prefix + "_locator"], "sha256": observation[prefix + "_sha256"]}
                    for prefix in ("output", "provider_receipt")]))
                operations[observation["operation_id"]] = {"schema": "q3_team_assignment_receipt.v1", "state": "CONFIRMED", "observation": observation}
        operations[manifest["operation_id"]] = {"state": "OBSERVED", "actor": data["owner_thread_id"], "epoch": 1,
            "checkpoint_sha256": workflow_runtime._resume_digest(raw), "remote_ownership": data["ownership"],
            "remote_thread": data["owner_thread_id"], "local_head": base}
        self.local(operations=operations)
        workflow_runtime.team_reserve_effect(self.repo, operation_id=manifest["operation_id"])
        self.fixture.candidate.write_bytes(team_records.canonical_json(manifest))
        for name, value in (("_team_enabled", True), ("_team_writer_inventory", {}),
                            ("_team_integration_engine", {"fixture_engine": True, "commit": base})):
            patcher = mock.patch.object(workflow_runtime, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)
        return manifest

    def integrate(self):
        return workflow_runtime.team_integrate_candidate(self.repo, candidate=self.fixture.candidate)

    def test_integration_copies_exact_bytes_preserves_foreign_and_replays(self):
        manifest = self.integration_fixture()
        foreign = self.repo / "docs/foreign.md"
        foreign.write_bytes(b"another owner's work\n")
        result = self.integrate()
        self.assertEqual(result["status"], "INTEGRATED")
        self.assertFalse(result["mathematical_acceptance"])
        for row in manifest["files"]:
            self.assertEqual(workflow_runtime._resume_digest((self.repo / row["path"]).read_bytes()), row["sha256"])
        local = (self.repo / ".git" / workflow_runtime.TEAM_LOCAL).read_bytes()
        self.assertEqual(self.integrate()["status"], "NOOP")
        self.assertEqual((self.repo / ".git" / workflow_runtime.TEAM_LOCAL).read_bytes(), local)
        self.assertEqual(foreign.read_bytes(), b"another owner's work\n")
        self.assertEqual(workflow_runtime._team_git(self.repo, "rev-parse", "HEAD").decode().strip(), manifest["expected_head"])
        self.source.write_bytes(b"exact source\n")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "COMPLETED_DESTINATION_CHANGED"):
            self.integrate()
        self.assertEqual(self.source.read_bytes(), b"exact source\n")

    def test_integration_first_raw_evidence_needs_no_git_candidate_or_native_result(self):
        manifest = self.integration_fixture(intake=True)
        self.assertIsNone(manifest["candidate_commit"])
        self.assertFalse(any(item.get("schema") == "q3_team_assignment_receipt.v1"
                             for item in workflow_runtime._team_local(self.repo)["operations"].values()))
        result = self.integrate()
        self.assertEqual(result["evidence_status"], "UNADJUDICATED")
        self.assertFalse(result["mathematical_acceptance"])
        self.assertEqual(result["status"], "INTEGRATED")
        self.assertEqual(self.integrate()["status"], "NOOP")

    def test_integration_completed_negative_review_does_not_approve(self):
        manifest = self.integration_fixture(verdict="SOURCE_INTEGRATION_REJECTED")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "NOT_EXACTLY_APPROVED"):
            self.integrate()
        self.assertEqual(workflow_runtime._resume_digest(self.source.read_bytes()), manifest["files"][0]["before_sha256"])
        self.assertNotIn("integration", workflow_runtime._team_local_operation(self.repo, manifest["operation_id"]))

    def test_integration_changed_preimage_review_owner_and_epoch_refused_before_write(self):
        manifest = self.integration_fixture()
        target = self.repo / manifest["files"][1]["path"]
        original = target.read_bytes()
        for label, patcher in (("owner", mock.patch.dict(workflow_runtime.os.environ, {"CODEX_THREAD_ID": "foreign"})),
                               ("epoch", mock.patch.dict(workflow_runtime.os.environ, {"Q3_OWNER_EPOCH": "2"}))):
            with self.subTest(label=label), patcher, self.assertRaises(workflow_runtime.WorkflowRuntimeError):
                self.integrate()
            self.assertEqual(target.read_bytes(), original)
        review = self.repo / "docs/integration-output-RESULT.json"
        saved = review.read_bytes()
        review.write_bytes(saved + b" ")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "EVIDENCE_HASH_MISMATCH"):
            self.integrate()
        review.write_bytes(saved)
        target.write_bytes(b"foreign edit\n")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PREIMAGE_CHANGED"):
            self.integrate()
        self.assertEqual(target.read_bytes(), b"foreign edit\n")
        self.assertEqual(workflow_runtime._resume_digest(self.source.read_bytes()), manifest["files"][0]["before_sha256"])

    def test_integration_crash_keeps_all_writers_held_before_mutable_control(self):
        manifest = self.integration_fixture()
        real = workflow_runtime._resume_cas_bytes
        def crash(repo, relative, before, after, epoch, **kwargs):
            real(repo, relative, before, after, epoch, **kwargs)
            raise RuntimeError("simulated inter-file crash")
        with mock.patch.object(workflow_runtime, "_resume_cas_bytes", side_effect=crash):
            with self.assertRaisesRegex(RuntimeError, "inter-file crash"):
                self.integrate()
        local = workflow_runtime._team_local_operation(self.repo, manifest["operation_id"])
        self.assertEqual(local["integration"]["manifest"], manifest)
        self.assertEqual(local["state"], "RESERVED")
        (self.repo / "docs/CODEX_CONTROL.md").write_bytes(b"mixed invalid control\n")
        self.registered.stop()
        with mock.patch.object(workflow_runtime, "_team_enabled", side_effect=AssertionError("control read before pending guard")):
            for command in workflow_runtime.TEAM_FENCED_CALLS | workflow_runtime.TEAM_NATIVE_EFFECTS:
                with self.subTest(command=command), self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
                    workflow_runtime.team_guard(self.repo, command=command, paths=[])
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
                workflow_runtime.team_observe_remote(self.repo, operation_id="another-action")
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
                workflow_runtime.team_confirm_effect(self.repo, operation_id=manifest["operation_id"],
                    candidate=self.fixture.candidate, expected_sha256="a" * 64)
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
                self.fixture.save(self.document(self.data()))
        self.fixture.candidate.write_bytes(team_records.canonical_json(manifest))
        self.assertEqual(self.integrate()["status"], "INTEGRATED")
        workflow_runtime._team_pending_guard(self.repo)

    def test_integration_crash_before_write_and_third_state_drift(self):
        manifest = self.integration_fixture()
        with mock.patch.object(workflow_runtime, "_resume_cas_bytes", side_effect=RuntimeError("before copy")):
            with self.assertRaisesRegex(RuntimeError, "before copy"):
                self.integrate()
        self.source.write_bytes(b"unexpected third state\n")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PREIMAGE_CHANGED"):
            self.integrate()
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
            workflow_runtime._team_pending_guard(self.repo)
        self.assertEqual(workflow_runtime._resume_digest((self.repo / manifest["files"][1]["path"]).read_bytes()), manifest["files"][1]["before_sha256"])

    def test_reviewed_source_rejects_new_untracked_destination_collision(self):
        manifest = self.integration_fixture(include_untracked_destination=True)
        collision = self.repo / "docs/new-target.md"
        before = collision.read_bytes()
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PREIMAGE_CHANGED"):
            self.integrate()
        self.assertEqual(collision.read_bytes(), before)
        self.assertNotIn("integration", workflow_runtime._team_local_operation(self.repo, manifest["operation_id"]))

    def test_reviewed_source_preserves_executable_git_source_mode(self):
        manifest = self.integration_fixture(include_executable=True)
        result = self.integrate()
        self.assertEqual(result["status"], "INTEGRATED")
        executable = self.repo / "docs/executable.sh"
        self.assertEqual(stat.S_IMODE(executable.stat().st_mode), 0o755)
        row = next(item for item in manifest["files"] if item["path"] == "docs/executable.sh")
        _, mode = workflow_runtime._team_integration_blob(self.repo, manifest["candidate_commit"], row["path"])
        self.assertEqual(mode, 0o755)

    def test_integration_rejects_changed_assignment_immutable_input_and_scope(self):
        self.setUp()
        manifest = self.integration_fixture()
        registry = self.repo / workflow_runtime.TEAM_ASSIGNMENTS
        raw = registry.read_bytes()
        parsed = team_records.read_registry(raw, "assignments")
        current = parsed["assignments"][manifest["implementer_assignment"]]
        for changes in (
            {"input_hashes": [{"path": "docs/changed-input.md", "sha256": "c" * 64}]},
            {"permitted_paths": ["docs/source.md"]},
        ):
            with self.subTest(changes=changes):
                updated = dict(current["assignment"])
                updated.update(changes)
                updated.update(
                    operation="UPDATE",
                    previous_assignment_event_sha256=current["last_event_sha256"],
                    previous_assignment_sha256=team_records._assignment_state_sha(current["assignment"]),
                )
                with self.assertRaisesRegex(team_records.TeamRecordError, "ASSIGNMENT_IMMUTABLE_FIELD"):
                    team_records.prepare_assignment(
                        raw, updated, workflow_runtime._resume_digest(raw)
                    )

        self.assertEqual(manifest["mode"], "REVIEWED_SOURCE")

    def test_pending_integration_blocks_real_public_writer_entrypoints(self):
        manifest = self.integration_fixture()
        with mock.patch.object(workflow_runtime, "_resume_cas_bytes", side_effect=RuntimeError("before copy")):
            with self.assertRaisesRegex(RuntimeError, "before copy"):
                self.integrate()

        self.registered.stop()
        for command in workflow_runtime.TEAM_FENCED_CALLS | workflow_runtime.TEAM_NATIVE_EFFECTS:
            with self.subTest(command=command), self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"
            ):
                workflow_runtime.team_guard(self.repo, command=command, paths=[])
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
            workflow_runtime.team_local_init(self.repo)
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
            workflow_runtime.team_observe_remote(self.repo, operation_id="other-action")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
            workflow_runtime.team_reserve_effect(self.repo, operation_id="other-action")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INTEGRATION_PENDING"):
            workflow_runtime.team_confirm_effect(
                self.repo, operation_id=manifest["operation_id"],
                candidate=self.fixture.candidate, expected_sha256="a" * 64,
            )

    def _fresh_process_integration_fixture(self):
        """Build a real committed engine and an independent --root destination."""
        root_holder = tempfile.TemporaryDirectory(prefix="q3-team-fresh-integration-")
        self.addCleanup(root_holder.cleanup)
        root = Path(root_holder.name)
        source_root = Path(__file__).resolve().parents[2]
        git_env = {
            **os.environ,
            "GIT_AUTHOR_NAME": "Fixture",
            "GIT_COMMITTER_NAME": "Fixture",
            "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
            "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
        }

        def git(repo, *args, input=None, index=None):
            env = {**git_env, **({"GIT_INDEX_FILE": str(index)} if index else {})}
            result = subprocess.run(
                ["git", *args], cwd=repo, env=env, input=input,
                capture_output=True, check=True,
            )
            return result.stdout.decode().strip()

        engine = root / "engine"
        engine_sources = tuple(
            path.relative_to(source_root).as_posix()
            for path in sorted((source_root / "orchestrator").glob("*.py"))
        ) + ("scripts/q3_docs_corpus.py",)
        for relative in engine_sources:
            target = engine / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_root / relative, target)
        git(engine, "init", "-q")
        git(engine, "add", ".")
        git(engine, "commit", "-qm", "Immutable committed integration engine")
        engine_head = git(engine, "rev-parse", "HEAD")

        destination = root / "destination"
        destination.mkdir()
        git(destination, "init", "-q")
        for relative in (
            "docs/CODEX_CONTROL.md",
            "docs/cartographer/TOOLS.yaml",
            "docs/INSTRUCTION_ISSUES.md",
            "docs/Codex/AGENTS_LEDGER.md",
            "docs/Codex/GOAL.md",
            "orchestrator/workflow_runtime.py",
        ):
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_root / relative, target)
        (destination / "docs/INSTRUCTION_ISSUES.md").write_bytes(b"# Fixture issues\n")
        (destination / workflow_runtime.TEAM_ASSIGNMENTS).write_bytes(b"# Fixture assignments\n")
        (destination / workflow_runtime.RESUME_PATH).write_bytes(b"placeholder resume\n")
        (destination / workflow_runtime.RESUME_HISTORY_PATH).write_bytes(
            workflow_runtime.RESUME_HISTORY_HEADER
        )
        (destination / "docs/source.md").write_bytes(b"exact source\n")
        (destination / "zz-integration-target.txt").write_bytes(b"old target\n")
        git(destination, "add", ".")
        git(destination, "commit", "-qm", "Integration destination baseline")
        expected_head = git(destination, "rev-parse", "HEAD")

        lock = destination / ".git/q3-three-body.writer.lock"
        lock.touch(mode=0o600)
        secret = b"1" * 32
        installation_ref = hashlib.sha256(
            b"q3-team-installation-v1\0" + secret
        ).hexdigest()
        installation = {
            "schema": workflow_runtime.TEAM_INSTALLATION,
            "installation_secret": secret.hex(),
            "installation_ref": installation_ref,
        }
        private_installation = destination / ".git" / workflow_runtime.TEAM_INSTALLATION
        private_installation.write_bytes(workflow_runtime._team_json(installation))
        private_installation.chmod(0o600)
        local = {
            "schema": workflow_runtime.TEAM_LOCAL,
            "installation_ref": installation_ref,
            "operations": {},
            "watch": None,
            "epoch_floor": 0,
        }
        private_local = destination / ".git" / workflow_runtime.TEAM_LOCAL
        private_local.write_bytes(workflow_runtime._team_json(local))
        private_local.chmod(0o600)

        candidate_index = root / "candidate.index"
        git(destination, "read-tree", expected_head, index=candidate_index)
        before_runtime = (destination / "orchestrator/workflow_runtime.py").read_bytes()
        after_runtime = before_runtime + b"\n# candidate runtime replacement\n" + b"# padding\n" * 150000
        before_target = (destination / "zz-integration-target.txt").read_bytes()
        after_target = b"candidate target\n" + b"x" * 1450000
        candidate_files = []
        for path, before, after in (
            ("orchestrator/workflow_runtime.py", before_runtime, after_runtime),
            ("zz-integration-target.txt", before_target, after_target),
        ):
            blob = git(destination, "hash-object", "-w", "--stdin", input=after)
            git(destination, "update-index", "--cacheinfo", "100644," + blob + "," + path,
                index=candidate_index)
            candidate_files.append({
                "path": path,
                "source_path": path,
                "before_sha256": workflow_runtime._resume_digest(before),
                "sha256": workflow_runtime._resume_digest(after),
            })
        candidate_tree = git(destination, "write-tree", index=candidate_index)
        candidate_commit = git(
            destination, "commit-tree", candidate_tree, "-p", expected_head,
            input=b"Fresh process candidate\n",
        )

        source_digest = workflow_runtime._resume_digest(
            (destination / "docs/source.md").read_bytes()
        )
        assignments = []
        permitted = [item["path"] for item in candidate_files]
        for role, assignee in (("implementation", "producer"), ("independent-checker", "checker")):
            assignment = TeamRecordsTests.assignment(assignment_id="fresh-" + assignee)
            assignment.update(
                owner_task=self.data()["owner_thread_id"], owner_host="local", owner_epoch=1,
                owner_installation_ref=installation_ref, assignee=assignee, role=role,
                base_commit=expected_head, subject="fresh process integration",
                input_hashes=[{"path": "docs/source.md", "sha256": source_digest}],
                permitted_paths=permitted,
            )
            assignments.append(assignment)
        assignments_path = destination / workflow_runtime.TEAM_ASSIGNMENTS
        assignments_path.write_bytes(b"# Fixture assignments\n")
        for assignment in assignments:
            previous = assignments_path.read_bytes()
            updated, _ = team_records.prepare_assignment(
                previous, assignment, workflow_runtime._resume_digest(previous)
            )
            assignments_path.write_bytes(updated)
        producer, checker = assignments
        manifest = {
            "schema": "q3_team_integration.v1",
            "mode": "REVIEWED_SOURCE",
            "operation_id": "fresh-process-integration",
            "owner_task": self.data()["owner_thread_id"],
            "installation_ref": installation_ref,
            "epoch": 1,
            "expected_head": expected_head,
            "implementer_assignment": producer["assignment_id"],
            "assignment_sha256": workflow_runtime._resume_digest(
                team_records.canonical_json(team_records._assignment_immutable_view(producer))
            ),
            "checker_assignment": checker["assignment_id"],
            "candidate_commit": candidate_commit,
            "files": candidate_files,
        }
        manifest_bytes = team_records.canonical_json(manifest)
        manifest_path = root / "detached-manifest.json"
        manifest_path.write_bytes(manifest_bytes)

        review_artifact = {
            "schema": "q3_team_integration_review.v1",
            "manifest_sha256": workflow_runtime._resume_digest(manifest_bytes),
            "base_commit": expected_head,
            "candidate_commit": candidate_commit,
            "files": [{"path": row["path"], "sha256": row["sha256"]} for row in candidate_files],
            "implementer_assignment": producer["assignment_id"],
            "checker_assignment": checker["assignment_id"],
            "verdict": "SOURCE_INTEGRATION_APPROVED",
        }
        observations = TeamRecordsTests.provenance_context(checker).observations[checker["assignment_id"]]
        for observation in observations:
            phase = observation["phase"]
            output = b"fresh launch\n" if phase == "LAUNCH" else team_records.canonical_json(review_artifact)
            output_path = destination / ("docs/fresh-integration-output-" + phase + ".json")
            receipt_path = destination / ("docs/fresh-integration-provider-" + phase + ".json")
            output_path.write_bytes(output)
            receipt_path.write_bytes(b'{"simulated_provider":true}\n')
            observation["output_locator"] = str(output_path.relative_to(destination))
            observation["output_sha256"] = workflow_runtime._resume_digest(output)
            observation["provider_receipt_locator"] = str(receipt_path.relative_to(destination))
            observation["provider_receipt_sha256"] = workflow_runtime._resume_digest(receipt_path.read_bytes())
            observation["evidence_sha256"] = workflow_runtime._resume_digest(team_records.canonical_json([
                {"locator": observation[prefix + "_locator"], "sha256": observation[prefix + "_sha256"]}
                for prefix in ("output", "provider_receipt")
            ]))
            local["operations"][observation["operation_id"]] = {
                "schema": "q3_team_assignment_receipt.v1",
                "state": "CONFIRMED",
                "observation": observation,
            }

        data = self.data()
        data["ownership"]["installation_ref"] = installation_ref
        data["source_manifest"] = {"docs/source.md": source_digest}
        data["operation"]["inputs"] = dict(data["source_manifest"])
        source_manifest_sha = workflow_runtime._resume_digest(
            workflow_runtime._team_json(data["source_manifest"])
        )
        for stage in data["stages"].values():
            stage["source_sha256"] = source_manifest_sha
        data["operation"].update(
            id=manifest["operation_id"],
            command="workflow-team-integrate-candidate",
            subject={
                "kind": "REPAIR", "id": manifest["operation_id"],
                "sha256": workflow_runtime._resume_digest(manifest_bytes),
            },
        )
        raw = self.document(data)
        (destination / workflow_runtime.RESUME_PATH).write_bytes(raw)
        _, goal_record = workflow_runtime._resume_history_record(
            "goal", 0, (destination / "docs/Codex/GOAL.md").read_bytes()
        )
        _, intent = workflow_runtime._resume_history_record("intent", data["revision"], raw)
        (destination / workflow_runtime.RESUME_HISTORY_PATH).write_bytes(
            workflow_runtime.RESUME_HISTORY_HEADER + goal_record + intent
        )
        local["operations"][manifest["operation_id"]] = {
            "state": "OBSERVED",
            "actor": data["owner_thread_id"],
            "epoch": 1,
            "checkpoint_sha256": workflow_runtime._resume_digest(raw),
            "remote_ownership": data["ownership"],
            "remote_thread": data["owner_thread_id"],
            "local_head": expected_head,
        }
        private_local.write_bytes(workflow_runtime._team_json(local))
        workflow_runtime.team_reserve_effect(
            destination, operation_id=manifest["operation_id"]
        )

        return {
            "root": root,
            "engine": engine,
            "destination": destination,
            "engine_head": engine_head,
            "expected_head": expected_head,
            "manifest": manifest,
            "manifest_path": manifest_path,
            "before_runtime": before_runtime,
            "after_runtime": after_runtime,
            "before_target": before_target,
            "after_target": after_target,
            "private_local": private_local,
        }

    def test_fresh_process_recovers_persisted_manifest_after_runtime_write_crash(self):
        fixture = self._fresh_process_integration_fixture()
        engine = fixture["engine"]
        destination = fixture["destination"]
        manifest = fixture["manifest"]
        manifest_path = fixture["manifest_path"]
        environment = {
            **os.environ,
            "CODEX_THREAD_ID": manifest["owner_task"],
            "Q3_OWNER_EPOCH": "1",
            "PYTHONPATH": "",
        }
        command = [
            sys.executable, str(engine / "orchestrator/workflow_runtime.py"),
            "--root", str(destination), "team-integrate-candidate",
            "--candidate", str(manifest_path),
        ]
        process = subprocess.Popen(
            command, cwd=engine, env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        killed_after_first_write = False
        deadline = time.monotonic() + 45
        runtime_path = destination / "orchestrator/workflow_runtime.py"
        while process.poll() is None and time.monotonic() < deadline:
            try:
                if runtime_path.stat().st_size == len(fixture["after_runtime"]):
                    process.send_signal(signal.SIGKILL)
                    killed_after_first_write = True
                    break
            except FileNotFoundError:
                pass
            time.sleep(0.001)
        if not killed_after_first_write:
            process.kill()
        stdout, stderr = process.communicate(timeout=15)
        self.assertTrue(
            killed_after_first_write,
            (stdout + stderr).decode(errors="replace"),
        )
        self.assertEqual(process.returncode, -signal.SIGKILL)
        self.assertEqual(runtime_path.read_bytes(), fixture["after_runtime"])
        self.assertEqual(
            (destination / "zz-integration-target.txt").read_bytes(),
            fixture["before_target"],
        )

        pending = json.loads(fixture["private_local"].read_bytes())
        pending_record = pending["operations"][manifest["operation_id"]]
        self.assertEqual(pending_record["state"], "RESERVED")
        self.assertEqual(pending_record["integration"]["state"], "PENDING")
        self.assertEqual(pending_record["integration"]["manifest"], manifest)

        pending_plan = subprocess.run(
            [sys.executable, str(engine / "orchestrator/workflow_runtime.py"),
             "--root", str(destination), "plan"],
            cwd=engine, env=environment, capture_output=True, text=True, check=False,
        )
        self.assertEqual(pending_plan.returncode, 2, pending_plan.stdout + pending_plan.stderr)
        pending_card = json.loads(pending_plan.stdout)
        self.assertEqual(pending_card["status"], "HOLD")
        self.assertEqual(pending_card["continuation"]["status"], "RECOVERY_ONLY")
        recovery = pending_card["continuation"]["recovery"]
        self.assertEqual(recovery["recover_operation"], manifest["operation_id"])
        self.assertEqual(recovery["engine"]["root"], str(engine))
        self.assertEqual(recovery["engine"]["commit"], fixture["engine_head"])
        self.assertFalse(pending_card["writes_performed"])
        self.assertFalse(pending_card["execution_ready"])
        self.assertIsNone(pending_card["selected_goal"])

        detached = manifest_path.with_suffix(".detached")
        manifest_path.rename(detached)
        detached.write_bytes(b'{"detached_manifest_was_changed":true}\n')
        self.assertFalse(manifest_path.exists())

        recovered = subprocess.run(
            [
                sys.executable, str(engine / "orchestrator/workflow_runtime.py"),
                "--root", str(destination), "team-integrate-candidate",
                "--recover-operation", manifest["operation_id"],
            ],
            cwd=engine, env=environment, capture_output=True, text=True, check=False,
        )
        self.assertEqual(recovered.returncode, 0, recovered.stdout + recovered.stderr)
        recovery_receipt = json.loads(recovered.stdout)
        self.assertEqual(recovery_receipt["status"], "INTEGRATED")
        self.assertEqual(runtime_path.read_bytes(), fixture["after_runtime"])
        target = destination / "zz-integration-target.txt"
        self.assertEqual(target.read_bytes(), fixture["after_target"])
        self.assertEqual(stat.S_IMODE(runtime_path.stat().st_mode), 0o644)
        self.assertEqual(stat.S_IMODE(target.stat().st_mode), 0o644)
        self.assertEqual(
            subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=engine, text=True).strip(),
            fixture["engine_head"],
        )
        self.assertEqual(
            subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=destination, text=True).strip(),
            fixture["expected_head"],
        )
        self.assertEqual(subprocess.check_output(["git", "remote"], cwd=engine, text=True), "")
        self.assertEqual(subprocess.check_output(["git", "remote"], cwd=destination, text=True), "")
        completed = json.loads(fixture["private_local"].read_bytes())
        completed_record = completed["operations"][manifest["operation_id"]]
        self.assertEqual(completed_record["state"], "CONFIRMED")
        self.assertEqual(completed_record["integration"]["state"], "COMPLETE")
        workflow_runtime._team_pending_guard(destination)

        replay = subprocess.run(
            [
                sys.executable, str(engine / "orchestrator/workflow_runtime.py"),
                "--root", str(destination), "team-integrate-candidate",
                "--recover-operation", manifest["operation_id"],
            ],
            cwd=engine, env=environment, capture_output=True, text=True, check=False,
        )
        self.assertEqual(replay.returncode, 2)
        replay_receipt = json.loads(replay.stdout)
        self.assertEqual(replay_receipt["status"], "HOLD")
        self.assertIn("RECOVERY_RECORD_REQUIRED", replay_receipt["reason"])

    def test_integration_schema_rejects_raw_alias_symlink_and_untracked_collision(self):
        manifest = self.integration_fixture(intake=True)
        altered = json.loads(json.dumps(manifest))
        altered["files"][0]["path"] = "docs/arbitrary.bin"
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "CONTENT_ADDRESS"):
            workflow_runtime._team_integration_manifest(team_records.canonical_json(altered))
        altered = json.loads(json.dumps(manifest))
        altered["files"][0]["content_base64"] += "\n"
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "BASE64"):
            workflow_runtime._team_integration_manifest(team_records.canonical_json(altered))
        evidence = self.repo / manifest["files"][0]["path"]
        evidence.parent.mkdir(parents=True, exist_ok=True)
        evidence.symlink_to(self.source)
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "UNSAFE_PATH"):
            self.integrate()
        evidence.rename(evidence.with_suffix(".saved-symlink"))
        evidence.write_bytes(b"different existing untracked bytes")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PREIMAGE_CHANGED"):
            self.integrate()

    def test_integration_requires_commit_object_and_producing_base_ancestry(self):
        manifest = self.integration_fixture()
        _, data, _ = workflow_runtime._team_current(self.repo)
        blob = workflow_runtime._team_git(self.repo, "rev-parse", manifest["expected_head"] + ":docs/source.md").decode().strip()
        unrelated_env = {**workflow_runtime.os.environ, "GIT_AUTHOR_NAME": "Fixture", "GIT_COMMITTER_NAME": "Fixture",
                         "GIT_AUTHOR_EMAIL": "fixture@example.invalid", "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
        tree = workflow_runtime._team_git(self.repo, "rev-parse", manifest["candidate_commit"] + "^{tree}").decode().strip()
        unrelated = subprocess.run(["git", "commit-tree", tree], cwd=self.repo, env=unrelated_env,
                                   input=b"unrelated root\n", capture_output=True, check=True).stdout.decode().strip()
        for value, error in ((blob, "COMMIT_OBJECT_REQUIRED"), (unrelated, "GIT_OBSERVATION_FAILED:merge-base")):
            changed = {**manifest, "candidate_commit": value}
            with self.subTest(candidate=value), self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, error):
                workflow_runtime._team_integration_review(self.repo, data, changed, team_records.canonical_json(changed))
        changed = {**manifest, "expected_head": manifest["candidate_commit"]}
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INDEPENDENT_BASE_REVIEW_REQUIRED"):
            workflow_runtime._team_integration_review(self.repo, data, changed, team_records.canonical_json(changed))

    def test_integration_recovers_persisted_manifest_but_rejects_changed_engine(self):
        manifest = self.integration_fixture()
        with mock.patch.object(workflow_runtime, "_resume_cas_bytes", side_effect=RuntimeError("before copy")):
            with self.assertRaisesRegex(RuntimeError, "before copy"):
                self.integrate()
        with mock.patch.object(workflow_runtime, "_team_integration_engine", return_value={"different_engine": True}):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "PERSISTED_IDENTITY_CHANGED"):
                self.integrate()
        manifest = json.loads(self.fixture.candidate.read_bytes())
        manifest["files"][0]["sha256"] = "a" * 64
        self.fixture.candidate.write_bytes(team_records.canonical_json(manifest))
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "EXACT_INTENT_REQUIRED"):
            self.integrate()
        self.fixture.candidate.rename(self.fixture.candidate.with_suffix(".lost"))
        result = workflow_runtime.team_integrate_candidate(self.repo, recover_operation="integration-fixture")
        self.assertEqual(result["status"], "INTEGRATED")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "RECOVERY_RECORD_REQUIRED"):
            workflow_runtime.team_integrate_candidate(self.repo, recover_operation="integration-fixture")

    def test_initialization_private_replay_and_no_secret_receipt(self):
        result = workflow_runtime.team_local_init(self.repo)
        self.assertEqual(result["status"], "NOOP")
        private = self.repo / ".git" / workflow_runtime.TEAM_INSTALLATION
        self.assertEqual(private.stat().st_mode & 0o777, 0o600)
        secret = json.loads(private.read_bytes())["installation_secret"]
        self.assertNotIn(secret, json.dumps(result))
        raw = private.read_bytes()
        with workflow_runtime._execution_writer_epoch(self.repo):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "LOCK_COLLISION"):
                workflow_runtime.team_local_init(self.repo)
        self.assertEqual(private.read_bytes(), raw)

    def test_identity_mismatch_and_missing_identity_with_existing_bindings(self):
        private = self.repo / ".git" / workflow_runtime.TEAM_INSTALLATION
        original = private.read_bytes()
        data = json.loads(original)
        data["installation_ref"] = "f" * 64
        private.write_bytes(workflow_runtime._team_json(data))
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "REFERENCE_MISMATCH"):
            workflow_runtime._team_installation(self.repo)
        private.write_bytes(original)
        self.local(epoch_floor=2)
        # Rename the fixture identity rather than deleting it.
        private.rename(private.with_suffix(".saved"))
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INSTALLATION_RECOVERY_REQUIRED"):
            workflow_runtime.team_local_init(self.repo)

    def test_local_identity_read_does_not_treat_access_time_as_a_write(self):
        import itertools
        from types import SimpleNamespace
        private = self.repo / ".git" / workflow_runtime.TEAM_INSTALLATION
        before = private.lstat()
        after = SimpleNamespace(**{name: getattr(before, name) for name in dir(before) if name.startswith("st_")})
        after.st_atime_ns += 1000000000
        with mock.patch.object(Path, "lstat", side_effect=itertools.chain([before], itertools.repeat(after))):
            self.assertEqual(workflow_runtime._team_installation(self.repo)["installation_ref"], self.identity)

    def test_v1_archive_stays_readable_after_v2_migration(self):
        first = self.fixture.document()
        self.fixture.save(first)
        data = self.data()
        data.update(revision=2, previous_sha256=workflow_runtime._resume_digest(first))
        self.fixture.save(self.document(data), expected=data["previous_sha256"])
        records = workflow_runtime._resume_history(self.fixture.history.read_bytes())
        self.assertIn(("resume", 1, first), records.values())
        self.assertEqual(self.fixture.save(self.document(data), expected=data["previous_sha256"])["status"], "NOOP")

    def _bootstrap_publication_fixture(self):
        """Build one real bare-v1 remote and a closed v1-to-v2 owner candidate."""
        holder = tempfile.TemporaryDirectory(prefix="q3-team-bootstrap-main-")
        self.addCleanup(holder.cleanup)
        root = Path(holder.name)
        seed, remote, owner = root / "seed", root / "remote.git", root / "owner"
        owner_id = "01a084f4-7498-7021-bac2-91d184d58dc7"
        full_control = (Path(__file__).resolve().parents[2] / "docs/CODEX_CONTROL.md").read_text()
        old_control = full_control.replace("TEAM_RUNTIME_VERSION: 1\n", "")
        full_tools = (Path(__file__).resolve().parents[2] / str(workflow_runtime.TOOLS)).read_bytes()
        old_tools = (
            b"tool_families:\n  workflow:\n    tools:\n"
            b"      - id: workflow-resume-checkpoint\n        status: ENABLED\n"
            b"        writes: true\n        write_paths:\n"
            b"          - docs/Codex/RESUME.md\n          - docs/Codex/GOAL_HISTORY.md\n"
        )

        def git(repo, *args, env=None):
            return subprocess.check_output(
                ["git", *args], cwd=repo, env=env, text=True
            ).strip()

        def git_run(repo, *args, env=None):
            return subprocess.run(["git", *args], cwd=repo, env=env, check=True)

        def body_document(data):
            body = "\n".join(
                "## " + name + "\nObserved evidence; reconcile before acting.\n"
                for name in workflow_runtime.RESUME_SECTIONS
            )
            return (
                "---\n" + workflow_runtime.yaml.safe_dump(data, sort_keys=False)
                + "---\n" + body
            ).encode()

        def v1_document(revision, previous, *, kind="NONE", state="NONE", operation_id="", evidence=None):
            return body_document({
                "schema": "q3_resume.v1", "revision": revision,
                "observed_at": "2026-09-11T10:00:00+02:00", "previous_sha256": previous,
                "owner_thread_id": owner_id, "owner_host_id": "local",
                "reconciliation_pending": False, "recovery_from": None,
                "pins": {"head": "a" * 40, "physical_goal": "docs/goal.md",
                         "source_commit": "b" * 40, "request_id": "REQ-EXISTING",
                         "phase_id": "PHASE-EXISTING"},
                "stages": {name: "PENDING" for name in
                           ("receipt", "independent_review", "parent_check", "acceptance", "publication")},
                "operation": {"kind": kind, "state": state, "id": operation_id,
                               "evidence": evidence or []},
            })

        def v2_data(*, revision, previous, installation_ref, operation, source_manifest):
            request = {"path": "docs/request.txt", "commit": "a" * 40, "blob": "b" * 40,
                       "sha256": "c" * 64, "boundary_id": "BOUNDARY",
                       "conversation_id": "fixture-chat"}
            source_sha = workflow_runtime._resume_digest(workflow_runtime._team_json(source_manifest))
            request_subject = {"kind": "REQUEST", "id": "REQ-EXISTING", "sha256": request["sha256"]}
            verdict_subject = {"kind": "VERDICT", "id": "VERDICT-EXISTING", "sha256": "d" * 64}
            stages = {
                name: {"subject": request_subject if index < 3 else verdict_subject,
                       "state": "NOT_STARTED", "evidence": {}, "source_sha256": source_sha,
                       "checked_by": None}
                for index, name in enumerate(workflow_runtime.TEAM_STAGES)
            }
            return {
                "schema": "q3_resume.v2", "revision": revision,
                "observed_at": "2026-09-11T10:00:00+02:00", "previous_sha256": previous,
                "owner_thread_id": owner_id, "owner_host_id": "local",
                "reconciliation_pending": False, "recovery_from": None,
                "pins": {"head": "a" * 40, "physical_goal": "docs/goal.md",
                         "source_commit": "b" * 40, "request_id": "REQ-EXISTING",
                         "phase_id": "PHASE-EXISTING", "phase_key": dict(PHASE_KEY),
                         "request": request},
                "stages": stages, "operation": operation,
                "ownership": {"installation_ref": installation_ref, "epoch": 1,
                              "state": "ACTIVE", "transfer": None},
                "source_manifest": source_manifest,
            }

        def save(repo, raw, expected):
            candidate = repo / "bootstrap-candidate.md"
            candidate.write_bytes(raw)
            return workflow_runtime.resume_checkpoint(repo, candidate=candidate, expected_sha256=expected)

        for path in (workflow_runtime.RESUME_PATH, workflow_runtime.TOOLS,
                     workflow_runtime.RESUME_HISTORY_PATH, workflow_runtime.TEAM_ISSUES,
                     workflow_runtime.TEAM_ASSIGNMENTS, Path("docs/CODEX_CONTROL.md"),
                     Path("docs/Codex/GOAL.md"), Path("orchestrator/workflow_runtime.py")):
            (seed / path).parent.mkdir(parents=True, exist_ok=True)
        git_run(root, "init", "--bare", "-q", str(remote))
        git_run(root, "init", "-q", str(seed))
        (seed / "docs/CODEX_CONTROL.md").write_text(old_control)
        (seed / workflow_runtime.TOOLS).write_bytes(old_tools)
        (seed / workflow_runtime.TEAM_ISSUES).write_bytes(b"# Fixture issues\n")
        (seed / workflow_runtime.TEAM_ASSIGNMENTS).write_bytes(b"# Fixture assignments\n")
        (seed / "docs/Codex/GOAL.md").write_bytes(b"goal\n")
        (seed / "docs/bootstrap-source.txt").write_bytes(b"stable reviewed source\n")
        (seed / "orchestrator/workflow_runtime.py").write_bytes(b"old runtime subset\n")
        initial = v1_document(1, "ABSENT")
        (seed / workflow_runtime.RESUME_PATH).write_bytes(initial)
        _, goal_entry = workflow_runtime._resume_history_record("goal", 0, b"goal\n")
        _, intent_entry = workflow_runtime._resume_history_record("intent", 1, initial)
        (seed / workflow_runtime.RESUME_HISTORY_PATH).write_bytes(
            workflow_runtime.RESUME_HISTORY_HEADER + goal_entry + intent_entry
        )
        env = {**workflow_runtime.os.environ, "GIT_AUTHOR_NAME": "Fixture",
               "GIT_COMMITTER_NAME": "Fixture", "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
               "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
        git_run(seed, "add", ".", env=env)
        git_run(seed, "commit", "-qm", "Initial v1 checkpoint", env=env)
        git_run(seed, "branch", "-M", "rh_clean")
        git_run(seed, "remote", "add", "origin", str(remote))
        git_run(seed, "push", "-q", "origin", "HEAD:refs/heads/rh_clean", env=env)
        git_run(root, "clone", "-q", "--branch", "rh_clean", str(remote), str(owner))
        (owner / ".git/q3-three-body.writer.lock").touch()

        initial_sha = workflow_runtime._resume_digest(initial)
        local_install_id = "BOOTSTRAP-PUBLICATION:local-install"
        local_intent = v1_document(2, initial_sha, kind="PUBLISH", state="INTENT",
                                   operation_id=local_install_id)
        save(owner, local_intent, initial_sha)
        runtime = owner / "orchestrator/workflow_runtime.py"
        runtime.write_bytes(b"reviewed runtime subset\n")
        (owner / workflow_runtime.TOOLS).write_bytes(full_tools)
        git_run(owner, "add", "orchestrator/workflow_runtime.py", str(workflow_runtime.TOOLS),
                str(workflow_runtime.RESUME_PATH), str(workflow_runtime.RESUME_HISTORY_PATH), env=env)
        git_run(owner, "commit", "-qm", "Install reviewed runtime subset", env=env)
        local_commit = git(owner, "rev-parse", "HEAD")

        local_confirmed = v1_document(
            3, workflow_runtime._resume_digest(local_intent), kind="PUBLISH", state="CONFIRMED",
            operation_id=local_install_id, evidence=["bootstrap_local_commit:" + local_commit]
        )
        save(owner, local_confirmed, workflow_runtime._resume_digest(local_intent))
        confirmed_sha = workflow_runtime._resume_digest(local_confirmed)
        identity = workflow_runtime.team_local_init(owner)

        migration_source_manifest = {
            "docs/bootstrap-source.txt": workflow_runtime._resume_digest(
                (owner / "docs/bootstrap-source.txt").read_bytes()
            ),
        }
        local_inputs = {
            "docs/cartographer/TOOLS.yaml": workflow_runtime._resume_digest(
                (owner / workflow_runtime.TOOLS).read_bytes()
            ),
            "orchestrator/workflow_runtime.py": workflow_runtime._resume_digest(runtime.read_bytes()),
        }
        local_operation_id = local_install_id
        local_operation = {
            "kind": "PUBLISH", "state": "CONFIRMED", "id": local_operation_id,
            "evidence": ["bootstrap_local_commit:" + local_commit],
            "subject": {"kind": "REPAIR", "id": local_operation_id,
                        "sha256": workflow_runtime._resume_digest(workflow_runtime._team_json(local_inputs))},
            "command": "workflow-team-bootstrap-publish", "inputs": local_inputs,
        }
        migrated = v2_data(revision=4, previous=confirmed_sha,
                           installation_ref=identity["installation_ref"],
                           operation=local_operation, source_manifest=migration_source_manifest)
        save(owner, body_document(migrated), confirmed_sha)
        git_run(owner, "add", str(workflow_runtime.RESUME_PATH),
                str(workflow_runtime.RESUME_HISTORY_PATH), env=env)
        git_run(owner, "commit", "-qm", "Migrate owner checkpoint", env=env)
        migrated_sha = workflow_runtime._resume_digest(body_document(migrated))

        final_control = owner / "docs/CODEX_CONTROL.md"
        final_control.write_text(full_control)
        final_input = owner / "docs/bootstrap-input.txt"
        final_input.write_bytes(b"final reviewed input\n")
        source_manifest = {
            "docs/bootstrap-source.txt": migration_source_manifest["docs/bootstrap-source.txt"],
            "docs/bootstrap-input.txt": workflow_runtime._resume_digest(final_input.read_bytes()),
        }
        publication_inputs = {
            "docs/CODEX_CONTROL.md": workflow_runtime._resume_digest(final_control.read_bytes()),
            "docs/bootstrap-input.txt": source_manifest["docs/bootstrap-input.txt"],
            **local_inputs,
        }
        git_run(owner, "add", "docs/CODEX_CONTROL.md", "docs/bootstrap-input.txt", env=env)
        git_run(owner, "commit", "-qm", "Install final control and source", env=env)

        publication_id = "BOOTSTRAP-PUBLICATION"
        publication_operation = {
            "kind": "PUBLISH", "state": "INTENT", "id": publication_id, "evidence": [],
            "subject": {"kind": "REPAIR", "id": publication_id,
                        "sha256": workflow_runtime._resume_digest(workflow_runtime._team_json(publication_inputs))},
            "command": "workflow-team-bootstrap-publish", "inputs": publication_inputs,
        }
        publication = v2_data(revision=5, previous=migrated_sha,
                              installation_ref=identity["installation_ref"],
                              operation=publication_operation, source_manifest=source_manifest)
        publication_raw = body_document(publication)
        save(owner, publication_raw, migrated_sha)
        git_run(owner, "add", str(workflow_runtime.RESUME_PATH), str(workflow_runtime.RESUME_HISTORY_PATH), env=env)
        git_run(owner, "commit", "-qm", "Start initial publication", env=env)
        expected_head = git(owner, "rev-parse", "HEAD")
        remote_raw = initial
        remote_commit = git(seed, "rev-parse", "HEAD")
        return {
            "root": root, "remote": remote, "owner": owner, "owner_id": owner_id,
            "operation_id": publication_id, "expected_head": expected_head,
            "remote_commit": remote_commit, "remote_raw": remote_raw,
            "remote_resume_sha256": workflow_runtime._resume_digest(remote_raw),
            "publication_raw": publication_raw, "source_manifest": source_manifest,
            "publication_inputs": publication_inputs,
            "local_install_commit": local_commit,
        }

    def _bootstrap_commit_tree(self, fixture, *, writes=(), deletes=(), modes=None, message):
        owner = fixture["owner"]
        paths = set()
        for relative, payload in writes:
            path = owner / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            paths.add(str(relative))
        for relative in deletes:
            path = owner / relative
            path.unlink()
            paths.add(str(relative))
        for relative, mode in (modes or {}).items():
            path = owner / relative
            path.chmod(mode)
            paths.add(str(relative))
        env = {
            **workflow_runtime.os.environ,
            "GIT_AUTHOR_NAME": "Fixture",
            "GIT_COMMITTER_NAME": "Fixture",
            "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
            "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
        }
        subprocess.run(
            ["git", "add", "-A", "--", *sorted(paths)],
            cwd=owner, env=env, check=True,
        )
        subprocess.run(["git", "commit", "-qm", message], cwd=owner, env=env, check=True)
        fixture["expected_head"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=owner, text=True
        ).strip()

    @staticmethod
    def _bootstrap_render_snapshot(raw, mutate):
        data, body = workflow_runtime._resume_document(raw)
        updated = json.loads(json.dumps(data))
        mutate(updated)
        return (
            "---\n" + workflow_runtime.yaml.safe_dump(updated, sort_keys=False)
            + "---\n" + body
        ).encode()

    def _bootstrap_rewrite_snapshots(self, fixture, mutations, *, propagate=False, message):
        owner = fixture["owner"]
        history_path = owner / workflow_runtime.RESUME_HISTORY_PATH
        current_path = owner / workflow_runtime.RESUME_PATH
        original_history = history_path.read_bytes()
        records = workflow_runtime._resume_history(original_history)
        snapshots = {
            revision: raw
            for kind, revision, raw in records.values()
            if kind == "intent"
        }
        updated = dict(snapshots)
        for revision, mutate in mutations.items():
            updated[revision] = self._bootstrap_render_snapshot(updated[revision], mutate)
        if propagate:
            first_changed = min(mutations)
            for revision in range(first_changed + 1, max(updated) + 1):
                data, _ = workflow_runtime._resume_document(updated[revision])
                previous = workflow_runtime._resume_digest(updated[revision - 1])
                if data["previous_sha256"] != previous:
                    updated[revision] = self._bootstrap_render_snapshot(
                        updated[revision], lambda value, previous=previous: value.update(
                            previous_sha256=previous
                        )
                    )
        history = original_history
        for revision, old_raw in snapshots.items():
            new_raw = updated[revision]
            if new_raw == old_raw:
                continue
            kinds = {
                kind
                for kind, value_revision, payload in records.values()
                if value_revision == revision and payload == old_raw
            }
            for kind in sorted(kinds):
                _, old_entry = workflow_runtime._resume_history_record(kind, revision, old_raw)
                _, new_entry = workflow_runtime._resume_history_record(kind, revision, new_raw)
                self.assertEqual(history.count(old_entry), 1)
                history = history.replace(old_entry, new_entry)
        current_data, _ = workflow_runtime._resume_document(current_path.read_bytes())
        current_revision = current_data["revision"]
        writes = [(workflow_runtime.RESUME_HISTORY_PATH, history)]
        if updated[current_revision] != current_path.read_bytes():
            fixture["publication_raw"] = updated[current_revision]
            writes.append((workflow_runtime.RESUME_PATH, updated[current_revision]))
        self._bootstrap_commit_tree(
            fixture,
            writes=tuple(writes),
            message=message,
        )

    def _bootstrap_publish(self, fixture):
        return workflow_runtime.team_bootstrap_publish(
            fixture["owner"], operation_id=fixture["operation_id"],
            expected_head=fixture["expected_head"],
            expected_remote_commit=fixture["remote_commit"],
            expected_remote_resume_sha256=fixture["remote_resume_sha256"],
        )

    def test_bootstrap_closed_manifest_negative_matrix(self):
        def extra_committed_path(fixture):
            self._bootstrap_commit_tree(
                fixture, writes=(("docs/unlisted.txt", b"unlisted\n"),),
                message="Add unlisted bootstrap path",
            )

        def omitted_input(fixture):
            def mutate(data):
                data["operation"]["inputs"].pop("orchestrator/workflow_runtime.py")
                data["operation"]["subject"]["sha256"] = workflow_runtime._resume_digest(
                    workflow_runtime._team_json(data["operation"]["inputs"])
                )
            self._bootstrap_rewrite_snapshots(
                fixture, {5: mutate}, message="Omit bootstrap input from manifest"
            )

        def self_reference(fixture):
            def mutate(data):
                data["operation"]["inputs"][str(workflow_runtime.RESUME_PATH)] = "0" * 64
                data["operation"]["subject"]["sha256"] = workflow_runtime._resume_digest(
                    workflow_runtime._team_json(data["operation"]["inputs"])
                )
            self._bootstrap_rewrite_snapshots(
                fixture, {5: mutate}, message="Add self-referential bootstrap input"
            )

        def deleted_input(fixture):
            self._bootstrap_commit_tree(
                fixture, deletes=("orchestrator/workflow_runtime.py",),
                message="Delete bootstrap input",
            )

        def mode_drift(fixture):
            self._bootstrap_commit_tree(
                fixture, modes={"orchestrator/workflow_runtime.py": 0o755},
                message="Change bootstrap input mode",
            )

        def missing_history_prefix(fixture):
            def mutate(data):
                data["pins"]["head"] = "c" * 40
            self._bootstrap_rewrite_snapshots(
                fixture, {1: mutate}, message="Break committed remote history prefix"
            )

        def changed_intermediate_history(fixture):
            def mutate(data):
                data["previous_sha256"] = "0" * 64
            self._bootstrap_rewrite_snapshots(
                fixture, {3: mutate}, message="Break intermediate history chain"
            )

        def local_install_mismatch(fixture):
            def mutate(data):
                data["operation"]["state"] = "UNKNOWN"
                data["operation"]["evidence"] = []
            self._bootstrap_rewrite_snapshots(
                fixture, {3: mutate}, propagate=True,
                message="Remove local install confirmation",
            )

        def initial_epoch(fixture):
            def mutate(data):
                data["ownership"]["epoch"] = 2
            self._bootstrap_rewrite_snapshots(
                fixture, {5: mutate}, message="Retire initial bootstrap epoch"
            )

        cases = (
            ("extra committed input", extra_committed_path,
             r"TEAM_BOOTSTRAP_SCOPE_MISMATCH", {}),
            ("omitted declared input", omitted_input,
             r"TEAM_BOOTSTRAP_SCOPE_MISMATCH", {}),
            ("self-referential metadata", self_reference,
             r"TEAM_BOOTSTRAP_SELF_REFERENTIAL_INPUTS", {}),
            ("deleted declared input", deleted_input,
             r"TEAM_BOOTSTRAP_DELETION_FORBIDDEN:orchestrator/workflow_runtime\.py", {}),
            ("intermediate mode drift", mode_drift,
             r"TEAM_BOOTSTRAP_INTERMEDIATE_SOURCE_UNREVIEWED:orchestrator/workflow_runtime\.py", {}),
            ("missing remote history prefix", missing_history_prefix,
             r"TEAM_BOOTSTRAP_COMMITTED_HISTORY_OR_CHECKPOINT_CHANGED", {}),
            ("changed intermediate history", changed_intermediate_history,
             r"TEAM_BOOTSTRAP_HISTORY_CHAIN_CHANGED", {}),
            ("local install confirmation mismatch", local_install_mismatch,
             r"TEAM_BOOTSTRAP_LOCAL_INSTALL_CONFIRMATION_REQUIRED", {}),
            ("initial epoch mismatch", initial_epoch,
             r"TEAM_BOOTSTRAP_INITIAL_OWNER_REQUIRED", {}),
            ("foreign initial owner", lambda fixture: None,
             r"TEAM_OBSERVER_ONLY", {"CODEX_THREAD_ID": "foreign-bootstrap-owner"}),
        )
        for label, prepare, error, environment in cases:
            with self.subTest(case=label):
                fixture = self._bootstrap_publication_fixture()
                prepare(fixture)
                before_local = workflow_runtime._team_local(fixture["owner"])
                before_remote = workflow_runtime._team_git(
                    fixture["owner"], "ls-remote", "origin", "refs/heads/rh_clean"
                )
                with mock.patch.dict(workflow_runtime.os.environ, environment):
                    with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, error):
                        self._bootstrap_publish(fixture)
                self.assertEqual(workflow_runtime._team_local(fixture["owner"]), before_local)
                self.assertEqual(
                    workflow_runtime._team_git(
                        fixture["owner"], "ls-remote", "origin", "refs/heads/rh_clean"
                    ),
                    before_remote,
                )

    def test_bootstrap_publish_subprocess_sigkill_after_remote_push_reconciles(self):
        fixture = self._bootstrap_publication_fixture()
        root, owner, remote = fixture["root"], fixture["owner"], fixture["remote"]
        started = root / "post-receive.started"
        release = root / "post-receive.release"
        hook = remote / "hooks/post-receive"
        hook.write_text(
            "#!/bin/sh\n"
            f"printf started > {started}\n"
            f"while [ ! -e {release} ]; do sleep 0.01; done\n"
        )
        hook.chmod(0o755)
        driver = (
            "import json,sys\n"
            "from pathlib import Path\n"
            "from orchestrator import workflow_runtime as w\n"
            "w.live_plan_v10=lambda repo, **kwargs: {'status': 'HOLD', 'holds': ['TEST_DRIVER']}\n"
            "repo=Path(sys.argv[1])\n"
            "kwargs={'operation_id': sys.argv[2]}\n"
            "if sys.argv[3] == 'publish':\n"
            "    kwargs.update(expected_head=sys.argv[4], expected_remote_commit=sys.argv[5], "
            "expected_remote_resume_sha256=sys.argv[6])\n"
            "else:\n"
            "    kwargs['reconcile_only']=True\n"
            "print(json.dumps(w.team_bootstrap_publish(repo, **kwargs), sort_keys=True))\n"
        )
        environment = {
            **workflow_runtime.os.environ,
            "CODEX_THREAD_ID": fixture["owner_id"],
            "Q3_OWNER_EPOCH": "1",
        }
        script = Path(__file__).resolve().parents[2] / "orchestrator/workflow_runtime.py"
        command = [
            sys.executable, "-c", driver, str(owner), fixture["operation_id"], "publish",
            fixture["expected_head"], fixture["remote_commit"], fixture["remote_resume_sha256"],
        ]
        process = subprocess.Popen(
            command, cwd=script.parents[1], env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            start_new_session=True,
        )
        try:
            deadline = time.monotonic() + 45
            while not started.exists() and process.poll() is None and time.monotonic() < deadline:
                time.sleep(0.005)
            if not started.exists():
                stdout, stderr = process.communicate(timeout=5)
                self.fail("bootstrap post-receive hook was not reached: " + stdout + stderr)
            self.assertEqual(
                workflow_runtime._team_local(owner)["operations"][fixture["operation_id"]]["state"],
                "RESERVED",
            )
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate(timeout=15)
            self.assertEqual(process.returncode, -signal.SIGKILL, stdout + stderr)
            self.assertEqual(
                workflow_runtime._team_git(owner, "ls-remote", "origin", "refs/heads/rh_clean")
                .decode().split()[0],
                fixture["expected_head"],
            )
        finally:
            if process.poll() is None:
                release.touch()
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    process.wait(timeout=5)
        reconcile = subprocess.run(
            [
                sys.executable, "-c", driver, str(owner), fixture["operation_id"], "reconcile",
            ],
            cwd=script.parents[1], env=environment,
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(reconcile.returncode, 0, reconcile.stdout + reconcile.stderr)
        receipt = json.loads(reconcile.stdout)
        self.assertEqual(receipt["status"], "CONFIRMED")
        self.assertFalse(receipt["push_attempted"])

    def test_bootstrap_publish_first_v1_remote_succeeds_without_force_or_lease(self):
        fixture = self._bootstrap_publication_fixture()
        commands = []
        real_git = workflow_runtime._team_git

        def observed_git(repo, *args):
            commands.append(args)
            return real_git(repo, *args)

        with mock.patch.object(workflow_runtime, "_team_git", side_effect=observed_git):
            result = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            )
        self.assertEqual(result["status"], "CONFIRMED")
        self.assertTrue(result["push_attempted"])
        pushes = [args for args in commands if args and args[0] == "push"]
        self.assertEqual(
            pushes,
            [("push", "--no-follow-tags", "--recurse-submodules=no", "origin",
              fixture["expected_head"] + ":refs/heads/rh_clean")],
        )
        push_text = " ".join(" ".join(args) for args in pushes)
        self.assertNotIn("--force", push_text)
        self.assertNotIn("lease", push_text)
        self.assertNotIn("+refs/", push_text)
        self.assertEqual(
            workflow_runtime._team_git(fixture["owner"], "ls-remote", "origin",
                                        "refs/heads/rh_clean").decode().split()[0],
            fixture["expected_head"],
        )
        local = workflow_runtime._team_local(fixture["owner"])
        receipt = local["operations"][fixture["operation_id"]]
        self.assertEqual(receipt["state"], "CONFIRMED")
        manifest = receipt["bootstrap"]
        self.assertEqual(manifest["schema"], "q3_team_bootstrap_publish.v1")
        self.assertEqual(manifest["candidate_commit"], fixture["expected_head"])
        self.assertEqual(manifest["remote_commit"], fixture["remote_commit"])
        self.assertEqual(manifest["candidate_resume_sha256"], workflow_runtime._resume_digest(fixture["publication_raw"]))
        self.assertEqual(manifest["files"], sorted(manifest["files"], key=lambda row: row["path"]))
        self.assertEqual(
            [row["path"] for row in manifest["files"]],
            sorted(set(fixture["publication_inputs"]) | {str(workflow_runtime.RESUME_PATH), str(workflow_runtime.RESUME_HISTORY_PATH)}),
        )
        for row in manifest["files"]:
            self.assertIn(row["mode"], {0o644, 0o755})
            if row["path"] in fixture["publication_inputs"]:
                self.assertEqual(row["sha256"], fixture["publication_inputs"][row["path"]])
                if row["path"] == "docs/bootstrap-input.txt":
                    self.assertIsNone(row["before_mode"])
                else:
                    self.assertIn(row["before_mode"], {0o644, 0o755})
            else:
                self.assertIn(row["before_mode"], {0o644, 0o755})
        self.assertIn(
            {"commit": fixture["local_install_commit"], "parent": fixture["remote_commit"]},
            manifest["parents"],
        )
        self.assertTrue((fixture["owner"] / workflow_runtime.RESUME_HISTORY_PATH).read_bytes().startswith(
            (fixture["root"] / "seed" / workflow_runtime.RESUME_HISTORY_PATH).read_bytes()
        ))
        self.assertFalse(any(args and args[0] == "hook" for args in commands))
        self.assertFalse(any(args and args[0] == "config" and any(
            value in args for value in ("--add", "--unset", "--unset-all", "--replace-all")
        ) for args in commands))
        replay = workflow_runtime.team_bootstrap_publish(
            fixture["owner"], operation_id=fixture["operation_id"],
            expected_head=fixture["expected_head"],
            expected_remote_commit=fixture["remote_commit"],
            expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            reconcile_only=True,
        )
        self.assertEqual(replay["status"], "CONFIRMED")
        self.assertFalse(replay["push_attempted"])

    def test_bootstrap_publish_interruption_before_reservation_retries_once(self):
        fixture = self._bootstrap_publication_fixture()
        real_save = workflow_runtime._team_local_save
        with mock.patch.object(workflow_runtime, "_team_local_save", side_effect=RuntimeError("before reservation")):
            with self.assertRaisesRegex(RuntimeError, "before reservation"):
                workflow_runtime.team_bootstrap_publish(
                    fixture["owner"], operation_id=fixture["operation_id"],
                    expected_head=fixture["expected_head"],
                    expected_remote_commit=fixture["remote_commit"],
                    expected_remote_resume_sha256=fixture["remote_resume_sha256"],
                )
        self.assertFalse((fixture["owner"] / ".git" / workflow_runtime.TEAM_LOCAL).exists())
        result = workflow_runtime.team_bootstrap_publish(
            fixture["owner"], operation_id=fixture["operation_id"],
            expected_head=fixture["expected_head"],
            expected_remote_commit=fixture["remote_commit"],
            expected_remote_resume_sha256=fixture["remote_resume_sha256"],
        )
        self.assertEqual(result["status"], "CONFIRMED")
        self.assertIsNotNone(real_save)

    def test_bootstrap_publish_before_push_unknown_reconciles_without_second_push(self):
        fixture = self._bootstrap_publication_fixture()
        pushes = []
        real_git = workflow_runtime._team_git

        def fail_push(repo, *args):
            if args and args[0] == "push":
                pushes.append(args)
                raise workflow_runtime.WorkflowRuntimeError("simulated push interruption")
            return real_git(repo, *args)

        with mock.patch.object(workflow_runtime, "_team_git", side_effect=fail_push):
            first = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            )
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError, "TEAM_BOOTSTRAP_ARGUMENT_DRIFT"
            ):
                workflow_runtime.team_bootstrap_publish(
                    fixture["owner"], operation_id=fixture["operation_id"],
                    expected_head="0" * 40, reconcile_only=True,
                )
            second = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
                reconcile_only=True,
            )
        self.assertEqual(first["status"], "UNKNOWN")
        self.assertEqual(second["status"], "UNKNOWN")
        self.assertEqual(len(pushes), 1)
        self.assertEqual(
            workflow_runtime._team_local(fixture["owner"])["operations"][fixture["operation_id"]]["state"],
            "UNKNOWN",
        )

    def test_bootstrap_publish_after_server_push_before_confirmation_reconciles(self):
        fixture = self._bootstrap_publication_fixture()
        save_calls = 0
        pushes = []
        real_save = workflow_runtime._team_local_save
        real_git = workflow_runtime._team_git

        def crash_confirmation(repo, before, after, epoch):
            nonlocal save_calls
            save_calls += 1
            if save_calls == 2:
                raise RuntimeError("after server push")
            return real_save(repo, before, after, epoch)

        def observed_git(repo, *args):
            if args and args[0] == "push":
                pushes.append(args)
            return real_git(repo, *args)

        with mock.patch.object(workflow_runtime, "_team_local_save", side_effect=crash_confirmation), \
             mock.patch.object(workflow_runtime, "_team_git", side_effect=observed_git):
            with self.assertRaisesRegex(RuntimeError, "after server push"):
                workflow_runtime.team_bootstrap_publish(
                    fixture["owner"], operation_id=fixture["operation_id"],
                    expected_head=fixture["expected_head"],
                    expected_remote_commit=fixture["remote_commit"],
                    expected_remote_resume_sha256=fixture["remote_resume_sha256"],
                )
            self.assertEqual(
                workflow_runtime._team_local(fixture["owner"])["operations"][fixture["operation_id"]]["state"],
                "RESERVED",
            )
            self.assertEqual(len(pushes), 1)
            recovered = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
                reconcile_only=True,
            )
        self.assertEqual(recovered["status"], "CONFIRMED")
        self.assertEqual(len(pushes), 1)

    def test_bootstrap_pending_fences_checkpoint_and_unrelated_writer_before_push(self):
        fixture = self._bootstrap_publication_fixture()
        injected = False
        real_git = workflow_runtime._team_git
        current_path = fixture["owner"] / workflow_runtime.RESUME_PATH
        history_path = fixture["owner"] / workflow_runtime.RESUME_HISTORY_PATH
        local_path = fixture["owner"] / ".git" / workflow_runtime.TEAM_LOCAL

        def inject_before_push(repo, *args):
            nonlocal injected
            if args and args[0] == "merge-base" and not injected:
                local = workflow_runtime._team_local(repo)
                if local["operations"].get(fixture["operation_id"], {}).get("state") == "RESERVED":
                    injected = True
                    before = {path: path.read_bytes() for path in (current_path, history_path, local_path)}
                    candidate = repo / "pending-replay.md"
                    current_raw = current_path.read_bytes()
                    current_data, current_body = workflow_runtime._resume_document(current_raw)
                    next_data = json.loads(json.dumps(current_data))
                    next_data["revision"] += 1
                    next_data["previous_sha256"] = workflow_runtime._resume_digest(current_raw)
                    candidate.write_bytes(
                        ("---\n" + workflow_runtime.yaml.safe_dump(next_data, sort_keys=False)
                         + "---\n" + current_body).encode()
                    )
                    with self.assertRaisesRegex(
                        workflow_runtime.WorkflowRuntimeError, "TEAM_BOOTSTRAP_PENDING"
                    ):
                        workflow_runtime.resume_checkpoint(
                            repo, candidate=candidate,
                            expected_sha256=workflow_runtime._resume_digest(current_raw),
                        )
                    self.assertEqual(
                        workflow_runtime._team_local(repo)["operations"][fixture["operation_id"]]["state"],
                        "RESERVED",
                    )
                    with self.assertRaisesRegex(
                        workflow_runtime.WorkflowRuntimeError, "TEAM_BOOTSTRAP_PENDING"
                    ):
                        self.registered.stop()
                        try:
                            workflow_runtime.team_observe_remote(repo, operation_id="unrelated-observation")
                        finally:
                            self.registered.start()
                    self.assertEqual(
                        {path: path.read_bytes() for path in (current_path, history_path, local_path)},
                        before,
                    )
            return real_git(repo, *args)

        with mock.patch.object(workflow_runtime, "_team_git", side_effect=inject_before_push):
            result = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            )
        self.assertTrue(injected)
        self.assertEqual(result["status"], "CONFIRMED")
        replay = current_path.read_bytes()
        replay_data, replay_body = workflow_runtime._resume_document(replay)
        replay_candidate_data = json.loads(json.dumps(replay_data))
        replay_candidate_data["revision"] += 1
        replay_candidate_data["previous_sha256"] = workflow_runtime._resume_digest(replay)
        candidate = fixture["owner"] / "post-confirm-replay.md"
        candidate.write_bytes(
            ("---\n" + workflow_runtime.yaml.safe_dump(replay_candidate_data, sort_keys=False)
             + "---\n" + replay_body).encode()
        )
        self.assertEqual(
            workflow_runtime.resume_checkpoint(
                fixture["owner"], candidate=candidate,
                expected_sha256=workflow_runtime._resume_digest(replay), dry_run=True,
            )["status"],
            "DRY_RUN",
        )

    def test_bootstrap_intermediate_ancestor_fast_forward_is_confirmed(self):
        fixture = self._bootstrap_publication_fixture()
        pushes = []
        moved = False
        real_git = workflow_runtime._team_git

        def move_then_push(repo, *args):
            nonlocal moved
            if args and args[0] == "push":
                pushes.append(args)
                if not moved:
                    moved = True
                    subprocess.run(
                        ["git", "push", "-q", "origin",
                         fixture["local_install_commit"] + ":refs/heads/rh_clean"],
                        cwd=fixture["owner"], check=True,
                    )
            return real_git(repo, *args)

        with mock.patch.object(workflow_runtime, "_team_git", side_effect=move_then_push):
            result = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            )
        self.assertTrue(moved)
        self.assertEqual(result["status"], "CONFIRMED")
        self.assertEqual(len(pushes), 1)
        self.assertEqual(
            workflow_runtime._team_git(fixture["owner"], "ls-remote", "origin",
                                        "refs/heads/rh_clean").decode().split()[0],
            fixture["expected_head"],
        )

    def _bootstrap_remote_change(self, fixture, *, foreign_owner=False, foreign_path=False):
        intruder = fixture["root"] / (
            "intruder-owner" if foreign_owner else "intruder-foreign"
        )
        subprocess.run(
            ["git", "clone", "-q", "--branch", "rh_clean",
             str(fixture["remote"]), str(intruder)], check=True
        )
        changed_resume = intruder / workflow_runtime.RESUME_PATH
        if foreign_owner:
            raw = changed_resume.read_bytes()
            changed_resume.write_bytes(
                raw.replace(fixture["owner_id"].encode(), b"11111111-1111-4111-8111-111111111111", 1)
            )
        if foreign_path:
            (intruder / "docs/unreviewed-foreign.txt").write_bytes(b"unreviewed remote change\n")
        env = {
            **workflow_runtime.os.environ,
            "GIT_AUTHOR_NAME": "Intruder",
            "GIT_COMMITTER_NAME": "Intruder",
            "GIT_AUTHOR_EMAIL": "intruder@example.invalid",
            "GIT_COMMITTER_EMAIL": "intruder@example.invalid",
        }
        subprocess.run(["git", "add", "."], cwd=intruder, env=env, check=True)
        subprocess.run(["git", "commit", "-qm", "Uncooperative remote change"], cwd=intruder, env=env, check=True)
        subprocess.run(
            ["git", "push", "-q", "origin", "HEAD:refs/heads/rh_clean"],
            cwd=intruder, env=env, check=True,
        )
        changed_commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=intruder, text=True
        ).strip()
        return changed_commit, changed_resume.read_bytes()

    def test_bootstrap_reconcile_only_without_saved_reservation_does_not_write(self):
        fixture = self._bootstrap_publication_fixture()
        before = (fixture["owner"] / ".git" / workflow_runtime.TEAM_LOCAL).exists()
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError, "TEAM_BOOTSTRAP_ORIGINAL_RESERVATION_REQUIRED"
        ):
            workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"], reconcile_only=True
            )
        self.assertEqual(
            (fixture["owner"] / ".git" / workflow_runtime.TEAM_LOCAL).exists(), before
        )

    def test_bootstrap_rejects_foreign_owner_and_changed_remote_pins_before_reservation(self):
        fixture = self._bootstrap_publication_fixture()
        with mock.patch.dict(workflow_runtime.os.environ, {"CODEX_THREAD_ID": "foreign-task"}):
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError, "TEAM_OBSERVER_ONLY"
            ):
                workflow_runtime.team_bootstrap_publish(
                    fixture["owner"], operation_id=fixture["operation_id"],
                    expected_head=fixture["expected_head"],
                    expected_remote_commit=fixture["remote_commit"],
                    expected_remote_resume_sha256=fixture["remote_resume_sha256"],
                )
        changed_commit, changed_raw = self._bootstrap_remote_change(fixture, foreign_owner=True)
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError, "TEAM_BOOTSTRAP_REMOTE_OWNER_OR_PINS_CHANGED"
        ):
            workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=changed_commit,
                expected_remote_resume_sha256=workflow_runtime._resume_digest(changed_raw),
            )
        self.assertNotIn(
            fixture["operation_id"], workflow_runtime._team_local(fixture["owner"])["operations"]
        )

    def test_bootstrap_rejects_v2_remote_and_local_candidate_drift(self):
        fixture = self._bootstrap_publication_fixture()
        subprocess.run(
            ["git", "push", "-q", "origin", fixture["expected_head"] + ":refs/heads/rh_clean"],
            cwd=fixture["owner"], check=True,
        )
        candidate_raw = (fixture["owner"] / workflow_runtime.RESUME_PATH).read_bytes()
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError, "TEAM_BOOTSTRAP_REMOTE_OWNER_OR_PINS_CHANGED"
        ):
            workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["expected_head"],
                expected_remote_resume_sha256=workflow_runtime._resume_digest(candidate_raw),
            )

        fixture = self._bootstrap_publication_fixture()
        changed_input = fixture["owner"] / "docs/bootstrap-input.txt"
        changed_input.write_bytes(b"candidate drift\n")
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError, "TEAM_SOURCE_CHANGED:docs/bootstrap-input.txt"
        ):
            workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            )
        self.assertNotIn(
            fixture["operation_id"], workflow_runtime._team_local(fixture["owner"])["operations"]
        )

    def test_bootstrap_push_remote_nonancestor_returns_unknown_without_retry(self):
        fixture = self._bootstrap_publication_fixture()
        intruder = fixture["root"] / "intruder-nonancestor"
        subprocess.run(
            ["git", "clone", "-q", "--branch", "rh_clean",
             str(fixture["remote"]), str(intruder)], check=True
        )
        (intruder / "docs/unreviewed-foreign.txt").write_bytes(b"divergent tip\n")
        env = {
            **workflow_runtime.os.environ,
            "GIT_AUTHOR_NAME": "Intruder",
            "GIT_COMMITTER_NAME": "Intruder",
            "GIT_AUTHOR_EMAIL": "intruder@example.invalid",
            "GIT_COMMITTER_EMAIL": "intruder@example.invalid",
        }
        subprocess.run(["git", "add", "."], cwd=intruder, env=env, check=True)
        subprocess.run(["git", "commit", "-qm", "Divergent remote tip"], cwd=intruder, env=env, check=True)
        divergent = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=intruder, text=True).strip()
        subprocess.run(
            ["git", "push", "-q", "origin", "HEAD:refs/heads/test-divergent"],
            cwd=intruder, env=env, check=True,
        )
        pushes = []
        real_git = workflow_runtime._team_git
        moved = False

        def move_remote_then_push(repo, *args):
            nonlocal moved
            if args and args[0] == "push" and not moved:
                moved = True
                subprocess.run(
                    ["git", "--git-dir", str(fixture["remote"]), "update-ref",
                     "refs/heads/rh_clean", divergent, fixture["remote_commit"]], check=True,
                )
                pushes.append(args)
            return real_git(repo, *args)

        with mock.patch.object(workflow_runtime, "_team_git", side_effect=move_remote_then_push):
            result = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=fixture["expected_head"],
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            )
            retry = workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"], reconcile_only=True
            )
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertEqual(retry["status"], "UNKNOWN")
        self.assertEqual(len(pushes), 1)
        self.assertEqual(
            workflow_runtime._team_git(fixture["owner"], "ls-remote", "origin",
                                        "refs/heads/rh_clean").decode().split()[0],
            divergent,
        )

    def test_bootstrap_rejects_non_descendant_candidate_before_push(self):
        fixture = self._bootstrap_publication_fixture()
        tree = subprocess.check_output(
            ["git", "rev-parse", fixture["expected_head"] + "^{tree}"],
            cwd=fixture["owner"], text=True,
        ).strip()
        env = {
            **workflow_runtime.os.environ,
            "GIT_AUTHOR_NAME": "Fixture",
            "GIT_COMMITTER_NAME": "Fixture",
            "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
            "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
        }
        non_descendant = subprocess.check_output(
            ["git", "commit-tree", tree], cwd=fixture["owner"], env=env,
            input=b"non-descendant candidate\n", stderr=subprocess.PIPE,
        ).decode().strip()
        subprocess.run(["git", "reset", "--hard", non_descendant], cwd=fixture["owner"], check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError, "TEAM_GIT_OBSERVATION_FAILED:merge-base"
        ):
            workflow_runtime.team_bootstrap_publish(
                fixture["owner"], operation_id=fixture["operation_id"],
                expected_head=non_descendant,
                expected_remote_commit=fixture["remote_commit"],
                expected_remote_resume_sha256=fixture["remote_resume_sha256"],
            )
        self.assertNotIn(
            fixture["operation_id"], workflow_runtime._team_local(fixture["owner"])["operations"]
        )

    def test_v1_continuation_reports_migration_without_v2_ownership_error(self):
        """A legacy checkpoint needs migration, not an inapplicable owner lookup."""
        raw = self.fixture.document(operation={"kind": "NONE", "state": "NONE", "id": "", "evidence": []})
        data, _ = workflow_runtime._resume_document(raw)
        self.install(data)
        runtime = self.repo / "orchestrator/state/CHANNEL_RUNTIME.json"
        runtime.parent.mkdir(parents=True, exist_ok=True)
        runtime.write_text(json.dumps({"active_proshka_phase": {"phase_id": data["pins"]["phase_id"]}}))
        queue = self.repo / "docs/routeB_bus/PROSHKA_QUEUE.md"
        queue.parent.mkdir(parents=True, exist_ok=True)
        queue.write_text("## " + data["pins"]["request_id"] + "\n")
        snapshot = mock.Mock(selected_goal=data["pins"]["physical_goal"],
                             exact_source_pin=data["pins"]["source_commit"])
        before = {path: path.read_bytes() for path in self.repo.rglob("*") if path.is_file()}
        card = workflow_runtime._team_continuation(self.repo, snapshot, [])
        self.assertEqual(card["blockers"], [
            {"scope": "EXECUTION", "code": "TEAM_RESUME_MIGRATION_REQUIRED"},
        ])
        self.assertNotIn("local", card)
        self.assertIn("whole_tree", card)
        self.assertEqual(card["owner"]["task"], data["owner_thread_id"])
        self.assertEqual(before, {path: path.read_bytes() for path in self.repo.rglob("*") if path.is_file()})

    def test_legacy_v1_local_install_confirmation_precedes_fresh_v2_publish_intent(self):
        """Old-control local confirmation survives migration before publication intent."""
        fixture = ResumeCheckpointTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        repo = fixture.repo
        owner = "01a084f4-7498-7021-bac2-91d184d58dc7"

        def v1_document(revision, previous, *, kind="NONE", state="NONE", operation_id="", evidence=None):
            return fixture.document(
                revision,
                previous,
                operation={"kind": kind, "state": state, "id": operation_id, "evidence": evidence or []},
            )

        with mock.patch.object(workflow_runtime, "_team_registered"), mock.patch.dict(
            workflow_runtime.os.environ, {"CODEX_THREAD_ID": owner, "Q3_OWNER_EPOCH": "1"}
        ):
            first = v1_document(1, "ABSENT")
            self.assertEqual(fixture.save(first)["status"], "SAVED")
            first_sha = workflow_runtime._resume_digest(first)
            self.assertEqual(
                workflow_runtime._resume_document(first)[0]["operation"]["state"], "NONE"
            )

            local_install_id = "LEGACY-INITIAL-PUBLICATION:local-install"
            local_intent = v1_document(
                2, first_sha, kind="PUBLISH", state="INTENT", operation_id=local_install_id
            )
            self.assertEqual(fixture.save(local_intent, expected=first_sha)["status"], "SAVED")
            intent_sha = workflow_runtime._resume_digest(local_intent)

            runtime = repo / "orchestrator/workflow_runtime.py"
            runtime.parent.mkdir(parents=True, exist_ok=True)
            runtime.write_bytes(b"reviewed runtime subset\n")
            source = repo / "docs/source.md"
            source.write_bytes(b"exact source\n")
            env = {
                **workflow_runtime.os.environ,
                "GIT_AUTHOR_NAME": "Fixture",
                "GIT_COMMITTER_NAME": "Fixture",
                "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
                "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
            }
            subprocess.run(
                ["git", "add", "orchestrator/workflow_runtime.py", str(workflow_runtime.TOOLS), "docs/source.md"],
                cwd=repo,
                env=env,
                check=True,
            )
            subprocess.run(
                ["git", "commit", "-qm", "Install reviewed runtime subset"],
                cwd=repo,
                env=env,
                check=True,
            )
            local_commit = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True
            ).strip()
            local_confirmed = v1_document(
                3,
                intent_sha,
                kind="PUBLISH",
                state="CONFIRMED",
                operation_id=local_install_id,
                evidence=["bootstrap_local_commit:" + local_commit],
            )
            self.assertEqual(fixture.save(local_confirmed, expected=intent_sha)["status"], "SAVED")
            confirmed_sha = workflow_runtime._resume_digest(local_confirmed)

            # This is deliberately after v1 confirmation while the control still has no
            # TEAM_RUNTIME_VERSION field; the next checkpoint enables the v2 migration.
            identity = workflow_runtime.team_local_init(repo)
            source_manifest = {
                "docs/source.md": workflow_runtime._resume_digest(source.read_bytes()),
                "orchestrator/workflow_runtime.py": workflow_runtime._resume_digest(runtime.read_bytes()),
                str(workflow_runtime.TOOLS): workflow_runtime._resume_digest(
                    (repo / workflow_runtime.TOOLS).read_bytes()
                ),
            }
            request = {
                "path": "docs/request.txt",
                "commit": "a" * 40,
                "blob": "b" * 40,
                "sha256": "c" * 64,
                "boundary_id": "BOUNDARY",
                "conversation_id": "fixture-chat",
            }
            phase_key = dict(PHASE_KEY)
            request_subject = {"kind": "REQUEST", "id": "REQ-EXISTING", "sha256": request["sha256"]}
            verdict_subject = {"kind": "VERDICT", "id": "VERDICT-EXISTING", "sha256": "d" * 64}
            source_sha = workflow_runtime._resume_digest(workflow_runtime._team_json(source_manifest))
            stages = {
                name: {
                    "subject": request_subject if index < 3 else verdict_subject,
                    "state": "NOT_STARTED",
                    "evidence": {},
                    "source_sha256": source_sha,
                    "checked_by": None,
                }
                for index, name in enumerate(workflow_runtime.TEAM_STAGES)
            }
            local_inputs = {
                "orchestrator/workflow_runtime.py": source_manifest["orchestrator/workflow_runtime.py"],
                str(workflow_runtime.TOOLS): source_manifest[str(workflow_runtime.TOOLS)],
            }
            local_subject = {
                "kind": "REPAIR",
                "id": local_install_id,
                "sha256": workflow_runtime._resume_digest(workflow_runtime._team_json(local_inputs)),
            }
            migrated = {
                "schema": "q3_resume.v2",
                "revision": 4,
                "observed_at": "2026-09-11T10:00:00+02:00",
                "previous_sha256": confirmed_sha,
                "owner_thread_id": owner,
                "owner_host_id": "local",
                "reconciliation_pending": False,
                "recovery_from": None,
                "pins": {
                    "head": "a" * 40,
                    "physical_goal": "docs/goal.md",
                    "source_commit": "b" * 40,
                    "request_id": "REQ-EXISTING",
                    "phase_id": "PHASE-EXISTING",
                    "phase_key": phase_key,
                    "request": request,
                },
                "stages": stages,
                "operation": {
                    "kind": "PUBLISH",
                    "state": "CONFIRMED",
                    "id": local_install_id,
                    "evidence": ["bootstrap_local_commit:" + local_commit],
                    "subject": local_subject,
                    "command": "workflow-team-bootstrap-publish",
                    "inputs": local_inputs,
                },
                "ownership": {
                    "installation_ref": identity["installation_ref"],
                    "epoch": 1,
                    "state": "ACTIVE",
                    "transfer": None,
                },
                "source_manifest": source_manifest,
            }
            control = repo / "docs/CODEX_CONTROL.md"
            control.write_text(
                "```yaml\nCONTROL_ID: Q3_EXECUTOR_CONTROL\nCONTROL_VERSION: 10\nSTATUS: ACTIVE\n"
                "HONESTY_STATE: CHALLENGER_NOT_RH\nOWNER_ONLY_BOUNDARY: PX_RH_CLAIM\n"
                "TEAM_RUNTIME_VERSION: 1\n```\n"
            )
            migrated_raw = self.document(migrated)
            self.assertEqual(fixture.save(migrated_raw, expected=confirmed_sha)["status"], "SAVED")
            migrated_data, _ = workflow_runtime._resume_document(fixture.current.read_bytes())
            self.assertEqual(migrated_data["operation"]["id"], local_install_id)
            self.assertEqual(migrated_data["operation"]["state"], "CONFIRMED")
            self.assertEqual(
                migrated_data["operation"]["evidence"], ["bootstrap_local_commit:" + local_commit]
            )

            publication_id = "LEGACY-INITIAL-PUBLICATION"
            publication_inputs = {**local_inputs, "docs/source.md": source_manifest["docs/source.md"]}
            publication = json.loads(json.dumps(migrated_data))
            publication["revision"] = 5
            publication["previous_sha256"] = workflow_runtime._resume_digest(fixture.current.read_bytes())
            publication["operation"] = {
                "kind": "PUBLISH",
                "state": "INTENT",
                "id": publication_id,
                "evidence": [],
                "subject": {
                    "kind": "REPAIR",
                    "id": publication_id,
                    "sha256": workflow_runtime._resume_digest(workflow_runtime._team_json(publication_inputs)),
                },
                "command": "workflow-team-bootstrap-publish",
                "inputs": publication_inputs,
            }
            publication_raw = self.document(publication)
            self.assertEqual(
                fixture.save(
                    publication_raw,
                    expected=publication["previous_sha256"],
                )["status"],
                "SAVED",
            )
            final_data, _ = workflow_runtime._resume_document(fixture.current.read_bytes())
            self.assertEqual(final_data["operation"]["id"], publication_id)
            self.assertEqual(final_data["operation"]["state"], "INTENT")
            self.assertEqual(final_data["operation"]["inputs"], publication_inputs)
            records = workflow_runtime._resume_history(fixture.history.read_bytes())
            self.assertIn(("intent", 3, local_confirmed), records.values())
            self.assertIn(("intent", 4, migrated_raw), records.values())

    def test_stage_subject_and_prerequisites_prevent_false_acceptance(self):
        data = self.data()
        evidence = data["source_manifest"]
        for name in ("receipt", "independent_review", "parent_check", "acceptance"):
            data["stages"][name].update(state="DONE", evidence=evidence, checked_by="checker")
        workflow_runtime._resume_document(self.document(data))
        data["stages"]["independent_review"]["subject"]["id"] = "PRIOR-FLOW"
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "stage prerequisite"):
            workflow_runtime._resume_document(self.document(data))
        data = self.data()
        data["stages"]["delivery"].update(state="DONE", evidence=evidence, checked_by="checker")
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "stage prerequisite delivery"):
            workflow_runtime._resume_document(self.document(data))

    def test_unknown_send_cannot_be_erased_or_changed_to_new_operation(self):
        before = self.data()
        before["operation"]["state"] = "UNKNOWN"
        after = json.loads(json.dumps(before))
        after["operation"]["id"] = "another-request"
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "UNRESOLVED_OPERATION"):
            workflow_runtime._team_owner_transition(self.repo, before, after)
        after = json.loads(json.dumps(before))
        after["operation"].update(state="CONFIRMED", evidence=["docs/source.md"])
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "OPERATION_CONFIRMATION_REQUIRED"):
            workflow_runtime._team_owner_transition(self.repo, before, after)
        self.local(operations={before["operation"]["id"]: {"state": "CONFIRMED", "actor": before["owner_thread_id"], "epoch": 1}})
        workflow_runtime._team_owner_transition(self.repo, before, after)

    def test_foreign_owner_and_retired_epoch_are_rejected(self):
        data = self.data()
        self.install(data)
        with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
            with mock.patch.dict(workflow_runtime.os.environ, {"CODEX_THREAD_ID": "foreign-task"}):
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "OBSERVER_ONLY"):
                    workflow_runtime.team_guard(self.repo, command="workflow-team-record", paths=[])
            self.local(epoch_floor=2)
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "RETIRED_EPOCH"):
                workflow_runtime.team_guard(self.repo, command="workflow-team-record", paths=[])

    def test_source_drift_holds_affected_execution(self):
        data = self.data()
        self.install(data)
        self.source.write_bytes(b"changed source\n")
        with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "TEAM_SOURCE_CHANGED"):
                workflow_runtime.team_guard(self.repo, command="workflow-close-node", paths=[])

    def test_writer_inventory_is_complete_and_legacy_direct_entry_is_refused(self):
        inventory = workflow_runtime._team_writer_inventory(self.repo)
        self.assertEqual(set(inventory["fenced"]), workflow_runtime.TEAM_FENCED_CALLS)
        all_writers = set(inventory["fenced"]) | set(inventory["inherited_only"]) | set(inventory["isolated_only"])
        self.assertTrue(
            {
                "aristotle",
                "cartographer-loaders",
                "packet-ingest",
                "paper-ingest",
                "slack-manual-chat-reconciliation",
                "task-specific-generators",
                "tool-census",
            }
            <= all_writers
        )
        self.install(self.data())
        with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "UNFENCED_WRITER_FORBIDDEN"):
                workflow_runtime.team_guard(self.repo, command="knowledge-spine-goal-close", paths=[])
        path = self.repo / workflow_runtime.TOOLS
        text = path.read_text()
        path.write_text(text.replace("    - bind-request\n", "", 1))
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "INVENTORY_INCOMPLETE"):
            workflow_runtime._team_writer_inventory(self.repo)

    def test_confirmed_issue_holds_exact_operation_while_unrelated_work_proceeds(self):
        self.install(self.data())
        report = TeamRecordsTests.report()
        report["affected_operations"] = ["workflow-phase-close"]
        path = self.repo / workflow_runtime.TEAM_ISSUES
        raw, _ = team_records.prepare_report(path.read_bytes(), report, workflow_runtime._resume_digest(path.read_bytes()))
        for state in ("REPRODUCING", "CONFIRMED_BUG"):
            event = TeamRecordsTests.transition(team_records.read_registry(raw, "issues"), state)
            raw, _ = team_records.prepare_issue_event(raw, event, workflow_runtime._resume_digest(raw))
        path.write_bytes(raw)
        with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "DEPENDENT_OPERATION_HELD"):
                workflow_runtime.team_guard(self.repo, command="workflow-phase-close", paths=[])
            self.assertEqual(workflow_runtime.team_guard(self.repo, command="workflow-session-close", paths=[])["epoch"], 1)

    def test_close_child_keeps_writer_lock_after_parent_crash(self):
        import sys
        directory = self.repo / "specs_docs"
        directory.mkdir()
        child = directory / "session_close.py"
        child.write_text("import os, signal, sys\nos.kill(os.getppid(), signal.SIGKILL)\n"
                         "print('child owns inherited lock', flush=True)\nsys.stdin.read(1)\n")
        code = ("from pathlib import Path\nfrom orchestrator import workflow_runtime as w\n"
                "w._team_enabled=lambda repo: True\nw.team_guard=lambda *args, **kwargs: {}\n"
                f"w._run_close_script(Path({str(self.repo)!r}), 'specs_docs/session_close.py', [])\n")
        parent = subprocess.Popen([sys.executable, "-c", code], cwd=Path(__file__).resolve().parents[2],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            self.assertEqual(parent.stdout.readline().strip(), "child owns inherited lock")
            self.assertEqual(parent.wait(timeout=5), -9)
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "LOCK_COLLISION"):
                with workflow_runtime._execution_writer_epoch(self.repo):
                    pass
        finally:
            parent.stdin.write("x")
            parent.stdin.flush()
            parent.stdin.close()
            parent.stdout.read()
            parent.stdout.close()
            parent.stderr.close()
        with workflow_runtime._execution_writer_epoch(self.repo):
            pass

    def transfer(self, data, *, target_ref=None, target_thread=None, mode="SAME_INSTALLATION"):
        return {"id": "transfer-1", "mode": mode, "from_ref": data["ownership"]["installation_ref"],
                "from_thread": data["owner_thread_id"], "to_ref": target_ref or self.identity,
                "to_thread": target_thread or "01a08f80-f033-7a31-8f3a-3aef042a3fbc",
                "predecessor_commit": None, "evidence": {}}

    def watch(self, data, *, state="ACTIVE", target=None, wake=None, supported=False):
        return {"schema": "q3_team_native_observation.v1", "installation_ref": self.identity,
                "actor": data["owner_thread_id"], "epoch": data["ownership"]["epoch"],
                "transfer_id": (data["ownership"]["transfer"] or {}).get("id", "transfer-1"),
                "watch_id": "watch-existing", "target_thread": target or data["owner_thread_id"], "state": state,
                "continuation_minutes": 10, "agent_check_minutes": 20, "observed_at": "2026-09-11T12:00:00+02:00",
                "scheduled_wake_at": wake, "provider_receipt": "docs/source.md",
                "provider_receipt_sha256": workflow_runtime._resume_digest(self.source.read_bytes()),
                "retarget_supported": supported}

    def test_same_installation_transfer_rejects_unsupported_retarget_before_epoch_advance(self):
        old = self.data()
        old["operation"].update(state="CONFIRMED", evidence=["docs/source.md"])
        old["ownership"].update(state="HANDOFF_QUIESCED", transfer=self.transfer(old))
        new = json.loads(json.dumps(old))
        new["ownership"].update(state="WATCH_RECONCILE_PENDING", epoch=2)
        new["owner_thread_id"] = new["ownership"]["transfer"]["to_thread"]
        self.local(watch=self.watch(old))
        with mock.patch.object(workflow_runtime, "_team_quiescence"):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "RETARGET_UNSUPPORTED"):
                workflow_runtime._team_owner_transition(self.repo, old, new)
            self.local(watch=self.watch(old, supported=True))
            workflow_runtime._team_owner_transition(self.repo, old, new)
        self.assertEqual(old["ownership"]["epoch"], 1)

    def test_native_watch_requires_integer_ten_twenty_cadence(self):
        data = self.data()
        self.install(data)
        evidence = self.watch(data)
        self.fixture.candidate.write_bytes(workflow_runtime._team_json(evidence))
        result = workflow_runtime.team_observe_native(
            self.repo, candidate=self.fixture.candidate,
            expected_sha256=workflow_runtime._resume_digest(self.fixture.candidate.read_bytes()))
        self.assertEqual(result["status"], "OBSERVED")
        self.assertEqual(workflow_runtime._team_local(self.repo)["watch"]["continuation_minutes"], 10)
        self.assertFalse(result["scheduled_wake_observed"])
        before = workflow_runtime._team_private_read(self.repo, workflow_runtime.TEAM_LOCAL)
        for field, values in (
            ("continuation_minutes", (0, 5, True, False, 5.0, 10.0, "10", [], None)),
            ("agent_check_minutes", (0, 5, True, False, 20.0, "20", [], None)),
        ):
            for value in values:
                with self.subTest(field=field, value=value):
                    evidence = self.watch(data)
                    evidence[field] = value
                    self.fixture.candidate.write_bytes(workflow_runtime._team_json(evidence))
                    with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "TEAM_NATIVE_SCHEMA_INVALID"):
                        workflow_runtime.team_observe_native(
                            self.repo, candidate=self.fixture.candidate,
                            expected_sha256=workflow_runtime._resume_digest(self.fixture.candidate.read_bytes()))
                    self.assertEqual(workflow_runtime._team_private_read(self.repo, workflow_runtime.TEAM_LOCAL), before)

    def test_watch_intent_is_not_replayed_and_activation_requires_actual_wake(self):
        old = self.data()
        old["ownership"].update(state="WATCH_RECONCILE_PENDING", epoch=2, transfer=self.transfer(old))
        old["owner_thread_id"] = old["ownership"]["transfer"]["to_thread"]
        self.install(old)
        with mock.patch.dict(workflow_runtime.os.environ, {"CODEX_THREAD_ID": old["owner_thread_id"]}):
            self.local(watch=self.watch(old, supported=True))
            first = workflow_runtime.team_watch_intent(self.repo, action="UPDATE", transfer_id="transfer-1", target_thread=old["owner_thread_id"])
            self.assertEqual(first["status"], "RESERVED")
            second = workflow_runtime.team_watch_intent(self.repo, action="UPDATE", transfer_id="transfer-1", target_thread=old["owner_thread_id"])
            self.assertEqual(second["status"], "RECONCILE_ORIGINAL")
            new = json.loads(json.dumps(old))
            new["ownership"]["state"] = "ACTIVE"
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "WATCH_RECONCILIATION_REQUIRED"):
                workflow_runtime._team_owner_transition(self.repo, old, new)
            evidence = self.watch(old, wake="2026-09-11T12:10:00+02:00", supported=True)
            self.fixture.candidate.write_bytes(workflow_runtime._team_json(evidence))
            workflow_runtime.team_observe_native(self.repo, candidate=self.fixture.candidate,
                                                expected_sha256=workflow_runtime._resume_digest(self.fixture.candidate.read_bytes()))
            workflow_runtime._team_owner_transition(self.repo, old, new)

    def test_incomplete_source_recheck_cannot_reuse_done_stages(self):
        data = self.data()
        stage = data["stages"]["receipt"]
        stage.update(state="DONE", evidence=data["source_manifest"], checked_by="owner")
        data["source_manifest"] = {"docs/source.md": "e" * 64}
        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "stage source verification stale"):
            workflow_runtime._resume_document(self.document(data))

    def test_reservation_is_once_and_lost_confirmation_requires_inspection(self):
        data = self.data()
        raw = self.install(data)
        receipt = {"state": "OBSERVED", "checkpoint_sha256": workflow_runtime._resume_digest(raw),
                   "actor": data["owner_thread_id"], "epoch": 1, "remote_ownership": data["ownership"],
                   "remote_thread": data["owner_thread_id"], "local_head": "a" * 40}
        self.local(operations={data["operation"]["id"]: receipt})
        with mock.patch.object(workflow_runtime, "_team_git", return_value=("a" * 40).encode()):
            result = workflow_runtime.team_reserve_effect(self.repo, operation_id=data["operation"]["id"])
            self.assertEqual(result["status"], "RESERVED")
            retry = workflow_runtime.team_reserve_effect(self.repo, operation_id=data["operation"]["id"])
            self.assertEqual(retry, {"status": "RECONCILE_ORIGINAL", "operation_id": data["operation"]["id"], "execute": False})

    def test_foreign_observer_cannot_poison_remote_or_native_records(self):
        data = self.data()
        self.install(data)
        with mock.patch.dict(workflow_runtime.os.environ, {"CODEX_THREAD_ID": "foreign-task"}):
            with mock.patch.object(workflow_runtime, "_team_remote") as remote:
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "NOT_OWNER_OR_NAMED_CLAIMANT"):
                    workflow_runtime.team_observe_remote(self.repo, operation_id="existing-request")
                remote.assert_not_called()
            evidence = self.watch(data)
            evidence["actor"] = "foreign-task"
            self.fixture.candidate.write_bytes(workflow_runtime._team_json(evidence))
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "OBSERVER_ONLY"):
                workflow_runtime.team_observe_native(self.repo, candidate=self.fixture.candidate,
                    expected_sha256=workflow_runtime._resume_digest(self.fixture.candidate.read_bytes()))
        self.assertIsNone(workflow_runtime._team_private_read(self.repo, workflow_runtime.TEAM_LOCAL))

    def test_archive_writer_crash_boundaries_and_original_report_replay(self):
        self.install(self.data())
        (self.repo / "docs/session_protocols").mkdir()
        raw, original = team_records.prepare_report(b"# preserved legacy\n", TeamRecordsTests.report(),
            workflow_runtime._resume_digest(b"# preserved legacy\n"))
        issue_path = self.repo / workflow_runtime.TEAM_ISSUES
        expected = workflow_runtime._resume_digest(raw)
        for failure in range(1, 5):
            with self.subTest(after_durable_step=failure):
                issue_path.write_bytes(raw)
                request = {"schema": "q3_team_archive_request.v1", "registry_kind": "issues", "event_count": 1,
                           "expected_registry_sha256": expected,
                           "archive_ref": f"docs/session_protocols/team-archive-fixture-{failure}.json"}
                self.fixture.candidate.write_bytes(team_records.canonical_json(request))
                real, count = workflow_runtime._resume_cas_bytes, 0
                def interrupted(*args):
                    nonlocal count
                    real(*args)
                    count += 1
                    if count == failure:
                        raise RuntimeError("fixture interruption")
                with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
                    with mock.patch.object(workflow_runtime, "_resume_cas_bytes", side_effect=interrupted):
                        with self.assertRaisesRegex(RuntimeError, "fixture interruption"):
                            workflow_runtime.team_record(self.repo, kind="archive", candidate=self.fixture.candidate,
                                expected_sha256=expected)
                    result = workflow_runtime.team_record(self.repo, kind="archive", candidate=self.fixture.candidate,
                        expected_sha256=expected)
                    final_receipt = (self.repo / result["receipt_path"]).read_bytes()
                    retry = workflow_runtime.team_record(self.repo, kind="archive", candidate=self.fixture.candidate,
                        expected_sha256=expected)
                self.assertEqual(retry["status"], "NOOP")
                self.assertEqual((self.repo / result["receipt_path"]).read_bytes(), final_receipt)
                loader = lambda path: (self.repo / path).read_bytes()
                unchanged, replay = team_records.prepare_report(issue_path.read_bytes(), TeamRecordsTests.report(),
                    "0" * 64, archive_loader=loader)
                self.assertEqual(unchanged, issue_path.read_bytes())
                self.assertEqual(replay["receipt_sha256"], original["receipt_sha256"])
                self.assertTrue(unchanged.startswith(b"# preserved legacy\n"))

    def test_typed_cross_clone_release_claim_wake_and_old_owner_rejection(self):
        self._cross_clone_transfer_scenario(abort_claim=False)

    def test_cross_clone_claim_abort_after_watch_creation_and_fresh_reclaim(self):
        self._cross_clone_transfer_scenario(abort_claim=True)

    def _cross_clone_transfer_scenario(self, *, abort_claim):
        """Real Git transport plus every typed checkpoint phase; no remote/wake success stub."""
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            remote, home = root / "remote.git", root / "home"
            env = {**workflow_runtime.os.environ, "GIT_AUTHOR_NAME": "Fixture", "GIT_COMMITTER_NAME": "Fixture",
                   "GIT_AUTHOR_EMAIL": "fixture@example.invalid", "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
            def git(repo, *args):
                return subprocess.run(["git", *args], cwd=repo, env=env, capture_output=True, check=True).stdout.decode().strip()
            def save(repo, data):
                previous = (repo / workflow_runtime.RESUME_PATH).read_bytes()
                before, _ = workflow_runtime._resume_document(previous)
                data.update(revision=before["revision"] + 1, previous_sha256=workflow_runtime._resume_digest(previous))
                path = repo / "candidate.md"
                path.write_bytes(self.document(data))
                return workflow_runtime.resume_checkpoint(repo, candidate=path, expected_sha256=data["previous_sha256"])
            def publish(repo, message):
                git(repo, "add", "docs")
                git(repo, "commit", "-qm", message)
                git(repo, "push", "origin", "HEAD:refs/heads/rh_clean")
                return git(repo, "rev-parse", "HEAD")
            def observe_watch(repo, data, state, wake=None):
                observed = self.watch(data, state=state, wake=wake)
                observed["installation_ref"] = data["ownership"]["installation_ref"]
                observed["watch_id"] = None if state == "ABSENT" else "watch-home" if repo == home else "watch-existing"
                path = repo / "native.json"
                path.write_bytes(workflow_runtime._team_json(observed))
                workflow_runtime.team_observe_native(repo, candidate=path,
                    expected_sha256=workflow_runtime._resume_digest(path.read_bytes()))

            git(root, "init", "--bare", "-q", str(remote))
            git(self.repo, "remote", "add", "origin", str(remote))
            data = self.data()
            data["operation"].update(state="CONFIRMED", evidence=["docs/source.md"])
            self.install(data)
            publish(self.repo, "Fixture initial checkpoint")
            git(root, "clone", "-q", "--branch", "rh_clean", str(remote), str(home))
            home_ref = workflow_runtime.team_local_init(home)["installation_ref"]
            home_thread = "01a08f80-f033-7a31-8f3a-3aef042a3fbc"
            transfer = self.transfer(data, target_ref=home_ref, target_thread=home_thread, mode="CROSS_INSTALLATION")
            data["ownership"].update(state="HANDOFF_INTENT", transfer=transfer)
            save(self.repo, data)
            observe_watch(self.repo, data, "ACTIVE")
            workflow_runtime.team_watch_intent(self.repo, action="PAUSE", transfer_id="transfer-1", target_thread=data["owner_thread_id"])
            observe_watch(self.repo, data, "PAUSED")
            evidence = {"schema": "q3_team_quiescence.v1", "transfer_id": "transfer-1", "epoch": 1,
                        "source_manifest": data["source_manifest"], "head": git(self.repo, "rev-parse", "HEAD"),
                        "dirty_paths": {}, "canonical_writers_idle": True, "unknown_operations": [],
                        "assignments": [], "outputs": {}, "provider_receipt": data["source_manifest"]}
            path = self.repo / "docs/quiescence.json"
            path.write_bytes(workflow_runtime._team_json(evidence))
            data["ownership"]["transfer"]["evidence"] = {"docs/quiescence.json": workflow_runtime._resume_digest(path.read_bytes())}
            data["ownership"]["state"] = "HANDOFF_QUIESCED"
            save(self.repo, data)
            data["ownership"]["state"] = "RELEASED"
            save(self.repo, data)
            release = publish(self.repo, "Fixture released to home")
            git(home, "pull", "--ff-only", "origin", "rh_clean")
            self.assertFalse((home / ".git" / workflow_runtime.TEAM_LOCAL).exists())
            with mock.patch.dict(workflow_runtime.os.environ, {"CODEX_THREAD_ID": home_thread, "Q3_OWNER_EPOCH": "2"}):
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "NOT_OWNER_OR_NAMED_CLAIMANT"):
                    workflow_runtime.team_observe_remote(home, operation_id="wrong-transfer:release")
                workflow_runtime.team_observe_remote(home, operation_id="transfer-1:release")
                claim = json.loads(json.dumps(data))
                claim.update(owner_thread_id=home_thread)
                claim["ownership"].update(state="CLAIM_PENDING", epoch=2, installation_ref=home_ref)
                claim["ownership"]["transfer"]["predecessor_commit"] = release
                save(home, claim)
                with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
                    with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "RECONCILIATION_REQUIRED"):
                        workflow_runtime.team_guard(home, command="workflow-team-record", paths=[])
                claim_commit = publish(home, "Fixture pending home claim")
                # Losing a push receipt is reconciled against the same published claim.
                workflow_runtime.team_observe_remote(home, operation_id="transfer-1:claim")
                retry = workflow_runtime.team_observe_remote(home, operation_id="transfer-1:claim")
                self.assertEqual(retry["status"], "NOOP")
                observe_watch(home, claim, "ABSENT")
                workflow_runtime.team_watch_intent(home, action="CREATE", transfer_id="transfer-1", target_thread=home_thread)
                self.assertEqual(workflow_runtime.team_watch_intent(home, action="CREATE", transfer_id="transfer-1",
                    target_thread=home_thread)["status"], "RECONCILE_ORIGINAL")
                active = json.loads(json.dumps(claim))
                active["ownership"]["state"] = "ACTIVE"
                observe_watch(home, claim, "ACTIVE")
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "WATCH_RECONCILIATION_REQUIRED"):
                    save(home, active)
                if abort_claim:
                    # A created watch may need pausing before its first wake. This is
                    # a distinct effect; retrying CREATE must still never execute twice.
                    pause = workflow_runtime.team_watch_intent(home, action="PAUSE",
                        transfer_id="transfer-1", target_thread=home_thread)
                    self.assertEqual(pause["status"], "RESERVED")
                    self.assertEqual(workflow_runtime.team_watch_intent(home, action="CREATE",
                        transfer_id="transfer-1", target_thread=home_thread)["status"], "RECONCILE_ORIGINAL")
                    observe_watch(home, claim, "PAUSED")
                    aborted = json.loads(json.dumps(claim))
                    aborted["ownership"].update(state="CLAIM_ABORTED", transfer={
                        **self.transfer(claim, target_ref=self.identity,
                            target_thread=data["owner_thread_id"], mode="CROSS_INSTALLATION"),
                        "id": "transfer-2", "predecessor_commit": claim_commit})
                    save(home, aborted)
                    aborted_commit = publish(home, "Fixture verified home claim abort")
                    workflow_runtime.team_observe_remote(home, operation_id="transfer-2:aborted")
                    self.assertEqual(workflow_runtime.team_observe_remote(home,
                        operation_id="transfer-2:aborted")["status"], "NOOP")
                    self.assertEqual(aborted["ownership"]["epoch"], 2)
                    with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
                        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "RECONCILIATION_REQUIRED"):
                            workflow_runtime.team_guard(home, command="workflow-team-record", paths=[])
                else:
                    # This is a simulated provider observation, not live-app acceptance.
                    observe_watch(home, claim, "ACTIVE", wake="2026-09-11T12:10:00+02:00")
                    save(home, active)
                    active_commit = publish(home, "Fixture home active after provider wake")
                    with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
                        self.assertEqual(workflow_runtime.team_guard(home, command="workflow-team-record", paths=[])["epoch"], 2)
                        with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "CALLER_EPOCH_CHANGED"):
                            workflow_runtime.team_guard(home, command="workflow-team-record", paths=[], expected_epoch=1)
            git(self.repo, "fetch", "origin", "rh_clean")
            git(self.repo, "merge", "--ff-only", "FETCH_HEAD")
            if abort_claim:
                with mock.patch.dict(workflow_runtime.os.environ, {"Q3_OWNER_EPOCH": "3"}):
                    workflow_runtime.team_observe_remote(self.repo, operation_id="transfer-2:release")
                    reclaimed = json.loads(json.dumps(aborted))
                    reclaimed["owner_thread_id"] = data["owner_thread_id"]
                    reclaimed["ownership"].update(state="CLAIM_PENDING", epoch=3, installation_ref=self.identity)
                    reclaimed["ownership"]["transfer"]["predecessor_commit"] = aborted_commit
                    save(self.repo, reclaimed)
                    publish(self.repo, "Fixture new epoch claim after verified abort")
                    workflow_runtime.team_observe_remote(self.repo, operation_id="transfer-2:claim")
                    observe_watch(self.repo, reclaimed, "PAUSED")
                    workflow_runtime.team_watch_intent(self.repo, action="UPDATE",
                        transfer_id="transfer-2", target_thread=reclaimed["owner_thread_id"])
                    observe_watch(self.repo, reclaimed, "ACTIVE", wake="2026-09-11T12:20:00+02:00")
                    reclaimed["ownership"]["state"] = "ACTIVE"
                    save(self.repo, reclaimed)
                    publish(self.repo, "Fixture reclaimed after scheduled wake")
                    with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
                        self.assertEqual(workflow_runtime.team_guard(self.repo,
                            command="workflow-team-record", paths=[])["epoch"], 3)
                return
            with mock.patch.object(workflow_runtime, "_team_enabled", return_value=True):
                with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "OBSERVER_ONLY"):
                    workflow_runtime.team_guard(self.repo, command="workflow-team-record", paths=[])
            self.assertEqual(git(self.repo, "rev-parse", "HEAD"), active_commit)

    def test_two_independent_clones_never_share_identity_and_only_one_claim_pushes(self):
        # Actual git remote/clone/fast-forward behavior, not a mocked push result.
        import os
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            remote, home, rival = root / "remote.git", root / "home", root / "rival"
            env = {**os.environ, "GIT_AUTHOR_NAME": "Fixture", "GIT_COMMITTER_NAME": "Fixture",
                   "GIT_AUTHOR_EMAIL": "fixture@example.invalid", "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
            def git(repo, *args, check=True):
                return subprocess.run(["git", *args], cwd=repo, env=env, capture_output=True, check=check)
            git(root, "init", "--bare", "-q", str(remote))
            self.install(self.data())
            git(self.repo, "add", "docs")
            git(self.repo, "commit", "-qm", "Fixture release")
            git(self.repo, "push", str(remote), "HEAD:refs/heads/rh_clean")
            for clone in (home, rival):
                git(root, "clone", "-q", "--branch", "rh_clean", str(remote), str(clone))
            home_id = workflow_runtime.team_local_init(home)["installation_ref"]
            rival_id = workflow_runtime.team_local_init(rival)["installation_ref"]
            self.assertEqual(len({self.identity, home_id, rival_id}), 3)
            self.assertFalse((home / ".git" / workflow_runtime.TEAM_LOCAL).exists())
            for clone in (home, rival):
                (clone / "docs/claim.txt").write_text(clone.name)
                git(clone, "add", "docs/claim.txt")
                git(clone, "commit", "-qm", "Fixture claim")
            self.assertEqual(git(home, "push", "origin", "HEAD:refs/heads/rh_clean").returncode, 0)
            self.assertNotEqual(git(rival, "push", "origin", "HEAD:refs/heads/rh_clean", check=False).returncode, 0)
            remote_head = git(home, "ls-remote", "origin", "refs/heads/rh_clean").stdout.split()[0]
            self.assertEqual(remote_head, git(home, "rev-parse", "HEAD").stdout.strip())
            self.assertNotEqual(remote_head, git(rival, "rev-parse", "HEAD").stdout.strip())

    def test_repair_source_set_rejects_extra_locator(self):
        expected = {"docs/input.md": "a" * 64}
        rows = [
            {"locator": "docs/input.md", "sha256": "a" * 64},
            {"locator": "git:" + "b" * 40 + ":docs/old.md", "sha256": "b" * 64},
        ]
        with self.assertRaisesRegex(
            workflow_runtime.WorkflowRuntimeError, "TEAM_ISSUE_RESULT_SOURCE_MISMATCH"
        ):
            workflow_runtime._team_validate_repair_source_set(rows, expected)

    def test_named_repair_commit_verifies_descendant_bytes_and_rejects_old_reachable_commit(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            env = {
                **workflow_runtime.os.environ,
                "GIT_AUTHOR_NAME": "Fixture",
                "GIT_COMMITTER_NAME": "Fixture",
                "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
                "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
            }

            def git(*args: str) -> str:
                return subprocess.run(
                    ["git", *args], cwd=repo, env=env, capture_output=True, check=True
                ).stdout.decode().strip()

            git("init", "-q")
            (repo / "repair.txt").write_text("base\n")
            git("add", "repair.txt")
            git("commit", "-qm", "base")
            base = git("rev-parse", "HEAD")
            (repo / "repair.txt").write_text("old reachable\n")
            git("commit", "-qam", "old reachable")
            old = git("rev-parse", "HEAD")
            (repo / "repair.txt").write_text("verified candidate\n")
            git("commit", "-qam", "verified candidate")
            candidate = git("rev-parse", "HEAD")
            expected = hashlib.sha256(b"verified candidate\n").hexdigest()
            payload = {
                "candidate_commit": candidate,
                "candidate_manifest": [{"path": "repair.txt", "sha256": expected}],
            }
            self.assertEqual(
                workflow_runtime._team_validate_repair_candidate(
                    repo, payload, base_commit=base
                ),
                {"repair.txt": expected},
            )
            payload["candidate_commit"] = old
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError,
                "TEAM_REPAIR_CANDIDATE_BYTES_MISMATCH",
            ):
                workflow_runtime._team_validate_repair_candidate(
                    repo, payload, base_commit=base
                )

    def test_reviewed_local_bytes_commit_excludes_foreign_paths(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            env = {
                **workflow_runtime.os.environ,
                "GIT_AUTHOR_NAME": "Fixture",
                "GIT_COMMITTER_NAME": "Fixture",
                "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
                "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
            }

            def git(*args: str) -> str:
                return subprocess.run(
                    ["git", *args], cwd=repo, env=env, capture_output=True, check=True
                ).stdout.decode().strip()

            git("init", "-q")
            (repo / "repair.txt").write_text("base\n")
            (repo / "foreign.txt").write_text("foreign base\n")
            git("add", ".")
            git("commit", "-qm", "base")
            base = git("rev-parse", "HEAD")

            reviewed_bytes = b"reviewed local bytes\n"
            (repo / "repair.txt").write_bytes(reviewed_bytes)
            digest = hashlib.sha256(reviewed_bytes).hexdigest()
            manifest = [{"path": "repair.txt", "sha256": digest}]

            assignment = TeamRecordsTests.provenance_assignment(role="independent-checker")
            assignment.update(base_commit=base, permitted_paths=["repair.txt"])
            assignment_legacy = b"legacy assignments\n"
            assignment_raw, _ = team_records.prepare_assignment(
                assignment_legacy, assignment, hashlib.sha256(assignment_legacy).hexdigest()
            )
            assignments = team_records.read_registry(assignment_raw, "assignments")
            report = TeamRecordsTests.report()
            report["base_commit"] = base
            issue_legacy = b"legacy issues\n"
            issue_raw, _ = team_records.prepare_report(
                issue_legacy, report, hashlib.sha256(issue_legacy).hexdigest()
            )
            issues = team_records.read_registry(issue_raw, "issues")
            issue = next(iter(issues["issues"].values()))
            review = TeamRecordsTests.repair_review_artifact(issue, manifest)
            context = TeamRecordsTests.provenance_context(
                assignment, report=report, review_artifact=review
            )
            result_observation = context.observations[assignment["assignment_id"]][1]
            event = TeamRecordsTests.transition(
                issues,
                "FIX_VERIFIED",
                actor="reporter-task",
                actor_role="independent-checker",
                verifier_id="reporter-task",
                evidence=[
                    {
                        "locator": result_observation["output_locator"],
                        "sha256": result_observation["output_sha256"],
                    }
                ],
                candidate_manifest=manifest,
            )
            team_records.validate_issue_event_actor(
                event, assignments, context, expected_base_commit=base
            )

            # The reviewed bytes are committed after review.  An unrelated
            # foreign edit remains dirty and is excluded from this commit.
            git("add", "repair.txt")
            git("commit", "-qm", "named repair")
            candidate = git("rev-parse", "HEAD")
            (repo / "foreign.txt").write_text("foreign dirty edit\n")
            self.assertEqual(
                workflow_runtime._team_validate_repair_candidate(
                    repo,
                    {"candidate_commit": candidate, "candidate_manifest": manifest},
                    base_commit=base,
                ),
                {"repair.txt": digest},
            )
            self.assertEqual((repo / "foreign.txt").read_text(), "foreign dirty edit\n")
            self.assertIn("M foreign.txt", git("status", "--porcelain"))

            # A named candidate commit that also includes the foreign path is
            # rejected before commit acceptance; no branch merge/push occurs.
            second_bytes = b"second repair bytes\n"
            (repo / "repair.txt").write_bytes(second_bytes)
            (repo / "foreign.txt").write_text("foreign committed edit\n")
            git("add", ".")
            git("commit", "-qm", "repair plus foreign")
            second = git("rev-parse", "HEAD")
            second_manifest = [{
                "path": "repair.txt",
                "sha256": hashlib.sha256(second_bytes).hexdigest(),
            }]
            with self.assertRaisesRegex(
                workflow_runtime.WorkflowRuntimeError, "TEAM_REPAIR_CANDIDATE_DIFF_MISMATCH"
            ):
                workflow_runtime._team_validate_repair_candidate(
                    repo,
                    {"candidate_commit": second, "candidate_manifest": second_manifest},
                    base_commit=base,
                )


class TeamRecordsTests(unittest.TestCase):
    """Focused tests for pure issue/assignment framing and lifecycle helpers."""

    SHA = "a" * 64

    @classmethod
    def report(cls, number: int = 1, *, attempt: str | None = None, actual: str = "observed") -> dict[str, object]:
        return {
            "schema": team_records.ISSUE_REPORT_SCHEMA,
            "reporter_task": "reporter-task",
            "reporter_host": "linux-installation",
            "assignment_id": f"assignment-{number}",
            "attempt_id": attempt or f"attempt-{number}",
            "observed_at": "2026-09-11T12:00:00+02:00",
            "subject_id": f"subject-{number}",
            "subject_type": "code-defect",
            "base_commit": cls.SHA,
            "input_paths": [{"path": "orchestrator/workflow_runtime.py", "sha256": cls.SHA}],
            "severity": "MEDIUM",
            "suspected_class": "CODE_DEFECT",
            "expected_behavior": "The registered route preserves the exact predecessor.",
            "expected_rule_source": {"locator": "docs/Codex/TEAM_RUNTIME_REFACTOR_PLAN_2026-09-11.md", "sha256": cls.SHA},
            "actual_behavior": actual,
            "reproduction": "Call the pure preparation helper twice with the same preimage.",
            "affected_operations": ["issue-intake", "repair-acceptance"],
            "evidence": [{"locator": "evidence/reproduction.txt", "sha256": cls.SHA}],
            "uncertainty": "The source fixture is synthetic.",
        }

    @classmethod
    def transition(
        cls,
        registry: dict[str, object],
        transition: str,
        *,
        actor: str = "independent-checker",
        source: str = "docs/Codex/TEAM_RUNTIME_REFACTOR_PLAN_2026-09-11.md",
        **extra: object,
    ) -> dict[str, object]:
        issue = next(iter(registry["issues"].values()))
        payload: dict[str, object] = {
            "schema": team_records.ISSUE_TRANSITION_SCHEMA,
            "issue_id": issue["issue_id"],
            "report_id": issue["report_id"],
            "transition": transition,
            "actor_id": actor,
            "actor_role": "independent-checker",
            "evidence": [{"locator": "evidence/check.txt", "sha256": cls.SHA}],
            "source_binding": [{"locator": source, "sha256": cls.SHA}],
            "reason": f"Evidence supports {transition}.",
            "previous_event_sha256": issue["last_event_sha256"],
            "previous_state_sha256": team_records._state_sha(issue),
        }
        if transition in team_records.REPAIR_STATES:
            payload.update({"repair_subject_type": "repository-repair", "repair_subject_id": "repair-1"})
        if transition in {"FIX_VERIFIED", "FIX_COMMITTED", "FIX_PUSH_VERIFIED"}:
            payload["candidate_manifest"] = [{"path": "orchestrator/team_records.py", "sha256": cls.SHA}]
        if transition in {"FIX_COMMITTED", "FIX_PUSH_VERIFIED"}:
            payload["candidate_commit"] = cls.SHA
        payload.update(extra)
        return payload

    @classmethod
    def assignment(
        cls,
        *,
        assignment_id: str = "assignment-team-records",
        operation: str = "CREATE",
        previous: str = "ABSENT",
    ) -> dict[str, object]:
        return {
            "schema": team_records.ASSIGNMENT_SCHEMA,
            "assignment_id": assignment_id,
            "operation": operation,
            "owner_task": "owner-task",
            "owner_host": "linux-installation",
            "owner_installation_ref": cls.SHA,
            "owner_epoch": 4,
            "assignee": "worker-task",
            "requested_model": "gpt-5.6-luna",
            "requested_effort": "high",
            "resolved_model": "gpt-5.6-luna",
            "resolved_effort": "high",
            "role": "implementation",
            "subject": "team records candidate",
            "base_commit": cls.SHA,
            "input_hashes": [{"path": "docs/Codex/TEAM_RUNTIME_REFACTOR_PLAN_2026-09-11.md", "sha256": cls.SHA}],
            "permitted_paths": ["orchestrator/team_records.py"],
            "output_locator": "candidate/orchestrator/team_records.py",
            "prerequisites": ["source-review"],
            "stopping_condition": "Focused tests pass.",
            "expected_duration_seconds": 900,
            "next_check": "2026-09-11T12:15:00+02:00",
            "status": "ASSIGNED",
            "previous_assignment_event_sha256": "ABSENT",
            "previous_assignment_sha256": previous,
        }

    @classmethod
    def provenance_assignment(cls, *, role: str = "independent-checker") -> dict[str, object]:
        assignment = cls.assignment(assignment_id="assignment-1")
        assignment["assignee"] = "reporter-task"
        assignment["role"] = role
        return assignment

    @classmethod
    def provenance_context(
        cls,
        assignment: dict[str, object],
        *,
        report: dict[str, object] | None = None,
        result_state: str = "COMPLETED",
        actor_id: str = "owner-actor",
        review_artifact: bytes | None = None,
    ) -> team_records.TrustedTeamContext:
        source_sha = hashlib.sha256(team_records.canonical_json(assignment["input_hashes"])).hexdigest()
        payload_sha = team_records._assignment_binding_sha(assignment)
        report_output = team_records.canonical_json(report or cls.report())
        report_output_sha = hashlib.sha256(report_output).hexdigest()
        observations: list[dict[str, object]] = []
        output_artifacts: dict[str, bytes] = {}
        for phase, state in (("LAUNCH", "RUNNING"), ("RESULT", result_state)):
            output = None if phase == "LAUNCH" else review_artifact if review_artifact is not None else report_output
            output_sha = cls.SHA if output is None else hashlib.sha256(output).hexdigest()
            evidence = [
                {"locator": f"evidence/{phase.lower()}.out", "sha256": output_sha},
                {"locator": f"provider/{phase.lower()}.json", "sha256": cls.SHA},
            ]
            observations.append(
                {
                    "schema": team_records.NATIVE_OBSERVATION_SCHEMA,
                    "assignment_id": assignment["assignment_id"],
                    "phase": phase,
                    "operation_id": f"native-{phase.lower()}",
                    "owner_task": assignment["owner_task"],
                    "owner_installation_ref": assignment["owner_installation_ref"],
                    "owner_epoch": assignment["owner_epoch"],
                    "assignee": assignment["assignee"],
                    "native_agent_id": "agent-native",
                    "native_owner_task": assignment["owner_task"],
                    "requested_model": assignment["requested_model"],
                    "requested_effort": assignment["requested_effort"],
                    "resolved_model": assignment["resolved_model"],
                    "resolved_effort": assignment["resolved_effort"],
                    "subject": assignment["subject"],
                    "state": state,
                    "output_locator": evidence[0]["locator"],
                    "output_sha256": evidence[0]["sha256"],
                    "provider_receipt_locator": evidence[1]["locator"],
                    "provider_receipt_sha256": evidence[1]["sha256"],
                    "payload_sha256": payload_sha,
                    "evidence_sha256": hashlib.sha256(team_records.canonical_json(evidence)).hexdigest(),
                    "source_sha256": source_sha,
                }
            )
            if output is not None:
                output_artifacts[f"evidence/{phase.lower()}.out"] = output

        return team_records.TrustedTeamContext(
            owner_task=assignment["owner_task"],
            owner_host=assignment["owner_host"],
            owner_installation_ref=assignment["owner_installation_ref"],
            owner_epoch=assignment["owner_epoch"],
            actor_id=actor_id,
            observations={assignment["assignment_id"]: observations},
            output_artifacts=output_artifacts,
        )

    @classmethod
    def repair_review_artifact(
        cls,
        issue: dict[str, object],
        manifest: list[dict[str, str]],
        *,
        issue_id: str | None = None,
        base_commit: str | None = None,
        repair_subject_type: str = "repository-repair",
        repair_subject_id: str = "repair-1",
        verdict: str = "REPAIR_APPROVED",
    ) -> bytes:
        report = issue["report"]
        return team_records.canonical_json(
            {
                "schema": team_records.REPAIR_REVIEW_SCHEMA,
                "issue_id": issue_id or issue["issue_id"],
                "repair_subject_type": repair_subject_type,
                "repair_subject_id": repair_subject_id,
                "base_commit": base_commit or report["base_commit"],
                "candidate_manifest": manifest,
                "verdict": verdict,
            }
        )

    def test_canonical_json_and_duplicate_key_rejection(self):
        self.assertEqual(team_records.canonical_json({"b": 2, "a": 1}), b'{"a":1,"b":2}\n')
        with self.assertRaisesRegex(team_records.TeamRecordError, "DUPLICATE_JSON_KEY"):
            team_records.load_payload(b'{"a":1,"a":2}\n')
        with self.assertRaisesRegex(team_records.TeamRecordError, "UNSUPPORTED_JSON_VALUE"):
            team_records.canonical_json({"value": 1.5})
        with self.assertRaisesRegex(team_records.TeamRecordError, "NONCANONICAL_PAYLOAD"):
            team_records.load_payload(b'{"a": 1}\n')

    def test_report_provenance_rejects_unknown_assignment_and_reporter_mismatch(self):
        assignment = self.provenance_assignment()
        legacy = b"legacy assignments\n"
        raw, _ = team_records.prepare_assignment(
            legacy, assignment, hashlib.sha256(legacy).hexdigest()
        )
        registry = team_records.read_registry(raw, "assignments")
        context = self.provenance_context(assignment)
        with self.assertRaisesRegex(team_records.TeamRecordError, "ASSIGNMENT_UNKNOWN"):
            team_records.validate_report_provenance(self.report(number=2), registry, context)

        mismatched = self.report()
        mismatched["reporter_task"] = "spoofed-reporter"
        with self.assertRaisesRegex(team_records.TeamRecordError, "REPORTER_ASSIGNMENT_MISMATCH"):
            team_records.validate_report_provenance(mismatched, registry, context)

    def test_report_provenance_accepts_running_native_receipts(self):
        assignment = self.provenance_assignment()
        legacy = b"legacy assignments\n"
        raw, _ = team_records.prepare_assignment(
            legacy, assignment, hashlib.sha256(legacy).hexdigest()
        )
        registry = team_records.read_registry(raw, "assignments")
        context = self.provenance_context(assignment, result_state="RUNNING")
        result = team_records.validate_report_provenance(self.report(), registry, context)
        self.assertEqual(result["assignment_id"], assignment["assignment_id"])
        self.assertEqual(result["operation_ids"], ("native-launch", "native-result"))
        self.assertEqual(len(result["source_hashes"]), 1)
        self.assertEqual(len(result["evidence_hashes"]), 4)

    def test_report_provenance_rejects_unrelated_report_payload(self):
        assignment = self.provenance_assignment()
        legacy = b"legacy assignments\n"
        raw, _ = team_records.prepare_assignment(
            legacy, assignment, hashlib.sha256(legacy).hexdigest()
        )
        registry = team_records.read_registry(raw, "assignments")
        context = self.provenance_context(assignment, report=self.report())
        with self.assertRaisesRegex(team_records.TeamRecordError, "REPORT_OUTPUT_BINDING_INVALID"):
            team_records.validate_report_provenance(
                self.report(actual="unrelated report"), registry, context
            )

    def test_report_provenance_survives_status_and_next_check_update(self):
        assignment = self.provenance_assignment()
        legacy = b"legacy assignments\n"
        created, _ = team_records.prepare_assignment(
            legacy, assignment, hashlib.sha256(legacy).hexdigest()
        )
        created_registry = team_records.read_registry(created, "assignments")
        current = created_registry["assignments"][assignment["assignment_id"]]
        updated = dict(assignment)
        updated.update(
            {
                "operation": "UPDATE",
                "status": "RUNNING",
                "next_check": "2026-09-11T12:30:00+02:00",
                "previous_assignment_sha256": team_records._assignment_state_sha(
                    current["assignment"]
                ),
                "previous_assignment_event_sha256": current["last_event_sha256"],
            }
        )
        updated_raw, _ = team_records.prepare_assignment(
            created, updated, hashlib.sha256(created).hexdigest()
        )
        updated_registry = team_records.read_registry(updated_raw, "assignments")
        result = team_records.validate_report_provenance(
            self.report(), updated_registry, self.provenance_context(assignment)
        )
        self.assertEqual(result["assignment_id"], assignment["assignment_id"])

    def test_native_launch_and_result_share_agent_and_subject(self):
        assignment = self.provenance_assignment()
        legacy = b"legacy assignments\n"
        raw, _ = team_records.prepare_assignment(
            legacy, assignment, hashlib.sha256(legacy).hexdigest()
        )
        registry = team_records.read_registry(raw, "assignments")
        context = self.provenance_context(assignment)
        observations = [dict(item) for item in context.observations[assignment["assignment_id"]]]
        observations[1]["native_agent_id"] = "different-agent"
        broken = team_records.TrustedTeamContext(
            owner_task=context.owner_task,
            owner_host=context.owner_host,
            owner_installation_ref=context.owner_installation_ref,
            owner_epoch=context.owner_epoch,
            actor_id=context.actor_id,
            observations={assignment["assignment_id"]: observations},
        )
        with self.assertRaisesRegex(team_records.TeamRecordError, "NATIVE_AGENT_BINDING_INVALID"):
            team_records.validate_report_provenance(self.report(), registry, broken)

    def test_issue_actor_provenance_rejects_spoofed_owner_and_accepts_independent(self):
        assignment = self.provenance_assignment()
        legacy_assignments = b"legacy assignments\n"
        assignment_raw, _ = team_records.prepare_assignment(
            legacy_assignments, assignment, hashlib.sha256(legacy_assignments).hexdigest()
        )
        assignments = team_records.read_registry(assignment_raw, "assignments")
        legacy_issues = b"legacy issues\n"
        issue_raw, _ = team_records.prepare_report(
            legacy_issues, self.report(), hashlib.sha256(legacy_issues).hexdigest()
        )
        issues = team_records.read_registry(issue_raw, "issues")
        context = self.provenance_context(assignment)

        spoofed = self.transition(issues, "ASSIGNED", actor="spoofed-owner")
        spoofed["actor_role"] = "owner"
        with self.assertRaisesRegex(team_records.TeamRecordError, "OWNER_ACTOR_MISMATCH"):
            team_records.validate_issue_event_actor(spoofed, assignments, context)

        result_observation = context.observations[assignment["assignment_id"]][1]
        independent = self.transition(
            issues,
            "CONFIRMED_BUG",
            actor="reporter-task",
            evidence=[
                {
                    "locator": result_observation["output_locator"],
                    "sha256": result_observation["output_sha256"],
                }
            ],
        )
        result = team_records.validate_issue_event_actor(independent, assignments, context)
        self.assertEqual(result["actor_class"], "independent")
        self.assertEqual(result["assignment_id"], assignment["assignment_id"])

        implementer_assignment = self.provenance_assignment(role="implementation")
        implementer_context = self.provenance_context(implementer_assignment)
        implementer_assignments_raw, _ = team_records.prepare_assignment(
            legacy_assignments,
            implementer_assignment,
            hashlib.sha256(legacy_assignments).hexdigest(),
        )
        implementer_assignments = team_records.read_registry(
            implementer_assignments_raw, "assignments"
        )
        implementer_evidence = implementer_context.observations[
            implementer_assignment["assignment_id"]
        ][1]
        candidate = self.transition(
            issues,
            "FIX_CANDIDATE",
            actor="reporter-task",
            actor_role="implementer",
            evidence=[
                {
                    "locator": implementer_evidence["output_locator"],
                    "sha256": implementer_evidence["output_sha256"],
                }
            ],
        )
        result = team_records.validate_issue_event_actor(
            candidate, implementer_assignments, implementer_context
        )
        self.assertEqual(result["actor_class"], "implementer")

        candidate["implementer_id"] = "another-implementer"
        with self.assertRaisesRegex(team_records.TeamRecordError, "IMPLEMENTER_IDENTITY_INVALID"):
            team_records.validate_issue_event_actor(
                candidate, implementer_assignments, implementer_context
            )

    def test_fix_verified_binds_manifest_to_completed_review_artifact(self):
        assignment = self.provenance_assignment(role="independent-checker")
        legacy_assignments = b"legacy assignments\n"
        assignment_raw, _ = team_records.prepare_assignment(
            legacy_assignments, assignment, hashlib.sha256(legacy_assignments).hexdigest()
        )
        assignments = team_records.read_registry(assignment_raw, "assignments")
        legacy_issues = b"legacy issues\n"
        issue_raw, _ = team_records.prepare_report(
            legacy_issues, self.report(), hashlib.sha256(legacy_issues).hexdigest()
        )
        issues = team_records.read_registry(issue_raw, "issues")
        issue = next(iter(issues["issues"].values()))
        manifest = [{"path": "orchestrator/team_records.py", "sha256": self.SHA}]

        def event(context: team_records.TrustedTeamContext, **extra: object) -> dict[str, object]:
            result_observation = context.observations[assignment["assignment_id"]][1]
            return self.transition(
                issues,
                "FIX_VERIFIED",
                actor="reporter-task",
                actor_role="independent-checker",
                verifier_id="reporter-task",
                evidence=[
                    {
                        "locator": result_observation["output_locator"],
                        "sha256": result_observation["output_sha256"],
                    }
                ],
                candidate_manifest=manifest,
                **extra,
            )

        reviewed = self.repair_review_artifact(issue, manifest)
        context = self.provenance_context(assignment, review_artifact=reviewed)
        result = team_records.validate_issue_event_actor(
            event(context), assignments, context, expected_base_commit=self.SHA
        )
        self.assertEqual(result["actor_class"], "independent")

        genuine_other_output = self.provenance_context(assignment)
        with self.assertRaisesRegex(team_records.TeamRecordError, "NATIVE_REVIEW_ARTIFACT_INVALID"):
            team_records.validate_issue_event_actor(
                event(genuine_other_output), assignments, genuine_other_output,
                expected_base_commit=self.SHA,
            )

        wrong_manifest = [{"path": "orchestrator/team_records.py", "sha256": "b" * 64}]
        wrong_manifest_artifact = self.repair_review_artifact(issue, wrong_manifest)
        wrong_manifest_context = self.provenance_context(
            assignment, review_artifact=wrong_manifest_artifact
        )
        with self.assertRaisesRegex(team_records.TeamRecordError, "NATIVE_REVIEW_MANIFEST_MISMATCH"):
            team_records.validate_issue_event_actor(
                event(wrong_manifest_context), assignments, wrong_manifest_context,
                expected_base_commit=self.SHA,
            )

        wrong_issue_artifact = self.repair_review_artifact(
            issue, manifest, issue_id="issue-" + "b" * 64
        )
        wrong_issue_context = self.provenance_context(assignment, review_artifact=wrong_issue_artifact)
        with self.assertRaisesRegex(team_records.TeamRecordError, "NATIVE_REVIEW_ISSUE_MISMATCH"):
            team_records.validate_issue_event_actor(
                event(wrong_issue_context), assignments, wrong_issue_context,
                expected_base_commit=self.SHA,
            )

        wrong_base_artifact = self.repair_review_artifact(
            issue, manifest, base_commit="c" * 64
        )
        wrong_base_context = self.provenance_context(assignment, review_artifact=wrong_base_artifact)
        with self.assertRaisesRegex(team_records.TeamRecordError, "NATIVE_REVIEW_BASE_MISMATCH"):
            team_records.validate_issue_event_actor(
                event(wrong_base_context), assignments, wrong_base_context,
                expected_base_commit=self.SHA,
            )

        rejected = self.repair_review_artifact(issue, manifest, verdict="REPAIR_REJECTED")
        rejected_context = self.provenance_context(assignment, review_artifact=rejected)
        with self.assertRaisesRegex(
            team_records.TeamRecordError,
            "NATIVE_REVIEW_ARTIFACT_INVALID.*REPAIR_REVIEW_NOT_APPROVED",
        ):
            team_records.validate_issue_event_actor(
                event(rejected_context), assignments, rejected_context,
                expected_base_commit=self.SHA,
            )

    def test_running_observation_without_concrete_receipt_is_rejected(self):
        assignment = self.provenance_assignment()
        legacy = b"legacy assignments\n"
        raw, _ = team_records.prepare_assignment(
            legacy, assignment, hashlib.sha256(legacy).hexdigest()
        )
        registry = team_records.read_registry(raw, "assignments")
        context = self.provenance_context(assignment)
        broken = dict(context.observations[assignment["assignment_id"]][0])
        del broken["provider_receipt_sha256"]
        broken_context = team_records.TrustedTeamContext(
            owner_task=context.owner_task,
            owner_host=context.owner_host,
            owner_installation_ref=context.owner_installation_ref,
            owner_epoch=context.owner_epoch,
            actor_id=context.actor_id,
            observations={assignment["assignment_id"]: [broken, context.observations[assignment["assignment_id"]][1]]},
        )
        with self.assertRaisesRegex(team_records.TeamRecordError, "NATIVE_OBSERVATION_SCHEMA_INVALID"):
            team_records.validate_report_provenance(self.report(), registry, broken_context)

    def test_report_replay_after_subsequent_event_and_receipt_recovery(self):
        legacy = b"# historical issues\n\n"
        first, receipt = team_records.prepare_report(
            legacy, self.report(), hashlib.sha256(legacy).hexdigest()
        )
        registry = team_records.read_registry(first, "issues")
        reproducing = self.transition(registry, "REPRODUCING")
        second, _ = team_records.prepare_issue_event(
            first, reproducing, hashlib.sha256(first).hexdigest()
        )
        registry = team_records.read_registry(second, "issues")
        confirmed = self.transition(registry, "CONFIRMED_BUG")
        third, _ = team_records.prepare_issue_event(
            second, confirmed, hashlib.sha256(second).hexdigest()
        )
        replayed, replay_receipt = team_records.prepare_report(
            third, self.report(), "0" * 64
        )
        self.assertEqual(replayed, third)
        self.assertEqual(replay_receipt["status"], "NOOP")
        self.assertEqual(replay_receipt["event_id"], receipt["event_id"])
        self.assertEqual(replay_receipt["receipt_sha256"], receipt["receipt_sha256"])
        self.assertEqual(replay_receipt["post_registry_sha256"], receipt["post_registry_sha256"])

    def test_changed_attempt_collision_and_stale_new_report(self):
        raw = b"legacy\n"
        # Keep the first call explicit so the expected preimage is visible.
        first, _ = team_records.prepare_report(raw, self.report(actual="one"), hashlib.sha256(raw).hexdigest())
        changed = self.report(actual="two")
        with self.assertRaisesRegex(team_records.TeamRecordError, "ATTEMPT_COLLISION"):
            team_records.prepare_report(first, changed, hashlib.sha256(first).hexdigest())
        second = self.report(number=2)
        with self.assertRaisesRegex(team_records.TeamRecordError, "STALE_REGISTRY"):
            team_records.prepare_report(first, second, hashlib.sha256(raw).hexdigest())

    def test_correction_requires_new_attempt_and_supersedes_link(self):
        raw = b"legacy\n"
        first, first_receipt = team_records.prepare_report(
            raw, self.report(actual="initial"), hashlib.sha256(raw).hexdigest()
        )
        correction = self.report(attempt="attempt-correction", actual="corrected")
        correction["supersedes_report_id"] = first_receipt["report_id"]
        corrected, _ = team_records.prepare_report(
            first, correction, hashlib.sha256(first).hexdigest()
        )
        self.assertEqual(len(team_records.read_registry(corrected, "issues")["issues"]), 2)

    def test_corrupted_framing_and_legacy_prefix_are_fail_closed(self):
        legacy = b"legacy text with *literal* markers\n"
        prepared, _ = team_records.prepare_report(
            legacy, self.report(), hashlib.sha256(legacy).hexdigest()
        )
        self.assertTrue(prepared.startswith(legacy))
        parsed = team_records.read_registry(prepared, "issues")
        self.assertEqual(parsed["legacy_prefix"], legacy)
        self.assertEqual(parsed["legacy_sha256"], hashlib.sha256(legacy).hexdigest())
        with self.assertRaisesRegex(team_records.TeamRecordError, "REGISTRY_FRAMING_INVALID|PAYLOAD_INVALID|NONCANONICAL"):
            team_records.read_registry(prepared[:-1], "issues")
        oversized = prepared + team_records.FRAME_PREFIX + b"999999\n"
        with self.assertRaisesRegex(team_records.TeamRecordError, "LIMIT_FRAME_BYTES"):
            team_records.read_registry(oversized, "issues")

    def test_archive_replay_uses_verified_immutable_bytes(self):
        raw = b"legacy\n"
        first, first_receipt = team_records.prepare_report(raw, self.report(), hashlib.sha256(raw).hexdigest())
        second_payload = self.report(number=2)
        second, _ = team_records.prepare_report(first, second_payload, hashlib.sha256(first).hexdigest())
        archive, compact, archive_receipt = team_records.prepare_archive(
            second, "issues", hashlib.sha256(second).hexdigest(), "archive/issues-1.json"
        )
        receipt_core = {
            key: value
            for key, value in archive_receipt.items()
            if key not in {"status", "receipt_sha256"}
        }
        self.assertEqual(
            archive_receipt["receipt_sha256"],
            hashlib.sha256(team_records.canonical_json(receipt_core)).hexdigest(),
        )
        self.assertEqual(archive_receipt["archive_sha256"], hashlib.sha256(archive).hexdigest())
        loader = {"archive/issues-1.json": archive}
        parsed = team_records.read_registry(compact, "issues", loader)
        self.assertEqual(len(parsed["events"]), 2)
        replayed, receipt = team_records.prepare_report(compact, self.report(), "0" * 64, loader)
        self.assertEqual(replayed, compact)
        self.assertEqual(receipt["status"], "NOOP")
        self.assertEqual(receipt["receipt_sha256"], first_receipt["receipt_sha256"])
        with self.assertRaisesRegex(team_records.TeamRecordError, "ARCHIVE_HASH_INVALID"):
            team_records.read_registry(compact, "issues", {"archive/issues-1.json": b"tampered"})

    def test_independent_identity_and_source_binding_rejections(self):
        raw = b"legacy\n"
        current, _ = team_records.prepare_report(raw, self.report(), hashlib.sha256(raw).hexdigest())
        registry = team_records.read_registry(current, "issues")
        with self.assertRaisesRegex(team_records.TeamRecordError, "SOURCE_BINDING_REQUIRED"):
            bad = self.transition(registry, "REPRODUCING")
            bad["source_binding"] = []
            team_records.prepare_issue_event(current, bad, hashlib.sha256(current).hexdigest())
        reproducing = self.transition(registry, "REPRODUCING")
        current, _ = team_records.prepare_issue_event(current, reproducing, hashlib.sha256(current).hexdigest())
        registry = team_records.read_registry(current, "issues")
        current, _ = team_records.prepare_issue_event(
            current,
            self.transition(registry, "CONFIRMED_BUG"),
            hashlib.sha256(current).hexdigest(),
        )
        registry = team_records.read_registry(current, "issues")
        current, _ = team_records.prepare_issue_event(
            current,
            self.transition(registry, "ASSIGNED"),
            hashlib.sha256(current).hexdigest(),
        )
        registry = team_records.read_registry(current, "issues")
        current, _ = team_records.prepare_issue_event(
            current,
            self.transition(registry, "FIX_CANDIDATE", actor="implementer"),
            hashlib.sha256(current).hexdigest(),
        )
        registry = team_records.read_registry(current, "issues")
        with self.assertRaisesRegex(team_records.TeamRecordError, "INDEPENDENT_IDENTITY_REQUIRED"):
            team_records.prepare_issue_event(
                current,
                self.transition(registry, "FIX_VERIFIED", actor="implementer"),
                hashlib.sha256(current).hexdigest(),
            )

    def test_repair_candidate_identity_is_required_and_stable(self):
        raw = b"legacy\n"
        current, _ = team_records.prepare_report(raw, self.report(), hashlib.sha256(raw).hexdigest())
        registry = team_records.read_registry(current, "issues")
        for transition, actor, role in (
            ("REPRODUCING", "independent-checker", "independent-checker"),
            ("CONFIRMED_BUG", "independent-checker", "independent-checker"),
            ("ASSIGNED", "owner-actor", "owner"),
            ("FIX_CANDIDATE", "implementer", "implementer"),
        ):
            current, _ = team_records.prepare_issue_event(
                current,
                self.transition(registry, transition, actor=actor, actor_role=role),
                hashlib.sha256(current).hexdigest(),
            )
            registry = team_records.read_registry(current, "issues")

        manifest = [{"path": "orchestrator/team_records.py", "sha256": self.SHA}]
        verified = self.transition(
            registry,
            "FIX_VERIFIED",
            actor="verifier",
            actor_role="independent-checker",
            verifier_id="verifier",
            candidate_manifest=manifest,
        )
        current, _ = team_records.prepare_issue_event(
            current, verified, hashlib.sha256(current).hexdigest()
        )
        registry = team_records.read_registry(current, "issues")
        committed = self.transition(
            registry,
            "FIX_COMMITTED",
            actor="owner-actor",
            actor_role="owner",
            candidate_manifest=manifest,
            candidate_commit=self.SHA,
        )
        current, _ = team_records.prepare_issue_event(
            current, committed, hashlib.sha256(current).hexdigest()
        )
        registry = team_records.read_registry(current, "issues")
        published = self.transition(
            registry,
            "FIX_PUSH_VERIFIED",
            actor="owner-actor",
            actor_role="owner",
            candidate_manifest=manifest,
            candidate_commit=self.SHA,
        )
        current, _ = team_records.prepare_issue_event(
            current, published, hashlib.sha256(current).hexdigest()
        )
        issue = next(iter(team_records.read_registry(current, "issues")["issues"].values()))
        self.assertEqual(issue["state"], "FIX_PUSH_VERIFIED")
        self.assertEqual(issue["repair_candidate_manifest"], manifest)
        self.assertEqual(issue["repair_candidate_commit"], self.SHA)

    def test_repair_commit_cannot_change_verified_candidate(self):
        raw = b"legacy\n"
        current, _ = team_records.prepare_report(raw, self.report(), hashlib.sha256(raw).hexdigest())
        registry = team_records.read_registry(current, "issues")
        for transition, actor, role in (
            ("REPRODUCING", "independent-checker", "independent-checker"),
            ("CONFIRMED_BUG", "independent-checker", "independent-checker"),
            ("ASSIGNED", "owner-actor", "owner"),
            ("FIX_CANDIDATE", "implementer", "implementer"),
        ):
            current, _ = team_records.prepare_issue_event(
                current,
                self.transition(registry, transition, actor=actor, actor_role=role),
                hashlib.sha256(current).hexdigest(),
            )
            registry = team_records.read_registry(current, "issues")
        manifest = [{"path": "orchestrator/team_records.py", "sha256": self.SHA}]
        current, _ = team_records.prepare_issue_event(
            current,
            self.transition(
                registry, "FIX_VERIFIED", actor="verifier", actor_role="independent-checker",
                verifier_id="verifier", candidate_manifest=manifest,
            ),
            hashlib.sha256(current).hexdigest(),
        )
        registry = team_records.read_registry(current, "issues")
        changed = self.transition(
            registry,
            "FIX_COMMITTED",
            actor="owner-actor",
            actor_role="owner",
            candidate_manifest=[{"path": "orchestrator/workflow_runtime.py", "sha256": self.SHA}],
            candidate_commit=self.SHA,
        )
        with self.assertRaisesRegex(team_records.TeamRecordError, "REPAIR_CANDIDATE_CHANGED"):
            team_records.prepare_issue_event(current, changed, hashlib.sha256(current).hexdigest())

    def test_legal_and_illegal_lifecycle_transitions(self):
        raw = b"legacy\n"
        current, _ = team_records.prepare_report(raw, self.report(), hashlib.sha256(raw).hexdigest())
        registry = team_records.read_registry(current, "issues")
        with self.assertRaisesRegex(team_records.TeamRecordError, "ILLEGAL_TRANSITION"):
            team_records.prepare_issue_event(
                current,
                self.transition(registry, "CONFIRMED_BUG"),
                hashlib.sha256(current).hexdigest(),
            )
        current, _ = team_records.prepare_issue_event(
            current,
            self.transition(registry, "REPRODUCING"),
            hashlib.sha256(current).hexdigest(),
        )
        registry = team_records.read_registry(current, "issues")
        current, _ = team_records.prepare_issue_event(
            current,
            self.transition(registry, "CONFIRMED_BUG"),
            hashlib.sha256(current).hexdigest(),
        )
        self.assertEqual(next(iter(team_records.read_registry(current, "issues")["issues"].values()))["state"], "CONFIRMED_BUG")

    def test_assignment_create_update_retry_and_stale_preimage(self):
        raw = b"# historical assignments\n"
        created, create_receipt = team_records.prepare_assignment(
            raw, self.assignment(), hashlib.sha256(raw).hexdigest()
        )
        registry = team_records.read_registry(created, "assignments")
        current = next(iter(registry["assignments"].values()))
        current_payload = current["assignment"]
        previous = team_records._assignment_state_sha(current_payload)
        updated_payload = self.assignment(operation="UPDATE", previous=previous)
        updated_payload["previous_assignment_event_sha256"] = current["last_event_sha256"]
        updated, _ = team_records.prepare_assignment(
            created, updated_payload, hashlib.sha256(created).hexdigest()
        )
        replayed, replay_receipt = team_records.prepare_assignment(
            updated, updated_payload, "0" * 64
        )
        self.assertEqual(replayed, updated)
        self.assertEqual(replay_receipt["status"], "NOOP")
        self.assertEqual(replay_receipt["event_id"], team_records.read_registry(updated, "assignments")["events"][1]["event_id"])
        self.assertNotEqual(create_receipt["event_id"], replay_receipt["event_id"])
        with self.assertRaisesRegex(team_records.TeamRecordError, "ASSIGNMENT_PRECONDITION"):
            team_records.prepare_assignment(
                updated,
                self.assignment(operation="RETRY", previous="b" * 64),
                hashlib.sha256(updated).hexdigest(),
            )

    def test_global_chain_and_entity_predecessors_interleave(self):
        legacy = b"legacy\n"
        report_a = self.report(number=1)
        report_b = self.report(number=2)
        issues_a, receipt_a = team_records.prepare_report(
            legacy, report_a, hashlib.sha256(legacy).hexdigest()
        )
        issues_b, _ = team_records.prepare_report(
            issues_a, report_b, hashlib.sha256(issues_a).hexdigest()
        )
        registry = team_records.read_registry(issues_b, "issues")
        transition_a = self.transition(registry, "REPRODUCING")
        interleaved, _ = team_records.prepare_issue_event(
            issues_b, transition_a, hashlib.sha256(issues_b).hexdigest()
        )
        parsed = team_records.read_registry(interleaved, "issues")
        events = parsed["events"]
        self.assertEqual(len(events), 3)
        self.assertEqual(
            events[2]["previous_event_sha256"], team_records._event_sha(events[1])
        )
        self.assertEqual(
            events[2]["payload"]["previous_event_sha256"], team_records._event_sha(events[0])
        )
        replayed, replay_receipt = team_records.prepare_report(
            interleaved, report_a, "0" * 64
        )
        self.assertEqual(replayed, interleaved)
        self.assertEqual(replay_receipt["receipt_sha256"], receipt_a["receipt_sha256"])

        assignments = b"legacy assignments\n"
        assignments_a, _ = team_records.prepare_assignment(
            assignments,
            self.assignment(assignment_id="assignment-a"),
            hashlib.sha256(assignments).hexdigest(),
        )
        assignments_b, _ = team_records.prepare_assignment(
            assignments_a,
            self.assignment(assignment_id="assignment-b"),
            hashlib.sha256(assignments_a).hexdigest(),
        )
        assignments_registry = team_records.read_registry(assignments_b, "assignments")
        current_a = assignments_registry["assignments"]["assignment-a"]
        updated_a = self.assignment(
            assignment_id="assignment-a",
            operation="UPDATE",
            previous=team_records._assignment_state_sha(current_a["assignment"]),
        )
        updated_a["previous_assignment_event_sha256"] = current_a["last_event_sha256"]
        assignments_interleaved, _ = team_records.prepare_assignment(
            assignments_b, updated_a, hashlib.sha256(assignments_b).hexdigest()
        )
        assignments_parsed = team_records.read_registry(assignments_interleaved, "assignments")
        assignment_events = assignments_parsed["events"]
        self.assertEqual(len(assignment_events), 3)
        self.assertEqual(
            assignment_events[2]["previous_event_sha256"], team_records._event_sha(assignment_events[1])
        )
        self.assertEqual(
            assignment_events[2]["payload"]["previous_assignment_event_sha256"],
            team_records._event_sha(assignment_events[0]),
        )

    def test_archive_replay_after_interleaved_issue_updates(self):
        legacy = b"legacy\n"
        report_a = self.report(number=1)
        report_b = self.report(number=2)
        first, receipt_a = team_records.prepare_report(
            legacy, report_a, hashlib.sha256(legacy).hexdigest()
        )
        second, _ = team_records.prepare_report(
            first, report_b, hashlib.sha256(first).hexdigest()
        )
        registry = team_records.read_registry(second, "issues")
        third, _ = team_records.prepare_issue_event(
            second,
            self.transition(registry, "REPRODUCING"),
            hashlib.sha256(second).hexdigest(),
        )
        archive, compact, _ = team_records.prepare_archive(
            third, "issues", hashlib.sha256(third).hexdigest(), "archive/interleaved.json", event_count=2
        )
        loader = {"archive/interleaved.json": archive}
        parsed = team_records.read_registry(compact, "issues", loader)
        self.assertEqual(len(parsed["events"]), 3)
        replayed, replay_receipt = team_records.prepare_report(
            compact, report_a, "0" * 64, loader
        )
        self.assertEqual(replayed, compact)
        self.assertEqual(replay_receipt["status"], "NOOP")
        self.assertEqual(replay_receipt["receipt_sha256"], receipt_a["receipt_sha256"])



if __name__ == "__main__":
    unittest.main()
