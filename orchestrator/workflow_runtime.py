#!/usr/bin/env python3
"""Stateless front door for the existing Q3 goal lifecycle.

This module compiles the authoritative selector, tool manifest, derived-artifact
registry, review transport contract, and close helpers into one deterministic
plan.  Its run command then executes the registered, explicitly scoped
transition and emits receipts. The resume-checkpoint command stores advisory
observations and their byte history, never selector state. Only the registered
initial-migration command may publish its reserved exact fast-forward candidate;
the planner never commits, pushes, promotes, or makes an RH claim. Browser
transport is performed by the current Codex body after ``review-plan`` has
validated the exact attachment; compiling a plan never claims delivery.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import platform
import re
import secrets
import stat
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager, nullcontext
from dataclasses import asdict, replace
from datetime import datetime
from pathlib import Path
from typing import Any, BinaryIO, Iterator, Sequence

import yaml

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import node_registry_v10  # noqa: E402
from orchestrator.startup_runtime import (  # noqa: E402
    AUTHORITATIVE_MODE,
    AUTHORITATIVE_SCHEMA,
    StartupRuntimeError,
    StartupSnapshot,
    _git_common_dir,
    _goal_header,
    _has_symlink_component,
    _lexical_relative,
    _load_unique_json,
    _startup_read_epoch,
    _validate_modern_answer,
    build_shadow_snapshot,
    build_startup_snapshot,
    goal_close_receipt_path,
    phase_close_receipt_path,
    validate_goal_close_receipt,
    validate_phase_close_receipt,
)

TOOLS = Path("docs/cartographer/TOOLS.yaml")
REGISTRY = Path("docs/cartographer/DERIVED_ARTIFACTS.yaml")
FINGERPRINT_PATHS = (
    Path("docs/CODEX_CONTROL.md"),
    TOOLS,
    REGISTRY,
)
RUNTIME_FINGERPRINT_PATHS = (
    Path("orchestrator/state/CHANNEL_RUNTIME.json"),
    Path("orchestrator/state/SEMANTIC_QUARANTINE.json"),
    Path("q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"),
    Path("q3.lean.aristotle/.qmd_cache/semantic_index_receipt.json"),
)

REVIEW_INSTRUCTION = (
    "Read the attached controlling request in full. Treat the .txt attachment as the "
    "authoritative byte-exact payload. Follow its required response schema and return "
    "exactly the requested verdict. Same living phase chat. Do not use Answer now."
)

CANONICAL_CALL_CLASSES = {
    "DELEGATED_STRATEGIC_REVIEW",
    "EXPLORATION_REVIEW",
    "PX_RH_CLAIM_REVIEW",
}
RESEARCH_DEBT_PACKET_SUBTYPE = "RESEARCH_DEBT_CHALLENGE"
DEPENDENCY_CONTRACT_RECEIPT_SCHEMA = "q3_research_dependency_contract_receipt.v1"
SUPPLIER_PREFLIGHT_SCHEMA = "q3_supplier_preflight.v1"
SEARCH_EVIDENCE_SCHEMA = "q3_search_evidence.v1"
SEARCH_EVIDENCE_STDOUT_MAX_BYTES = 32 * 1024
SUPPLIER_PROVENANCE_CLASSES = frozenset(
    {"SOURCE_DECLARED", "GENERATED_OR_DERIVED"}
)
SUPPLIER_STATUS_EXIT = {
    "CANDIDATE_ONLY": 0,
    "EXACT_FIT": 0,
    "REJECTED": 0,
    "FOREIGN_UNVERIFIED": 0,
    "COMPLETE_ABSENCE": 1,
    "INCOMPLETE": 2,
}
SUPPLIER_PAYLOAD_FIELDS = frozenset(
    {
        "schema",
        "query",
        "candidate_requested",
        "target_requested",
        "candidate_provenance",
        "shelf",
        "external_lean",
        "environment",
        "status",
        "reason",
        "boundary",
        "candidate",
        "comparison",
        "foreign_candidate",
        "source_candidates",
        "prose_candidates_present",
        "source_absence_scope",
    }
)
SHADOW_PLAN_SCHEMA = "q3_workflow_plan.v2"
TEAM_PLAN_SCHEMA = "q3_workflow_plan.v3"
PRODUCTION_PLAN_MODE = "PRODUCTION_V10"
SHADOW_PLAN_MAX_BYTES = 8 * 1024
SHADOW_PLAN_MAX_LINES = 150
SHADOW_STARTUP_MAX_BYTES = 4 * 1024
SHADOW_STARTUP_MAX_LINES = 60
SHADOW_STARTUP_SCHEMA = "q3_startup_snapshot.v10.shadow.v1"
_BENCHMARK_TIMING_SCHEMA = "q3_shadow_startup_timing.v1"
_BENCHMARK_TIMING_PREFIX = "Q3_SHADOW_STARTUP_TIMING:"

COMMON_TOOLS = (
    "workflow-runtime",
    "codex-session-start",
    "roof-port-supplier-ledger",
    "goal-run-selector",
    "ask-shelf",
    "kb-query",
)
ACTION_TOOLS = {
    "SELECT_EXACT_GOAL": (
        "workflow-close-node",
        "workflow-search-evidence",
        "supplier-preflight",
        "lean-validation",
        "knowledge-spine-step-close",
        "knowledge-spine-goal-close",
        "workflow-session-close",
    ),
    "MINT_READY": ("supplier-preflight", "goal-run-selector"),
    "PHASE_TRANSITION_REQUIRED": (
        "knowledge-spine-goal-close",
        "workflow-phase-close",
    ),
    "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM": (),
}


class WorkflowRuntimeError(RuntimeError):
    pass


class _ExecutionWriterEpoch:
    """Stable exclusive ownership of the canonical repository writer lock."""

    def __init__(
        self,
        *,
        path: Path,
        handle: BinaryIO,
        identity: tuple[int, int, int],
    ) -> None:
        self.path = path
        self.handle = handle
        self.identity = identity
        self.open = True

    @staticmethod
    def _identity(value: os.stat_result) -> tuple[int, int, int]:
        return value.st_dev, value.st_ino, value.st_mode

    def recheck(self) -> None:
        if not self.open:
            raise WorkflowRuntimeError("WORKFLOW_WRITER_LOCK_NOT_HELD")
        try:
            path_identity = self._identity(os.lstat(self.path))
            handle_identity = self._identity(os.fstat(self.handle.fileno()))
        except OSError as exc:
            raise WorkflowRuntimeError(
                f"WORKFLOW_WRITER_LOCK_UNAVAILABLE:{exc}"
            ) from exc
        if path_identity != self.identity or handle_identity != self.identity:
            raise WorkflowRuntimeError("WORKFLOW_WRITER_LOCK_IDENTITY_CHANGED")


@contextmanager
def _execution_writer_epoch(
    repo: Path, *, integration_operation: str | None = None, bootstrap_operation: str | None = None,
) -> Iterator[_ExecutionWriterEpoch]:
    """Hold one non-blocking exclusive flock across the entire write transaction."""

    try:
        lock_path = _git_common_dir(repo.resolve()) / "q3-three-body.writer.lock"
        initial = os.lstat(lock_path)
    except (OSError, StartupRuntimeError) as exc:
        raise WorkflowRuntimeError(f"WORKFLOW_WRITER_LOCK_UNAVAILABLE:{exc}") from exc
    identity = _ExecutionWriterEpoch._identity(initial)
    if stat.S_ISLNK(initial.st_mode) or not stat.S_ISREG(initial.st_mode):
        raise WorkflowRuntimeError("WORKFLOW_WRITER_LOCK_IDENTITY_INVALID")
    handle: BinaryIO | None = None
    epoch: _ExecutionWriterEpoch | None = None
    try:
        descriptor = os.open(
            lock_path,
            os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0),
        )
        handle = os.fdopen(descriptor, "rb", closefd=True)
        if _ExecutionWriterEpoch._identity(os.fstat(handle.fileno())) != identity:
            raise WorkflowRuntimeError("WORKFLOW_WRITER_LOCK_IDENTITY_CHANGED")
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise WorkflowRuntimeError("WORKFLOW_WRITER_LOCK_COLLISION") from exc
        epoch = _ExecutionWriterEpoch(path=lock_path, handle=handle, identity=identity)
        epoch.recheck()
        _team_pending_guard(repo, operation_id=integration_operation, bootstrap_id=bootstrap_operation)
        yield epoch
        epoch.recheck()
    finally:
        if epoch is not None:
            epoch.open = False
        if handle is not None:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            finally:
                handle.close()


def _bounded_shadow_values(value: object, *, limit: int = 8) -> tuple[list[str], int]:
    values = list(value) if isinstance(value, (list, tuple)) else []
    compact = [str(item)[:160] for item in values[:limit]]
    return compact, max(0, len(values) - len(compact))


def _compact_startup_snapshot(
    snapshot: StartupSnapshot, *, shadow: bool = True
) -> dict[str, Any]:
    raw = snapshot.to_dict()
    expected_schema = SHADOW_STARTUP_SCHEMA if shadow else AUTHORITATIVE_SCHEMA
    expected_mode = "SHADOW_NOT_AUTHORITY" if shadow else AUTHORITATIVE_MODE
    if (
        raw.get("schema") != expected_schema
        or raw.get("mode") != expected_mode
        or (shadow and raw.get("run_authorized") is not False)
        or (not shadow and not isinstance(raw.get("run_authorized"), bool))
        or raw.get("honesty_state") != "CHALLENGER_NOT_RH"
    ):
        raise WorkflowRuntimeError(
            "SHADOW_V10_STARTUP_SNAPSHOT_INVALID"
            if shadow
            else "PRODUCTION_V10_STARTUP_SNAPSHOT_INVALID"
        )
    fatal_errors, fatal_errors_omitted = _bounded_shadow_values(raw["fatal_errors"])
    blocked_features, blocked_features_omitted = _bounded_shadow_values(
        raw["blocked_features"]
    )
    warnings, warnings_omitted = _bounded_shadow_values(raw["warnings"])
    compact = {
        "schema": raw["schema"],
        "mode": raw["mode"],
        "control_sha256": raw["control_sha256"],
        "control_version": raw["control_version"],
        "control_status": raw["control_status"],
        "git_head": raw["git_head"],
        "git_origin_head": raw["git_origin_head"],
        "git_tree": raw["git_tree"],
        "git_dirty": raw["git_dirty"],
        "selected_goal": raw["selected_goal"],
        "honesty_state": raw["honesty_state"],
        "exact_node_pin": raw["exact_node_pin"],
        "exact_source_pin": raw["exact_source_pin"],
        "exact_theorem_pin": raw["exact_theorem_pin"],
        "exact_consumer_pin": raw["exact_consumer_pin"],
        "fatal_errors": fatal_errors,
        "fatal_errors_omitted": fatal_errors_omitted,
        "blocked_features": blocked_features,
        "blocked_features_omitted": blocked_features_omitted,
        "warnings": warnings,
        "warnings_omitted": warnings_omitted,
        "next_action": str(raw["next_action"])[:320],
        "run_authorized": bool(raw["run_authorized"]),
    }
    if not shadow and snapshot.team_runtime_version:
        compact["team_runtime_version"] = snapshot.team_runtime_version
    rendered = json.dumps(compact, ensure_ascii=False, indent=2, sort_keys=True)
    if len(rendered.encode("utf-8")) > SHADOW_STARTUP_MAX_BYTES or len(
        rendered.splitlines()
    ) > SHADOW_STARTUP_MAX_LINES:
        raise WorkflowRuntimeError(
            "SHADOW_V10_STARTUP_SUMMARY_LIMIT_EXCEEDED"
            if shadow
            else "PRODUCTION_V10_STARTUP_SUMMARY_LIMIT_EXCEEDED"
        )
    return compact


def _compact_node_registry_summary(summary: dict[str, Any]) -> dict[str, Any]:
    valid = (
        summary.get("schema") == node_registry_v10.SUMMARY_SCHEMA
        and summary.get("status") in {"PASS", "HOLD", "VALIDATION_REQUIRED", "FATAL"}
        and isinstance(summary.get("code"), str)
    )
    compact = {
        "schema": summary.get("schema"),
        "status": summary["status"] if valid else "FATAL",
        "code": (
            summary["code"]
            if valid
            else "NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID"
        ),
        "registry_hash": summary.get("registry_hash"),
        "node_count": summary.get("node_count"),
        "edge_count": summary.get("edge_count"),
        "historical_v9_unmapped": summary.get("historical_v9_unmapped"),
        "consumption_status": summary.get("consumption_status"),
    }
    if summary.get("detail"):
        compact["detail"] = str(summary["detail"])[:320]
    return compact


def _registry_epoch_failure(code: str, detail: str) -> dict[str, Any]:
    return {
        "schema": node_registry_v10.SUMMARY_SCHEMA,
        "status": "FATAL",
        "code": code,
        "registry_hash": None,
        "node_count": 0,
        "edge_count": 0,
        "historical_v9_unmapped": 0,
        "consumption_status": "NOT_RUN_STARTUP_EPOCH_INVALID",
        "detail": detail,
    }


def _production_goal_binding(startup: dict[str, Any]) -> dict[str, Any]:
    selected_goal = startup.get("selected_goal")
    return {
        "action": "SELECT_EXACT_GOAL" if selected_goal else "HOLD",
        "selected_goal_id": startup.get("exact_node_pin"),
        "selected_goal_path": selected_goal,
        "exact_node_pin": startup.get("exact_node_pin"),
        "exact_source_pin": startup.get("exact_source_pin"),
        "exact_theorem_pin": startup.get("exact_theorem_pin"),
        "exact_consumer_pin": startup.get("exact_consumer_pin"),
    }


def _worktree_git_blob(path: Path) -> str | None:
    try:
        raw = path.read_bytes()
    except OSError:
        return None
    header = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(header + raw).hexdigest()


def _build_compact_roof_ledger(
    repo: Path,
    *,
    git_head: str | None,
    database: Path,
) -> dict[str, Any]:
    """Run the canonical roof builder with one closed-set batch Git read."""

    from orchestrator import roof_port_ledger

    tracked_paths = {
        roof_port_ledger.ROOF_SOURCE.as_posix(),
        *(
            raw_path
            for spec in roof_port_ledger.PORT_SPECS
            for raw_path, _declaration, _target in spec["candidates"]
        ),
    }
    receipt_path = repo / roof_port_ledger.AXIOM_RECEIPT
    try:
        receipt_text = receipt_path.read_text(encoding="utf-8")
    except OSError:
        receipt_text = ""
    match = re.search(
        r"(?m)^audited_baseline_head:\s*([0-9a-f]{40})\s*$", receipt_text
    )
    audited_head = match.group(1) if match else None
    specs = [f"HEAD:{path}" for path in sorted(tracked_paths)]
    if audited_head is not None:
        specs.append(f"{audited_head}:{roof_port_ledger.ROOF_SOURCE.as_posix()}")
    proc = subprocess.run(
        ["git", "cat-file", "--batch-check"],
        cwd=repo,
        input="".join(f"{spec}\n" for spec in specs),
        capture_output=True,
        text=True,
        check=False,
    )
    lines = proc.stdout.splitlines()
    if proc.returncode != 0 or len(lines) != len(specs):
        raise WorkflowRuntimeError("WORKFLOW_ROOF_GIT_BATCH_INVALID")
    resolved: dict[str, str | None] = {}
    for spec, line in zip(specs, lines, strict=True):
        fields = line.split()
        if len(fields) == 3 and fields[1] == "blob":
            resolved[spec] = fields[0]
        elif line.endswith(" missing"):
            resolved[spec] = None
        else:
            raise WorkflowRuntimeError("WORKFLOW_ROOF_GIT_BATCH_INVALID")

    def cached_git(_repo: Path, *args: str) -> str | None:
        if args == ("rev-parse", "HEAD"):
            return git_head
        if len(args) == 2 and args[0] == "rev-parse":
            if args[1] not in resolved:
                raise WorkflowRuntimeError("WORKFLOW_ROOF_GIT_QUERY_OUTSIDE_BATCH")
            return resolved[args[1]]
        if len(args) == 2 and args[0] == "hash-object":
            if args[1] not in tracked_paths:
                raise WorkflowRuntimeError("WORKFLOW_ROOF_GIT_QUERY_OUTSIDE_BATCH")
            return _worktree_git_blob(repo / args[1])
        raise WorkflowRuntimeError("WORKFLOW_ROOF_GIT_QUERY_OUTSIDE_BATCH")

    original_git = roof_port_ledger._git
    roof_port_ledger._git = cached_git
    try:
        roof = roof_port_ledger.build(repo, database)
    finally:
        roof_port_ledger._git = original_git
    roof_bookkeeping = roof.get("assembly_bookkeeping", {})
    return {
        "schema": roof.get("schema"),
        "integrity_status": roof.get("integrity_status"),
        "integrity_reasons": roof.get("integrity_reasons"),
        "honesty_state": roof.get("honesty_state"),
        "semantic_slot_count": roof.get("semantic_slot_count"),
        "direct_proof_input_count": roof.get("direct_proof_input_count"),
        "port_summary": roof.get("port_summary"),
        "assembly_bookkeeping": {
            "status": roof_bookkeeping.get("status"),
            "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
            "global": roof_bookkeeping.get("global"),
            "quarantined_edge_count": len(
                roof_bookkeeping.get("quarantined_edges") or []
            ),
        },
        "proof_percentage_interpretation": "REJECTED",
        "PX_RH_CLAIM": "NOT_MADE",
    }


def _compile_production_logical_plan(
    repo: Path,
    *,
    snapshot: StartupSnapshot,
    registry_summary: dict[str, Any],
    holds: list[str],
) -> dict[str, Any]:
    """Build the proof-loop card from the already selected startup epoch."""

    from orchestrator import proof_loop

    selected_goal_path = (
        repo / snapshot.selected_goal if snapshot.selected_goal is not None else None
    )
    database = repo / "q3.lean.aristotle/aristotle_db/knowledge.db"
    chain = proof_loop.goal_assembly_chain(selected_goal_path)
    assembly = proof_loop.assembly_snapshot(database, chain=chain)
    compact_roof = _build_compact_roof_ledger(
        repo,
        git_head=snapshot.git_head,
        database=database,
    )
    startup = _compact_startup_snapshot(snapshot, shadow=False)
    contract = proof_loop.compile_contract(
        goal_binding=_production_goal_binding(startup),
        holds=holds,
        assembly_debt=[],
        assembly=assembly,
        roof_ledger=compact_roof,
        route=None,
    )
    assembly_global = assembly.get("global", {})
    roof_ports = compact_roof.get("port_summary", {})
    return {
        "proof_loop": contract,
        "denominator_statuses": {
            "assembly": {
                "status": assembly.get("status"),
                "fixed": assembly_global.get("fixed"),
                "total": assembly_global.get("total"),
                "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
            },
            "roof_port_ledger": {
                "status": compact_roof.get("integrity_status"),
                "semantic_slot_count": compact_roof.get("semantic_slot_count"),
                "direct_proof_input_count": compact_roof.get(
                    "direct_proof_input_count"
                ),
                "jointly_bound": roof_ports.get("jointly_bound"),
            },
            "node_registry": {
                "status": registry_summary.get("status"),
                "code": registry_summary.get("code"),
            },
        },
    }


def compile_shadow_plan_v10(
    *,
    startup_snapshot: StartupSnapshot,
    node_registry_summary: dict[str, Any],
    host_executor: str,
) -> dict[str, Any]:
    """Compile a bounded read-only v10 observation with no run authority."""
    startup = _compact_startup_snapshot(startup_snapshot, shadow=True)
    registry = _compact_node_registry_summary(node_registry_summary)
    holds = list(startup["fatal_errors"])
    registry_status = registry["status"]
    if registry_status == "FATAL":
        holds.append(str(registry["code"]))
    if startup["control_status"] != "ACTIVE":
        holds.append(f"CONTROL_NOT_ACTIVE:{startup['control_status']}")
    status = "FATAL" if startup["fatal_errors"] or registry_status == "FATAL" else (
        "HOLD" if holds or registry_status in {"HOLD", "VALIDATION_REQUIRED"} else "READY"
    )
    blocked_features = [
        {
            "feature": feature,
            "scope": "SHADOW_V10_EXECUTION",
            "code": "BLOCKED_BY_DESIGN",
        }
        for feature in startup["blocked_features"]
    ]
    if registry_status in {"HOLD", "VALIDATION_REQUIRED"}:
        blocked_features.append(
            {
                "feature": "RUN_CLOSE_NODE",
                "scope": "NODE_REGISTRY_V10_CONSUMPTION",
                "code": registry["code"],
            }
        )
    return {
        "schema": SHADOW_PLAN_SCHEMA,
        "status": status,
        "mode": "SHADOW_V10_READ_ONLY",
        "host_executor": host_executor,
        "startup": startup,
        "node_registry": registry,
        "selected_goal": startup["selected_goal"],
        "holds": sorted(set(holds)),
        "blocked_features": blocked_features,
        "run_authorized": False,
        "writes_performed": False,
        "legacy_v9_authority_unchanged": True,
        "PX_RH_CLAIM": "NOT_MADE",
    }


def compile_plan_v10(
    *,
    startup_snapshot: StartupSnapshot,
    node_registry_summary: dict[str, Any],
    host_executor: str,
    logical_plan: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Compile the authoritative read-only startup result for production v10."""

    startup = _compact_startup_snapshot(startup_snapshot, shadow=False)
    registry = _compact_node_registry_summary(node_registry_summary)
    holds = list(startup["fatal_errors"])
    registry_status = registry["status"]
    if registry_status != "PASS":
        holds.append(str(registry["code"]))
    if startup["control_status"] != "ACTIVE":
        holds.append(f"CONTROL_NOT_ACTIVE:{startup['control_status']}")
    blocked_features = [
        {
            "feature": feature,
            "scope": "PRODUCTION_V10_EXECUTION",
            "code": "STARTUP_FEATURE_BLOCKED",
        }
        for feature in startup["blocked_features"]
    ]
    if registry_status in {"HOLD", "VALIDATION_REQUIRED"}:
        blocked_features.append(
            {
                "feature": "RUN_CLOSE_NODE",
                "scope": "NODE_REGISTRY_V10_CONSUMPTION",
                "code": registry["code"],
            }
        )
    fatal = bool(startup["fatal_errors"]) or registry_status == "FATAL"
    run_authorized = bool(
        startup["run_authorized"] and registry_status == "PASS" and not holds
    )
    status = "FATAL" if fatal else ("READY" if run_authorized else "HOLD")
    if logical_plan is None:
        from orchestrator import proof_loop

        contract = proof_loop.compile_contract(
            goal_binding=_production_goal_binding(startup),
            holds=holds,
            assembly_debt=[],
        )
        logical_plan = {
            "proof_loop": contract,
            "denominator_statuses": {
                "assembly": {
                    "status": "UNAVAILABLE",
                    "fixed": None,
                    "total": None,
                    "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
                },
                "roof_port_ledger": {
                    "status": "UNAVAILABLE",
                    "semantic_slot_count": 6,
                    "direct_proof_input_count": 7,
                    "jointly_bound": None,
                },
                "node_registry": {
                    "status": registry["status"],
                    "code": registry["code"],
                },
            },
        }
    return {
        "schema": SHADOW_PLAN_SCHEMA,
        "status": status,
        "mode": PRODUCTION_PLAN_MODE,
        "host_executor": host_executor,
        "startup": startup,
        "node_registry": registry,
        "logical_plan": logical_plan,
        "selected_goal": startup["selected_goal"],
        "holds": sorted(set(holds)),
        "blocked_features": blocked_features,
        "run_authorized": run_authorized,
        "writes_performed": False,
        "legacy_v9_authority_unchanged": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }


def live_shadow_plan_v10(
    repo: Path,
    *,
    owned_paths: list[str],
    _benchmark_timing_sink: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Build exactly one startup snapshot and reuse it for the shadow plan."""
    owned_scope = tuple(owned_paths)
    startup_started = (
        time.perf_counter() if _benchmark_timing_sink is not None else None
    )
    with _startup_read_epoch(repo) as (epoch_guard, lock_error):
        snapshot = build_shadow_snapshot(
            repo,
            owned_paths=owned_scope,
            _epoch_guard=epoch_guard,
            _epoch_lock_error=lock_error,
        )
        if _benchmark_timing_sink is not None:
            assert startup_started is not None
            _benchmark_timing_sink.update(
                {
                    "schema": _BENCHMARK_TIMING_SCHEMA,
                    "startup_duration_ms": round(
                        (time.perf_counter() - startup_started) * 1000, 3
                    ),
                    "snapshot_constructor_calls": 1,
                }
            )
        exact_edge_pins = (
            snapshot.exact_node_pin,
            snapshot.exact_source_pin,
            snapshot.exact_theorem_pin,
            snapshot.exact_consumer_pin,
        )
        if not all(isinstance(pin, str) and pin for pin in exact_edge_pins):
            exact_edge_pins = (None, None, None, None)
        if lock_error is not None:
            registry_summary = _registry_epoch_failure(
                "NODE_REGISTRY_WRITER_EPOCH_UNAVAILABLE", lock_error
            )
        else:
            registry_summary = node_registry_v10.startup_gate_summary(
                repo,
                snapshot.selected_goal,
                owned_paths=owned_scope,
                exact_node_pin=exact_edge_pins[0],
                exact_source_pin=exact_edge_pins[1],
                exact_theorem_pin=exact_edge_pins[2],
                exact_consumer_pin=exact_edge_pins[3],
            )
            epoch_error = epoch_guard.recheck()
            if epoch_error is not None:
                snapshot = replace(
                    snapshot,
                    selected_goal=None,
                    exact_node_pin=None,
                    exact_source_pin=None,
                    exact_theorem_pin=None,
                    exact_consumer_pin=None,
                    fatal_errors=tuple(
                        dict.fromkeys((epoch_error, *snapshot.fatal_errors))
                    ),
                    next_action="STOP_FAIL_CLOSED",
                )
                registry_summary = _registry_epoch_failure(
                    "NODE_REGISTRY_STARTUP_EPOCH_DRIFT", epoch_error
                )
    host = {"Darwin": "CODEX_MAC", "Linux": "CODEX_LINUX"}.get(
        platform.system(), "UNSUPPORTED_HOST"
    )
    return compile_shadow_plan_v10(
        startup_snapshot=snapshot,
        node_registry_summary=registry_summary,
        host_executor=host,
    )


def live_plan_v10(
    repo: Path,
    *,
    owned_paths: list[str],
    _benchmark_timing_sink: dict[str, Any] | None = None,
    _writer_epoch: _ExecutionWriterEpoch | None = None,
) -> dict[str, Any]:
    """Build exactly one authoritative v10 snapshot and reuse its exact pins."""

    owned_scope = tuple(owned_paths)
    startup_started = (
        time.perf_counter() if _benchmark_timing_sink is not None else None
    )
    read_epoch = (_startup_read_epoch(repo) if _writer_epoch is None
                  else nullcontext((_writer_epoch, None)))
    with read_epoch as (epoch_guard, lock_error):
        bootstrap = _team_pending_bootstrap(repo)
        if bootstrap is not None and lock_error is None:
            operation_id, receipt = bootstrap
            saved = receipt["bootstrap"]
            if epoch_guard.recheck() is not None or _team_pending_bootstrap(repo) != bootstrap:
                raise WorkflowRuntimeError("TEAM_READ_EPOCH_CHANGED")
            return {"schema": TEAM_PLAN_SCHEMA, "mode": PRODUCTION_PLAN_MODE, "status": "HOLD",
                    "holds": ["TEAM_BOOTSTRAP_PENDING"], "run_authorized": False,
                    "writes_performed": False, "execution_ready": False, "PX_RH_CLAIM": "NOT_MADE",
                    "selected_goal": None, "continuation": {"schema": "q3_continuation.v1", "status": "RECOVERY_ONLY",
                        "owner": {"task": receipt["actor"], "installation_ref": receipt["installation_ref"], "epoch": receipt["epoch"]},
                        "recovery": {"operation_id": operation_id, "manifest_sha256": receipt["manifest_sha256"],
                                     "candidate_commit": saved["candidate_commit"],
                                     "command": "team-bootstrap-publish", "reconcile_only": True},
                        "blockers": [{"scope": "ALL_WRITERS", "code": "TEAM_BOOTSTRAP_PENDING"}]}}
        pending = _team_pending_integration(repo)
        if pending is not None and lock_error is None:
            operation_id, integration = pending
            saved = _team_integration_manifest(_team_json(integration["manifest"]))
            if (_resume_digest(_team_json(saved)) != integration["manifest_sha256"]
                    or saved["operation_id"] != operation_id):
                raise WorkflowRuntimeError("TEAM_INTEGRATION_RECOVERY_MANIFEST_CHANGED")
            _, observed_resume, _ = _team_current(repo)
            if epoch_guard.recheck() is not None or _team_pending_integration(repo) != pending:
                raise WorkflowRuntimeError("TEAM_READ_EPOCH_CHANGED")
            # A mixed control/source tree cannot authorize ordinary planning.
            # Display the saved recovery identity using the immutable engine.
            return {"schema": TEAM_PLAN_SCHEMA, "mode": PRODUCTION_PLAN_MODE, "status": "HOLD",
                    "holds": ["TEAM_INTEGRATION_PENDING"], "run_authorized": False,
                    "writes_performed": False, "execution_ready": False, "PX_RH_CLAIM": "NOT_MADE",
                    "selected_goal": None, "continuation": {"schema": "q3_continuation.v1", "status": "RECOVERY_ONLY",
                        "saved_frontier": observed_resume["pins"]["physical_goal"],
                        "owner": {"task": saved["owner_task"], "installation_ref": saved["installation_ref"], "epoch": saved["epoch"]},
                        "recovery": {"operation_id": operation_id, "manifest_sha256": integration["manifest_sha256"],
                                     "engine": integration["engine"], "command": "team-integrate-candidate",
                                     "recover_operation": operation_id},
                        "blockers": [{"scope": "ALL_WRITERS", "code": "TEAM_INTEGRATION_PENDING"}]}}
        snapshot = build_startup_snapshot(
            repo,
            owned_paths=owned_scope,
            _epoch_guard=epoch_guard,
            _epoch_lock_error=lock_error,
        )
        if _benchmark_timing_sink is not None:
            assert startup_started is not None
            _benchmark_timing_sink.update(
                {
                    "schema": _BENCHMARK_TIMING_SCHEMA,
                    "startup_duration_ms": round(
                        (time.perf_counter() - startup_started) * 1000, 3
                    ),
                    "snapshot_constructor_calls": 1,
                }
            )
        exact_edge_pins = (
            snapshot.exact_node_pin,
            snapshot.exact_source_pin,
            snapshot.exact_theorem_pin,
            snapshot.exact_consumer_pin,
        )
        if not all(isinstance(pin, str) and pin for pin in exact_edge_pins):
            exact_edge_pins = (None, None, None, None)
        if lock_error is not None:
            registry_summary = _registry_epoch_failure(
                "NODE_REGISTRY_WRITER_EPOCH_UNAVAILABLE", lock_error
            )
        else:
            registry_summary = node_registry_v10.startup_gate_summary(
                repo,
                snapshot.selected_goal,
                owned_paths=owned_scope,
                exact_node_pin=exact_edge_pins[0],
                exact_source_pin=exact_edge_pins[1],
                exact_theorem_pin=exact_edge_pins[2],
                exact_consumer_pin=exact_edge_pins[3],
            )
            epoch_error = epoch_guard.recheck()
            if epoch_error is not None:
                snapshot = replace(
                    snapshot,
                    selected_goal=None,
                    exact_node_pin=None,
                    exact_source_pin=None,
                    exact_theorem_pin=None,
                    exact_consumer_pin=None,
                    fatal_errors=tuple(
                        dict.fromkeys((epoch_error, *snapshot.fatal_errors))
                    ),
                    next_action="STOP_FAIL_CLOSED",
                    run_authorized=False,
                )
                registry_summary = _registry_epoch_failure(
                    "NODE_REGISTRY_STARTUP_EPOCH_DRIFT", epoch_error
                )
        logical_holds = list(snapshot.fatal_errors)
        if registry_summary.get("status") != "PASS":
            logical_holds.append(str(registry_summary.get("code")))
        if snapshot.control_status != "ACTIVE":
            logical_holds.append(f"CONTROL_NOT_ACTIVE:{snapshot.control_status}")
        logical_plan = _compile_production_logical_plan(
            repo,
            snapshot=snapshot,
            registry_summary=registry_summary,
            holds=sorted(set(logical_holds)),
        )
        continuation = None
        if snapshot.team_runtime_version == 1:
            continuation = _team_continuation(repo, snapshot, owned_paths)
            if epoch_guard.recheck() is not None:
                continuation = {"status": "HOLD", "blockers": [{"scope": "SHARED_STATE", "code": "TEAM_READ_EPOCH_CHANGED"}]}
    host = {"Darwin": "CODEX_MAC", "Linux": "CODEX_LINUX"}.get(
        platform.system(), "UNSUPPORTED_HOST"
    )
    result = compile_plan_v10(
        startup_snapshot=snapshot,
        node_registry_summary=registry_summary,
        host_executor=host,
        logical_plan=logical_plan,
    )
    if continuation is not None:
        result["schema"] = TEAM_PLAN_SCHEMA
        result["continuation"] = continuation
        result["execution_ready"] = False  # Native prerequisites always require a live observation.
    return result


def render_shadow_plan_v10(plan: dict[str, Any]) -> str:
    rendered = json.dumps(plan, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    if len(rendered.encode("utf-8")) > SHADOW_PLAN_MAX_BYTES or len(
        rendered.splitlines()
    ) > SHADOW_PLAN_MAX_LINES:
        fallback = {
            "schema": SHADOW_PLAN_SCHEMA,
            "status": "FATAL",
            "holds": ["SHADOW_V10_OUTPUT_LIMIT_EXCEEDED"],
            "run_authorized": False,
            "writes_performed": False,
            "legacy_v9_authority_unchanged": True,
            "PX_RH_CLAIM": "NOT_MADE",
        }
        return json.dumps(fallback, separators=(",", ":"), sort_keys=True)
    return rendered


def render_plan_v10(plan: dict[str, Any]) -> str:
    """Render one bounded production plan without invoking any other runtime."""

    rendered = json.dumps(plan, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    limit = TEAM_PLAN_MAX_BYTES if plan.get("schema") == TEAM_PLAN_SCHEMA else SHADOW_PLAN_MAX_BYTES
    if len(rendered.encode("utf-8")) > limit or len(
        rendered.splitlines()
    ) > SHADOW_PLAN_MAX_LINES:
        fallback = {
            "schema": SHADOW_PLAN_SCHEMA,
            "status": "FATAL",
            "mode": PRODUCTION_PLAN_MODE,
            "holds": ["PRODUCTION_V10_OUTPUT_LIMIT_EXCEEDED"],
            "run_authorized": False,
            "writes_performed": False,
            "PX_RH_CLAIM": "NOT_MADE",
        }
        return json.dumps(fallback, separators=(",", ":"), sort_keys=True)
    return rendered


def _single_request_header(text: str, field: str) -> tuple[str | None, str | None]:
    matches = re.findall(rf"(?m)^{re.escape(field)}:\s*(\S+)\s*$", text)
    if not matches:
        return None, f"PROSHKA_{field}_MISSING"
    if len(matches) != 1:
        return None, f"PROSHKA_{field}_AMBIGUOUS"
    return matches[0], None


def _exploration_review_receipt(runtime: dict[str, Any]) -> dict[str, Any]:
    """Validate and summarize the canonical bounded-exploration call gate."""
    from orchestrator import spine

    try:
        spine.validate_runtime(runtime)
        active = runtime.get("active_exploration")
        phase = runtime.get("active_proshka_phase")
        if not isinstance(active, dict):
            raise spine.ControlViolation(
                "EXPLORATION_RUNTIME_MISSING", "no active bounded exploration"
            )
        if not isinstance(phase, dict) or phase.get("status") != "ACTIVE":
            raise spine.ControlViolation(
                "EXPLORATION_RUNTIME_MISSING", "no active Proshka phase"
            )
        if not spine.phase_keys_equal(active.get("phase_key"), phase.get("phase_key")):
            raise spine.ControlViolation(
                "EXPLORATION_PHASE_KEY_SMUGGLE",
                "bounded exploration and living chat have different phase keys",
            )
        exploration_id = active.get("exploration_id")
        blocker = active.get("blocker_fingerprint")
        if not isinstance(exploration_id, str) or not exploration_id.strip():
            raise spine.ControlViolation(
                "EXPLORATION_RUNTIME_MISSING", "exploration_id is missing"
            )
        if not isinstance(blocker, str) or not re.fullmatch(r"[0-9a-f]{64}", blocker):
            raise spine.ControlViolation(
                "EXPLORATION_RUNTIME_MISSING", "blocker_fingerprint is missing or invalid"
            )
        counter_fields = (
            "no_progress_streak",
            "total_cycles",
            "active_reasoning_seconds",
            "proshka_review_count",
        )
        if any(not isinstance(active.get(field), int) for field in counter_fields):
            raise spine.ControlViolation(
                "EXPLORATION_RUNTIME_MISSING", "bounded-exploration counters are incomplete"
            )
        decision = spine.stall_decision(
            no_progress_streak=active["no_progress_streak"],
            total_cycles=active["total_cycles"],
            active_reasoning_seconds=active["active_reasoning_seconds"],
            proshka_review_count=active["proshka_review_count"],
        )
        if decision.get("state") != "HARD_STALL" or decision.get("proshka_call") is not True:
            raise spine.ControlViolation(
                "EXPLORATION_REVIEW_OUTSIDE_GATE",
                f"bounded exploration state is {decision.get('state')}",
            )
        spine.validate_exploration_review({
            "fresh_chat": False,
            "full_context_reupload": False,
            "state": decision["state"],
            "review_count_for_episode": active["proshka_review_count"],
            "review_count_for_phase_blocker": active["proshka_review_count"],
            "ordinary_goal_close_as_sole_trigger": False,
        })
    except spine.ControlViolation as exc:
        raise WorkflowRuntimeError(exc.code) from exc
    return {
        "schema": "q3_bounded_exploration_review_eligibility.v1",
        "result": "EXPLORATION_REVIEW_ALLOWED",
        "exploration_id": exploration_id,
        "phase_id": phase.get("phase_id"),
        "blocker_fingerprint": blocker,
        "no_progress_streak": active["no_progress_streak"],
        "total_cycles": active["total_cycles"],
        "proshka_review_count": active["proshka_review_count"],
    }


def _dependency_contract_receipt(
    repo: Path,
    path: Path,
    *,
    candidate: str,
    target: str,
    exact_theorem_pin: str | None = None,
    exact_consumer_pin: str | None = None,
) -> dict[str, Any]:
    from orchestrator import research_dependency_contract

    resolved = path if path.is_absolute() else repo / path
    try:
        raw = resolved.read_bytes()
        payload = _load_unique_json(resolved)
    except (OSError, StartupRuntimeError) as exc:
        raise WorkflowRuntimeError(
            f"CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:{exc}"
        ) from exc
    if not isinstance(payload, dict) or set(payload) != {
        "schema", "candidate", "target", "candidate_provenance", "contract"
    }:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:SCHEMA")
    if payload.get("schema") != DEPENDENCY_CONTRACT_RECEIPT_SCHEMA:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:SCHEMA")
    if payload.get("candidate") != candidate:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_CANDIDATE_MISMATCH")
    if payload.get("target") != target:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_TARGET_MISMATCH")
    candidate_provenance = payload.get("candidate_provenance")
    if candidate_provenance not in SUPPLIER_PROVENANCE_CLASSES:
        raise WorkflowRuntimeError(
            "CONSUMER_FIRST_CONTRACT_CANDIDATE_PROVENANCE_INVALID"
        )
    contract = payload.get("contract")
    if not isinstance(contract, dict):
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:CONTRACT")
    try:
        research_dependency_contract.validate(contract)
    except research_dependency_contract.DependencyContractError as exc:
        raise WorkflowRuntimeError(
            f"CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:{exc}"
        ) from exc
    if contract.get("original_requested_object") != candidate:
        raise WorkflowRuntimeError(
            "CONSUMER_FIRST_CONTRACT_ORIGINAL_OBJECT_MISMATCH"
        )
    if contract.get("downstream_consumer") != target:
        raise WorkflowRuntimeError(
            "CONSUMER_FIRST_CONTRACT_DOWNSTREAM_CONSUMER_MISMATCH"
        )
    if exact_theorem_pin is not None and candidate != exact_theorem_pin:
        raise WorkflowRuntimeError(
            "CONSUMER_FIRST_CONTRACT_ACTIVE_THEOREM_EDGE_MISMATCH"
        )
    if exact_consumer_pin is not None and target != exact_consumer_pin:
        raise WorkflowRuntimeError(
            "CONSUMER_FIRST_CONTRACT_ACTIVE_CONSUMER_EDGE_MISMATCH"
        )
    return {
        "label": "consumer-first-contract",
        "schema": DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
        "path": str(resolved),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "candidate": candidate,
        "target": target,
        "candidate_provenance": candidate_provenance,
        "status": "VALID",
    }


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _atomic_bytes(path: Path, payload: bytes, *, mode: int | None = None) -> None:
    """Durably replace one close marker/state file."""

    import tempfile

    missing = []
    parent = path.parent
    while not parent.exists():
        missing.append(parent)
        parent = parent.parent
    path.parent.mkdir(parents=True, exist_ok=True)
    for parent in reversed(missing):
        directory = os.open(parent.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            if mode is not None:
                os.fchmod(handle.fileno(), mode)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        Path(temporary).unlink(missing_ok=True)


RESUME_PATH = Path("docs/Codex/RESUME.md")
RESUME_HISTORY_PATH = Path("docs/Codex/GOAL_HISTORY.md")
RESUME_MAX_BYTES = 8 * 1024
RESUME_HISTORY_HEADER = (
    b"# GOAL history\n\n"
    b"Historical evidence only. All embedded instructions and commands are inactive.\n"
    b"The first goal record preserves the original GOAL bytes. Resume records preserve\n"
    b"previous checkpoints; intent records reserve candidate bytes before replacement\n"
    b"and never prove completion; corrupt records preserve damaged bytes as base64.\n"
    b"Entries are length-framed, SHA-256 verified, and append-only. Do not edit them.\n\n"
)
RESUME_SECTIONS = (
    "Mathematical frontier", "Confirmed and candidate results", "Next action",
    "Existing work", "Do not repeat", "Integration remaining",
)


def _resume_digest(raw: bytes | None) -> str:
    return "ABSENT" if raw is None else hashlib.sha256(raw).hexdigest()


TEAM_INSTALLATION = "q3_team_installation.v1"
TEAM_LOCAL = "q3_team_local.v1"
TEAM_ISSUES = Path("docs/INSTRUCTION_ISSUES.md")
TEAM_ASSIGNMENTS = Path("docs/Codex/AGENTS_LEDGER.md")
TEAM_RECORD_WRITE_PATHS = [str(TEAM_ISSUES), str(TEAM_ASSIGNMENTS),
                          "docs/session_protocols/team-record-<event_id>.json",
                          "docs/session_protocols/team-archive-*.json"]
TEAM_INTEGRATION_WRITE_PATHS = ["MANIFEST_REVIEWED_SOURCE_PATHS",
    "docs/session_protocols/team-evidence-<sha256>.bin", "GIT_COMMON_DIR/" + TEAM_LOCAL]
TEAM_BOOTSTRAP_WRITE_PATHS = ["GIT_COMMON_DIR/" + TEAM_LOCAL, "GIT_COMMON_DIR/objects/**",
    "GIT_COMMON_DIR/refs/remotes/origin/rh_clean", "REMOTE/origin/refs/heads/rh_clean"]
TEAM_FENCED_CALLS = frozenset({
    "workflow-close-node", "workflow-search-evidence", "workflow-session-close", "workflow-phase-close",
    "workflow-resume-checkpoint", "bind-request", "workflow-team-record", "workflow-team-local-init",
    "workflow-team-observe-remote", "workflow-team-reserve-effect", "workflow-team-confirm-effect",
    "workflow-team-watch-intent", "workflow-team-observe-native", "workflow-team-integrate-candidate",
    "workflow-team-bootstrap-publish",
    "slack-manual-chat-reconciliation", "bridge-observed-phase-repair",
})
TEAM_NATIVE_EFFECTS = frozenset({
    "dispatch-proshka", "agent-launch", "publication", "calculation",
    "aristotle-submit", "paper-ingest",
})
TEAM_STAGES = (
    "request_preparation", "request_review", "delivery", "receipt",
    "independent_review", "parent_check", "acceptance", "publication",
)
TEAM_OWNER_STATES = {
    "ACTIVE", "HANDOFF_INTENT", "HANDOFF_QUIESCED", "WATCH_RECONCILE_PENDING",
    "RELEASED", "CLAIM_PENDING", "CLAIM_ABORTED",
}
TEAM_READ_MAX = 4 * 1024 * 1024
TEAM_PLAN_MAX_BYTES = 16 * 1024


def _team_hex(value: object, size: int = 64) -> bool:
    return isinstance(value, str) and re.fullmatch("[0-9a-f]{" + str(size) + "}", value) is not None


def _team_json(value: object) -> bytes:
    # Runtime-generated closed records contain only JSON integers/strings/containers.
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":"), allow_nan=False) + "\n").encode("utf-8")


def _team_enabled(repo: Path) -> bool:
    _team_pending_guard(repo)
    from orchestrator.startup_runtime import validate_battle_v10_control

    return validate_battle_v10_control(repo).team_runtime_version == 1


def _team_registered(repo: Path, command: str, paths: list[str], *, bootstrap_id: str | None = None) -> None:
    _team_pending_guard(repo, bootstrap_id=bootstrap_id)
    entry = load_tool_index(repo / TOOLS).get("workflow-" + command, {})
    if (entry.get("status") != "ENABLED" or entry.get("writes") is not True
            or entry.get("write_paths") != paths):
        raise WorkflowRuntimeError("TEAM_TOOL_NOT_REGISTERED:" + command)


def _team_writer_inventory(repo: Path) -> dict[str, Any]:
    from orchestrator.routeb_goal_state import load_unique_yaml

    document = load_unique_yaml((repo / TOOLS).read_text(encoding="utf-8"))
    inventory = document.get("team_runtime_writer_inventory")
    if not isinstance(inventory, dict) or set(inventory) != {"fenced", "inherited_only", "isolated_only"}:
        raise WorkflowRuntimeError("TEAM_WRITER_INVENTORY_MISSING")
    groups = list(inventory.values())
    if any(not isinstance(group, list) or any(not isinstance(item, str) for item in group) for group in groups):
        raise WorkflowRuntimeError("TEAM_WRITER_INVENTORY_INVALID")
    names = [name for group in groups for name in group]
    callable_writers = {
        name for name, entry in load_tool_index(repo / TOOLS).items()
        if entry.get("status") in {"ENABLED", "AVAILABLE", "DEGRADED"}
        and entry.get("writes") is True
    }
    if (len(names) != len(set(names)) or set(names) != callable_writers
            or set(inventory["fenced"]) != TEAM_FENCED_CALLS):
        raise WorkflowRuntimeError("TEAM_WRITER_INVENTORY_INCOMPLETE_OR_DUPLICATE")
    return inventory


def _team_private_read(repo: Path, name: str) -> dict[str, Any] | None:
    common = _git_common_dir(repo)
    if Path(name).name != name:
        raise WorkflowRuntimeError("TEAM_LOCAL_NAME_INVALID")
    path = common / name
    try:
        before = path.lstat()
    except FileNotFoundError:
        return None
    if not stat.S_ISREG(before.st_mode) or stat.S_IMODE(before.st_mode) != 0o600:
        raise WorkflowRuntimeError("TEAM_LOCAL_PRIVATE_FILE_REQUIRED:" + name)
    if before.st_size > TEAM_READ_MAX:
        raise WorkflowRuntimeError("TEAM_LOCAL_READ_LIMIT:" + name)
    result = _load_unique_json(path)
    after = path.lstat()
    # Reading can change atime; it is not a source mutation.
    stable_fields = ("st_dev", "st_ino", "st_mode", "st_uid", "st_gid", "st_size", "st_mtime_ns", "st_ctime_ns")
    if (any(getattr(before, key) != getattr(after, key) for key in stable_fields)
            or path.read_bytes() != _team_json(result)):
        raise WorkflowRuntimeError("TEAM_LOCAL_CORRUPT_OR_CHANGED:" + name)
    return result


def _team_pending_integration(repo: Path) -> tuple[str, dict[str, Any]] | None:
    """Read the existing marker independently of mutable control and identity."""
    try:
        (repo / ".git").lstat()
    except FileNotFoundError:
        # A non-repository has no common-dir operation marker. Its ordinary
        # writer/startup checks retain their own missing-repository behavior.
        return
    local = _team_private_read(repo, TEAM_LOCAL)
    if local is None:
        return
    operations = local.get("operations")
    if not isinstance(operations, dict):
        raise WorkflowRuntimeError("TEAM_LOCAL_BINDING_INVALID")
    pending = []
    for key, receipt in operations.items():
        integration = receipt.get("integration") if isinstance(receipt, dict) else None
        if integration is not None:
            if (not isinstance(integration, dict) or integration.get("state") not in {"PENDING", "COMPLETE"}
                    or receipt.get("state") != ("RESERVED" if integration["state"] == "PENDING" else "CONFIRMED")):
                raise WorkflowRuntimeError("TEAM_INTEGRATION_RECEIPT_INVALID")
            if integration["state"] == "PENDING":
                pending.append((key, integration))
    if len(pending) > 1:
        raise WorkflowRuntimeError("TEAM_INTEGRATION_PENDING_AMBIGUOUS")
    return pending[0] if pending else None


def _team_pending_bootstrap(repo: Path) -> tuple[str, dict[str, Any]] | None:
    if not (repo / ".git").exists():
        return None
    local = _team_private_read(repo, TEAM_LOCAL)
    if local is None:
        return None
    operations = local.get("operations")
    if not isinstance(operations, dict):
        raise WorkflowRuntimeError("TEAM_LOCAL_BINDING_INVALID")
    pending = []
    for key, receipt in operations.items():
        saved = receipt.get("bootstrap") if isinstance(receipt, dict) else None
        if saved is None:
            continue
        if (not isinstance(saved, dict) or saved.get("schema") != "q3_team_bootstrap_publish.v1"
                or saved.get("operation_id") != key or receipt.get("state") not in {"RESERVED", "UNKNOWN", "CONFIRMED"}
                or receipt.get("manifest_sha256") != _resume_digest(_team_json(saved))):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_RESERVATION_INVALID")
        if receipt["state"] in {"RESERVED", "UNKNOWN"}:
            pending.append((key, receipt))
    if len(pending) > 1:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_PENDING_AMBIGUOUS")
    return pending[0] if pending else None


def _team_pending_guard(repo: Path, *, operation_id: str | None = None, bootstrap_id: str | None = None) -> None:
    bootstrap = _team_pending_bootstrap(repo)
    if bootstrap is not None and bootstrap[0] != bootstrap_id:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_PENDING:" + bootstrap[0])
    pending = _team_pending_integration(repo)
    if pending is not None and pending[0] != operation_id:
        raise WorkflowRuntimeError("TEAM_INTEGRATION_PENDING:" + pending[0])


def _team_installation(repo: Path) -> dict[str, str]:
    data = _team_private_read(repo, TEAM_INSTALLATION)
    if data is None:
        raise WorkflowRuntimeError("INSTALLATION_RECOVERY_REQUIRED:run team-local-init for a new installation; restore private identity for an existing owner")
    if (set(data) != {"schema", "installation_secret", "installation_ref"}
            or data["schema"] != TEAM_INSTALLATION
            or not _team_hex(data["installation_secret"])):
        raise WorkflowRuntimeError("TEAM_INSTALLATION_INVALID")
    ref = hashlib.sha256(b"q3-team-installation-v1\0" + bytes.fromhex(data["installation_secret"])).hexdigest()
    if ref != data["installation_ref"]:
        raise WorkflowRuntimeError("TEAM_INSTALLATION_REFERENCE_MISMATCH")
    # Never return the private component to a caller or receipt.
    return {"installation_ref": ref}


def team_local_init(repo: Path) -> dict[str, Any]:
    """Create a clone-local namespace, never acquire project execution ownership."""
    _team_registered(repo, "team-local-init", ["GIT_COMMON_DIR/q3-three-body.writer.lock", "GIT_COMMON_DIR/" + TEAM_INSTALLATION])
    common = _git_common_dir(repo)
    lock = common / "q3-three-body.writer.lock"
    try:
        fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, "O_NOFOLLOW", 0), 0o600)
    except FileExistsError:
        pass
    else:
        with os.fdopen(fd, "wb") as handle:
            handle.flush()
            os.fsync(handle.fileno())
        _resume_sync(lock)
    with _execution_writer_epoch(repo) as epoch:
        current = _team_private_read(repo, TEAM_INSTALLATION)
        if current is not None:
            return {"status": "NOOP", **_team_installation(repo), "execution_acquired": False}
        # An existing owner on this host must restore its identity, not regenerate it.
        if _team_private_read(repo, TEAM_LOCAL) is not None:
            raise WorkflowRuntimeError("INSTALLATION_RECOVERY_REQUIRED:local bindings already exist")
        secret = secrets.token_bytes(32)
        ref = hashlib.sha256(b"q3-team-installation-v1\0" + secret).hexdigest()
        current_resume = _resume_file(repo, RESUME_PATH)
        if current_resume is not None:
            data, _ = _resume_document(current_resume)
            if data.get("ownership", {}).get("installation_ref") == ref:
                raise WorkflowRuntimeError("TEAM_INSTALLATION_REFERENCE_COLLISION")
        data = {"schema": TEAM_INSTALLATION, "installation_secret": secret.hex(), "installation_ref": ref}
        path = common / TEAM_INSTALLATION
        # Exclusive creation, never overwrite even if an uncooperative writer races init.
        fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, "O_NOFOLLOW", 0), 0o600)
        with os.fdopen(fd, "wb") as handle:
            handle.write(_team_json(data))
            handle.flush()
            os.fsync(handle.fileno())
        _resume_sync(path)
        epoch.recheck()
        return {"status": "INITIALIZED", **_team_installation(repo), "execution_acquired": False}


def _team_subject(subject: object) -> None:
    if (not isinstance(subject, dict) or set(subject) != {"kind", "id", "sha256"}
            or subject["kind"] not in {"REQUEST", "VERDICT", "REPAIR", "TRANSFER", "WATCH", "ASSIGNMENT"}
            or not isinstance(subject["id"], str) or not subject["id"]
            or not _team_hex(subject["sha256"])):
        raise ValueError("typed subject")


def _team_path_hashes(values: object) -> None:
    if not isinstance(values, dict):
        raise ValueError("path/hash mapping")
    for path, digest in values.items():
        if (not isinstance(path, str) or not path or Path(path).is_absolute()
                or ".." in Path(path).parts or str(Path(path)) != path
                or not _team_hex(digest)):
            raise ValueError("relative path/hash")


def _team_document(data: dict[str, Any]) -> None:
    """Closed v2 additions; v1 archive interpretation remains unchanged."""
    if set(data) != {"schema", "revision", "observed_at", "previous_sha256", "owner_thread_id",
                     "owner_host_id", "reconciliation_pending", "recovery_from", "pins", "stages",
                     "operation", "ownership", "source_manifest"}:
        raise ValueError("v2 envelope fields")
    owner = data["ownership"]
    if (not isinstance(owner, dict) or set(owner) != {"installation_ref", "epoch", "state", "transfer"}
            or not _team_hex(owner["installation_ref"])
            or type(owner["epoch"]) is not int or owner["epoch"] < 1
            or owner["state"] not in TEAM_OWNER_STATES):
        raise ValueError("ownership")
    transfer = owner["transfer"]
    if transfer is not None:
        if (not isinstance(transfer, dict)
                or set(transfer) != {"id", "mode", "from_ref", "from_thread", "to_ref", "to_thread", "predecessor_commit", "evidence"}
                or not isinstance(transfer["id"], str) or not transfer["id"]
                or transfer["mode"] not in {"SAME_INSTALLATION", "CROSS_INSTALLATION"}
                or any(not _team_hex(transfer[key]) for key in ("from_ref", "to_ref"))
                or any(not re.fullmatch(r"[0-9a-f-]{36}", str(transfer[key])) for key in ("from_thread", "to_thread"))
                or (transfer["predecessor_commit"] is not None and not _team_hex(transfer["predecessor_commit"], 40))):
            raise ValueError("transfer")
        _team_path_hashes(transfer["evidence"])
    elif owner["state"] != "ACTIVE":
        raise ValueError("pending owner requires transfer")
    _team_path_hashes(data["source_manifest"])
    if not data["source_manifest"]:
        raise ValueError("source_manifest empty")
    pins = data["pins"]
    if set(pins) != {"head", "physical_goal", "source_commit", "request_id", "phase_id", "phase_key", "request"}:
        raise ValueError("v2 pins")
    from orchestrator import spine
    try:
        spine.validate_phase_key(pins["phase_key"])
    except (ValueError, RuntimeError) as exc:
        raise ValueError("phase_key") from exc
    request = pins["request"]
    if (not isinstance(request, dict) or set(request) != {"path", "commit", "blob", "sha256", "boundary_id", "conversation_id"}
            or not _team_hex(request["commit"], 40) or not _team_hex(request["blob"], 40)
            or not isinstance(request["boundary_id"], str) or not request["boundary_id"]
            or not isinstance(request["conversation_id"], str) or not request["conversation_id"]):
        raise ValueError("request pins")
    _team_path_hashes({request["path"]: request["sha256"]})
    if set(data["stages"]) != set(TEAM_STAGES):
        raise ValueError("typed stages")
    for name, stage in data["stages"].items():
        if (not isinstance(stage, dict) or set(stage) != {"subject", "state", "evidence", "source_sha256", "checked_by"}
                or stage["state"] not in {"NOT_STARTED", "PENDING", "UNKNOWN", "DONE", "REJECTED"}):
            raise ValueError("stage " + name)
        _team_subject(stage["subject"])
        _team_path_hashes(stage["evidence"])
        if stage["state"] in {"DONE", "REJECTED"} and not stage["evidence"]:
            raise ValueError("stage evidence " + name)
        if not _team_hex(stage["source_sha256"]) or (stage["checked_by"] is not None and not isinstance(stage["checked_by"], str)):
            raise ValueError("stage verification identity " + name)
        if stage["state"] == "DONE" and (stage["source_sha256"] != _resume_digest(_team_json(data["source_manifest"])) or not stage["checked_by"]):
            raise ValueError("stage source verification stale " + name)
        required_kind = "REQUEST" if name in TEAM_STAGES[:3] else "VERDICT"
        if stage["subject"]["kind"] != required_kind:
            raise ValueError("stage subject type " + name)
        if required_kind == "REQUEST" and (stage["subject"]["id"] != pins["request_id"] or stage["subject"]["sha256"] != request["sha256"]):
            raise ValueError("stage bound request " + name)
    for stage_name, prerequisites in {
        "request_review": ("request_preparation",),
        "delivery": ("request_review",),
        "independent_review": ("receipt",),
        "parent_check": ("receipt",),
        "acceptance": ("independent_review", "parent_check"),
        "publication": ("acceptance",),
    }.items():
        stage = data["stages"][stage_name]
        if stage["state"] == "DONE":
            for name in prerequisites:
                prior = data["stages"][name]
                if prior["state"] != "DONE" or prior["subject"] != stage["subject"]:
                    raise ValueError("stage prerequisite " + stage_name + ":" + name)
    operation = data["operation"]
    if set(operation) != {"kind", "state", "id", "evidence", "subject", "command", "inputs"}:
        raise ValueError("operation fields")
    _team_subject(operation["subject"])
    _team_path_hashes(operation["inputs"])
    if not isinstance(operation["command"], str) or not operation["command"]:
        raise ValueError("operation command")


def _team_verify_paths(repo: Path, paths: dict[str, str]) -> None:
    for relative, expected in paths.items():
        actual = _resume_file(repo, Path(relative))
        if _resume_digest(actual) != expected:
            raise WorkflowRuntimeError("TEAM_SOURCE_CHANGED:" + relative)


def _team_current(repo: Path) -> tuple[bytes, dict[str, Any], str]:
    raw = _resume_file(repo, RESUME_PATH)
    if raw is None:
        raise WorkflowRuntimeError("TEAM_RESUME_MISSING")
    data, body = _resume_document(raw)
    if data["schema"] != "q3_resume.v2":
        raise WorkflowRuntimeError("TEAM_RESUME_MIGRATION_REQUIRED")
    history = _resume_file(repo, RESUME_HISTORY_PATH)
    if history is None or len(history) > TEAM_READ_MAX:
        raise WorkflowRuntimeError("TEAM_HISTORY_UNAVAILABLE_OR_READ_LIMIT")
    if ("intent", data["revision"], raw) not in _resume_history(history).values():
        raise WorkflowRuntimeError("RESUME_CURRENT_CHECKSUM_MISMATCH")
    return raw, data, body


def _team_actor(repo: Path, owner: dict[str, Any]) -> None:
    local_ref = _team_installation(repo)["installation_ref"]
    if (owner["ownership"]["installation_ref"] != local_ref
            or owner["owner_thread_id"] != os.environ.get("CODEX_THREAD_ID")):
        raise WorkflowRuntimeError("TEAM_OBSERVER_ONLY:owner installation/task mismatch")


def _team_local(repo: Path) -> dict[str, Any]:
    ref = _team_installation(repo)["installation_ref"]
    value = _team_private_read(repo, TEAM_LOCAL)
    if value is None:
        return {"schema": TEAM_LOCAL, "installation_ref": ref, "operations": {}, "watch": None, "epoch_floor": 0}
    if (set(value) != {"schema", "installation_ref", "operations", "watch", "epoch_floor"}
            or value["schema"] != TEAM_LOCAL or value["installation_ref"] != ref
            or not isinstance(value["operations"], dict)
            or type(value["epoch_floor"]) is not int):
        raise WorkflowRuntimeError("TEAM_LOCAL_BINDING_INVALID")
    return value


def _team_local_save(repo: Path, before: dict[str, Any], after: dict[str, Any], epoch: _ExecutionWriterEpoch) -> None:
    if _team_local(repo) != before:
        raise WorkflowRuntimeError("TEAM_LOCAL_PREIMAGE_CHANGED")
    payload = _team_json(after)
    if len(payload) > TEAM_READ_MAX:
        raise WorkflowRuntimeError("TEAM_LOCAL_READ_LIMIT:archive completed local receipts before adding operations")
    epoch.recheck()
    _atomic_bytes(_git_common_dir(repo) / TEAM_LOCAL, payload)
    if _team_private_read(repo, TEAM_LOCAL) != after:
        raise WorkflowRuntimeError("TEAM_LOCAL_READBACK_MISMATCH")


def _team_local_operation(repo: Path, operation_id: str) -> dict[str, Any] | None:
    return _team_local(repo)["operations"].get(operation_id)


def _team_git(repo: Path, *args: str) -> bytes:
    completed = subprocess.run(["git", *args], cwd=repo, capture_output=True, timeout=45, check=False)
    if completed.returncode:
        # Transport errors may contain credential-bearing URLs; do not echo stderr.
        raise WorkflowRuntimeError("TEAM_GIT_OBSERVATION_FAILED:" + args[0])
    return completed.stdout


def _team_remote_checkpoint(repo: Path) -> tuple[str, bytes, dict[str, Any]]:
    """Explicit network observation, never called by plan or while holding flock."""
    def remote_tip() -> str:
        lines = _team_git(repo, "ls-remote", "--exit-code", "origin", "refs/heads/rh_clean").decode().splitlines()
        if len(lines) != 1:
            raise WorkflowRuntimeError("TEAM_REMOTE_BRANCH_AMBIGUOUS")
        commit, ref = lines[0].split("\t")
        if ref != "refs/heads/rh_clean" or not _team_hex(commit, 40):
            raise WorkflowRuntimeError("TEAM_REMOTE_REF_INVALID")
        return commit

    commit = remote_tip()
    # Fetch only objects: no FETCH_HEAD, worktree, index, branch or tracking-ref mutation.
    _team_git(repo, "fetch", "--no-tags", "--no-write-fetch-head", "origin", commit)
    raw = _team_git(repo, "show", commit + ":" + str(RESUME_PATH))
    data, _ = _resume_document(raw)
    if remote_tip() != commit:
        raise WorkflowRuntimeError("TEAM_REMOTE_CHANGED_DURING_OBSERVATION")
    return commit, raw, data


def _team_remote(repo: Path) -> tuple[str, bytes, dict[str, Any]]:
    commit, raw, data = _team_remote_checkpoint(repo)
    if data["schema"] != "q3_resume.v2":
        raise WorkflowRuntimeError("TEAM_REMOTE_CHANGED_OR_UNMIGRATED")
    return commit, raw, data


def _team_bootstrap_endpoint(repo: Path) -> str:
    fetch_urls = _team_git(repo, "remote", "get-url", "--all", "origin").splitlines()
    push_urls = _team_git(repo, "remote", "get-url", "--push", "--all", "origin").splitlines()
    mirror = _team_git(repo, "config", "--type=bool", "--default=false", "--get", "remote.origin.mirror").strip()
    if len(fetch_urls) != 1 or push_urls != fetch_urls or mirror != b"false":
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_SINGLE_ORIGIN_ENDPOINT_REQUIRED")
    # Endpoint strings may contain credentials and never enter output or receipts.
    return _resume_digest(fetch_urls[0])


def _team_bootstrap_manifest(
    repo: Path, raw: bytes, data: dict[str, Any], remote_commit: str,
    remote_raw: bytes, remote_data: dict[str, Any], candidate: str,
) -> dict[str, Any]:
    """Validate the initial migration and bind every committed changed byte."""
    operation = data["operation"]
    if (remote_data["schema"] != "q3_resume.v1"
            or any(remote_data[k] != data[k] for k in ("owner_thread_id", "owner_host_id"))
            or any(remote_data["pins"][k] != data["pins"][k] for k in
                   ("physical_goal", "source_commit", "request_id", "phase_id"))):
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_REMOTE_OWNER_OR_PINS_CHANGED")
    if (operation["kind"] != "PUBLISH" or operation["state"] != "INTENT"
            or operation["command"] != "workflow-team-bootstrap-publish"
            or not operation["inputs"]
            or operation["subject"] != {"kind": "REPAIR", "id": operation["id"],
                                      "sha256": _resume_digest(_team_json(operation["inputs"]))}):
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_EXACT_INTENT_REQUIRED")
    _team_git(repo, "merge-base", "--is-ancestor", remote_commit, candidate)
    chain = _team_git(repo, "rev-list", "--reverse", "--parents", remote_commit + ".." + candidate).decode().splitlines()
    parent = remote_commit
    parents = []
    for row in chain:
        parts = row.split()
        if len(parts) != 2 or parts[1] != parent:
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_LINEAR_ANCESTRY_REQUIRED")
        parents.append({"commit": parts[0], "parent": parts[1]})
        parent = parts[0]
    if not parents or parent != candidate:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_NEW_CANDIDATE_REQUIRED")
    history = _resume_file(repo, RESUME_HISTORY_PATH)
    remote_history = _team_git(repo, "show", remote_commit + ":" + str(RESUME_HISTORY_PATH))
    _resume_history(remote_history)
    if (history is None or not history.startswith(remote_history)
            or _team_git(repo, "show", candidate + ":" + str(RESUME_PATH)) != raw
            or _team_git(repo, "show", candidate + ":" + str(RESUME_HISTORY_PATH)) != history):
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_COMMITTED_HISTORY_OR_CHECKPOINT_CHANGED")
    versions = {v: b for kind, v, b in _resume_history(history).values() if kind in {"resume", "intent"}}
    start = remote_data["revision"]
    if versions.get(start) != remote_raw or versions.get(data["revision"]) != raw:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_REMOTE_HISTORY_MISSING")
    previous = remote_raw
    snapshots = {}
    for revision in range(start, data["revision"] + 1):
        payload = versions[revision]
        value, _ = _resume_document(payload)
        if revision != start and value["previous_sha256"] != _resume_digest(previous):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_HISTORY_CHAIN_CHANGED")
        if (any(value[k] != data[k] for k in ("owner_thread_id", "owner_host_id"))
                or any(value["pins"][k] != data["pins"][k] for k in
                       ("physical_goal", "source_commit", "request_id", "phase_id"))):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_HISTORY_OWNER_OR_PINS_CHANGED")
        snapshots[revision] = value
        previous = payload
    installs = [v for v, value in snapshots.items() if value["schema"] == "q3_resume.v1"
                and value["operation"]["id"] == operation["id"] + ":local-install"
                and value["operation"]["kind"] == "PUBLISH" and value["operation"]["state"] == "INTENT"]
    if len(installs) != 1 or installs[0] - 1 not in snapshots:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_LOCAL_INSTALL_INTENT_REQUIRED")
    install_revision = installs[0]
    if snapshots[install_revision - 1]["operation"]["state"] not in {"NONE", "CONFIRMED"}:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_UNRESOLVED_PREDECESSOR")
    confirmed = snapshots.get(install_revision + 1, {})
    migrated = snapshots.get(install_revision + 2, {})
    local_op = confirmed.get("operation", {})
    if (confirmed.get("schema") != "q3_resume.v1" or local_op.get("kind") != "PUBLISH"
            or local_op.get("id") != operation["id"] + ":local-install" or local_op.get("state") != "CONFIRMED"
            or migrated.get("schema") != "q3_resume.v2"
            or any(migrated["operation"].get(k) != local_op[k] for k in ("kind", "id", "state"))):
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_LOCAL_INSTALL_CONFIRMATION_REQUIRED")
    commits = [line.removeprefix("bootstrap_local_commit:") for line in local_op["evidence"]
               if line.startswith("bootstrap_local_commit:")]
    if len(commits) != 1 or not _team_hex(commits[0], 40) or commits[0] not in {row["commit"] for row in parents}:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_LOCAL_COMMIT_REQUIRED")
    if _team_git(repo, "show", commits[0] + ":" + str(RESUME_PATH)) != versions[install_revision]:
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_LOCAL_COMMIT_INTENT_MISMATCH")
    metadata = {str(RESUME_PATH), str(RESUME_HISTORY_PATH)}
    if metadata & set(operation["inputs"]):
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_SELF_REFERENTIAL_INPUTS")
    changed = _team_git(repo, "diff", "--name-only", "--no-renames", "-z", remote_commit, candidate, "--").decode().split("\0")[:-1]
    if changed != sorted(set(operation["inputs"]) | metadata):
        raise WorkflowRuntimeError("TEAM_BOOTSTRAP_SCOPE_MISMATCH")
    files = []
    for path in changed:
        if ("\x00" in path or path.startswith("-") or Path(path).is_absolute()
                or str(Path(path)) != path or ".." in Path(path).parts
                or any(part.startswith(".git") for part in Path(path).parts)):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_PATH_INVALID")
        before, before_mode = _team_integration_blob(repo, remote_commit, path)
        after, mode = _team_integration_blob(repo, candidate, path)
        if after is None:
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_DELETION_FORBIDDEN:" + path)
        if (path in operation["inputs"] and _resume_digest(after) != operation["inputs"][path]
                or _resume_file(repo, Path(path)) != after
                or (0o755 if (repo / path).stat().st_mode & 0o111 else 0o644) != mode):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_INPUT_CHANGED:" + path)
        files.append({"path": path, "before_sha256": _resume_digest(before), "sha256": _resume_digest(after),
                      "before_mode": before_mode, "mode": mode})
    for row in parents:
        changes = _team_git(repo, "diff", "--name-only", "--no-renames", "-z",
                            row["parent"], row["commit"], "--").decode().split("\0")[:-1]
        if not set(changes).issubset(changed):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_INTERMEDIATE_SCOPE_CHANGED")
        checkpoint = _team_git(repo, "show", row["commit"] + ":" + str(RESUME_PATH))
        value, _ = _resume_document(checkpoint)
        if versions.get(value["revision"]) != checkpoint:
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_INTERMEDIATE_CHECKPOINT_CHANGED")
        for path in changes:
            content, mode = _team_integration_blob(repo, row["commit"], path)
            expected_mode = next(item["mode"] for item in files if item["path"] == path)
            if content is None or mode != expected_mode or (path in operation["inputs"] and _resume_digest(content) != operation["inputs"][path]):
                raise WorkflowRuntimeError("TEAM_BOOTSTRAP_INTERMEDIATE_SOURCE_UNREVIEWED:" + path)
    return {"schema": "q3_team_bootstrap_publish.v1", "operation_id": operation["id"],
            "branch": "refs/heads/rh_clean", "remote_commit": remote_commit,
            "remote_resume_sha256": _resume_digest(remote_raw), "remote_history_sha256": _resume_digest(remote_history),
            "candidate_commit": candidate, "candidate_resume_sha256": _resume_digest(raw),
            "parents": parents, "inputs_sha256": operation["subject"]["sha256"], "files": files}


def team_bootstrap_publish(
    repo: Path, *, operation_id: str, expected_head: str | None = None,
    expected_remote_commit: str | None = None, expected_remote_resume_sha256: str | None = None,
    reconcile_only: bool = False,
) -> dict[str, Any]:
    """Reserve first publication before transport; every retry only observes it."""
    _team_registered(repo, "team-bootstrap-publish", TEAM_BOOTSTRAP_WRITE_PATHS, bootstrap_id=operation_id)
    if not operation_id or len(operation_id) > 140:
        raise WorkflowRuntimeError("TEAM_OPERATION_ID_INVALID")
    with _execution_writer_epoch(repo, bootstrap_operation=operation_id):
        raw, data, _ = _team_current(repo)
        _team_actor(repo, data)
        local = _team_local(repo)
        prior = local["operations"].get(operation_id)
        if (data["ownership"]["state"] != "ACTIVE" or data["ownership"]["epoch"] != 1
                or data["ownership"]["transfer"] is not None or data["reconciliation_pending"]
                or os.environ.get("Q3_OWNER_EPOCH") != "1" or local["epoch_floor"] > 1):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_INITIAL_OWNER_REQUIRED")
        if prior is not None:
            manifest = prior.get("bootstrap")
            if (not isinstance(manifest, dict) or manifest.get("schema") != "q3_team_bootstrap_publish.v1"
                    or prior.get("manifest_sha256") != _resume_digest(_team_json(manifest))
                    or prior.get("actor") != data["owner_thread_id"] or prior.get("epoch") != 1
                    or prior.get("installation_ref") != data["ownership"]["installation_ref"]
                    or manifest.get("operation_id") != operation_id or manifest.get("branch") != "refs/heads/rh_clean"):
                raise WorkflowRuntimeError("TEAM_BOOTSTRAP_RESERVATION_INVALID")
            for argument, key in ((expected_head, "candidate_commit"), (expected_remote_commit, "remote_commit"),
                                  (expected_remote_resume_sha256, "remote_resume_sha256")):
                if argument is not None and argument != manifest[key]:
                    raise WorkflowRuntimeError("TEAM_BOOTSTRAP_ARGUMENT_DRIFT")
            if prior["state"] == "CONFIRMED":
                return {"status": "CONFIRMED", "operation_id": operation_id, "push_attempted": False,
                        "candidate_commit": manifest["candidate_commit"], "writes_performed": False}
            if prior["state"] not in {"RESERVED", "UNKNOWN"}:
                raise WorkflowRuntimeError("TEAM_BOOTSTRAP_RESERVATION_INVALID")
        elif reconcile_only:
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_ORIGINAL_RESERVATION_REQUIRED")
    push_attempted = False
    if prior is None:
        if not (_team_hex(expected_head, 40) and _team_hex(expected_remote_commit, 40)
                and _team_hex(expected_remote_resume_sha256)):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_EXACT_ARGUMENTS_REQUIRED")
        endpoint = _team_bootstrap_endpoint(repo)
        remote_commit, remote_raw, remote_data = _team_remote_checkpoint(repo)
        if remote_commit != expected_remote_commit or _resume_digest(remote_raw) != expected_remote_resume_sha256:
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_REMOTE_PREIMAGE_CHANGED")
        with _execution_writer_epoch(repo, bootstrap_operation=operation_id) as epoch:
            if team_guard(repo, command="workflow-team-bootstrap-publish", paths=[]) is None:
                raise WorkflowRuntimeError("TEAM_RUNTIME_NOT_ACTIVATED")
            if (live_plan_v10(repo, owned_paths=[], _writer_epoch=epoch).get("status") == "FATAL"
                    or _resume_file(repo, RESUME_PATH) != raw or _team_local(repo) != local
                    or _team_git(repo, "rev-parse", "HEAD").decode().strip() != expected_head
                    or data["operation"]["id"] != operation_id or _team_bootstrap_endpoint(repo) != endpoint):
                raise WorkflowRuntimeError("TEAM_BOOTSTRAP_LOCAL_PREIMAGE_CHANGED")
            if any(item.get("bootstrap") or item.get("state") in {"RESERVED", "UNKNOWN"}
                   for item in local["operations"].values()):
                raise WorkflowRuntimeError("TEAM_BOOTSTRAP_EXISTING_EFFECT_REQUIRES_RECONCILIATION")
            manifest = _team_bootstrap_manifest(repo, raw, data, remote_commit, remote_raw, remote_data, expected_head)
            _team_verify_paths(repo, data["source_manifest"])
            _team_verify_paths(repo, data["operation"]["inputs"])
            receipt = {"schema": "q3_team_bootstrap_reservation.v1", "state": "RESERVED", "actor": data["owner_thread_id"],
                       "epoch": 1, "installation_ref": data["ownership"]["installation_ref"],
                       "origin_sha256": endpoint,
                       "checkpoint_sha256": _resume_digest(raw), "bootstrap": manifest,
                       "manifest_sha256": _resume_digest(_team_json(manifest)), "evidence": {}}
            # Recheck every input after the potentially lengthy history/tree validation.
            if (_resume_file(repo, RESUME_PATH) != raw or _team_git(repo, "rev-parse", "HEAD").decode().strip() != expected_head
                    or _team_bootstrap_manifest(repo, raw, data, remote_commit, remote_raw, remote_data, expected_head) != manifest):
                raise WorkflowRuntimeError("TEAM_BOOTSTRAP_LOCAL_PREIMAGE_CHANGED")
            _team_local_save(repo, local, {**local, "epoch_floor": 1,
                "operations": {**local["operations"], operation_id: receipt}}, epoch)
        # No caller can re-enter the push after this durable reservation, even
        # if this process dies before calling Git or before observing its result.
        try:
            _team_git(repo, "merge-base", "--is-ancestor", expected_remote_commit, expected_head)
            push_attempted = True
            _team_git(repo, "push", "--no-follow-tags", "--recurse-submodules=no",
                      "origin", expected_head + ":refs/heads/rh_clean")
        except (WorkflowRuntimeError, OSError, subprocess.SubprocessError):
            pass  # Only independently observed remote bytes may confirm the effect.
    else:
        if _team_bootstrap_endpoint(repo) != prior.get("origin_sha256"):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_ORIGIN_CHANGED")
    try:
        observed_commit, observed_raw, _ = _team_remote_checkpoint(repo)
        observed = {"remote_commit": observed_commit, "remote_resume_sha256": _resume_digest(observed_raw)}
    except (WorkflowRuntimeError, OSError, subprocess.SubprocessError):
        observed = {"remote_commit": None, "remote_resume_sha256": None}
    state = ("CONFIRMED" if observed["remote_commit"] == manifest["candidate_commit"]
             and observed["remote_resume_sha256"] == manifest["candidate_resume_sha256"] else "UNKNOWN")
    with _execution_writer_epoch(repo, bootstrap_operation=operation_id) as epoch:
        _, current, _ = _team_current(repo)
        _team_actor(repo, current)
        local = _team_local(repo)
        prior = local["operations"].get(operation_id)
        if (prior is None or prior.get("manifest_sha256") != _resume_digest(_team_json(manifest))
                or prior.get("bootstrap") != manifest or prior.get("epoch") != current["ownership"]["epoch"]):
            raise WorkflowRuntimeError("TEAM_BOOTSTRAP_RESERVATION_CHANGED")
        if prior["state"] == "CONFIRMED":
            state = "CONFIRMED"  # Another reconciliation already observed the exact commit.
        else:
            updated = {**prior, "state": state, "evidence": observed}
            if updated != prior:
                _team_local_save(repo, local, {**local, "operations": {**local["operations"], operation_id: updated}}, epoch)
    return {"status": state, "operation_id": operation_id, "push_attempted": push_attempted,
            "candidate_commit": manifest["candidate_commit"], "observation": observed,
            "next": "confirm the saved checkpoint" if state == "CONFIRMED" else "reconcile the original operation; never repeat push"}


def team_observe_remote(repo: Path, *, operation_id: str) -> dict[str, Any]:
    """Persist one operation-bound observation; retry never renews a spent grant."""
    _team_registered(repo, "team-observe-remote", ["GIT_COMMON_DIR/" + TEAM_LOCAL, "GIT_COMMON_DIR/objects/**"])
    raw, data, _ = _team_current(repo)
    local = _team_local(repo)
    if not operation_id or len(operation_id) > 160:
        raise WorkflowRuntimeError("TEAM_OPERATION_ID_INVALID")
    actor = os.environ.get("CODEX_THREAD_ID")
    owner = data["ownership"]
    transfer = owner["transfer"]
    is_owner = local["installation_ref"] == owner["installation_ref"] and actor == data["owner_thread_id"]
    is_claimant = (owner["state"] in {"RELEASED", "CLAIM_ABORTED"} and transfer is not None
                   and actor == transfer["to_thread"] and local["installation_ref"] == transfer["to_ref"]
                   and operation_id == transfer["id"] + ":release")
    if not (is_owner or is_claimant):
        raise WorkflowRuntimeError("TEAM_REMOTE_OBSERVER_NOT_OWNER_OR_NAMED_CLAIMANT")
    prior = local["operations"].get(operation_id)
    if prior is not None:
        return {"status": "NOOP", "operation_id": operation_id, "state": prior["state"],
                "next": "inspect original operation; an existing observation is not renewed"}
    commit, remote_raw, remote_data = _team_remote(repo)
    receipt = {"schema": "q3_team_remote_observation.v1", "operation_id": operation_id,
               "state": "OBSERVED", "installation_ref": local["installation_ref"],
               "actor": os.environ.get("CODEX_THREAD_ID"), "epoch": data["ownership"]["epoch"],
               "checkpoint_sha256": _resume_digest(raw),
               "local_head": _team_git(repo, "rev-parse", "HEAD").decode().strip(),
               "remote_commit": commit, "remote_resume_sha256": _resume_digest(remote_raw),
               "remote_ownership": remote_data["ownership"],
               "remote_thread": remote_data["owner_thread_id"], "evidence": {}}
    with _execution_writer_epoch(repo) as epoch:
        if _resume_file(repo, RESUME_PATH) != raw:
            raise WorkflowRuntimeError("TEAM_OBSERVATION_CHECKPOINT_CHANGED")
        if os.environ.get("CODEX_THREAD_ID") != actor:
            raise WorkflowRuntimeError("TEAM_OBSERVATION_ACTOR_CHANGED")
        updated = {**local, "operations": {**local["operations"], operation_id: receipt}}
        _team_local_save(repo, local, updated, epoch)
    return {"status": "OBSERVED", "operation_id": operation_id, "remote_commit": commit,
            "remote_resume_sha256": receipt["remote_resume_sha256"], "execution_acquired": False}


def team_reserve_effect(repo: Path, *, operation_id: str) -> dict[str, Any]:
    _team_registered(repo, "team-reserve-effect", ["GIT_COMMON_DIR/" + TEAM_LOCAL])
    with _execution_writer_epoch(repo) as epoch:
        raw, data, _ = _team_current(repo)
        _team_actor(repo, data)
        if data["ownership"]["state"] != "ACTIVE" or data["reconciliation_pending"]:
            raise WorkflowRuntimeError("TEAM_OWNER_RECONCILIATION_REQUIRED")
        operation = data["operation"]
        if operation["id"] != operation_id or operation["state"] != "INTENT":
            raise WorkflowRuntimeError("TEAM_EXACT_EFFECT_INTENT_REQUIRED")
        _team_verify_paths(repo, data["source_manifest"])
        _team_verify_paths(repo, operation["inputs"])
        local = _team_local(repo)
        receipt = local["operations"].get(operation_id)
        if not receipt:
            raise WorkflowRuntimeError("TEAM_REMOTE_OBSERVATION_REQUIRED")
        if receipt["state"] != "OBSERVED":
            return {"status": "RECONCILE_ORIGINAL", "operation_id": operation_id, "execute": False}
        if (receipt["checkpoint_sha256"] != _resume_digest(raw)
                or receipt["actor"] != data["owner_thread_id"]
                or receipt["epoch"] != data["ownership"]["epoch"]
                or receipt["remote_ownership"] != data["ownership"]
                or receipt["remote_thread"] != data["owner_thread_id"]
                or receipt["local_head"] != _team_git(repo, "rev-parse", "HEAD").decode().strip()):
            raise WorkflowRuntimeError("TEAM_REMOTE_OWNERSHIP_OR_INPUT_DRIFT")
        updated = {**local, "operations": {**local["operations"], operation_id: {**receipt, "state": "RESERVED"}},
                   "epoch_floor": max(local["epoch_floor"], data["ownership"]["epoch"])}
        _team_local_save(repo, local, updated, epoch)
        return {"status": "RESERVED", "operation_id": operation_id, "execute_once": True,
                "lost_receipt_action": "RECONCILE_ORIGINAL"}


def _team_evidence(repo: Path, relative: str, expected: str) -> dict[str, Any]:
    raw = _resume_file(repo, Path(relative))
    if _resume_digest(raw) != expected:
        raise WorkflowRuntimeError("TEAM_EVIDENCE_CHANGED:" + relative)
    assert raw is not None
    try:
        value = _load_unique_json(repo / relative)
    except StartupRuntimeError as exc:
        raise WorkflowRuntimeError("TEAM_EVIDENCE_INVALID") from exc
    if _team_json(value) != raw:
        raise WorkflowRuntimeError("TEAM_EVIDENCE_NONCANONICAL")
    return value


def team_observe_native(repo: Path, *, candidate: Path, expected_sha256: str) -> dict[str, Any]:
    """Store externally observed native evidence; never invent a provider observation."""
    _team_registered(repo, "team-observe-native", ["GIT_COMMON_DIR/" + TEAM_LOCAL])
    payload = candidate.read_bytes()
    if _resume_digest(payload) != expected_sha256:
        raise WorkflowRuntimeError("TEAM_NATIVE_PAYLOAD_CHANGED")
    evidence = _load_unique_json(candidate)
    if evidence.get("schema") == "q3_team_assignment_observation.v1":
        return _team_observe_assignment(repo, evidence, payload)
    required = {"schema", "installation_ref", "actor", "epoch", "transfer_id", "watch_id", "target_thread",
                "state", "continuation_minutes", "agent_check_minutes", "observed_at", "scheduled_wake_at",
                "provider_receipt", "provider_receipt_sha256", "retarget_supported"}
    if (set(evidence) != required or evidence["schema"] != "q3_team_native_observation.v1"
            or _team_json(evidence) != payload or evidence["state"] not in {"ACTIVE", "PAUSED", "ABSENT", "UNKNOWN"}
            or type(evidence["retarget_supported"]) is not bool
            or type(evidence["continuation_minutes"]) is not int or evidence["continuation_minutes"] != 10
            or type(evidence["agent_check_minutes"]) is not int or evidence["agent_check_minutes"] != 20):
        raise WorkflowRuntimeError("TEAM_NATIVE_SCHEMA_INVALID")
    with _execution_writer_epoch(repo) as epoch:
        _, data, _ = _team_current(repo)
        _team_actor(repo, data)
        local = _team_local(repo)
        if (evidence["installation_ref"] != local["installation_ref"]
                or evidence["actor"] != os.environ.get("CODEX_THREAD_ID")
                or evidence["epoch"] != data["ownership"]["epoch"]):
            raise WorkflowRuntimeError("TEAM_NATIVE_OWNER_MISMATCH")
        _team_verify_paths(repo, {evidence["provider_receipt"]: evidence["provider_receipt_sha256"]})
        for name in ("observed_at", "scheduled_wake_at"):
            value = evidence[name]
            if value is None and name == "scheduled_wake_at":
                continue
            if not isinstance(value, str) or datetime.fromisoformat(value).utcoffset() is None:
                raise WorkflowRuntimeError("TEAM_NATIVE_OBSERVATION_TIME_INVALID")
        if local["watch"] == evidence:
            return {"status": "NOOP", "watch_id": evidence["watch_id"]}
        operations = dict(local["operations"])
        for action in ("CREATE", "UPDATE", "PAUSE"):
            intent_id = evidence["transfer_id"] + ":watch:" + action
            intent = operations.get(intent_id)
            if intent is not None and intent["state"] == "RESERVED":
                desired = "PAUSED" if action == "PAUSE" else "ACTIVE"
                if (evidence["state"] == desired and evidence["target_thread"] == intent["target_thread"]
                        and (intent["watch_id"] is None or intent["watch_id"] == evidence["watch_id"])):
                    operations[intent_id] = {**intent, "state": "CONFIRMED", "evidence": evidence}
        _team_local_save(repo, local, {**local, "watch": evidence, "operations": operations}, epoch)
    return {"status": "OBSERVED", "watch_id": evidence["watch_id"], "provider_state": evidence["state"],
            "scheduled_wake_observed": evidence["scheduled_wake_at"] is not None}


def _team_assignments(repo: Path) -> dict[str, Any]:
    from orchestrator import team_records

    raw = _resume_file(repo, TEAM_ASSIGNMENTS)
    if raw is None:
        raise WorkflowRuntimeError("TEAM_ASSIGNMENTS_MISSING")
    return team_records.read_registry(raw, "assignments", archive_loader=lambda path: _resume_file(repo, Path(path)))


def _team_assignment_context(repo: Path, data: dict[str, Any], assignments: dict[str, Any],
                             assignment_ids: list[str], result_hashes: set[str]) -> Any:
    """Recheck local native observations and their durable evidence, not report assertions."""
    from orchestrator import team_records

    operations = _team_local(repo)["operations"]
    observations = {}
    output_artifacts: dict[str, bytes] = {}
    for assignment_id in assignment_ids:
        row = assignments["assignments"].get(assignment_id)
        if row is None:
            raise WorkflowRuntimeError("TEAM_ASSIGNMENT_UNKNOWN:" + assignment_id)
        assignment = row["assignment"]
        found = []
        for item in operations.values():
            observation = item.get("observation", {})
            if (item.get("schema") == "q3_team_assignment_receipt.v1"
                    and observation.get("assignment_id") == assignment_id):
                if observation.get("phase") == "RESULT" and observation.get("output_sha256") not in result_hashes:
                    continue
                team_records._validate_native_observation(assignment, observation, phase=observation["phase"])
                for prefix in ("output", "provider_receipt"):
                    raw = _team_locator(repo, observation[prefix + "_locator"], observation[prefix + "_sha256"])
                    if prefix == "output":
                        output_artifacts[observation[prefix + "_locator"]] = raw
                found.append(observation)
        completed = [item for item in found if item["phase"] == "RESULT" and item["state"] == "COMPLETED"]
        if len(completed) == 1:
            found = [item for item in found if item["phase"] == "LAUNCH"] + completed
        observations[assignment_id] = found
    return team_records.TrustedTeamContext(
        owner_task=data["owner_thread_id"], owner_host=data["owner_host_id"],
        owner_installation_ref=data["ownership"]["installation_ref"], owner_epoch=data["ownership"]["epoch"],
        actor_id=data["owner_thread_id"], observations=observations, output_artifacts=output_artifacts)


def _team_observe_assignment(repo: Path, evidence: dict[str, Any], payload: bytes) -> dict[str, Any]:
    from orchestrator import team_records

    if _team_json(evidence) != payload:
        raise WorkflowRuntimeError("TEAM_NATIVE_NONCANONICAL")
    with _execution_writer_epoch(repo) as epoch:
        _, data, _ = _team_current(repo)
        _team_actor(repo, data)
        if data["ownership"]["state"] not in {"ACTIVE", "HANDOFF_INTENT"}:
            raise WorkflowRuntimeError("TEAM_OWNER_RECONCILIATION_REQUIRED")
        assignments = _team_assignments(repo)
        assignment_id = evidence.get("assignment_id")
        row = assignments["assignments"].get(assignment_id)
        if row is None:
            raise WorkflowRuntimeError("TEAM_ASSIGNMENT_UNKNOWN")
        assignment = row["assignment"]
        context = team_records.TrustedTeamContext(data["owner_thread_id"], data["owner_host_id"],
            data["ownership"]["installation_ref"], data["ownership"]["epoch"], data["owner_thread_id"], {})
        team_records._validate_assignment_owner(assignment, context)
        phase = evidence.get("phase")
        if phase not in {"LAUNCH", "RESULT"}:
            raise WorkflowRuntimeError("TEAM_NATIVE_PHASE_INVALID")
        team_records._validate_native_observation(assignment, evidence, phase=phase)
        for prefix in ("output", "provider_receipt"):
            _team_locator(repo, evidence[prefix + "_locator"], evidence[prefix + "_sha256"])
        local = _team_local(repo)
        operation_id = evidence["operation_id"]
        record = {"schema": "q3_team_assignment_receipt.v1", "state": "CONFIRMED", "observation": evidence}
        prior = local["operations"].get(operation_id)
        if prior is not None and prior.get("observation") == evidence:
            return {"status": "NOOP", "assignment_id": assignment_id, "phase": phase}
        for item in local["operations"].values():
            observed = item.get("observation", {})
            if (phase == "LAUNCH" and observed.get("assignment_id") == assignment_id
                    and observed.get("phase") == phase):
                raise WorkflowRuntimeError("TEAM_NATIVE_PHASE_CONFLICT:reuse the original observation")
        if phase == "LAUNCH":
            operation = data["operation"]
            if (not prior or prior.get("state") != "RESERVED" or operation["id"] != operation_id
                    or operation["command"] != "agent-launch" or operation["subject"]["id"] != assignment_id
                    or operation["subject"]["sha256"] != team_records._assignment_binding_sha(assignment)
                    or prior.get("actor") != data["owner_thread_id"] or prior.get("epoch") != data["ownership"]["epoch"]):
                raise WorkflowRuntimeError("TEAM_AGENT_LAUNCH_RESERVATION_REQUIRED")
        elif prior is not None:
            raise WorkflowRuntimeError("TEAM_NATIVE_OPERATION_CONFLICT")
        else:
            context = _team_assignment_context(repo, data, assignments, [assignment_id], set())
            launch = context.observations[assignment_id]
            if (len(launch) != 1 or launch[0]["phase"] != "LAUNCH"
                    or launch[0]["native_agent_id"] != evidence["native_agent_id"]):
                raise WorkflowRuntimeError("TEAM_NATIVE_LAUNCH_BINDING_REQUIRED")
        record.update(actor=data["owner_thread_id"], epoch=data["ownership"]["epoch"])
        if prior is not None:
            record = {**prior, **record}
        _team_local_save(repo, local, {**local, "operations": {**local["operations"], operation_id: record}}, epoch)
    return {"status": "OBSERVED", "assignment_id": assignment_id, "phase": phase,
            "mathematical_acceptance": False}


def team_watch_intent(repo: Path, *, action: str, transfer_id: str, target_thread: str) -> dict[str, Any]:
    _team_registered(repo, "team-watch-intent", ["GIT_COMMON_DIR/" + TEAM_LOCAL])
    if action not in {"CREATE", "UPDATE", "PAUSE"} or not re.fullmatch(r"[0-9a-f-]{36}", target_thread) or not transfer_id:
        raise WorkflowRuntimeError("TEAM_WATCH_INTENT_INVALID")
    with _execution_writer_epoch(repo) as epoch:
        _, data, _ = _team_current(repo)
        _team_actor(repo, data)
        local = _team_local(repo)
        operation_id = transfer_id + ":watch:" + action
        if operation_id in local["operations"]:
            return {"status": "RECONCILE_ORIGINAL", "operation_id": operation_id, "execute": False}
        if any(key.startswith(transfer_id + ":watch:") and value["state"] in {"RESERVED", "UNKNOWN"}
               for key, value in local["operations"].items()):
            raise WorkflowRuntimeError("TEAM_WATCH_EFFECT_UNRESOLVED")
        transfer = data["ownership"]["transfer"]
        if data["ownership"]["state"] != "ACTIVE" and (transfer is None or transfer["id"] != transfer_id):
            raise WorkflowRuntimeError("TEAM_WATCH_TRANSFER_MISMATCH")
        watch = local["watch"]
        if watch is None or watch["state"] == "UNKNOWN":
            raise WorkflowRuntimeError("TEAM_WATCH_INVENTORY_REQUIRED")
        if action == "CREATE" and watch["state"] != "ABSENT":
            raise WorkflowRuntimeError("TEAM_WATCH_CONFIRMED_ABSENCE_REQUIRED")
        if action != "CREATE" and (watch["state"] == "ABSENT" or not watch["watch_id"]):
            raise WorkflowRuntimeError("TEAM_EXISTING_WATCH_REQUIRED")
        if target_thread != data["owner_thread_id"]:
            if (transfer is None or transfer["mode"] != "SAME_INSTALLATION"
                    or target_thread != transfer["to_thread"] or watch["retarget_supported"] is not True):
                raise WorkflowRuntimeError("TEAM_WATCH_RETARGET_UNSUPPORTED_OR_UNVERIFIED")
        if data["ownership"]["state"] == "CLAIM_PENDING":
            remote = local["operations"].get(transfer_id + ":claim")
            if remote is None or remote["remote_ownership"] != data["ownership"]:
                raise WorkflowRuntimeError("TEAM_VERIFIED_REMOTE_CLAIM_REQUIRED")
        receipt = {"schema": "q3_team_watch_intent.v1", "operation_id": operation_id, "state": "RESERVED",
                   "actor": data["owner_thread_id"], "installation_ref": local["installation_ref"],
                   "epoch": data["ownership"]["epoch"], "action": action, "target_thread": target_thread,
                   "watch_id": watch["watch_id"], "inventory": watch, "evidence": {}}
        _team_local_save(repo, local, {**local, "operations": {**local["operations"], operation_id: receipt}}, epoch)
        return {"status": "RESERVED", "operation_id": operation_id, "watch_id": watch["watch_id"], "execute_once": True}


def team_confirm_effect(repo: Path, *, operation_id: str, candidate: Path, expected_sha256: str) -> dict[str, Any]:
    _team_registered(repo, "team-confirm-effect", ["GIT_COMMON_DIR/" + TEAM_LOCAL])
    payload = candidate.read_bytes()
    if _resume_digest(payload) != expected_sha256:
        raise WorkflowRuntimeError("TEAM_CONFIRMATION_PAYLOAD_CHANGED")
    record = _load_unique_json(candidate)
    if (set(record) != {"schema", "operation_id", "outcome", "evidence"}
            or record["schema"] != "q3_team_effect_observation.v1" or record["operation_id"] != operation_id
            or record["outcome"] not in {"CONFIRMED", "NOT_EXECUTED", "UNKNOWN"}
            or _team_json(record) != payload or not record["evidence"]):
        raise WorkflowRuntimeError("TEAM_CONFIRMATION_SCHEMA_INVALID")
    _team_path_hashes(record["evidence"])
    with _execution_writer_epoch(repo) as epoch:
        _, data, _ = _team_current(repo)
        _team_actor(repo, data)
        _team_verify_paths(repo, record["evidence"])
        local = _team_local(repo)
        prior = local["operations"].get(operation_id)
        if not prior or prior["state"] not in {"RESERVED", "CONFIRMED", "NOT_EXECUTED", "UNKNOWN"}:
            raise WorkflowRuntimeError("TEAM_ORIGINAL_RESERVATION_REQUIRED")
        if prior["state"] in {"CONFIRMED", "NOT_EXECUTED"}:
            if prior["evidence"] != record or prior["state"] != record["outcome"]:
                raise WorkflowRuntimeError("TEAM_CONFIRMATION_CONFLICT")
            return {"status": "NOOP", "operation_id": operation_id}
        updated = {**local, "operations": {**local["operations"], operation_id: {**prior, "state": record["outcome"], "evidence": record}}}
        _team_local_save(repo, local, updated, epoch)
    return {"status": "OBSERVED", "operation_id": operation_id, "outcome": record["outcome"]}


def team_guard(repo: Path, *, command: str, paths: list[str], effect: bool = False,
               expected_epoch: int | None = None) -> dict[str, Any] | None:
    """Called by registered writers while holding their canonical writer epoch.

    This cooperative check does not authenticate a same-user shell or perform a
    network request. External effects additionally need an exact local reservation.
    """
    _team_pending_guard(repo)
    if not _team_enabled(repo):
        return None
    if command not in TEAM_FENCED_CALLS | TEAM_NATIVE_EFFECTS:
        raise WorkflowRuntimeError("TEAM_UNFENCED_WRITER_FORBIDDEN:" + command)
    _team_writer_inventory(repo)
    raw, data, _ = _team_current(repo)
    _team_actor(repo, data)
    if expected_epoch is None:
        value = os.environ.get("Q3_OWNER_EPOCH", "")
        if not re.fullmatch(r"[1-9][0-9]*", value):
            raise WorkflowRuntimeError("TEAM_CALLER_EPOCH_REQUIRED:use the epoch observed by plan")
        expected_epoch = int(value)
    if type(expected_epoch) is not int or expected_epoch != data["ownership"]["epoch"]:
        raise WorkflowRuntimeError("TEAM_CALLER_EPOCH_CHANGED")
    if data["ownership"]["epoch"] < _team_local(repo)["epoch_floor"]:
        raise WorkflowRuntimeError("TEAM_RETIRED_EPOCH")
    if data["ownership"]["state"] != "ACTIVE" or data["reconciliation_pending"]:
        raise WorkflowRuntimeError("TEAM_OWNER_RECONCILIATION_REQUIRED")
    _team_verify_paths(repo, data["source_manifest"])
    if command != "workflow-team-record":
        from orchestrator import team_records
        raw_issues = _resume_file(repo, TEAM_ISSUES)
        if raw_issues is None:
            raise WorkflowRuntimeError("TEAM_REGISTRY_MISSING")
        issues = team_records.read_registry(raw_issues, "issues", archive_loader=lambda path: _resume_file(repo, Path(path)))
        for issue in issues["issues"].values():
            if (issue["state"] in {"CONFIRMED_BUG", "CONFIRMED_RULE_CONFLICT", "ASSIGNED", "FIX_CANDIDATE", "FIX_VERIFIED", "FIX_COMMITTED"}
                    and command in issue["report"]["affected_operations"]):
                raise WorkflowRuntimeError("TEAM_DEPENDENT_OPERATION_HELD:" + issue["issue_id"])
    if effect:
        operation = data["operation"]
        if operation["state"] != "INTENT" or operation["command"] != command:
            raise WorkflowRuntimeError("TEAM_EXACT_EFFECT_INTENT_REQUIRED")
        _team_verify_paths(repo, operation["inputs"])
        if not set(paths).issubset(operation["inputs"]):
            raise WorkflowRuntimeError("TEAM_EFFECT_SCOPE_MISMATCH")
        receipt = _team_local_operation(repo, operation["id"])
        if (receipt is None or receipt.get("state") != "RESERVED"
                or receipt.get("checkpoint_sha256") != _resume_digest(raw)
                or receipt.get("actor") != data["owner_thread_id"]
                or receipt.get("epoch") != data["ownership"]["epoch"]):
            raise WorkflowRuntimeError("TEAM_EFFECT_REMOTE_RESERVATION_REQUIRED")
    return {"installation_ref": data["ownership"]["installation_ref"],
            "task": data["owner_thread_id"], "epoch": data["ownership"]["epoch"],
            "checkpoint_sha256": _resume_digest(raw), "operation_id": data["operation"]["id"]}


def _team_integration_manifest(payload: bytes) -> dict[str, Any]:
    from orchestrator import team_records
    import base64

    manifest = team_records.load_payload(payload)
    if (set(manifest) != {"schema", "mode", "operation_id", "owner_task", "installation_ref", "epoch",
                         "expected_head", "implementer_assignment", "assignment_sha256", "checker_assignment",
                         "candidate_commit", "files"}
            or manifest["schema"] != "q3_team_integration.v1"
            or manifest["mode"] not in {"EVIDENCE_INTAKE", "REVIEWED_SOURCE"}
            or type(manifest["epoch"]) is not int or manifest["epoch"] < 1
            or not _team_hex(manifest["expected_head"], 40)
            or not _team_hex(manifest["installation_ref"]) or not _team_hex(manifest["assignment_sha256"])
            or any(not isinstance(manifest[key], str) or not manifest[key] or len(manifest[key]) > 160
                   for key in ("operation_id", "owner_task", "implementer_assignment"))
            or not isinstance(manifest["files"], list) or not manifest["files"]):
        raise WorkflowRuntimeError("TEAM_INTEGRATION_MANIFEST_INVALID")
    intake = manifest["mode"] == "EVIDENCE_INTAKE"
    if intake:
        if manifest["candidate_commit"] is not None or manifest["checker_assignment"] is not None:
            raise WorkflowRuntimeError("TEAM_INTAKE_REQUIRES_NO_ACCEPTANCE_FIELDS")
    elif (not _team_hex(manifest["candidate_commit"], 40)
          or not isinstance(manifest["checker_assignment"], str) or not manifest["checker_assignment"]):
        raise WorkflowRuntimeError("TEAM_INTEGRATION_SOURCE_REVIEW_REQUIRED")
    paths = []
    for row in manifest["files"]:
        required = {"path", "before_sha256", "sha256", "content_base64" if intake else "source_path"}
        if (not isinstance(row, dict) or set(row) != required or not _team_hex(row["sha256"])
                or not (_team_hex(row["before_sha256"]) or row["before_sha256"] == "ABSENT")):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_FILE_INVALID")
        try:
            _team_path_hashes({row["path"]: row["sha256"]})
        except (TypeError, ValueError) as exc:
            raise WorkflowRuntimeError("TEAM_INTEGRATION_PATH_INVALID") from exc
        path = row["path"]
        if "\x00" in path or path.startswith("-") or any(part.startswith(".git") for part in Path(path).parts):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_PATH_INVALID")
        if intake:
            try:
                content = base64.b64decode(row["content_base64"], validate=True)
                valid = base64.b64encode(content).decode("ascii") == row["content_base64"]
            except (ValueError, TypeError) as exc:
                raise WorkflowRuntimeError("TEAM_INTAKE_BASE64_INVALID") from exc
            if (not valid or _resume_digest(content) != row["sha256"] or row["before_sha256"] != "ABSENT"
                    or path != "docs/session_protocols/team-evidence-" + row["sha256"] + ".bin"):
                raise WorkflowRuntimeError("TEAM_INTAKE_CONTENT_ADDRESS_INVALID")
        elif row["source_path"] != path:
            raise WorkflowRuntimeError("TEAM_INTEGRATION_SOURCE_PATH_MISMATCH")
        elif (path in {str(RESUME_PATH), str(RESUME_HISTORY_PATH), str(TEAM_ISSUES), str(TEAM_ASSIGNMENTS),
                       "docs/Codex/CURRENT.md", "docs/routeB_bus/SPINE_VIEW.md"}
              or path.startswith(("orchestrator/state/", "docs/session_protocols/team-"))
              or any(part.startswith(".") for part in Path(path).parts if part != ".agents")
              or re.search(r"\.(db|sqlite|sqlite3)(-|$)", path)):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_RESERVED_DESTINATION:" + path)
        paths.append(path)
    if paths != sorted(set(paths)):
        raise WorkflowRuntimeError("TEAM_INTEGRATION_PATHS_UNSORTED_OR_DUPLICATE")
    return manifest


def _team_integration_engine(repo: Path) -> dict[str, Any]:
    """Pin the existing isolated verification checkout, including loaded local code."""
    engine = REPO.resolve()
    if engine == repo.resolve() or _git_common_dir(engine) == _git_common_dir(repo):
        raise WorkflowRuntimeError("TEAM_INTEGRATION_ISOLATED_ENGINE_REQUIRED:use its --root option")
    commit = _team_git(engine, "rev-parse", "HEAD").decode().strip()
    _team_git(engine, "diff", "--no-ext-diff", "--quiet", "HEAD", "--")
    sources = {}
    for module in tuple(sys.modules.values()):
        file = getattr(module, "__file__", None)
        if not file:
            continue
        path = Path(file).resolve()
        if not path.is_relative_to(engine) or path.suffix != ".py":
            continue
        relative = path.relative_to(engine).as_posix()
        raw = _resume_file(engine, Path(relative))
        if raw != _team_git(engine, "show", commit + ":" + relative):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_ENGINE_SOURCE_CHANGED:" + relative)
        sources[relative] = _resume_digest(raw)
    if "orchestrator/workflow_runtime.py" not in sources:
        raise WorkflowRuntimeError("TEAM_INTEGRATION_ENGINE_IDENTITY_MISSING")
    return {"root": str(engine), "commit": commit, "source_sha256": sources,
            "python": platform.python_version(), "pyyaml": yaml.__version__}


def _team_integration_blob(repo: Path, commit: str, path: str) -> tuple[bytes | None, int | None]:
    entry = _team_git(repo, "ls-tree", "-z", commit, "--", path).split(b"\0")
    if entry == [b""]:
        return None, None
    if len(entry) != 2 or entry[-1] != b"":
        raise WorkflowRuntimeError("TEAM_INTEGRATION_GIT_PATH_AMBIGUOUS:" + path)
    metadata, found = entry[0].split(b"\t", 1)
    mode, kind, blob = metadata.decode().split()
    if found.decode() != path or kind != "blob" or mode not in {"100644", "100755"}:
        raise WorkflowRuntimeError("TEAM_INTEGRATION_GIT_MODE_INVALID:" + path)
    size = int(_team_git(repo, "cat-file", "-s", blob))
    if size > TEAM_READ_MAX:
        raise WorkflowRuntimeError("TEAM_INTEGRATION_SOURCE_LIMIT:" + path)
    return _team_git(repo, "cat-file", "blob", blob), int(mode[-3:], 8)


def _team_integration_review(repo: Path, data: dict[str, Any], manifest: dict[str, Any],
                             payload: bytes) -> dict[str, Any] | None:
    from orchestrator import team_records

    assignments = _team_assignments(repo)
    ids = [manifest["implementer_assignment"]]
    if manifest["checker_assignment"] is not None:
        ids.append(manifest["checker_assignment"])
    context = team_records.TrustedTeamContext(data["owner_thread_id"], data["owner_host_id"],
        data["ownership"]["installation_ref"], data["ownership"]["epoch"], data["owner_thread_id"], {})
    rows = []
    for assignment_id in ids:
        row = assignments["assignments"].get(assignment_id)
        if row is None:
            raise WorkflowRuntimeError("TEAM_ASSIGNMENT_UNKNOWN:" + assignment_id)
        assignment = row["assignment"]
        team_records._validate_assignment_owner(assignment, context)
        rows.append(assignment)
    producer = rows[0]
    if _resume_digest(team_records.canonical_json(team_records._assignment_immutable_view(producer))) != manifest["assignment_sha256"]:
        raise WorkflowRuntimeError("TEAM_INTEGRATION_ASSIGNMENT_CHANGED")
    if manifest["mode"] == "EVIDENCE_INTAKE":
        return None
    checker = rows[1]
    if (checker["assignment_id"] == producer["assignment_id"] or checker["role"] != "independent-checker"
            or checker["assignee"] in {producer["assignee"], data["owner_thread_id"]}
            or checker["base_commit"] != manifest["expected_head"]
            or producer["base_commit"] != manifest["expected_head"]):
        raise WorkflowRuntimeError("TEAM_INTEGRATION_INDEPENDENT_BASE_REVIEW_REQUIRED")
    paths = {row["path"] for row in manifest["files"]}
    if any(not paths.issubset(set(assignment["permitted_paths"])) for assignment in rows):
        raise WorkflowRuntimeError("TEAM_INTEGRATION_ASSIGNMENT_SCOPE_MISMATCH")
    if _team_git(repo, "cat-file", "-t", manifest["candidate_commit"]).strip() != b"commit":
        raise WorkflowRuntimeError("TEAM_INTEGRATION_COMMIT_OBJECT_REQUIRED")
    _team_git(repo, "merge-base", "--is-ancestor", producer["base_commit"], manifest["candidate_commit"])
    hashes = {item.get("observation", {}).get("output_sha256") for item in _team_local(repo)["operations"].values()
              if item.get("observation", {}).get("assignment_id") == checker["assignment_id"]}
    context = _team_assignment_context(repo, data, assignments, [checker["assignment_id"]], hashes)
    launch, result = team_records._validated_assignment_observation(checker, context)
    if result["state"] != "COMPLETED":
        raise WorkflowRuntimeError("TEAM_INTEGRATION_COMPLETED_REVIEW_REQUIRED")
    raw = context.output_artifacts[result["output_locator"]]
    expected = {"schema": "q3_team_integration_review.v1", "manifest_sha256": _resume_digest(payload),
                "base_commit": manifest["expected_head"], "candidate_commit": manifest["candidate_commit"],
                "files": [{"path": row["path"], "sha256": row["sha256"]} for row in manifest["files"]],
                "implementer_assignment": producer["assignment_id"], "checker_assignment": checker["assignment_id"],
                "verdict": "SOURCE_INTEGRATION_APPROVED"}
    if team_records.load_payload(raw) != expected:
        raise WorkflowRuntimeError("TEAM_INTEGRATION_REVIEW_NOT_EXACTLY_APPROVED")
    destinations = {str((repo / path).resolve()) for path in paths}
    for observation in (launch, result):
        for prefix in ("output", "provider_receipt"):
            locator = observation[prefix + "_locator"]
            if not locator.startswith("git:") and str((repo / locator).resolve()) in destinations:
                raise WorkflowRuntimeError("TEAM_INTEGRATION_REVIEW_OVERWRITE_FORBIDDEN")
    return {"checker_assignment_sha256": team_records._assignment_binding_sha(checker),
            "launch": launch, "result": result, "artifact": expected}


def team_integrate_candidate(
    repo: Path, *, candidate: Path | None = None, recover_operation: str | None = None,
) -> dict[str, Any]:
    """Recoverable local copy of one reserved exact candidate; never publication."""
    import base64

    if (candidate is None) == (recover_operation is None):
        raise WorkflowRuntimeError("TEAM_INTEGRATION_CANDIDATE_OR_RECOVERY_REQUIRED")
    if recover_operation is not None:
        # An explicit operation ID recovers its durable manifest without touching
        # a lost, moved or changed worker/output file. It selects no new action.
        local = _team_private_read(repo, TEAM_LOCAL)
        receipt = (local or {}).get("operations", {}).get(recover_operation, {})
        saved = receipt.get("integration", {})
        if saved.get("state") != "PENDING":
            raise WorkflowRuntimeError("TEAM_INTEGRATION_RECOVERY_RECORD_REQUIRED")
        payload = _team_json(saved.get("manifest"))
        if (_resume_digest(payload) != saved.get("manifest_sha256")
                or saved["manifest"].get("operation_id") != recover_operation):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_RECOVERY_MANIFEST_CHANGED")
    else:
        assert candidate is not None
        payload = candidate.read_bytes()
    manifest = _team_integration_manifest(payload)
    operation_id = manifest["operation_id"]
    with _execution_writer_epoch(repo, integration_operation=operation_id) as epoch:
        raw, data, _ = _team_current(repo)
        _team_actor(repo, data)
        local = _team_local(repo)
        prior = local["operations"].get(operation_id)
        integration = prior.get("integration") if prior else None
        if integration is None:
            _team_registered(repo, "team-integrate-candidate", TEAM_INTEGRATION_WRITE_PATHS)
            if team_guard(repo, command="workflow-team-integrate-candidate", paths=[], effect=True) is None:
                raise WorkflowRuntimeError("TEAM_RUNTIME_NOT_ACTIVATED")
        if (data["ownership"]["state"] != "ACTIVE" or data["reconciliation_pending"]
                or manifest["owner_task"] != data["owner_thread_id"]
                or manifest["installation_ref"] != data["ownership"]["installation_ref"]
                or manifest["epoch"] != data["ownership"]["epoch"]
                or os.environ.get("Q3_OWNER_EPOCH") != str(manifest["epoch"])
                or local["epoch_floor"] > manifest["epoch"]):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_OWNER_CHANGED")
        operation = data["operation"]
        if (operation["id"] != operation_id or operation["state"] != "INTENT"
                or operation["command"] != "workflow-team-integrate-candidate"
                or operation["subject"] != {"kind": "REPAIR", "id": operation_id, "sha256": _resume_digest(payload)}):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_EXACT_INTENT_REQUIRED")
        if (not prior or prior.get("state") not in {"RESERVED", "CONFIRMED"}
                or prior.get("checkpoint_sha256") != _resume_digest(raw)
                or prior.get("actor") != data["owner_thread_id"] or prior.get("epoch") != manifest["epoch"]
                or prior.get("remote_ownership") != data["ownership"] or prior.get("remote_thread") != data["owner_thread_id"]
                or prior.get("local_head") != manifest["expected_head"]
                or _team_git(repo, "rev-parse", "HEAD").decode().strip() != manifest["expected_head"]):
            raise WorkflowRuntimeError("TEAM_INTEGRATION_RESERVATION_OR_HEAD_CHANGED")
        if integration is None and prior["state"] != "RESERVED":
            raise WorkflowRuntimeError("TEAM_INTEGRATION_RESERVATION_REQUIRED")
        review = _team_integration_review(repo, data, manifest, payload)
        engine = _team_integration_engine(repo)
        intake = manifest["mode"] == "EVIDENCE_INTAKE"
        files = []
        total = 0
        for row in manifest["files"]:
            path = row["path"]
            if candidate is not None and (repo / path).resolve() == candidate.resolve():
                raise WorkflowRuntimeError("TEAM_INTEGRATION_MANIFEST_OVERWRITE_FORBIDDEN")
            before, before_mode = (None, None) if intake else _team_integration_blob(repo, manifest["expected_head"], path)
            after, mode = ((base64.b64decode(row["content_base64"], validate=True), 0o644) if intake
                           else _team_integration_blob(repo, manifest["candidate_commit"], path))
            if before is None and not intake and _team_git(repo, "ls-files", "--", path).strip():
                raise WorkflowRuntimeError("TEAM_INTEGRATION_INDEX_PREIMAGE_CHANGED:" + path)
            if after is None or _resume_digest(after) != row["sha256"] or _resume_digest(before) != row["before_sha256"]:
                raise WorkflowRuntimeError("TEAM_INTEGRATION_BLOB_MISMATCH:" + path)
            total += len(after) + len(before or b"")
            if total > TEAM_READ_MAX:
                raise WorkflowRuntimeError("TEAM_INTEGRATION_SOURCE_LIMIT")
            actual = _resume_file(repo, Path(path))
            actual_mode = None if actual is None else (0o755 if (repo / path).stat().st_mode & 0o111 else 0o644)
            original = actual == before and actual_mode == before_mode
            copied = actual == after and actual_mode == mode
            if integration is not None and integration["state"] == "COMPLETE" and not copied:
                raise WorkflowRuntimeError("TEAM_INTEGRATION_COMPLETED_DESTINATION_CHANGED:" + path)
            if not original and not ((integration is not None or intake) and copied):
                raise WorkflowRuntimeError("TEAM_INTEGRATION_PREIMAGE_CHANGED:" + path)
            if not intake and integration is None:
                _team_git(repo, "diff", "--no-ext-diff", "--quiet", "--cached", manifest["expected_head"], "--", path)
            files.append((row, before, after, mode, actual, actual_mode))
        expected = {"schema": "q3_team_integration_reservation.v1", "state": "PENDING", "manifest": manifest,
                    "manifest_sha256": _resume_digest(payload), "engine": engine, "review": review,
                    "preimages": [{"path": row["path"], "sha256": row["before_sha256"]} for row in manifest["files"]]}
        if integration is not None and {**integration, "state": "PENDING"} != expected:
            raise WorkflowRuntimeError("TEAM_INTEGRATION_PERSISTED_IDENTITY_CHANGED")
        # Dependencies outside this transaction still must match. Its destinations
        # may already hold the candidate after a crash, so do not demand old bytes.
        destinations = {row["path"]: row for row in manifest["files"]}
        for paths in (data["source_manifest"], operation["inputs"]):
            for path, digest in paths.items():
                if integration is not None and path in destinations:
                    if digest != destinations[path]["before_sha256"]:
                        raise WorkflowRuntimeError("TEAM_INTEGRATION_DEPENDENCY_CHANGED:" + path)
                else:
                    _team_verify_paths(repo, {path: digest})
        if integration is None:
            updated = {**local, "operations": {**local["operations"], operation_id: {**prior, "integration": expected}}}
            _team_local_save(repo, local, updated, epoch)
            local, prior = updated, updated["operations"][operation_id]
        for row, before, after, mode, actual, actual_mode in files:
            path = Path(row["path"])
            if actual != after or actual_mode != mode:
                _resume_cas_bytes(repo, path, actual, after, epoch, mode=mode)
            _resume_sync(repo / path)
            if _resume_file(repo, path) != after or (0o755 if (repo / path).stat().st_mode & 0o111 else 0o644) != mode:
                raise WorkflowRuntimeError("TEAM_INTEGRATION_READBACK_MISMATCH:" + str(path))
        if _team_integration_engine(repo) != engine:
            raise WorkflowRuntimeError("TEAM_INTEGRATION_ENGINE_CHANGED")
        for row, _, after, mode, _, _ in files:
            path = Path(row["path"])
            if _resume_file(repo, path) != after or (0o755 if (repo / path).stat().st_mode & 0o111 else 0o644) != mode:
                raise WorkflowRuntimeError("TEAM_INTEGRATION_FINAL_READBACK_MISMATCH:" + str(path))
        receipt = {"operation_id": operation_id, "manifest_sha256": _resume_digest(payload), "mode": manifest["mode"],
                   "files": [{"path": row["path"], "sha256": row["sha256"]} for row in manifest["files"]],
                   "mathematical_acceptance": False, "publication": False,
                   "evidence_status": "UNADJUDICATED" if intake else "SOURCE_INTEGRATION_APPROVED"}
        updated = {**local, "operations": {**local["operations"], operation_id: {**prior, "state": "CONFIRMED",
                   "integration": {**expected, "state": "COMPLETE"}, "evidence": receipt}}}
        if updated != local:
            _team_local_save(repo, local, updated, epoch)
        else:
            _resume_sync(_git_common_dir(repo) / TEAM_LOCAL)
        return {"status": "NOOP" if integration is not None and integration["state"] == "COMPLETE" else "INTEGRATED", **receipt}


def _team_transfer_evidence(repo: Path, data: dict[str, Any], schema: str) -> dict[str, Any]:
    transfer = data["ownership"]["transfer"]
    matches = []
    for path, digest in transfer["evidence"].items():
        evidence = _team_evidence(repo, path, digest)
        if evidence.get("schema") == schema:
            matches.append(evidence)
    if len(matches) != 1 or matches[0].get("transfer_id") != transfer["id"]:
        raise WorkflowRuntimeError("TEAM_TRANSFER_EVIDENCE_REQUIRED:" + schema)
    return matches[0]


def _team_quiescence(repo: Path, data: dict[str, Any]) -> None:
    record = _team_transfer_evidence(repo, data, "q3_team_quiescence.v1")
    if (set(record) != {"schema", "transfer_id", "epoch", "source_manifest", "head", "dirty_paths",
                       "canonical_writers_idle", "unknown_operations", "assignments", "outputs", "provider_receipt"}
            or record["epoch"] != data["ownership"]["epoch"]
            or record["source_manifest"] != data["source_manifest"]
            or record["canonical_writers_idle"] is not True
            or record["unknown_operations"] != []
            or not isinstance(record["assignments"], list)
            or any(item.get("state") not in {"COLLECTED", "QUIESCED", "ISOLATED_CANDIDATE"} for item in record["assignments"])
            or data["operation"]["state"] in {"INTENT", "UNKNOWN"}):
        raise WorkflowRuntimeError("TEAM_QUIESCENCE_INCOMPLETE")
    for field in ("source_manifest", "dirty_paths", "outputs", "provider_receipt"):
        _team_path_hashes(record[field])
        _team_verify_paths(repo, record[field])
    if not record["provider_receipt"]:
        raise WorkflowRuntimeError("TEAM_QUIESCENCE_PROVIDER_RECEIPT_MISSING")
    # Control/checkpoint/transfer receipts are the explicitly recorded transfer writes.
    if record["head"] != _team_git(repo, "rev-parse", "HEAD").decode().strip():
        raise WorkflowRuntimeError("TEAM_QUIESCENCE_HEAD_CHANGED")


def _team_owner_transition(repo: Path, before: dict[str, Any], after: dict[str, Any]) -> None:
    """Validate every owner transition before the checkpoint transaction archives bytes."""
    if before["schema"] == "q3_resume.v1":
        if (after["schema"] != "q3_resume.v2" or after["owner_thread_id"] != before["owner_thread_id"]
                or after["owner_host_id"] != before["owner_host_id"]
                or after["ownership"]["epoch"] != 1 or after["ownership"]["state"] != "ACTIVE"
                or after["ownership"]["transfer"] is not None):
            raise WorkflowRuntimeError("TEAM_MIGRATION_OWNER_CHANGED")
        if any(after["pins"].get(key) != value for key, value in before["pins"].items()):
            raise WorkflowRuntimeError("TEAM_MIGRATION_CHANGED_PIN")
        if any(after["operation"].get(key) != before["operation"][key] for key in ("kind", "id", "state")):
            raise WorkflowRuntimeError("TEAM_MIGRATION_CHANGED_OPERATION")
        _team_actor(repo, after)
        _team_verify_paths(repo, after["source_manifest"])
        return
    if after["schema"] != "q3_resume.v2":
        raise WorkflowRuntimeError("TEAM_CURRENT_SCHEMA_DOWNGRADE_FORBIDDEN")
    old, new = before["ownership"], after["ownership"]
    same_owner = (all(old[k] == new[k] for k in ("epoch", "state", "installation_ref"))
                  and before["owner_thread_id"] == after["owner_thread_id"])
    if same_owner:
        if old["transfer"] != new["transfer"]:
            prior, candidate = old["transfer"], new["transfer"]
            if (prior is None or candidate is None
                    or any(prior[k] != candidate[k] for k in prior if k != "evidence")
                    or any(candidate["evidence"].get(k) != v for k, v in prior["evidence"].items())):
                raise WorkflowRuntimeError("TEAM_TRANSFER_IDENTITY_CHANGED")
        _team_actor(repo, before)
        if new["epoch"] < _team_local(repo)["epoch_floor"]:
            raise WorkflowRuntimeError("TEAM_RETIRED_EPOCH")
        _team_verify_paths(repo, after["source_manifest"])
        for name in TEAM_STAGES:
            candidate = after["stages"][name]
            if candidate != before["stages"][name] and candidate["state"] == "DONE":
                if name == "independent_review" and candidate["checked_by"] == after["owner_thread_id"]:
                    raise WorkflowRuntimeError("TEAM_INDEPENDENT_REVIEW_REQUIRED")
                if name == "parent_check" and candidate["checked_by"] != after["owner_thread_id"]:
                    raise WorkflowRuntimeError("TEAM_PARENT_CHECK_REQUIRED")
                _team_verify_paths(repo, candidate["evidence"])
                if name == "independent_review":
                    _team_verify_stage_reviewer(repo, after, candidate)
        if old["state"] != "ACTIVE" and any(before[k] != after[k] for k in ("operation", "pins", "stages", "source_manifest")):
            raise WorkflowRuntimeError("TEAM_PENDING_OWNER_MATH_MUTATION")
        prior_op, next_op = before["operation"], after["operation"]
        if prior_op["state"] in {"INTENT", "UNKNOWN"}:
            if any(prior_op[k] != next_op[k] for k in ("id", "kind", "subject", "command", "inputs")):
                raise WorkflowRuntimeError("TEAM_UNRESOLVED_OPERATION_CANNOT_BE_REPLACED")
            if next_op["state"] == "CONFIRMED":
                observation = _team_local_operation(repo, prior_op["id"])
                if (not next_op["evidence"] or observation is None
                        or observation.get("state") not in {"CONFIRMED", "NOT_EXECUTED"}
                        or observation.get("actor") != before["owner_thread_id"]
                        or observation.get("epoch") != old["epoch"]):
                    raise WorkflowRuntimeError("TEAM_OPERATION_CONFIRMATION_REQUIRED")
        return
    if any(before[k] != after[k] for k in ("operation", "pins", "stages", "source_manifest")):
        raise WorkflowRuntimeError("TEAM_TRANSFER_CHANGED_MATHEMATICAL_STATE")
    pair = old["state"], new["state"]
    allowed = {
        ("ACTIVE", "HANDOFF_INTENT"), ("HANDOFF_INTENT", "HANDOFF_QUIESCED"),
        ("HANDOFF_INTENT", "ACTIVE"), ("HANDOFF_QUIESCED", "ACTIVE"),
        ("HANDOFF_QUIESCED", "WATCH_RECONCILE_PENDING"), ("WATCH_RECONCILE_PENDING", "ACTIVE"),
        ("HANDOFF_QUIESCED", "RELEASED"), ("RELEASED", "CLAIM_PENDING"),
        ("CLAIM_ABORTED", "CLAIM_PENDING"), ("CLAIM_PENDING", "ACTIVE"),
        ("CLAIM_PENDING", "CLAIM_ABORTED"),
    }
    if pair not in allowed:
        raise WorkflowRuntimeError("TEAM_OWNER_TRANSITION_INVALID")
    transferring = pair[1] in {"CLAIM_PENDING", "WATCH_RECONCILE_PENDING"}
    if new["epoch"] != old["epoch"] + int(transferring):
        raise WorkflowRuntimeError("TEAM_OWNER_EPOCH_INVALID")
    _team_actor(repo, after if pair[1] == "CLAIM_PENDING" else before)
    transfer = new["transfer"]
    if transfer is None:
        raise WorkflowRuntimeError("TEAM_TRANSFER_ID_MISSING")
    if old["transfer"] is not None and pair[0] != "ACTIVE" and pair[1] != "CLAIM_ABORTED":
        for key in ("id", "mode", "from_ref", "from_thread", "to_ref", "to_thread"):
            if old["transfer"][key] != transfer[key]:
                raise WorkflowRuntimeError("TEAM_TRANSFER_IDENTITY_CHANGED")
    if pair[0] == "ACTIVE":
        if (transfer["from_ref"] != old["installation_ref"] or transfer["from_thread"] != before["owner_thread_id"]
                or transfer["to_ref"] == transfer["from_ref"] and transfer["to_thread"] == transfer["from_thread"]):
            raise WorkflowRuntimeError("TEAM_TRANSFER_PARTICIPANTS_INVALID")
    if pair[1] == "CLAIM_PENDING" and (transfer["from_ref"] != old["installation_ref"] or transfer["from_thread"] != before["owner_thread_id"]):
        raise WorkflowRuntimeError("TEAM_CLAIM_RELEASE_OWNER_MISMATCH")
    if pair[1] == "CLAIM_ABORTED":
        if (transfer["from_ref"] != old["installation_ref"] or transfer["from_thread"] != before["owner_thread_id"]
                or transfer["id"] == old["transfer"]["id"]):
            raise WorkflowRuntimeError("TEAM_ABORT_NEW_RELEASE_IDENTITY_REQUIRED")
    expected_ref = transfer["to_ref"] if transferring or pair[0] in {"WATCH_RECONCILE_PENDING", "CLAIM_PENDING"} else transfer["from_ref"]
    expected_thread = transfer["to_thread"] if expected_ref == transfer["to_ref"] and (transferring or pair[0] in {"WATCH_RECONCILE_PENDING", "CLAIM_PENDING"}) else transfer["from_thread"]
    if pair[1] == "CLAIM_ABORTED":
        expected_ref, expected_thread = old["installation_ref"], before["owner_thread_id"]
    if new["installation_ref"] != expected_ref or after["owner_thread_id"] != expected_thread:
        raise WorkflowRuntimeError("TEAM_TRANSFER_TARGET_MISMATCH")
    local = _team_local(repo)
    watch = local["watch"]
    if pair[1] in {"HANDOFF_QUIESCED", "RELEASED", "WATCH_RECONCILE_PENDING"}:
        _team_quiescence(repo, before if pair[1] != "HANDOFF_QUIESCED" else after)
        if any(item["state"] in {"RESERVED", "UNKNOWN"} for item in local["operations"].values()):
            raise WorkflowRuntimeError("TEAM_OUTSTANDING_EFFECT_RESERVATION")
    if pair[1] in {"RELEASED", "CLAIM_ABORTED"}:
        watch_transfer_id = old["transfer"]["id"] if pair[1] == "CLAIM_ABORTED" else transfer["id"]
        if watch is None or watch["state"] not in {"PAUSED", "ABSENT"} or watch["transfer_id"] != watch_transfer_id:
            raise WorkflowRuntimeError("TEAM_OLD_WATCH_NOT_QUIESCED")
        if any(item["state"] in {"RESERVED", "UNKNOWN"} for item in local["operations"].values()):
            raise WorkflowRuntimeError("TEAM_OUTSTANDING_EFFECT_RESERVATION")
    if pair[1] == "WATCH_RECONCILE_PENDING":
        if (transfer["mode"] != "SAME_INSTALLATION" or transfer["from_ref"] != transfer["to_ref"]
                or watch is None or watch["retarget_supported"] is not True
                or watch["target_thread"] != before["owner_thread_id"]):
            raise WorkflowRuntimeError("TEAM_WATCH_RETARGET_UNSUPPORTED_OR_UNVERIFIED")
    if pair[1] == "CLAIM_PENDING":
        receipt = local["operations"].get(transfer["id"] + ":release")
        if (transfer["mode"] != "CROSS_INSTALLATION" or transfer["from_ref"] == transfer["to_ref"]
                or receipt is None or receipt["remote_ownership"] != old
                or receipt["remote_thread"] != before["owner_thread_id"]
                or receipt["remote_commit"] != transfer["predecessor_commit"]
                or receipt["local_head"] != receipt["remote_commit"]
                or _team_git(repo, "rev-parse", "HEAD").decode().strip() != receipt["remote_commit"]):
            raise WorkflowRuntimeError("TEAM_VERIFIED_RELEASE_REQUIRED")
    if pair[0] == "CLAIM_PENDING" and pair[1] in {"ACTIVE", "CLAIM_ABORTED"}:
        original_transfer = old["transfer"]
        receipt = local["operations"].get(original_transfer["id"] + ":claim")
        if (receipt is None or receipt["remote_ownership"] != old
                or receipt["remote_thread"] != before["owner_thread_id"]):
            raise WorkflowRuntimeError("TEAM_VERIFIED_REMOTE_CLAIM_REQUIRED")
        parents = _team_git(repo, "show", "-s", "--format=%P", receipt["remote_commit"]).decode().split()
        if parents != [original_transfer["predecessor_commit"]]:
            raise WorkflowRuntimeError("TEAM_CLAIM_NOT_DIRECT_RELEASE_SUCCESSOR")
        if pair[1] == "CLAIM_ABORTED" and transfer["predecessor_commit"] != receipt["remote_commit"]:
            raise WorkflowRuntimeError("TEAM_ABORT_CLAIM_PREDECESSOR_REQUIRED")
    if pair[1] == "ACTIVE":
        if (watch is None or watch["state"] != "ACTIVE" or watch["target_thread"] != after["owner_thread_id"]
                or watch["epoch"] != new["epoch"] or watch["transfer_id"] != transfer["id"]
                or watch["scheduled_wake_at"] is None):
            raise WorkflowRuntimeError("TEAM_WATCH_RECONCILIATION_REQUIRED")
        if pair[0] in {"CLAIM_PENDING", "WATCH_RECONCILE_PENDING"}:
            watch_intents = [local["operations"].get(transfer["id"] + ":watch:" + action)
                             for action in ("CREATE", "UPDATE")]
            if (not any(item is not None and item["state"] == "CONFIRMED" for item in watch_intents)
                    or any(key.startswith(transfer["id"] + ":watch:") and value["state"] in {"RESERVED", "UNKNOWN"}
                           for key, value in local["operations"].items())):
                raise WorkflowRuntimeError("TEAM_WATCH_INTENT_CONFIRMATION_REQUIRED")


def _team_verify_stage_reviewer(repo: Path, data: dict[str, Any], stage: dict[str, Any]) -> None:
    from orchestrator import team_records

    assignments = _team_assignments(repo)
    ids = [key for key, row in assignments["assignments"].items()
           if row["assignment"]["assignee"] == stage["checked_by"]
           and row["assignment"]["subject"] == stage["subject"]["id"]
           and row["assignment"]["role"] in team_records.INDEPENDENT_ACTOR_ROLES]
    context = _team_assignment_context(repo, data, assignments, ids, set(stage["evidence"].values()))
    matched = []
    for key in ids:
        assignment = assignments["assignments"][key]["assignment"]
        sources = {row["path"]: row["sha256"] for row in assignment["input_hashes"]}
        if sources != data["source_manifest"]:
            continue
        team_records._validate_assignment_owner(assignment, context)
        _, result = team_records._validated_assignment_observation(assignment, context)
        if (result["state"] == "COMPLETED"
                and stage["evidence"].get(result["output_locator"]) == result["output_sha256"]):
            matched.append(key)
    if len(matched) != 1:
        raise WorkflowRuntimeError("TEAM_INDEPENDENT_COMPLETED_ASSIGNMENT_REQUIRED")


def _team_continuation(repo: Path, snapshot: StartupSnapshot, owned_paths: list[str]) -> dict[str, Any]:
    """Bounded, local-only observation inside the caller's existing read epoch."""
    blockers: list[dict[str, str]] = []
    card: dict[str, Any] = {"schema": "q3_continuation.v1", "status": "OBSERVATION_ONLY", "blockers": blockers}
    read_paths = (RESUME_PATH, RESUME_HISTORY_PATH, TEAM_ISSUES, TEAM_ASSIGNMENTS,
                  Path("orchestrator/state/CHANNEL_RUNTIME.json"), Path("docs/routeB_bus/PROSHKA_QUEUE.md"))
    observed: dict[Path, bytes | None] = {}
    try:
        for path in read_paths:
            target = repo / path
            if target.exists() and target.stat().st_size > TEAM_READ_MAX:
                raise WorkflowRuntimeError("TEAM_READ_LIMIT:" + str(path))
            observed[path] = _resume_file(repo, path)
        raw = observed[RESUME_PATH]
        if raw is None:
            raise WorkflowRuntimeError("TEAM_RESUME_MISSING")
        data, body = _resume_document(raw)
        records = _resume_history(observed[RESUME_HISTORY_PATH] or b"")
        if ("intent", data["revision"], raw) not in records.values():
            raise WorkflowRuntimeError("RESUME_CURRENT_CHECKSUM_MISMATCH")
        card["checkpoint"] = {"revision": data["revision"], "sha256": _resume_digest(raw), "path": str(RESUME_PATH)}
        card["owner"] = {"task": data["owner_thread_id"], "host_alias": data["owner_host_id"], **data.get("ownership", {})}
        card["owner"].pop("transfer", None)
        card["proposal"] = {name: body.split("## " + name + "\n", 1)[1].split("\n## ", 1)[0].strip()[:600]
                            for name in ("Mathematical frontier", "Next action")}
        card["operation"] = {k: v for k, v in data["operation"].items() if k not in {"evidence", "inputs"}}
        card["stages"] = {k: {"state": v["state"], "subject": v["subject"]} if isinstance(v, dict) else v
                          for k, v in data["stages"].items()}
        if data["schema"] != "q3_resume.v2":
            blockers.append({"scope": "EXECUTION", "code": "TEAM_RESUME_MIGRATION_REQUIRED"})
        else:
            _team_verify_paths(repo, data["source_manifest"])
            for stage in data["stages"].values():
                if stage["state"] == "DONE":
                    _team_verify_paths(repo, stage["evidence"])
        if data["pins"]["physical_goal"] != snapshot.selected_goal or data["pins"]["source_commit"] != snapshot.exact_source_pin:
            blockers.append({"scope": "MATHEMATICAL_INPUTS", "code": "TEAM_CANONICAL_SOURCE_MISMATCH"})
        runtime = json.loads(observed[read_paths[4]] or b"{}")
        phase = runtime.get("active_proshka_phase") or {}
        if data["pins"]["phase_id"] != phase.get("phase_id"):
            blockers.append({"scope": "DISPATCH", "code": "TEAM_PHASE_MISMATCH"})
        if data["schema"] == "q3_resume.v2":
            request = data["pins"]["request"]
            if data["pins"]["phase_key"] != phase.get("phase_key"):
                blockers.append({"scope": "DISPATCH", "code": "TEAM_SIX_FIELD_PHASE_MISMATCH"})
            if request["conversation_id"] != phase.get("conversation_id"):
                blockers.append({"scope": "DISPATCH", "code": "TEAM_OBSERVED_CHAT_RECONCILIATION_REQUIRED"})
            request_raw = _team_git(repo, "show", request["commit"] + ":" + request["path"])
            blob = _team_git(repo, "rev-parse", request["commit"] + ":" + request["path"]).decode().strip()
            if _resume_digest(request_raw) != request["sha256"] or blob != request["blob"]:
                raise WorkflowRuntimeError("TEAM_REQUEST_PIN_MISMATCH")
            for field, value in (("REQUEST_ID", data["pins"]["request_id"]), ("BOUNDARY_ID", request["boundary_id"])):
                found, error = _single_request_header(request_raw.decode(), field)
                if error or found != value:
                    raise WorkflowRuntimeError("TEAM_REQUEST_HEADER_MISMATCH:" + field)
            _team_git(repo, "merge-base", "--is-ancestor", data["pins"]["head"], snapshot.git_head or "INVALID")
        queue = (observed[read_paths[5]] or b"").decode()
        request_matches = re.findall(r"(?m)^##\s+" + re.escape(data["pins"]["request_id"]) + r"(?:\s|$)", queue)
        if len(request_matches) != 1:
            blockers.append({"scope": "DISPATCH", "code": "TEAM_REQUEST_BINDING_MISSING_OR_AMBIGUOUS"})
        if data["operation"]["state"] in {"INTENT", "UNKNOWN"}:
            blockers.append({"scope": "REPLAY", "code": "RECONCILE_ORIGINAL_OPERATION_NO_AUTOMATIC_RETRY"})
        if data["reconciliation_pending"]:
            blockers.append({"scope": "EXECUTION", "code": "RECOVERED_CHECKPOINT_REQUIRES_RECONCILIATION"})
        if data["schema"] == "q3_resume.v2":
            try:
                local = _team_local(repo)
                card["local"] = {"installation_ref": local["installation_ref"], "task": os.environ.get("CODEX_THREAD_ID"),
                                 "watch": "UNKNOWN" if local["watch"] is None else local["watch"]["state"]}
                _team_actor(repo, data)
                if data["ownership"]["state"] != "ACTIVE":
                    blockers.append({"scope": "EXECUTION", "code": "TEAM_OWNER_" + data["ownership"]["state"]})
            except (WorkflowRuntimeError, KeyError) as exc:
                blockers.append({"scope": "LOCAL_EXECUTION", "code": str(exc)[:240]})
        status = _team_git(repo, "status", "--porcelain=v1", "-z", "--untracked-files=all")
        if len(status) > 128 * 1024:
            raise WorkflowRuntimeError("TEAM_WHOLE_TREE_STATUS_LIMIT")
        paths, parts, index = [], status.split(b"\0"), 0
        while index < len(parts) and parts[index]:
            row = parts[index].decode("utf-8")
            paths.append({"path": row[3:], "status": row[:2], "ownership": "DECLARED" if row[3:] in owned_paths else "UNKNOWN"})
            index += 1
            if "R" in row[:2] or "C" in row[:2]:
                if index >= len(parts) or not parts[index]:
                    raise WorkflowRuntimeError("TEAM_RENAME_STATUS_TRUNCATED")
                paths.append({"path": parts[index].decode(), "status": "SOURCE", "ownership": "UNKNOWN"})
                index += 1
        card["whole_tree"] = {"dirty": paths[:24], "omitted": max(0, len(paths) - 24), "status_sha256": _resume_digest(status),
                              "all_paths_command": "git status --short --untracked-files=all"}
        card["registries"] = _team_registry_card(repo, observed)
        inventory = _team_writer_inventory(repo)
        card["writer_routes"] = {name: len(items) for name, items in inventory.items()}
        for path, before in observed.items():
            if _resume_file(repo, path) != before:
                raise WorkflowRuntimeError("TEAM_READ_PREIMAGE_CHANGED:" + str(path))
        if _team_git(repo, "status", "--porcelain=v1", "-z", "--untracked-files=all") != status:
            raise WorkflowRuntimeError("TEAM_WHOLE_TREE_CHANGED")
        card["native_checks"] = [
            {"status": "NEEDS_LIVE_OBSERVATION", "subject": data["owner_thread_id"], "read": "owning app task, its agents, durable outputs and native watch"},
            {"status": "NEEDS_LIVE_OBSERVATION", "subject": data["pins"]["request_id"], "read": "existing request/chat and committed result before new dispatch"},
        ]
    except (WorkflowRuntimeError, StartupRuntimeError, ValueError, OSError, KeyError) as exc:
        blockers.append({"scope": "CONTINUATION", "code": str(exc)[:240]})
        card["status"] = "HOLD"
    return card


def _team_registry_card(repo: Path, observed: dict[Path, bytes | None]) -> dict[str, Any]:
    from orchestrator import team_records

    result: dict[str, Any] = {}
    for name, path in (("issues", TEAM_ISSUES), ("assignments", TEAM_ASSIGNMENTS)):
        raw = observed[path]
        if raw is None:
            raise WorkflowRuntimeError("TEAM_REGISTRY_MISSING:" + str(path))
        registry = team_records.read_registry(raw, name, archive_loader=lambda relative: _resume_file(repo, Path(relative)))
        if name == "issues":
            items = [{"id": key, "state": value["state"], "severity": value["report"]["severity"],
                      "affected_operations": value["report"]["affected_operations"][:5]}
                     for key, value in registry[name].items()
                     if value["state"] not in {"AGENT_CONTEXT_ERROR", "EXPECTED_GUARD", "DUPLICATE", "FIX_PUSH_VERIFIED"}]
        else:
            items = [{"id": key, "state": value["assignment"]["status"],
                      "owner_task": value["assignment"]["owner_task"], "assignee": value["assignment"]["assignee"],
                      "next_check": value["assignment"]["next_check"]}
                     for key, value in registry[name].items()
                     if value["assignment"]["status"] not in {"DONE", "COMPLETED", "CANCELLED", "FAILED"}]
        result[name] = {"path": str(path), "sha256": _resume_digest(raw), "items": items[:6],
                        "omitted": max(0, len(items) - 6), "legacy": "PRESERVED_UNMAPPED_NOT_AUTOMATICALLY_CLOSED"}
    return result


def _team_locator(repo: Path, locator: str, expected: str, *, durable_only: bool = True) -> bytes:
    if locator.startswith("git:"):
        try:
            _, commit, path = locator.split(":", 2)
        except ValueError as exc:
            raise WorkflowRuntimeError("TEAM_GIT_LOCATOR_INVALID") from exc
        if not _team_hex(commit, 40):
            raise WorkflowRuntimeError("TEAM_GIT_LOCATOR_INVALID")
        _team_path_hashes({path: expected})
        raw = _team_git(repo, "show", commit + ":" + path)
    else:
        _team_path_hashes({locator: expected})
        raw = _resume_file(repo, Path(locator))
        if durable_only and not locator.startswith("docs/"):
            raise WorkflowRuntimeError("TEAM_DURABLE_CANONICAL_EVIDENCE_REQUIRED:" + locator)
    if _resume_digest(raw) != expected:
        raise WorkflowRuntimeError("TEAM_EVIDENCE_HASH_MISMATCH:" + locator)
    return raw


def _team_repair_source_map(rows: object) -> dict[str, str]:
    """Project transition source locators onto their exact repository paths."""
    if not isinstance(rows, list):
        raise WorkflowRuntimeError("TEAM_REPAIR_SOURCE_SET_INVALID")
    result: dict[str, str] = {}
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"locator", "sha256"}:
            raise WorkflowRuntimeError("TEAM_REPAIR_SOURCE_SET_INVALID")
        locator = row["locator"]
        path = locator.split(":", 2)[-1] if isinstance(locator, str) and locator.startswith("git:") else locator
        if not isinstance(path, str) or path in result:
            raise WorkflowRuntimeError("TEAM_REPAIR_SOURCE_SET_INVALID")
        result[path] = row["sha256"]
    return result


def _team_validate_repair_source_set(rows: object, expected: dict[str, str]) -> None:
    if _team_repair_source_map(rows) != expected:
        raise WorkflowRuntimeError("TEAM_ISSUE_RESULT_SOURCE_MISMATCH")


def _team_candidate_manifest(payload: dict[str, Any]) -> dict[str, str]:
    manifest = payload.get("candidate_manifest")
    if not isinstance(manifest, list):
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_MANIFEST_REQUIRED")
    result: dict[str, str] = {}
    for row in manifest:
        if not isinstance(row, dict) or set(row) != {"path", "sha256"}:
            raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_MANIFEST_INVALID")
        path, digest = row["path"], row["sha256"]
        if not isinstance(path, str) or path in result or not isinstance(digest, str):
            raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_MANIFEST_INVALID")
        result[path] = digest
    if not result:
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_MANIFEST_REQUIRED")
    return result


def _team_validate_repair_candidate(
    repo: Path, payload: dict[str, Any], *, base_commit: str
) -> dict[str, str]:
    """Bind one named repair diff and its bytes to a descendant Git commit."""
    candidate_commit = payload.get("candidate_commit")
    if not (_team_hex(base_commit, 40) or _team_hex(base_commit, 64)):
        raise WorkflowRuntimeError("TEAM_REPAIR_BASE_COMMIT_INVALID")
    if not (_team_hex(candidate_commit, 40) or _team_hex(candidate_commit, 64)):
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_COMMIT_INVALID")
    if candidate_commit == base_commit:
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_NOT_DESCENDANT")
    manifest = _team_candidate_manifest(payload)
    try:
        object_type = _team_git(repo, "cat-file", "-t", str(candidate_commit)).decode().strip()
    except WorkflowRuntimeError as exc:
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_COMMIT_INVALID") from exc
    if object_type != "commit":
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_COMMIT_INVALID")
    try:
        _team_git(repo, "merge-base", "--is-ancestor", base_commit, str(candidate_commit))
    except WorkflowRuntimeError as exc:
        raise WorkflowRuntimeError("TEAM_REPAIR_BASE_ANCESTRY_INVALID") from exc
    try:
        parents = _team_git(repo, "show", "-s", "--format=%P", str(candidate_commit)).decode().split()
    except (UnicodeDecodeError, WorkflowRuntimeError) as exc:
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_PARENT_INVALID") from exc
    if len(parents) != 1 or not (_team_hex(parents[0], 40) or _team_hex(parents[0], 64)):
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_PARENT_INVALID")
    try:
        changed_raw = _team_git(
            repo, "diff", "--name-only", "--no-renames", "-z", parents[0], str(candidate_commit), "--"
        )
        changed_paths = [item.decode("utf-8") for item in changed_raw.split(b"\0") if item]
    except (UnicodeDecodeError, WorkflowRuntimeError) as exc:
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_DIFF_INVALID") from exc
    if len(changed_paths) != len(set(changed_paths)) or set(changed_paths) != set(manifest):
        raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_DIFF_MISMATCH")
    for path, expected in manifest.items():
        try:
            raw = _team_git(repo, "show", f"{candidate_commit}:{path}")
        except WorkflowRuntimeError as exc:
            raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_PATH_INVALID:" + path) from exc
        if _resume_digest(raw) != expected:
            raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_BYTES_MISMATCH:" + path)
    return manifest


def team_record(repo: Path, *, kind: str, candidate: Path, expected_sha256: str) -> dict[str, Any]:
    from orchestrator import team_records

    if kind == "archive":
        return _team_archive(repo, candidate=candidate, expected_sha256=expected_sha256)
    routes = {"report": (TEAM_ISSUES, team_records.prepare_report),
              "issue-event": (TEAM_ISSUES, team_records.prepare_issue_event),
              "assignment": (TEAM_ASSIGNMENTS, team_records.prepare_assignment)}
    if kind not in routes:
        raise WorkflowRuntimeError("TEAM_RECORD_KIND_INVALID")
    relative, prepare = routes[kind]
    _team_registered(repo, "team-record", TEAM_RECORD_WRITE_PATHS)
    payload = team_records.load_payload(candidate.read_bytes())
    with _execution_writer_epoch(repo) as epoch:
        actor = team_guard(repo, command="workflow-team-record", paths=[str(relative)])
        if actor is None:
            raise WorkflowRuntimeError("TEAM_RUNTIME_NOT_ACTIVATED")
        raw = _resume_file(repo, relative)
        if raw is None:
            raise WorkflowRuntimeError("TEAM_REGISTRY_MISSING")
        updated, receipt = prepare(raw, payload, expected_sha256,
                                   archive_loader=lambda path: _resume_file(repo, Path(path)))
        # Exact replay restores the SAME receipt even when current inputs have moved.
        if receipt["status"] != "NOOP":
            for field in ("evidence", "source_binding"):
                for row in payload.get(field, []):
                    _team_locator(repo, row["locator"], row["sha256"], durable_only=field == "evidence")
            for row in payload.get("input_paths", []):
                _team_locator(repo, "git:" + payload["base_commit"] + ":" + row["path"], row["sha256"])
            if kind == "report":
                rule = payload["expected_rule_source"]
                _team_locator(repo, rule["locator"], rule["sha256"])
                _, data, _ = _team_current(repo)
                assignments = _team_assignments(repo)
                context = _team_assignment_context(repo, data, assignments, [payload["assignment_id"]],
                    {team_records._payload_sha(payload)})
                team_records.validate_report_provenance(payload, assignments, context)
            elif kind == "assignment":
                if (payload["owner_task"] != actor["task"] or payload["owner_epoch"] != actor["epoch"]
                        or payload["owner_installation_ref"] != actor["installation_ref"]):
                    raise WorkflowRuntimeError("TEAM_ASSIGNMENT_OWNER_MISMATCH")
                for row in payload["input_hashes"]:
                    _team_locator(repo, "git:" + payload["base_commit"] + ":" + row["path"], row["sha256"])
                # CREATE is an intent, never a native agent launch receipt.
                if payload["operation"] == "CREATE" and payload["status"] not in {"ASSIGNED", "PENDING"}:
                    raise WorkflowRuntimeError("TEAM_ASSIGNMENT_LAUNCH_OBSERVATION_REQUIRED")
            if kind == "issue-event":
                _, data, _ = _team_current(repo)
                assignments = _team_assignments(repo)
                ids = [] if payload["transition"] in team_records.OWNER_TRANSITIONS else [
                    key for key, row in assignments["assignments"].items()
                    if row["assignment"]["assignee"] == payload["actor_id"]
                    and row["assignment"]["subject"] in {payload["issue_id"], payload.get("repair_subject_id")}
                ]
                context = _team_assignment_context(repo, data, assignments, ids,
                    {row["sha256"] for row in payload["evidence"]})
                review_base_commit = None
                if payload["transition"] == "FIX_VERIFIED":
                    review_issues = team_records.read_registry(
                        raw, "issues", archive_loader=lambda path: _resume_file(repo, Path(path))
                    )
                    review_issue = review_issues["issues"].get(payload["issue_id"])
                    if review_issue is None:
                        raise WorkflowRuntimeError("TEAM_ISSUE_UNKNOWN")
                    review_base_commit = review_issue["report"]["base_commit"]
                provenance = team_records.validate_issue_event_actor(
                    payload, assignments, context, expected_base_commit=review_base_commit
                )
                if provenance["actor_class"] != "owner":
                    assignment = assignments["assignments"][provenance["assignment_id"]]["assignment"]
                    # Only the assigned issue/repair and the exact checked source set.
                    if assignment["assignment_id"] not in ids:
                        raise WorkflowRuntimeError("TEAM_ISSUE_ASSIGNMENT_SUBJECT_MISMATCH")
                    expected = {row["path"]: row["sha256"] for row in assignment["input_hashes"]}
                    _team_validate_repair_source_set(payload["source_binding"], expected)
                    if payload["transition"] == "FIX_VERIFIED":
                        manifest = _team_candidate_manifest(payload)
                        if not set(manifest).issubset(set(assignment["permitted_paths"])):
                            raise WorkflowRuntimeError("TEAM_REPAIR_CANDIDATE_SCOPE_MISMATCH")
            if kind == "issue-event" and payload["transition"] in {"FIX_COMMITTED", "FIX_PUSH_VERIFIED"}:
                issues = team_records.read_registry(raw, "issues",
                    archive_loader=lambda path: _resume_file(repo, Path(path)))
                issue = issues["issues"].get(payload["issue_id"])
                if issue is None:
                    raise WorkflowRuntimeError("TEAM_ISSUE_UNKNOWN")
                _team_validate_repair_candidate(repo, payload, base_commit=issue["report"]["base_commit"])
                if payload["transition"] == "FIX_PUSH_VERIFIED":
                    remote = _team_local_operation(repo, payload["repair_subject_id"] + ":publication")
                    if remote is None:
                        raise WorkflowRuntimeError("TEAM_REPAIR_REMOTE_OBSERVATION_REQUIRED")
                    if remote.get("remote_commit") != payload["candidate_commit"]:
                        raise WorkflowRuntimeError("TEAM_REPAIR_REMOTE_COMMIT_MISMATCH")
                    _team_git(repo, "merge-base", "--is-ancestor",
                              payload["candidate_commit"], remote["remote_commit"])
        stable_receipt = {**receipt, "status": "RECORDED"}
        receipt_path = Path("docs/session_protocols/team-record-" + receipt["event_id"] + ".json")
        prior_receipt = _resume_file(repo, receipt_path)
        receipt_bytes = team_records.canonical_json(stable_receipt)
        if prior_receipt is not None and prior_receipt != receipt_bytes:
            raise WorkflowRuntimeError("TEAM_RECEIPT_CONFLICT")
        if updated != raw:
            _resume_cas_bytes(repo, relative, raw, updated, epoch)
        else:
            _resume_sync(repo / relative)
        # Crash after the event but before this write is repaired by exact replay.
        if prior_receipt is None:
            _resume_cas_bytes(repo, receipt_path, None, receipt_bytes, epoch)
        _resume_sync(repo / receipt_path)
        return {**receipt, "receipt_path": str(receipt_path), "mathematical_acceptance": False}


def _team_archive(repo: Path, *, candidate: Path, expected_sha256: str) -> dict[str, Any]:
    """Move verified frames to immutable history; an intent alone is never completion."""
    from orchestrator import team_records

    _team_registered(repo, "team-record", TEAM_RECORD_WRITE_PATHS)
    request = team_records.load_payload(candidate.read_bytes())
    if (set(request) != {"schema", "registry_kind", "event_count", "expected_registry_sha256", "archive_ref"}
            or request["schema"] != "q3_team_archive_request.v1"
            or request["registry_kind"] not in {"issues", "assignments"}
            or request["expected_registry_sha256"] != expected_sha256
            or not re.fullmatch(r"docs/session_protocols/team-archive-[A-Za-z0-9_-]+\.json", request["archive_ref"])):
        raise WorkflowRuntimeError("TEAM_ARCHIVE_REQUEST_INVALID")
    relative = TEAM_ISSUES if request["registry_kind"] == "issues" else TEAM_ASSIGNMENTS
    archive_path = Path(request["archive_ref"])
    intent_path = archive_path.with_name(archive_path.stem + "-intent.json")
    with _execution_writer_epoch(repo) as epoch:
        if team_guard(repo, command="workflow-team-record", paths=[str(relative)]) is None:
            raise WorkflowRuntimeError("TEAM_RUNTIME_NOT_ACTIVATED")
        raw = _resume_file(repo, relative)
        if raw is None:
            raise WorkflowRuntimeError("TEAM_REGISTRY_MISSING")
        loader = lambda path: _resume_file(repo, Path(path))
        registry = team_records.read_registry(raw, request["registry_kind"], archive_loader=loader)
        intent_raw = _resume_file(repo, intent_path)
        markers = [item for item in registry["_archive_markers"]
                   if item["event"]["payload"]["archive_ref"]["path"] == str(archive_path)]
        if markers:
            if len(markers) != 1 or intent_raw is None:
                raise WorkflowRuntimeError("TEAM_ARCHIVE_REPLAY_INTENT_REQUIRED")
            intent = team_records.load_payload(intent_raw)
            if (set(intent) != {"schema", "request", "receipt"}
                    or intent["schema"] != "q3_team_archive_intent.v1" or intent["request"] != request
                    or intent["receipt"]["event_id"] != markers[0]["event"]["event_id"]
                    or intent["receipt"]["pre_registry_sha256"] != expected_sha256
                    or intent["receipt"]["archive_sha256"] != markers[0]["event"]["payload"]["archive_ref"]["sha256"]):
                raise WorkflowRuntimeError("TEAM_ARCHIVE_REPLAY_CONFLICT")
            receipt, updated = intent["receipt"], raw
        else:
            archive_bytes, updated, receipt = team_records.prepare_archive(raw, request["registry_kind"], expected_sha256,
                str(archive_path), event_count=request["event_count"], archive_loader=loader)
            archive_before = _resume_file(repo, archive_path)
            if archive_before is not None and archive_before != archive_bytes:
                raise WorkflowRuntimeError("TEAM_ARCHIVE_PATH_CONFLICT")
            if archive_before is None:
                _resume_cas_bytes(repo, archive_path, None, archive_bytes, epoch)
            intent = {"schema": "q3_team_archive_intent.v1", "request": request, "receipt": receipt}
            intent_bytes = team_records.canonical_json(intent)
            if intent_raw is not None and intent_raw != intent_bytes:
                raise WorkflowRuntimeError("TEAM_ARCHIVE_INTENT_CONFLICT")
            if intent_raw is None:
                _resume_cas_bytes(repo, intent_path, None, intent_bytes, epoch)
            team_records.read_registry(updated, request["registry_kind"], archive_loader=loader)
            _resume_cas_bytes(repo, relative, raw, updated, epoch)
        receipt_path = Path("docs/session_protocols/team-record-" + receipt["event_id"] + ".json")
        receipt_bytes = team_records.canonical_json(receipt)
        receipt_before = _resume_file(repo, receipt_path)
        if receipt_before is not None and receipt_before != receipt_bytes:
            raise WorkflowRuntimeError("TEAM_RECEIPT_CONFLICT")
        if receipt_before is None:
            _resume_cas_bytes(repo, receipt_path, None, receipt_bytes, epoch)
        for path in (archive_path, intent_path, relative, receipt_path):
            _resume_sync(repo / path)
        return {**receipt, "status": "NOOP" if markers else "RECORDED", "receipt_path": str(receipt_path),
                "mathematical_acceptance": False}


def _resume_document(raw: bytes) -> tuple[dict[str, Any], str]:
    """Validate the observation envelope, never its mathematical truth/authority."""
    from orchestrator.routeb_goal_state import load_unique_yaml

    try:
        if len(raw) > RESUME_MAX_BYTES or not raw.endswith(b"\n"):
            raise ValueError("size or final newline")
        text = raw.decode("utf-8")
        if not text.startswith("---\n"):
            raise ValueError("front matter")
        header, body = text[4:].split("\n---\n", 1)
        data = load_unique_yaml(header)
        if not isinstance(data, dict) or data.get("schema") not in {"q3_resume.v1", "q3_resume.v2"}:
            raise ValueError("schema")
        revision = data.get("revision")
        if type(revision) is not int or revision < 1:
            raise ValueError("revision")
        if not re.fullmatch(r"ABSENT|[0-9a-f]{64}", str(data.get("previous_sha256"))):
            raise ValueError("previous_sha256")
        observed = datetime.fromisoformat(data["observed_at"])
        if observed.utcoffset() is None:
            raise ValueError("observed_at timezone")
        if not re.fullmatch(r"[0-9a-f-]{36}", data["owner_thread_id"]):
            raise ValueError("owner_thread_id")
        if not isinstance(data.get("owner_host_id"), str) or not data["owner_host_id"].strip():
            raise ValueError("owner_host_id")
        if type(data.get("reconciliation_pending")) is not bool:
            raise ValueError("reconciliation_pending")
        if "recovery_from" not in data or not (
            data["recovery_from"] is None or isinstance(data["recovery_from"], str)
        ):
            raise ValueError("recovery_from")
        for field in ("pins", "stages", "operation"):
            if not isinstance(data.get(field), dict):
                raise ValueError(field)
        for field in ("head", "physical_goal", "source_commit", "request_id", "phase_id"):
            if not isinstance(data["pins"].get(field), str) or not data["pins"][field]:
                raise ValueError("pins." + field)
        for field in ("receipt", "independent_review", "parent_check", "acceptance", "publication"):
            stage = data["stages"].get(field)
            state = stage.get("state") if isinstance(stage, dict) else stage
            if state not in {
                "NOT_STARTED", "PENDING", "UNKNOWN", "DONE", "REJECTED",
            }:
                raise ValueError("stages." + field)
        operation = data["operation"]
        if operation.get("kind") not in {"NONE", "DISPATCH", "COMPUTE", "PUBLISH", "WATCH", "ASSIGN"}:
            raise ValueError("operation.kind")
        if operation.get("state") not in {"NONE", "INTENT", "UNKNOWN", "CONFIRMED"}:
            raise ValueError("operation.state")
        if not isinstance(operation.get("id"), str) or not isinstance(operation.get("evidence"), list):
            raise ValueError("operation identity/evidence")
        if not all(isinstance(item, str) for item in operation["evidence"]):
            raise ValueError("operation evidence paths")
        if operation["kind"] != "NONE" and not operation["id"]:
            raise ValueError("operation id missing")
        if (operation["kind"] == "NONE") != (operation["state"] == "NONE"):
            raise ValueError("operation none mismatch")
        if operation["state"] == "CONFIRMED" and not operation["evidence"]:
            raise ValueError("operation receipt missing")
        if data["schema"] == "q3_resume.v2":
            _team_document(data)
        for section in RESUME_SECTIONS:
            marker = "## " + section + "\n"
            if body.count(marker) != 1 or not body.split(marker)[1].split("\n## ")[0].strip():
                raise ValueError("section " + section)
        return data, body
    except (ValueError, TypeError, KeyError, UnicodeError, yaml.YAMLError) as exc:
        raise WorkflowRuntimeError(f"RESUME_INVALID:{exc}") from exc


def _resume_history_record(kind: str, revision: int, raw: bytes) -> tuple[str, bytes]:
    import base64

    if kind not in {"goal", "resume", "intent", "corrupt"}:
        raise WorkflowRuntimeError("RESUME_HISTORY_KIND_INVALID")
    encoded = base64.b64encode(raw) if kind == "corrupt" else raw
    fence = b"`" * max(4, 1 + max((len(m[0]) for m in re.finditer(rb"`+", encoded)), default=0))
    digest = _resume_digest(raw)
    key = f"{kind}-{revision}-{digest}"
    metadata = json.dumps({
        "key": key, "kind": kind, "revision": revision, "sha256": digest,
        "size": len(encoded), "fence": fence.decode(),
    }, sort_keys=True, separators=(",", ":")).encode()
    return key, (b"<!-- q3-history " + metadata + b" -->\n" + fence + b"text\n"
                 + encoded + b"\n" + fence + b"\n<!-- /q3-history -->\n\n")


def _resume_history(raw: bytes) -> dict[str, tuple[str, int, bytes]]:
    import base64

    records: dict[str, tuple[str, int, bytes]] = {}
    revisions: dict[int, bytes] = {}
    try:
        if not raw.startswith(RESUME_HISTORY_HEADER):
            raise ValueError("header")
        offset = len(RESUME_HISTORY_HEADER)
        while offset < len(raw):
            start = offset
            end = raw.index(b"\n", offset)
            line = raw[offset:end]
            if not line.startswith(b"<!-- q3-history ") or not line.endswith(b" -->"):
                raise ValueError("entry header")
            meta = json.loads(line[len(b"<!-- q3-history "):-4])
            fence = meta["fence"].encode()
            offset = end + 1 + len(fence) + len(b"text\n")
            size = meta["size"]
            if type(size) is not int or size < 0:
                raise ValueError("size")
            encoded = raw[offset:offset + size]
            payload = base64.b64decode(encoded, validate=True) if meta["kind"] == "corrupt" else encoded
            kind, revision = meta["kind"], meta["revision"]
            if type(revision) is not int or revision < 0:
                raise ValueError("revision")
            key, canonical = _resume_history_record(kind, revision, payload)
            if raw[start:start + len(canonical)] != canonical or key in records:
                raise ValueError("bytes/hash/duplicate")
            if kind == "goal" and (records or revision != 0):
                raise ValueError("original goal must be first")
            if kind in {"resume", "intent"}:
                parsed, _ = _resume_document(payload)
                if parsed["revision"] != revision or (revision in revisions and revisions[revision] != payload):
                    raise ValueError("conflicting revision")
                revisions[revision] = payload
            records[key] = kind, revision, payload
            offset = start + len(canonical)
        if not records or next(iter(records.values()))[0] != "goal":
            raise ValueError("original goal missing")
        if revisions and sorted(revisions) != list(range(1, len(revisions) + 1)):
            raise ValueError("gapped/orphan revision")
        return records
    except (ValueError, TypeError, KeyError, UnicodeError) as exc:
        raise WorkflowRuntimeError(f"RESUME_HISTORY_INVALID:{exc}") from exc


def _resume_file(repo: Path, relative: Path) -> bytes | None:
    if relative.is_absolute() or ".." in relative.parts or _has_symlink_component(repo, relative):
        raise WorkflowRuntimeError("RESUME_UNSAFE_PATH:" + str(relative))
    path = repo / relative
    try:
        if not stat.S_ISREG(path.lstat().st_mode):
            raise WorkflowRuntimeError("RESUME_NOT_REGULAR:" + str(relative))
        return path.read_bytes()
    except FileNotFoundError:
        return None


def _resume_cas_bytes(
    repo: Path, relative: Path, before: bytes | None, after: bytes,
    epoch: _ExecutionWriterEpoch, *, mode: int | None = None,
) -> None:
    """Used by checkpoint saves and the owner-scoped one-time document migration."""
    epoch.recheck()
    if _resume_file(repo, relative) != before:
        raise WorkflowRuntimeError("RESUME_PREIMAGE_CHANGED:" + str(relative))
    if mode is None:
        _atomic_bytes(repo / relative, after)
    else:
        _atomic_bytes(repo / relative, after, mode=mode)
    epoch.recheck()
    if _resume_file(repo, relative) != after:
        raise WorkflowRuntimeError("RESUME_READBACK_MISMATCH:" + str(relative))


def _resume_sync(path: Path) -> None:
    # A retry after replace but before directory fsync must finish durability too.
    with path.open("rb") as handle:
        os.fsync(handle.fileno())
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def resume_checkpoint(
    repo: Path, *, candidate: Path, expected_sha256: str,
    dry_run: bool = False, recover_from: str | None = None,
) -> dict[str, Any]:
    """Persist observations only. No dispatch, selector, Git delivery or admission."""
    from orchestrator.startup_runtime import validate_battle_v10_control

    payload = candidate.read_bytes()
    proposed, proposed_body = _resume_document(payload)
    if proposed["previous_sha256"] != expected_sha256:
        raise WorkflowRuntimeError("RESUME_EXPECTED_PREDECESSOR_MISMATCH")
    with _execution_writer_epoch(repo) as epoch:
        plan = live_plan_v10(
            repo, owned_paths=[str(RESUME_PATH), str(RESUME_HISTORY_PATH)],
            _writer_epoch=epoch,
        )
        if plan.get("status") == "FATAL" or plan.get("startup", {}).get("fatal_errors"):
            raise WorkflowRuntimeError("RESUME_STARTUP_FATAL:" + str(plan.get("holds")))
        control = validate_battle_v10_control(repo)
        manifest = _resume_file(repo, TOOLS)
        tool = load_tool_index(repo / TOOLS).get("workflow-resume-checkpoint", {})
        if (tool.get("status") != "ENABLED" or tool.get("writes") is not True
                or tool.get("write_paths") != [str(RESUME_PATH), str(RESUME_HISTORY_PATH)]):
            raise WorkflowRuntimeError("RESUME_TOOL_NOT_REGISTERED")
        current = _resume_file(repo, RESUME_PATH)
        history = _resume_file(repo, RESUME_HISTORY_PATH)
        if history is None:
            raise WorkflowRuntimeError("RESUME_HISTORY_MISSING")
        records = _resume_history(history)
        versions = {version: raw for kind, version, raw in records.values() if kind in {"resume", "intent"}}
        if proposed["revision"] in versions and versions[proposed["revision"]] != payload:
            raise WorkflowRuntimeError("RESUME_REVISION_CONFLICT")
        # A lost receipt is safely retryable only with the identical candidate and predecessor.
        if current == payload:
            if proposed["schema"] == "q3_resume.v2":
                _team_actor(repo, proposed)
            if versions.get(proposed["revision"]) != payload:
                raise WorkflowRuntimeError("RESUME_INTENT_ARCHIVE_MISSING")
            if expected_sha256 != "ABSENT" and not any(
                _resume_digest(raw) == expected_sha256 and kind in {"resume", "corrupt"}
                for kind, _, raw in records.values()
            ):
                raise WorkflowRuntimeError("RESUME_PREDECESSOR_ARCHIVE_MISSING")
            if proposed["recovery_from"] != recover_from:
                raise WorkflowRuntimeError("RESUME_RECOVERY_REPLAY_MISMATCH")
            if not dry_run:
                _resume_sync(repo / RESUME_HISTORY_PATH)
                _resume_sync(repo / RESUME_PATH)
                epoch.recheck()
                if (_resume_file(repo, RESUME_PATH) != payload
                        or _resume_file(repo, RESUME_HISTORY_PATH) != history):
                    raise WorkflowRuntimeError("RESUME_READBACK_MISMATCH")
            return {"status": "NOOP", "revision": proposed["revision"],
                    "sha256": _resume_digest(payload), "writes_performed": False}
        if _resume_digest(current) != expected_sha256:
            raise WorkflowRuntimeError("RESUME_PREIMAGE_CHANGED:" + str(RESUME_PATH))
        previous = None
        if current is not None:
            try:
                previous, _ = _resume_document(current)
                if versions.get(previous["revision"]) != current:
                    raise WorkflowRuntimeError("RESUME_CURRENT_CHECKSUM_MISMATCH")
            except WorkflowRuntimeError:
                previous = None
                if not recover_from:
                    raise WorkflowRuntimeError("RESUME_CORRUPT_REQUIRES_RECOVERY")
        if recover_from:
            source = records.get(recover_from)
            if not source or source[0] not in {"resume", "intent"} or previous is not None:
                raise WorkflowRuntimeError("RESUME_RECOVERY_SOURCE_INVALID")
            restored, restored_body = _resume_document(source[2])
            mutable = {"revision", "observed_at", "previous_sha256", "reconciliation_pending", "recovery_from"}
            if (proposed_body != restored_body
                    or {k: v for k, v in proposed.items() if k not in mutable}
                    != {k: v for k, v in restored.items() if k not in mutable}
                    or proposed["recovery_from"] != recover_from
                    or proposed["reconciliation_pending"] is not True):
                raise WorkflowRuntimeError("RESUME_RECOVERY_CONTENT_MISMATCH")
        elif proposed["recovery_from"] is not None or (current is None and any(
                kind == "resume" for kind, _, _ in records.values())):
            raise WorkflowRuntimeError("RESUME_RECOVERY_REQUIRED")
        if previous is not None and (control.team_runtime_version == 1 or proposed["schema"] == "q3_resume.v2"):
            _team_owner_transition(repo, previous, proposed)
        elif proposed["schema"] == "q3_resume.v2":
            _team_actor(repo, proposed)
            if proposed["ownership"]["epoch"] < _team_local(repo)["epoch_floor"]:
                raise WorkflowRuntimeError("TEAM_RETIRED_EPOCH")
        last = (max([0, *(v for v in versions if v != proposed["revision"])])
                if recover_from else previous["revision"] if previous else 0)
        if not recover_from and any(version > last + 1 for version in versions):
            raise WorkflowRuntimeError("RESUME_ORPHAN_INTENT")
        if proposed["revision"] != last + 1:
            raise WorkflowRuntimeError("RESUME_REVISION_CONFLICT")
        updated_history = history
        archived_key = None
        if current is not None:
            kind, version = ("resume", previous["revision"]) if previous else ("corrupt", 0)
            archived_key, entry = _resume_history_record(kind, version, current)
            if kind == "resume" and version in versions and versions[version] != current:
                raise WorkflowRuntimeError("RESUME_REVISION_CONFLICT")
            if archived_key not in records:
                updated_history += entry
        intent_key, intent_entry = _resume_history_record("intent", proposed["revision"], payload)
        if intent_key not in records:
            updated_history += intent_entry
        _resume_history(updated_history)
        if not dry_run:
            epoch.recheck()
            if (validate_battle_v10_control(repo) != control
                    or _resume_file(repo, TOOLS) != manifest):
                raise WorkflowRuntimeError("RESUME_AUTHORITY_CHANGED")
            if _resume_file(repo, RESUME_PATH) != current:
                raise WorkflowRuntimeError("RESUME_PREIMAGE_CHANGED:" + str(RESUME_PATH))
            if updated_history != history:
                _resume_cas_bytes(repo, RESUME_HISTORY_PATH, history, updated_history, epoch)
            _resume_sync(repo / RESUME_HISTORY_PATH)
            # A crash here leaves an idempotently reusable archive, never a lost preimage.
            if _resume_file(repo, RESUME_HISTORY_PATH) != updated_history:
                raise WorkflowRuntimeError("RESUME_HISTORY_CHANGED")
            _resume_cas_bytes(repo, RESUME_PATH, current, payload, epoch)
        return {"status": "DRY_RUN" if dry_run else "SAVED",
                "revision": proposed["revision"], "sha256": _resume_digest(payload),
                "archived_key": archived_key, "reconciliation_pending": proposed["reconciliation_pending"],
                "writes_performed": not dry_run, "authority": "OBSERVATIONS_ONLY"}


def _terminal_goal_bytes(goal_path: Path) -> bytes:
    raw = goal_path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise WorkflowRuntimeError("GOAL_TERMINALIZATION_INVALID_UTF8") from exc
    fence = re.search(r"```(?:yaml|yml)\s*\n(?P<body>.*?)```", text, re.DOTALL | re.IGNORECASE)
    if fence is None:
        raise WorkflowRuntimeError("GOAL_TERMINALIZATION_HEADER_MISSING")
    body = fence.group("body")
    matches = list(re.finditer(r"(?m)^STATUS:\s*OPEN\s*$", body))
    if len(matches) != 1:
        raise WorkflowRuntimeError("GOAL_TERMINALIZATION_STATUS_INVALID")
    match = matches[0]
    start = fence.start("body") + match.start()
    end = fence.start("body") + match.end()
    return (text[:start] + "STATUS: CLOSED" + text[end:]).encode()


def _load_closed_json(path: Path, *, code: str) -> dict[str, Any]:
    try:
        value = _load_unique_json(path)
    except StartupRuntimeError as exc:
        raise WorkflowRuntimeError(f"{code}:{exc}") from exc
    return value


def _compact_stage(receipt: dict[str, Any]) -> dict[str, Any]:
    compact = {
        key: receipt.get(key)
        for key in ("label", "exit", "duration_ms", "output_sha256")
    }
    compact["schema"] = "q3_close_stage.v1"
    compact["status"] = "PASS" if receipt.get("exit") == 0 else "FAIL"
    return compact


def _validate_phase_close_output(path: Path) -> tuple[dict[str, Any], str]:
    try:
        payload = _load_unique_json(path)
    except StartupRuntimeError as exc:
        raise WorkflowRuntimeError(f"PHASE_CLOSE_OUTPUT_INVALID:{exc}") from exc
    required = {
        "schema", "derived_executed", "derived_status", "gates",
        "verdict_migration", "blueprint_exit", "manual_debt",
        "commit_push_performed", "PX_RH_CLAIM",
    }
    if set(payload) != required or payload.get("schema") != "q3_phase_close.v1":
        raise WorkflowRuntimeError("PHASE_CLOSE_OUTPUT_SCHEMA_INVALID")
    gates = payload.get("gates")
    statuses = payload.get("derived_status")
    migration = payload.get("verdict_migration")
    debt = payload.get("manual_debt")
    if (
        not isinstance(gates, list)
        or not gates
        or any(
            not isinstance(row, dict)
            or set(row) != {"path", "exit"}
            or row.get("exit") != 0
            for row in gates
        )
        or not isinstance(statuses, list)
        or not statuses
        or any(
            not isinstance(row, dict)
            or set(row) != {"id", "status"}
            or row.get("status") not in {"FRESH", "CURRENT_WORKTREE"}
            for row in statuses
        )
        or not any(row.get("id") == "routeb-publication-blueprint" for row in statuses)
        or not isinstance(migration, dict)
        or migration.get("exit") != 0
        or migration.get("pending") is not False
        or not isinstance(debt, dict)
        or set(debt) != {"assembly_review_required", "insight_required", "cards"}
        or any(not isinstance(items, list) or items for items in debt.values())
        or payload.get("blueprint_exit") != 0
        or payload.get("commit_push_performed") is not False
        or payload.get("PX_RH_CLAIM") != "NOT_MADE"
    ):
        raise WorkflowRuntimeError("PHASE_CLOSE_OUTPUT_NOT_GREEN")
    canonical = json.dumps(
        payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    if len(canonical) > 32768:
        raise WorkflowRuntimeError("PHASE_CLOSE_OUTPUT_NOT_GREEN")
    return payload, hashlib.sha256(canonical).hexdigest()


def _phase_output_fingerprints(repo: Path, payload: dict[str, Any]) -> dict[str, str]:
    from orchestrator import dependency_registry

    ids = {row["id"] for row in payload["derived_status"]}
    if "routeb-publication-blueprint" not in ids:
        raise WorkflowRuntimeError("PHASE_CLOSE_BLUEPRINT_STATUS_MISSING")
    registry = dependency_registry.load_registry(
        repo / "docs/cartographer/DERIVED_ARTIFACTS.yaml"
    )
    blueprint_rows = [
        row for row in registry if row["id"] == "routeb-publication-blueprint"
    ]
    if len(blueprint_rows) != 1 or len(blueprint_rows[0]["outputs"]) != 12:
        raise WorkflowRuntimeError("PHASE_CLOSE_BLUEPRINT_OUTPUT_SET_INVALID")
    outputs: dict[str, str] = {}
    for row in blueprint_rows:
        for pattern_value in row["outputs"]:
            pattern = str(pattern_value)
            paths = (
                sorted(repo.glob(pattern))
                if any(char in pattern for char in "*?[")
                else [repo / pattern]
            )
            for path in paths:
                relative = _lexical_relative(repo, path)
                if (
                    _has_symlink_component(repo, relative)
                    or not path.is_file()
                ):
                    raise WorkflowRuntimeError(
                        f"PHASE_CLOSE_DERIVED_OUTPUT_INVALID:{relative.as_posix()}"
                    )
                outputs[relative.as_posix()] = _sha256(path)
    if not outputs:
        raise WorkflowRuntimeError("PHASE_CLOSE_DERIVED_OUTPUTS_MISSING")
    return dict(sorted(outputs.items()))


def _close_input_hashes(
    *, answer_path: Path, attempt_path: Path, next_goal_spec: Path | None,
    channel_runtime: Path, current_phase_key: Path | None = None,
) -> dict[str, str]:
    result = {
        "answer": _sha256(answer_path),
        "attempt": _sha256(attempt_path),
        "channel_runtime": _sha256(channel_runtime),
    }
    if next_goal_spec is not None:
        result["next_goal_spec"] = _sha256(next_goal_spec)
    if current_phase_key is not None:
        result["current_phase_key"] = _sha256(current_phase_key)
    return result


def _recheck_close_inputs(
    repo: Path, paths: dict[str, Path], expected: dict[str, str]
) -> None:
    for label, path in paths.items():
        try:
            relative = _lexical_relative(repo, path)
        except Exception as exc:
            raise WorkflowRuntimeError(f"WORKFLOW_CLOSE_INPUT_OUTSIDE_REPO:{label}") from exc
        if (
            _has_symlink_component(repo, relative)
            or not path.is_file()
            or _sha256(path) != expected[label]
        ):
            raise WorkflowRuntimeError(f"WORKFLOW_CLOSE_INPUT_DRIFT:{label}")


def _recheck_close_recovery_identity(
    repo: Path,
    *,
    plan: dict[str, Any],
    epoch: _ExecutionWriterEpoch,
    receipt: dict[str, Any],
) -> None:
    """Recheck immutable production identity while allowing expected goal terminalization."""

    epoch.recheck()
    startup = plan.get("startup")
    if not isinstance(startup, dict):
        raise WorkflowRuntimeError("WORKFLOW_EXECUTION_SNAPSHOT_INVALID")
    if _git(repo, "rev-parse", "HEAD") != startup.get("git_head"):
        raise WorkflowRuntimeError("WORKFLOW_CLOSE_EPOCH_HEAD_DRIFT")
    current_tree = _git(repo, "rev-parse", "HEAD^{tree}")
    if current_tree != startup.get("git_tree"):
        raise WorkflowRuntimeError("WORKFLOW_CLOSE_EPOCH_TREE_DRIFT")
    if _sha256(repo / "docs/CODEX_CONTROL.md") != startup.get("control_sha256"):
        raise WorkflowRuntimeError("WORKFLOW_CLOSE_EPOCH_CONTROL_DRIFT")
    if receipt.get("control_sha256") != startup.get("control_sha256"):
        raise WorkflowRuntimeError("WORKFLOW_CLOSE_RECEIPT_CONTROL_DRIFT")
    current_head = str(startup["git_head"])
    base_head = receipt.get("base_head")
    if current_head == base_head:
        if receipt.get("git_tree") != current_tree:
            raise WorkflowRuntimeError("WORKFLOW_CLOSE_RECEIPT_TREE_DRIFT")
        return
    goal_rel = str(receipt.get("goal_path"))
    allowed = {
        goal_rel,
        goal_close_receipt_path(repo / goal_rel).relative_to(repo).as_posix(),
        phase_close_receipt_path(repo / goal_rel).relative_to(repo).as_posix(),
    }
    changed = set(
        _git(repo, "diff", "--name-only", str(base_head), current_head, "--").splitlines()
    )
    if not changed or not changed.issubset(allowed):
        raise WorkflowRuntimeError("WORKFLOW_CLOSE_PARTIAL_DELIVERY_SCOPE_DRIFT")
    for relative in changed:
        path = repo / relative
        if not path.is_file() or _git(repo, "hash-object", "--", relative) != _git(
            repo, "rev-parse", f"HEAD:{relative}"
        ):
            raise WorkflowRuntimeError("WORKFLOW_CLOSE_PARTIAL_DELIVERY_BLOB_DRIFT")


def _verify_close_consumption_identity(
    repo: Path,
    *,
    plan: dict[str, Any],
    startup: dict[str, Any],
    owned_paths: Sequence[str],
) -> None:
    try:
        consumption = node_registry_v10.verify_consumption(
            repo,
            selected_goal_path=plan.get("selected_goal"),
            owned_paths=owned_paths,
            exact_node_pin=startup.get("exact_node_pin"),
            exact_source_pin=startup.get("exact_source_pin"),
            exact_theorem_pin=startup.get("exact_theorem_pin"),
            exact_consumer_pin=startup.get("exact_consumer_pin"),
            writer_lock_held=True,
        )
    except (
        node_registry_v10.NodeRegistryError,
        OSError,
        subprocess.SubprocessError,
    ) as exc:
        raise WorkflowRuntimeError(
            f"GOAL_CLOSE_RECOVERY_CONSUMPTION_IDENTITY_DRIFT:{exc}"
        ) from exc
    if consumption.get("status") != "PASS":
        raise WorkflowRuntimeError(
            "GOAL_CLOSE_RECOVERY_CONSUMPTION_IDENTITY_DRIFT:"
            + str(consumption.get("code", consumption.get("status")))
        )


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True, text=True
    ).stdout.strip()


def _recheck_production_identity(
    repo: Path,
    *,
    plan: dict[str, Any],
    epoch: _ExecutionWriterEpoch,
) -> str | None:
    """Revalidate the startup identity while the exclusive writer epoch is held."""

    try:
        epoch.recheck()
        startup = plan.get("startup")
        if not isinstance(startup, dict):
            return "WORKFLOW_EXECUTION_SNAPSHOT_INVALID"
        if _git(repo, "rev-parse", "HEAD") != startup.get("git_head"):
            return "WORKFLOW_EXECUTION_EPOCH_HEAD_DRIFT"
        if _git(repo, "rev-parse", "HEAD^{tree}") != startup.get("git_tree"):
            return "WORKFLOW_EXECUTION_EPOCH_TREE_DRIFT"
        control = repo / "docs/CODEX_CONTROL.md"
        if _sha256(control) != startup.get("control_sha256"):
            return "WORKFLOW_EXECUTION_EPOCH_CONTROL_DRIFT"
        selected_goal = startup.get("selected_goal")
        if selected_goal != plan.get("selected_goal") or not isinstance(
            selected_goal, str
        ):
            return "WORKFLOW_EXECUTION_EPOCH_SELECTED_GOAL_DRIFT"
        selected = Path(selected_goal)
        if selected.is_absolute() or ".." in selected.parts or "\\" in selected_goal:
            return "WORKFLOW_EXECUTION_EPOCH_SELECTED_GOAL_DRIFT"
        head_blob = _git(repo, "rev-parse", f"HEAD:{selected_goal}")
        current_blob = _git(repo, "hash-object", "--", selected_goal)
        if current_blob != head_blob:
            return "WORKFLOW_EXECUTION_EPOCH_SELECTED_GOAL_DRIFT"
    except (OSError, subprocess.SubprocessError, WorkflowRuntimeError):
        return "WORKFLOW_EXECUTION_EPOCH_RECHECK_FAILED"
    return None


def _relative_repo_path(repo: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repo.resolve()).as_posix()
    except ValueError as exc:
        raise WorkflowRuntimeError(f"REVIEW_ATTACHMENT_OUTSIDE_REPO:{path}") from exc


def compile_review_dispatch(
    repo: Path,
    *,
    attachment: Path,
    request_commit: str,
    request_id: str,
    boundary_id: str,
    expected_sha256: str,
) -> dict[str, Any]:
    """Validate one byte-locked review attachment without claiming it was sent.

    The returned envelope is consumed by the current Codex body, which performs
    the same-chat browser upload and send autonomously.  UI observation is the
    delivery receipt; this pure compiler deliberately cannot manufacture one.
    """
    holds: list[str] = []
    path = attachment if attachment.is_absolute() else repo / attachment
    relative = _relative_repo_path(repo, path)
    if path.suffix != ".txt":
        holds.append("PROSHKA_ATTACHMENT_NOT_TXT")
    if not path.is_file():
        holds.append(f"PROSHKA_ATTACHMENT_MISSING:{relative}")
        raw = b""
    else:
        raw = path.read_bytes()
    try:
        request_text = raw.decode("utf-8")
    except UnicodeDecodeError:
        request_text = ""
        holds.append("PROSHKA_ATTACHMENT_NOT_UTF8")
    if not raw.endswith(b"\n"):
        holds.append("PROSHKA_ATTACHMENT_FINAL_LF_MISSING")
    actual_sha256 = hashlib.sha256(raw).hexdigest()
    if not re.fullmatch(r"[0-9a-f]{64}", expected_sha256):
        holds.append("PROSHKA_EXPECTED_SHA256_INVALID")
    elif actual_sha256 != expected_sha256:
        holds.append("PROSHKA_ATTACHMENT_SHA256_MISMATCH")
    request_id_match = re.search(r"(?m)^REQUEST_ID:\s*(\S+)\s*$", request_text)
    boundary_match = re.search(r"(?m)^BOUNDARY_ID:\s*(\S+)\s*$", request_text)
    if request_id_match is None or request_id_match.group(1) != request_id:
        holds.append("PROSHKA_REQUEST_ID_MISMATCH")
    if boundary_match is None or boundary_match.group(1) != boundary_id:
        holds.append("PROSHKA_BOUNDARY_ID_MISMATCH")

    call_class, call_class_hold = _single_request_header(request_text, "CALL_CLASS")
    packet_subtype, packet_subtype_hold = _single_request_header(
        request_text, "PACKET_SUBTYPE"
    )
    if call_class_hold:
        holds.append(call_class_hold)
    elif call_class not in CANONICAL_CALL_CLASSES:
        holds.append(f"PROSHKA_CALL_CLASS_INVALID:{call_class}")
    if packet_subtype_hold and "PACKET_SUBTYPE:" in request_text:
        holds.append(packet_subtype_hold)
    if packet_subtype == RESEARCH_DEBT_PACKET_SUBTYPE and call_class != "EXPLORATION_REVIEW":
        holds.append("RESEARCH_DEBT_CHALLENGE_CALL_CLASS_MISMATCH")

    queue_path = repo / "docs/routeB_bus/PROSHKA_QUEUE.md"
    try:
        queue_text = queue_path.read_text(encoding="utf-8")
    except OSError:
        queue_text = ""
        holds.append("PROSHKA_QUEUE_MISSING")
    section = re.search(
        rf"(?ms)^##\s+{re.escape(request_id)}\b(.*?)(?=^##\s+|\Z)", queue_text,
    )
    status_match = (
        re.search(r"(?m)^-?\s*`?STATUS:\s*(OPEN|IN_REVIEW|ANSWERED|DROPPED)\b", section.group(1))
        if section else None
    )
    queue_status = status_match.group(1) if status_match else None
    if queue_status != "OPEN":
        holds.append(f"PROSHKA_REQUEST_NOT_OPEN:{request_id}:{queue_status or 'MISSING'}")

    try:
        _git(repo, "cat-file", "-e", f"{request_commit}^{{commit}}")
        commit_blob = _git(repo, "rev-parse", f"{request_commit}:{relative}")
        worktree_blob = _git(repo, "hash-object", relative)
        if commit_blob != worktree_blob:
            holds.append("PROSHKA_ATTACHMENT_COMMIT_BLOB_MISMATCH")
    except subprocess.CalledProcessError:
        commit_blob = "UNRESOLVED"
        worktree_blob = "UNRESOLVED"
        holds.append("PROSHKA_REQUEST_COMMIT_OR_PATH_INVALID")

    runtime_path = repo / "orchestrator/state/CHANNEL_RUNTIME.json"
    eligibility_receipt = None
    try:
        runtime = json.loads(runtime_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        runtime = {}
        holds.append("PROSHKA_CHAT_HANDLE_LOST")
    phase = runtime.get("active_proshka_phase") if isinstance(runtime, dict) else None
    if not isinstance(phase, dict) or phase.get("status") != "ACTIVE":
        conversation_id = None
        holds.append("PROSHKA_ACTIVE_PHASE_MISSING")
    else:
        conversation_id = phase.get("conversation_id")
        if not isinstance(conversation_id, str) or not conversation_id.strip():
            holds.append("PROSHKA_CHAT_HANDLE_LOST")
        if phase.get("last_boundary_id") == boundary_id:
            holds.append(f"PROSHKA_REVIEW_BOUNDARY_ALREADY_RECORDED:{boundary_id}")
        from orchestrator import spine

        phase_key = phase.get("phase_key")
        try:
            phase_key = spine.validate_phase_key(phase_key)
        except spine.ControlViolation:
            phase_key = {}
            holds.append("PROSHKA_ACTIVE_PHASE_KEY_INVALID")
        for field in (*spine.PHASE_KEY_FIELDS, "phase_id"):
            value, error = _single_request_header(request_text, field.upper())
            expected = phase.get("phase_id") if field == "phase_id" else phase_key.get(field)
            if error:
                holds.append(error)
            elif value != expected:
                holds.append(f"PROSHKA_{field.upper()}_MISMATCH")
    if call_class == "EXPLORATION_REVIEW":
        try:
            eligibility_receipt = _exploration_review_receipt(runtime)
        except WorkflowRuntimeError as exc:
            holds.append(str(exc))

    manifest = {
        "path": relative,
        "bytes": len(raw),
        "lines": raw.count(b"\n"),
        "final_newline": "LF" if raw.endswith(b"\n") else "MISSING",
        "sha256": actual_sha256,
        "git_blob": worktree_blob,
        "request_commit": request_commit,
        "commit_blob": commit_blob,
    }
    return {
        "schema": "q3_review_dispatch_plan.v1",
        "status": "HOLD" if holds else "REVIEW_DISPATCH_READY",
        "holds": sorted(set(holds)),
        "boundary_id": boundary_id,
        "request_id": request_id,
        "call_class": call_class,
        "packet_subtype": packet_subtype,
        "queue_status": queue_status,
        "conversation_id": conversation_id,
        "eligibility_receipt": eligibility_receipt,
        "attachment_manifest": manifest,
        "short_instruction": REVIEW_INSTRUCTION,
        "transport": {
            "owner": "CURRENT_CODEX_BODY",
            "same_living_chat_required": True,
            "single_attachment_required": True,
            "repository_owner_confirmation_required": False,
            "host_safety_confirmation": "ENFORCED_BY_ACTIVE_UI_RUNTIME",
            "answer_now_forbidden": True,
            "delivery_receipt_required": True,
            "delivery_performed": False,
        },
        "PX_RH_CLAIM": "NOT_MADE",
    }


def _exists_at_head(repo: Path, relative: str) -> bool:
    return subprocess.run(
        ["git", "cat-file", "-e", f"HEAD:{relative}"],
        cwd=repo,
        capture_output=True,
    ).returncode == 0


def _worktree_fingerprint(repo: Path, owned_paths: list[str]) -> str:
    if not owned_paths:
        return "NO_OWNED_SCOPE"
    payload = subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all", "--", *owned_paths],
        cwd=repo,
        check=True,
        capture_output=True,
    ).stdout
    digest = hashlib.sha256()
    digest.update(payload)
    for relative in sorted(owned_paths):
        path = repo / relative
        if path.is_file():
            digest.update(relative.encode())
            digest.update(path.read_bytes())
    return digest.hexdigest()


def input_fingerprints(
    repo: Path,
    *,
    owned_paths: list[str] | None = None,
    goal_path: str | None = None,
) -> dict[str, str]:
    result: dict[str, str] = {}
    for relative in (*FINGERPRINT_PATHS, *RUNTIME_FINGERPRINT_PATHS):
        path = repo / relative
        result[relative.as_posix()] = _sha256(path) if path.is_file() else "MISSING"
    for path in sorted(repo.glob("docs/routeB_bus/CODEX_REQ_STATE_*.yaml")):
        result[str(path.relative_to(repo))] = _sha256(path)
    if goal_path:
        path = Path(goal_path)
        result["selected_goal"] = _sha256(path) if path.is_file() else "MISSING"
    result["git_head"] = _git(repo, "rev-parse", "HEAD")
    result["worktree_scope"] = _worktree_fingerprint(repo, owned_paths or [])
    return result


def command_receipt(repo: Path, command: list[str], *, label: str,
                    writer_epoch: _ExecutionWriterEpoch | None = None) -> dict[str, Any]:
    started = time.monotonic()
    if writer_epoch is not None:
        writer_epoch.recheck()
    proc = subprocess.run(command, cwd=repo, capture_output=True, text=True,
                          pass_fds=() if writer_epoch is None else (writer_epoch.handle.fileno(),))
    if writer_epoch is not None:
        writer_epoch.recheck()
    output = proc.stdout + proc.stderr
    return {
        "label": label,
        "command": command,
        "exit": proc.returncode,
        "duration_ms": round((time.monotonic() - started) * 1000),
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
        "output_tail": output[-6000:],
    }


def _supplier_preflight_receipt(
    repo: Path,
    *,
    query: str,
    candidate: str | None,
    target: str | None,
    candidate_provenance: str | None,
) -> dict[str, Any]:
    command = [sys.executable, "scripts/supplier_preflight.py", "--query", query]
    if candidate is not None:
        command.extend(("--candidate", candidate))
    if target is not None:
        command.extend(("--target", target))
    if candidate_provenance is not None:
        command.extend(("--candidate-provenance", candidate_provenance))
    started = time.monotonic()
    proc = subprocess.run(command, cwd=repo, capture_output=True, text=True)
    duration_ms = round((time.monotonic() - started) * 1000)
    error: str | None = None
    payload: dict[str, Any] | None = None
    try:
        decoded = json.loads(proc.stdout)
        if not isinstance(decoded, dict):
            raise ValueError("JSON root is not an object")
        payload = decoded
    except (json.JSONDecodeError, ValueError) as exc:
        error = f"SUPPLIER_PREFLIGHT_OUTPUT_INVALID:{exc}"
    if payload is not None:
        status = payload.get("status")
        if set(payload) != SUPPLIER_PAYLOAD_FIELDS:
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:SCHEMA_FIELDS"
        elif payload.get("schema") != SUPPLIER_PREFLIGHT_SCHEMA:
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:SCHEMA"
        elif (
            payload.get("query") != query
            or payload.get("candidate_requested") != candidate
            or payload.get("target_requested") != target
            or payload.get("candidate_provenance") != candidate_provenance
        ):
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:REQUEST_BINDING"
        elif status not in SUPPLIER_STATUS_EXIT:
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:STATUS"
        elif proc.returncode != SUPPLIER_STATUS_EXIT[status]:
            error = "SUPPLIER_PREFLIGHT_EXIT_STATUS_MISMATCH"
        elif not isinstance(payload.get("reason"), str) or not payload["reason"]:
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:REASON"
        elif not isinstance(payload.get("boundary"), str):
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:BOUNDARY"
        elif status == "EXACT_FIT" and (
            not isinstance(payload.get("comparison"), dict)
            or payload["comparison"].get("status") != "EXACT_FIT"
        ):
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:EXACT_FIT_EVIDENCE"
        elif status == "COMPLETE_ABSENCE" and (
            candidate_provenance != "SOURCE_DECLARED"
            or payload.get("source_absence_scope") != "SOURCE_DECLARATION_ABSENCE"
            or "SOURCE_DECLARATION_ABSENCE" not in payload["reason"]
        ):
            error = "SUPPLIER_PREFLIGHT_OUTPUT_INVALID:ABSENCE_SCOPE"
    combined = proc.stdout + proc.stderr
    return {
        "label": "supplier-preflight",
        "command": command,
        "exit": proc.returncode,
        "duration_ms": duration_ms,
        "output_sha256": hashlib.sha256(combined.encode()).hexdigest(),
        "output_tail": combined[-6000:],
        "payload": payload,
        "validation_error": error,
    }


def goal_assembly_chain(goal_path: str | None) -> str | None:
    if not goal_path:
        return None
    path = Path(goal_path)
    if not path.is_file():
        return None
    match = re.search(
        r"^ASSEMBLY_CHAIN:\s*([^\s]+)\s*$",
        path.read_text(encoding="utf-8"),
        re.MULTILINE,
    )
    return match.group(1) if match else None


def load_tool_index(path: Path) -> dict[str, dict[str, Any]]:
    try:
        payload = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (OSError, yaml.YAMLError) as exc:
        raise WorkflowRuntimeError(f"WORKFLOW_TOOL_MANIFEST_INVALID:{exc}") from exc
    families = payload.get("tool_families") if isinstance(payload, dict) else None
    if not isinstance(families, dict):
        raise WorkflowRuntimeError("WORKFLOW_TOOL_MANIFEST_INVALID:tool_families")
    index: dict[str, dict[str, Any]] = {}
    for family in families.values():
        if not isinstance(family, dict):
            continue
        for tool in family.get("tools", []):
            if not isinstance(tool, dict) or not isinstance(tool.get("id"), str):
                continue
            tool_id = tool["id"]
            if tool_id in index:
                raise WorkflowRuntimeError(f"WORKFLOW_TOOL_DUPLICATE:{tool_id}")
            index[tool_id] = tool
    return index


def selector_binding(
    repo: Path,
    *,
    next_goal_spec: Path | None = None,
    current_phase_key: Path | None = None,
) -> tuple[dict[str, Any], str | None]:
    command = [sys.executable, str(repo / "orchestrator/goal_runtime.py"), "--json"]
    if next_goal_spec:
        command.extend(("--next-goal-spec", str(next_goal_spec)))
    if current_phase_key:
        command.extend(("--current-phase-key", str(current_phase_key)))
    proc = subprocess.run(command, cwd=repo, capture_output=True, text=True)
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        detail = proc.stderr.strip() or proc.stdout.strip() or f"exit={proc.returncode}"
        return {"action": "HOLD"}, f"GOAL_SELECTOR_UNREADABLE:{detail}"
    if proc.returncode != 0 or payload.get("ok") is not True:
        code = payload.get("code", "GOAL_SELECTOR_FAILED")
        detail = payload.get("detail")
        return {"action": "HOLD"}, f"{code}:{detail}" if detail else str(code)
    result = payload.get("result")
    if not isinstance(result, dict) or not isinstance(result.get("action"), str):
        return {"action": "HOLD"}, "GOAL_SELECTOR_RESULT_INVALID"
    return result, None


def compile_plan(
    *,
    goal_binding: dict[str, Any],
    selector_hold: str | None,
    tool_index: dict[str, dict[str, Any]],
    derived_status: list[dict[str, Any]],
    assembly_debt: list[str],
    owned_dirty: list[str],
    foreign_dirty: list[str],
    fingerprints: dict[str, str],
    host_executor: str,
    through: str = "plan",
    owned_scope: list[str] | None = None,
    expected_writes: list[str] | None = None,
    startup: dict[str, Any] | None = None,
    assembly_snapshot: dict[str, Any] | None = None,
    roof_ledger_snapshot: dict[str, Any] | None = None,
    route: dict[str, Any] | None = None,
) -> dict[str, Any]:
    from orchestrator import proof_loop

    action = str(goal_binding.get("action", "HOLD"))
    requested = list(dict.fromkeys((*COMMON_TOOLS, *ACTION_TOOLS.get(action, ()))))
    selected: list[dict[str, Any]] = []
    holds = [selector_hold] if selector_hold else []
    if startup is not None and startup.get("exit") != 0:
        holds.append(f"START_GATE_FAILED:{startup.get('exit')}")
    for tool_id in requested:
        tool = tool_index.get(tool_id)
        if tool is None:
            holds.append(f"REQUIRED_TOOL_UNREGISTERED:{tool_id}")
            continue
        if tool.get("status") != "ENABLED":
            holds.append(f"REQUIRED_TOOL_NOT_ENABLED:{tool_id}:{tool.get('status')}")
        selected.append(
            {
                "id": tool_id,
                "mode": tool.get("mode"),
                "writes": tool.get("writes"),
            }
        )
    for item in derived_status:
        if item.get("status") not in {"FRESH", "CURRENT_WORKTREE"}:
            holds.append(f"DERIVED_ARTIFACT_NOT_FRESH:{item.get('artifact_id')}:{item.get('status')}")
    if action == "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM":
        holds.append("OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM")
    if (
        roof_ledger_snapshot is not None
        and roof_ledger_snapshot.get("integrity_status") != "HEAD_LOCKED"
    ):
        holds.append(
            "ROOF_PORT_LEDGER_INVALID:"
            + ",".join(roof_ledger_snapshot.get("integrity_reasons") or ["UNKNOWN"])
        )
    logical_plan = {
        "goal_binding": goal_binding,
        "startup_receipt": startup,
        "through": through,
        "selected_tools": selected,
        "derived_status": derived_status,
        "gates": [
            "codex-session-start",
            "goal-run-selector",
            "lean-validation-for-owned-lean",
            "workflow-session-close",
            "workflow-phase-close-on-transition",
        ],
        "manual_debt": {
            "assembly_review_required": assembly_debt,
            "insight_required": ["INSIGHT_REQUIRED_FOR_CHANGED_SCOPE"] if owned_dirty else [],
            "semantic_debt_auto_resolved": False,
        },
        "expected_writes": sorted(set(expected_writes or [])),
        "owned_scope": sorted(set(owned_scope or [])),
        "owned_dirty": owned_dirty,
        "foreign_dirty_preserved": foreign_dirty,
        "input_fingerprints": fingerprints,
        "proshka": {
            "dispatch_performed": False,
            "eligible_class": (
                "DELEGATED_STRATEGIC_REVIEW"
                if action == "PHASE_TRANSITION_REQUIRED" else None
            ),
            "transport_owner": "CURRENT_CODEX_BODY",
            "same_living_chat_required": True,
            "byte_exact_attachment_required": True,
            "repository_owner_confirmation_required": False,
            "host_safety_confirmation": "ENFORCED_BY_ACTIVE_UI_RUNTIME",
            "delivery_receipt_required": True,
        },
        "scoped_delivery": {
            "performed": False,
            "repository_owner_confirmation_required": False,
            "required_after_green_owned_delta": True,
        },
        "PX_RH_CLAIM": "NOT_MADE",
    }
    unique_holds = sorted(set(item for item in holds if item))
    logical_plan["proof_loop"] = proof_loop.compile_contract(
        goal_binding=goal_binding,
        holds=unique_holds,
        assembly_debt=assembly_debt,
        assembly=assembly_snapshot,
        roof_ledger=roof_ledger_snapshot,
        route=route,
    )
    return {
        "schema": "q3_workflow_plan.v1",
        "status": "HOLD" if unique_holds else "READY",
        "host_executor": host_executor,
        "logical_plan": logical_plan,
        "holds": unique_holds,
    }


def live_plan(
    repo: Path,
    *,
    next_goal_spec: Path | None,
    current_phase_key: Path | None,
    owned_paths: list[str],
    through: str,
) -> dict[str, Any]:
    from orchestrator import (
        dependency_registry,
        proof_loop,
        roof_port_ledger,
        session_briefing,
    )
    from specs_docs import phase_close, session_close

    binding, selector_hold = selector_binding(
        repo,
        next_goal_spec=next_goal_spec,
        current_phase_key=current_phase_key,
    )
    statuses = dependency_registry.statuses(
        repo, repo / REGISTRY, consumer="workflow-plan"
    )
    owned, foreign = session_close.dirty_split(repo, owned_paths)
    host = {"Darwin": "CODEX_MAC", "Linux": "CODEX_LINUX"}.get(
        platform.system(), "UNSUPPORTED_HOST"
    )
    route = session_briefing.snapshot(repo)["route"]
    selected_goal = binding.get("selected_goal_path") or route.get(
        "selected_goal_path"
    )
    selected_goal_path = Path(selected_goal) if isinstance(selected_goal, str) else None
    if selected_goal_path is not None and not selected_goal_path.is_absolute():
        selected_goal_path = repo / selected_goal_path
    chain = proof_loop.goal_assembly_chain(selected_goal_path)
    database = (repo / phase_close.DEFAULT_DB.relative_to(REPO)).resolve()
    assembly = proof_loop.assembly_snapshot(database, chain=chain)
    roof_ledger_snapshot = roof_port_ledger.build(repo, database)
    return compile_plan(
        goal_binding=binding,
        selector_hold=selector_hold,
        tool_index=load_tool_index(repo / TOOLS),
        derived_status=[asdict(item) for item in statuses],
        assembly_debt=phase_close.assembly_debt(
            database,
            chain=goal_assembly_chain(binding.get("selected_goal_path")),
        ),
        owned_dirty=owned,
        foreign_dirty=foreign,
        fingerprints=input_fingerprints(
            repo,
            owned_paths=owned_paths,
            goal_path=binding.get("selected_goal_path"),
        ),
        host_executor=host,
        through=through,
        owned_scope=owned_paths,
        expected_writes=[
            *(str(item) for item in owned_paths),
            *(
                str(output)
                for row in dependency_registry.load_registry(repo / REGISTRY)
                if dependency_registry.applies_to(row, "session-close")
                for output in row["outputs"]
            ),
        ],
        startup=None,
        assembly_snapshot=assembly,
        roof_ledger_snapshot=roof_ledger_snapshot,
        route=route,
    )


def _held_run(
    *,
    plan: dict[str, Any],
    receipts: list[dict[str, Any]],
    holds: list[str],
) -> dict[str, Any]:
    return {
        "schema": "q3_workflow_run.v1",
        "status": "HOLD",
        "holds": sorted(set(holds)),
        "plan": plan,
        "receipts": receipts,
        "commit_push_performed": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }


def _execution_epoch_hold(
    repo: Path,
    *,
    plan: dict[str, Any],
    epoch: _ExecutionWriterEpoch,
    holds: list[str],
) -> bool:
    code = _recheck_production_identity(repo, plan=plan, epoch=epoch)
    if code is None:
        return False
    holds.append(code)
    return True


def _execute_goal_and_phase_close(
    repo: Path,
    *,
    plan: dict[str, Any],
    startup: dict[str, Any],
    epoch: _ExecutionWriterEpoch,
    attempt_payload: Path,
    attempt: dict[str, Any],
    next_goal_spec: Path | None,
    current_phase_key: Path | None,
    receipts: list[dict[str, Any]],
    owned_paths: Sequence[str] = (),
) -> str:
    """Finish a CLOSE_GOAL attempt as a recoverable staged transaction."""

    from orchestrator import goal_runtime, spine

    attempt_payload = (
        attempt_payload if attempt_payload.is_absolute() else repo / attempt_payload
    )
    current_phase_key = (
        current_phase_key
        if current_phase_key is None or current_phase_key.is_absolute()
        else repo / current_phase_key
    )
    if attempt.get("next_action") != "CLOSE_GOAL":
        raise WorkflowRuntimeError("GOAL_CLOSE_ATTEMPT_ACTION_REQUIRED")
    selected = startup.get("selected_goal")
    if not isinstance(selected, str):
        raise WorkflowRuntimeError("GOAL_CLOSE_SELECTED_GOAL_REQUIRED")
    goal_path = repo / selected
    marker = goal_close_receipt_path(goal_path)
    answer_path = goal_path.with_name(
        goal_path.name.removesuffix(".goal.md") + ".answer.md"
    )
    if answer_path.is_symlink() or not answer_path.is_file():
        raise WorkflowRuntimeError("GOAL_CLOSE_MATCHING_ANSWER_REQUIRED")
    _validate_modern_answer(goal_path, _goal_header(goal_path), answer_path)
    existing: dict[str, Any] | None = None
    if marker.is_file():
        # Startup performs the full Git-epoch/ancestry validation.  Inside the
        # held writer epoch we validate structure and bytes here, then bind the
        # receipt to the immutable compiled snapshot below.
        existing = validate_goal_close_receipt(
            goal_path, answer_path, marker, verify_git_epoch=False
        )
        receipt_spec = existing.get("next_goal_spec_path")
        if next_goal_spec is None and isinstance(receipt_spec, str):
            next_goal_spec = repo / receipt_spec
    if next_goal_spec is None:
        raise WorkflowRuntimeError("NEXT_GOAL_SPEC_REQUIRED_FOR_CLOSE_GOAL")
    next_goal_spec = (
        next_goal_spec
        if next_goal_spec is None or next_goal_spec.is_absolute()
        else repo / next_goal_spec
    )
    current_phase_key = (
        current_phase_key
        if current_phase_key is None or current_phase_key.is_absolute()
        else repo / current_phase_key
    )
    channel_path = repo / "orchestrator/state/CHANNEL_RUNTIME.json"
    input_paths = {
        "answer": answer_path,
        "attempt": attempt_payload,
        "channel_runtime": channel_path,
    }
    if next_goal_spec is not None:
        input_paths["next_goal_spec"] = next_goal_spec
    if current_phase_key is not None:
        input_paths["current_phase_key"] = current_phase_key
    input_hashes = _close_input_hashes(
        answer_path=answer_path,
        attempt_path=attempt_payload,
        next_goal_spec=next_goal_spec,
        channel_runtime=channel_path,
        current_phase_key=current_phase_key,
    )
    current: dict[str, str] | None = None
    next_phase: dict[str, str] | None = None
    changed = False
    if next_goal_spec is not None:
        spec_payload = _load_closed_json(next_goal_spec, code="NEXT_GOAL_SPEC_INVALID")
        spec = goal_runtime.validate_next_goal_spec(spec_payload, repo_root=repo)
        runtime = _load_closed_json(channel_path, code="CHANNEL_RUNTIME_INVALID")
        spine.validate_runtime(runtime)
        active = runtime.get("active_proshka_phase")
        if not isinstance(active, dict):
            raise WorkflowRuntimeError("PHASE_TRANSITION_CURRENT_PHASE_MISSING")
        current = spine.validate_phase_key(active.get("phase_key"))
        if current_phase_key is not None:
            supplied = _load_closed_json(
                current_phase_key, code="CURRENT_PHASE_KEY_INVALID"
            )
            if not spine.phase_keys_equal(supplied, current):
                raise WorkflowRuntimeError("CURRENT_PHASE_KEY_DRIFT")
        next_phase = spine.validate_phase_key(spec["phase_key"])
        changed = not spine.phase_keys_equal(current, next_phase)
        if spec["phase_key_change"] != changed:
            raise WorkflowRuntimeError("PHASE_CHANGE_DECLARATION_DRIFT")
    if existing is not None:
        startup_edge = {
            "node": startup.get("exact_node_pin"),
            "source": startup.get("exact_source_pin"),
            "theorem": startup.get("exact_theorem_pin"),
            "consumer": startup.get("exact_consumer_pin"),
        }
        if existing.get("exact_edge") != startup_edge:
            raise WorkflowRuntimeError("GOAL_CLOSE_EXACT_EDGE_DRIFT")
        attempt_rel = _lexical_relative(repo, attempt_payload).as_posix()
        if existing.get("attempt_path") != attempt_rel:
            raise WorkflowRuntimeError("GOAL_CLOSE_ATTEMPT_PATH_DRIFT")
        if existing.get("attempt_sha256") != input_hashes["attempt"]:
            raise WorkflowRuntimeError("GOAL_CLOSE_ATTEMPT_BLOB_DRIFT")
        expected_spec_path = (
            _lexical_relative(repo, next_goal_spec).as_posix()
            if next_goal_spec is not None
            else None
        )
        if (
            existing.get("next_goal_spec_path") != expected_spec_path
            or existing.get("next_goal_spec_sha256")
            != input_hashes.get("next_goal_spec")
            or existing.get("channel_runtime_sha256")
            != input_hashes["channel_runtime"]
            or existing.get("phase_close_required") != changed
            or existing.get("current_phase_key") != current
            or existing.get("next_phase_key") != next_phase
            or existing.get("current_phase_key_path")
            != (
                _lexical_relative(repo, current_phase_key).as_posix()
                if current_phase_key is not None
                else None
            )
            or existing.get("current_phase_key_sha256")
            != input_hashes.get("current_phase_key")
        ):
            raise WorkflowRuntimeError("GOAL_CLOSE_PHASE_BINDING_DRIFT")
        _recheck_close_recovery_identity(
            repo, plan=plan, epoch=epoch, receipt=existing
        )
    else:
        _recheck_close_inputs(repo, input_paths, input_hashes)
        if _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=[]):
            raise WorkflowRuntimeError("WORKFLOW_CLOSE_EPOCH_DRIFT")
    if existing is None:
        open_bytes = goal_path.read_bytes()
        open_goal_sha256 = hashlib.sha256(open_bytes).hexdigest()
        terminal_bytes = _terminal_goal_bytes(goal_path)
        command = [
            sys.executable,
            "orchestrator/spine.py",
            "--refresh",
            "--reason",
            "goal-close",
        ]
        goal_stage = command_receipt(repo, command, label="goal-close", writer_epoch=epoch)
        receipts.append(goal_stage)
        if goal_stage.get("exit") != 0:
            raise WorkflowRuntimeError("GOAL_CLOSE_STAGE_FAILED")
        _recheck_close_inputs(repo, input_paths, input_hashes)
        if _sha256(goal_path) != open_goal_sha256:
            raise WorkflowRuntimeError("GOAL_CLOSE_GOAL_BYTES_DRIFT")
        if _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=[]):
            raise WorkflowRuntimeError("WORKFLOW_CLOSE_EPOCH_DRIFT")
        edge = {
            "node": startup.get("exact_node_pin"),
            "source": startup.get("exact_source_pin"),
            "theorem": startup.get("exact_theorem_pin"),
            "consumer": startup.get("exact_consumer_pin"),
        }
        if any(not isinstance(value, str) or not value for value in edge.values()):
            raise WorkflowRuntimeError("GOAL_CLOSE_EXACT_EDGE_REQUIRED")
        marker_payload = {
            "schema": "q3_goal_close_receipt.v1",
            "goal_path": selected,
            "answer_path": answer_path.relative_to(repo).as_posix(),
            "base_head": startup.get("git_head"),
            "git_tree": startup.get("git_tree"),
            "control_sha256": startup.get("control_sha256"),
            "open_goal_sha256": open_goal_sha256,
            "terminal_goal_sha256": hashlib.sha256(terminal_bytes).hexdigest(),
            "answer_sha256": input_hashes["answer"],
            "attempt_path": _lexical_relative(repo, attempt_payload).as_posix(),
            "attempt_sha256": input_hashes["attempt"],
            "exact_edge": edge,
            "stages": [_compact_stage(goal_stage)],
            "next_goal_spec_path": (
                _lexical_relative(repo, next_goal_spec).as_posix()
                if next_goal_spec is not None
                else None
            ),
            "next_goal_spec_sha256": input_hashes.get("next_goal_spec"),
            "channel_runtime_sha256": input_hashes["channel_runtime"],
            "phase_close_required": changed,
            "current_phase_key": current,
            "next_phase_key": next_phase,
            "current_phase_key_path": (
                _lexical_relative(repo, current_phase_key).as_posix()
                if current_phase_key is not None
                else None
            ),
            "current_phase_key_sha256": input_hashes.get("current_phase_key"),
        }
        _atomic_bytes(
            marker,
            (
                json.dumps(
                    marker_payload,
                    ensure_ascii=False,
                    sort_keys=True,
                    indent=2,
                )
                + "\n"
            ).encode(),
        )
        # Receipt first: a crash here is recoverable as GOAL_TERMINALIZE_PENDING.
        _recheck_close_inputs(repo, input_paths, input_hashes)
        validate_goal_close_receipt(
            goal_path, answer_path, marker, verify_git_epoch=False
        )
        if _sha256(goal_path) != open_goal_sha256:
            raise WorkflowRuntimeError("GOAL_CLOSE_GOAL_BYTES_DRIFT")
        if _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=[]):
            raise WorkflowRuntimeError("WORKFLOW_CLOSE_EPOCH_DRIFT")
        _atomic_bytes(goal_path, terminal_bytes)
        existing = marker_payload
    else:
        goal_is_open = _goal_header(goal_path).get("STATUS") == "OPEN"
        terminal_bytes = (
            _terminal_goal_bytes(goal_path)
            if goal_is_open
            else goal_path.read_bytes()
        )
        if hashlib.sha256(terminal_bytes).hexdigest() != existing["terminal_goal_sha256"]:
            raise WorkflowRuntimeError("GOAL_CLOSE_RECEIPT_COLLISION")
        if goal_is_open:
            _verify_close_consumption_identity(
                repo, plan=plan, startup=startup, owned_paths=owned_paths
            )
            validate_goal_close_receipt(
                goal_path, answer_path, marker, verify_git_epoch=False
            )
            _recheck_close_inputs(repo, input_paths, input_hashes)
            _recheck_close_recovery_identity(
                repo, plan=plan, epoch=epoch, receipt=existing
            )
            if _sha256(goal_path) != existing["open_goal_sha256"]:
                raise WorkflowRuntimeError("GOAL_CLOSE_GOAL_BYTES_DRIFT")
            _atomic_bytes(goal_path, terminal_bytes)
        receipts.append({"label": "goal-close", "exit": 0, "status": "ALREADY_CLOSED"})

    if not changed:
        return "CLOSED_GOAL"
    assert next_goal_spec is not None and current is not None and next_phase is not None
    phase_marker = phase_close_receipt_path(goal_path)
    if phase_marker.is_file():
        _verify_close_consumption_identity(
            repo, plan=plan, startup=startup, owned_paths=owned_paths
        )
        _recheck_close_inputs(repo, input_paths, input_hashes)
        _recheck_close_recovery_identity(repo, plan=plan, epoch=epoch, receipt=existing)
        if _sha256(goal_path) != existing["terminal_goal_sha256"]:
            raise WorkflowRuntimeError("GOAL_CLOSE_TERMINAL_BYTES_DRIFT")
        validate_phase_close_receipt(goal_path, marker, phase_marker)
        receipts.append({"label": "phase-close", "exit": 0, "status": "ALREADY_CLOSED"})
        return "CLOSED_GOAL_PHASE"
    _recheck_close_inputs(repo, input_paths, input_hashes)
    _recheck_close_recovery_identity(repo, plan=plan, epoch=epoch, receipt=existing)
    if _sha256(goal_path) != existing["terminal_goal_sha256"]:
        raise WorkflowRuntimeError("GOAL_CLOSE_TERMINAL_BYTES_DRIFT")
    chain = goal_assembly_chain(str(goal_path))
    with tempfile.TemporaryDirectory(prefix="q3-phase-close-") as temp_dir:
        phase_output = Path(temp_dir) / "phase-close.json"
        command = [
            sys.executable,
            "specs_docs/phase_close.py",
            "--repair",
            "--json-out",
            str(phase_output),
        ]
        if chain:
            command.extend(("--assembly-chain", chain))
        phase_stage = command_receipt(repo, command, label="phase-close", writer_epoch=epoch)
        receipts.append(phase_stage)
        if phase_stage.get("exit") != 0:
            raise WorkflowRuntimeError("PHASE_CLOSE_STAGE_FAILED")
        phase_result, phase_output_sha256 = _validate_phase_close_output(phase_output)
        derived_outputs = _phase_output_fingerprints(repo, phase_result)
    _recheck_close_inputs(repo, input_paths, input_hashes)
    _recheck_close_recovery_identity(repo, plan=plan, epoch=epoch, receipt=existing)
    validate_goal_close_receipt(
        goal_path, answer_path, marker, verify_git_epoch=False
    )
    if _sha256(goal_path) != existing["terminal_goal_sha256"]:
        raise WorkflowRuntimeError("GOAL_CLOSE_TERMINAL_BYTES_DRIFT")
    if _phase_output_fingerprints(repo, phase_result) != derived_outputs:
        raise WorkflowRuntimeError("PHASE_CLOSE_DERIVED_OUTPUT_DRIFT")
    _verify_close_consumption_identity(
        repo, plan=plan, startup=startup, owned_paths=owned_paths
    )
    _recheck_close_inputs(repo, input_paths, input_hashes)
    _recheck_close_recovery_identity(repo, plan=plan, epoch=epoch, receipt=existing)
    validate_goal_close_receipt(
        goal_path, answer_path, marker, verify_git_epoch=False
    )
    if _sha256(goal_path) != existing["terminal_goal_sha256"]:
        raise WorkflowRuntimeError("GOAL_CLOSE_TERMINAL_BYTES_DRIFT")
    phase_payload = {
        "schema": "q3_phase_close_receipt.v1",
        "goal_path": selected,
        "goal_close_receipt_sha256": _sha256(marker),
        "next_goal_spec_sha256": input_hashes["next_goal_spec"],
        "channel_runtime_sha256": input_hashes["channel_runtime"],
        "current_phase_key": current,
        "next_phase_key": next_phase,
        "stage": _compact_stage(phase_stage),
        "phase_output_sha256": phase_output_sha256,
        "phase_evidence": phase_result,
        "derived_output_fingerprints": derived_outputs,
    }
    _atomic_bytes(
        phase_marker,
        (json.dumps(phase_payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode(),
    )
    return "CLOSED_GOAL_PHASE"


def _execute_close_node_transaction(
    repo: Path,
    *,
    plan: dict[str, Any],
    production_v10: bool,
    startup: dict[str, Any],
    epoch: _ExecutionWriterEpoch | None,
    owned_paths: list[str],
    query: str | None,
    candidate: str | None,
    target: str | None,
    attempt_payload: Path,
    attempt: dict[str, Any],
    insight_payload: Path | None,
    run_kernel: bool,
    protocol_out: Path | None,
    contract_receipt: dict[str, Any] | None,
    receipts: list[dict[str, Any]],
    holds: list[str],
    next_goal_spec: Path | None = None,
    current_phase_key: Path | None = None,
) -> dict[str, Any]:
    if production_v10:
        assert epoch is not None
        selected = startup.get("selected_goal")
        recovery_marker = (
            goal_close_receipt_path(repo / selected)
            if isinstance(selected, str)
            else None
        )
        recovery_receipt_valid = False
        if recovery_marker is not None and recovery_marker.is_file():
            recovery_goal = repo / selected
            recovery_answer = recovery_goal.with_name(
                recovery_goal.name.removesuffix(".goal.md") + ".answer.md"
            )
            try:
                validate_goal_close_receipt(
                    recovery_goal,
                    recovery_answer,
                    recovery_marker,
                    verify_git_epoch=False,
                )
            except (StartupRuntimeError, OSError) as exc:
                holds.append(str(exc))
                return _held_run(plan=plan, receipts=receipts, holds=holds)
            recovery_receipt_valid = True
        if (
            attempt.get("next_action") == "CLOSE_GOAL"
            and recovery_receipt_valid
        ):
            before = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
            try:
                close_status = _execute_goal_and_phase_close(
                    repo,
                    plan=plan,
                    startup=startup,
                    epoch=epoch,
                    attempt_payload=attempt_payload,
                    attempt=attempt,
                    next_goal_spec=next_goal_spec,
                    current_phase_key=current_phase_key,
                    receipts=receipts,
                    owned_paths=owned_paths,
                )
                recovery_holds: list[str] = []
            except (
                WorkflowRuntimeError,
                StartupRuntimeError,
                OSError,
                subprocess.SubprocessError,
            ) as exc:
                close_status = "CLOSE_RETRY_PENDING"
                recovery_holds = [str(exc)]
            after = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
            return {
                "schema": "q3_workflow_run.v1",
                "status": close_status,
                "holds": recovery_holds,
                "plan": plan,
                "receipts": receipts,
                "changed_paths_before": before.splitlines(),
                "changed_paths_after": after.splitlines(),
                "commit_push_performed": False,
                "PX_RH_CLAIM": "NOT_MADE",
            }
        if _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=holds):
            return _held_run(plan=plan, receipts=receipts, holds=holds)
        if any(not _exists_at_head(repo, path) for path in owned_paths) and not query:
            holds.append("ASK_SHELF_REQUIRED_FOR_NEW_OBJECT")
            return _held_run(plan=plan, receipts=receipts, holds=holds)
        try:
            consumption = node_registry_v10.verify_consumption(
                repo,
                selected_goal_path=plan.get("selected_goal"),
                owned_paths=owned_paths,
                exact_node_pin=startup.get("exact_node_pin"),
                exact_source_pin=startup.get("exact_source_pin"),
                exact_theorem_pin=startup.get("exact_theorem_pin"),
                exact_consumer_pin=startup.get("exact_consumer_pin"),
                writer_lock_held=True,
            )
        except (
            node_registry_v10.NodeRegistryError,
            OSError,
            subprocess.SubprocessError,
        ) as exc:
            holds.append(f"NODE_REGISTRY_V10_CONSUMPTION_FAILED:{exc}")
        else:
            if consumption.get("status") != "PASS":
                holds.append(
                    "NODE_REGISTRY_V10_CONSUMPTION_FAILED:"
                    + str(consumption.get("code", consumption.get("status")))
                )
            receipts.append(
                {
                    "label": "node-registry-v10-consumption",
                    "exit": 0 if consumption.get("status") == "PASS" else 2,
                    "payload": consumption,
                }
            )
        _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=holds)
        if holds:
            return _held_run(plan=plan, receipts=receipts, holds=holds)

    before = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
    if query:
        provenance = (
            contract_receipt.get("candidate_provenance")
            if contract_receipt is not None
            else None
        )
        supplier = _supplier_preflight_receipt(
            repo,
            query=query,
            candidate=candidate,
            target=target,
            candidate_provenance=provenance,
        )
        receipts.append(supplier)
        supplier_payload = supplier.get("payload")
        supplier_status = (
            supplier_payload.get("status")
            if isinstance(supplier_payload, dict)
            else None
        )
        if supplier.get("validation_error"):
            holds.append(str(supplier["validation_error"]))
        elif candidate is not None and target is not None:
            if supplier_status != "EXACT_FIT":
                holds.append(f"SUPPLIER_PREFLIGHT_NOT_EXACT_FIT:{supplier_status}")
        elif supplier_status == "COMPLETE_ABSENCE":
            holds.append(
                "SUPPLIER_SOURCE_DECLARATION_ABSENCE_REQUIRES_LATER_CREATION_DECISION"
            )
        else:
            holds.append(f"SUPPLIER_PREFLIGHT_DISCOVERY_ONLY:{supplier_status}")
        if production_v10:
            assert epoch is not None
            _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=holds)
    if run_kernel and not holds:
        for path in owned_paths:
            if path.endswith(".lean") and path.startswith("q3.lean.aristotle/"):
                receipts.append(
                    command_receipt(
                        repo,
                        ["bash", "scripts/q3_check.sh", path],
                        label=f"kernel:{path}",
                        writer_epoch=epoch,
                    )
                )
                if production_v10:
                    assert epoch is not None
                    if _execution_epoch_hold(
                        repo, plan=plan, epoch=epoch, holds=holds
                    ):
                        break
    elif not holds and any(path.endswith(".lean") for path in owned_paths):
        holds.append("KERNEL_GATE_REQUIRED")
    if any(item.get("exit", 0) != 0 for item in receipts):
        holds.append("PRE_CLOSE_GATE_FAILED")
    if not holds:
        command = [
            sys.executable,
            "orchestrator/spine.py",
            "--refresh",
            "--reason",
            "step-close",
            "--attempt-payload",
            str(attempt_payload),
        ]
        if insight_payload:
            command.extend(("--insight-payload", str(insight_payload)))
        receipts.append(command_receipt(repo, command, label="step-close", writer_epoch=epoch))
        if production_v10:
            assert epoch is not None
            _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=holds)
    if not holds and receipts[-1]["exit"] == 0:
        command = [
            sys.executable,
            "specs_docs/session_close.py",
            "--root",
            str(repo),
            "--repair",
        ]
        for path in owned_paths:
            command.extend(("--owned-path", path))
        if run_kernel:
            command.append("--run-kernel")
        if protocol_out:
            command.extend(("--protocol-out", str(protocol_out)))
        receipts.append(command_receipt(repo, command, label="session-close", writer_epoch=epoch))
        if production_v10:
            assert epoch is not None
            _execution_epoch_hold(repo, plan=plan, epoch=epoch, holds=holds)
    close_status = "CLOSED_NODE"
    if (
        production_v10
        and not holds
        and receipts[-1]["exit"] == 0
        and attempt.get("next_action") == "CLOSE_GOAL"
    ):
        assert epoch is not None
        try:
            close_status = _execute_goal_and_phase_close(
                repo,
                plan=plan,
                startup=startup,
                epoch=epoch,
                attempt_payload=attempt_payload,
                attempt=attempt,
                next_goal_spec=next_goal_spec,
                current_phase_key=current_phase_key,
                receipts=receipts,
                owned_paths=owned_paths,
            )
        except (
            WorkflowRuntimeError,
            StartupRuntimeError,
            OSError,
            subprocess.SubprocessError,
        ) as exc:
            holds.append(str(exc))
            close_status = "CLOSE_RETRY_PENDING"
    failed = [item for item in receipts if item.get("exit", 0) != 0]
    after = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
    return {
        "schema": "q3_workflow_run.v1",
        "status": (
            "CLOSE_RETRY_PENDING"
            if close_status == "CLOSE_RETRY_PENDING"
            else "HOLD" if failed or holds else close_status
        ),
        "holds": sorted(
            set(
                [
                    *holds,
                    *(
                        f"COMMAND_FAILED:{item['label']}:{item['exit']}"
                        for item in failed
                    ),
                ]
            )
        ),
        "plan": plan,
        "receipts": receipts,
        "changed_paths_before": before.splitlines(),
        "changed_paths_after": after.splitlines(),
        "commit_push_performed": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }


def execute_close_node(
    repo: Path,
    *,
    plan: dict[str, Any],
    owned_paths: list[str],
    query: str | None,
    candidate: str | None,
    target: str | None,
    attempt_payload: Path | None,
    insight_payload: Path | None,
    run_kernel: bool,
    protocol_out: Path | None,
    dependency_contract_receipt: Path | None = None,
    next_goal_spec: Path | None = None,
    current_phase_key: Path | None = None,
) -> dict[str, Any]:
    _team_pending_guard(repo)
    from orchestrator import goal_events
    plan_schema = plan.get("schema")
    production_v10 = (
        plan_schema in {SHADOW_PLAN_SCHEMA, TEAM_PLAN_SCHEMA}
        and plan.get("mode") == PRODUCTION_PLAN_MODE
    )
    legacy_v9 = plan_schema == "q3_workflow_plan.v1"
    if not (production_v10 or legacy_v9):
        return {
            "schema": "q3_workflow_run.v1",
            "status": "HOLD",
            "holds": ["WORKFLOW_RUN_PLAN_SCHEMA_UNSUPPORTED"],
            "plan": plan,
            "receipts": [],
            "commit_push_performed": False,
            "PX_RH_CLAIM": "NOT_MADE",
        }
    receipts: list[dict[str, Any]] = []
    holds = list(plan.get("holds", []))
    if production_v10:
        startup = plan.get("startup")
        if not isinstance(startup, dict):
            holds.append("PRODUCTION_V10_STARTUP_SNAPSHOT_INVALID")
        else:
            receipts.append({"label": "production-v10-startup", "payload": startup})
        if plan.get("status") != "READY" or plan.get("run_authorized") is not True:
            holds.append("PRODUCTION_V10_RUN_NOT_AUTHORIZED")
    else:
        startup = plan.get("logical_plan", {}).get("startup_receipt")
        if not isinstance(startup, dict):
            holds.append("LEGACY_V9_STARTUP_RECEIPT_REQUIRED")
        else:
            receipts.append(startup)
            if startup.get("exit") != 0:
                holds.append(f"START_GATE_FAILED:{startup.get('exit')}")
    if not owned_paths:
        holds.append("OWNED_SCOPE_REQUIRED")
    if attempt_payload is None:
        holds.append("GOAL_ATTEMPT_EVENT_REQUIRED")
        attempt: dict[str, Any] = {}
    elif (repo_attempt_payload := (
        attempt_payload if attempt_payload.is_absolute() else repo / attempt_payload
    )).is_file():
        attempt_payload = repo_attempt_payload
        raw_attempt: dict[str, Any] = {}
        try:
            raw_attempt = _load_closed_json(
                attempt_payload, code="GOAL_ATTEMPT_PAYLOAD_INVALID"
            )
            attempt = goal_events.validate_attempt(raw_attempt, repo_root=repo)
        except (goal_events.GoalEventError, WorkflowRuntimeError) as exc:
            selected = startup.get("selected_goal") if isinstance(startup, dict) else None
            recovery_marker = (
                goal_close_receipt_path(repo / selected)
                if production_v10 and isinstance(selected, str)
                else None
            )
            # Once the goal bytes are terminal, the original attempt's OPEN-goal
            # hash intentionally no longer validates. The durable receipt is the
            # recovery authority and rebinds the exact attempt bytes below.
            if (
                raw_attempt.get("next_action") == "CLOSE_GOAL"
                and recovery_marker is not None
                and recovery_marker.is_file()
            ):
                attempt = raw_attempt
            else:
                attempt = {}
                holds.append(str(exc))
    else:
        # The registered step-close writer remains the authority for ordinary
        # node-only calls; goal terminalization requires the decoded payload.
        attempt = {}
    if (
        not holds
        and not production_v10
        and any(not _exists_at_head(repo, path) for path in owned_paths)
        and not query
    ):
        holds.append("ASK_SHELF_REQUIRED_FOR_NEW_OBJECT")
    contract_receipt: dict[str, Any] | None = None
    if candidate or target:
        if not (query and candidate and target):
            holds.append("SUPPLIER_PREFLIGHT_TRIPLE_REQUIRED")
        if dependency_contract_receipt is None:
            holds.append("CONSUMER_FIRST_CONTRACT_RECEIPT_REQUIRED")
        elif candidate and target:
            try:
                contract_receipt = _dependency_contract_receipt(
                    repo,
                    dependency_contract_receipt,
                    candidate=candidate,
                    target=target,
                    exact_theorem_pin=(
                        startup.get("exact_theorem_pin")
                        if production_v10 and isinstance(startup, dict)
                        else None
                    ),
                    exact_consumer_pin=(
                        startup.get("exact_consumer_pin")
                        if production_v10 and isinstance(startup, dict)
                        else None
                    ),
                )
                receipts.append(contract_receipt)
            except WorkflowRuntimeError as exc:
                holds.append(str(exc))
    if holds:
        return _held_run(plan=plan, receipts=receipts, holds=holds)
    assert attempt_payload is not None
    if production_v10:
        try:
            with _execution_writer_epoch(repo) as epoch:
                team_guard(repo, command="workflow-close-node", paths=owned_paths)
                return _execute_close_node_transaction(
                    repo,
                    plan=plan,
                    production_v10=True,
                    startup=startup,
                    epoch=epoch,
                    owned_paths=owned_paths,
                    query=query,
                    candidate=candidate,
                    target=target,
                    attempt_payload=attempt_payload,
                    attempt=attempt,
                    insight_payload=insight_payload,
                    run_kernel=run_kernel,
                    protocol_out=protocol_out,
                    contract_receipt=contract_receipt,
                    receipts=receipts,
                    holds=holds,
                    next_goal_spec=next_goal_spec,
                    current_phase_key=current_phase_key,
                )
        except WorkflowRuntimeError as exc:
            holds.append(str(exc))
            return _held_run(plan=plan, receipts=receipts, holds=holds)
    return _execute_close_node_transaction(
        repo,
        plan=plan,
        production_v10=False,
        startup=startup,
        epoch=None,
        owned_paths=owned_paths,
        query=query,
        candidate=candidate,
        target=target,
        attempt_payload=attempt_payload,
        attempt=attempt,
        insight_payload=insight_payload,
        run_kernel=run_kernel,
        protocol_out=protocol_out,
        contract_receipt=contract_receipt,
        receipts=receipts,
        holds=holds,
        next_goal_spec=next_goal_spec,
        current_phase_key=current_phase_key,
    )


def _add_plan_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--next-goal-spec", type=Path)
    parser.add_argument("--current-phase-key", type=Path)
    parser.add_argument("--owned-path", action="append", default=[])


def _run_close_script(repo: Path, script: str, forwarded: list[str]) -> int:
    if _team_enabled(repo):
        mapping = {"specs_docs/session_close.py": "workflow-session-close", "specs_docs/phase_close.py": "workflow-phase-close"}
        if script not in mapping:
            raise WorkflowRuntimeError("TEAM_UNFENCED_WRITER_FORBIDDEN:" + script)
        with _execution_writer_epoch(repo) as epoch:
            team_guard(repo, command=mapping[script], paths=[])
            return subprocess.run(
                [sys.executable, str(repo / script), "--root", str(repo), *forwarded], cwd=repo,
                pass_fds=(epoch.handle.fileno(),),
            ).returncode
    return subprocess.run(
        [sys.executable, str(repo / script), "--root", str(repo), *forwarded],
        cwd=repo,
    ).returncode


def _supplier_search_dispatch(
    repo: Path,
    *,
    search_intent: Path,
    owned_paths: list[str],
    record_evidence: bool,
    oracle_card: str | None,
) -> int:
    """Run one read-only SearchIntent and optionally persist its exact evidence."""

    if record_evidence:
        _team_pending_guard(repo)
    from scripts import supplier_preflight

    plan = live_plan_v10(repo, owned_paths=owned_paths)
    startup = plan.get("startup")
    holds: list[str] = []
    if plan.get("status") == "FATAL" or not isinstance(startup, dict):
        holds.append("SUPPLIER_SEARCH_STARTUP_FATAL")
    elif startup.get("fatal_errors"):
        holds.append("SUPPLIER_SEARCH_STARTUP_FATAL")
    if holds:
        print(json.dumps({
            "schema": "q3_supplier_search_dispatch.v1",
            "status": "FATAL",
            "holds": sorted(set(holds)),
            "child_started": False,
        }, ensure_ascii=False, sort_keys=True))
        return 2
    try:
        intent_path = (
            search_intent if search_intent.is_absolute() else repo / search_intent
        )
        intent_raw, intent_before = _search_input_snapshot(intent_path)
        decoded_intent = json.loads(intent_raw.decode("utf-8"))
        intent = supplier_preflight.validate_search_intent_runtime(decoded_intent, repo=repo)
    except (OSError, ValueError, WorkflowRuntimeError) as exc:
        intent = None
        holds.append(f"SUPPLIER_SEARCH_INTENT_INVALID:{exc}")
    if isinstance(startup, dict) and isinstance(intent, dict):
        bindings = (
            ("goal_file", plan.get("selected_goal")),
            ("node_id", startup.get("exact_node_pin")),
            ("source_pin", startup.get("exact_source_pin")),
        )
        for field, expected in bindings:
            if intent.get(field) != expected:
                holds.append(f"SUPPLIER_SEARCH_BINDING_MISMATCH:{field}")
        admission = intent.get("admission")
        if isinstance(admission, dict):
            for field, expected in (
                ("theorem", startup.get("exact_theorem_pin")),
                ("consumer", startup.get("exact_consumer_pin")),
            ):
                if admission.get(field) != expected:
                    holds.append(f"SUPPLIER_SEARCH_BINDING_MISMATCH:{field}")
    card_path: Path | None = None
    card_rel: str | None = None
    card_before: tuple[tuple[int, int, int, int, int, int, int], str] | None = None
    if record_evidence:
        if oracle_card is None:
            holds.append("SUPPLIER_SEARCH_ORACLE_CARD_REQUIRED")
        else:
            try:
                card_path, card_rel, card_before = _search_card_state(
                    repo, oracle_card=oracle_card, owned_paths=owned_paths
                )
            except WorkflowRuntimeError as exc:
                holds.append(str(exc))
    if holds:
        print(json.dumps({
            "schema": "q3_supplier_search_dispatch.v1",
            "status": "FATAL",
            "holds": sorted(set(holds)),
            "child_started": False,
        }, ensure_ascii=False, sort_keys=True))
        return 2
    command = [
        sys.executable,
        str(repo / "scripts/supplier_preflight.py"),
        "--search-intent",
        str(intent_path),
    ]
    if not record_evidence:
        return subprocess.run(command, cwd=repo).returncode

    assert intent is not None
    assert card_path is not None and card_rel is not None and card_before is not None
    supplier = subprocess.run(
        command, cwd=repo, capture_output=True, text=True, check=False
    )
    try:
        evidence = _parse_search_evidence(supplier.stdout, supplier.returncode)
        current_plan = live_plan_v10(repo, owned_paths=owned_paths)
        if _supplier_plan_identity(current_plan) != _supplier_plan_identity(plan):
            raise WorkflowRuntimeError("SUPPLIER_SEARCH_PLAN_IDENTITY_DRIFT")
    except WorkflowRuntimeError as exc:
        return _supplier_search_failure(str(exc), supplier_stderr=supplier.stderr)

    try:
        frozen_intent = _canonical_json_bytes(intent)
        frozen_evidence = _canonical_json_bytes(evidence)
        expected_intent_id = hashlib.sha256(frozen_intent[:-1]).hexdigest()
        expected_observation_id = _search_observation_identity(evidence)
        with tempfile.TemporaryDirectory(prefix="q3-search-evidence-") as temporary:
            temporary_path = Path(temporary)
            intent_temp = temporary_path / "intent.json"
            evidence_temp = temporary_path / "evidence.json"
            intent_temp.write_bytes(frozen_intent)
            evidence_temp.write_bytes(frozen_evidence)
            with _execution_writer_epoch(repo) as epoch:
                team_guard(repo, command="workflow-search-evidence", paths=[card_rel])
                identity_error = _recheck_production_identity(
                    repo, plan=current_plan, epoch=epoch
                )
                if identity_error is not None:
                    raise WorkflowRuntimeError(identity_error)
                if _search_input_snapshot(intent_path)[1] != intent_before:
                    raise WorkflowRuntimeError("SUPPLIER_SEARCH_INTENT_DRIFT")
                if _search_card_state(
                    repo, oracle_card=card_rel, owned_paths=owned_paths
                )[2] != card_before:
                    raise WorkflowRuntimeError("SUPPLIER_SEARCH_ORACLE_CARD_DRIFT")
                supplier_preflight.validate_search_intent_runtime(intent, repo=repo)
                epoch.recheck()
                writer_command = [
                    sys.executable,
                    str(repo / "q3.lean.aristotle/scripts/oracle_questions.py"),
                    "record-evidence",
                    "--card",
                    card_rel,
                    "--intent",
                    str(intent_temp),
                    "--evidence",
                    str(evidence_temp),
                    "--inherited-writer-lock-fd",
                    str(epoch.handle.fileno()),
                ]
                writer = subprocess.run(
                    writer_command,
                    cwd=repo,
                    capture_output=True,
                    text=True,
                    check=False,
                    pass_fds=(epoch.handle.fileno(),),
                )
                writer_receipt = _parse_search_writer_receipt(
                    writer.stdout,
                    writer.returncode,
                    expected_observation_id=expected_observation_id,
                )
                epoch.recheck()
                supplier_preflight.validate_search_intent_runtime(intent, repo=repo)
                if _search_input_snapshot(intent_path)[1] != intent_before:
                    raise WorkflowRuntimeError("SUPPLIER_SEARCH_INTENT_DRIFT")
                identity_error = _recheck_production_identity(
                    repo, plan=current_plan, epoch=epoch
                )
                if identity_error is not None:
                    raise WorkflowRuntimeError(identity_error)
                card_after_path, _, card_after = _search_card_state(
                    repo, oracle_card=card_rel, owned_paths=owned_paths
                )
                _validate_search_card_postcondition(
                    card_after_path,
                    before=card_before,
                    after=card_after,
                    writer_receipt=writer_receipt,
                    expected_intent_id=expected_intent_id,
                    expected_observation_id=expected_observation_id,
                    frozen_evidence=frozen_evidence,
                )
    except (OSError, ValueError, WorkflowRuntimeError) as exc:
        writer_stderr = writer.stderr if "writer" in locals() else ""
        return _supplier_search_failure(str(exc), supplier_stderr=writer_stderr)
    if supplier.stderr:
        print(supplier.stderr, file=sys.stderr, end="")
    print(supplier.stdout, end="")
    return supplier.returncode


def _supplier_plan_identity(plan: dict[str, Any]) -> tuple[object, ...]:
    startup = plan.get("startup")
    if not isinstance(startup, dict) or plan.get("status") == "FATAL":
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_STARTUP_FATAL")
    return (
        plan.get("selected_goal"),
        startup.get("selected_goal"),
        startup.get("git_head"),
        startup.get("git_tree"),
        startup.get("control_sha256"),
        startup.get("exact_node_pin"),
        startup.get("exact_source_pin"),
        startup.get("exact_theorem_pin"),
        startup.get("exact_consumer_pin"),
    )


def _canonical_json_bytes(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _search_observation_identity(evidence: dict[str, Any]) -> str:
    """Independently reproduce the oracle's durable observation identity."""

    observed_at = evidence.get("observed_at")
    if not isinstance(observed_at, str) or not observed_at:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_OBSERVATION_TIME_INVALID")
    try:
        observed = datetime.fromisoformat(observed_at)
    except ValueError as exc:
        raise WorkflowRuntimeError(
            "SUPPLIER_SEARCH_OBSERVATION_TIME_INVALID"
        ) from exc
    if observed.tzinfo is None:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_OBSERVATION_TIME_INVALID")

    def strip_runtime(value: object) -> object:
        if isinstance(value, dict):
            return {
                key: strip_runtime(item)
                for key, item in value.items()
                if key
                not in {
                    "metrics",
                    "observation_id",
                    "elapsed_seconds",
                    "duration_ms",
                }
            }
        if isinstance(value, list):
            return [strip_runtime(item) for item in value]
        return value

    identity_payload = {
        "observed_at": observed_at,
        "evidence": strip_runtime(evidence),
    }
    return hashlib.sha256(_canonical_json_bytes(identity_payload)[:-1]).hexdigest()


def _search_input_snapshot(
    path: Path,
) -> tuple[bytes, tuple[tuple[int, int, int, int, int], str]]:
    if path.is_symlink():
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_INTENT_SYMLINK")
    try:
        before = os.lstat(path)
        raw = path.read_bytes()
        after = os.lstat(path)
    except OSError as exc:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_INTENT_UNREADABLE") from exc
    before_identity = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
    )
    after_identity = (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
    )
    if not stat.S_ISREG(before.st_mode) or before_identity != after_identity:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_INTENT_CONCURRENT_MUTATION")
    return raw, (before_identity, hashlib.sha256(raw).hexdigest())


def _parse_search_evidence(stdout: str, returncode: int) -> dict[str, Any]:
    try:
        encoded = stdout.encode("utf-8")
        if len(encoded) > SEARCH_EVIDENCE_STDOUT_MAX_BYTES:
            raise WorkflowRuntimeError("SUPPLIER_SEARCH_EVIDENCE_STDOUT_OVERSIZED")
        evidence = json.loads(stdout)
    except (UnicodeEncodeError, json.JSONDecodeError) as exc:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_EVIDENCE_INVALID") from exc
    if (
        not isinstance(evidence, dict)
        or evidence.get("schema") != SEARCH_EVIDENCE_SCHEMA
        or evidence.get("status") not in {"PASS", "INCOMPLETE"}
    ):
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_EVIDENCE_INVALID")
    expected_exit = 2 if evidence["status"] == "INCOMPLETE" else 0
    if returncode != expected_exit:
        raise WorkflowRuntimeError(
            f"SUPPLIER_SEARCH_CHILD_EXIT_MISMATCH:{returncode}"
        )
    return evidence


def _parse_search_writer_receipt(
    stdout: str, returncode: int, *, expected_observation_id: str
) -> dict[str, str]:
    if returncode != 0:
        raise WorkflowRuntimeError(
            f"SUPPLIER_SEARCH_EVIDENCE_WRITER_FAILED:{returncode}"
        )
    try:
        if len(stdout.encode("utf-8")) > SEARCH_EVIDENCE_STDOUT_MAX_BYTES:
            raise WorkflowRuntimeError(
                "SUPPLIER_SEARCH_EVIDENCE_WRITER_RECEIPT_INVALID"
            )
        receipt = json.loads(stdout)
    except (UnicodeEncodeError, json.JSONDecodeError) as exc:
        raise WorkflowRuntimeError(
            "SUPPLIER_SEARCH_EVIDENCE_WRITER_RECEIPT_INVALID"
        ) from exc
    if (
        not isinstance(receipt, dict)
        or set(receipt) != {"schema", "status", "observation_id"}
        or receipt.get("schema") != "q3_search_evidence_write.v1"
        or receipt.get("status") not in {"RECORDED", "NOOP"}
        or not isinstance(receipt.get("observation_id"), str)
        or re.fullmatch(r"[0-9a-f]{64}", receipt["observation_id"]) is None
        or receipt["observation_id"] != expected_observation_id
    ):
        raise WorkflowRuntimeError(
            "SUPPLIER_SEARCH_EVIDENCE_WRITER_RECEIPT_INVALID"
        )
    return receipt


def _validate_search_card_postcondition(
    card_path: Path,
    *,
    before: tuple[tuple[int, int, int, int, int, int, int], str],
    after: tuple[tuple[int, int, int, int, int, int, int], str],
    writer_receipt: dict[str, str],
    expected_intent_id: str,
    expected_observation_id: str,
    frozen_evidence: bytes,
) -> None:
    observation_id = writer_receipt["observation_id"]
    if observation_id != expected_observation_id:
        raise WorkflowRuntimeError(
            "SUPPLIER_SEARCH_ORACLE_CARD_EVIDENCE_BINDING_FAILED"
        )
    block_pattern = re.compile(
        rb"<!-- Q3_SEARCH_EVIDENCE_V1_BEGIN intent_id="
        + expected_intent_id.encode("ascii")
        + rb" observation_id="
        + observation_id.encode("ascii")
        + rb" -->\n```json\n(.*?)\n```\n<!-- Q3_SEARCH_EVIDENCE_V1_END -->",
        re.DOTALL,
    )
    try:
        card_bytes = card_path.read_bytes()
        bytes_stable = hashlib.sha256(card_bytes).hexdigest() == after[1]
        matches = block_pattern.findall(card_bytes)
        if len(matches) != 1:
            raise WorkflowRuntimeError(
                "SUPPLIER_SEARCH_ORACLE_CARD_EVIDENCE_BINDING_FAILED"
            )
        stored = json.loads(matches[0].decode("utf-8"))
        if not isinstance(stored, dict):
            raise WorkflowRuntimeError(
                "SUPPLIER_SEARCH_ORACLE_CARD_EVIDENCE_BINDING_FAILED"
            )
        stored_observation_id = stored.pop("observation_id", None)
        exact_evidence = _canonical_json_bytes(stored) == frozen_evidence
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise WorkflowRuntimeError(
            "SUPPLIER_SEARCH_ORACLE_CARD_POSTCONDITION_FAILED"
        ) from exc
    if stored_observation_id != observation_id or not exact_evidence:
        raise WorkflowRuntimeError(
            "SUPPLIER_SEARCH_ORACLE_CARD_EVIDENCE_BINDING_FAILED"
        )
    status = writer_receipt["status"]
    if (
        not bytes_stable
        or stat.S_IMODE(after[0][2]) != stat.S_IMODE(before[0][2])
        or after[0][5:] != before[0][5:]
        or (status == "RECORDED" and after[1] == before[1])
        or (status == "NOOP" and after != before)
    ):
        raise WorkflowRuntimeError(
            "SUPPLIER_SEARCH_ORACLE_CARD_POSTCONDITION_FAILED"
        )


def _search_card_state(
    repo: Path, *, oracle_card: str, owned_paths: list[str]
) -> tuple[Path, str, tuple[tuple[int, int, int, int, int, int, int], str]]:
    lexical = Path(oracle_card)
    if "\\" in oracle_card or ".." in lexical.parts:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_ORACLE_CARD_PATH_INVALID")
    if lexical.is_absolute():
        try:
            relative = lexical.relative_to(repo)
        except ValueError as exc:
            raise WorkflowRuntimeError(
                "SUPPLIER_SEARCH_ORACLE_CARD_OUTSIDE_REPO"
            ) from exc
    else:
        relative = lexical
    card_rel = relative.as_posix()
    normalized_owned: list[str] = []
    for value in owned_paths:
        candidate = Path(value)
        if "\\" in value or ".." in candidate.parts:
            raise WorkflowRuntimeError("SUPPLIER_SEARCH_OWNED_PATH_INVALID")
        if candidate.is_absolute():
            try:
                candidate = candidate.relative_to(repo)
            except ValueError as exc:
                raise WorkflowRuntimeError(
                    "SUPPLIER_SEARCH_OWNED_PATH_OUTSIDE_REPO"
                ) from exc
        normalized_owned.append(candidate.as_posix())
    if normalized_owned != [card_rel]:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_ORACLE_CARD_NOT_EXACTLY_OWNED")
    card_path = repo / relative
    if _has_symlink_component(repo, relative):
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_ORACLE_CARD_SYMLINK")
    try:
        before = os.lstat(card_path)
        raw = card_path.read_bytes()
        after = os.lstat(card_path)
    except OSError as exc:
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_ORACLE_CARD_INVALID") from exc
    before_identity = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_uid,
        before.st_gid,
    )
    after_identity = (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
        after.st_uid,
        after.st_gid,
    )
    if (
        not stat.S_ISREG(before.st_mode)
        or before_identity != after_identity
    ):
        raise WorkflowRuntimeError("SUPPLIER_SEARCH_ORACLE_CARD_INVALID")
    return card_path, card_rel, (before_identity, hashlib.sha256(raw).hexdigest())


def _supplier_search_failure(
    code: str, *, supplier_stderr: str = "", child_started: bool = True
) -> int:
    if supplier_stderr:
        print(supplier_stderr, file=sys.stderr, end="")
    print(json.dumps({
        "schema": "q3_supplier_search_dispatch.v1",
        "status": "FATAL",
        "holds": [code],
        "child_started": child_started,
    }, ensure_ascii=False, sort_keys=True))
    return 2


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=REPO)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("team-local-init")
    bootstrap = subparsers.add_parser("team-bootstrap-publish")
    bootstrap.add_argument("--operation-id", required=True)
    bootstrap.add_argument("--expected-head")
    bootstrap.add_argument("--expected-remote-commit")
    bootstrap.add_argument("--expected-remote-resume-sha256")
    bootstrap.add_argument("--reconcile-only", action="store_true")
    team_integration = subparsers.add_parser("team-integrate-candidate")
    team_integration_mode = team_integration.add_mutually_exclusive_group(required=True)
    team_integration_mode.add_argument("--candidate", type=Path)
    team_integration_mode.add_argument("--recover-operation")
    team_watch = subparsers.add_parser("team-watch-intent")
    team_watch.add_argument("--action", choices=["CREATE", "UPDATE", "PAUSE"], required=True)
    team_watch.add_argument("--transfer-id", required=True)
    team_watch.add_argument("--target-thread", required=True)
    team_record_parser = subparsers.add_parser("team-record")
    team_record_parser.add_argument("--kind", choices=["report", "issue-event", "assignment", "archive"], required=True)
    team_record_parser.add_argument("--candidate", type=Path, required=True)
    team_record_parser.add_argument("--expected-sha256", required=True)
    for name in ("team-observe-remote", "team-reserve-effect"):
        team_parser = subparsers.add_parser(name)
        team_parser.add_argument("--operation-id", required=True)
    team_native = subparsers.add_parser("team-observe-native")
    team_native.add_argument("--candidate", type=Path, required=True)
    team_native.add_argument("--expected-sha256", required=True)
    team_confirm = subparsers.add_parser("team-confirm-effect")
    team_confirm.add_argument("--operation-id", required=True)
    team_confirm.add_argument("--candidate", type=Path, required=True)
    team_confirm.add_argument("--expected-sha256", required=True)
    plan_parser = subparsers.add_parser("plan")
    _add_plan_options(plan_parser)
    plan_parser.add_argument("--shadow-v10", action="store_true")
    plan_parser.add_argument(
        "--benchmark-startup-timing",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    run_parser = subparsers.add_parser("run")
    run_parser.add_argument(
        "--through", choices=["close-node", "supplier-preflight"], required=True
    )
    _add_plan_options(run_parser)
    run_parser.add_argument("--query")
    run_parser.add_argument("--candidate")
    run_parser.add_argument("--target")
    run_parser.add_argument("--attempt-payload", type=Path)
    run_parser.add_argument("--insight-payload", type=Path)
    run_parser.add_argument("--run-kernel", action="store_true")
    run_parser.add_argument("--protocol-out", type=Path)
    run_parser.add_argument("--dependency-contract-receipt", type=Path)
    run_parser.add_argument("--search-intent", type=Path)
    run_parser.add_argument("--record-evidence", action="store_true")
    run_parser.add_argument("--oracle-card")
    subparsers.add_parser("close-session")
    subparsers.add_parser("close-phase")
    resume_parser = subparsers.add_parser("resume-checkpoint")
    resume_parser.add_argument("--candidate", type=Path, required=True)
    resume_parser.add_argument("--expected-sha256", required=True)
    resume_mode = resume_parser.add_mutually_exclusive_group()
    resume_mode.add_argument("--dry-run", action="store_true")
    resume_mode.add_argument("--recover-from")
    review_parser = subparsers.add_parser("review-plan")
    review_parser.add_argument("--attachment", type=Path, required=True)
    review_parser.add_argument("--request-commit", required=True)
    review_parser.add_argument("--request-id", required=True)
    review_parser.add_argument("--boundary-id", required=True)
    review_parser.add_argument("--expected-sha256", required=True)
    args, forwarded = parser.parse_known_args()
    repo = args.root.resolve()
    if args.command.startswith("team-"):
        if forwarded:
            parser.error("unrecognized arguments: " + " ".join(forwarded))
        try:
            if args.command == "team-local-init":
                result = team_local_init(repo)
            elif args.command == "team-bootstrap-publish":
                result = team_bootstrap_publish(repo, operation_id=args.operation_id, expected_head=args.expected_head,
                    expected_remote_commit=args.expected_remote_commit,
                    expected_remote_resume_sha256=args.expected_remote_resume_sha256, reconcile_only=args.reconcile_only)
            elif args.command == "team-integrate-candidate":
                result = team_integrate_candidate(repo, candidate=args.candidate, recover_operation=args.recover_operation)
            elif args.command == "team-watch-intent":
                result = team_watch_intent(repo, action=args.action, transfer_id=args.transfer_id, target_thread=args.target_thread)
            elif args.command == "team-record":
                result = team_record(repo, kind=args.kind, candidate=args.candidate, expected_sha256=args.expected_sha256)
            elif args.command == "team-observe-remote":
                result = team_observe_remote(repo, operation_id=args.operation_id)
            elif args.command == "team-reserve-effect":
                result = team_reserve_effect(repo, operation_id=args.operation_id)
            elif args.command == "team-observe-native":
                result = team_observe_native(repo, candidate=args.candidate, expected_sha256=args.expected_sha256)
            else:
                result = team_confirm_effect(repo, operation_id=args.operation_id, candidate=args.candidate, expected_sha256=args.expected_sha256)
        except (WorkflowRuntimeError, StartupRuntimeError, OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
            result = {"status": "HOLD", "reason": str(exc), "receipt_confirmed": False}
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
        return 2 if result["status"] in {"HOLD", "RECONCILE_ORIGINAL", "UNKNOWN"} else 0
    if args.command == "resume-checkpoint":
        if forwarded:
            parser.error("unrecognized arguments: " + " ".join(forwarded))
        try:
            result = resume_checkpoint(
                repo, candidate=args.candidate, expected_sha256=args.expected_sha256,
                dry_run=args.dry_run, recover_from=args.recover_from,
            )
        except (WorkflowRuntimeError, StartupRuntimeError, OSError, subprocess.SubprocessError) as exc:
            result = {"status": "HOLD", "reason": str(exc),
                      "receipt_confirmed": False, "reconciliation_required": True}
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
        return 0 if result["status"] in {"SAVED", "NOOP", "DRY_RUN"} else 2
    if args.command == "close-session":
        return _run_close_script(repo, "specs_docs/session_close.py", forwarded)
    if args.command == "close-phase":
        return _run_close_script(repo, "specs_docs/phase_close.py", forwarded)
    if args.command == "review-plan":
        if forwarded:
            parser.error("unrecognized arguments: " + " ".join(forwarded))
        try:
            result = compile_review_dispatch(
                repo,
                attachment=args.attachment,
                request_commit=args.request_commit,
                request_id=args.request_id,
                boundary_id=args.boundary_id,
                expected_sha256=args.expected_sha256,
            )
        except (WorkflowRuntimeError, subprocess.CalledProcessError) as exc:
            result = {
                "schema": "q3_review_dispatch_plan.v1",
                "status": "HOLD",
                "holds": [str(exc)],
            }
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
        return 0 if result.get("status") == "REVIEW_DISPATCH_READY" else 2
    if forwarded:
        parser.error("unrecognized arguments: " + " ".join(forwarded))
    if args.command == "run" and args.through == "supplier-preflight":
        if args.search_intent is None:
            parser.error("--through supplier-preflight requires --search-intent")
        if args.record_evidence and not args.oracle_card:
            parser.error("--record-evidence requires --oracle-card")
        if args.oracle_card and not args.record_evidence:
            parser.error("--oracle-card requires --record-evidence")
        return _supplier_search_dispatch(
            repo,
            search_intent=args.search_intent,
            owned_paths=args.owned_path,
            record_evidence=args.record_evidence,
            oracle_card=args.oracle_card,
        )
    if args.command == "plan" and args.shadow_v10:
        benchmark_timing: dict[str, Any] | None = (
            {} if args.benchmark_startup_timing else None
        )
        try:
            result = live_shadow_plan_v10(
                repo,
                owned_paths=args.owned_path,
                _benchmark_timing_sink=benchmark_timing,
            )
        except (
            WorkflowRuntimeError,
            StartupRuntimeError,
            node_registry_v10.NodeRegistryError,
            KeyError,
            OSError,
            subprocess.CalledProcessError,
            TypeError,
        ) as exc:
            result = {
                "schema": SHADOW_PLAN_SCHEMA,
                "status": "FATAL",
                "mode": "SHADOW_V10_READ_ONLY",
                "holds": [f"SHADOW_V10_UNAVAILABLE:{type(exc).__name__}:{exc}"],
                "run_authorized": False,
                "writes_performed": False,
                "legacy_v9_authority_unchanged": True,
                "PX_RH_CLAIM": "NOT_MADE",
            }
        print(render_shadow_plan_v10(result))
        if benchmark_timing:
            print(
                _BENCHMARK_TIMING_PREFIX
                + json.dumps(
                    benchmark_timing,
                    ensure_ascii=True,
                    separators=(",", ":"),
                    sort_keys=True,
                ),
                file=sys.stderr,
            )
        return 0 if result.get("status") == "READY" else 2
    try:
        benchmark_timing = (
            {}
            if args.command == "plan" and args.benchmark_startup_timing
            else None
        )
        if benchmark_timing is None:
            plan = live_plan_v10(repo, owned_paths=args.owned_path)
        else:
            plan = live_plan_v10(
                repo,
                owned_paths=args.owned_path,
                _benchmark_timing_sink=benchmark_timing,
            )
        result = (
            execute_close_node(
                repo,
                plan=plan,
                owned_paths=args.owned_path,
                query=args.query,
                candidate=args.candidate,
                target=args.target,
                attempt_payload=args.attempt_payload,
                insight_payload=args.insight_payload,
                run_kernel=args.run_kernel,
                protocol_out=args.protocol_out,
                dependency_contract_receipt=args.dependency_contract_receipt,
                next_goal_spec=args.next_goal_spec,
                current_phase_key=args.current_phase_key,
            )
            if args.command == "run" else plan
        )
    except (
        WorkflowRuntimeError,
        StartupRuntimeError,
        node_registry_v10.NodeRegistryError,
        RuntimeError,
        subprocess.CalledProcessError,
        KeyError,
        OSError,
        TypeError,
    ) as exc:
        result = {
            "schema": SHADOW_PLAN_SCHEMA,
            "status": "FATAL",
            "mode": PRODUCTION_PLAN_MODE,
            "holds": [str(exc)],
            "run_authorized": False,
            "writes_performed": False,
            "PX_RH_CLAIM": "NOT_MADE",
        }
    if args.command == "plan":
        print(render_plan_v10(result))
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    if benchmark_timing:
        print(
            _BENCHMARK_TIMING_PREFIX
            + json.dumps(
                benchmark_timing,
                ensure_ascii=True,
                separators=(",", ":"),
                sort_keys=True,
            ),
            file=sys.stderr,
        )
    return 0 if result.get("status") in {
        "READY", "CLOSED_NODE", "CLOSED_GOAL", "CLOSED_GOAL_PHASE",
    } else 2


if __name__ == "__main__":
    raise SystemExit(main())
