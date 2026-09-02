#!/usr/bin/env python3
"""Stateless front door for the existing Q3 goal lifecycle.

This module compiles the authoritative selector, tool manifest, derived-artifact
registry, review transport contract, and close helpers into one deterministic
plan.  Its run command then executes the registered, explicitly scoped
transition and emits receipts.  It owns no durable runtime state and never
commits, pushes, publishes externally, promotes, or makes an RH claim.  Browser
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
import stat
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager
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
def _execution_writer_epoch(repo: Path) -> Iterator[_ExecutionWriterEpoch]:
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
) -> dict[str, Any]:
    """Build exactly one authoritative v10 snapshot and reuse its exact pins."""

    owned_scope = tuple(owned_paths)
    startup_started = (
        time.perf_counter() if _benchmark_timing_sink is not None else None
    )
    with _startup_read_epoch(repo) as (epoch_guard, lock_error):
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
    host = {"Darwin": "CODEX_MAC", "Linux": "CODEX_LINUX"}.get(
        platform.system(), "UNSUPPORTED_HOST"
    )
    return compile_plan_v10(
        startup_snapshot=snapshot,
        node_registry_summary=registry_summary,
        host_executor=host,
        logical_plan=logical_plan,
    )


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
    if len(rendered.encode("utf-8")) > SHADOW_PLAN_MAX_BYTES or len(
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


def _atomic_bytes(path: Path, payload: bytes) -> None:
    """Durably replace one close marker/state file."""

    import tempfile

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
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


def command_receipt(repo: Path, command: list[str], *, label: str) -> dict[str, Any]:
    started = time.monotonic()
    proc = subprocess.run(command, cwd=repo, capture_output=True, text=True)
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
        goal_stage = command_receipt(repo, command, label="goal-close")
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
        phase_stage = command_receipt(repo, command, label="phase-close")
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
        receipts.append(command_receipt(repo, command, label="step-close"))
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
        receipts.append(command_receipt(repo, command, label="session-close"))
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
    from orchestrator import goal_events
    plan_schema = plan.get("schema")
    production_v10 = (
        plan_schema == SHADOW_PLAN_SCHEMA
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
    review_parser = subparsers.add_parser("review-plan")
    review_parser.add_argument("--attachment", type=Path, required=True)
    review_parser.add_argument("--request-commit", required=True)
    review_parser.add_argument("--request-id", required=True)
    review_parser.add_argument("--boundary-id", required=True)
    review_parser.add_argument("--expected-sha256", required=True)
    args, forwarded = parser.parse_known_args()
    repo = args.root.resolve()
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
