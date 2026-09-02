#!/usr/bin/env python3
"""Read-only warm/cold benchmark for the v10 shadow workflow plan."""

from __future__ import annotations

import argparse
import builtins
import hashlib
import io
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from collections import Counter
from contextlib import ExitStack
from pathlib import Path, PurePosixPath
from typing import Any, Callable, TypeVar
from unittest import mock

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import startup_runtime, workflow_runtime  # noqa: E402

DEFAULT_WARM_RUNS = 20
DEFAULT_COLD_RUNS = 3
WARM_STARTUP_P95_MS = 1000
WARM_FULL_P95_MS = 1500
COLD_STARTUP_MAX_MS = 2500
COLD_FULL_MAX_MS = 3000
SUBPROCESS_MAX_PER_RUN = 10
GIT_MAX_PER_RUN = 5
OPENED_REPO_PATHS_MAX_PER_RUN = 500
T = TypeVar("T")
EXPECTED_GOAL = "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"
EXPECTED_NODE = "REALZERO_GROUND_DIAGONAL_TO_XI"
EXPECTED_SOURCE_PIN = "f82b09f8c24f0b74a62c5c48e5e4e9a3b2b36cc7"
EXPECTED_LIVE_FATALS: frozenset[str] = frozenset()
REQUIRED_BLOCKED_FEATURES = frozenset(
    {
        "BLOCKED_FEATURE:EXACT_THEOREM_EDGE_UNSELECTED",
        "BLOCKED_FEATURE:EXACT_CONSUMER_EDGE_UNSELECTED",
        "RUN",
        "DISPATCH",
        "MINT",
        "STATE_WRITE",
        "RUN_CLOSE_NODE",
    }
)
FORBIDDEN_RUNTIME_COMMANDS = frozenset(
    {"lake", "lean", "session_start.sh", "spine.py", "three_body_loop.py"}
)
PROOF_BODY_PLANT_MARKER = b"-- CONTROL_V10_PROOF_BODY_VALIDATION_PLANT"
TRACE_SENTINEL_PATHS = (
    "orchestrator/workflow_runtime.py",
    "orchestrator/state/NODE_REGISTRY_V10.json",
    "docs/CODEX_CONTROL.md",
)
OPAQUE_BUS_SENTINEL_PATH = "docs/routeB_bus/.benchmark-opaque/deep/999_fake.goal.md"
PHASE_A_CANDIDATE_PATHS = (
    EXPECTED_GOAL,
    "orchestrator/workflow_runtime.py",
    "orchestrator/benchmarks/control_v10_benchmark.py",
    "orchestrator/startup_runtime.py",
    "orchestrator/goal_runtime.py",
    "orchestrator/node_registry_v10.py",
    "orchestrator/lean_dependency_runtime.py",
    "orchestrator/state/NODE_REGISTRY_V10.json",
    "orchestrator/tests/test_workflow_runtime.py",
    "orchestrator/tests/test_startup_runtime.py",
    "orchestrator/tests/test_goal_runtime.py",
    "orchestrator/tests/test_node_registry_v10.py",
    "orchestrator/tests/test_lean_dependency_runtime.py",
)
COLD_REQUIRED_PATHS = (
    "docs/CODEX_CONTROL.md",
    "docs/Codex/CURRENT.md",
    "orchestrator/routeb_goal_state.py",
    (
        "q3.lean.aristotle/ACTIVE/requests/"
        "routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
    ),
    *PHASE_A_CANDIDATE_PATHS,
)
COLD_STATIC_SPARSE_PATTERNS = (
    *("/" + relative for relative in COLD_REQUIRED_PATHS),
    "/docs/routeB_bus/*.goal.md",
    "/docs/routeB_bus/*.answer.md",
)
COLD_FORBIDDEN_ROOTS = ("docs/routeB_bus/litreview/pdfs",)


def _runtime_environment(temp_root: Path | None = None) -> dict[str, str]:
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    if temp_root is not None:
        temp_root.mkdir(parents=True, exist_ok=True)
        cache_root = temp_root / "cache"
        cache_root.mkdir(parents=True, exist_ok=True)
        environment.update(
            {
                "TMPDIR": str(temp_root),
                "TMP": str(temp_root),
                "TEMP": str(temp_root),
                "XDG_CACHE_HOME": str(cache_root),
            }
        )
    return environment


def _argv(command: object) -> list[str]:
    if isinstance(command, (list, tuple)):
        return [str(item) for item in command]
    if command is None:
        return []
    return [str(command)]


def _forbidden_argv_audit(commands: list[list[str]]) -> dict[str, Any]:
    findings: list[dict[str, Any]] = []
    forbidden_pattern = re.compile(
        r"(?<![A-Za-z0-9_.-])(" + "|".join(
            re.escape(item) for item in sorted(FORBIDDEN_RUNTIME_COMMANDS)
        ) + r")(?![A-Za-z0-9_.-])",
        re.IGNORECASE,
    )
    for command_index, command in enumerate(commands):
        for argument_index, argument in enumerate(command):
            basename = Path(argument).name.lower()
            forbidden = basename if basename in FORBIDDEN_RUNTIME_COMMANDS else None
            if forbidden is None:
                match = forbidden_pattern.search(argument)
                forbidden = match.group(1).lower() if match is not None else None
            if forbidden is not None:
                findings.append(
                    {
                        "command_index": command_index,
                        "argument_index": argument_index,
                        "argument": argument,
                        "forbidden": forbidden,
                    }
                )
    return {"pass": not findings, "findings": findings, "commands": commands}


def _functional_plan_audit(plan: dict[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    if plan.get("schema") != workflow_runtime.SHADOW_PLAN_SCHEMA:
        errors.append("PLAN_SCHEMA_MISMATCH")
    if plan.get("mode") != "SHADOW_V10_READ_ONLY":
        errors.append("PLAN_MODE_MISMATCH")
    if plan.get("run_authorized") is not False:
        errors.append("PLAN_RUN_AUTHORIZED")
    if plan.get("writes_performed") is not False:
        errors.append("PLAN_WRITES_PERFORMED")
    blocked = plan.get("blocked_features")
    blocked_names = (
        {
            item.get("feature")
            for item in blocked
            if isinstance(item, dict) and isinstance(item.get("feature"), str)
        }
        if isinstance(blocked, list)
        else set()
    )
    missing_blockers = sorted(REQUIRED_BLOCKED_FEATURES - blocked_names)
    if missing_blockers:
        errors.append("PLAN_REQUIRED_BLOCKERS_MISSING:" + ",".join(missing_blockers))
    holds = plan.get("holds")
    hold_values = [str(item) for item in holds] if isinstance(holds, list) else []
    if any("SHADOW_V10_UNAVAILABLE" in item for item in hold_values):
        errors.append("SHADOW_V10_UNAVAILABLE")
    expected_fatal_values = sorted(EXPECTED_LIVE_FATALS)
    status = plan.get("status")
    exact_live_fatal_status_pass = status == "HOLD"
    if not exact_live_fatal_status_pass:
        errors.append("PLAN_STATUS_NOT_EXPECTED_HOLD:" + str(status))
    expected_fatals = [
        item for item in hold_values if item in EXPECTED_LIVE_FATALS
    ]
    unexpected = [
        item for item in hold_values if item not in EXPECTED_LIVE_FATALS
    ]
    exact_live_fatal_set_pass = hold_values == expected_fatal_values
    if not exact_live_fatal_set_pass:
        detail = ",".join(unexpected) if unexpected else "MISSING_FATAL_CODE"
        errors.append("PLAN_UNEXPECTED_FATAL:" + detail)
    startup = plan.get("startup")
    startup_fatal_errors = (
        [str(item) for item in startup.get("fatal_errors", [])]
        if isinstance(startup, dict)
        and isinstance(startup.get("fatal_errors"), list)
        else []
    )
    startup_fatal_set_pass = startup_fatal_errors == expected_fatal_values
    if not startup_fatal_set_pass:
        errors.append("PLAN_STARTUP_FATAL_SET_MISMATCH")
    startup_honesty_state_pass = (
        isinstance(startup, dict)
        and startup.get("honesty_state") == "CHALLENGER_NOT_RH"
    )
    if not startup_honesty_state_pass:
        errors.append("PLAN_HONESTY_STATE_MISMATCH")
    exact_selector_pass = (
        isinstance(startup, dict)
        and startup.get("selected_goal") == EXPECTED_GOAL
        and startup.get("exact_node_pin") == EXPECTED_NODE
        and startup.get("exact_source_pin") == EXPECTED_SOURCE_PIN
        and startup.get("exact_theorem_pin") is None
        and startup.get("exact_consumer_pin") is None
    )
    if not exact_selector_pass:
        errors.append("PLAN_EXACT_SELECTOR_MISMATCH")
    legacy_v9_authority_unchanged_pass = (
        plan.get("legacy_v9_authority_unchanged") is True
    )
    if not legacy_v9_authority_unchanged_pass:
        errors.append("PLAN_LEGACY_V9_AUTHORITY_CHANGED")
    px_rh_claim_not_made_pass = plan.get("PX_RH_CLAIM") == "NOT_MADE"
    if not px_rh_claim_not_made_pass:
        errors.append("PLAN_PX_RH_CLAIM_CHANGED")
    return {
        "pass": not errors,
        "errors": errors,
        "status": status,
        "expected_live_fatals": expected_fatals,
        "exact_live_fatal_status_pass": exact_live_fatal_status_pass,
        "exact_live_fatal_set_pass": exact_live_fatal_set_pass,
        "startup_fatal_set_pass": startup_fatal_set_pass,
        "startup_honesty_state_pass": startup_honesty_state_pass,
        "exact_selector_pass": exact_selector_pass,
        "legacy_v9_authority_unchanged_pass": (
            legacy_v9_authority_unchanged_pass
        ),
        "px_rh_claim_not_made_pass": px_rh_claim_not_made_pass,
        "required_blocked_features": sorted(REQUIRED_BLOCKED_FEATURES),
        "observed_blocked_features": sorted(blocked_names),
    }


def _normalized_payload(payload: dict[str, Any], repo: Path) -> str:
    repo_text = str(repo.resolve())

    def normalize(value: Any) -> Any:
        if isinstance(value, dict):
            return {str(key): normalize(item) for key, item in value.items()}
        if isinstance(value, list):
            return [normalize(item) for item in value]
        if isinstance(value, str):
            return value.replace(repo_text, "$REPO")
        return value

    return json.dumps(
        normalize(payload), ensure_ascii=False, separators=(",", ":"), sort_keys=True
    )


def _normalized_command(command: list[str], repo: Path) -> list[str]:
    repo_text = str(repo)
    return [argument.replace(repo_text, "$REPO") for argument in command]


def _argv_multiset_containment(
    required: list[list[str]], observed: list[list[str]]
) -> dict[str, Any]:
    required_counts = Counter(tuple(command) for command in required)
    observed_counts = Counter(tuple(command) for command in observed)
    missing = [
        {
            "argv": list(command),
            "required": required_count,
            "observed": observed_counts[command],
            "missing": required_count - observed_counts[command],
        }
        for command, required_count in sorted(required_counts.items())
        if observed_counts[command] < required_count
    ]
    return {
        "pass": not missing,
        "required_count": sum(required_counts.values()),
        "observed_count": sum(observed_counts.values()),
        "missing": missing,
    }


def _command_name(command: object) -> str:
    if not isinstance(command, (list, tuple)) or not command:
        return ""
    return Path(str(command[0])).name


def _instrument_call(
    repo: Path, call: Callable[[Callable[[], dict[str, Any]]], T]
) -> tuple[T, dict[str, Any]]:
    counters = {
        "subprocess": 0,
        "git": 0,
        "path": 0,
        "repo_path": 0,
        "scandir": 0,
        "open": 0,
    }
    opened_repo_paths: set[str] = set()
    subprocess_argv: list[list[str]] = []
    original_run = subprocess.run
    original_scandir = os.scandir
    original_builtin_open = builtins.open
    original_io_open = io.open
    original_os_open = os.open
    repo_prefix = os.path.abspath(repo)

    def count_path(value: object, *, kind: str | None = None) -> None:
        counters["path"] += 1
        if kind is not None:
            counters[kind] += 1
        try:
            candidate = os.path.abspath(os.fspath(value))
            if os.path.commonpath((repo_prefix, candidate)) == repo_prefix:
                counters["repo_path"] += 1
                if kind in {"open", "scandir"}:
                    opened_repo_paths.add(candidate)
        except (TypeError, ValueError):
            pass

    def counted_run(*args: Any, **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        counters["subprocess"] += 1
        command = args[0] if args else kwargs.get("args")
        subprocess_argv.append(_argv(command))
        if _command_name(command) == "git":
            counters["git"] += 1
        return original_run(*args, **kwargs)

    def counted_scandir(path: object = ".") -> Any:
        count_path(path, kind="scandir")
        return original_scandir(path)

    def counted_io_open(file: object, *args: Any, **kwargs: Any) -> Any:
        count_path(file, kind="open")
        return original_io_open(file, *args, **kwargs)

    def counted_builtin_open(file: object, *args: Any, **kwargs: Any) -> Any:
        count_path(file, kind="open")
        return original_builtin_open(file, *args, **kwargs)

    def counted_os_open(file: object, *args: Any, **kwargs: Any) -> Any:
        count_path(file, kind="open")
        return original_os_open(file, *args, **kwargs)

    path_methods = (
        "read_text",
        "read_bytes",
        "open",
        "stat",
        "exists",
        "is_file",
        "is_dir",
        "is_symlink",
        "iterdir",
        "glob",
        "rglob",
        "resolve",
    )
    started = time.perf_counter()

    def checkpoint() -> dict[str, Any]:
        observed = dict(counters)
        observed["opened_repo_paths"] = len(opened_repo_paths)
        return {
            "duration_ms": round((time.perf_counter() - started) * 1000, 3),
            "counts": observed,
            "subprocess_argv": [list(command) for command in subprocess_argv],
        }

    with ExitStack() as stack:
        stack.enter_context(mock.patch.object(subprocess, "run", new=counted_run))
        stack.enter_context(mock.patch.object(os, "scandir", new=counted_scandir))
        stack.enter_context(mock.patch.object(builtins, "open", new=counted_builtin_open))
        stack.enter_context(mock.patch.object(io, "open", new=counted_io_open))
        stack.enter_context(mock.patch.object(os, "open", new=counted_os_open))
        for name in path_methods:
            original: Callable[..., Any] = getattr(Path, name)

            def counted_path(
                path: Path,
                *args: Any,
                _original: Callable[..., Any] = original,
                **kwargs: Any,
            ) -> Any:
                count_path(path)
                return _original(path, *args, **kwargs)

            stack.enter_context(mock.patch.object(Path, name, new=counted_path))
        value = call(checkpoint)
        metrics = checkpoint()
    return value, metrics


def _workflow_plan_command(repo: Path) -> list[str]:
    return [
        sys.executable,
        str(repo / "orchestrator/workflow_runtime.py"),
        "--root",
        str(repo),
        "plan",
        "--shadow-v10",
        "--benchmark-startup-timing",
    ]


def _shadow_output_budgets(plan: dict[str, Any], rendered: str) -> dict[str, Any]:
    startup_rendered = json.dumps(
        plan.get("startup", {}), ensure_ascii=False, indent=2, sort_keys=True
    )
    budgets = {
        "plan_bytes": len(rendered.encode("utf-8")),
        "plan_lines": len(rendered.splitlines()),
        "plan_bytes_limit": workflow_runtime.SHADOW_PLAN_MAX_BYTES,
        "plan_lines_limit": workflow_runtime.SHADOW_PLAN_MAX_LINES,
        "startup_bytes": len(startup_rendered.encode("utf-8")),
        "startup_lines": len(startup_rendered.splitlines()),
        "startup_bytes_limit": workflow_runtime.SHADOW_STARTUP_MAX_BYTES,
        "startup_lines_limit": workflow_runtime.SHADOW_STARTUP_MAX_LINES,
    }
    budgets["pass"] = (
        budgets["plan_bytes"] <= budgets["plan_bytes_limit"]
        and budgets["plan_lines"] <= budgets["plan_lines_limit"]
        and budgets["startup_bytes"] <= budgets["startup_bytes_limit"]
        and budgets["startup_lines"] <= budgets["startup_lines_limit"]
    )
    return budgets


def _shadow_result_summary(plan: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": plan.get("schema"),
        "status": plan.get("status"),
        "run_authorized": plan.get("run_authorized"),
        "selected_goal": plan.get("selected_goal"),
        "holds": plan.get("holds"),
        "blocked_features": plan.get("blocked_features"),
        "node_registry_status": plan.get("node_registry", {}).get("status"),
        "node_registry_code": plan.get("node_registry", {}).get("code"),
    }


def _instrumented_once(
    repo: Path, *, registry_scope: str | None = None
) -> dict[str, Any]:
    startup_capture: dict[str, Any] = {}
    snapshot_constructor_calls = 0
    original_builder = workflow_runtime.build_shadow_snapshot
    original_summary = workflow_runtime.node_registry_v10.startup_gate_summary

    def production_plan(
        checkpoint: Callable[[], dict[str, Any]],
    ) -> tuple[dict[str, Any], str]:
        nonlocal snapshot_constructor_calls

        def measured_builder(*args: Any, **kwargs: Any) -> Any:
            nonlocal snapshot_constructor_calls
            snapshot_constructor_calls += 1
            snapshot_started = time.perf_counter()
            snapshot = original_builder(*args, **kwargs)
            captured = checkpoint()
            captured["duration_ms"] = round(
                (time.perf_counter() - snapshot_started) * 1000, 3
            )
            startup_capture.update(captured)
            return snapshot

        def measured_summary(
            repo_arg: Path,
            selected_goal_path: object,
            owned_paths: object = (),
            *,
            exact_node_pin: str | None = None,
            exact_theorem_pin: str | None = None,
            exact_consumer_pin: str | None = None,
        ) -> dict[str, Any]:
            selected = (
                registry_scope if registry_scope is not None else selected_goal_path
            )
            if registry_scope is not None:
                exact_node_pin = None
                exact_theorem_pin = None
                exact_consumer_pin = None
            return original_summary(
                repo_arg,
                selected,
                owned_paths=owned_paths,
                exact_node_pin=exact_node_pin,
                exact_theorem_pin=exact_theorem_pin,
                exact_consumer_pin=exact_consumer_pin,
            )

        with (
            mock.patch.object(
                workflow_runtime, "build_shadow_snapshot", new=measured_builder
            ),
            mock.patch.object(
                workflow_runtime.node_registry_v10,
                "startup_gate_summary",
                new=measured_summary,
            ),
        ):
            plan = workflow_runtime.live_shadow_plan_v10(repo, owned_paths=[])
            return plan, workflow_runtime.render_shadow_plan_v10(plan)

    (plan, rendered), total_metrics = _instrument_call(repo, production_plan)
    if not startup_capture:
        raise RuntimeError("BENCHMARK_STARTUP_CHECKPOINT_MISSING")
    startup_metrics = dict(startup_capture)
    plan_metrics = {
        "duration_ms": round(
            max(0.0, total_metrics["duration_ms"] - startup_metrics["duration_ms"]),
            3,
        ),
        "counts": {
            name: max(
                0,
                int(total_metrics["counts"][name])
                - int(startup_metrics["counts"][name]),
            )
            for name in total_metrics["counts"]
        },
    }
    budgets = _shadow_output_budgets(plan, rendered)
    runtime_argv = [list(command) for command in total_metrics["subprocess_argv"]]
    return {
        "startup": startup_metrics,
        "plan": plan_metrics,
        "total": {
            "duration_ms": total_metrics["duration_ms"],
            "counts": total_metrics["counts"],
        },
        "result": _shadow_result_summary(plan),
        "payload": plan,
        "budgets": budgets,
        "snapshot_constructor_calls": snapshot_constructor_calls,
        "runtime_subprocess_argv": runtime_argv,
        "functional_audit": _functional_plan_audit(plan),
        "forbidden_argv_audit": _forbidden_argv_audit(runtime_argv),
        "measurement": {
            "duration": (
                "STARTUP_IS_EXACT_BUILD_SHADOW_SNAPSHOT_WALL; "
                "TOTAL_IS_LIVE_SHADOW_PLAN_IN_PROCESS_INCLUDES_RENDER"
            ),
            "counts": "VERIFIED_DIRECT_RUNTIME_COUNTS_NOT_OS_WIDE",
            "counts_scope": (
                "subprocess.run plus builtins.open io.open os.open os.scandir and Path APIs; "
                "child-process internal syscalls excluded"
            ),
        },
    }


def _run_direct_instrumentation(
    repo: Path, environment: dict[str, str]
) -> dict[str, Any]:
    with mock.patch.dict(os.environ, environment, clear=True):
        sample = _instrumented_once(repo)
    return {"repo": str(repo), "sample": sample}


def _status_manifest(repo: Path) -> dict[str, Any]:
    read_env = _runtime_environment()
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
        env=read_env,
    ).stdout.strip()
    origin = subprocess.run(
        ["git", "rev-parse", "origin/rh_clean"],
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
        env=read_env,
    )
    origin_head = origin.stdout.strip() if origin.returncode == 0 else None
    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=repo,
        check=True,
        capture_output=True,
        env=read_env,
    )
    tracked_diff = subprocess.run(
        ["git", "diff", "--binary", "HEAD", "--"],
        cwd=repo,
        check=True,
        capture_output=True,
        env=read_env,
    ).stdout
    staged_diff = subprocess.run(
        ["git", "diff", "--cached", "--binary", "HEAD", "--"],
        cwd=repo,
        check=True,
        capture_output=True,
        env=read_env,
    ).stdout
    untracked_raw = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "-z"],
        cwd=repo,
        check=True,
        capture_output=True,
        env=read_env,
    ).stdout
    entries = [
        item
        for item in status.stdout.decode("utf-8", "surrogateescape").split("\0")
        if item
    ]
    untracked_paths = [
        item
        for item in untracked_raw.decode("utf-8", "surrogateescape").split("\0")
        if item
    ]
    untracked: list[dict[str, Any]] = []
    for relative in sorted(untracked_paths):
        path = repo / relative
        if path.is_symlink():
            raw = os.readlink(path).encode("utf-8", "surrogateescape")
            kind = "symlink"
        else:
            raw = path.read_bytes()
            kind = "file"
        untracked.append(
            {
                "path": relative,
                "kind": kind,
                "bytes": len(raw),
                "sha256": hashlib.sha256(raw).hexdigest(),
            }
        )
    canonical = json.dumps(
        {
            "head": head,
            "origin_head": origin_head,
            "status_sha256": hashlib.sha256(status.stdout).hexdigest(),
            "tracked_diff_sha256": hashlib.sha256(tracked_diff).hexdigest(),
            "staged_diff_sha256": hashlib.sha256(staged_diff).hexdigest(),
            "untracked": untracked,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return {
        "sha256": hashlib.sha256(canonical).hexdigest(),
        "head": head,
        "origin_head": origin_head,
        "entry_count": len(entries),
        "entries": entries,
        "tracked_diff_bytes": len(tracked_diff),
        "tracked_diff_sha256": hashlib.sha256(tracked_diff).hexdigest(),
        "staged_diff_bytes": len(staged_diff),
        "staged_diff_sha256": hashlib.sha256(staged_diff).hexdigest(),
        "untracked": untracked,
    }


def _non_git_tree_manifest(repo: Path) -> dict[str, Any]:
    entries: dict[str, dict[str, Any]] = {}
    stack = [repo]
    while stack:
        directory = stack.pop()
        with os.scandir(directory) as iterator:
            children = sorted(iterator, key=lambda item: item.name)
        for child in children:
            path = Path(child.path)
            relative = path.relative_to(repo).as_posix()
            if relative == ".git" or relative.startswith(".git/"):
                continue
            if child.is_symlink():
                raw = os.readlink(path).encode("utf-8", "surrogateescape")
                entries[relative] = {
                    "kind": "symlink",
                    "bytes": len(raw),
                    "sha256": hashlib.sha256(raw).hexdigest(),
                }
            elif child.is_dir(follow_symlinks=False):
                entries[relative] = {"kind": "directory"}
                stack.append(path)
            elif child.is_file(follow_symlinks=False):
                raw = path.read_bytes()
                entries[relative] = {
                    "kind": "file",
                    "bytes": len(raw),
                    "sha256": hashlib.sha256(raw).hexdigest(),
                }
            else:
                stat = child.stat(follow_symlinks=False)
                entries[relative] = {
                    "kind": "other",
                    "mode": stat.st_mode,
                    "size": stat.st_size,
                }
    canonical = json.dumps(
        entries, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return {
        "sha256": hashlib.sha256(canonical).hexdigest(),
        "entry_count": len(entries),
        "entries": entries,
        "scope": "FULL_REPO_TREE_EXCLUDING_DOT_GIT_INCLUDES_IGNORED_PATHS",
    }


def _summary(rows: list[dict[str, Any]], stage: str) -> dict[str, Any]:
    durations = sorted(float(row[stage]["duration_ms"]) for row in rows)
    p95_index = max(0, math.ceil(len(durations) * 0.95) - 1)
    return {
        "runs": len(rows),
        "duration_ms": {
            "min": min(durations),
            "median": round(statistics.median(durations), 3),
            "p95": durations[p95_index],
            "max": max(durations),
        },
        "counts": {
            name: {
                "min": min(int(row[stage]["counts"][name]) for row in rows),
                "max": max(int(row[stage]["counts"][name]) for row in rows),
                "total": sum(int(row[stage]["counts"][name]) for row in rows),
            }
            for name in (
                "subprocess",
                "git",
                "path",
                "repo_path",
                "scandir",
                "open",
                "opened_repo_paths",
            )
        },
    }


def _canonical_sparse_paths(extra_sparse_paths: tuple[str, ...]) -> tuple[str, ...]:
    patterns: list[str] = []
    for raw in extra_sparse_paths:
        relative = PurePosixPath(raw)
        if (
            not raw
            or relative.is_absolute()
            or ".." in relative.parts
            or "\\" in raw
            or "\n" in raw
            or "\r" in raw
            or any(character in raw for character in "*?[]")
            or relative.as_posix() != raw
        ):
            raise RuntimeError("COLD_CHECKOUT_EXTRA_SPARSE_PATH_INVALID:" + raw)
        pattern = "/" + raw
        if pattern not in patterns:
            patterns.append(pattern)
    return tuple(patterns)


def _physical_goal_source_paths(repo: Path) -> tuple[str, ...]:
    sources: list[str] = []
    bus = repo / Path(*startup_runtime.BUS_REL.parts)
    try:
        with os.scandir(bus) as iterator:
            goals = sorted(
                Path(entry.path)
                for entry in iterator
                if not entry.is_symlink()
                and entry.is_file(follow_symlinks=False)
                and entry.name.endswith(".goal.md")
            )
    except OSError:
        return ()
    for goal in goals:
        answer = goal.with_name(goal.name.removesuffix(".goal.md") + ".answer.md")
        if answer.is_file():
            continue
        try:
            header = startup_runtime._goal_header_if_present(goal)
        except startup_runtime.StartupRuntimeError:
            continue
        if header is None or header.get("STATUS") != startup_runtime.OPEN_STATUS:
            continue
        source = header.get("SOURCE")
        if isinstance(source, str) and source:
            sources.append(source)
    return tuple(dict.fromkeys(sources))


def _plant_production_shape(repo: Path) -> None:
    """Add stable ignored/nested and collapsed-untracked benchmark plants."""

    opaque = repo / OPAQUE_BUS_SENTINEL_PATH
    opaque.parent.mkdir(parents=True, exist_ok=True)
    opaque.write_text("nested bus sentinel: never authoritative\n", encoding="utf-8")
    exclude = repo / ".git/info/exclude"
    exclude.parent.mkdir(parents=True, exist_ok=True)
    with exclude.open("a", encoding="utf-8") as handle:
        handle.write("\n/docs/routeB_bus/.benchmark-opaque/\n")
    collapsed = repo / ".benchmark-untracked/nested/sentinel.txt"
    collapsed.parent.mkdir(parents=True, exist_ok=True)
    collapsed.write_text("collapsed untracked parent plant\n", encoding="utf-8")


def _active_current_task_paths(repo: Path) -> tuple[str, ...]:
    current = repo / Path(*startup_runtime.CURRENT_REL.parts)
    try:
        payload = startup_runtime._current_mapping(current)
    except startup_runtime.StartupRuntimeError:
        return ()
    if payload.get("status") != "ACTIVE":
        return ()
    task_file = payload.get("task_file")
    return (task_file,) if isinstance(task_file, str) and task_file else ()


def _startup_dynamic_sparse_paths(repo: Path) -> tuple[str, ...]:
    return tuple(
        dict.fromkeys(
            (*_physical_goal_source_paths(repo), *_active_current_task_paths(repo))
        )
    )


def _materialized_lfs_filter_paths(repo: Path) -> tuple[str, ...]:
    materialized: list[str] = []
    stack = [repo]
    while stack:
        directory = stack.pop()
        with os.scandir(directory) as iterator:
            children = sorted(iterator, key=lambda item: item.name)
        for child in children:
            if directory == repo and child.name == ".git":
                continue
            path = Path(child.path)
            if child.is_symlink() or child.is_file(follow_symlinks=False):
                materialized.append(path.relative_to(repo).as_posix())
            elif child.is_dir(follow_symlinks=False):
                stack.append(path)
    if not materialized:
        return ()
    proc = subprocess.run(
        ["git", "check-attr", "--cached", "-z", "--stdin", "filter"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
        input="".join(relative + "\0" for relative in materialized),
    )
    raw = proc.stdout
    fields = raw.split("\0")
    if fields and fields[-1] == "":
        fields.pop()
    if len(fields) % 3:
        raise RuntimeError("COLD_CHECKOUT_LFS_ATTRIBUTE_OUTPUT_INVALID")
    lfs_paths = [
        path
        for path, attribute, value in zip(fields[0::3], fields[1::3], fields[2::3])
        if attribute == "filter" and value == "lfs"
    ]
    return tuple(sorted(set(lfs_paths)))


def _isolated_checkout(
    repo: Path,
    destination: Path,
    *,
    extra_sparse_paths: tuple[str, ...] = (),
) -> Path:
    extra_patterns = _canonical_sparse_paths(extra_sparse_paths)
    subprocess.run(
        [
            "git",
            "clone",
            "--quiet",
            "--shared",
            "--no-checkout",
            str(repo),
            str(destination),
        ],
        check=True,
        capture_output=True,
    )
    subprocess.run(
        ["git", "sparse-checkout", "init", "--no-cone"],
        cwd=destination,
        check=True,
        capture_output=True,
    )
    subprocess.run(
        [
            "git",
            "sparse-checkout",
            "set",
            "--no-cone",
            *COLD_STATIC_SPARSE_PATTERNS,
            *extra_patterns,
        ],
        cwd=destination,
        check=True,
        capture_output=True,
    )
    checkout_run = subprocess.run(
        ["git", "checkout", "--quiet", "HEAD"],
        cwd=destination,
        check=False,
        capture_output=True,
        text=True,
    )
    if checkout_run.returncode:
        raise RuntimeError(
            "COLD_CHECKOUT_FAILED:"
            + checkout_run.stderr.strip()
            + ":"
            + checkout_run.stdout.strip()
        )
    git_dir = destination / ".git"
    if not git_dir.is_dir():
        raise RuntimeError("COLD_CHECKOUT_GIT_DIR_MISSING")
    (git_dir / "q3-three-body.writer.lock").touch(exist_ok=True)
    missing = [
        relative
        for relative in (*COLD_REQUIRED_PATHS, *extra_sparse_paths)
        if not (destination / relative).is_file()
    ]
    if missing:
        raise RuntimeError("COLD_CHECKOUT_REQUIRED_PATH_MISSING:" + ",".join(missing))
    if not any((destination / "docs/routeB_bus").glob("*.goal.md")):
        raise RuntimeError("COLD_CHECKOUT_PHYSICAL_GOAL_SURFACE_MISSING")
    excluded = sorted(
        path.relative_to(destination).as_posix()
        for relative in COLD_FORBIDDEN_ROOTS
        for path in (destination / relative).rglob("*")
        if path.is_file() or path.is_symlink()
    )
    if excluded:
        raise RuntimeError(
            "COLD_CHECKOUT_NON_STARTUP_LFS_PAYLOAD_PRESENT:"
            + ",".join(excluded[:32])
        )
    materialized_lfs_paths = _materialized_lfs_filter_paths(destination)
    if materialized_lfs_paths:
        raise RuntimeError(
            "COLD_CHECKOUT_MATERIALIZED_LFS_FILTER_PRESENT:"
            + ",".join(materialized_lfs_paths[:32])
        )
    return destination


def _candidate_checkout(repo: Path, destination: Path) -> Path:
    startup_dynamic_paths = _startup_dynamic_sparse_paths(repo)
    checkout = _isolated_checkout(
        repo,
        destination,
        extra_sparse_paths=startup_dynamic_paths,
    )
    missing = [
        relative
        for relative in PHASE_A_CANDIDATE_PATHS
        if not (repo / relative).is_file()
    ]
    if missing:
        raise RuntimeError("PHASE_A_CANDIDATE_PATH_MISSING:" + ",".join(missing))
    for relative in PHASE_A_CANDIDATE_PATHS:
        source = repo / relative
        target = checkout / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    subprocess.run(
        ["git", "add", "--sparse", "--", *PHASE_A_CANDIDATE_PATHS],
        cwd=checkout,
        check=True,
        capture_output=True,
    )
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Control v10 Benchmark",
            "-c",
            "user.email=benchmark@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "temporary exact Phase A candidate",
        ],
        cwd=checkout,
        check=True,
        capture_output=True,
    )
    _plant_production_shape(checkout)
    return checkout


def _parse_production_startup_timing(stderr: str) -> dict[str, Any]:
    prefix = workflow_runtime._BENCHMARK_TIMING_PREFIX
    records = [
        line[len(prefix) :]
        for line in stderr.splitlines()
        if line.startswith(prefix)
    ]
    if not records:
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_MISSING")
    if len(records) != 1:
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_DUPLICATE")
    try:
        timing = json.loads(records[0])
    except json.JSONDecodeError as exc:
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_INVALID_JSON") from exc
    required_keys = {
        "schema",
        "startup_duration_ms",
        "snapshot_constructor_calls",
    }
    if not isinstance(timing, dict) or set(timing) != required_keys:
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_FIELDS_INVALID")
    if timing["schema"] != workflow_runtime._BENCHMARK_TIMING_SCHEMA:
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_SCHEMA_INVALID")
    duration = timing["startup_duration_ms"]
    if (
        isinstance(duration, bool)
        or not isinstance(duration, (int, float))
        or not math.isfinite(float(duration))
        or float(duration) < 0
    ):
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_DURATION_INVALID")
    constructor_calls = timing["snapshot_constructor_calls"]
    if (
        isinstance(constructor_calls, bool)
        or not isinstance(constructor_calls, int)
        or constructor_calls != 1
    ):
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_SNAPSHOT_COUNT_INVALID")
    return {
        "schema": timing["schema"],
        "startup_duration_ms": float(duration),
        "snapshot_constructor_calls": constructor_calls,
    }


def _run_production_cli(
    repo: Path, environment: dict[str, str]
) -> dict[str, Any]:
    command = _workflow_plan_command(repo)
    manifest_before = _non_git_tree_manifest(repo)
    started = time.perf_counter()
    proc = subprocess.run(
        command,
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
        env=environment,
    )
    duration_ms = round((time.perf_counter() - started) * 1000, 3)
    manifest_after = _non_git_tree_manifest(repo)
    changed_paths = sorted(
        relative
        for relative in set(manifest_before["entries"])
        | set(manifest_after["entries"])
        if manifest_before["entries"].get(relative)
        != manifest_after["entries"].get(relative)
    )
    write_audit = {
        "before_sha256": manifest_before["sha256"],
        "after_sha256": manifest_after["sha256"],
        "entry_count_before": manifest_before["entry_count"],
        "entry_count_after": manifest_after["entry_count"],
        "changed_paths": changed_paths,
        "pass": manifest_before == manifest_after,
        "scope": manifest_before["scope"],
        "measurement_excludes_manifest_wall": True,
    }
    if changed_paths:
        raise RuntimeError(
            "BENCHMARK_DIRECT_PRODUCTION_REPO_WRITE:"
            + ",".join(changed_paths[:32])
        )
    if proc.returncode not in {0, 2}:
        raise RuntimeError(f"PRODUCTION_CLI_FAILED:{proc.stderr.strip()}")
    startup_timing = _parse_production_startup_timing(proc.stderr)
    if startup_timing["startup_duration_ms"] > duration_ms:
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_EXCEEDS_TOTAL")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError("PRODUCTION_CLI_OUTPUT_INVALID") from exc
    if not isinstance(payload, dict):
        raise RuntimeError("PRODUCTION_CLI_OUTPUT_NOT_OBJECT")
    return {
        "repo": str(repo),
        "command": command,
        "returncode": proc.returncode,
        "duration_ms": duration_ms,
        "startup_timing": startup_timing,
        "payload": payload,
        "functional_audit": _functional_plan_audit(payload),
        "write_audit": write_audit,
    }


_STRACE_SYSCALL = re.compile(
    r"^\s*(?:\d+\s+)?(?:\[pid\s+\d+\]\s+)?(?P<name>[A-Za-z_][A-Za-z0-9_]*)\("
)
_STRACE_UNFINISHED = re.compile(
    r"^\s*(?:(?P<pid>\d+)\s+|\[pid\s+(?P<bracket_pid>\d+)\]\s+)?"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)\(.*<unfinished \.\.\.>\s*$"
)
_STRACE_RESUMED = re.compile(
    r"^\s*(?:(?P<pid>\d+)\s+|\[pid\s+(?P<bracket_pid>\d+)\]\s+)?"
    r"<\.\.\. (?P<name>[A-Za-z_][A-Za-z0-9_]*) resumed>(?P<rest>.*)$"
)
_STRACE_OPEN_RESULT = re.compile(
    r"\bopen(?:at|at2)?\(.*\)\s+=\s+\d+<([^>]+)>"
)
_STRACE_ANNOTATED_PATH = re.compile(r"<([^<>]+)>")
_STRACE_QUOTED_VALUE = re.compile(r'"((?:\\.|[^"\\])*)"')
_WRITE_OPEN_FLAGS = re.compile(
    r"\bO_(?:WRONLY|RDWR|CREAT|TRUNC|APPEND|TMPFILE)\b"
)
_FD_WRITE_SYSCALLS = frozenset(
    {"write", "writev", "pwrite64", "pwritev", "pwritev2", "ftruncate"}
)
_COPY_WRITE_SYSCALLS = frozenset({"copy_file_range", "sendfile"})
_PATH_MUTATION_SYSCALLS = frozenset(
    {
        "chmod",
        "chown",
        "creat",
        "fchmodat",
        "fchownat",
        "lchown",
        "link",
        "linkat",
        "mkdir",
        "mkdirat",
        "mknod",
        "mknodat",
        "rename",
        "renameat",
        "renameat2",
        "rmdir",
        "symlink",
        "symlinkat",
        "truncate",
        "unlink",
        "unlinkat",
        "utime",
        "utimensat",
        "utimes",
    }
)


def _strace_syscall_name(line: str) -> str | None:
    match = _STRACE_SYSCALL.match(line)
    return match.group("name") if match is not None else None


def _coalesce_strace_records(trace: str) -> tuple[list[tuple[int, str]], list[str]]:
    records: list[tuple[int, str]] = []
    pending: dict[str, tuple[str, str, int]] = {}
    errors: list[str] = []
    for line_number, line in enumerate(trace.splitlines(), start=1):
        unfinished = _STRACE_UNFINISHED.match(line)
        if unfinished is not None:
            pid = unfinished.group("pid") or unfinished.group("bracket_pid") or "ROOT"
            if pid in pending:
                errors.append(f"NESTED_UNFINISHED:{pid}:{line_number}")
                continue
            prefix = line[: line.rfind("<unfinished ...>")]
            pending[pid] = (unfinished.group("name"), prefix, line_number)
            continue
        resumed = _STRACE_RESUMED.match(line)
        if resumed is not None:
            pid = resumed.group("pid") or resumed.group("bracket_pid") or "ROOT"
            prior = pending.pop(pid, None)
            if prior is None:
                errors.append(f"ORPHAN_RESUMED:{pid}:{line_number}")
                continue
            name, prefix, source_line = prior
            if name != resumed.group("name"):
                errors.append(
                    f"RESUMED_NAME_MISMATCH:{pid}:{name}:{resumed.group('name')}"
                )
                continue
            records.append((source_line, prefix + resumed.group("rest")))
            continue
        records.append((line_number, line))
    errors.extend(
        f"UNRESOLVED_UNFINISHED:{pid}:{name}:{line_number}"
        for pid, (name, _prefix, line_number) in sorted(pending.items())
    )
    return records, errors


def _decode_strace_string(value: str) -> str | None:
    try:
        decoded = json.loads(f'"{value}"')
    except json.JSONDecodeError:
        return None
    return decoded if isinstance(decoded, str) else None


def _repo_path(value: str, repo: Path) -> str | None:
    cleaned = value.removesuffix(" (deleted)")
    if cleaned.startswith(("pipe:[", "socket:[", "anon_inode:")):
        return None
    candidate = Path(cleaned)
    if not candidate.is_absolute():
        candidate = repo / candidate
    normalized = os.path.abspath(os.path.normpath(candidate))
    repo_prefix = os.path.abspath(repo)
    try:
        if os.path.commonpath((repo_prefix, normalized)) != repo_prefix:
            return None
    except ValueError:
        return None
    return normalized


def _annotated_paths_ordered(line: str) -> list[str]:
    return _STRACE_ANNOTATED_PATH.findall(line)


def _annotated_repo_paths(line: str, repo: Path) -> list[str]:
    return sorted(
        {
            path
            for value in _annotated_paths_ordered(line)
            if (path := _repo_path(value, repo)) is not None
        }
    )


def _quoted_repo_paths(line: str, repo: Path) -> list[str]:
    paths: set[str] = set()
    for encoded in _STRACE_QUOTED_VALUE.findall(line):
        decoded = _decode_strace_string(encoded)
        if decoded is None:
            continue
        path = _repo_path(decoded, repo)
        if path is not None:
            paths.add(path)
    return sorted(paths)


def _parse_strace_opened_repo_paths(trace: str, repo: Path) -> list[str]:
    opened: set[str] = set()
    records, _errors = _coalesce_strace_records(trace)
    for _line_number, line in records:
        match = _STRACE_OPEN_RESULT.search(line)
        if match is None:
            continue
        candidate = _repo_path(match.group(1), repo)
        if candidate is not None:
            opened.add(candidate)
    return sorted(opened)


def _extract_execve_argv(line: str) -> list[str]:
    syscall = _strace_syscall_name(line)
    if syscall not in {"execve", "execveat"}:
        raise ValueError("NOT_EXECVE")
    start = line.find("[")
    if start < 0:
        raise ValueError("EXECVE_ARGV_START_MISSING")
    quoted = False
    escaped = False
    depth = 0
    end = -1
    for index in range(start, len(line)):
        character = line[index]
        if quoted:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                quoted = False
            continue
        if character == '"':
            quoted = True
        elif character == "[":
            depth += 1
        elif character == "]":
            depth -= 1
            if depth == 0:
                end = index
                break
    if end < 0:
        raise ValueError("EXECVE_ARGV_END_MISSING")
    try:
        parsed = json.loads(line[start : end + 1])
    except json.JSONDecodeError as exc:
        raise ValueError("EXECVE_ARGV_UNPARSED") from exc
    if not isinstance(parsed, list) or not all(isinstance(item, str) for item in parsed):
        raise ValueError("EXECVE_ARGV_INVALID")
    return parsed


def _sentinel_manifest(repo: Path) -> dict[str, dict[str, Any]]:
    manifest: dict[str, dict[str, Any]] = {}
    for relative in TRACE_SENTINEL_PATHS:
        path = repo / relative
        if not path.is_file() or path.is_symlink():
            raise RuntimeError("TRACE_SENTINEL_UNAVAILABLE:" + relative)
        raw = path.read_bytes()
        manifest[relative] = {
            "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
        }
    return manifest


def _strace_integer_result(line: str) -> int | None:
    results = re.findall(r"\)\s+=\s+(-?\d+)(?=<|\s|$)", line)
    return int(results[-1]) if results else None


def _strace_write_events(trace: str, repo: Path) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    records, fragment_errors = _coalesce_strace_records(trace)
    if fragment_errors:
        raise RuntimeError("STRACE_FRAGMENT_GAP:" + ",".join(fragment_errors))
    for line_number, line in records:
        syscall = _strace_syscall_name(line)
        if syscall is None:
            continue
        result = _strace_integer_result(line)
        if result is None or result < 0:
            continue
        annotated_values = _annotated_paths_ordered(line)
        annotated = [
            path
            for value in annotated_values
            if (path := _repo_path(value, repo)) is not None
        ]
        quoted = _quoted_repo_paths(line, repo)
        paths: list[str] = []
        kind: str | None = None
        if syscall in {"open", "openat", "openat2"} and _WRITE_OPEN_FLAGS.search(line):
            opened_match = _STRACE_OPEN_RESULT.search(line)
            opened_path = (
                _repo_path(opened_match.group(1), repo)
                if opened_match is not None
                else None
            )
            paths = [opened_path] if opened_path is not None else quoted
            kind = "WRITE_CAPABLE_OPEN"
        elif syscall in _FD_WRITE_SYSCALLS:
            destination = (
                _repo_path(annotated_values[0], repo)
                if annotated_values
                else None
            )
            paths = [destination] if destination is not None else []
            kind = "FD_WRITE_OR_TRUNCATE"
        elif syscall == "copy_file_range":
            destination = (
                _repo_path(annotated_values[1], repo)
                if len(annotated_values) >= 2
                else None
            )
            paths = [destination] if destination is not None else []
            kind = "COPY_DESTINATION"
        elif syscall == "sendfile":
            destination = (
                _repo_path(annotated_values[0], repo)
                if annotated_values
                else None
            )
            paths = [destination] if destination is not None else []
            kind = "COPY_DESTINATION"
        elif syscall in _PATH_MUTATION_SYSCALLS:
            paths = sorted(set(annotated + quoted))
            kind = "PATH_MUTATION"
        if kind is None:
            continue
        for path in paths:
            events.append(
                {
                    "line": line_number,
                    "syscall": syscall,
                    "kind": kind,
                    "path": path,
                }
            )
    return events


def _analyze_strace(
    trace: str,
    repo: Path,
    *,
    expected_root_argv: list[str],
    sentinels_before: dict[str, dict[str, Any]],
    sentinels_after: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    if not trace.strip():
        raise RuntimeError("STRACE_TRACE_EMPTY_FAIL_CLOSED")
    records, fragment_errors = _coalesce_strace_records(trace)
    if fragment_errors:
        raise RuntimeError("STRACE_FRAGMENT_GAP:" + ",".join(fragment_errors))
    syscall_records = [
        (line_number, line)
        for line_number, line in records
        if _strace_syscall_name(line) is not None
    ]
    if not syscall_records:
        raise RuntimeError("STRACE_TRACE_UNPARSED_FAIL_CLOSED")
    execve_records = [
        (line_number, line)
        for line_number, line in syscall_records
        if _strace_syscall_name(line) in {"execve", "execveat"}
    ]
    execve_argv: list[list[str]] = []
    successful_execve_argv: list[list[str]] = []
    execve_errors: list[str] = []
    for _line_number, line in execve_records:
        try:
            argv = _extract_execve_argv(line)
            execve_argv.append(argv)
            if _strace_integer_result(line) == 0:
                successful_execve_argv.append(argv)
        except ValueError as exc:
            execve_errors.append(str(exc))
    logical_trace = "\n".join(line for _line_number, line in records)
    opened = _parse_strace_opened_repo_paths(logical_trace, repo)
    observed = sorted(
        {
            path
            for _line_number, line in syscall_records
            for path in (*_annotated_repo_paths(line, repo), *_quoted_repo_paths(line, repo))
        }
    )
    write_events = _strace_write_events(logical_trace, repo)
    sentinels_unchanged = sentinels_before == sentinels_after
    sentinel_observed = {
        relative: os.path.abspath(repo / relative) in opened
        for relative in TRACE_SENTINEL_PATHS
    }
    opaque_bus_sentinel_not_opened = (
        os.path.abspath(repo / OPAQUE_BUS_SENTINEL_PATH) not in opened
    )
    runtime_execve_argv = list(successful_execve_argv)
    if expected_root_argv in runtime_execve_argv:
        runtime_execve_argv.remove(expected_root_argv)
    runtime_git_argv = [
        argv
        for argv in runtime_execve_argv
        if argv and Path(argv[0]).name.lower() == "git"
    ]
    trace_coverage = {
        "nonempty": True,
        "fragment_parser_complete": not fragment_errors,
        "syscall_lines_present": bool(syscall_records),
        "execve_present": bool(execve_records),
        "execve_argv_fully_parsed": len(execve_argv) == len(execve_records)
        and not execve_errors,
        "exact_root_execve_succeeded": expected_root_argv in successful_execve_argv,
        "repo_open_paths_present": bool(opened),
        "all_sentinels_successfully_opened": all(sentinel_observed.values()),
        "sentinel_manifest_complete": (
            set(sentinels_before) == set(TRACE_SENTINEL_PATHS)
            and set(sentinels_after) == set(TRACE_SENTINEL_PATHS)
        ),
        "opaque_bus_sentinel_not_opened": opaque_bus_sentinel_not_opened,
    }
    trace_coverage_pass = all(trace_coverage.values())
    if not trace_coverage_pass:
        failed = ",".join(
            key for key, passed in trace_coverage.items() if not passed
        )
        raise RuntimeError("STRACE_TRACE_COVERAGE_INCOMPLETE:" + failed)
    write_free_pass = not write_events and sentinels_unchanged
    return {
        "trace_coverage": trace_coverage,
        "trace_coverage_pass": trace_coverage_pass,
        "syscall_line_count": len(syscall_records),
        "execve_line_count": len(execve_records),
        "execve_argv": execve_argv,
        "successful_execve_argv": successful_execve_argv,
        "runtime_execve_argv": runtime_execve_argv,
        "runtime_subprocess_count": len(runtime_execve_argv),
        "runtime_git_count": len(runtime_git_argv),
        "execve_parse_errors": execve_errors,
        "opened_repo_paths": opened,
        "opened_repo_paths_count": len(opened),
        "observed_repo_paths_count": len(observed),
        "observed_repo_paths_sha256": hashlib.sha256(
            "\n".join(observed).encode("utf-8")
        ).hexdigest(),
        "write_events": write_events,
        "ignored_repo_paths_in_scope": True,
        "sentinel_trace_observed": sentinel_observed,
        "opaque_bus_sentinel_not_opened": opaque_bus_sentinel_not_opened,
        "sentinels_before": sentinels_before,
        "sentinels_after": sentinels_after,
        "sentinels_unchanged": sentinels_unchanged,
        "write_free_pass": write_free_pass,
    }


def _run_audited_process(
    repo: Path, environment: dict[str, str], trace_path: Path
) -> dict[str, Any]:
    strace = shutil.which("strace") if sys.platform.startswith("linux") else None
    if strace is None:
        raise RuntimeError("STRACE_UNAVAILABLE_FAIL_CLOSED")
    trace_path.parent.mkdir(parents=True, exist_ok=True)
    runtime_command = _workflow_plan_command(repo)
    command = [
        strace,
        "-f",
        "-yy",
        "-qq",
        "-v",
        "-s",
        "4096",
        "-e",
        "trace=%file,%desc,execve,execveat",
        "-o",
        str(trace_path),
        "--",
        *runtime_command,
    ]
    sentinels_before = _sentinel_manifest(repo)
    started = time.perf_counter()
    proc = subprocess.run(
        command,
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
        env=environment,
    )
    duration_ms = round((time.perf_counter() - started) * 1000, 3)
    if proc.returncode not in {0, 2}:
        raise RuntimeError(
            f"AUDITED_PROCESS_FAILED:{proc.returncode}:{proc.stderr.strip()}"
        )
    startup_timing = _parse_production_startup_timing(proc.stderr)
    if startup_timing["startup_duration_ms"] > duration_ms:
        raise RuntimeError("BENCHMARK_STARTUP_TIMING_EXCEEDS_TOTAL")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError("AUDITED_PROCESS_OUTPUT_INVALID") from exc
    if not isinstance(payload, dict):
        raise RuntimeError("AUDITED_PROCESS_OUTPUT_NOT_PLAN")
    try:
        trace = trace_path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        raise RuntimeError("STRACE_OUTPUT_UNAVAILABLE") from exc
    sentinels_after = _sentinel_manifest(repo)
    trace_audit = _analyze_strace(
        trace,
        repo,
        expected_root_argv=runtime_command,
        sentinels_before=sentinels_before,
        sentinels_after=sentinels_after,
    )
    counts = {
        "subprocess": trace_audit["runtime_subprocess_count"],
        "git": trace_audit["runtime_git_count"],
        "path": trace_audit["observed_repo_paths_count"],
        "repo_path": trace_audit["observed_repo_paths_count"],
        "scandir": 0,
        "open": trace_audit["opened_repo_paths_count"],
        "opened_repo_paths": trace_audit["opened_repo_paths_count"],
    }
    zero_counts = {name: 0 for name in counts}
    sample = {
        "payload": payload,
        "startup": {
            "duration_ms": startup_timing["startup_duration_ms"],
            "counts": dict(counts),
        },
        "plan": {
            "duration_ms": round(
                max(0.0, duration_ms - startup_timing["startup_duration_ms"]),
                3,
            ),
            "counts": zero_counts,
        },
        "total": {"duration_ms": duration_ms, "counts": dict(counts)},
        "result": _shadow_result_summary(payload),
        "budgets": _shadow_output_budgets(payload, proc.stdout),
        "snapshot_constructor_calls": startup_timing["snapshot_constructor_calls"],
        "runtime_subprocess_argv": trace_audit["runtime_execve_argv"],
        "functional_audit": _functional_plan_audit(payload),
    }
    return {
        "repo": str(repo),
        "command": command,
        "runtime_command": runtime_command,
        "returncode": proc.returncode,
        "duration_ms": duration_ms,
        "sample": sample,
        "trace_audit": trace_audit,
    }


def _combine_runtime_sample(
    production: dict[str, Any],
    direct: dict[str, Any],
    audited: dict[str, Any],
) -> dict[str, Any]:
    audited_sample = audited["sample"]
    direct_sample = direct["sample"]
    production_normalized = _normalized_payload(
        production["payload"], Path(production["repo"])
    )
    direct_normalized = _normalized_payload(
        direct_sample["payload"], Path(direct["repo"])
    )
    audited_normalized = _normalized_payload(
        audited_sample["payload"], Path(audited["repo"])
    )
    payload_parity = {
        "production_matches_audited": production_normalized == audited_normalized,
        "production_matches_direct": production_normalized == direct_normalized,
        "direct_matches_audited": direct_normalized == audited_normalized,
        "production_sha256": hashlib.sha256(
            production_normalized.encode("utf-8")
        ).hexdigest(),
        "direct_sha256": hashlib.sha256(
            direct_normalized.encode("utf-8")
        ).hexdigest(),
        "audited_sha256": hashlib.sha256(
            audited_normalized.encode("utf-8")
        ).hexdigest(),
    }
    payload_parity["pass"] = all(
        payload_parity[field]
        for field in (
            "production_matches_audited",
            "production_matches_direct",
            "direct_matches_audited",
        )
    )
    trace_audit = audited["trace_audit"]
    direct_commands = [
        list(command) for command in direct_sample["runtime_subprocess_argv"]
    ]
    commands = [
        list(production["command"]),
        list(audited["command"]),
        list(audited["runtime_command"]),
        *direct_commands,
        *[
            list(command)
            for command in audited_sample["runtime_subprocess_argv"]
        ],
        *[list(command) for command in trace_audit["successful_execve_argv"]],
    ]
    forbidden_argv = _forbidden_argv_audit(commands)
    functional_pass = all(
        audit["pass"]
        for audit in (
            production["functional_audit"],
            direct_sample["functional_audit"],
            audited_sample["functional_audit"],
        )
    )
    functional_invariant_fields = (
        "exact_live_fatal_status_pass",
        "exact_live_fatal_set_pass",
        "startup_fatal_set_pass",
        "startup_honesty_state_pass",
        "exact_selector_pass",
        "legacy_v9_authority_unchanged_pass",
        "px_rh_claim_not_made_pass",
    )
    functional_invariants = {
        field: all(
            audit.get(field) is True
            for audit in (
                production["functional_audit"],
                direct_sample["functional_audit"],
                audited_sample["functional_audit"],
            )
        )
        for field in functional_invariant_fields
    }
    production_startup = production["startup_timing"]
    direct_startup_duration_ms = direct_sample["startup"]["duration_ms"]
    audited_startup_duration_ms = audited_sample["startup"]["duration_ms"]
    startup = dict(direct_sample["startup"])
    startup["duration_ms"] = production_startup["startup_duration_ms"]
    startup["measurement"] = "DIRECT_PRODUCTION_BUILD_SHADOW_SNAPSHOT_WALL"
    startup["direct_instrumented_duration_ms"] = direct_startup_duration_ms
    startup["direct_instrumented_measurement"] = (
        "IN_PROCESS_DIRECT_CALL_DIAGNOSTIC_NOT_PERFORMANCE_BUDGET"
    )
    startup["audited_twin_duration_ms"] = audited_startup_duration_ms
    startup["audited_twin_measurement"] = (
        "EXACT_PRODUCTION_CLI_STRACE_DIAGNOSTIC_NOT_PERFORMANCE_BUDGET"
    )
    startup["counts_measurement"] = "DIRECT_PYTHON_CALL_INSTRUMENTATION"
    plan = dict(direct_sample["plan"])
    plan["duration_ms"] = round(
        max(0.0, production["duration_ms"] - startup["duration_ms"]), 3
    )
    plan["measurement"] = "DIRECT_PRODUCTION_TOTAL_MINUS_STARTUP"
    plan["counts_measurement"] = "DIRECT_PYTHON_CALL_INSTRUMENTATION"
    total = {
        "duration_ms": production["duration_ms"],
        "counts": dict(direct_sample["total"]["counts"]),
        "counts_measurement": (
            "LINUX_STRACE_FULL_PROCESS_TREE_SUBPROCESS_AND_GIT_COUNTS; "
            "LINUX_STRACE_UNIQUE_REPO_OPENS; "
            "DIRECT_PYTHON_COUNTS_RETAINED_FOR_NON_BUDGET_DIAGNOSTICS"
        ),
    }
    total["counts"]["subprocess"] = trace_audit["runtime_subprocess_count"]
    total["counts"]["git"] = trace_audit["runtime_git_count"]
    total["counts"]["opened_repo_paths"] = trace_audit["opened_repo_paths_count"]
    production_runtime_command = _normalized_command(
        list(production["command"]), Path(production["repo"])
    )
    audited_runtime_command = _normalized_command(
        list(audited["runtime_command"]), Path(audited["repo"])
    )
    normalized_direct_commands = [
        _normalized_command(command, Path(direct["repo"]))
        for command in direct_commands
    ]
    normalized_successful_trace_commands = [
        _normalized_command(list(command), Path(audited["repo"]))
        for command in trace_audit["successful_execve_argv"]
    ]
    direct_argv_containment = _argv_multiset_containment(
        normalized_direct_commands,
        normalized_successful_trace_commands,
    )
    process_count_crosscheck = {
        "production_runtime_command": production_runtime_command,
        "audited_runtime_command": audited_runtime_command,
        "exact_production_cli_trace_pass": (
            production_runtime_command == audited_runtime_command
        ),
        "direct_runtime_subprocess": direct_sample["total"]["counts"][
            "subprocess"
        ],
        "direct_runtime_git": direct_sample["total"]["counts"]["git"],
        "trace_runtime_subprocess": trace_audit["runtime_subprocess_count"],
        "trace_runtime_git": trace_audit["runtime_git_count"],
        "direct_argv_multiset_containment": direct_argv_containment,
        "pass": (
            production_runtime_command == audited_runtime_command
            and direct_argv_containment["pass"]
        ),
    }
    operation_count_budget = {
        "subprocess": total["counts"]["subprocess"],
        "subprocess_limit": SUBPROCESS_MAX_PER_RUN,
        "git": total["counts"]["git"],
        "git_limit": GIT_MAX_PER_RUN,
        "opened_repo_paths": total["counts"]["opened_repo_paths"],
        "opened_repo_paths_limit": OPENED_REPO_PATHS_MAX_PER_RUN,
        "subprocess_git_measurement": "LINUX_STRACE_FULL_PROCESS_TREE",
        "opened_repo_paths_measurement": "LINUX_STRACE_FULL_PROCESS_TREE",
    }
    operation_count_budget["pass"] = (
        operation_count_budget["subprocess"]
        <= operation_count_budget["subprocess_limit"]
        and operation_count_budget["git"] <= operation_count_budget["git_limit"]
        and operation_count_budget["opened_repo_paths"]
        <= operation_count_budget["opened_repo_paths_limit"]
    )
    opened_digest = hashlib.sha256(
        "\n".join(trace_audit["opened_repo_paths"]).encode("utf-8")
    ).hexdigest()
    runtime_acceptance = {
        "functional_plan_pass": functional_pass,
        **functional_invariants,
        "full_payload_parity_pass": bool(payload_parity["pass"]),
        "forbidden_argv_pass": forbidden_argv["pass"],
        "direct_production_tree_manifest_pass": (
            production["write_audit"]["pass"] is True
        ),
        "write_free_pass": trace_audit["write_free_pass"],
        "trace_coverage_pass": trace_audit["trace_coverage_pass"],
        "process_count_crosscheck_pass": process_count_crosscheck["pass"],
        "snapshot_count_parity_pass": (
            production_startup["snapshot_constructor_calls"] == 1
            and direct_sample["snapshot_constructor_calls"] == 1
            and audited_sample["snapshot_constructor_calls"] == 1
        ),
    }
    runtime_acceptance["pass"] = all(runtime_acceptance.values())
    return {
        "startup": startup,
        "plan": plan,
        "total": total,
        "result": dict(audited_sample["result"]),
        "budgets": dict(audited_sample["budgets"]),
        "operation_count_budget": operation_count_budget,
        "snapshot_constructor_calls": production_startup[
            "snapshot_constructor_calls"
        ],
        "runtime_subprocess_argv": commands,
        "direct_runtime_subprocess_argv": direct_commands,
        "functional_audits": {
            "production": production["functional_audit"],
            "direct": direct_sample["functional_audit"],
            "audited": audited_sample["functional_audit"],
        },
        "process_count_crosscheck": process_count_crosscheck,
        "forbidden_argv_audit": forbidden_argv,
        "payload_parity": payload_parity,
        "production_cli": {
            "command": production["command"],
            "returncode": production["returncode"],
            "duration_ms": production["duration_ms"],
            "startup_timing": dict(production_startup),
            "write_audit": dict(production["write_audit"]),
        },
        "audited_process": {
            "command": audited["command"],
            "returncode": audited["returncode"],
            "duration_ms": audited["duration_ms"],
            "startup_duration_ms": audited_startup_duration_ms,
        },
        "descendant_process_diagnostics": {
            "subprocess_count": trace_audit["runtime_subprocess_count"],
            "git_count": trace_audit["runtime_git_count"],
            "runtime_execve_argv": trace_audit["runtime_execve_argv"],
            "budget_authority": True,
        },
        "strace": {
            "command": audited["command"],
            "returncode": audited["returncode"],
            "opened_repo_paths": trace_audit["opened_repo_paths_count"],
            "opened_repo_paths_sha256": opened_digest,
            "opened_repo_paths_sample": trace_audit["opened_repo_paths"][:16],
            "execve_argv": trace_audit["execve_argv"],
            "successful_execve_argv": trace_audit["successful_execve_argv"],
            "runtime_execve_argv": trace_audit["runtime_execve_argv"],
            "write_events": trace_audit["write_events"],
            "write_free_pass": trace_audit["write_free_pass"],
            "trace_coverage": trace_audit["trace_coverage"],
            "trace_coverage_pass": trace_audit["trace_coverage_pass"],
            "sentinels_before": trace_audit["sentinels_before"],
            "sentinels_after": trace_audit["sentinels_after"],
            "sentinels_unchanged": trace_audit["sentinels_unchanged"],
            "ignored_repo_paths_in_scope": trace_audit[
                "ignored_repo_paths_in_scope"
            ],
        },
        "runtime_acceptance": runtime_acceptance,
    }


def _prime_runtime_measurement(repo: Path, temp_root: Path) -> dict[str, Any]:
    production = _run_production_cli(
        repo, _runtime_environment(temp_root / "production-environment")
    )
    return {
        "production": production,
        "write_audit": dict(production["write_audit"]),
    }


def _warm_samples(
    repo: Path, temp_root: Path, *, runs: int
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    prime = _prime_runtime_measurement(repo, temp_root / "prime")
    samples: list[dict[str, Any]] = []
    for index in range(runs):
        run_root = temp_root / f"run-{index:02d}"
        production = _run_production_cli(
            repo, _runtime_environment(run_root / "production-environment")
        )
        direct = _run_direct_instrumentation(
            repo, _runtime_environment(run_root / "direct-environment")
        )
        audited = _run_audited_process(
            repo,
            _runtime_environment(run_root / "audited-environment"),
            run_root / "trace" / "runtime.strace",
        )
        samples.append(_combine_runtime_sample(production, direct, audited))
    return prime, samples


def _cold_once(repo: Path, temp_root: Path) -> dict[str, Any]:
    temp_root.mkdir(parents=True, exist_ok=True)
    startup_dynamic_paths = _startup_dynamic_sparse_paths(repo)
    production_destination = temp_root / "production-checkout"
    production_checkout = (
        _isolated_checkout(
            repo,
            production_destination,
            extra_sparse_paths=startup_dynamic_paths,
        )
        if startup_dynamic_paths
        else _isolated_checkout(repo, production_destination)
    )
    _plant_production_shape(production_checkout)
    production = _run_production_cli(
        production_checkout,
        _runtime_environment(temp_root / "production-environment"),
    )
    audited_destination = temp_root / "audited-checkout"
    audited_checkout = (
        _isolated_checkout(
            repo,
            audited_destination,
            extra_sparse_paths=startup_dynamic_paths,
        )
        if startup_dynamic_paths
        else _isolated_checkout(repo, audited_destination)
    )
    _plant_production_shape(audited_checkout)
    direct = _run_direct_instrumentation(
        audited_checkout,
        _runtime_environment(temp_root / "direct-environment"),
    )
    audited = _run_audited_process(
        audited_checkout,
        _runtime_environment(temp_root / "audited-environment"),
        temp_root / "trace" / "runtime.strace",
    )
    sample = _combine_runtime_sample(production, direct, audited)
    sample["cold_checkout_paths"] = {
        "production": str(production_checkout),
        "audited": str(audited_checkout),
    }
    return sample


def _compact_failing_samples(
    rows: list[dict[str, Any]], *, startup_limit: int, total_limit: int
) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        reasons = [
            name
            for name, passed in row["runtime_acceptance"].items()
            if name != "pass" and passed is not True
        ]
        if row["startup"]["duration_ms"] > startup_limit:
            reasons.append("startup_duration")
        if row["total"]["duration_ms"] > total_limit:
            reasons.append("total_duration")
        counts = row["total"]["counts"]
        if counts["subprocess"] > SUBPROCESS_MAX_PER_RUN:
            reasons.append("subprocess_count")
        if counts["git"] > GIT_MAX_PER_RUN:
            reasons.append("git_count")
        if counts["opened_repo_paths"] > OPENED_REPO_PATHS_MAX_PER_RUN:
            reasons.append("opened_repo_paths")
        if not row["budgets"]["pass"]:
            reasons.append("output_budget")
        if row["snapshot_constructor_calls"] != 1:
            reasons.append("snapshot_constructor_count")
        if reasons:
            failures.append(
                {
                    "index": index,
                    "reasons": sorted(set(reasons)),
                    "startup_ms": row["startup"]["duration_ms"],
                    "total_ms": row["total"]["duration_ms"],
                    "counts": {
                        key: counts[key]
                        for key in ("subprocess", "git", "opened_repo_paths")
                    },
                    "functional_errors": {
                        name: audit["errors"]
                        for name, audit in row["functional_audits"].items()
                        if audit["errors"]
                    },
                    "forbidden_argv": row["forbidden_argv_audit"]["findings"][:8],
                    "payload_parity": row["payload_parity"],
                    "write_events": row["strace"]["write_events"][:32],
                    "trace_coverage": row["strace"]["trace_coverage"],
                }
            )
    return failures


_TOP_LEVEL_DECLARATION = re.compile(
    rb"(?m)^(?:@\[[^\n]*\]\s+)*"
    rb"(?:(?:private|protected|noncomputable|opaque|partial)\s+)*"
    rb"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|"
    rb"namespace|section|end)\b"
)
_LEAN_THEOREM_DECLARATION = re.compile(
    rb"(?m)^(?:@\[[^\n]*\]\s+)*"
    rb"(?:(?:private|protected|noncomputable)\s+)*"
    rb"(?:theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
    rb"(?![A-Za-z0-9_'])"
)


def _lean_namespace_at(source: bytes, offset: int) -> str:
    blocks: list[tuple[str, tuple[str, ...]]] = []
    for raw_line in source[:offset].splitlines():
        if raw_line[:1].isspace():
            continue
        line = raw_line.strip()
        namespace = re.fullmatch(rb"namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", line)
        if namespace is not None:
            token = namespace.group(1).decode("utf-8")
            components = tuple(part for part in token.split(".") if part)
            blocks.append(("namespace", components))
            continue
        if re.fullmatch(rb"section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?", line):
            blocks.append(("section", ()))
            continue
        if re.fullmatch(rb"end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?", line):
            if blocks:
                blocks.pop()
    components = [
        component
        for kind, namespace_components in blocks
        if kind == "namespace"
        for component in namespace_components
    ]
    return ".".join(components)


def _outer_proof_assignment_offset(block: bytes, *, absolute_start: int) -> int:
    round_depth = 0
    square_depth = 0
    brace_depth = 0
    block_comment_depth = 0
    in_string = False
    escaped = False
    index = 0
    while index < len(block):
        if block_comment_depth:
            if block.startswith(b"/-", index):
                block_comment_depth += 1
                index += 2
                continue
            if block.startswith(b"-/", index):
                block_comment_depth -= 1
                index += 2
                continue
            index += 1
            continue
        if in_string:
            current = block[index]
            if escaped:
                escaped = False
            elif current == ord("\\"):
                escaped = True
            elif current == ord('"'):
                in_string = False
            index += 1
            continue
        if block.startswith(b"--", index):
            newline = block.find(b"\n", index + 2)
            index = len(block) if newline < 0 else newline + 1
            continue
        if block.startswith(b"/-", index):
            block_comment_depth = 1
            index += 2
            continue
        current = block[index]
        if current == ord('"'):
            in_string = True
            index += 1
            continue
        if current == ord("("):
            round_depth += 1
        elif current == ord(")"):
            round_depth = max(0, round_depth - 1)
        elif current == ord("["):
            square_depth += 1
        elif current == ord("]"):
            square_depth = max(0, square_depth - 1)
        elif current == ord("{"):
            brace_depth += 1
        elif current == ord("}"):
            brace_depth = max(0, brace_depth - 1)
        elif (
            current == ord(":")
            and block.startswith(b":=", index)
            and round_depth == square_depth == brace_depth == 0
        ):
            assignment = re.match(rb":=\s+by\b", block[index:])
            if assignment is not None:
                return absolute_start + index
        index += 1
    raise RuntimeError("PROOF_BODY_PLANT_EXACT_ASSIGNMENT_NOT_FOUND")


def _proof_body_assignment_offset(source: bytes, theorem_id: str) -> int:
    leaf = theorem_id.rsplit(".", 1)[-1]
    if not leaf or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", leaf):
        raise RuntimeError("PROOF_BODY_PLANT_THEOREM_ID_INVALID")
    matches = []
    for declaration in _LEAN_THEOREM_DECLARATION.finditer(source):
        declared_name = declaration.group("name").decode("utf-8")
        namespace = _lean_namespace_at(source, declaration.start())
        resolved = (
            declared_name.removeprefix("_root_.")
            if declared_name.startswith("_root_.")
            else f"{namespace}.{declared_name}" if namespace else declared_name
        )
        if resolved == theorem_id and declared_name.rsplit(".", 1)[-1] == leaf:
            matches.append(declaration)
    if len(matches) != 1:
        raise RuntimeError(
            "PROOF_BODY_PLANT_EXACT_DECLARATION_COUNT:" + str(len(matches))
        )
    target = matches[0]
    next_declaration = _TOP_LEVEL_DECLARATION.search(source, target.end())
    target_end = next_declaration.start() if next_declaration is not None else len(source)
    return _outer_proof_assignment_offset(
        source[target.start() : target_end], absolute_start=target.start()
    )


def _proof_body_plant_bytes(source: bytes, theorem_id: str) -> bytes:
    assignment_offset = _proof_body_assignment_offset(source, theorem_id)
    insert_at = assignment_offset + len(b":= by")
    marker = b"\n  " + PROOF_BODY_PLANT_MARKER
    return source[:insert_at] + marker + source[insert_at:]


def _registered_proof_body_commit_plant(
    repo: Path, temp_root: Path
) -> dict[str, Any]:
    source_registry = workflow_runtime.node_registry_v10.load_registry(repo)
    source_candidates = [
        node
        for node in source_registry["nodes"]
        if node["semantic_review_inputs"]["exact_edges"]
    ]
    if not source_candidates:
        raise RuntimeError("PROOF_BODY_PLANT_REGISTERED_SUPPLIER_MISSING")
    source_node = sorted(source_candidates, key=lambda item: item["node_id"])[0]
    theorem_relative = source_node["source"]["path"]
    checkout = _isolated_checkout(
        repo,
        temp_root / "theorem-checkout",
        extra_sparse_paths=(
            *_startup_dynamic_sparse_paths(repo),
            theorem_relative,
        ),
    )
    registry_before = workflow_runtime.node_registry_v10.load_registry(checkout)
    candidates = [
        node
        for node in registry_before["nodes"]
        if node["semantic_review_inputs"]["exact_edges"]
    ]
    if not candidates:
        raise RuntimeError("PROOF_BODY_PLANT_REGISTERED_SUPPLIER_MISSING")
    node_before = sorted(candidates, key=lambda item: item["node_id"])[0]
    edge_id = sorted(node_before["semantic_review_inputs"]["exact_edges"])[0]
    edge = next(
        item for item in registry_before["edges"] if item["edge_id"] == edge_id
    )
    theorem_id = edge["theorem"]
    if theorem_id not in node_before["theorem_ids"]:
        raise RuntimeError("PROOF_BODY_PLANT_EDGE_THEOREM_NOT_REGISTERED")
    baseline_sample = _instrumented_once(
        checkout, registry_scope=node_before["node_id"]
    )
    theorem_relative = node_before["source"]["path"]
    theorem_path = checkout / theorem_relative
    base_head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=checkout,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    semantic_review_before = {
        "semantic_review_hash": node_before["semantic_review_hash"],
        "review": node_before["review"],
    }
    expected_source_sha256 = node_before["validation_inputs"]["source_bytes"][
        "sha256"
    ]
    source_before = theorem_path.read_bytes()
    assignment_offset = _proof_body_assignment_offset(source_before, theorem_id)
    planted_source = _proof_body_plant_bytes(source_before, theorem_id)
    theorem_path.write_bytes(planted_source)
    marker_offset = planted_source.index(PROOF_BODY_PLANT_MARKER)
    planted_source_sha256 = hashlib.sha256(planted_source).hexdigest()
    validation_invalidated = planted_source_sha256 != expected_source_sha256
    subprocess.run(
        ["git", "add", "--", theorem_relative],
        cwd=checkout,
        check=True,
        capture_output=True,
    )
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Control v10 Benchmark",
            "-c",
            "user.email=benchmark@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "temporary registered proof-only validation plant",
        ],
        cwd=checkout,
        check=True,
        capture_output=True,
    )
    plant_head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=checkout,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    changed_paths = subprocess.run(
        [
            "git",
            "diff-tree",
            "--no-commit-id",
            "--name-only",
            "-r",
            f"{plant_head}^",
            plant_head,
        ],
        cwd=checkout,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    exact_source_only_commit = changed_paths == [theorem_relative]
    before = _status_manifest(checkout)
    sample = _instrumented_once(checkout, registry_scope=node_before["node_id"])
    after = _status_manifest(checkout)
    registry_after = workflow_runtime.node_registry_v10.load_registry(checkout)
    node_after = next(
        node
        for node in registry_after["nodes"]
        if node["node_id"] == node_before["node_id"]
    )
    semantic_review_after = {
        "semantic_review_hash": node_after["semantic_review_hash"],
        "review": node_after["review"],
    }
    head_after = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=checkout,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    baseline_registry_pass = baseline_sample["result"]["node_registry_status"] == "PASS"
    startup_scope_only_pass = (
        sample["result"]["node_registry_status"] == "PASS"
        and sample["result"]["node_registry_code"]
        == "NODE_REGISTRY_STARTUP_SCOPE_PASS"
    )
    semantic_review_unchanged = semantic_review_before == semantic_review_after
    return {
        "theorem_path": theorem_relative,
        "theorem_id": theorem_id,
        "edge_id": edge_id,
        "node_id": node_before["node_id"],
        "before": before,
        "after": after,
        "status_manifest_unchanged": before == after,
        "no_tracked_or_untracked_derived_changes": before == after,
        "base_head": base_head,
        "plant_head": plant_head,
        "head_unchanged_during_shadow": plant_head == head_after,
        "plant_commit_created": plant_head != base_head,
        "plant_commit_changed_paths": changed_paths,
        "plant_commit_exact_source_only": exact_source_only_commit,
        "expected_source_sha256": expected_source_sha256,
        "planted_source_sha256": planted_source_sha256,
        "validation_invalidated": validation_invalidated,
        "proof_assignment_offset": assignment_offset,
        "proof_body_marker_offset": marker_offset,
        "proof_body_marker_after_assignment": (
            marker_offset > assignment_offset + len(b":= by")
        ),
        "validation_next_action": "DEEP_REPROBE_REQUIRED",
        "semantic_review_before": semantic_review_before,
        "semantic_review_after": semantic_review_after,
        "semantic_review_unchanged": semantic_review_unchanged,
        "plant_result": sample["result"],
        "startup_scope_only_pass": startup_scope_only_pass,
        "baseline_registry_pass": baseline_registry_pass,
        "output_budgets_pass": (
            baseline_sample["budgets"]["pass"] and sample["budgets"]["pass"]
        ),
        "pass": (
            before == after
            and plant_head != base_head
            and exact_source_only_commit
            and plant_head == head_after
            and baseline_registry_pass
            and validation_invalidated
            and marker_offset > assignment_offset + len(b":= by")
            and semantic_review_unchanged
            and startup_scope_only_pass
            and sample["result"]["run_authorized"] is False
            and baseline_sample["budgets"]["pass"]
            and sample["budgets"]["pass"]
        ),
    }


def benchmark(repo: Path, *, warm_runs: int, cold_runs: int) -> dict[str, Any]:
    if (warm_runs, cold_runs) != (DEFAULT_WARM_RUNS, DEFAULT_COLD_RUNS):
        raise ValueError("BENCHMARK_AUTHORITATIVE_MATRIX_REQUIRES_20_WARM_3_COLD")
    before = _status_manifest(repo)
    with tempfile.TemporaryDirectory(prefix="q3-control-v10-benchmark-") as tmp:
        temp_root = Path(tmp)
        candidate = _candidate_checkout(repo, temp_root / "phase-a-candidate")
        candidate_before = _status_manifest(candidate)
        environment_names = (
            "TMPDIR",
            "TMP",
            "TEMP",
            "XDG_CACHE_HOME",
            "PYTHONDONTWRITEBYTECODE",
            "GIT_OPTIONAL_LOCKS",
        )
        old_environment = {
            name: os.environ.get(name) for name in environment_names
        }
        try:
            runtime_environment = _runtime_environment(temp_root)
            for name in environment_names:
                os.environ[name] = runtime_environment[name]
            prime, warm = _warm_samples(
                candidate, temp_root / "warm", runs=warm_runs
            )
            cold = [
                _cold_once(candidate, temp_root / f"cold-{index}")
                for index in range(cold_runs)
            ]
            proof_body_plant = _registered_proof_body_commit_plant(
                candidate, temp_root
            )
        finally:
            for name, value in old_environment.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value
        candidate_after = _status_manifest(candidate)
    after = _status_manifest(repo)
    status_unchanged = before == after
    candidate_unchanged = candidate_before == candidate_after
    output_budgets_pass = all(
        row["budgets"]["pass"] for row in [*warm, *cold]
    )
    constructor_budget_pass = all(
        row["snapshot_constructor_calls"] == 1 for row in [*warm, *cold]
    )
    warm_startup_summary = _summary(warm, "startup")
    warm_post_startup_summary = _summary(warm, "plan")
    warm_total_summary = _summary(warm, "total")
    cold_startup_summary = _summary(cold, "startup")
    cold_post_startup_summary = _summary(cold, "plan")
    cold_total_summary = _summary(cold, "total")
    count_budgets_pass = all(
        row["operation_count_budget"]["pass"] for row in [*warm, *cold]
    )
    functional_plan_pass = all(
        row["runtime_acceptance"]["functional_plan_pass"]
        for row in [*warm, *cold]
    )
    exact_live_fatal_status_pass = all(
        row["runtime_acceptance"]["exact_live_fatal_status_pass"]
        for row in [*warm, *cold]
    )
    exact_live_fatal_set_pass = all(
        row["runtime_acceptance"]["exact_live_fatal_set_pass"]
        for row in [*warm, *cold]
    )
    startup_fatal_set_pass = all(
        row["runtime_acceptance"]["startup_fatal_set_pass"]
        for row in [*warm, *cold]
    )
    startup_honesty_state_pass = all(
        row["runtime_acceptance"]["startup_honesty_state_pass"]
        for row in [*warm, *cold]
    )
    exact_selector_pass = all(
        row["runtime_acceptance"]["exact_selector_pass"]
        for row in [*warm, *cold]
    )
    legacy_v9_authority_unchanged_pass = all(
        row["runtime_acceptance"]["legacy_v9_authority_unchanged_pass"]
        for row in [*warm, *cold]
    )
    px_rh_claim_not_made_pass = all(
        row["runtime_acceptance"]["px_rh_claim_not_made_pass"]
        for row in [*warm, *cold]
    )
    direct_production_tree_manifest_pass = (
        prime["write_audit"]["pass"] is True
        and all(
            row["runtime_acceptance"][
                "direct_production_tree_manifest_pass"
            ]
            for row in [*warm, *cold]
        )
    )
    full_payload_parity_pass = all(
        row["runtime_acceptance"]["full_payload_parity_pass"]
        for row in [*warm, *cold]
    )
    forbidden_argv_pass = all(
        row["runtime_acceptance"]["forbidden_argv_pass"]
        for row in [*warm, *cold]
    )
    write_free_pass = all(
        row["runtime_acceptance"]["write_free_pass"]
        for row in [*warm, *cold]
    )
    trace_coverage_pass = all(
        row["runtime_acceptance"]["trace_coverage_pass"]
        for row in [*warm, *cold]
    )
    assertions = {
        "output_budgets_pass": output_budgets_pass,
        "one_snapshot_per_plan_pass": constructor_budget_pass,
        "functional_plan_exact_contract_pass": functional_plan_pass,
        "exact_live_fatal_status_pass": exact_live_fatal_status_pass,
        "exact_live_fatal_set_pass": exact_live_fatal_set_pass,
        "startup_fatal_set_pass": startup_fatal_set_pass,
        "startup_honesty_state_pass": startup_honesty_state_pass,
        "exact_goal_058_selector_pass": exact_selector_pass,
        "legacy_v9_authority_unchanged_pass": (
            legacy_v9_authority_unchanged_pass
        ),
        "px_rh_claim_not_made_pass": px_rh_claim_not_made_pass,
        "direct_production_tree_manifest_pass": (
            direct_production_tree_manifest_pass
        ),
        "full_normalized_payload_parity_pass": full_payload_parity_pass,
        "forbidden_runtime_argv_pass": forbidden_argv_pass,
        "linux_strace_write_free_pass": write_free_pass,
        "linux_strace_trace_coverage_pass": trace_coverage_pass,
        "warm_startup_p95_pass": (
            warm_startup_summary["duration_ms"]["p95"] <= WARM_STARTUP_P95_MS
        ),
        "warm_full_plan_p95_pass": (
            warm_total_summary["duration_ms"]["p95"] <= WARM_FULL_P95_MS
        ),
        "cold_startup_each_pass": all(
            row["startup"]["duration_ms"] <= COLD_STARTUP_MAX_MS for row in cold
        ),
        "cold_full_plan_each_pass": all(
            row["total"]["duration_ms"] <= COLD_FULL_MAX_MS for row in cold
        ),
        "direct_runtime_operation_count_budgets_pass": count_budgets_pass,
        "source_status_manifest_unchanged": status_unchanged,
        "candidate_status_manifest_unchanged": candidate_unchanged,
        "registered_proof_body_no_derived_changes_pass": proof_body_plant[
            "pass"
        ],
    }
    assertions["all_pass"] = all(assertions.values())
    return {
        "schema": "q3_control_v10_benchmark.v1",
        "mode": "READ_ONLY_SHADOW_EXACT_PHASE_A_CANDIDATE_COMMIT",
        "configuration": {
            "warm_runs": warm_runs,
            "cold_runs": cold_runs,
            "candidate_paths": list(PHASE_A_CANDIDATE_PATHS),
            "candidate_head": candidate_before["head"],
        },
        "budgets": {
            "warm_startup_p95_ms": WARM_STARTUP_P95_MS,
            "warm_full_plan_p95_ms": WARM_FULL_P95_MS,
            "cold_startup_each_ms": COLD_STARTUP_MAX_MS,
            "cold_full_plan_each_ms": COLD_FULL_MAX_MS,
            "subprocess_per_run": SUBPROCESS_MAX_PER_RUN,
            "git_per_run": GIT_MAX_PER_RUN,
            "opened_repo_paths_per_run": OPENED_REPO_PATHS_MAX_PER_RUN,
            "duration_measurement": (
                "FRESH_PRODUCTION_CLI_WALL_FOR_WARM_AND_COLD"
            ),
            "count_measurement": (
                "LINUX_STRACE_FULL_PROCESS_TREE_SUBPROCESS_GIT_AND_"
                "UNIQUE_REPO_OPENS"
            ),
            "os_wide_count_acceptance": "LINUX_STRACE_F_Y_Y_REQUIRED_FAIL_CLOSED",
        },
        "warm": {
            "prime_production": {
                "command": prime["production"]["command"],
                "returncode": prime["production"]["returncode"],
                "duration_ms": prime["production"]["duration_ms"],
                "write_audit": prime["write_audit"],
            },
            "startup_summary": warm_startup_summary,
            "post_startup_summary": warm_post_startup_summary,
            "total_summary": warm_total_summary,
            "sample_count": len(warm),
            "counts_by_run": [row["total"]["counts"] for row in warm],
            "direct_runtime_subprocess_argv_by_run": [
                row["direct_runtime_subprocess_argv"] for row in warm
            ],
            "descendant_process_counts_by_run": [
                {
                    "subprocess": row["descendant_process_diagnostics"][
                        "subprocess_count"
                    ],
                    "git": row["descendant_process_diagnostics"]["git_count"],
                }
                for row in warm
            ],
            "runtime_subprocess_argv_by_run": [
                row["runtime_subprocess_argv"] for row in warm
            ],
            "payload_parity_by_run": [row["payload_parity"] for row in warm],
            "write_free_by_run": [
                row["runtime_acceptance"]["write_free_pass"] for row in warm
            ],
            "trace_coverage_by_run": [
                row["runtime_acceptance"]["trace_coverage_pass"] for row in warm
            ],
            "failing_samples": _compact_failing_samples(
                warm,
                startup_limit=WARM_STARTUP_P95_MS,
                total_limit=WARM_FULL_P95_MS,
            ),
        },
        "cold": {
            "isolation": "FRESH_LOCAL_SHARED_CLONE_AND_TEMP_ENV_PER_RUN",
            "startup_summary": cold_startup_summary,
            "post_startup_summary": cold_post_startup_summary,
            "total_summary": cold_total_summary,
            "sample_count": len(cold),
            "counts_by_run": [row["total"]["counts"] for row in cold],
            "direct_runtime_subprocess_argv_by_run": [
                row["direct_runtime_subprocess_argv"] for row in cold
            ],
            "descendant_process_counts_by_run": [
                {
                    "subprocess": row["descendant_process_diagnostics"][
                        "subprocess_count"
                    ],
                    "git": row["descendant_process_diagnostics"]["git_count"],
                }
                for row in cold
            ],
            "runtime_subprocess_argv_by_run": [
                row["runtime_subprocess_argv"] for row in cold
            ],
            "payload_parity_by_run": [row["payload_parity"] for row in cold],
            "write_free_by_run": [
                row["runtime_acceptance"]["write_free_pass"] for row in cold
            ],
            "trace_coverage_by_run": [
                row["runtime_acceptance"]["trace_coverage_pass"] for row in cold
            ],
            "failing_samples": _compact_failing_samples(
                cold,
                startup_limit=COLD_STARTUP_MAX_MS,
                total_limit=COLD_FULL_MAX_MS,
            ),
        },
        "source_status_manifest": {"before": before, "after": after},
        "candidate_status_manifest": {
            "before": candidate_before,
            "after": candidate_after,
        },
        "registered_proof_body_commit_plant": proof_body_plant,
        "budget_assertions": assertions,
        "network_used": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--warm-runs", type=int, default=DEFAULT_WARM_RUNS)
    parser.add_argument("--cold-runs", type=int, default=DEFAULT_COLD_RUNS)
    parser.add_argument("--single", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    repo = args.root.resolve()
    os.environ["GIT_OPTIONAL_LOCKS"] = "0"
    if args.single:
        with tempfile.TemporaryDirectory(
            prefix="q3-control-v10-smoke-"
        ) as tmp:
            candidate = _candidate_checkout(repo, Path(tmp) / "candidate")
            result = _instrumented_once(candidate)
    else:
        result = benchmark(
            repo, warm_runs=args.warm_runs, cold_runs=args.cold_runs
        )
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    if args.single:
        single_pass = (
            result["functional_audit"]["pass"]
            and result["forbidden_argv_audit"]["pass"]
            and result["budgets"]["pass"]
            and result["snapshot_constructor_calls"] == 1
        )
        return 0 if single_pass else 2
    return 0 if result["budget_assertions"]["all_pass"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
