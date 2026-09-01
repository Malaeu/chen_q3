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
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from contextlib import ExitStack
from pathlib import Path
from typing import Any, Callable, TypeVar
from unittest import mock

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import workflow_runtime  # noqa: E402

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
PHASE_A_CANDIDATE_PATHS = (
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
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json",
)


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
            snapshot = original_builder(*args, **kwargs)
            startup_capture.update(checkpoint())
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
    return {
        "startup": startup_metrics,
        "plan": plan_metrics,
        "total": {
            "duration_ms": total_metrics["duration_ms"],
            "counts": total_metrics["counts"],
        },
        "result": {
            "schema": plan.get("schema"),
            "status": plan.get("status"),
            "run_authorized": plan.get("run_authorized"),
            "selected_goal": plan.get("selected_goal"),
            "holds": plan.get("holds"),
            "blocked_features": plan.get("blocked_features"),
            "node_registry_status": plan.get("node_registry", {}).get("status"),
            "node_registry_code": plan.get("node_registry", {}).get("code"),
        },
        "budgets": budgets,
        "snapshot_constructor_calls": snapshot_constructor_calls,
        "measurement": {
            "duration": "PRODUCTION_LIVE_SHADOW_PLAN_IN_PROCESS_INCLUDES_RENDER",
            "counts": "VERIFIED_DIRECT_RUNTIME_COUNTS_NOT_OS_WIDE",
            "counts_scope": (
                "subprocess.run plus builtins.open io.open os.open os.scandir and Path APIs; "
                "child-process internal syscalls excluded"
            ),
        },
    }


def _status_manifest(repo: Path) -> dict[str, Any]:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    origin = subprocess.run(
        ["git", "rev-parse", "origin/rh_clean"],
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    origin_head = origin.stdout.strip() if origin.returncode == 0 else None
    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        cwd=repo,
        check=True,
        capture_output=True,
    )
    tracked_diff = subprocess.run(
        ["git", "diff", "--binary", "HEAD", "--"],
        cwd=repo,
        check=True,
        capture_output=True,
    ).stdout
    staged_diff = subprocess.run(
        ["git", "diff", "--cached", "--binary", "HEAD", "--"],
        cwd=repo,
        check=True,
        capture_output=True,
    ).stdout
    untracked_raw = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "-z"],
        cwd=repo,
        check=True,
        capture_output=True,
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


def _isolated_checkout(repo: Path, destination: Path) -> Path:
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
            "/docs/CODEX_CONTROL.md",
            "/docs/Codex/CURRENT.md",
            "/docs/cartographer/",
            "/docs/routeB_bus/",
            "/orchestrator/",
            "/scripts/",
            "/specs_docs/",
            (
                "/q3.lean.aristotle/ACTIVE/requests/"
                "routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
            ),
            "/q3.lean.aristotle/Q3/Benchmarks/",
            "/q3.lean.aristotle/Q3/Proofs/RouteB/",
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
        for relative in COLD_REQUIRED_PATHS
        if not (destination / relative).is_file()
    ]
    if missing:
        raise RuntimeError("COLD_CHECKOUT_REQUIRED_PATH_MISSING:" + ",".join(missing))
    if not any((destination / "docs/routeB_bus").glob("*.goal.md")):
        raise RuntimeError("COLD_CHECKOUT_PHYSICAL_GOAL_SURFACE_MISSING")
    return destination


def _candidate_checkout(repo: Path, destination: Path) -> Path:
    checkout = _isolated_checkout(repo, destination)
    missing = [relative for relative in PHASE_A_CANDIDATE_PATHS if not (repo / relative).is_file()]
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
    return checkout


def _cold_once(repo: Path, temp_root: Path) -> dict[str, Any]:
    temp_root.mkdir(parents=True, exist_ok=True)
    checkout = _isolated_checkout(repo, temp_root / "checkout")
    environment = os.environ.copy()
    environment.update(
        {
            "TMPDIR": str(temp_root),
            "TMP": str(temp_root),
            "TEMP": str(temp_root),
            "XDG_CACHE_HOME": str(temp_root / "cache"),
            "PYTHONDONTWRITEBYTECODE": "1",
        }
    )
    started = time.perf_counter()
    proc = subprocess.run(
        [
            sys.executable,
            str(checkout / "orchestrator/benchmarks/control_v10_benchmark.py"),
            "--root",
            str(checkout),
            "--single",
        ],
        cwd=checkout,
        check=False,
        capture_output=True,
        text=True,
        env=environment,
    )
    if proc.returncode:
        raise RuntimeError(f"COLD_SHADOW_FAILED:{proc.stderr.strip()}")
    instrumented_process_wall_ms = round((time.perf_counter() - started) * 1000, 3)
    sample = json.loads(proc.stdout)
    cli_started = time.perf_counter()
    cli = subprocess.run(
        [
            sys.executable,
            str(checkout / "orchestrator/workflow_runtime.py"),
            "--root",
            str(checkout),
            "plan",
            "--shadow-v10",
        ],
        cwd=checkout,
        check=False,
        capture_output=True,
        text=True,
        env=environment,
    )
    cli_wall_ms = round((time.perf_counter() - cli_started) * 1000, 3)
    if cli.returncode not in {0, 2}:
        raise RuntimeError(f"COLD_PRODUCTION_CLI_FAILED:{cli.stderr.strip()}")
    try:
        cli_plan = json.loads(cli.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError("COLD_PRODUCTION_CLI_OUTPUT_INVALID") from exc
    expected = sample["result"]
    cli_matches = (
        cli_plan.get("schema") == expected["schema"]
        and cli_plan.get("status") == expected["status"]
        and cli_plan.get("selected_goal") == expected["selected_goal"]
        and cli_plan.get("run_authorized") is False
    )
    # Treat the complete production CLI wall time as the cold-start duration.
    # This is conservative: imports, startup, registry summary, rendering, and
    # argument parsing are all charged to both the startup and full-plan caps.
    sample["startup"]["duration_ms"] = cli_wall_ms
    sample["total"]["duration_ms"] = cli_wall_ms
    sample["instrumented_process_wall_ms"] = instrumented_process_wall_ms
    sample["production_cli"] = {
        "command": ["workflow_runtime.py", "--root", str(checkout), "plan", "--shadow-v10"],
        "returncode": cli.returncode,
        "duration_ms": cli_wall_ms,
        "result_matches_instrumented_runtime": cli_matches,
    }
    sample["measurement"]["duration"] = (
        "FRESH_PRODUCTION_CLI_WALL_INCLUDES_IMPORTS_STARTUP_COMPILE_AND_RENDER"
    )
    return sample


def _registered_source_byte_commit_plant(
    repo: Path, temp_root: Path
) -> dict[str, Any]:
    checkout = _isolated_checkout(repo, temp_root / "theorem-checkout")
    registry_before = workflow_runtime.node_registry_v10.load_registry(checkout)
    candidates = [
        node
        for node in registry_before["nodes"]
        if node["semantic_review_inputs"]["exact_edges"]
    ]
    if not candidates:
        raise RuntimeError("THEOREM_ONLY_PLANT_REGISTERED_SUPPLIER_MISSING")
    node_before = sorted(candidates, key=lambda item: item["node_id"])[0]
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
    with theorem_path.open("ab") as stream:
        stream.write(b"\n-- CONTROL_V10_PROOF_ONLY_VALIDATION_PLANT\n")
    planted_source_sha256 = hashlib.sha256(theorem_path.read_bytes()).hexdigest()
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
        node for node in registry_after["nodes"] if node["node_id"] == node_before["node_id"]
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
            and semantic_review_unchanged
            and startup_scope_only_pass
            and sample["result"]["run_authorized"] is False
            and baseline_sample["budgets"]["pass"]
            and sample["budgets"]["pass"]
        ),
    }


def benchmark(repo: Path, *, warm_runs: int, cold_runs: int) -> dict[str, Any]:
    if warm_runs <= 0 or cold_runs <= 0:
        raise ValueError("warm_runs and cold_runs must be positive")
    before = _status_manifest(repo)
    with tempfile.TemporaryDirectory(prefix="q3-control-v10-benchmark-") as tmp:
        temp_root = Path(tmp)
        candidate = _candidate_checkout(repo, temp_root / "phase-a-candidate")
        candidate_before = _status_manifest(candidate)
        old_temp = {name: os.environ.get(name) for name in ("TMPDIR", "TMP", "TEMP")}
        try:
            for name in old_temp:
                os.environ[name] = str(temp_root)
            warm = [_instrumented_once(candidate) for _ in range(warm_runs)]
        finally:
            for name, value in old_temp.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value
        cold = [
            _cold_once(candidate, temp_root / f"cold-{index}")
            for index in range(cold_runs)
        ]
        source_byte_plant = _registered_source_byte_commit_plant(candidate, temp_root)
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
        row["total"]["counts"]["subprocess"] <= SUBPROCESS_MAX_PER_RUN
        and row["total"]["counts"]["git"] <= GIT_MAX_PER_RUN
        and row["total"]["counts"]["opened_repo_paths"]
        <= OPENED_REPO_PATHS_MAX_PER_RUN
        for row in [*warm, *cold]
    )
    assertions = {
        "output_budgets_pass": output_budgets_pass,
        "one_snapshot_per_plan_pass": constructor_budget_pass,
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
        "cold_production_cli_pass": all(
            row["production_cli"]["result_matches_instrumented_runtime"]
            for row in cold
        ),
        "direct_runtime_operation_count_budgets_pass": count_budgets_pass,
        "source_status_manifest_unchanged": status_unchanged,
        "candidate_status_manifest_unchanged": candidate_unchanged,
        "registered_source_byte_no_derived_changes_pass": source_byte_plant[
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
                "WARM_IN_PROCESS_INSTRUMENTED; COLD_FRESH_PROCESS_WALL_INCLUDES_IMPORTS_AND_CLI"
            ),
            "count_measurement": (
                "VERIFIED_DIRECT_RUNTIME_COUNTS_NOT_OS_WIDE; child-process internal "
                "syscalls excluded"
            ),
            "os_wide_count_acceptance": "NOT_CLAIMED_PORTABLE_SYSCALL_TRACE_UNAVAILABLE",
        },
        "warm": {
            "startup_summary": warm_startup_summary,
            "post_startup_summary": warm_post_startup_summary,
            "total_summary": warm_total_summary,
            "samples": warm,
        },
        "cold": {
            "isolation": "FRESH_LOCAL_SHARED_CLONE_AND_TEMP_ENV_PER_RUN",
            "startup_summary": cold_startup_summary,
            "post_startup_summary": cold_post_startup_summary,
            "total_summary": cold_total_summary,
            "samples": cold,
        },
        "source_status_manifest": {"before": before, "after": after},
        "candidate_status_manifest": {
            "before": candidate_before,
            "after": candidate_after,
        },
        "registered_source_byte_commit_plant": source_byte_plant,
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
    result = (
        _instrumented_once(repo)
        if args.single
        else benchmark(repo, warm_runs=args.warm_runs, cold_runs=args.cold_runs)
    )
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    if args.single:
        return 0
    return 0 if result["budget_assertions"]["all_pass"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
