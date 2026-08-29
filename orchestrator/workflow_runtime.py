#!/usr/bin/env python3
"""Stateless front door for the existing Q3 goal lifecycle.

This module compiles the authoritative selector, tool manifest, derived-artifact
registry, and close helpers into one deterministic plan.  Its run command then
executes the registered, explicitly scoped transition and emits receipts.  It
owns no durable runtime state and never commits, pushes, publishes externally,
promotes, or makes an RH claim.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
import subprocess
import sys
import time
from dataclasses import asdict
from pathlib import Path
from typing import Any

import yaml

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import dependency_registry  # noqa: E402
from specs_docs import phase_close, session_close  # noqa: E402

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

COMMON_TOOLS = (
    "workflow-runtime",
    "codex-session-start",
    "goal-run-selector",
    "ask-shelf",
    "kb-query",
)
ACTION_TOOLS = {
    "SELECT_EXACT_GOAL": (
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


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True, text=True
    ).stdout.strip()


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


def startup_receipt(repo: Path) -> dict[str, Any]:
    return command_receipt(repo, ["bash", "specs_docs/session_start.sh"], label="session-start")


def goal_assembly_chain(goal_path: str | None) -> str | None:
    if not goal_path:
        return None
    path = Path(goal_path)
    if not path.is_file():
        return None
    match = re.search(r"^ASSEMBLY_CHAIN:\s*([^\s]+)\s*$", path.read_text(encoding="utf-8"), re.MULTILINE)
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
) -> dict[str, Any]:
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
            "calls_performed": 0,
            "eligible_class": (
                "DELEGATED_STRATEGIC_REVIEW"
                if action == "PHASE_TRANSITION_REQUIRED" else None
            ),
            "transport_owner": "CODEX_LINUX_ONLY",
        },
        "commit_push_performed": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }
    unique_holds = sorted(set(item for item in holds if item))
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
    binding, selector_hold = selector_binding(
        repo,
        next_goal_spec=next_goal_spec,
        current_phase_key=current_phase_key,
    )
    statuses = dependency_registry.statuses(repo, repo / REGISTRY, consumer="workflow-plan")
    owned, foreign = session_close.dirty_split(repo, owned_paths)
    host = {"Darwin": "CODEX_MAC", "Linux": "CODEX_LINUX"}.get(platform.system(), "UNSUPPORTED_HOST")
    startup = startup_receipt(repo)
    return compile_plan(
        goal_binding=binding,
        selector_hold=selector_hold,
        tool_index=load_tool_index(repo / TOOLS),
        derived_status=[asdict(item) for item in statuses],
        assembly_debt=phase_close.assembly_debt(
            (repo / phase_close.DEFAULT_DB.relative_to(REPO)).resolve(),
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
            *(str(output) for row in dependency_registry.load_registry(repo / REGISTRY)
              if dependency_registry.applies_to(row, "session-close")
              for output in row["outputs"]),
        ],
        startup=startup,
    )


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
) -> dict[str, Any]:
    receipts: list[dict[str, Any]] = []
    startup = plan.get("logical_plan", {}).get("startup_receipt") or startup_receipt(repo)
    receipts.append(startup)
    holds = list(plan.get("holds", []))
    if startup["exit"] != 0:
        holds.append(f"START_GATE_FAILED:{startup['exit']}")
    if not owned_paths:
        holds.append("OWNED_SCOPE_REQUIRED")
    if attempt_payload is None:
        holds.append("GOAL_ATTEMPT_EVENT_REQUIRED")
    if any(not _exists_at_head(repo, path) for path in owned_paths) and not query:
        holds.append("ASK_SHELF_REQUIRED_FOR_NEW_OBJECT")
    if candidate or target:
        if not (query and candidate and target):
            holds.append("SUPPLIER_PREFLIGHT_TRIPLE_REQUIRED")
    if holds:
        return {
            "schema": "q3_workflow_run.v1",
            "status": "HOLD",
            "holds": sorted(set(holds)),
            "plan": plan,
            "receipts": receipts,
            "commit_push_performed": False,
            "PX_RH_CLAIM": "NOT_MADE",
        }
    before = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
    if query:
        receipts.append(command_receipt(repo, ["bash", "ask.sh", query], label="ask-shelf"))
        command = [sys.executable, "scripts/supplier_preflight.py", "--query", query]
        if candidate and target:
            command.extend(("--candidate", candidate, "--target", target))
        receipts.append(command_receipt(repo, command, label="supplier-preflight"))
    if run_kernel:
        for path in owned_paths:
            if path.endswith(".lean") and path.startswith("q3.lean.aristotle/"):
                receipts.append(command_receipt(repo, ["bash", "scripts/q3_check.sh", path], label=f"kernel:{path}"))
    elif any(path.endswith(".lean") for path in owned_paths):
        holds.append("KERNEL_GATE_REQUIRED")
    if any(item["exit"] != 0 for item in receipts):
        holds.append("PRE_CLOSE_GATE_FAILED")
    if not holds:
        command = [sys.executable, "orchestrator/spine.py", "--refresh", "--reason", "step-close",
                   "--attempt-payload", str(attempt_payload)]
        if insight_payload:
            command.extend(("--insight-payload", str(insight_payload)))
        receipts.append(command_receipt(repo, command, label="step-close"))
    if not holds and receipts[-1]["exit"] == 0:
        command = [sys.executable, "specs_docs/session_close.py", "--root", str(repo), "--repair"]
        for path in owned_paths:
            command.extend(("--owned-path", path))
        if run_kernel:
            command.append("--run-kernel")
        if protocol_out:
            command.extend(("--protocol-out", str(protocol_out)))
        receipts.append(command_receipt(repo, command, label="session-close"))
    failed = [item for item in receipts if item["exit"] != 0]
    after = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
    return {
        "schema": "q3_workflow_run.v1",
        "status": "HOLD" if failed or holds else "CLOSED_NODE",
        "holds": sorted(set([*holds, *(f"COMMAND_FAILED:{item['label']}:{item['exit']}" for item in failed)])),
        "plan": plan,
        "receipts": receipts,
        "changed_paths_before": before.splitlines(),
        "changed_paths_after": after.splitlines(),
        "commit_push_performed": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }


def _add_plan_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--next-goal-spec", type=Path)
    parser.add_argument("--current-phase-key", type=Path)
    parser.add_argument("--owned-path", action="append", default=[])


def _run_close_script(repo: Path, script: str, forwarded: list[str]) -> int:
    return subprocess.run([sys.executable, str(repo / script), "--root", str(repo), *forwarded], cwd=repo).returncode


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=REPO)
    subparsers = parser.add_subparsers(dest="command", required=True)
    plan_parser = subparsers.add_parser("plan")
    _add_plan_options(plan_parser)
    run_parser = subparsers.add_parser("run")
    run_parser.add_argument("--through", choices=["close-node"], required=True)
    _add_plan_options(run_parser)
    run_parser.add_argument("--query")
    run_parser.add_argument("--candidate")
    run_parser.add_argument("--target")
    run_parser.add_argument("--attempt-payload", type=Path)
    run_parser.add_argument("--insight-payload", type=Path)
    run_parser.add_argument("--run-kernel", action="store_true")
    run_parser.add_argument("--protocol-out", type=Path)
    subparsers.add_parser("close-session")
    subparsers.add_parser("close-phase")
    args, forwarded = parser.parse_known_args()
    repo = args.root.resolve()
    if args.command == "close-session":
        return _run_close_script(repo, "specs_docs/session_close.py", forwarded)
    if args.command == "close-phase":
        return _run_close_script(repo, "specs_docs/phase_close.py", forwarded)
    if forwarded:
        parser.error("unrecognized arguments: " + " ".join(forwarded))
    through = "close-node" if args.command == "run" else "plan"
    try:
        plan = live_plan(
            repo,
            next_goal_spec=args.next_goal_spec,
            current_phase_key=args.current_phase_key,
            owned_paths=args.owned_path,
            through=through,
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
            )
            if args.command == "run" else plan
        )
    except (WorkflowRuntimeError, dependency_registry.DependencyRegistryError, subprocess.CalledProcessError) as exc:
        result = {"schema": "q3_workflow_plan.v1", "status": "HOLD", "holds": [str(exc)]}
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    return 0 if result.get("status") in {"READY", "CLOSED_NODE"} else 2


if __name__ == "__main__":
    raise SystemExit(main())
