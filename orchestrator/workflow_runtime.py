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

from orchestrator import (  # noqa: E402
    dependency_registry,
    proof_loop,
    research_dependency_contract,
    roof_port_ledger,
    session_briefing,
    spine,
)
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


def _single_request_header(text: str, field: str) -> tuple[str | None, str | None]:
    matches = re.findall(rf"(?m)^{re.escape(field)}:\s*(\S+)\s*$", text)
    if not matches:
        return None, f"PROSHKA_{field}_MISSING"
    if len(matches) != 1:
        return None, f"PROSHKA_{field}_AMBIGUOUS"
    return matches[0], None


def _exploration_review_receipt(runtime: dict[str, Any]) -> dict[str, Any]:
    """Validate and summarize the canonical bounded-exploration call gate."""
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
) -> dict[str, Any]:
    resolved = path if path.is_absolute() else repo / path
    try:
        raw = resolved.read_bytes()
        payload = json.loads(raw.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise WorkflowRuntimeError(
            f"CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:{exc}"
        ) from exc
    if not isinstance(payload, dict) or set(payload) != {
        "schema", "candidate", "target", "contract"
    }:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:SCHEMA")
    if payload.get("schema") != DEPENDENCY_CONTRACT_RECEIPT_SCHEMA:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:SCHEMA")
    if payload.get("candidate") != candidate:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_CANDIDATE_MISMATCH")
    if payload.get("target") != target:
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_TARGET_MISMATCH")
    contract = payload.get("contract")
    if not isinstance(contract, dict):
        raise WorkflowRuntimeError("CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:CONTRACT")
    try:
        research_dependency_contract.validate(contract)
    except research_dependency_contract.DependencyContractError as exc:
        raise WorkflowRuntimeError(
            f"CONSUMER_FIRST_CONTRACT_RECEIPT_INVALID:{exc}"
        ) from exc
    return {
        "label": "consumer-first-contract",
        "schema": DEPENDENCY_CONTRACT_RECEIPT_SCHEMA,
        "path": str(resolved),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "candidate": candidate,
        "target": target,
        "status": "VALID",
    }


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True, text=True
    ).stdout.strip()


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
    assembly_snapshot: dict[str, Any] | None = None,
    roof_ledger_snapshot: dict[str, Any] | None = None,
    route: dict[str, Any] | None = None,
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
    binding, selector_hold = selector_binding(
        repo,
        next_goal_spec=next_goal_spec,
        current_phase_key=current_phase_key,
    )
    statuses = dependency_registry.statuses(repo, repo / REGISTRY, consumer="workflow-plan")
    owned, foreign = session_close.dirty_split(repo, owned_paths)
    host = {"Darwin": "CODEX_MAC", "Linux": "CODEX_LINUX"}.get(platform.system(), "UNSUPPORTED_HOST")
    route = session_briefing.snapshot(repo)["route"]
    startup = startup_receipt(repo)
    selected_goal = binding.get("selected_goal_path") or route.get("selected_goal_path")
    selected_goal_path = Path(selected_goal) if isinstance(selected_goal, str) else None
    if selected_goal_path is not None and not selected_goal_path.is_absolute():
        selected_goal_path = repo / selected_goal_path
    chain = proof_loop.goal_assembly_chain(selected_goal_path)
    assembly = proof_loop.assembly_snapshot(
        (repo / phase_close.DEFAULT_DB.relative_to(REPO)).resolve(),
        chain=chain,
    )
    roof_ledger_snapshot = roof_port_ledger.build(
        repo,
        (repo / phase_close.DEFAULT_DB.relative_to(REPO)).resolve(),
    )
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
        assembly_snapshot=assembly,
        roof_ledger_snapshot=roof_ledger_snapshot,
        route=route,
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
    dependency_contract_receipt: Path | None = None,
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
        if dependency_contract_receipt is None:
            holds.append("CONSUMER_FIRST_CONTRACT_RECEIPT_REQUIRED")
        elif candidate and target:
            try:
                receipts.append(_dependency_contract_receipt(
                    repo,
                    dependency_contract_receipt,
                    candidate=candidate,
                    target=target,
                ))
            except WorkflowRuntimeError as exc:
                holds.append(str(exc))
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
    if any(item.get("exit", 0) != 0 for item in receipts):
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
    failed = [item for item in receipts if item.get("exit", 0) != 0]
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
    run_parser.add_argument("--dependency-contract-receipt", type=Path)
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
                dependency_contract_receipt=args.dependency_contract_receipt,
            )
            if args.command == "run" else plan
        )
    except (WorkflowRuntimeError, dependency_registry.DependencyRegistryError, subprocess.CalledProcessError) as exc:
        result = {"schema": "q3_workflow_plan.v1", "status": "HOLD", "holds": [str(exc)]}
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    return 0 if result.get("status") in {"READY", "CLOSED_NODE"} else 2


if __name__ == "__main__":
    raise SystemExit(main())
