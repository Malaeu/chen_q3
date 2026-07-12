#!/usr/bin/env python3
"""Read-only Route B execution-state and physical-bus consistency check."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
BUS_DIR = REQUEST_DIR / "bus"
STATE_PATH = REQUEST_DIR / "ROUTE_B_EXECUTION_STATE.json"
LOOP_PATH = REQUEST_DIR / "loop_state.json"
MASTER_STATE_PATH = REQUEST_DIR.parent / "routeB_lamport_rh_closure" / "STATE.json"
NAME_RE = re.compile(r"^(\d{3})_([a-z0-9_]+)\.(goal|answer)\.md$")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_answer_sha256(path: Path) -> str:
    """Hash an answer while omitting explicitly self-referential hash lines."""
    digest = hashlib.sha256()
    for line in path.read_bytes().splitlines(keepends=True):
        if b"HASH-OMIT" not in line:
            digest.update(line)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"top-level JSON must be an object: {path}")
    return data


def scan_bus() -> dict[str, Any]:
    entries: dict[str, dict[str, list[Path]]] = {}
    errors: list[str] = []

    for path in sorted(BUS_DIR.iterdir()):
        if path.name == "BUS_PROTOCOL.md" or not path.is_file():
            continue
        if not (path.name.endswith(".goal.md") or path.name.endswith(".answer.md")):
            continue
        match = NAME_RE.fullmatch(path.name)
        if match is None:
            errors.append(f"BUS_NAMING_ERROR:{path.name}")
            continue
        nnn, stem, kind = match.groups()
        by_stem = entries.setdefault(nnn, {}).setdefault(stem, [])
        by_stem.append(path)

    goals: dict[str, Path] = {}
    answers: dict[str, Path] = {}
    for nnn, stems in sorted(entries.items()):
        if len(stems) != 1:
            errors.append(f"BUS_DUPLICATE_NNN:{nnn}:{','.join(sorted(stems))}")
            continue
        stem, paths = next(iter(stems.items()))
        for path in paths:
            kind = NAME_RE.fullmatch(path.name).group(3)  # type: ignore[union-attr]
            target = goals if kind == "goal" else answers
            if nnn in target:
                errors.append(f"BUS_DUPLICATE_{kind.upper()}:{nnn}")
            target[nnn] = path
        if nnn in answers and nnn not in goals:
            errors.append(f"BUS_ORPHAN_ANSWER:{nnn}_{stem}")

    goal_numbers = sorted(int(nnn) for nnn in goals)
    if goal_numbers:
        expected = list(range(1, max(goal_numbers) + 1))
        if goal_numbers != expected:
            errors.append("BUS_GOAL_NUMBER_GAP")

    for nnn, answer in sorted(answers.items()):
        text = answer.read_text(encoding="utf-8")
        if "MYTHOS_PROSHKA_HANDOFF" not in text:
            errors.append(f"ANSWER_HANDOFF_MISSING:{nnn}")
        if "ACTIONS LOG" not in text:
            errors.append(f"ANSWER_ACTIONS_LOG_MISSING:{nnn}")

    closed = sorted(nnn for nnn in goals if nnn in answers)
    unanswered = sorted(nnn for nnn in goals if nnn not in answers)
    last_closed = closed[-1] if closed else None
    next_expected = f"{(max(goal_numbers) + 1) if goal_numbers else 1:03d}"
    return {
        "goals": goals,
        "answers": answers,
        "closed": closed,
        "unanswered": unanswered,
        "last_closed": last_closed,
        "lowest_unanswered": unanswered[0] if unanswered else None,
        "next_expected": next_expected,
        "errors": errors,
    }


def relpath(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate hard invariants")
    parser.add_argument("--json", action="store_true", help="emit machine-readable result")
    args = parser.parse_args()

    bus = scan_bus()
    bus_errors = list(bus["errors"])
    state_errors: list[str] = []
    pin_errors: list[str] = []

    try:
        state = load_json(STATE_PATH)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        state = {}
        state_errors.append(f"EXECUTION_STATE_INVALID:{exc}")

    try:
        loop = load_json(LOOP_PATH)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        loop = {}
        state_errors.append(f"LOOP_STATE_INVALID:{exc}")

    try:
        master = load_json(MASTER_STATE_PATH)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        master = {}
        state_errors.append(f"MASTER_STATE_INVALID:{exc}")

    state_bus = state.get("bus", {})
    comparisons = {
        "last_contiguous_closed_nnn": bus["last_closed"],
        "lowest_unanswered_nnn": bus["lowest_unanswered"],
        "next_expected_nnn": bus["next_expected"],
    }
    for key, actual in comparisons.items():
        if state_bus.get(key) != actual:
            state_errors.append(
                f"EXECUTION_STATE_BUS_DRIFT:{key}:state={state_bus.get(key)!r}:disk={actual!r}"
            )

    if state_bus.get("closed_nnns") != bus["closed"]:
        state_errors.append("EXECUTION_STATE_CLOSED_SET_DRIFT")

    expected_bus_status = "ACTIVE_GOAL_PRESENT" if bus["lowest_unanswered"] else "IDLE_WAITING_FOR_GOAL"
    if state_bus.get("status") != expected_bus_status:
        state_errors.append(
            f"EXECUTION_STATE_BUS_STATUS_DRIFT:state={state_bus.get('status')!r}:disk={expected_bus_status!r}"
        )

    current = state.get("current", {})
    if current.get("selected_bus_goal_nnn") != bus["lowest_unanswered"]:
        state_errors.append("EXECUTION_STATE_SELECTED_GOAL_DRIFT")

    last_closed = state.get("last_closed", {})
    if bus["last_closed"]:
        goal_path = bus["goals"][bus["last_closed"]]
        answer_path = bus["answers"][bus["last_closed"]]
        if last_closed.get("nnn") != bus["last_closed"]:
            state_errors.append("EXECUTION_STATE_LAST_CLOSED_DRIFT")
        if last_closed.get("goal_sha256") != sha256(goal_path):
            pin_errors.append(f"LAST_GOAL_HASH_DRIFT:{relpath(goal_path)}")
        answer_hash_mode = last_closed.get("answer_hash_mode", "ordinary_sha256")
        if answer_hash_mode == "canonical_payload_omit_hash_lines":
            actual_answer_hash = canonical_answer_sha256(answer_path)
        else:
            actual_answer_hash = sha256(answer_path)
        if last_closed.get("answer_sha256") != actual_answer_hash:
            pin_errors.append(f"LAST_ANSWER_HASH_DRIFT:{relpath(answer_path)}")

    if loop.get("latest_closed_bus_nnn") != bus["last_closed"]:
        state_errors.append("LOOP_STATE_LATEST_CLOSED_DRIFT")
    if loop.get("lowest_unanswered_bus_nnn") != bus["lowest_unanswered"]:
        state_errors.append("LOOP_STATE_LOWEST_UNANSWERED_DRIFT")
    if loop.get("next_expected_bus_nnn") != bus["next_expected"]:
        state_errors.append("LOOP_STATE_NEXT_EXPECTED_DRIFT")

    master_compiler = master.get("compiler", {})
    master_resume = master.get("resume", {})
    master_nodes = master.get("nodes", {})
    active_master_nodes = []
    if isinstance(master_nodes, dict):
        active_master_nodes = [
            node.get("id")
            for node in master_nodes.values()
            if isinstance(node, dict) and node.get("activity") == "ACTIVE"
        ]
    else:
        state_errors.append("MASTER_STATE_NODES_NOT_OBJECT")

    master_active = master_compiler.get("active_node_id")
    active_claims = {
        "master.compiler.active_node_id": master_active,
        "master.resume.current_leaf": master_resume.get("current_leaf"),
        "execution.current.contract_obligation": current.get("contract_obligation"),
        "loop.active_master_leaf": loop.get("active_master_leaf"),
        "loop.current_contract_obligation": loop.get("current_contract_obligation"),
    }
    if len(set(active_claims.values())) != 1:
        state_errors.append(f"MASTER_ACTIVE_LEAF_DRIFT:{active_claims}")
    if active_master_nodes != [master_active]:
        state_errors.append(
            f"MASTER_ACTIVE_NODE_COUNT_OR_ID_DRIFT:nodes={active_master_nodes!r}:declared={master_active!r}"
        )
    if master_compiler.get("active_node_count") != len(active_master_nodes):
        state_errors.append("MASTER_ACTIVE_NODE_COUNT_FIELD_DRIFT")

    lifecycle_claims = {
        "master.compiler.lifecycle": master_compiler.get("lifecycle"),
        "master.resume.mode": master_resume.get("mode"),
        "execution.operational_status": state.get("operational_status"),
        "loop.current_execution_status": loop.get("current_execution_status"),
    }
    if len(set(lifecycle_claims.values())) != 1:
        state_errors.append(f"MASTER_LIFECYCLE_DRIFT:{lifecycle_claims}")

    stop_claims = {
        "master.resume.current_stop": master_resume.get("current_stop"),
        "execution.current.stop_code": current.get("stop_code"),
        "loop.current_gate": loop.get("current_gate"),
    }
    if len(set(stop_claims.values())) != 1:
        state_errors.append(f"MASTER_STOP_CODE_DRIFT:{stop_claims}")

    master_bus = master.get("bus", {})
    if master_bus.get("observed_closed_nnns") != bus["closed"]:
        state_errors.append("MASTER_BUS_CLOSED_SET_DRIFT")
    if master_bus.get("lowest_unanswered_nnn") != bus["lowest_unanswered"]:
        state_errors.append("MASTER_BUS_LOWEST_UNANSWERED_DRIFT")
    if master_bus.get("next_free_nnn") != bus["next_expected"]:
        state_errors.append("MASTER_BUS_NEXT_FREE_DRIFT")
    if master_bus.get("codex_may_create_next_goal") is not False:
        state_errors.append("MASTER_BUS_CODEX_CREATE_PERMISSION_DRIFT")

    if bus["lowest_unanswered"] is not None and active_master_nodes:
        state_errors.append("ACTIVE_PHYSICAL_BUS_WITH_ACTIVE_MASTER_NODE")
    if bus["lowest_unanswered"] is None and master.get("owner_authorization", {}).get("status") == "OWNER_AUTHORIZED_AUTORUN":
        if len(active_master_nodes) != 1:
            state_errors.append("IDLE_OWNER_AUTORUN_REQUIRES_ONE_ACTIVE_MASTER_NODE")

    contract = state.get("contract", {})
    contract_path = REPO_ROOT / contract.get("path", "")
    if not contract_path.is_file():
        pin_errors.append("CONTRACT_V2_MISSING")
    elif sha256(contract_path) != contract.get("sha256"):
        pin_errors.append(f"CONTRACT_V2_HASH_DRIFT:{relpath(contract_path)}")

    for name, pin in state.get("pins", {}).items():
        path = REPO_ROOT / pin.get("path", "")
        if not path.is_file():
            pin_errors.append(f"PIN_MISSING:{name}")
        elif sha256(path) != pin.get("sha256"):
            pin_errors.append(f"PIN_HASH_DRIFT:{name}:{relpath(path)}")

    result = {
        "route": state.get("route_id", "RouteB_TwoLevelSpectralLadder"),
        "operational_status": state.get("operational_status", "UNKNOWN"),
        "architecture_status": state.get("architecture", {}).get("status", "UNKNOWN"),
        "rh_status": state.get("architecture", {}).get("route_b_rh_status", "UNKNOWN"),
        "current_stage": current.get("stage_id"),
        "current_obligation": current.get("contract_obligation"),
        "current_name": current.get("name"),
        "master_active_node": master_active,
        "master_stop_code": master_resume.get("current_stop"),
        "closed_nnns": bus["closed"],
        "lowest_unanswered_nnn": bus["lowest_unanswered"],
        "next_expected_nnn": bus["next_expected"],
        "last_closed": last_closed,
        "next_required_actor": current.get("next_required_actor"),
        "next_action": current.get("next_action"),
        "bus_errors": bus_errors,
        "state_errors": state_errors,
        "pin_errors": pin_errors,
    }

    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False))
    else:
        closed_display = "NONE"
        if bus["closed"]:
            closed_display = (
                bus["closed"][0]
                if len(bus["closed"]) == 1
                else f"{bus['closed'][0]}..{bus['closed'][-1]}"
            )
        active_display = bus["lowest_unanswered"] or "NONE"
        selected_display = current.get("selected_bus_goal_nnn") or "NONE"
        print(
            f"ROUTE_B: {result['operational_status']} / {result['rh_status']} / "
            f"{result['architecture_status']}"
        )
        print(
            f"STEP: {result['current_stage']} / {result['current_obligation']} / "
            f"{result['current_name']}"
        )
        print(
            f"BUS: closed={closed_display} active={active_display} "
            f"next-number={bus['next_expected']} selected-next={selected_display}"
        )
        print(
            f"LAST: {last_closed.get('nnn', 'NONE')} "
            f"{last_closed.get('name', 'NONE')} / "
            f"{last_closed.get('verdict', 'NONE')}"
        )
        print(f"ACTOR: {result['next_required_actor']}")
        print(f"ACTION: {result['next_action']}")
        all_errors = bus_errors + state_errors + pin_errors
        if all_errors:
            print("CHECK: FAIL")
            for error in all_errors:
                print(f"- {error}")
        else:
            print("CHECK: OK")

    if not args.check:
        return 0
    if pin_errors:
        return 4
    if state_errors:
        return 3
    if bus_errors:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
