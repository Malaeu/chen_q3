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
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from orchestrator.routeb_goal_state import is_paused_goal

BUS_DIR = REPO_ROOT / "docs" / "routeB_bus"
STATE_PATH = REQUEST_DIR / "ROUTE_B_EXECUTION_STATE.json"
STATUS_SURFACE_REGISTRY_PATH = (
    REPO_ROOT / "docs" / "semantic_quarantine" / "STATUS_SURFACE_REGISTRY_v1.json"
)
NAME_RE = re.compile(
    r"^(?P<goal_id>\d{3}[A-Za-z]*)_(?P<stem>[a-z0-9_]+)\.(?P<kind>goal|answer)\.md$"
)
ID_RE = re.compile(r"^(?P<root>\d{3})(?P<suffix>[A-Za-z]*)$")


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


def historical_marker_errors(
    repo_root: Path = REPO_ROOT,
    registry_path: Path = STATUS_SURFACE_REGISTRY_PATH,
) -> list[str]:
    """Validate explicit marker subscriptions on historical status surfaces."""
    try:
        registry = load_json(registry_path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        return [f"STATUS_SURFACE_REGISTRY_INVALID:{exc}"]

    surfaces = registry.get("surfaces")
    if not isinstance(surfaces, list):
        return ["STATUS_SURFACE_REGISTRY_INVALID:surfaces must be a list"]

    errors: list[str] = []
    for row in surfaces:
        if not isinstance(row, dict) or row.get("role") != "HISTORICAL":
            continue
        marker = row.get("required_marker")
        if not isinstance(marker, str) or not marker:
            continue
        rel = row.get("path")
        if not isinstance(rel, str) or not rel:
            errors.append("STATUS_SURFACE_REGISTRY_INVALID:marker row missing path")
            continue
        path = repo_root / rel
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            text = ""
        if marker not in text:
            errors.append(f"STALE_MONITOR_MISSING_HISTORICAL_MARKER:{rel}")
    return errors


def goal_id_key(goal_id: str) -> tuple[int, str]:
    match = ID_RE.fullmatch(goal_id)
    if match is None:
        raise ValueError(f"invalid goal id: {goal_id}")
    return int(match.group("root")), match.group("suffix").lower()


def answer_header_errors(goal_id: str, path: Path) -> list[str]:
    """Validate the machine header used by the living Route B bus."""
    text = path.read_text(encoding="utf-8")
    root = ID_RE.fullmatch(goal_id).group("root")  # type: ignore[union-attr]
    errors: list[str] = []
    if re.search(rf"(?m)^GOAL:\s*{re.escape(root)}\s*$", text) is None:
        errors.append(f"ANSWER_GOAL_HEADER_MISSING:{goal_id}")
    if re.search(r"(?m)^STATUS:\s*CLOSED(?:_[A-Z0-9_]+)?\s*$", text) is None:
        errors.append(f"ANSWER_CLOSED_STATUS_MISSING:{goal_id}")
    if re.search(r"(?m)^(?:EXACT_RESULT|RESULT|SUCCESS):\s*\S+", text) is None:
        errors.append(f"ANSWER_RESULT_HEADER_MISSING:{goal_id}")
    return errors


def scan_bus() -> dict[str, Any]:
    entries: dict[str, dict[str, list[Path]]] = {}
    errors: list[str] = []

    for path in sorted(BUS_DIR.iterdir()):
        if not path.is_file():
            continue
        if not (path.name.endswith(".goal.md") or path.name.endswith(".answer.md")):
            continue
        match = NAME_RE.fullmatch(path.name)
        if match is None:
            errors.append(f"BUS_NAMING_ERROR:{path.name}")
            continue
        goal_id = match.group("goal_id")
        stem = match.group("stem")
        by_stem = entries.setdefault(goal_id, {}).setdefault(stem, [])
        by_stem.append(path)

    goal_roots = [goal_id_key(goal_id)[0] for goal_id, stems in entries.items()
                  if any(path.name.endswith(".goal.md") for paths in stems.values() for path in paths)]
    current_root = max(goal_roots) if goal_roots else None
    current_ids = {
        goal_id for goal_id in entries
        if current_root is not None and goal_id_key(goal_id)[0] == current_root
    }

    goals: dict[str, Path] = {}
    answers: dict[str, Path] = {}
    paused_all: dict[str, Path] = {}
    for goal_id, stems in sorted(entries.items(), key=lambda item: goal_id_key(item[0])):
        for paths in stems.values():
            for goal_path in (path for path in paths if path.name.endswith(".goal.md")):
                if is_paused_goal(goal_path):
                    paused_all[goal_id] = goal_path
        if goal_id not in current_ids:
            continue
        if len(stems) != 1:
            errors.append(f"BUS_DUPLICATE_ID:{goal_id}:{','.join(sorted(stems))}")
            continue
        stem, paths = next(iter(stems.items()))
        for path in paths:
            kind = NAME_RE.fullmatch(path.name).group("kind")  # type: ignore[union-attr]
            if kind == "goal" and goal_id in paused_all:
                continue
            target = goals if kind == "goal" else answers
            if goal_id in target:
                errors.append(f"BUS_DUPLICATE_{kind.upper()}:{goal_id}")
            target[goal_id] = path
        if goal_id in answers and goal_id not in goals:
            errors.append(f"BUS_ORPHAN_ANSWER:{goal_id}_{stem}")

    for goal_id, answer in sorted(answers.items(), key=lambda item: goal_id_key(item[0])):
        errors.extend(answer_header_errors(goal_id, answer))

    closed = sorted((goal_id for goal_id in goals if goal_id in answers), key=goal_id_key)
    unanswered = sorted((goal_id for goal_id in goals if goal_id not in answers), key=goal_id_key)
    last_closed = closed[-1] if closed else None
    next_expected = f"{(current_root + 1) if current_root is not None else 1:03d}"
    return {
        "current_root": f"{current_root:03d}" if current_root is not None else None,
        "goals": goals,
        "answers": answers,
        "paused": sorted(paused_all, key=goal_id_key),
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
    marker_errors = historical_marker_errors()

    try:
        state = load_json(STATE_PATH)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        state = {}
        state_errors.append(f"EXECUTION_STATE_INVALID:{exc}")

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
    if state_bus.get("paused_nnns") != bus["paused"]:
        state_errors.append("EXECUTION_STATE_PAUSED_SET_DRIFT")

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
        "current_root": bus["current_root"],
        "closed_nnns": bus["closed"],
        "paused_nnns": bus["paused"],
        "lowest_unanswered_nnn": bus["lowest_unanswered"],
        "next_expected_nnn": bus["next_expected"],
        "last_closed": last_closed,
        "next_required_actor": current.get("next_required_actor"),
        "next_action": current.get("next_action"),
        "bus_errors": bus_errors,
        "state_errors": state_errors,
        "pin_errors": pin_errors,
        "status_surface_errors": marker_errors,
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
        print(f"PAUSED_RESTORABLE: {','.join(bus['paused']) or 'NONE'}")
        print(
            f"LAST: {last_closed.get('nnn', 'NONE')} "
            f"{last_closed.get('name', 'NONE')} / "
            f"{last_closed.get('verdict', 'NONE')}"
        )
        print(f"ACTOR: {result['next_required_actor']}")
        print(f"ACTION: {result['next_action']}")
        all_errors = bus_errors + state_errors + pin_errors + marker_errors
        if all_errors:
            print("CHECK: FAIL")
            for error in all_errors:
                print(f"- {error}")
        else:
            print("CHECK: OK")

    if not args.check:
        return 0
    if marker_errors:
        return 5
    if pin_errors:
        return 4
    if state_errors:
        return 3
    if bus_errors:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
