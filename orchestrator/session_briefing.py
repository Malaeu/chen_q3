#!/usr/bin/env python3
"""Read-only Route B session briefing and local close-session checkpoint."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

import yaml

REPO = Path(__file__).resolve().parents[1]
ROUTE_STATE = Path(
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/"
    "ROUTE_B_EXECUTION_STATE.json"
)
LIVE_BUS = Path("docs/routeB_bus")
CURRENT_TASK = Path("docs/Codex/CURRENT.md")
DEBT_REGISTRY = Path("docs/routeB_bus/RECHECKABLE_RESEARCH_DEBTS.json")
DEFAULT_CHECKPOINT = Path(
    "q3.lean.aristotle/.qmd_cache/session_briefing_checkpoint.json"
)

SCHEMA = "q3_routeb_session_checkpoint.v1"
REGISTRY_SCHEMA = "q3_routeb_recheckable_research_debts.v2"
DEBT_STATUSES = {
    "KILLED_RECHECKABLE",
    "REOPEN_CANDIDATE",
    "SOURCE_VERIFIED",
    "REOPENED",
}
TRANSITIONS = {
    "KILLED_RECHECKABLE": {"REOPEN_CANDIDATE"},
    "REOPEN_CANDIDATE": {"KILLED_RECHECKABLE", "SOURCE_VERIFIED"},
    "SOURCE_VERIFIED": {"REOPEN_CANDIDATE", "REOPENED"},
    "REOPENED": set(),
}


class SessionBriefingError(RuntimeError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise SessionBriefingError(f"DUPLICATE_JSON_KEY:{key}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object
        )
    except (OSError, json.JSONDecodeError) as exc:
        raise SessionBriefingError(f"JSON_UNREADABLE:{path}:{exc}") from exc
    if not isinstance(data, dict):
        raise SessionBriefingError(f"JSON_ROOT_INVALID:{path}")
    return data


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=repo, capture_output=True, text=True
    )
    if proc.returncode != 0:
        raise SessionBriefingError(proc.stderr.strip() or "GIT_QUERY_FAILED")
    return proc.stdout.strip()


def _machine_header(path: Path) -> dict[str, Any]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise SessionBriefingError(f"MACHINE_HEADER_UNREADABLE:{path}:{exc}") from exc
    match = re.search(r"(?ms)^```yaml\s*\n(.*?)^```\s*$", text)
    if not match:
        return {}
    try:
        data = yaml.safe_load(match.group(1))
    except yaml.YAMLError as exc:
        raise SessionBriefingError(f"YAML_HEADER_INVALID:{path}:{exc}") from exc
    return data if isinstance(data, dict) else {}


def validate_registry(repo: Path, path: Path | None = None) -> dict[str, Any]:
    registry_path = path or repo / DEBT_REGISTRY
    data = load_json(registry_path)
    if set(data) != {"schema", "lifecycle", "debts"} or data.get("schema") != REGISTRY_SCHEMA:
        raise SessionBriefingError("RESEARCH_DEBT_REGISTRY_SCHEMA_INVALID")
    lifecycle = data.get("lifecycle")
    expected = [
        "KILLED_RECHECKABLE",
        "REOPEN_CANDIDATE",
        "SOURCE_VERIFIED",
        "REOPENED",
    ]
    if (
        not isinstance(lifecycle, dict)
        or set(lifecycle) != {"automatic_reopen_allowed", "ordered_states", "rule"}
        or lifecycle.get("ordered_states") != expected
    ):
        raise SessionBriefingError("RESEARCH_DEBT_LIFECYCLE_INVALID")
    if lifecycle.get("automatic_reopen_allowed") is not False:
        raise SessionBriefingError("RESEARCH_DEBT_AUTOMATIC_REOPEN_FORBIDDEN")
    debts = data.get("debts")
    if not isinstance(debts, list):
        raise SessionBriefingError("RESEARCH_DEBT_ROWS_INVALID")
    seen: set[str] = set()
    allowed_triggers = {
        "NEW_LITERATURE", "NEW_THEOREM", "NEW_DERIVATION",
        "PROSHKA_RESEARCH", "COUNTEREXAMPLE",
    }
    required = {
        "id", "target_id", "classification", "not_disproved", "status",
        "killed_at", "reason", "missing_object", "terminal_consumer",
        "why_interesting", "unlock_value", "estimated_difficulty",
        "last_attempt", "reopen_if", "reopen_triggers", "next_probe",
        "novelty_requirement", "last_external_check", "search_hints",
        "related_goal", "authoritative_refs",
    }
    for row in debts:
        if not isinstance(row, dict) or set(row) != required:
            raise SessionBriefingError("RESEARCH_DEBT_ROW_FIELDS_INVALID")
        debt_id = row["id"]
        if not isinstance(debt_id, str) or not debt_id or debt_id in seen:
            raise SessionBriefingError("RESEARCH_DEBT_ID_INVALID_OR_DUPLICATE")
        seen.add(debt_id)
        if row["status"] not in DEBT_STATUSES:
            raise SessionBriefingError(f"RESEARCH_DEBT_STATUS_INVALID:{debt_id}")
        if row["classification"] != "RESEARCH_DEBT" or row["not_disproved"] is not True:
            raise SessionBriefingError(f"RESEARCH_DEBT_CLASSIFICATION_INVALID:{debt_id}")
        if row["unlock_value"] not in {"HIGH", "MEDIUM", "LOW"}:
            raise SessionBriefingError(f"RESEARCH_DEBT_UNLOCK_INVALID:{debt_id}")
        if row["estimated_difficulty"] not in {"LOW", "MEDIUM", "HIGH", "UNKNOWN"}:
            raise SessionBriefingError(f"RESEARCH_DEBT_DIFFICULTY_INVALID:{debt_id}")
        for field in (
            "target_id", "reason", "missing_object", "terminal_consumer",
            "why_interesting", "next_probe", "related_goal",
        ):
            if not isinstance(row[field], str) or not row[field].strip():
                raise SessionBriefingError(f"RESEARCH_DEBT_TEXT_INVALID:{debt_id}:{field}")
        if not isinstance(row["last_attempt"], dict) or set(row["last_attempt"]) != {
            "date", "outcome", "approach"
        }:
            raise SessionBriefingError(f"RESEARCH_DEBT_LAST_ATTEMPT_INVALID:{debt_id}")
        if any(
            not isinstance(row["last_attempt"][field], str)
            or not row["last_attempt"][field].strip()
            for field in ("date", "outcome", "approach")
        ):
            raise SessionBriefingError(f"RESEARCH_DEBT_LAST_ATTEMPT_INVALID:{debt_id}")
        for field in (
            "reopen_if", "reopen_triggers", "novelty_requirement",
            "search_hints", "authoritative_refs",
        ):
            if not isinstance(row[field], list) or not row[field]:
                raise SessionBriefingError(f"RESEARCH_DEBT_LIST_INVALID:{debt_id}:{field}")
        if not set(row["reopen_triggers"]).issubset(allowed_triggers):
            raise SessionBriefingError(f"RESEARCH_DEBT_TRIGGER_INVALID:{debt_id}")
        if any(not isinstance(item, str) or not item.strip() for field in (
            "reopen_if", "reopen_triggers", "novelty_requirement", "search_hints"
        ) for item in row[field]):
            raise SessionBriefingError(f"RESEARCH_DEBT_LIST_ITEM_INVALID:{debt_id}")
        for field in ("killed_at", "last_external_check"):
            try:
                dt.date.fromisoformat(row[field])
            except (TypeError, ValueError) as exc:
                raise SessionBriefingError(
                    f"RESEARCH_DEBT_DATE_INVALID:{debt_id}:{field}"
                ) from exc
        try:
            dt.date.fromisoformat(row["last_attempt"]["date"])
        except (TypeError, ValueError) as exc:
            raise SessionBriefingError(
                f"RESEARCH_DEBT_DATE_INVALID:{debt_id}:last_attempt.date"
            ) from exc
        for ref in row["authoritative_refs"]:
            if not isinstance(ref, dict) or set(ref) != {"path", "commit", "git_blob"}:
                raise SessionBriefingError(f"RESEARCH_DEBT_REF_INVALID:{debt_id}")
            source = repo / ref["path"]
            if not source.is_file():
                raise SessionBriefingError(f"RESEARCH_DEBT_REF_MISSING:{ref['path']}")
            _git(repo, "merge-base", "--is-ancestor", ref["commit"], "HEAD")
            actual = _git(repo, "rev-parse", f"{ref['commit']}:{ref['path']}")
            if actual != ref["git_blob"]:
                raise SessionBriefingError(f"RESEARCH_DEBT_REF_BLOB_DRIFT:{ref['path']}")
    return data


def transition_allowed(before: str, after: str) -> bool:
    return after in TRANSITIONS.get(before, set())


def _tracked_markdown(repo: Path, prefix: str) -> list[Path]:
    names = _git(repo, "ls-files", prefix).splitlines()
    return [repo / name for name in names if name.endswith(".md")]


def authoritative_totals(repo: Path) -> dict[str, int]:
    bus = repo / LIVE_BUS
    completed = sum(
        1
        for goal in bus.glob("*.goal.md")
        if goal.with_name(goal.name.removesuffix(".goal.md") + ".answer.md").is_file()
    )
    kill_artifacts = 0
    proved_verdicts = 0
    for path in _tracked_markdown(repo, "docs/routeB_bus"):
        text = path.read_text(encoding="utf-8", errors="replace")
        if re.search(r"(?m)^(?:OPERATIVE_CLASS|RESULT):\s*KILL_[A-Z0-9_]+\s*$", text):
            kill_artifacts += 1
        if "/proshka/PROSHKA_VERDICT" in path.as_posix() and re.match(
            r"^# STATUS:\s*PROVED\b", text
        ):
            proved_verdicts += 1
    answered = 0
    queue = bus / "PROSHKA_QUEUE.md"
    if queue.is_file():
        text = queue.read_text(encoding="utf-8")
        for match in re.finditer(
            r"(?ms)^##\s+REQ-[0-9A-Za-z-]+\b(.*?)(?=^##\s+|\Z)", text
        ):
            if re.search(r"(?m)^-?\s*`?STATUS:\s*ANSWERED\b", match.group(1)):
                answered += 1
    return {
        "completed_bus_goals": completed,
        "kill_outcome_artifacts": kill_artifacts,
        "answered_requests": answered,
        "proved_verdict_artifacts": proved_verdicts,
    }


def _current_task(repo: Path) -> tuple[dict[str, Any], str]:
    path = repo / CURRENT_TASK
    header = _machine_header(path)
    task_file = header.get("task_file")
    if not isinstance(task_file, str) or not task_file:
        return header, ""
    task_path = (repo / task_file).resolve()
    try:
        task_path.relative_to(repo.resolve())
    except ValueError as exc:
        raise SessionBriefingError("CURRENT_TASK_PATH_OUTSIDE_REPO") from exc
    if not task_path.is_file():
        raise SessionBriefingError(f"CURRENT_TASK_FILE_MISSING:{task_file}")
    return header, task_path.read_text(encoding="utf-8")


def _latest_named_root(task_text: str) -> str | None:
    match = re.search(
        r"next independent dependency\s+root.*?`([A-Z][A-Z0-9_]+)`",
        task_text,
        flags=re.IGNORECASE | re.DOTALL,
    )
    return match.group(1) if match else None


def control_plane_drift(route: dict[str, Any]) -> bool:
    candidate = route.get("latest_named_unselected_root")
    return bool(candidate and candidate != route.get("dependency_root"))


def snapshot(repo: Path) -> dict[str, Any]:
    state = load_json(repo / ROUTE_STATE)
    task, task_text = _current_task(repo)
    current = state.get("current") if isinstance(state.get("current"), dict) else {}
    return {
        "schema": SCHEMA,
        "head": _git(repo, "rev-parse", "HEAD"),
        "route": {
            "goal": current.get("selected_bus_goal_nnn"),
            "dependency_root": current.get("contract_obligation"),
            "stage_id": current.get("stage_id"),
            "status": current.get("status"),
            "latest_named_unselected_root": _latest_named_root(task_text),
            "current_task_status": task.get("status"),
            "current_task_file": task.get("task_file"),
        },
        "totals": authoritative_totals(repo),
    }


def checkpoint_bytes(data: dict[str, Any]) -> bytes:
    return (json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def write_checkpoint(repo: Path, path: Path | None = None) -> Path:
    target = path or repo / DEFAULT_CHECKPOINT
    if not target.is_absolute():
        target = repo / target
    payload = checkpoint_bytes(snapshot(repo))
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{target.name}.", dir=target.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, target)
    finally:
        Path(temporary).unlink(missing_ok=True)
    return target


def load_checkpoint(path: Path) -> dict[str, Any] | None:
    if not path.is_file():
        return None
    data = load_json(path)
    totals = data.get("totals")
    required_totals = {
        "completed_bus_goals",
        "kill_outcome_artifacts",
        "answered_requests",
        "proved_verdict_artifacts",
    }
    if (
        set(data) != {"schema", "head", "route", "totals"}
        or data.get("schema") != SCHEMA
        or not isinstance(data.get("head"), str)
        or not isinstance(data.get("route"), dict)
        or not isinstance(totals, dict)
        or set(totals) != required_totals
        or not all(isinstance(value, int) and value >= 0 for value in totals.values())
    ):
        raise SessionBriefingError("SESSION_BRIEFING_CHECKPOINT_INVALID")
    return data


def _delta(now: dict[str, int], before: dict[str, Any] | None) -> dict[str, int | None]:
    if before is None:
        return {key: None for key in now}
    result: dict[str, int | None] = {}
    for key, value in now.items():
        old = before.get(key)
        result[key] = value - old if isinstance(old, int) and value >= old else None
    return result


def debt_priority(row: dict[str, Any], today: dt.date) -> tuple[str, int]:
    age = (today - dt.date.fromisoformat(row["last_external_check"])).days
    if row["status"] in {"REOPEN_CANDIDATE", "SOURCE_VERIFIED"}:
        return "HIGH_NEW_SIGNAL", age
    if age >= 30:
        return "HIGHLIGHT_30_PLUS", age
    if age >= 7:
        return "NORMAL", age
    return "RECENT_PASSIVE", age


def ranked_debts(rows: list[dict[str, Any]], today: dt.date) -> list[dict[str, Any]]:
    priority_order = {
        "HIGH_NEW_SIGNAL": 0,
        "HIGHLIGHT_30_PLUS": 1,
        "NORMAL": 2,
        "RECENT_PASSIVE": 3,
    }
    unlock_order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2}
    difficulty_order = {"LOW": 0, "MEDIUM": 1, "UNKNOWN": 2, "HIGH": 3}
    return sorted(
        rows,
        key=lambda row: (
            priority_order[debt_priority(row, today)[0]],
            unlock_order[row["unlock_value"]],
            difficulty_order[row["estimated_difficulty"]],
            row["id"],
        ),
    )


def render_briefing(
    repo: Path,
    *,
    checkpoint_path: Path | None = None,
    today: dt.date | None = None,
) -> str:
    registry = validate_registry(repo)
    now = snapshot(repo)
    cp_path = checkpoint_path or repo / DEFAULT_CHECKPOINT
    if not cp_path.is_absolute():
        cp_path = repo / cp_path
    checkpoint = load_checkpoint(cp_path)
    changes = _delta(now["totals"], checkpoint.get("totals") if checkpoint else None)
    route = now["route"]
    candidate = route.get("latest_named_unselected_root")
    drift = control_plane_drift(route)
    lines = [
        "ROUTE B — SESSION BRIEF",
        "",
        "WHERE WE ARE",
        f"  Goal: {route.get('goal') or '—'} · Route B: CHALLENGER / NOT_RH",
        f"  state dependency root: {route.get('dependency_root') or '—'}",
        f"  state stage/status: {route.get('stage_id') or '—'} / {route.get('status') or '—'}",
    ]
    if candidate:
        lines.append(f"  later named root: {candidate} (not selected by execution state)")
    lines.extend(["", "WHAT CHANGED since previous session checkpoint"])
    if checkpoint is None:
        lines.append("  checkpoint: absent — baseline will be written by close-session")
    else:
        lines.append(f"  checkpoint HEAD: {checkpoint.get('head', '—')[:12]}")
    labels = {
        "completed_bus_goals": "completed bus goals",
        "kill_outcome_artifacts": "KILL outcome artifacts",
        "answered_requests": "ANSWERED requests",
        "proved_verdict_artifacts": "PROVED verdict artifacts",
    }
    for key, label in labels.items():
        delta = changes[key]
        rendered = "n/a (no checkpoint)" if delta is None else f"+{delta}"
        lines.append(f"  {label}: {rendered} · total {now['totals'][key]}")
    lines.extend(["", "WHAT IS BLOCKING"])
    if drift:
        lines.append(
            "  CONTROL_PLANE_DRIFT: later closeout names a different root, but the "
            "execution state still carries the older G3 address."
        )
        lines.append("  BRIEFING_BLOCKER: CONTROL_PLANE_DRIFT")
        lines.append(
            "  No executable weighted-residual attack is selected; the latest task is CLOSED."
        )
    else:
        lines.append(f"  {route.get('status') or 'No machine-readable blocker found.'}")
    lines.extend(["", "WHAT CAN REOPEN"])
    today = today or dt.datetime.now(dt.timezone.utc).date()
    ordered = ranked_debts(registry["debts"], today)
    lines.append(f"  REOPENABLE RESEARCH DEBTS: {len(ordered)}")
    for row in ordered:
        priority, age = debt_priority(row, today)
        lines.append(
            f"  [{priority}] {row['id']} · RESEARCH_DEBT · "
            f"unlock {row['unlock_value']} · difficulty {row['estimated_difficulty']} · "
            f"last check {age}d ago"
        )
        lines.append(f"    missing: {row['missing_object']}")
        lines.append(f"    reopen only if: {row['reopen_if'][0]}")
    if ordered:
        top = ordered[0]
        lines.extend([
            "",
            "TOP RESEARCH-VALUE DEBT",
            f"  {top['id']}",
            f"  Why interesting: {top['why_interesting']}",
            f"  Next novel probe: {top['next_probe']}",
            "  Suggested action: ASK PROSHKA FOR NEW MATHEMATICS",
        ])
    lines.extend(["", "WHAT NEXT"])
    if drift:
        lines.append(
            "  Reconcile the execution address through an authorized physical rerank; "
            "do not invent state or resume a killed shelf."
        )
    else:
        lines.append("  Follow the physical bus and current execution-state action only.")
    active = [debt_priority(row, today)[0] for row in ordered]
    default = "NO (all checks are 0–6 days old)" if active and set(active) == {"RECENT_PASSIVE"} else "SELECT"
    lines.extend([
        "",
        f"Search our debts today? YES / NO / SELECT  [default: {default}]",
        "Spend one Proshka research cycle? YES / NO / SELECT  [default: NO]",
        "  YES prepares one exact gated RESEARCH_DEBT_CHALLENGE; it does not auto-send it.",
        "  External web/literature search was NOT run.",
        "  A search hit may create REOPEN_CANDIDATE only; SOURCE_VERIFIED is required before REOPENED.",
    ])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", nargs="?", choices=["brief", "checkpoint", "validate"], default="brief")
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--checkpoint-file", type=Path)
    parser.add_argument("--as-of", type=dt.date.fromisoformat)
    args = parser.parse_args()
    repo = args.root.resolve()
    try:
        if args.command == "validate":
            data = validate_registry(repo)
            print(f"RESEARCH_DEBTS_VALID debts={len(data['debts'])}")
        elif args.command == "checkpoint":
            path = write_checkpoint(repo, args.checkpoint_file)
            print(f"SESSION_CHECKPOINT_WRITTEN {path}")
        else:
            print(
                render_briefing(
                    repo,
                    checkpoint_path=args.checkpoint_file,
                    today=args.as_of,
                ),
                end="",
            )
    except SessionBriefingError as exc:
        print(f"SESSION_BRIEFING_INVALID:{exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
