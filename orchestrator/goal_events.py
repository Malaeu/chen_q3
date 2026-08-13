#!/usr/bin/env python3
"""Durable AUTOPILOT goal-attempt and reusable-insight writers.

The two event types deliberately have different canonical homes:

* registered attempts are append-only rows in ``knowledge.db``;
* reusable insights are compact, provenance-bound entries in ``INSIGHTS.md``.

Both inputs use closed JSON schemas.  Retrying the same exact payload is safe;
reusing an identifier for different bytes fails closed.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import sqlite3
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path, PurePosixPath
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
DEFAULT_DB = REPO_ROOT / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"
DEFAULT_INSIGHTS = REPO_ROOT / "q3.lean.aristotle" / "docs" / "INSIGHTS.md"

SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
GOAL_RUN_RE = re.compile(r"^GOAL(?P<goal_id>\d{3}[A-Za-z]*)-\d{8}T\d{6}Z$")
ATTEMPT_ID_RE = re.compile(
    r"^ATTEMPT_GOAL(?P<goal_id>\d{3}[A-Za-z]*)_(?P<cycle>\d{3})$"
)
INSIGHT_ID_RE = re.compile(r"^INSIGHT_[A-Z0-9][A-Z0-9_]{2,127}$")
DELTA_ID_RE = re.compile(r"^(?:NONE|[A-Z0-9][A-Z0-9_.:-]{2,191})$")

ATTEMPT_FIELDS = frozenset(
    {
        "schema",
        "attempt_id",
        "goal_run_id",
        "goal_file",
        "goal_sha256",
        "recorded_date",
        "cycle_index",
        "registered_prediction",
        "cheapest_killer",
        "blocker_fingerprint_before",
        "blocker_fingerprint_after",
        "delta_id",
        "progress_class",
        "cognitive_operator",
        "next_action",
        "source_provenance",
        "extra",
    }
)
INSIGHT_FIELDS = frozenset(
    {
        "schema",
        "insight_id",
        "recorded_date",
        "title",
        "workstream",
        "target",
        "summary",
        "validation",
        "boundary",
        "next_target",
        "source_provenance",
    }
)
PROVENANCE_FIELDS = frozenset({"path", "sha256", "role", "locator"})

PROGRESS_CLASSES = frozenset(
    {
        "PROOF_PROGRESS",
        "REPRESENTATION_PROGRESS",
        "FALSIFICATION_PROGRESS",
        "GAP_SHRINK",
        "NO_PROGRESS",
    }
)
COGNITIVE_OPERATORS = frozenset(
    {
        "REPRESENTATION_SHIFT",
        "COUNTEREXAMPLE_HUNT",
        "DUALIZE",
        "BOUNDARY_CASE",
        "UNIT_AUDIT",
        "MINIMAL_LEMMA",
        "LITERATURE_BRIDGE",
        "ABANDON_ROUTE",
    }
)
NEXT_ACTIONS = frozenset(
    {
        "CONTINUE_STEP",
        "CLOSE_GOAL",
        "REQUEST_STRATEGIC_REVIEW",
        "STOP",
    }
)


class GoalEventError(ValueError):
    """Fail-closed goal-event error with a stable machine code."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class EventReceipt:
    status: str
    event_id: str
    payload_sha256: str
    semantic_sha256: str | None = None


def _fail(code: str, detail: str = "") -> None:
    raise GoalEventError(code, detail)


def _canonical_bytes(payload: object) -> bytes:
    return json.dumps(
        payload,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _load_unique_json(path: Path) -> dict[str, Any]:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                _fail("GOAL_EVENT_PAYLOAD_INVALID", f"duplicate JSON key: {key}")
            result[key] = value
        return result

    try:
        payload = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=unique_object,
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        _fail("GOAL_EVENT_PAYLOAD_INVALID", str(exc))
    if not isinstance(payload, dict):
        _fail("GOAL_EVENT_PAYLOAD_INVALID", "top level must be a JSON object")
    return payload


def _nonempty_text(payload: dict[str, Any], field: str) -> str:
    value = payload.get(field)
    if not isinstance(value, str) or not value.strip():
        _fail("GOAL_EVENT_PAYLOAD_INVALID", f"{field} must be nonempty text")
    return value.strip()


def _iso_date(value: object, *, code: str) -> str:
    if not isinstance(value, str) or DATE_RE.fullmatch(value) is None:
        _fail(code, "recorded_date must be YYYY-MM-DD")
    try:
        date.fromisoformat(value)
    except ValueError as exc:
        _fail(code, f"recorded_date invalid: {exc}")
    return value


def _repo_file(value: object, *, repo_root: Path, label: str) -> tuple[str, Path]:
    if not isinstance(value, str) or not value:
        _fail("GOAL_EVENT_PROVENANCE_INVALID", f"{label} path missing")
    rel = PurePosixPath(value)
    if rel.is_absolute() or ".." in rel.parts or "\\" in value or rel.as_posix() != value:
        _fail(
            "GOAL_EVENT_PROVENANCE_INVALID",
            f"{label} must be a canonical repo-relative POSIX path",
        )
    root = repo_root.resolve()
    path = (root / Path(*rel.parts)).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        _fail("GOAL_EVENT_PROVENANCE_INVALID", f"{label} does not exist: {value}")
    return value, path


def _validate_provenance(
    value: object, *, repo_root: Path
) -> list[dict[str, str]]:
    if not isinstance(value, list) or not value:
        _fail("GOAL_EVENT_PROVENANCE_INVALID", "source_provenance must be nonempty")
    validated: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for index, row in enumerate(value):
        if not isinstance(row, dict) or set(row) != PROVENANCE_FIELDS:
            _fail(
                "GOAL_EVENT_PROVENANCE_INVALID",
                f"source_provenance[{index}] has unknown or missing fields",
            )
        rel, path = _repo_file(row.get("path"), repo_root=repo_root, label=f"source[{index}]")
        expected = row.get("sha256")
        if not isinstance(expected, str) or SHA256_RE.fullmatch(expected) is None:
            _fail("GOAL_EVENT_PROVENANCE_INVALID", f"source[{index}] SHA-256 invalid")
        if _sha256_file(path) != expected:
            _fail("GOAL_EVENT_PROVENANCE_INVALID", f"source[{index}] SHA-256 drift: {rel}")
        role = row.get("role")
        locator = row.get("locator")
        if not isinstance(role, str) or not role.strip():
            _fail("GOAL_EVENT_PROVENANCE_INVALID", f"source[{index}] role missing")
        if not isinstance(locator, str) or not locator.strip():
            _fail("GOAL_EVENT_PROVENANCE_INVALID", f"source[{index}] locator missing")
        identity = (rel, locator.strip())
        if identity in seen:
            _fail("GOAL_EVENT_PROVENANCE_INVALID", f"duplicate provenance: {identity}")
        seen.add(identity)
        validated.append(
            {
                "path": rel,
                "sha256": expected,
                "role": role.strip(),
                "locator": locator.strip(),
            }
        )
    return validated


def validate_attempt(payload: object, *, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    if not isinstance(payload, dict) or set(payload) != ATTEMPT_FIELDS:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "attempt schema is not closed")
    if payload.get("schema") != "q3_goal_attempt.v1":
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "unsupported schema")
    attempt_id = _nonempty_text(payload, "attempt_id")
    goal_run_id = _nonempty_text(payload, "goal_run_id")
    attempt_match = ATTEMPT_ID_RE.fullmatch(attempt_id)
    run_match = GOAL_RUN_RE.fullmatch(goal_run_id)
    if attempt_match is None or run_match is None:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "attempt or goal-run identity invalid")
    cycle = payload.get("cycle_index")
    if not isinstance(cycle, int) or isinstance(cycle, bool) or not 1 <= cycle <= 12:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "cycle_index must be 1..12")
    if (
        attempt_match.group("goal_id") != run_match.group("goal_id")
        or int(attempt_match.group("cycle")) != cycle
    ):
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "attempt identity disagrees with run/cycle")

    goal_rel, goal_path = _repo_file(
        payload.get("goal_file"), repo_root=repo_root, label="goal_file"
    )
    goal_sha = payload.get("goal_sha256")
    if not isinstance(goal_sha, str) or SHA256_RE.fullmatch(goal_sha) is None:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "goal_sha256 invalid")
    if _sha256_file(goal_path) != goal_sha:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", f"goal SHA-256 drift: {goal_rel}")
    if run_match.group("goal_id") not in Path(goal_rel).name:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "goal file disagrees with goal_run_id")

    _iso_date(payload.get("recorded_date"), code="GOAL_ATTEMPT_SCHEMA_INVALID")
    for field in (
        "registered_prediction",
        "cheapest_killer",
        "blocker_fingerprint_before",
        "blocker_fingerprint_after",
    ):
        value = _nonempty_text(payload, field)
        if field.startswith("blocker_") and SHA256_RE.fullmatch(value) is None:
            _fail("GOAL_ATTEMPT_SCHEMA_INVALID", f"{field} must be a SHA-256")
    delta_id = _nonempty_text(payload, "delta_id")
    if DELTA_ID_RE.fullmatch(delta_id) is None:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "delta_id invalid")
    if payload.get("progress_class") not in PROGRESS_CLASSES:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "progress_class invalid")
    if payload.get("cognitive_operator") not in COGNITIVE_OPERATORS:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "cognitive_operator invalid")
    if payload.get("next_action") not in NEXT_ACTIONS:
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "next_action invalid")
    if payload["progress_class"] == "NO_PROGRESS":
        if delta_id != "NONE":
            _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "NO_PROGRESS cannot claim a delta")
        if payload["blocker_fingerprint_before"] != payload["blocker_fingerprint_after"]:
            _fail(
                "GOAL_ATTEMPT_SCHEMA_INVALID",
                "NO_PROGRESS must preserve the blocker fingerprint",
            )
    elif delta_id == "NONE":
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "progress requires a named delta")
    extra = payload.get("extra")
    if not isinstance(extra, dict):
        _fail("GOAL_ATTEMPT_SCHEMA_INVALID", "extra must be an object")
    controller_names = ATTEMPT_FIELDS - {"schema", "extra", "source_provenance"}
    if set(extra) & controller_names:
        _fail(
            "GOAL_ATTEMPT_SCHEMA_INVALID",
            "extra cannot shadow controller-critical fields",
        )
    validated = dict(payload)
    validated["source_provenance"] = _validate_provenance(
        payload.get("source_provenance"), repo_root=repo_root
    )
    return validated


def _insert_journal_fts(conn: sqlite3.Connection, rowid: int, row: dict[str, Any]) -> None:
    conn.execute(
        "INSERT INTO journal_fts(rowid,title,body,target,boundary) VALUES (?,?,?,?,?)",
        (rowid, row["title"], row["body"], row["target"], row["boundary"]),
    )


def record_attempt(
    payload: object,
    *,
    db_path: Path = DEFAULT_DB,
    repo_root: Path = REPO_ROOT,
) -> EventReceipt:
    validated = validate_attempt(payload, repo_root=repo_root)
    canonical = _canonical_bytes(validated)
    payload_sha = _sha256_bytes(canonical)
    event_id = validated["attempt_id"]
    body = canonical.decode("utf-8")
    conn = sqlite3.connect(db_path)
    try:
        conn.execute("BEGIN IMMEDIATE")
        existing = conn.execute(
            "SELECT kind,artifact_sha,body FROM journal_entry WHERE id=?", (event_id,)
        ).fetchone()
        if existing is not None:
            if existing == ("attempt", payload_sha, body):
                conn.rollback()
                return EventReceipt("ALREADY_RECORDED", event_id, payload_sha)
            _fail("ATTEMPT_ID_COLLISION", event_id)
        cursor = conn.execute(
            "INSERT INTO journal_entry "
            "(id,date,kind,title,workstream,state,channel,target,validation,artifact_sha,"
            "boundary,next_target,body,source_file) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                event_id,
                validated["recorded_date"],
                "attempt",
                f"Registered cycle {validated['cycle_index']} for {validated['goal_run_id']}",
                validated["goal_run_id"],
                validated["progress_class"],
                "control-plane",
                validated["blocker_fingerprint_after"],
                validated["delta_id"],
                payload_sha,
                validated["registered_prediction"],
                validated["next_action"],
                body,
                validated["goal_file"],
            ),
        )
        _insert_journal_fts(
            conn,
            cursor.lastrowid,
            {
                "title": f"Registered cycle {validated['cycle_index']} for "
                f"{validated['goal_run_id']}",
                "body": body,
                "target": validated["blocker_fingerprint_after"],
                "boundary": validated["registered_prediction"],
            },
        )
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()
    return EventReceipt("RECORDED", event_id, payload_sha)


def validate_insight(payload: object, *, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    if not isinstance(payload, dict) or set(payload) != INSIGHT_FIELDS:
        _fail("GOAL_INSIGHT_SCHEMA_INVALID", "insight schema is not closed")
    if payload.get("schema") != "q3_goal_insight.v1":
        _fail("GOAL_INSIGHT_SCHEMA_INVALID", "unsupported schema")
    insight_id = _nonempty_text(payload, "insight_id")
    if INSIGHT_ID_RE.fullmatch(insight_id) is None:
        _fail("GOAL_INSIGHT_SCHEMA_INVALID", "insight_id invalid")
    _iso_date(payload.get("recorded_date"), code="GOAL_INSIGHT_SCHEMA_INVALID")
    for field in (
        "title",
        "workstream",
        "target",
        "summary",
        "validation",
        "boundary",
        "next_target",
    ):
        _nonempty_text(payload, field)
    validated = dict(payload)
    validated["source_provenance"] = _validate_provenance(
        payload.get("source_provenance"), repo_root=repo_root
    )
    return validated


def _insight_semantic_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in payload.items() if key != "insight_id"}


def _render_insight(
    payload: dict[str, Any], *, payload_sha: str, semantic_sha: str
) -> str:
    provenance = "\n".join(
        f"  - `{row['path']}` · `{row['locator']}` · role `{row['role']}` · "
        f"SHA-256 `{row['sha256']}`"
        for row in payload["source_provenance"]
    )
    machine = dict(payload)
    machine["payload_sha256"] = payload_sha
    machine["semantic_sha256"] = semantic_sha
    machine_json = json.dumps(machine, ensure_ascii=False, indent=2, sort_keys=True)
    return (
        f"## Insight ({payload['recorded_date']}, {payload['workstream']}) — "
        f"{payload['title']}\n\n"
        f"- Insight ID: `{payload['insight_id']}`\n"
        f"- Target: {payload['target']}\n"
        f"- Summary: {payload['summary']}\n"
        f"- Validation: {payload['validation']}\n"
        f"- Boundary: {payload['boundary']}\n"
        f"- Next target: {payload['next_target']}\n"
        "- Provenance:\n"
        f"{provenance}\n\n"
        "```json q3_goal_insight\n"
        f"{machine_json}\n"
        "```\n"
    )


def _existing_insight_receipts(text: str) -> list[dict[str, Any]]:
    pattern = re.compile(r"```json q3_goal_insight\n(.*?)\n```", re.DOTALL)
    rows: list[dict[str, Any]] = []
    for match in pattern.finditer(text):
        try:
            row = json.loads(match.group(1))
        except json.JSONDecodeError as exc:
            _fail("GOAL_INSIGHT_LOG_INVALID", f"malformed existing insight block: {exc}")
        if not isinstance(row, dict):
            _fail("GOAL_INSIGHT_LOG_INVALID", "existing insight block is not an object")
        rows.append(row)
    return rows


def record_insight(
    payload: object,
    *,
    insights_path: Path = DEFAULT_INSIGHTS,
    repo_root: Path = REPO_ROOT,
) -> EventReceipt:
    validated = validate_insight(payload, repo_root=repo_root)
    payload_sha = _sha256_bytes(_canonical_bytes(validated))
    semantic_sha = _sha256_bytes(_canonical_bytes(_insight_semantic_payload(validated)))
    event_id = validated["insight_id"]
    rendered = _render_insight(
        validated, payload_sha=payload_sha, semantic_sha=semantic_sha
    )
    try:
        with insights_path.open("r+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            text = handle.read()
            for row in _existing_insight_receipts(text):
                if row.get("insight_id") == event_id:
                    if row.get("payload_sha256") == payload_sha:
                        return EventReceipt(
                            "ALREADY_RECORDED", event_id, payload_sha, semantic_sha
                        )
                    _fail("INSIGHT_ID_COLLISION", event_id)
                if row.get("semantic_sha256") == semantic_sha:
                    return EventReceipt(
                        "ALREADY_RECORDED",
                        str(row.get("insight_id") or event_id),
                        str(row.get("payload_sha256") or payload_sha),
                        semantic_sha,
                    )
            handle.seek(0, os.SEEK_END)
            if text and not text.endswith("\n"):
                handle.write("\n")
            if text and not text.endswith("\n\n"):
                handle.write("\n")
            handle.write(rendered)
            handle.flush()
            os.fsync(handle.fileno())
    except OSError as exc:
        _fail("GOAL_INSIGHT_WRITE_FAILED", str(exc))
    return EventReceipt("RECORDED", event_id, payload_sha, semantic_sha)


def _print_receipt(receipt: EventReceipt) -> None:
    print(json.dumps(receipt.__dict__, ensure_ascii=False, sort_keys=True))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)

    attempt = sub.add_parser("record-attempt")
    attempt.add_argument("--payload", type=Path, required=True)
    attempt.add_argument("--db", type=Path, default=DEFAULT_DB)

    insight = sub.add_parser("record-insight")
    insight.add_argument("--payload", type=Path, required=True)
    insight.add_argument("--insights", type=Path, default=DEFAULT_INSIGHTS)

    args = parser.parse_args()
    try:
        payload = _load_unique_json(args.payload)
        if args.command == "record-attempt":
            receipt = record_attempt(payload, db_path=args.db)
        else:
            receipt = record_insight(payload, insights_path=args.insights)
    except (GoalEventError, sqlite3.Error) as exc:
        print(exc, file=sys.stderr)
        return 2
    _print_receipt(receipt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
