#!/usr/bin/env python3
"""Build and query the disposable Q3 observability database.

The database is an atomically replaced materialized view over current sensor
JSON and the Proshka timing ledger.  It never writes knowledge.db and never
claims proof or decision authority.

    python3 orchestrator/observability.py rebuild
    python3 orchestrator/observability.py summary
    python3 orchestrator/observability.py sources
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sqlite3
import statistics
import subprocess
import tempfile
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any


REPO = Path(__file__).resolve().parents[1]
DEFAULT_DB = REPO / "q3.lean.aristotle" / "aristotle_db" / "observability.db"
SCHEMA = REPO / "q3.lean.aristotle" / "aristotle_db" / "observability_schema.sql"
STALE_AFTER_DAYS = 14

DEFAULT_SOURCES = {
    "proof_graph": REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "PROOF_GRAPH.json",
    "sorry_frontier": REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "SORRY_FRONTIER.json",
    "taint_graph": REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "TAINT_GRAPH.json",
    "taint_sources": REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "TAINT_SOURCES.json",
    "numeric_checks": REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "NUMERIC_CHECKS_REPORT.json",
    "dependency_tree": REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "DEPS_TREE_MAIN.json",
    "proshka_timing": REPO / "q3.lean.aristotle" / "ACTIVE" / "pipeline" / "PROSHKA_REASONING_TIME_LOG.md",
    "autopsy_map": REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "AUTOPSY_MAP.json",
}

JSON_SOURCE_KINDS = frozenset(DEFAULT_SOURCES) - {"proshka_timing"}


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _display_path(path: Path, repo: Path) -> str:
    try:
        return str(path.resolve().relative_to(repo.resolve()))
    except ValueError:
        return str(path)


def _git_head(repo: Path) -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo, capture_output=True, text=True,
    )
    return proc.stdout.strip() if proc.returncode == 0 else "UNKNOWN"


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _as_bool(value: Any) -> int | None:
    if value is None:
        return None
    if isinstance(value, bool):
        return int(value)
    text = str(value).strip().lower()
    if text in {"true", "yes", "1"}:
        return 1
    if text in {"false", "no", "0"}:
        return 0
    return None


def _parse_date(value: Any) -> date | None:
    if not value:
        return None
    text = str(value).strip().replace(" UTC", "+00:00")
    for candidate in (text, text[:10]):
        try:
            return datetime.fromisoformat(candidate.replace("Z", "+00:00")).date()
        except ValueError:
            try:
                return date.fromisoformat(candidate)
            except ValueError:
                continue
    return None


def _is_stale(generated_at: Any, observed_at: str) -> bool:
    source_date = _parse_date(generated_at)
    observed_date = _parse_date(observed_at)
    if source_date is None or observed_date is None:
        return True
    return (observed_date - source_date).days > STALE_AFTER_DAYS


def _decode_scalar(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] == '"':
        try:
            return str(json.loads(value))
        except json.JSONDecodeError:
            return value[1:-1]
    if len(value) >= 2 and value[0] == value[-1] == "'":
        return value[1:-1]
    return value


def parse_timing_log(text: str) -> list[dict[str, Any]]:
    """Parse top-level fields from each headed YAML block in the timing log."""
    pattern = re.compile(
        r"^### (?P<heading>.+?)\n\n```yaml\n(?P<body>.*?)\n```",
        re.MULTILINE | re.DOTALL,
    )
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for match in pattern.finditer(text):
        body = match.group("body")
        fields: dict[str, str] = {}
        notes: list[str] = []
        collecting_notes = False
        for line in body.splitlines():
            field = re.match(r"^([A-Za-z0-9_]+):(?:\s*(.*))?$", line)
            if field:
                key, raw = field.group(1), (field.group(2) or "")
                collecting_notes = key == "notes" and raw in {">", ">-", "|", "|-"}
                if collecting_notes:
                    fields[key] = ""
                else:
                    fields[key] = _decode_scalar(raw)
                continue
            if collecting_notes and (line.startswith("  ") or not line.strip()):
                notes.append(line.strip())
        if notes:
            fields["notes"] = " ".join(part for part in notes if part)
        transaction = fields.get("transaction", "").strip()
        if not transaction:
            raise ValueError(f"timing block lacks transaction: {match.group('heading')}")
        if transaction in seen:
            raise ValueError(f"duplicate timing transaction: {transaction}")
        seen.add(transaction)
        raw_seconds = fields.get("wall_seconds", "")
        lower_bound = raw_seconds.startswith(">=")
        seconds_match = re.search(r"\d+", raw_seconds)
        rows.append({
            **fields,
            "heading": match.group("heading").strip(),
            "wall_seconds_int": int(seconds_match.group()) if seconds_match else None,
            "wall_is_lower_bound": int(lower_bound),
            "source_line_start": text.count("\n", 0, match.start()) + 1,
            "raw_sha256": hashlib.sha256(body.encode("utf-8")).hexdigest(),
        })
    return rows


def _load_json_source(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"JSON root is not an object: {path}")
    return data


def _record_count(source_id: str, data: dict[str, Any]) -> int:
    if source_id == "proof_graph":
        if data.get("roots"):
            return sum(len(root.get("nodes", [])) for root in data["roots"])
        return len(data.get("nodes", []))
    if source_id == "sorry_frontier":
        return int(data.get("total_sorries", 0))
    if source_id == "taint_graph":
        return len(data.get("nodes", []))
    if source_id == "taint_sources":
        return len(data.get("roots_by_file", {}))
    if source_id == "numeric_checks":
        return len(data.get("checks", []))
    if source_id == "dependency_tree":
        if data.get("roots"):
            return sum(len(root.get("deps", [])) for root in data["roots"])
        return len(data.get("deps", []))
    if source_id == "autopsy_map":
        return len(data.get("events", []))
    return 0


def _insert_json_source(
    conn: sqlite3.Connection,
    snapshot_id: str,
    source_id: str,
    path: Path,
    data: dict[str, Any],
    generated_at: str,
    repo: Path,
) -> None:
    source_generated = data.get("generated_at")
    health_status = (
        "ZERO_COVERAGE"
        if source_id == "numeric_checks" and data.get("coverage_status") == "EMPTY_CONFIG"
        else "READY"
    )
    conn.execute(
        "INSERT INTO source_state VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
        (
            snapshot_id, source_id, "sensor_json", _display_path(path, repo),
            _sha256(path), source_generated,
            datetime.fromtimestamp(path.stat().st_mtime, timezone.utc).isoformat(timespec="seconds"),
            _record_count(source_id, data), int(_is_stale(source_generated, generated_at)),
            "PARSED", health_status,
            "No configured numeric diagnostics; zero coverage, not PASS."
            if health_status == "ZERO_COVERAGE" else None,
        ),
    )

    if source_id == "taint_graph":
        for node in data.get("nodes", []):
            file_id = node.get("id")
            if not file_id:
                continue
            conn.execute(
                "INSERT INTO file_state VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (
                    snapshot_id, file_id, node.get("module"), node.get("direct_status"),
                    node.get("propagation_status"), node.get("integrity_status"),
                    node.get("numeric_check"), node.get("intrinsic_risk"),
                    node.get("risk_score"), node.get("risk_threshold"),
                    node.get("risk_status"), _as_bool(node.get("risk_exceeds")),
                    _as_bool(node.get("is_doomed")),
                    node.get("taint_origin_count", len(node.get("taint_sources", []))),
                    json.dumps(node.get("root_ids", []), ensure_ascii=False, sort_keys=True),
                    json.dumps(node.get("unresolved_imports", []), ensure_ascii=False, sort_keys=True),
                ),
            )
            conn.executemany(
                "INSERT INTO import_edge VALUES (?,?,?)",
                [(snapshot_id, file_id, dep) for dep in node.get("dependencies", [])],
            )
            conn.executemany(
                "INSERT OR IGNORE INTO sorry_site VALUES (?,?,?)",
                [(snapshot_id, file_id, int(line)) for line in node.get("sorries", [])],
            )
            conn.executemany(
                "INSERT INTO taint_edge VALUES (?,?,?)",
                [
                    (snapshot_id, file_id, src)
                    for src in node.get("taint_sources", node.get("taint_source", []))
                ],
            )
        for root in data.get("root_status", []):
            root_id = str(root.get("root_id") or "UNKNOWN_ROOT")
            conn.execute(
                "INSERT INTO proof_root "
                "(snapshot_id,root_id,entry_file,closure_files,tainted_files) VALUES (?,?,?,?,?) "
                "ON CONFLICT(snapshot_id,root_id) DO UPDATE SET "
                "entry_file=COALESCE(excluded.entry_file,proof_root.entry_file),"
                "closure_files=COALESCE(excluded.closure_files,proof_root.closure_files),"
                "tainted_files=excluded.tainted_files",
                (
                    snapshot_id, root_id, root.get("entry_file"),
                    root.get("closure_files"), root.get("tainted_files"),
                ),
            )

    elif source_id == "sorry_frontier":
        for item in data.get("files", []):
            file_id = item.get("file")
            if not file_id:
                continue
            conn.executemany(
                "INSERT OR IGNORE INTO sorry_site VALUES (?,?,?)",
                [(snapshot_id, file_id, int(line)) for line in item.get("lines", [])],
            )
        for closure in data.get("root_closures", []):
            root_id = str(closure.get("root_id") or "UNKNOWN_ROOT")
            root_sorries = sum(
                int(item.get("count", 0)) for item in data.get("files", [])
                if root_id in item.get("root_ids", [])
            )
            conn.execute(
                "INSERT INTO proof_root "
                "(snapshot_id,root_id,entry_file,closure_files,sorry_sites) VALUES (?,?,?,?,?) "
                "ON CONFLICT(snapshot_id,root_id) DO UPDATE SET "
                "entry_file=excluded.entry_file,closure_files=excluded.closure_files,"
                "sorry_sites=excluded.sorry_sites",
                (
                    snapshot_id, root_id, closure.get("entry_file"),
                    closure.get("file_count"), root_sorries,
                ),
            )
            conn.executemany(
                "INSERT INTO root_membership VALUES (?,?,?,?)",
                [
                    (snapshot_id, root_id, member.get("file"), int(member.get("depth", 0)))
                    for member in closure.get("files", []) if member.get("file")
                ],
            )

    elif source_id == "taint_sources":
        for file_id, roots in data.get("roots_by_file", {}).items():
            conn.executemany(
                "INSERT INTO taint_root VALUES (?,?,?)",
                [(snapshot_id, file_id, str(root)) for root in roots],
            )

    elif source_id == "dependency_tree":
        roots = data.get("roots") or [{
            "id": str(data.get("root") or "UNKNOWN_ROOT"),
            "deps": data.get("deps", []),
        }]
        for root in roots:
            root_id = str(root.get("id") or "UNKNOWN_ROOT")
            deps = root.get("deps", [])
            conn.execute(
                "INSERT INTO proof_root "
                "(snapshot_id,root_id,axiom_count,project_axiom_count) VALUES (?,?,?,?) "
                "ON CONFLICT(snapshot_id,root_id) DO UPDATE SET "
                "axiom_count=excluded.axiom_count,project_axiom_count=excluded.project_axiom_count",
                (
                    snapshot_id, root_id, len(deps),
                    sum(1 for dep in deps if dep.get("classification") == "PROJECT_AXIOM"),
                ),
            )
            for dep in deps:
                name = dep.get("name")
                if not name:
                    continue
                conn.execute(
                    "INSERT INTO axiom_dependency VALUES (?,?,?,?,?,?,?,?,?)",
                    (
                        snapshot_id, root_id, name, dep.get("file"),
                        dep.get("classification", "UNKNOWN"),
                        dep.get("mapping_status", "FOUND" if dep.get("file") else "UNKNOWN"),
                        json.dumps(dep.get("source_candidates", []), ensure_ascii=False, sort_keys=True),
                        json.dumps(dep.get("axioms_in_file", []), ensure_ascii=False, sort_keys=True),
                        json.dumps(dep.get("sorries_in_file", []), ensure_ascii=False, sort_keys=True),
                    ),
                )

    elif source_id == "proof_graph":
        roots = data.get("roots") or [{
            "id": str(data.get("root") or "UNKNOWN_ROOT"),
            "nodes": data.get("nodes", []),
        }]
        for root in roots:
            root_id = str(root.get("id") or "UNKNOWN_ROOT")
            for node in root.get("nodes", []):
                node_id = node.get("id")
                if not node_id:
                    continue
                classification = node.get("classification", node.get("status", "UNKNOWN"))
                conn.execute(
                    "INSERT INTO proof_node VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    (
                        snapshot_id, root_id, node_id, classification,
                        node.get("mapping_status", "UNKNOWN"), node.get("status"),
                        node.get("file"), _as_bool(node.get("root_reachable")),
                        node.get("direct_status"), node.get("propagation_status"),
                        node.get("integrity_status"), node.get("numeric_check"),
                        node.get("risk_score"), node.get("risk_status"),
                        _as_bool(node.get("risk_exceeds")), _as_bool(node.get("is_doomed")),
                        json.dumps(node.get("alternatives", []), ensure_ascii=False, sort_keys=True),
                    ),
                )

    elif source_id == "numeric_checks":
        for index, check in enumerate(data.get("checks", []), start=1):
            check_id = check.get("id") or f"UNNAMED_{index}"
            conn.execute(
                "INSERT INTO numeric_check VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                (
                    snapshot_id, check_id,
                    check.get("evidence_class", "NUMERIC_EVIDENCE_ONLY"),
                    check.get("status"),
                    json.dumps(check.get("command"), ensure_ascii=False, sort_keys=True),
                    check.get("cwd"), check.get("exit_code"), check.get("duration_s"),
                    int(bool(check.get("timed_out"))), check.get("stdout_sha256"),
                    check.get("stderr_sha256"),
                    check.get("notes"),
                ),
            )

    elif source_id == "autopsy_map":
        if data.get("schema") != "q3_autopsy_map.v1":
            raise ValueError("autopsy map schema mismatch")
        for event in data.get("events", []):
            conn.execute(
                "INSERT INTO autopsy_event VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (
                    snapshot_id, event["id"], event["source_file"],
                    int(event["source_line"]), event["goal_id"], event["front"],
                    event["tag"], event["note"], event.get("shape"),
                    int(bool(event["structured"])),
                    int(bool(event["namewatch_eligible"])), event["raw_sha256"],
                    "DERIVED_NONCANONICAL_OBSERVABILITY",
                ),
            )
        for wall in data.get("walls", []):
            conn.execute(
                "INSERT INTO wall_state VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                (
                    snapshot_id, wall["id"], wall["tag"], wall["dropped_structure"],
                    json.dumps(wall.get("coverage_tags", []), ensure_ascii=False, sort_keys=True),
                    json.dumps(wall.get("fronts", []), ensure_ascii=False, sort_keys=True),
                    json.dumps(wall.get("goals", []), ensure_ascii=False, sort_keys=True),
                    wall.get("candidate_card"), wall["status"], int(wall["event_count"]),
                    "DERIVED_NONCANONICAL_OBSERVABILITY",
                ),
            )
        for candidate in data.get("namewatch_candidates", []):
            conn.execute(
                "INSERT INTO namewatch_candidate VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                (
                    snapshot_id, candidate["id"], candidate["tag"], candidate["shape"],
                    json.dumps(candidate["goals"], ensure_ascii=False, sort_keys=True),
                    json.dumps(candidate["fronts"], ensure_ascii=False, sort_keys=True),
                    int(candidate["event_count"]), candidate["status"], candidate["reason"],
                    int(bool(candidate["auto_promoted"])),
                    "DERIVED_NONCANONICAL_OBSERVABILITY",
                ),
            )


def _insert_timing_source(
    conn: sqlite3.Connection,
    snapshot_id: str,
    path: Path,
    generated_at: str,
    repo: Path,
) -> None:
    text = path.read_text(encoding="utf-8")
    rows = parse_timing_log(text)
    latest = max((row.get("completed_at", "") for row in rows), default="")
    conn.execute(
        "INSERT INTO source_state VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
        (
            snapshot_id, "proshka_timing", "operational_ledger",
            _display_path(path, repo), _sha256(path), latest,
            datetime.fromtimestamp(path.stat().st_mtime, timezone.utc).isoformat(timespec="seconds"),
            len(rows), 0, "PARSED", "READY",
            "append-only source; DB is a rebuildable projection",
        ),
    )
    for row in rows:
        conn.execute(
            "INSERT INTO proshka_run VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                row["transaction"], snapshot_id, row["heading"], row.get("proof_address"),
                row.get("front"), row.get("conversation_id"), row.get("request_message_id"),
                row.get("sent_at"), row.get("completed_at"), row.get("wall_seconds_int"),
                row["wall_is_lower_bound"], row.get("wall_human"),
                _as_bool(row.get("answer_now_shown")), _as_bool(row.get("answer_now_clicked")),
                row.get("primary"), row.get("status"), row.get("result_pointer"),
                row.get("notes"), _display_path(path, repo), row["source_line_start"],
                row["raw_sha256"],
            ),
        )


def rebuild_database(
    db_path: Path = DEFAULT_DB,
    *,
    repo: Path = REPO,
    sources: dict[str, Path] | None = None,
    generated_at: str | None = None,
    source_commit: str | None = None,
) -> dict[str, Any]:
    """Build a complete database beside the target, verify it, then replace atomically."""
    sources = dict(sources or DEFAULT_SOURCES)
    generated_at = generated_at or _now_iso()
    source_commit = source_commit or _git_head(repo)
    snapshot_id = "OBS_" + hashlib.sha256(
        f"{source_commit}\0{generated_at}".encode("utf-8")
    ).hexdigest()[:20]
    db_path = db_path.resolve()
    db_path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temp_name = tempfile.mkstemp(
        prefix=f".{db_path.name}.", suffix=".tmp", dir=db_path.parent
    )
    os.close(descriptor)
    temp_path = Path(temp_name)
    conn: sqlite3.Connection | None = None
    try:
        conn = sqlite3.connect(temp_path)
        conn.execute("PRAGMA foreign_keys = ON")
        conn.executescript(SCHEMA.read_text(encoding="utf-8"))
        conn.execute("BEGIN IMMEDIATE")
        conn.execute(
            "INSERT INTO snapshot VALUES (?,?,?,?,?)",
            (snapshot_id, 6, generated_at, source_commit, "COMPLETE"),
        )
        for source_id in sorted(sources):
            path = sources[source_id]
            if not path.is_file():
                conn.execute(
                    "INSERT INTO source_state VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                    (
                        snapshot_id, source_id,
                        "operational_ledger" if source_id == "proshka_timing" else "sensor_json",
                        _display_path(path, repo), None, None, None, 0, 1, "MISSING", "MISSING",
                        "source missing at rebuild",
                    ),
                )
                continue
            if source_id == "proshka_timing":
                _insert_timing_source(conn, snapshot_id, path, generated_at, repo)
            elif source_id in JSON_SOURCE_KINDS:
                _insert_json_source(
                    conn, snapshot_id, source_id, path, _load_json_source(path),
                    generated_at, repo,
                )
            else:
                raise ValueError(f"unknown observability source: {source_id}")
        conn.commit()
        verdict = conn.execute("PRAGMA integrity_check").fetchone()[0]
        if verdict != "ok":
            raise sqlite3.DatabaseError(f"integrity_check: {verdict}")
        conn.close()
        conn = None
        os.chmod(temp_path, 0o644)
        os.replace(temp_path, db_path)
    except Exception:
        if conn is not None:
            conn.rollback()
            conn.close()
        temp_path.unlink(missing_ok=True)
        raise
    return summary_data(db_path)


def _connect_ro(db_path: Path) -> sqlite3.Connection:
    if not db_path.is_file():
        raise FileNotFoundError(db_path)
    conn = sqlite3.connect(f"file:{db_path.resolve()}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    return conn


def summary_data(db_path: Path = DEFAULT_DB) -> dict[str, Any]:
    conn = _connect_ro(db_path)
    try:
        snapshot = dict(conn.execute("SELECT * FROM snapshot").fetchone())
        sources = [dict(row) for row in conn.execute(
            "SELECT source_id,record_count,stale,parse_status,health_status,source_generated_at "
            "FROM source_state ORDER BY source_id"
        )]
        taint = {row[0] or "UNKNOWN": row[1] for row in conn.execute(
            "SELECT propagation_status,COUNT(*) FROM file_state GROUP BY propagation_status"
        )}
        numeric = {row[0] or "UNKNOWN": row[1] for row in conn.execute(
            "SELECT status,COUNT(*) FROM numeric_check GROUP BY status"
        )}
        durations = [row[0] for row in conn.execute(
            "SELECT wall_seconds FROM proshka_run WHERE wall_seconds IS NOT NULL"
        )]
        slowest = [dict(row) for row in conn.execute(
            "SELECT transaction_id,front,wall_seconds,wall_is_lower_bound,status "
            "FROM proshka_run WHERE wall_seconds IS NOT NULL "
            "ORDER BY wall_seconds DESC,transaction_id LIMIT 5"
        )]
        return {
            "snapshot": snapshot,
            "sources": sources,
            "stale_sources": sum(int(row["stale"]) for row in sources),
            "degraded_sources": sum(
                1 for row in sources if row["health_status"] != "READY"
            ),
            "sorry_sites": conn.execute("SELECT COUNT(*) FROM sorry_site").fetchone()[0],
            "sorry_files": conn.execute(
                "SELECT COUNT(DISTINCT file_id) FROM sorry_site"
            ).fetchone()[0],
            "proof_roots": conn.execute("SELECT COUNT(*) FROM proof_root").fetchone()[0],
            "root_memberships": conn.execute(
                "SELECT COUNT(*) FROM root_membership"
            ).fetchone()[0],
            "file_states": conn.execute("SELECT COUNT(*) FROM file_state").fetchone()[0],
            "import_edges": conn.execute("SELECT COUNT(*) FROM import_edge").fetchone()[0],
            "taint": taint,
            "doomed_files": conn.execute(
                "SELECT COUNT(*) FROM file_state WHERE is_doomed=1"
            ).fetchone()[0],
            "axiom_dependencies": conn.execute(
                "SELECT COUNT(*) FROM axiom_dependency"
            ).fetchone()[0],
            "proof_nodes": conn.execute("SELECT COUNT(*) FROM proof_node").fetchone()[0],
            "numeric": numeric,
            "numeric_checks": conn.execute("SELECT COUNT(*) FROM numeric_check").fetchone()[0],
            "proshka_runs": conn.execute("SELECT COUNT(*) FROM proshka_run").fetchone()[0],
            "proshka_seconds_total": sum(durations),
            "proshka_seconds_mean": round(statistics.mean(durations), 1) if durations else None,
            "proshka_seconds_median": round(statistics.median(durations), 1) if durations else None,
            "proshka_lower_bounds": conn.execute(
                "SELECT COUNT(*) FROM proshka_run WHERE wall_is_lower_bound=1"
            ).fetchone()[0],
            "answer_now_clicked": conn.execute(
                "SELECT COUNT(*) FROM proshka_run WHERE answer_now_clicked=1"
            ).fetchone()[0],
            "autopsy_events": conn.execute("SELECT COUNT(*) FROM autopsy_event").fetchone()[0],
            "structured_autopsies": conn.execute(
                "SELECT COUNT(*) FROM autopsy_event WHERE structured=1"
            ).fetchone()[0],
            "wall_states": conn.execute("SELECT COUNT(*) FROM wall_state").fetchone()[0],
            "namewatch_candidates": conn.execute(
                "SELECT COUNT(*) FROM namewatch_candidate"
            ).fetchone()[0],
            "slowest_runs": slowest,
        }
    finally:
        conn.close()


def summary_lines(db_path: Path = DEFAULT_DB) -> list[str]:
    if not db_path.is_file():
        return [f"- observability database missing: `{_display_path(db_path, REPO)}`"]
    data = summary_data(db_path)
    snap = data["snapshot"]
    lines = [
        "- authority: `DERIVED_NONCANONICAL_OBSERVABILITY`",
        f"- snapshot: `{snap['id']}` at `{snap['generated_at']}` from `{snap['source_commit'][:12]}`",
        f"- sources: `{len(data['sources'])}`; stale: `{data['stale_sources']}`; "
        f"degraded: `{data['degraded_sources']}`",
        f"- sorry sites/files: `{data['sorry_sites']}` / `{data['sorry_files']}`",
        f"- proof roots/root memberships: `{data['proof_roots']}` / `{data['root_memberships']}`",
        f"- file states/import edges: `{data['file_states']}` / `{data['import_edges']}`",
        f"- taint status: `{json.dumps(data['taint'], sort_keys=True)}`; doomed: `{data['doomed_files']}`",
        f"- axiom dependencies / proof nodes: `{data['axiom_dependencies']}` / `{data['proof_nodes']}`",
        f"- numeric checks: `{data['numeric_checks']}` `{json.dumps(data['numeric'], sort_keys=True)}`",
        f"- Proshka runs: `{data['proshka_runs']}`; observed seconds total/mean/median: "
        f"`{data['proshka_seconds_total']}` / `{data['proshka_seconds_mean']}` / "
        f"`{data['proshka_seconds_median']}`; lower bounds: `{data['proshka_lower_bounds']}`",
        f"- Answer-now clicks: `{data['answer_now_clicked']}`",
        f"- AUTOPSY events/structured: `{data['autopsy_events']}` / `{data['structured_autopsies']}`; "
        f"walls/namewatch flags: `{data['wall_states']}` / `{data['namewatch_candidates']}`",
        "",
        "| Source | Records | Generated | Stale | Parse | Health |",
        "|---|---:|---|---|---|---|",
    ]
    for source in data["sources"]:
        lines.append(
            f"| `{source['source_id']}` | {source['record_count']} | "
            f"{source['source_generated_at'] or ''} | "
            f"{'YES' if source['stale'] else 'no'} | {source['parse_status']} | "
            f"{source['health_status']} |"
        )
    if data["slowest_runs"]:
        lines += ["", "### Slowest recorded Proshka runs", "", "| Transaction | Front | Seconds | Bound | Status |", "|---|---|---:|---|---|"]
        for run in data["slowest_runs"]:
            lines.append(
                f"| `{run['transaction_id']}` | {run['front'] or ''} | {run['wall_seconds']} | "
                f"{'LOWER' if run['wall_is_lower_bound'] else 'observed'} | {run['status'] or ''} |"
            )
    return lines


def _db_arg(value: str | None) -> Path:
    return Path(value or os.environ.get("Q3_OBSERVABILITY_DB_PATH", DEFAULT_DB)).resolve()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--db", help="override observability.db path")
    sub = parser.add_subparsers(dest="command", required=True)
    rebuild = sub.add_parser("rebuild")
    rebuild.add_argument("--generated-at", help="fixed ISO time for a reproducible fixture")
    sub.add_parser("summary")
    sub.add_parser("sources")
    args = parser.parse_args()
    db_path = _db_arg(args.db)

    if args.command == "rebuild":
        data = rebuild_database(db_path, generated_at=args.generated_at)
        print(f"rebuilt {db_path}")
        print(f"snapshot={data['snapshot']['id']} sources={len(data['sources'])} "
              f"stale={data['stale_sources']} degraded={data['degraded_sources']} "
              f"proshka_runs={data['proshka_runs']}")
        return 0
    if args.command == "summary":
        print("\n".join(summary_lines(db_path)))
        return 0
    data = summary_data(db_path)
    for source in data["sources"]:
        print(f"{source['source_id']:18s} records={source['record_count']:5d} "
              f"stale={source['stale']} parse={source['parse_status']} "
              f"health={source['health_status']} "
              f"generated={source['source_generated_at'] or 'UNKNOWN'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
