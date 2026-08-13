#!/usr/bin/env python3
"""Dynamic semantic and external-Lean preflight for the selected physical goal."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import yaml

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import goal_runtime, kb_migrate_journal  # noqa: E402
from scripts import search_external_lean  # noqa: E402

ORACLE = REPO / "scripts" / "research_oracle.py"
FENCE_RE = re.compile(r"```(?:yaml|yml)\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)


def _goal_header(text: str) -> dict[str, Any]:
    match = FENCE_RE.search(text)
    if match is None:
        raise ValueError("selected goal has no YAML machine header")
    payload = yaml.safe_load(match.group(1))
    if not isinstance(payload, dict):
        raise ValueError("selected goal machine header is not a mapping")
    return payload


def selected_goal_path() -> Path:
    decision = goal_runtime.select_action(REPO / "docs" / "routeB_bus")
    if decision.action != "SELECT_EXACT_GOAL" or not decision.selected_goal_path:
        raise ValueError("no single executable physical goal")
    return Path(decision.selected_goal_path)


def derive_queries(goal_path: Path) -> list[dict[str, str]]:
    text = goal_path.read_text(encoding="utf-8")
    header = _goal_header(text)
    goal_id = str(header.get("GOAL") or "").zfill(3)
    node = str(header.get("NODE") or "").strip()
    success = str(header.get("SUCCESS") or "").strip()
    queries: list[dict[str, str]] = []
    if node:
        queries.append(
            {
                "id": "goal",
                "query": f"GOAL {goal_id} {node}",
                "expected_path_token": goal_path.name.replace("_", "-").lower(),
            }
        )
    exact_targets = list(dict.fromkeys(re.findall(r"`(Proposition\d+[A-Za-z0-9_]+)`", text)))
    if exact_targets:
        queries.append(
            {
                "id": "exact_target",
                "query": exact_targets[0],
                "expected_path_token": exact_targets[0].lower(),
            }
        )
    consumer = "Q3.RH" if "Q3.RH" in text else success
    if consumer:
        queries.append({"id": "terminal_consumer", "query": consumer})
    if success:
        queries.append({"id": "property_combination", "query": success.replace("_", " ")})
    try:
        rows, _skipped = kb_migrate_journal.parse()
        if rows:
            _index, fresh = max(
                enumerate(rows),
                key=lambda item: (str(item[1]["date"]), item[0]),
            )
            queries.append({"id": "fresh_insight", "query": str(fresh["title"])})
    except (OSError, UnicodeError, ValueError):
        pass
    deduplicated: list[dict[str, str]] = []
    seen: set[str] = set()
    for row in queries:
        folded = row["query"].casefold()
        if folded not in seen:
            seen.add(folded)
            deduplicated.append(row)
    if not 3 <= len(deduplicated) <= 5:
        raise ValueError(
            f"dynamic preflight requires 3-5 distinct queries, got {len(deduplicated)}"
        )
    return deduplicated


def _oracle_query(
    query: str, *, mode: str = "query", limit: int = 12
) -> list[dict[str, Any]]:
    command = [
        sys.executable,
        str(ORACLE),
        "query",
        query,
        "-c",
        "q3_docs",
        "-n",
        str(limit),
    ]
    if mode != "query":
        command.extend(["--mode", mode])
    proc = subprocess.run(
        command,
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=180,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or proc.stdout.strip())
    payload = json.loads(proc.stdout)
    if not isinstance(payload, list):
        raise RuntimeError("research oracle returned a non-list")
    return [row for row in payload if isinstance(row, dict)]


def _semantic_query(query: str) -> list[dict[str, Any]]:
    return _oracle_query(query)


def _lexical_query(query: str) -> list[dict[str, Any]]:
    """Fail-closed exact-name fallback for address-bearing preflight rows.

    Hybrid reciprocal-rank fusion is intentionally recall-oriented, so a
    newly added context document can displace the exact declaration file from
    its fixed top-k.  The path plant must test corpus coverage, not top-k rank
    stability.  A bounded lexical query is therefore used only when the hybrid
    result misses the declared expected path token.
    """

    return _oracle_query(query, mode="search", limit=30)


def _normalize_path(value: object) -> str:
    # qmd slugifies filename punctuation (not only underscores).  Normalize both
    # the requested filename token and returned qmd URI the same way so a real
    # hit such as ``058_..._xi.goal.md`` -> ``058-...-xi-goal.md`` is accepted.
    return re.sub(r"[^a-z0-9]+", "-", str(value or "").casefold()).strip("-")


def run_preflight(
    *,
    goal_path: Path | None = None,
    query_specs: list[dict[str, str]] | None = None,
) -> dict[str, object]:
    selected = goal_path or selected_goal_path()
    specs = query_specs or derive_queries(selected)
    rows: list[dict[str, object]] = []
    for spec in specs:
        semantic = _semantic_query(spec["query"])
        raw_token = spec.get("expected_path_token")
        token = _normalize_path(raw_token) if raw_token else None
        paths = [str(row.get("file") or row.get("path") or "") for row in semantic]
        if token is not None and not any(
            token in _normalize_path(path) for path in paths
        ):
            lexical = _lexical_query(spec["query"])
            seen_paths = set(paths)
            for row in lexical:
                path = str(row.get("file") or row.get("path") or "")
                if path not in seen_paths:
                    semantic.append(row)
                    paths.append(path)
                    seen_paths.add(path)
        expected_match = (
            any(token in _normalize_path(path) for path in paths) if token else None
        )
        external = search_external_lean.search_registry(spec["query"])
        errors = list(external.get("errors", []))
        status = "PASS"
        if not semantic or errors or (token is not None and expected_match is not True):
            status = "FAIL"
        rows.append(
            {
                "id": spec["id"],
                "query": spec["query"],
                "status": status,
                "result_count": len(semantic),
                "top_paths": paths[:8],
                "expected_path_token": token,
                "expected_path_match": expected_match,
                "external_lean": external,
            }
        )
    return {
        "schema": "q3_deep_preflight.v1",
        "goal_path": selected.relative_to(REPO).as_posix(),
        "status": "PASS" if all(row["status"] == "PASS" for row in rows) else "FAIL",
        "queries": rows,
        "boundary": "RETRIEVAL_CANDIDATES_NOT_PROOF",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--goal", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    payload = run_preflight(goal_path=args.goal)
    rendered = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0 if payload["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
