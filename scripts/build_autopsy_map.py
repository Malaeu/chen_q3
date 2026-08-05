#!/usr/bin/env python3
"""Build the structured AUTOPSY -> wall-map -> namewatch sensor.

The scanner is deliberately read-only over verdict/answer sources. Legacy
free-text AUTOPSY lines are visible but never guessed into the closed schema.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


REPO = Path(__file__).resolve().parents[1]
DEFAULT_ROOTS = (
    REPO / "q3.lean.aristotle" / "ACTIVE" / "requests" / "routeB_lamport_rh_closure",
)
DEFAULT_REGISTRY = REPO / "orchestrator" / "WALL_REGISTRY.json"
DEFAULT_JSON = REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "AUTOPSY_MAP.json"
DEFAULT_MD = REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "AUTOPSY_MAP.md"

AUTOPSY_TAGS_V1 = (
    "SOURCE_IDENTITY", "OBJECT_IDENTITY", "DOMAIN", "QUANTIFIER",
    "NORMALIZATION", "ORIENTATION", "LOCALIZATION", "SIGN", "PARITY",
    "MULTIPLICITY", "BOUNDEDNESS", "COUPLING", "ENDPOINT", "REGULARITY",
    "COMPACTNESS", "MEASURE_VS_ALGEBRA", "SPECTRAL_ORDERING",
    "CANCELLATION", "DEPENDENCY", "TRUST",
)
STRUCTURED_RE = re.compile(
    r"^AUTOPSY:\s*dropped=([A-Z][A-Z0-9_]*);\s*note=(\S.*)$"
)
LEGACY_RE = re.compile(r"^AUTOPSY:\s*(\S.*)$")
SHAPE_RE = re.compile(r"^shape=([A-Z][A-Z0-9_]*)(?:\s*\|\s*)(\S.*)$")
FRONT_RE = re.compile(r"^(?:front|FRONT):\s*[`\"']?([^`\"'\n]+)", re.MULTILINE)
GOAL_RE = re.compile(r"^(\d{3}(?:[A-Z0-9_.-]*))[_-]")


class AutopsyError(ValueError):
    pass


def _rel(path: Path, repo: Path) -> str:
    try:
        return path.resolve().relative_to(repo.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def _git_head(repo: Path) -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo, capture_output=True, text=True,
    )
    return proc.stdout.strip() if proc.returncode == 0 else "UNKNOWN"


def _source_generated_at(roots: Iterable[Path], registry_path: Path) -> str | None:
    paths = [registry_path]
    for root in roots:
        if root.is_file():
            paths.append(root)
        elif root.is_dir():
            paths.extend(
                path for path in root.rglob("*.md")
                if not any(part in {".git", ".lake", "_backups"} for part in path.parts)
            )
    mtimes = [path.stat().st_mtime for path in paths if path.is_file()]
    if not mtimes:
        return None
    return datetime.fromtimestamp(max(mtimes), timezone.utc).isoformat(timespec="seconds")


def _goal_id(path: Path) -> str:
    match = GOAL_RE.match(path.name)
    return match.group(1) if match else path.stem


def _front(text: str) -> str:
    match = FRONT_RE.search(text)
    return match.group(1).strip() if match else "UNCLASSIFIED_FRONT"


def parse_file(path: Path, *, repo: Path = REPO) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    front = _front(text)
    goal_id = _goal_id(path)
    rows: list[dict[str, Any]] = []
    for line_no, raw in enumerate(text.splitlines(), start=1):
        structured = STRUCTURED_RE.fullmatch(raw.strip())
        if structured:
            tag, note = structured.groups()
            if tag not in AUTOPSY_TAGS_V1:
                raise AutopsyError(
                    f"AUTOPSY_SCHEMA_INVALID {path}:{line_no}: unknown tag {tag}"
                )
            shape_match = SHAPE_RE.match(note)
            shape = shape_match.group(1) if shape_match else None
            explanation = shape_match.group(2) if shape_match else note
            event_id = hashlib.sha256(
                f"{_rel(path, repo)}\0{line_no}\0{raw}".encode("utf-8")
            ).hexdigest()[:20]
            rows.append({
                "id": f"AUT_{event_id}", "source_file": _rel(path, repo),
                "source_line": line_no, "goal_id": goal_id, "front": front,
                "tag": tag, "note": explanation, "shape": shape,
                "structured": True, "namewatch_eligible": bool(shape),
                "raw_sha256": hashlib.sha256(raw.encode("utf-8")).hexdigest(),
            })
            continue
        legacy = LEGACY_RE.fullmatch(raw.strip())
        if legacy and not legacy.group(1).startswith("dropped=<"):
            event_id = hashlib.sha256(
                f"{_rel(path, repo)}\0{line_no}\0{raw}".encode("utf-8")
            ).hexdigest()[:20]
            rows.append({
                "id": f"AUT_{event_id}", "source_file": _rel(path, repo),
                "source_line": line_no, "goal_id": goal_id, "front": front,
                "tag": "LEGACY_UNCLASSIFIED", "note": legacy.group(1),
                "shape": None, "structured": False,
                "namewatch_eligible": False,
                "raw_sha256": hashlib.sha256(raw.encode("utf-8")).hexdigest(),
            })
    return rows


def scan(roots: Iterable[Path], *, repo: Path = REPO) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    seen_paths: set[Path] = set()
    for root in roots:
        if not root.exists():
            continue
        paths = [root] if root.is_file() else sorted(root.rglob("*.md"))
        for path in paths:
            if path in seen_paths or any(part in {".git", ".lake", "_backups"} for part in path.parts):
                continue
            seen_paths.add(path)
            events.extend(parse_file(path, repo=repo))
    return sorted(events, key=lambda row: (row["source_file"], row["source_line"]))


def _registry(path: Path) -> tuple[list[dict[str, Any]], dict[str, str]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema") != "q3_wall_registry.v1" or not isinstance(data.get("walls"), list):
        raise AutopsyError("WALL_REGISTRY_INVALID")
    card_coverage = data.get("card_coverage", {})
    if not isinstance(card_coverage, dict):
        raise AutopsyError("WALL_REGISTRY_INVALID_CARD_COVERAGE")
    return data["walls"], {str(tag): str(card) for tag, card in card_coverage.items()}


def derive(
    events: list[dict[str, Any]], registry: list[dict[str, Any]],
    card_coverage: dict[str, str] | None = None,
) -> dict[str, Any]:
    card_coverage = card_coverage or {}
    registered_by_tag: dict[str, dict[str, Any]] = {}
    for wall in registry:
        for tag in wall.get("coverage_tags", []):
            registered_by_tag[tag] = wall

    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for event in events:
        if event["structured"]:
            grouped[event["tag"]].append(event)

    walls: list[dict[str, Any]] = []
    registered_tags: set[str] = set()
    for registered in sorted(registry, key=lambda row: row["id"]):
        tags = sorted(set(registered.get("coverage_tags", [])))
        registered_tags.update(tags)
        rows = [row for tag in tags for row in grouped.get(tag, [])]
        walls.append({
            "id": registered["id"], "tag": "+".join(tags),
            "coverage_tags": tags,
            "dropped_structure": registered.get("dropped_structure"),
            "goals": sorted({row["goal_id"] for row in rows}),
            "fronts": sorted({row["front"] for row in rows}),
            "event_count": len(rows), "candidate_card": None,
            "status": registered.get("status", "REGISTERED"),
        })
    for tag in sorted(set(grouped) - registered_tags):
        rows = grouped[tag]
        walls.append({
            "id": f"W_DROPPED_{tag}", "tag": tag, "coverage_tags": [tag],
            "dropped_structure": tag.lower(),
            "goals": sorted({row["goal_id"] for row in rows}),
            "fronts": sorted({row["front"] for row in rows}),
            "event_count": len(rows), "candidate_card": None,
            "status": "OBSERVED_UNRATIFIED",
        })

    by_shape: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for event in events:
        if event["namewatch_eligible"]:
            by_shape[(event["tag"], event["shape"])].append(event)
    candidates: list[dict[str, Any]] = []
    for (tag, shape), rows in sorted(by_shape.items()):
        goals = sorted({row["goal_id"] for row in rows})
        fronts = sorted({row["front"] for row in rows})
        if len(goals) < 2 or len(fronts) < 2:
            continue
        if tag in registered_by_tag or tag in card_coverage:
            continue
        candidate_id = f"NEW_FLAG_{tag}_{shape}"
        candidates.append({
            "id": candidate_id, "tag": tag, "shape": shape,
            "goals": goals, "fronts": fronts, "event_count": len(rows),
            "status": "NEW_FLAG_UNTESTED",
            "reason": "same structured dropped shape across >=2 goals and >=2 fronts; no registered wall coverage",
            "auto_promoted": False,
        })
        for wall in walls:
            if tag in wall["coverage_tags"] and wall["id"] == f"W_DROPPED_{tag}":
                wall["candidate_card"] = candidate_id
                wall["status"] = "NAMEWATCH_CANDIDATE"

    return {"events": events, "walls": walls, "namewatch_candidates": candidates}


def build(roots: Iterable[Path], registry_path: Path, *, repo: Path = REPO) -> dict[str, Any]:
    roots = tuple(roots)
    registry, card_coverage = _registry(registry_path)
    derived = derive(scan(roots, repo=repo), registry, card_coverage)
    return {
        "schema": "q3_autopsy_map.v1", "source_commit": _git_head(repo),
        "generated_at": _source_generated_at(roots, registry_path),
        "authority": "DERIVED_NONCANONICAL_OBSERVABILITY",
        "closed_tags": list(AUTOPSY_TAGS_V1), **derived,
    }


def render(data: dict[str, Any]) -> str:
    structured = sum(1 for row in data["events"] if row["structured"])
    legacy = len(data["events"]) - structured
    lines = [
        "# AUTOPSY live wall map", "",
        "Generated by `scripts/build_autopsy_map.py`; do not edit.",
        "Authority: `DERIVED_NONCANONICAL_OBSERVABILITY`.", "",
        f"- structured events: `{structured}`", f"- legacy unclassified: `{legacy}`",
        f"- walls: `{len(data['walls'])}`", f"- NEW_FLAG candidates: `{len(data['namewatch_candidates'])}`", "",
        "| Wall | Dropped structure | Fronts | Events | Candidate | Status |",
        "|---|---|---|---:|---|---|",
    ]
    for wall in data["walls"]:
        lines.append(
            f"| `{wall['id']}` | {wall['dropped_structure']} | "
            f"{', '.join(wall['fronts']) or '-'} | {wall['event_count']} | "
            f"{wall['candidate_card'] or '-'} | `{wall['status']}` |"
        )
    lines += ["", "## Namewatch", ""]
    if not data["namewatch_candidates"]:
        lines.append("- no eligible uncovered convergence")
    for candidate in data["namewatch_candidates"]:
        lines.append(
            f"- `[NEW_FLAG?] {candidate['id']}`: tag `{candidate['tag']}`, "
            f"shape `{candidate['shape']}`, goals `{len(candidate['goals'])}`, "
            f"fronts `{len(candidate['fronts'])}`; auto-promotion `false`."
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", action="append", type=Path)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--out", type=Path, default=DEFAULT_MD)
    args = parser.parse_args()
    data = build(tuple(args.root or DEFAULT_ROOTS), args.registry)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out.write_text(render(data), encoding="utf-8")
    print(
        f"autopsy events={len(data['events'])} walls={len(data['walls'])} "
        f"new_flags={len(data['namewatch_candidates'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
