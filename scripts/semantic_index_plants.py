#!/usr/bin/env python3
"""Fail-closed K1 plants for the curated q3_docs semantic index."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from q3_docs_corpus import (
    REPO_ROOT,
    corpus_snapshot,
    qmd_index_probe,
    semantic_machine_id,
)
from qmd_ops import qmd_lock, run_qmd

REPO = Path(__file__).resolve().parents[1]
DEFAULT_OUT = REPO / "q3.lean.aristotle" / ".qmd_cache" / "semantic_index_receipt.json"
COLLECTION = "q3_docs"
PLANTS = (
    ("POST_JUNE_IDENTIFICATION", "IdentificationAt", ("routeb-bus", "routeb-lamport-rh-closure")),
    ("POST_JUNE_EDGE_SLIVER", "edge-sliver", ("routeb-bus", "routeb-lamport-rh-closure")),
    ("PRE_SWITCH_STEP33", "ActiveCenteredCoeffEntryHboxCert", ("psd-step33-monitor", "q3/proofs")),
)


def resolve_qmd() -> str:
    found = shutil.which("qmd")
    if found:
        return found
    fallback = Path.home() / ".bun" / "bin" / "qmd"
    if fallback.is_file():
        return str(fallback)
    raise RuntimeError("qmd executable is missing")


def parse_results(raw: str) -> list[dict[str, Any]]:
    text = raw.strip()
    if not text or text.startswith("No results found"):
        return []
    start, end = text.find("["), text.rfind("]")
    if start < 0 or end < start:
        raise RuntimeError("qmd returned non-JSON search output")
    data = json.loads(text[start:end + 1])
    if not isinstance(data, list):
        raise RuntimeError("qmd result root is not a list")
    return [row for row in data if isinstance(row, dict)]


def result_path(row: dict[str, Any]) -> str:
    value = str(row.get("file") or row.get("path") or row.get("docid") or "")
    return value.lower().replace("_", "-")


def write_atomic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
        delete=False,
    ) as handle:
        pending = Path(handle.name)
        json.dump(payload, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(pending, path)


def run_plants(
    *,
    out: Path = DEFAULT_OUT,
    write: bool = True,
    dynamic_preflight: dict[str, Any] | None = None,
) -> dict[str, Any]:
    qmd = resolve_qmd()
    rows: list[dict[str, Any]] = []
    with qmd_lock("semantic_index_plants"):
        for plant_id, query, expected in PLANTS:
            lexical = parse_results(run_qmd(
                [qmd, "search", query, "--json", "-n", "30", "-c", COLLECTION]
            ))
            vector = parse_results(run_qmd(
                [qmd, "vsearch", query, "--json", "-n", "30", "-c", COLLECTION]
            ))
            results = lexical + vector
            paths = list(dict.fromkeys(result_path(row) for row in results))
            matched = [path for path in paths if any(token in path for token in expected)]
            status = "PASS" if matched else "FAIL_EMPTY_OR_WRONG_CORPUS"
            rows.append({
                "id": plant_id, "query": query, "status": status,
                "result_count": len(paths), "lexical_count": len(lexical),
                "vector_count": len(vector), "matched_paths": matched[:5],
            })
    status = "PASS" if all(row["status"] == "PASS" for row in rows) else "FAIL"
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO, capture_output=True, text=True,
    ).stdout.strip() or "UNKNOWN"
    corpus = corpus_snapshot(REPO_ROOT)
    qmd_index = qmd_index_probe(collection=COLLECTION)
    dynamic_queries = (
        dynamic_preflight.get("queries", [])
        if isinstance(dynamic_preflight, dict)
        else []
    )
    if isinstance(dynamic_preflight, dict) and dynamic_preflight.get("status") != "PASS":
        status = "FAIL"
    payload = {
        "schema": "q3_semantic_index_receipt.v2",
        "collection": COLLECTION,
        "authority": "MACHINE_LOCAL_RETRIEVAL_VALIDATION_NOT_PROOF",
        "machine_id": semantic_machine_id(),
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_commit": commit,
        "mode": "search_plus_vsearch",
        "status": status,
        "corpus": corpus,
        "qmd_index": qmd_index,
        "collection_file_count": qmd_index["collection_file_count"],
        "plants": rows,
        "dynamic_goal_path": (
            dynamic_preflight.get("goal_path")
            if isinstance(dynamic_preflight, dict)
            else None
        ),
        "dynamic_queries": dynamic_queries,
        "boundary": "RETRIEVAL_VALIDATION_NOT_PROOF",
    }
    if write:
        write_atomic(out, payload)
    if status != "PASS":
        failed = ", ".join(row["id"] for row in rows if row["status"] != "PASS")
        raise RuntimeError(f"SEMANTIC_INDEX_PLANT_FAILED: {failed}")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--dynamic-preflight", type=Path)
    parser.add_argument("--no-write", action="store_true")
    args = parser.parse_args()
    dynamic = None
    if args.dynamic_preflight:
        dynamic = json.loads(args.dynamic_preflight.read_text(encoding="utf-8"))
    payload = run_plants(
        out=args.out,
        write=not args.no_write,
        dynamic_preflight=dynamic,
    )
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
