#!/usr/bin/env python3
"""Read-only term search over the enabled external Lean registry."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
ATOM_DESCRIBE = REPO / "docs" / "cartographer" / "atom_describe.py"


def _load_bases() -> list[tuple[str, Path]]:
    spec = importlib.util.spec_from_file_location("q3_external_lean_registry", ATOM_DESCRIBE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {ATOM_DESCRIBE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.load_bases()


def query_terms(query: str) -> list[str]:
    seen: set[str] = set()
    terms: list[str] = []
    for token in re.findall(r"[A-Za-z][A-Za-z0-9_'.-]{2,}", query):
        folded = token.casefold()
        if folded not in seen:
            seen.add(folded)
            terms.append(token)
    return terms


def search_registry(
    query: str,
    *,
    bases: list[tuple[str, Path]] | None = None,
    max_matches: int = 20,
) -> dict[str, object]:
    resolved = _load_bases() if bases is None else bases
    terms = query_terms(query)
    matches: list[dict[str, object]] = []
    errors: list[str] = []
    if not terms:
        return {"schema": "q3_external_lean_search.v1", "query": query,
                "bases_queried": [base_id for base_id, _ in resolved],
                "terms": [], "matches": [], "errors": []}
    pattern = "|".join(re.escape(term) for term in terms)
    for base_id, root in resolved:
        proc = subprocess.run(
            ["rg", "-n", "-i", "--no-heading", "-g", "*.lean", "-m", "3", pattern, str(root)],
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        if proc.returncode not in {0, 1}:
            errors.append(f"{base_id}: {proc.stderr.strip() or proc.stdout.strip()}")
            continue
        for raw in proc.stdout.splitlines():
            try:
                path_text, line_text, snippet = raw.split(":", 2)
                path = Path(path_text).relative_to(root).as_posix()
                line = int(line_text)
            except (ValueError, OSError):
                continue
            matches.append(
                {"base_id": base_id, "path": path, "line": line, "snippet": snippet[:240]}
            )
            if len(matches) >= max_matches:
                break
        if len(matches) >= max_matches:
            break
    return {
        "schema": "q3_external_lean_search.v1",
        "query": query,
        "bases_queried": [base_id for base_id, _ in resolved],
        "terms": terms,
        "matches": matches,
        "errors": errors,
        "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("query")
    parser.add_argument("--max-matches", type=int, default=20)
    args = parser.parse_args()
    payload = search_registry(args.query, max_matches=args.max_matches)
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 2 if payload["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
