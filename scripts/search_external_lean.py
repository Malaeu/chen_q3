#!/usr/bin/env python3
"""Read-only term search over the enabled external Lean registry."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
from pathlib import Path
from types import ModuleType

REPO = Path(__file__).resolve().parents[1]
ATOM_DESCRIBE = REPO / "docs" / "cartographer" / "atom_describe.py"


def _registry_module() -> ModuleType:
    spec = importlib.util.spec_from_file_location("q3_external_lean_registry", ATOM_DESCRIBE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {ATOM_DESCRIBE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _load_bases() -> tuple[list[str], list[tuple[str, Path]]]:
    module = _registry_module()
    return module.enabled_base_ids(), module.load_bases()


def query_terms(query: str) -> list[str]:
    seen: set[str] = set()
    terms: list[str] = []
    for token in re.findall(r"[A-Za-z][A-Za-z0-9_'.-]{2,}", query):
        folded = token.casefold()
        if folded not in seen:
            seen.add(folded)
            terms.append(token)
    if not terms:
        for token in re.findall(r"\S{3,}", query):
            cleaned = token.strip(".,;:!?()[]{}\"'`")
            folded = cleaned.casefold()
            if len(cleaned) >= 3 and folded not in seen:
                seen.add(folded)
                terms.append(cleaned)
    return terms


def search_registry(
    query: str,
    *,
    bases: list[tuple[str, Path]] | None = None,
    enabled_ids: list[str] | None = None,
    max_matches: int = 20,
) -> dict[str, object]:
    if bases is None:
        try:
            expected, resolved = _load_bases()
        except Exception as exc:
            return {
                "schema": "q3_external_lean_search.v2",
                "query": query,
                "enabled_bases": [],
                "bases_queried": [],
                "terms": query_terms(query),
                "matches": [],
                "errors": [f"registry: {exc}"],
                "boundary": "INCOMPLETE_EXTERNAL_LEAN_SEARCH",
            }
    else:
        resolved = bases
        expected = list(enabled_ids) if enabled_ids is not None else [row[0] for row in bases]
    terms = query_terms(query)
    matches: list[dict[str, object]] = []
    errors: list[str] = []
    queried: list[str] = []
    returned_ids = [base_id for base_id, _ in resolved]
    duplicates = sorted({base_id for base_id in returned_ids if returned_ids.count(base_id) > 1})
    if duplicates:
        errors.append(f"ambiguous resolved base ids: {', '.join(duplicates)}")
    missing = sorted(set(expected) - set(returned_ids))
    unexpected = sorted(set(returned_ids) - set(expected))
    if missing:
        errors.append(f"enabled bases not resolved: {', '.join(missing)}")
    if unexpected:
        errors.append(f"resolved bases not enabled: {', '.join(unexpected)}")
    if not terms:
        return {"schema": "q3_external_lean_search.v2", "query": query,
                "enabled_bases": expected, "bases_queried": [],
                "terms": [], "matches": [],
                "errors": errors + ["query has no searchable Lean identifier"],
                "boundary": "INCOMPLETE_EXTERNAL_LEAN_SEARCH"}
    pattern = "|".join(re.escape(term) for term in terms)
    for base_id, root in resolved:
        if base_id in queried:
            continue
        proc = subprocess.run(
            ["rg", "-n", "-i", "--no-heading", "-g", "*.lean", "-m", "3", pattern, str(root)],
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        queried.append(base_id)
        if proc.returncode not in {0, 1}:
            errors.append(f"{base_id}: {proc.stderr.strip() or proc.stdout.strip()}")
            continue
        if len(matches) >= max_matches:
            continue
        for raw in proc.stdout.splitlines():
            try:
                path_text, line_text, snippet = raw.split(":", 2)
                path = Path(path_text).relative_to(root).as_posix()
                line = int(line_text)
            except (ValueError, OSError):
                continue
            declaration = re.search(
                r"^\s*(?:@\[[^]]*\]\s*)?(?:private\s+|protected\s+|"
                r"noncomputable\s+)*(?:theorem|lemma|def|abbrev|axiom|structure|"
                r"class|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b",
                snippet,
            )
            query_names = {term.casefold() for term in terms}
            match_kind = "TEXT_CANDIDATE"
            declaration_name = None
            if declaration is not None:
                declaration_name = declaration.group(1)
                if (
                    declaration_name.casefold() in query_names
                    or declaration_name.rsplit(".", 1)[-1].casefold() in query_names
                ):
                    match_kind = "EXACT_DECLARATION"
            matches.append(
                {
                    "base_id": base_id,
                    "path": path,
                    "line": line,
                    "match_kind": match_kind,
                    "declaration_name": declaration_name,
                    "snippet": snippet[:240],
                }
            )
            if len(matches) >= max_matches:
                break
    return {
        "schema": "q3_external_lean_search.v2",
        "query": query,
        "enabled_bases": expected,
        "bases_queried": queried,
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
