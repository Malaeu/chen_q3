#!/usr/bin/env python3
"""Bounded read-only metadata discovery over free arXiv and Crossref APIs."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from typing import Any

SCHEMA = "q3_literature_discovery.v1"
PROVIDERS = ("arxiv", "crossref")
MAX_RESPONSE_BYTES = 512 * 1024
MAX_QUERIES = 8
MAX_RESULTS_PER_PAIR = 8
MAX_GLOBAL_CANDIDATES = 24
MAX_TITLE_CHARS = 300
MAX_EXCERPT_CHARS = 1200
MAX_QUERY_CHARS = 240
DEFAULT_TIMEOUT_SECONDS = 8.0
BOUNDARY = "UNVERIFIED_METADATA_CANDIDATES_NOT_PROOF_OR_SEMANTIC_EQUIVALENCE"


class DiscoveryIncomplete(RuntimeError):
    pass


def _canonical_hash(value: object) -> str:
    raw = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _clean(value: object, limit: int) -> str:
    return " ".join(str(value or "").split())[:limit]


def normalize_queries(queries: list[str], *, max_queries: int = MAX_QUERIES) -> list[str]:
    if not 1 <= max_queries <= MAX_QUERIES:
        raise ValueError("max_queries must be in 1..8")
    result: list[str] = []
    seen: set[str] = set()
    for raw in queries:
        query = " ".join(raw.split())
        if not query or len(query) > MAX_QUERY_CHARS:
            raise ValueError("every query must contain 1..240 characters")
        folded = query.casefold()
        if folded not in seen:
            seen.add(folded)
            result.append(query)
    if not result or len(result) > max_queries:
        raise ValueError(f"query family must contain 1..{max_queries} distinct queries")
    return result


def _fetch(
    url: str, *, timeout_seconds: float, max_bytes: int, deadline: float | None = None
) -> bytes:
    deadline = deadline if deadline is not None else time.monotonic() + timeout_seconds
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise DiscoveryIncomplete("monotonic web batch budget exhausted")
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "Q3-Supplier-Pipeline/10.1 (metadata-only)"},
    )
    chunks: list[bytes] = []
    total = 0
    with urllib.request.urlopen(request, timeout=min(timeout_seconds, remaining)) as response:
        while total <= max_bytes:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise DiscoveryIncomplete("monotonic web batch budget exhausted")
            socket_object = getattr(
                getattr(getattr(response, "fp", None), "raw", None),
                "_sock",
                None,
            )
            if socket_object is not None and hasattr(socket_object, "settimeout"):
                socket_object.settimeout(max(0.001, remaining))
            chunk = response.read(min(64 * 1024, max_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
    payload = b"".join(chunks)
    if len(payload) > max_bytes:
        raise DiscoveryIncomplete(f"HTTP response exceeds {max_bytes} bytes")
    return payload


def _arxiv(
    query: str,
    *,
    timeout_seconds: float,
    max_results: int,
    deadline: float | None = None,
) -> list[dict[str, Any]]:
    url = "https://export.arxiv.org/api/query?" + urllib.parse.urlencode(
        {"search_query": f"all:{query}", "start": 0, "max_results": max_results}
    )
    raw = _fetch(
        url,
        timeout_seconds=timeout_seconds,
        max_bytes=MAX_RESPONSE_BYTES,
        deadline=deadline,
    )
    root = ET.fromstring(raw)
    ns = {"atom": "http://www.w3.org/2005/Atom"}
    rows: list[dict[str, Any]] = []
    for entry in root.findall("atom:entry", ns)[:max_results]:
        identifier = _clean(entry.findtext("atom:id", default="", namespaces=ns), 500)
        row = {
            "provider": "arxiv",
            "provider_id": identifier.rsplit("/", 1)[-1],
            "title": _clean(entry.findtext("atom:title", default="", namespaces=ns), MAX_TITLE_CHARS),
            "excerpt": _clean(entry.findtext("atom:summary", default="", namespaces=ns), MAX_EXCERPT_CHARS),
            "url": identifier,
            "published": _clean(entry.findtext("atom:published", default="", namespaces=ns), 40),
        }
        row["metadata_sha256"] = _canonical_hash(row)
        rows.append(row)
    return rows


def _crossref(
    query: str,
    *,
    timeout_seconds: float,
    max_results: int,
    deadline: float | None = None,
) -> list[dict[str, Any]]:
    url = "https://api.crossref.org/works?" + urllib.parse.urlencode(
        {"query.bibliographic": query, "rows": max_results, "select": "DOI,title,abstract,URL,published"}
    )
    raw = _fetch(
        url,
        timeout_seconds=timeout_seconds,
        max_bytes=MAX_RESPONSE_BYTES,
        deadline=deadline,
    )
    decoded = json.loads(raw)
    items = decoded.get("message", {}).get("items", [])
    if not isinstance(items, list):
        raise DiscoveryIncomplete("Crossref response has no item list")
    rows: list[dict[str, Any]] = []
    for item in items[:max_results]:
        if not isinstance(item, dict):
            continue
        titles = item.get("title")
        title = titles[0] if isinstance(titles, list) and titles else ""
        published = item.get("published")
        row = {
            "provider": "crossref",
            "provider_id": _clean(item.get("DOI"), 300),
            "title": _clean(title, MAX_TITLE_CHARS),
            "excerpt": _clean(item.get("abstract"), MAX_EXCERPT_CHARS),
            "url": _clean(item.get("URL"), 500),
            "published": _clean(published, 200),
        }
        row["metadata_sha256"] = _canonical_hash(row)
        rows.append(row)
    return rows


def discover(
    queries: list[str],
    *,
    providers: tuple[str, ...] = PROVIDERS,
    timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
    max_queries: int = MAX_QUERIES,
    max_results_per_pair: int = MAX_RESULTS_PER_PAIR,
) -> dict[str, Any]:
    started = time.monotonic()
    observed_at = datetime.now(timezone.utc).isoformat()
    errors: list[str] = []
    try:
        normalized = normalize_queries(queries, max_queries=max_queries)
    except ValueError as exc:
        normalized = []
        errors.append(str(exc))
    if timeout_seconds <= 0 or timeout_seconds > 30:
        errors.append("timeout_seconds must be in (0,30]")
    if not 1 <= max_results_per_pair <= MAX_RESULTS_PER_PAIR:
        errors.append("max_results_per_pair must be in 1..8")
    normalized_providers = tuple(dict.fromkeys(providers))
    if not normalized_providers or any(provider not in PROVIDERS for provider in normalized_providers):
        errors.append("providers must be a nonempty subset of arxiv,crossref")

    provider_rows: list[dict[str, Any]] = []
    candidates: list[dict[str, Any]] = []
    seen_candidates: set[tuple[str, str]] = set()
    functions = {"arxiv": _arxiv, "crossref": _crossref}
    deadline = started + max(0.001, timeout_seconds)
    if not errors:
        pairs = [(provider, query) for provider in normalized_providers for query in normalized]
        outcomes: dict[tuple[str, str], tuple[list[dict[str, Any]], list[str], float]] = {}

        def fetch_pair(provider: str, query: str) -> tuple[list[dict[str, Any]], list[str], float]:
            pair_started = time.monotonic()
            try:
                rows = functions[provider](
                    query,
                    timeout_seconds=max(0.001, deadline - time.monotonic()),
                    max_results=max_results_per_pair,
                    deadline=deadline,
                )
                pair_errors: list[str] = []
            except (
                DiscoveryIncomplete,
                OSError,
                TimeoutError,
                ValueError,
                ET.ParseError,
                json.JSONDecodeError,
            ) as exc:
                rows = []
                pair_errors = [str(exc)]
            return rows, pair_errors, time.monotonic() - pair_started

        executor = concurrent.futures.ThreadPoolExecutor(max_workers=min(8, len(pairs)))
        futures = {
            executor.submit(fetch_pair, provider, query): (provider, query)
            for provider, query in pairs
        }
        try:
            for future in concurrent.futures.as_completed(
                futures, timeout=max(0.001, deadline - time.monotonic())
            ):
                outcomes[futures[future]] = future.result()
        except TimeoutError:
            pass
        finally:
            for future in futures:
                future.cancel()
            executor.shutdown(wait=False, cancel_futures=True)

        for provider, query in pairs:
            rows, pair_errors, pair_elapsed = outcomes.get(
                (provider, query),
                ([], ["monotonic web batch budget exhausted"], timeout_seconds),
            )
            accepted: list[dict[str, Any]] = []
            duplicate_count = 0
            for row in rows:
                key = (provider, str(row.get("provider_id") or row.get("url")))
                if key in seen_candidates:
                    duplicate_count += 1
                    continue
                if len(candidates) >= MAX_GLOBAL_CANDIDATES:
                    pair_errors.append("GLOBAL_CANDIDATE_CAP_REACHED")
                    break
                seen_candidates.add(key)
                bound = {**row, "query": query, "query_sha256": _sha256_text(query)}
                candidates.append(bound)
                accepted.append(bound)
            errors.extend(f"{provider}:{query}:{error}" for error in pair_errors)
            provider_rows.append(
                {
                        "provider": provider,
                        "query": query,
                        "query_sha256": _sha256_text(query),
                        "status": (
                            "INCOMPLETE"
                            if pair_errors
                            else (
                                "CANDIDATES"
                                if accepted
                                else "HITS_DEDUPED"
                                if rows and duplicate_count == len(rows)
                                else "ZERO_HITS_AT_TIME"
                            )
                        ),
                        "observed_at": observed_at,
                        "candidate_count": len(accepted),
                        "candidate_hashes": [row["metadata_sha256"] for row in accepted],
                        "errors": pair_errors,
                        "duplicate_count": duplicate_count,
                        "elapsed_seconds": round(pair_elapsed, 6),
                }
            )
    return {
        "schema": SCHEMA,
        "observed_at": observed_at,
        "queries": normalized,
        "query_family_sha256": _canonical_hash(normalized),
        "providers": list(normalized_providers),
        "provider_rows": provider_rows,
        "candidates": candidates,
        "errors": errors,
        "status": "INCOMPLETE" if errors else ("CANDIDATES" if candidates else "ZERO_HITS_AT_TIME"),
        "boundary": BOUNDARY,
        "limits": {
            "timeout_seconds": timeout_seconds,
            "max_queries": max_queries,
            "max_results_per_pair": max_results_per_pair,
            "max_response_bytes": MAX_RESPONSE_BYTES,
            "max_global_candidates": MAX_GLOBAL_CANDIDATES,
            "max_title_chars": MAX_TITLE_CHARS,
            "max_excerpt_chars": MAX_EXCERPT_CHARS,
        },
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def validate_receipt(
    payload: object,
    *,
    expected_queries: list[str],
    expected_providers: tuple[str, ...] = PROVIDERS,
) -> tuple[bool, list[str]]:
    """Validate a discovery receipt before any candidate can cross the boundary."""
    errors: list[str] = []
    if not isinstance(payload, dict):
        return False, ["LITERATURE_RECEIPT_NOT_OBJECT"]
    expected_keys = {
        "schema", "observed_at", "queries", "query_family_sha256", "providers",
        "provider_rows", "candidates", "errors", "status", "boundary", "limits",
        "elapsed_seconds",
    }
    if set(payload) != expected_keys:
        errors.append("LITERATURE_RECEIPT_SCHEMA_NOT_CLOSED")
    try:
        queries = normalize_queries(expected_queries)
    except ValueError:
        queries = []
        errors.append("LITERATURE_EXPECTED_QUERIES_INVALID")
    providers = list(dict.fromkeys(expected_providers))
    if (
        payload.get("schema") != SCHEMA
        or payload.get("queries") != queries
        or payload.get("query_family_sha256") != _canonical_hash(queries)
        or payload.get("providers") != providers
        or len(providers) != len(expected_providers)
        or any(provider not in PROVIDERS for provider in providers)
        or payload.get("boundary") != BOUNDARY
    ):
        errors.append("LITERATURE_RECEIPT_BINDING_INVALID")
    observed_at = payload.get("observed_at")
    if not isinstance(observed_at, str) or not observed_at:
        errors.append("LITERATURE_RECEIPT_OBSERVATION_INVALID")
    top_errors = payload.get("errors")
    if not isinstance(top_errors, list) or any(not isinstance(item, str) for item in top_errors):
        errors.append("LITERATURE_RECEIPT_ERRORS_INVALID")
        top_errors = []
    limits = payload.get("limits")
    if not isinstance(limits, dict) or set(limits) != {
        "timeout_seconds", "max_queries", "max_results_per_pair",
        "max_response_bytes", "max_global_candidates", "max_title_chars",
        "max_excerpt_chars",
    }:
        errors.append("LITERATURE_RECEIPT_LIMITS_INVALID")
    elif (
        not isinstance(limits.get("timeout_seconds"), (int, float))
        or not 0 < limits["timeout_seconds"] <= 30
        or limits.get("max_queries") != MAX_QUERIES
        or limits.get("max_results_per_pair") != MAX_RESULTS_PER_PAIR
        or limits.get("max_response_bytes") != MAX_RESPONSE_BYTES
        or limits.get("max_global_candidates") != MAX_GLOBAL_CANDIDATES
        or limits.get("max_title_chars") != MAX_TITLE_CHARS
        or limits.get("max_excerpt_chars") != MAX_EXCERPT_CHARS
    ):
        errors.append("LITERATURE_RECEIPT_LIMITS_DRIFT")

    raw_candidates = payload.get("candidates")
    candidates = raw_candidates if isinstance(raw_candidates, list) else []
    if not isinstance(raw_candidates, list) or len(candidates) > MAX_GLOBAL_CANDIDATES:
        errors.append("LITERATURE_RECEIPT_CANDIDATES_INVALID")
    candidate_pairs: dict[tuple[str, str], list[str]] = {}
    seen_ids: set[tuple[str, str]] = set()
    for candidate in candidates:
        if not isinstance(candidate, dict) or set(candidate) != {
            "provider", "provider_id", "title", "excerpt", "url", "published",
            "metadata_sha256", "query", "query_sha256",
        }:
            errors.append("LITERATURE_CANDIDATE_SCHEMA_INVALID")
            continue
        provider = candidate.get("provider")
        query = candidate.get("query")
        identity = (str(provider), str(candidate.get("provider_id") or candidate.get("url")))
        base = {
            key: candidate.get(key)
            for key in ("provider", "provider_id", "title", "excerpt", "url", "published")
        }
        if (
            provider not in providers
            or query not in queries
            or candidate.get("query_sha256") != _sha256_text(str(query))
            or candidate.get("metadata_sha256") != _canonical_hash(base)
            or identity in seen_ids
        ):
            errors.append("LITERATURE_CANDIDATE_BINDING_INVALID")
            continue
        seen_ids.add(identity)
        candidate_pairs.setdefault((str(provider), str(query)), []).append(
            str(candidate["metadata_sha256"])
        )

    rows = payload.get("provider_rows")
    expected_pairs = [(provider, query) for provider in providers for query in queries]
    if not isinstance(rows, list) or len(rows) != len(expected_pairs):
        errors.append("LITERATURE_PROVIDER_DENOMINATOR_INVALID")
        rows = []
    for row, pair in zip(rows, expected_pairs, strict=False):
        if not isinstance(row, dict) or set(row) != {
            "provider", "query", "query_sha256", "status", "observed_at",
            "candidate_count", "candidate_hashes", "errors", "duplicate_count",
            "elapsed_seconds",
        }:
            errors.append("LITERATURE_PROVIDER_ROW_SCHEMA_INVALID")
            continue
        pair_hashes = candidate_pairs.get(pair, [])
        row_errors = row.get("errors")
        expected_row_status: str | None = None
        if isinstance(row_errors, list):
            expected_row_status = (
                "INCOMPLETE"
                if row_errors
                else "CANDIDATES"
                if pair_hashes
                else "HITS_DEDUPED"
                if isinstance(row.get("duplicate_count"), int)
                and row.get("duplicate_count", 0) > 0
                else "ZERO_HITS_AT_TIME"
            )
        if (
            (row.get("provider"), row.get("query")) != pair
            or row.get("query_sha256") != _sha256_text(pair[1])
            or row.get("observed_at") != observed_at
            or row.get("status") not in {"INCOMPLETE", "CANDIDATES", "HITS_DEDUPED", "ZERO_HITS_AT_TIME"}
            or row.get("status") != expected_row_status
            or row.get("candidate_count") != len(pair_hashes)
            or row.get("candidate_hashes") != pair_hashes
            or not isinstance(row_errors, list)
            or any(not isinstance(item, str) for item in row_errors)
            or not isinstance(row.get("duplicate_count"), int)
            or row.get("duplicate_count", -1) < 0
        ):
            errors.append("LITERATURE_PROVIDER_ROW_BINDING_INVALID")
    flattened_errors = [
        f"{row.get('provider')}:{row.get('query')}:{item}"
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("errors"), list)
        for item in row["errors"]
        if isinstance(item, str)
    ]
    if top_errors != flattened_errors:
        errors.append("LITERATURE_RECEIPT_ERROR_LEDGER_INVALID")
    status = payload.get("status")
    expected_status = (
        "INCOMPLETE" if top_errors else "CANDIDATES" if candidates else "ZERO_HITS_AT_TIME"
    )
    if status != expected_status:
        errors.append("LITERATURE_RECEIPT_STATUS_INVALID")
    return not errors, sorted(set(errors))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query", nargs="+")
    parser.add_argument("--provider", action="append", choices=PROVIDERS)
    parser.add_argument("--timeout-seconds", type=float, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--max-queries", type=int, default=MAX_QUERIES)
    parser.add_argument("--max-results", type=int, default=MAX_RESULTS_PER_PAIR)
    args = parser.parse_args()
    payload = discover(
        args.query,
        providers=tuple(args.provider or PROVIDERS),
        timeout_seconds=args.timeout_seconds,
        max_queries=args.max_queries,
        max_results_per_pair=args.max_results,
    )
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 2 if payload["status"] == "INCOMPLETE" else 0


if __name__ == "__main__":
    raise SystemExit(main())
