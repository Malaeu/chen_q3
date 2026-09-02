#!/usr/bin/env python3
"""One fail-closed shelf -> properties -> direct Lean type-fit preflight."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sqlite3
import stat
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from types import ModuleType
from typing import Any

REPO = Path(__file__).resolve().parents[1]
ASK = REPO / "ask.sh"
SEARCH_EXTERNAL = REPO / "scripts" / "search_external_lean.py"
LITERATURE_DISCOVERY = REPO / "scripts" / "literature_discovery.py"
RESEARCH_ORACLE = REPO / "scripts" / "research_oracle.py"
ORACLE_QUESTIONS = REPO / "q3.lean.aristotle" / "scripts" / "oracle_questions.py"
FIT = REPO / "docs" / "cartographer" / "comparator" / "fit.py"
SCHEMA = "q3_supplier_preflight.v1"
EXTERNAL_SCHEMA = "q3_external_lean_search.v2"
PROVENANCE_CLASSES = frozenset({"SOURCE_DECLARED", "GENERATED_OR_DERIVED"})
STATUS_EXIT = {
    "CANDIDATE_ONLY": 0,
    "EXACT_FIT": 0,
    "REJECTED": 0,
    "FOREIGN_UNVERIFIED": 0,
    "COMPLETE_ABSENCE": 1,
    "INCOMPLETE": 2,
}
BOUNDARY = (
    "TEXT_OR_SEMANTIC_MATCHES_ARE_CANDIDATES;_ONLY_DIRECT_LEAN_TYPECHECK_"
    "WITH_STANDARD_AXIOMS_ESTABLISHES_EXACT_FIT"
)
SOURCE_ABSENCE_SCOPE = "SOURCE_DECLARATION_ABSENCE"
SEARCH_INTENT_SCHEMA = "q3_search_intent.v1"
SEARCH_EVIDENCE_SCHEMA = "q3_search_evidence.v1"
SEARCH_MODES = frozenset({"DISCOVERY", "ADMISSION"})
SEARCH_PURPOSES = frozenset({"RESOLVE_SUPPLIER", "REFRESH_LITERATURE"})
SEARCH_COLLECTIONS = frozenset({"q3_docs", "math_papers", "zotero_lib"})
LOCAL_CANDIDATE_PROVIDERS = frozenset(
    {
        *SEARCH_COLLECTIONS,
        "knowledge-db",
        "local-literature",
        "lean-index",
        "lean-tree",
        "specs-docs",
    }
)
NETWORK_POLICIES = frozenset({"FORBID", "ALLOW_FREE_METADATA", "AFTER_LOCAL_COMPLETE_NO_EXACT_FIT"})
ALIAS_KINDS = frozenset({"TRANSLATION", "CHARACTERIZATION", "REPRESENTATION", "DUAL", "NEGATIVE"})
SEMANTIC_FIELDS = ("object", "domain", "normalization", "quantifiers", "assumptions", "output")
MAX_QUERY_CHARS = 240
MAX_QUERY_FAMILY = 8
MAX_QMD_PROCESSES = 8
MAX_GLOBAL_CANDIDATES = 24
LOCAL_BUDGET_SECONDS = 12.0
STDOUT_MAX_BYTES = 32 * 1024
RECORDED_BLOCK_MAX_BYTES = 64 * 1024
QMD_INDEX = Path.home() / ".cache" / "qmd" / "index.sqlite"


def _load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _strict_json_object(raw: str) -> dict[str, Any]:
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError("JSON root is not an object")
    return value


def run_external(
    query: str,
    *,
    candidate: str | None,
    candidate_provenance: str | None,
    timeout: float = 20.0,
) -> dict[str, Any]:
    """Run the complete external denominator exactly once."""
    command = [
        sys.executable,
        str(SEARCH_EXTERNAL),
        query,
        "--budget-seconds",
        "15",
    ]
    if candidate is not None:
        command.extend(("--candidate", candidate))
        if candidate_provenance is not None:
            command.extend(("--candidate-provenance", candidate_provenance))
    started = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {
            "returncode": None,
            "stdout": "",
            "stderr": str(exc),
            "duration_ms": round((time.monotonic() - started) * 1000),
            "payload": None,
            "error": f"external Lean search unavailable: {exc}",
        }
    error: str | None = None
    payload: dict[str, Any] | None = None
    try:
        payload = _strict_json_object(proc.stdout)
    except (json.JSONDecodeError, ValueError) as exc:
        error = f"external Lean search emitted invalid JSON: {exc}"
    if payload is not None:
        try:
            search_external = _load_module("q3_search_external_lean", SEARCH_EXTERNAL)
            valid, validation_errors = search_external.validate_receipt(
                payload,
                expected_query=query,
                expected_candidate=candidate,
                expected_candidate_provenance=candidate_provenance,
                revalidate_current_roots=False,
            )
        except Exception as exc:
            error = f"external Lean search validator unavailable: {exc}"
        else:
            if not valid:
                error = "external Lean search receipt invalid: " + "; ".join(
                    validation_errors
                )
    if payload is not None and bool(payload.get("errors")) == (proc.returncode == 0):
        error = "external Lean search exit/status mismatch"
    return {
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "duration_ms": round((time.monotonic() - started) * 1000),
        "payload": payload,
        "error": error,
    }


def _secure_receipt(raw: str) -> Path:
    fd, name = tempfile.mkstemp(prefix="q3-external-lean-", suffix=".json")
    path = Path(name)
    try:
        os.fchmod(fd, stat.S_IRUSR | stat.S_IWUSR)
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
    except Exception:
        path.unlink(missing_ok=True)
        raise
    return path


def run_shelf(
    query: str,
    *,
    external_receipt: Path,
    candidate: str | None,
    candidate_provenance: str | None,
    timeout: int = 60,
) -> dict[str, Any]:
    command = [
        str(ASK),
        "--deep",
        "--external-receipt",
        str(external_receipt),
    ]
    if candidate is not None:
        command.extend(("--external-candidate", candidate))
    if candidate_provenance is not None:
        command.extend(("--external-candidate-provenance", candidate_provenance))
    command.append(query)
    try:
        proc = subprocess.run(
            command,
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        return {
            "status": "INCOMPLETE",
            "returncode": None,
            "transcript": "",
            "error": f"complete shelf timed out after {exc.timeout}s",
        }
    status = {0: "HITS", 1: "SHELF_ABSENCE", 2: "INCOMPLETE"}.get(
        proc.returncode, "INCOMPLETE"
    )
    transcript = "\n".join(
        part for part in (proc.stdout.rstrip(), proc.stderr.rstrip()) if part
    )
    return {
        "status": status,
        "returncode": proc.returncode,
        "transcript": transcript[-30000:],
    }


def _external_exact_results(external: dict[str, Any]) -> list[dict[str, Any]]:
    rows = external.get("base_results")
    if not isinstance(rows, list):
        return []
    return [
        row["exact_candidate"]
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("exact_candidate"), dict)
    ]


def _external_complete(external: dict[str, Any]) -> bool:
    enabled = external.get("enabled_bases")
    queried = external.get("bases_queried")
    return (
        external.get("schema") == EXTERNAL_SCHEMA
        and isinstance(enabled, list)
        and isinstance(queried, list)
        and len(enabled) == len(set(enabled))
        and set(enabled) == set(queried)
        and external.get("errors") == []
        and external.get("boundary")
        == "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE"
    )


def _external_request_bound(
    external: dict[str, Any],
    *,
    query: str,
    candidate: str | None,
    candidate_provenance: str | None,
) -> bool:
    def digest(value: str) -> str:
        return hashlib.sha256(value.encode("utf-8")).hexdigest()

    return (
        external.get("query") == query
        and external.get("query_sha256") == digest(query)
        and external.get("candidate") == candidate
        and external.get("candidate_sha256")
        == (digest(candidate) if candidate is not None else None)
        and external.get("candidate_provenance") == candidate_provenance
    )


def _external_candidate_present(external: dict[str, Any]) -> bool:
    return any(
        row.get("status") == "PRESENT" for row in _external_exact_results(external)
    )


def _external_source_absent(external: dict[str, Any]) -> bool:
    results = _external_exact_results(external)
    enabled = external.get("enabled_bases")
    return (
        _external_complete(external)
        and isinstance(enabled, list)
        and len(results) == len(enabled)
        and all(
            row.get("status") == "ABSENT"
            and row.get("boundary") == SOURCE_ABSENCE_SCOPE
            and isinstance(row.get("searched_regular_source_count"), int)
            for row in results
        )
    )


def _base_payload(
    query: str,
    candidate: str | None,
    target: str | None,
    candidate_provenance: str | None,
) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "query": query,
        "candidate_requested": candidate,
        "target_requested": target,
        "candidate_provenance": candidate_provenance,
        "shelf": None,
        "external_lean": None,
        "environment": None,
        "status": "INCOMPLETE",
        "reason": "preflight did not complete",
        "boundary": BOUNDARY,
        "candidate": None,
        "comparison": None,
        "foreign_candidate": [],
        "source_candidates": [],
        "prose_candidates_present": False,
        "source_absence_scope": None,
    }


def run_preflight(
    query: str,
    *,
    candidate: str | None = None,
    target: str | None = None,
    candidate_provenance: str | None = None,
) -> dict[str, Any]:
    payload = _base_payload(query, candidate, target, candidate_provenance)
    if candidate_provenance is not None and candidate_provenance not in PROVENANCE_CLASSES:
        payload["reason"] = "candidate provenance class is invalid"
        return payload

    external_run = run_external(
        query,
        candidate=candidate,
        candidate_provenance=candidate_provenance,
    )
    external = external_run.get("payload")
    if not isinstance(external, dict):
        payload["external_lean"] = {
            "schema": EXTERNAL_SCHEMA,
            "errors": [external_run.get("error") or "external Lean search failed"],
        }
        payload["reason"] = "enabled external-base denominator failed"
        return payload
    payload["external_lean"] = external

    receipt: Path | None = None
    try:
        receipt = _secure_receipt(str(external_run["stdout"]))
        shelf = run_shelf(
            query,
            external_receipt=receipt,
            candidate=candidate,
            candidate_provenance=candidate_provenance,
        )
    except (OSError, ValueError) as exc:
        payload["reason"] = f"secure external receipt unavailable: {exc}"
        return payload
    finally:
        if receipt is not None:
            receipt.unlink(missing_ok=True)
    payload["shelf"] = shelf

    if (
        external_run.get("error")
        or not _external_complete(external)
        or not _external_request_bound(
            external,
            query=query,
            candidate=candidate,
            candidate_provenance=candidate_provenance,
        )
    ):
        payload["reason"] = "enabled external-base denominator failed"
        return payload
    if shelf["status"] == "INCOMPLETE":
        payload["reason"] = "complete deep shelf denominator failed"
        return payload
    if candidate is None:
        if shelf["status"] == "SHELF_ABSENCE":
            payload["reason"] = "PRECISE_CANDIDATE_REQUIRED_FOR_COMPLETE_ABSENCE"
        else:
            payload["status"] = "CANDIDATE_ONLY"
            payload["reason"] = "search produced recall candidates; no precise candidate supplied"
        return payload

    try:
        fit = _load_module("q3_supplier_fit", FIT)
        environment = fit.environment_freshness()
    except Exception as exc:
        payload["environment"] = {
            "status": "INCOMPLETE",
            "errors": [f"local fit runtime unavailable: {exc}"],
        }
        payload["reason"] = "local elaborated environment could not be inspected"
        return payload
    payload["environment"] = environment
    if environment.get("status") != "PASS":
        payload["reason"] = "local elaborated environment is stale or incomplete"
        return payload

    try:
        index = fit.load_index()
        candidate_name, candidate_row = fit.resolve_declaration(candidate, index)
    except fit.FitError as exc:
        if getattr(exc, "code", "") != "DECLARATION_NOT_FOUND":
            payload["reason"] = f"candidate unresolved: {exc}"
            return payload
        if _external_candidate_present(external):
            payload["status"] = "FOREIGN_UNVERIFIED"
            payload["foreign_candidate"] = [
                row
                for row in _external_exact_results(external)
                if row.get("status") == "PRESENT"
            ]
            payload["reason"] = (
                "foreign source declaration exists outside the compatible local Lean environment"
            )
            return payload
        try:
            source_candidates = fit.source_declaration_candidates(candidate)
        except fit.FitError as source_exc:
            payload["reason"] = f"source denominator incomplete: {source_exc}"
            return payload
        payload["source_candidates"] = source_candidates
        if source_candidates:
            payload["status"] = "CANDIDATE_ONLY"
            payload["reason"] = (
                "an exact local source declaration exists outside the fresh Route B index"
            )
            return payload
        if candidate_provenance != "SOURCE_DECLARED":
            payload["reason"] = "ELABORATED_EXTERNAL_DECLARATION_LOOKUP_REQUIRED"
            return payload
        if not _external_source_absent(external):
            payload["reason"] = "external source-declaration denominator is incomplete or present"
            return payload
        payload["status"] = "COMPLETE_ABSENCE"
        payload["reason"] = (
            "SOURCE_DECLARATION_ABSENCE: the explicit declaration is absent from every "
            "validated regular Lean source denominator; this is not global elaborated or "
            "semantic absence"
        )
        payload["prose_candidates_present"] = shelf["status"] == "HITS"
        payload["source_absence_scope"] = SOURCE_ABSENCE_SCOPE
        return payload

    payload["candidate"] = fit.declaration_properties(candidate_name, candidate_row)
    if candidate_provenance != "SOURCE_DECLARED":
        payload["reason"] = "CANDIDATE_PROVENANCE_EVIDENCE_REQUIRED"
        return payload
    if target is None:
        payload["status"] = "CANDIDATE_ONLY"
        payload["reason"] = "candidate properties resolved; exact target not supplied"
        return payload

    comparison = fit.direct_type_fit(candidate, target)
    payload["comparison"] = comparison
    comparison_status = comparison.get("status")
    if comparison_status not in {"EXACT_FIT", "REJECTED", "INCOMPLETE"}:
        payload["reason"] = "direct type-fit emitted an invalid status"
        return payload
    comparison_candidate = comparison.get("candidate")
    comparison_target = comparison.get("target")
    if comparison_status in {"EXACT_FIT", "REJECTED"} and (
        not isinstance(comparison_candidate, dict)
        or comparison_candidate.get("name") != candidate
        or not isinstance(comparison_target, dict)
        or comparison_target.get("name") != target
    ):
        payload["reason"] = "direct type-fit declaration identity mismatch"
        return payload
    payload["status"] = comparison_status
    payload["reason"] = {
        "INCOMPLETE": "direct type-fit could not be completed",
        "REJECTED": "Lean or the suitability gates rejected the candidate",
        "EXACT_FIT": "exact target type accepted the candidate in a fresh harness",
    }[comparison_status]
    return payload


class SearchIntentError(ValueError):
    pass


def _canonical_hash(value: object) -> str:
    raw = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _closed_object(value: object, fields: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != fields:
        raise SearchIntentError(f"{label} must have exactly {sorted(fields)}")
    return value


def _nonempty_text(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise SearchIntentError(f"{label} must be nonempty text")
    return value.strip()


def validate_search_intent(value: object) -> dict[str, Any]:
    fields = {
        "schema", "mode", "purpose", "goal_file", "goal_sha256", "node_id",
        "source_pin", "terminal_consumer", "desired_consumer", "admission", "canonical_terms",
        "alias_hypotheses", "known_false_friends", "collections", "network_policy",
    }
    intent = _closed_object(value, fields, "search intent")
    if intent.get("schema") != SEARCH_INTENT_SCHEMA:
        raise SearchIntentError("search intent schema mismatch")
    mode = _nonempty_text(intent.get("mode"), "mode")
    purpose = _nonempty_text(intent.get("purpose"), "purpose")
    if mode not in SEARCH_MODES or purpose not in SEARCH_PURPOSES:
        raise SearchIntentError("invalid mode or purpose")
    for field in ("goal_file", "node_id", "source_pin", "terminal_consumer"):
        _nonempty_text(intent.get(field), field)
    if not isinstance(intent.get("goal_sha256"), str) or re.fullmatch(r"[0-9a-f]{64}", intent["goal_sha256"]) is None:
        raise SearchIntentError("goal_sha256 must be lowercase SHA-256")
    surface = _closed_object(intent.get("desired_consumer"), set(SEMANTIC_FIELDS), "desired_consumer")
    for field in SEMANTIC_FIELDS:
        _nonempty_text(surface.get(field), f"desired_consumer.{field}")
    canonical = intent.get("canonical_terms")
    if not isinstance(canonical, list) or not 1 <= len(canonical) <= 8:
        raise SearchIntentError("canonical_terms must contain 1..8 terms")
    if any(not isinstance(term, str) or not term.strip() for term in canonical):
        raise SearchIntentError("canonical_terms contain invalid term")
    aliases = intent.get("alias_hypotheses")
    if not isinstance(aliases, list) or len(aliases) > 8:
        raise SearchIntentError("alias_hypotheses must contain at most 8 rows")
    alias_fields = {"kind", "term", "language", "provenance", "preserves"}
    for index, row in enumerate(aliases):
        alias = _closed_object(row, alias_fields, f"alias_hypotheses[{index}]")
        if alias.get("kind") not in ALIAS_KINDS:
            raise SearchIntentError("unknown alias kind")
        for field in ("term", "language", "provenance"):
            _nonempty_text(alias.get(field), f"alias.{field}")
        preserves = alias.get("preserves")
        if not isinstance(preserves, list) or any(field not in SEMANTIC_FIELDS for field in preserves):
            raise SearchIntentError("alias preserves contains unknown semantic field")
    false_friends = intent.get("known_false_friends")
    if not isinstance(false_friends, list) or len(false_friends) > 32:
        raise SearchIntentError("known_false_friends must contain at most 32 rows")
    for index, row in enumerate(false_friends):
        friend = _closed_object(row, {"term", "reason", "source_ref"}, f"known_false_friends[{index}]")
        for field in ("term", "reason", "source_ref"):
            _nonempty_text(friend.get(field), f"false_friend.{field}")
    collections = intent.get("collections")
    if not isinstance(collections, list) or not collections or len(collections) != len(set(collections)) or any(item not in SEARCH_COLLECTIONS for item in collections):
        raise SearchIntentError("collections must be a distinct nonempty allow-listed list")
    if intent.get("network_policy") not in NETWORK_POLICIES:
        raise SearchIntentError("invalid network_policy")
    admission = intent.get("admission")
    admission_fields = {
        "theorem", "consumer", "hypothesis_port", "dependency_contract",
        "source_blob", "consumer_blob", "target_declaration", "target_type_sha256",
        "candidate_provenance",
    }
    if mode == "DISCOVERY":
        if admission is not None:
            raise SearchIntentError("DISCOVERY admission must be null")
    else:
        row = _closed_object(admission, admission_fields, "admission")
        for field in admission_fields - {"dependency_contract"}:
            _nonempty_text(row.get(field), f"admission.{field}")
        if not isinstance(row.get("dependency_contract"), dict) or not row["dependency_contract"]:
            raise SearchIntentError("admission.dependency_contract must be a nonempty object")
        if row.get("candidate_provenance") not in PROVENANCE_CLASSES:
            raise SearchIntentError("invalid admission candidate_provenance")
        if row.get("target_declaration") == row.get("theorem"):
            raise SearchIntentError("ADMISSION_TARGET_MUST_BE_DISTINCT_CONSUMER_CHALLENGE")
        if re.fullmatch(r"[0-9a-f]{64}", str(row.get("target_type_sha256"))) is None:
            raise SearchIntentError("admission.target_type_sha256 must be lowercase SHA-256")
    return json.loads(json.dumps(intent, ensure_ascii=False))


def _safe_repo_file(repo: Path, relative_value: object, *, label: str) -> Path:
    relative = _nonempty_text(relative_value, label)
    candidate = Path(relative)
    if candidate.is_absolute() or "\\" in relative or ".." in candidate.parts:
        raise SearchIntentError(f"SEARCH_INTENT_RUNTIME_PATH_INVALID:{label}")
    path = repo / candidate
    current = repo
    for part in candidate.parts:
        current = current / part
        if current.is_symlink():
            raise SearchIntentError(f"SEARCH_INTENT_RUNTIME_SYMLINK:{label}")
    if not path.is_file():
        raise SearchIntentError(f"SEARCH_INTENT_RUNTIME_FILE_MISSING:{label}")
    return path


def _goal_machine_header(path: Path) -> dict[str, str]:
    try:
        from orchestrator.startup_runtime import _goal_header

        value = _goal_header(path)
    except Exception as exc:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_GOAL_HEADER_INVALID") from exc
    return {str(key): str(item) for key, item in value.items()}


def _git_blob(path: Path) -> str:
    raw = path.read_bytes()
    header = f"blob {len(raw)}\0".encode()
    return hashlib.sha1(header + raw).hexdigest()  # noqa: S324


def validate_search_intent_runtime(
    value: object, *, repo: Path = REPO
) -> dict[str, Any]:
    """Bind a closed SearchIntent to current physical goal and v10 edge bytes."""

    intent = validate_search_intent(value)
    repo = repo.resolve()
    goal_path = _safe_repo_file(repo, intent["goal_file"], label="goal_file")
    goal_relative = goal_path.relative_to(repo).as_posix()
    if goal_path.parent != repo / "docs" / "routeB_bus":
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_GOAL_OUTSIDE_PHYSICAL_BUS")
    if hashlib.sha256(goal_path.read_bytes()).hexdigest() != intent["goal_sha256"]:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_GOAL_BLOB_DRIFT")
    header = _goal_machine_header(goal_path)
    node = header.get("EXACT_NODE") or header.get("NODE")
    source_pin = header.get("SOURCE_PIN")
    theorem = header.get("EXACT_THEOREM") or header.get("THEOREM")
    consumer = (
        header.get("EXACT_CONSUMER")
        or header.get("TERMINAL_CONSUMER")
        or header.get("CONSUMER")
    )
    if node != intent["node_id"]:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_NODE_DRIFT")
    if source_pin != intent["source_pin"]:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_SOURCE_PIN_DRIFT")
    if consumer != intent["terminal_consumer"]:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_TERMINAL_CONSUMER_DRIFT")

    admission = intent.get("admission")
    if not isinstance(admission, dict):
        return intent
    if (
        theorem != admission["theorem"]
        or consumer != admission["consumer"]
        or admission["consumer"] != intent["terminal_consumer"]
    ):
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_EXACT_EDGE_DRIFT")
    registry_path = _safe_repo_file(
        repo,
        "orchestrator/state/NODE_REGISTRY_V10.json",
        label="node_registry",
    )
    try:
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_REGISTRY_INVALID") from exc
    if not isinstance(registry, dict) or registry.get("schema") != "q3_node_registry.v10":
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_REGISTRY_INVALID")
    nodes = [
        row
        for row in registry.get("nodes", [])
        if isinstance(row, dict) and row.get("node_id") == intent["node_id"]
    ]
    edges = [
        row
        for row in registry.get("edges", [])
        if isinstance(row, dict)
        and row.get("theorem") == admission["theorem"]
        and row.get("consumer") == admission["consumer"]
    ]
    if len(nodes) != 1 or len(edges) != 1:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_REGISTRY_EDGE_AMBIGUOUS")
    node_row, edge = nodes[0], edges[0]
    source = node_row.get("source")
    port = edge.get("hypothesis_port")
    contract = admission.get("dependency_contract")
    if not isinstance(source, dict) or not isinstance(port, dict):
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_REGISTRY_EDGE_INVALID")
    challenge_declaration = port.get("challenge_declaration")
    challenge_type_sha256 = port.get("challenge_type_sha256")
    if (
        not isinstance(challenge_declaration, str)
        or not challenge_declaration
        or not isinstance(challenge_type_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", challenge_type_sha256) is None
        or challenge_declaration
        in {admission["theorem"], port.get("direct_reference"), admission["consumer"]}
    ):
        raise SearchIntentError(
            "SEARCH_INTENT_RUNTIME_CONSUMER_HYPOTHESIS_CHALLENGE_UNAVAILABLE"
        )
    if (
        admission["theorem"] not in node_row.get("theorem_ids", [])
        or admission["consumer"] not in node_row.get("terminal_consumer", [])
        or
        source.get("commit") != intent["source_pin"]
        or
        admission["source_blob"] != source.get("blob")
        or admission["consumer_blob"] != edge.get("consumer_blob")
        or admission["hypothesis_port"] != port.get("direct_reference")
        or admission["target_declaration"] != challenge_declaration
        or admission["target_type_sha256"] != challenge_type_sha256
    ):
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_ADMISSION_BLOB_OR_PORT_DRIFT")
    expected_contract = {
        "edge_id": edge.get("edge_id"),
        "theorem": edge.get("theorem"),
        "consumer": edge.get("consumer"),
        "hypothesis_port": port.get("direct_reference"),
        "target_declaration": challenge_declaration,
        "target_type_sha256": challenge_type_sha256,
    }
    if contract != expected_contract:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_DEPENDENCY_CONTRACT_DRIFT")
    source_path = _safe_repo_file(repo, source.get("path"), label="source_path")
    consumer_path = _safe_repo_file(
        repo, edge.get("consumer_path"), label="consumer_path"
    )
    if _git_blob(source_path) != admission["source_blob"]:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_SOURCE_BLOB_DRIFT")
    if _git_blob(consumer_path) != admission["consumer_blob"]:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_CONSUMER_BLOB_DRIFT")
    source_at_pin = subprocess.run(
        [
            "git",
            "rev-parse",
            f"{intent['source_pin']}:{source.get('path')}",
        ],
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    if (
        source_at_pin.returncode != 0
        or source_at_pin.stdout.strip() != admission["source_blob"]
    ):
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_SOURCE_COMMIT_BLOB_DRIFT")
    if goal_relative != intent["goal_file"]:
        raise SearchIntentError("SEARCH_INTENT_RUNTIME_GOAL_PATH_NONCANONICAL")
    return intent


def _query(parts: list[str]) -> str:
    return " ".join(" ".join(part.split()) for part in parts if part).strip()[:MAX_QUERY_CHARS]


def generate_search_queries(intent: dict[str, Any]) -> list[dict[str, str]]:
    canonical = [str(term).strip() for term in intent["canonical_terms"]]
    surface = intent["desired_consumer"]
    aliases = intent["alias_hypotheses"]
    by_kind: dict[str, list[str]] = {}
    for row in aliases:
        by_kind.setdefault(str(row["kind"]), []).append(str(row["term"]))
    proposed = [
        ("EXACT_NAME", _query(canonical[:4])),
        ("CONSUMER_SURFACE", _query([surface["object"], surface["domain"], surface["output"], surface["quantifiers"]])),
    ]
    characteristic = (by_kind.get("CHARACTERIZATION", []) + by_kind.get("TRANSLATION", []))[:2]
    representation = (by_kind.get("REPRESENTATION", []) + by_kind.get("DUAL", []))[:2]
    negative = by_kind.get("NEGATIVE", [])[:2]
    if characteristic:
        proposed.append(
            (
                "UNVERIFIED_CHARACTERIZATION_TRANSLATION",
                _query(characteristic + [surface["object"], surface["output"]]),
            )
        )
    if representation:
        proposed.append(
            (
                "UNVERIFIED_REPRESENTATION_DUAL",
                _query(representation + [surface["object"], surface["output"]]),
            )
        )
    if negative:
        proposed.append(
            ("NEGATIVE_OR_COUNTEREXAMPLE", _query(negative + [surface["object"]]))
        )
    if len(proposed) < 5:
        proposed.append(
            ("THEOREM_SHAPE", _query([surface["assumptions"], surface["output"], surface["normalization"]]))
        )
    result: list[dict[str, str]] = []
    seen: set[str] = set()
    for kind, query in proposed:
        folded = query.casefold()
        if query and folded not in seen:
            seen.add(folded)
            result.append({"kind": kind, "query": query, "query_sha256": hashlib.sha256(query.encode()).hexdigest()})
    if not 3 <= len(result) <= 5:
        raise SearchIntentError("SEARCH_INTENT_INSUFFICIENT: need 3..5 distinct queries")
    return result


def _run_local_ask(query: str, *, timeout: float) -> dict[str, Any]:
    started = time.monotonic()
    try:
        proc = subprocess.run(
            [str(ASK), "--defer-external", query], cwd=REPO,
            capture_output=True, text=True, timeout=max(0.001, timeout), check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {"provider": "ask-local-cascade", "query": query, "status": "INCOMPLETE", "errors": [str(exc)], "elapsed_seconds": round(time.monotonic() - started, 6)}
    receipt = None
    for line in proc.stdout.splitlines():
        if line.startswith("ASK_RECEIPT_JSON: "):
            try:
                receipt = json.loads(line.removeprefix("ASK_RECEIPT_JSON: "))
            except json.JSONDecodeError:
                receipt = None
    status = "INCOMPLETE"
    receipt_errors: list[str] = []
    candidates: list[dict[str, Any]] = []
    provider_rows: list[dict[str, Any]] = []
    query_sha256 = hashlib.sha256(query.encode()).hexdigest()
    if not isinstance(receipt, dict):
        receipt_errors.append("ASK_LOCAL_RECEIPT_INVALID")
    elif (
        set(receipt)
        != {
            "schema", "query", "query_sha256", "provider_rows",
            "candidate_rows", "external_lean", "boundary",
        }
        or receipt.get("schema") != "q3_ask_local_receipt.v1"
        or receipt.get("query") != query
        or receipt.get("query_sha256") != query_sha256
        or receipt.get("external_lean") != "DEFERRED"
        or receipt.get("boundary") != "LOCAL_RECEIPT_FOREIGN_INCOMPLETE"
    ):
        receipt_errors.append("ASK_LOCAL_RECEIPT_BINDING_INVALID")
    else:
        rows = receipt.get("provider_rows", [])
        if isinstance(rows, list) and rows:
            provider_rows = [row for row in rows if isinstance(row, dict)]
            if len(provider_rows) != len(rows) or any(
                row.get("query") != query
                or row.get("query_sha256") != query_sha256
                or row.get("provider") not in {"local-shelves", *SEARCH_COLLECTIONS}
                or (
                    row.get("status") == "LOCAL_ZERO_AT_CORPUS_HASH"
                    and (
                        not isinstance(row.get("corpus_sha256"), str)
                        or re.fullmatch(r"[0-9a-f]{64}", row["corpus_sha256"])
                        is None
                    )
                )
                for row in provider_rows
            ):
                receipt_errors.append("ASK_LOCAL_PROVIDER_ROWS_INVALID")
            else:
                status = str(provider_rows[0].get("status", "INCOMPLETE"))
        else:
            receipt_errors.append("ASK_LOCAL_PROVIDER_ROWS_INVALID")
        raw_candidates = receipt.get("candidate_rows", [])
        if isinstance(raw_candidates, list) and len(raw_candidates) <= 8:
            candidates = [row for row in raw_candidates if isinstance(row, dict)][:8]
            if len(candidates) != len(raw_candidates) or any(
                row.get("provider") not in LOCAL_CANDIDATE_PROVIDERS
                or row.get("query") != query
                or row.get("query_sha256") != query_sha256
                or not isinstance(row.get("metadata_sha256"), str)
                or row.get("metadata_sha256")
                != _canonical_hash(
                    {key: value for key, value in row.items() if key != "metadata_sha256"}
                )
                for row in candidates
            ):
                receipt_errors.append("ASK_LOCAL_CANDIDATE_ROWS_INVALID")
            q3_rows = [
                row for row in provider_rows if row.get("provider") == "q3_docs"
            ]
            q3_candidates = [
                row for row in candidates if row.get("provider") == "q3_docs"
            ]
            if len(q3_rows) != 1:
                receipt_errors.append("ASK_LOCAL_Q3_DOCS_IDENTITY_INVALID")
                candidates = [
                    row for row in candidates if row.get("provider") != "q3_docs"
                ]
            else:
                q3_row = q3_rows[0]
                corpus_sha256 = q3_row.get("corpus_sha256")
                collection_identity = q3_row.get("collection_identity")
                if (
                    not isinstance(corpus_sha256, str)
                    or re.fullmatch(r"[0-9a-f]{64}", corpus_sha256) is None
                    or not isinstance(collection_identity, str)
                    or re.fullmatch(r"[0-9a-f]{64}", collection_identity) is None
                    or any(
                        row.get("corpus_sha256") != corpus_sha256
                        or row.get("collection_identity") != collection_identity
                        for row in q3_candidates
                    )
                    or q3_row.get("candidate_count") != len(q3_candidates)
                    or q3_row.get("candidate_hashes")
                    != [row.get("metadata_sha256") for row in q3_candidates]
                ):
                    receipt_errors.append("ASK_LOCAL_Q3_DOCS_IDENTITY_INVALID")
                    candidates = [
                        row
                        for row in candidates
                        if row.get("provider") != "q3_docs"
                    ]
        else:
            receipt_errors.append("ASK_LOCAL_CANDIDATE_ROWS_INVALID")
    if status == "INCOMPLETE" or any(
        row.get("status") == "INCOMPLETE" for row in provider_rows
    ):
        receipt_errors.append("ASK_LOCAL_PROVIDER_INCOMPLETE")
    return {
        "provider": "ask-local-cascade", "query": query,
        "query_sha256": hashlib.sha256(query.encode()).hexdigest(),
        "status": status, "returncode": proc.returncode,
        "receipt": receipt, "provider_rows": provider_rows, "candidates": candidates,
        "output_sha256": hashlib.sha256((proc.stdout + proc.stderr).encode()).hexdigest(),
        "output_tail": (proc.stdout + proc.stderr)[-4000:],
        "errors": receipt_errors,
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def _run_qmd(query: str, collection: str, *, timeout: float) -> dict[str, Any]:
    started = time.monotonic()
    fresh_identity: dict[str, str] | None = None
    if collection == "q3_docs":
        try:
            from orchestrator.spine import validate_semantic_index

            validation = validate_semantic_index()
            corpus = validation.get("corpus")
            qmd_index = validation.get("qmd_index")
            if not isinstance(corpus, dict) or not isinstance(qmd_index, dict):
                raise ValueError("fresh q3_docs identity is malformed")
            corpus_sha256 = corpus.get("sha256")
            collection_identity = qmd_index.get("identity")
            if not isinstance(corpus_sha256, str) or not isinstance(
                collection_identity, str
            ):
                raise ValueError("fresh q3_docs identity is incomplete")
            fresh_identity = {
                "corpus_sha256": corpus_sha256,
                "collection_identity": collection_identity,
            }
        except Exception as exc:
            return {
                "provider": collection,
                "query": query,
                "status": "INCOMPLETE",
                "candidates": [],
                "errors": [f"Q3_DOCS_FRESH_IDENTITY_INVALID:{exc}"],
                "elapsed_seconds": round(time.monotonic() - started, 6),
            }
    command = [sys.executable, str(RESEARCH_ORACLE), "query", query, "-c", collection, "--mode", "search", "-n", "8", "--budget-seconds", str(max(0.001, timeout))]
    try:
        proc = subprocess.run(command, cwd=REPO, capture_output=True, text=True, timeout=max(0.001, timeout), check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {"provider": collection, "query": query, "status": "INCOMPLETE", "candidates": [], "errors": [str(exc)], "elapsed_seconds": round(time.monotonic() - started, 6)}
    try:
        rows = json.loads(proc.stdout)
        if not isinstance(rows, list):
            raise ValueError("qmd JSON root is not a list")
    except (json.JSONDecodeError, ValueError) as exc:
        rows = []
        errors = [str(exc)]
    else:
        errors = [] if proc.returncode == 0 else [proc.stderr.strip() or f"exit {proc.returncode}"]
    candidates = []
    for row in rows[:8]:
        if isinstance(row, dict):
            candidate = {
                "provider": collection, "query": query,
                "provider_id": str(row.get("docid") or row.get("file") or "")[:500],
                "title": " ".join(str(row.get("title") or "").split())[:300],
                "excerpt": " ".join(str(row.get("snippet") or "").split())[:1200],
                "url": str(row.get("file") or "")[:500],
            }
            if fresh_identity is not None:
                candidate.update(fresh_identity)
            candidate["metadata_sha256"] = _canonical_hash(candidate)
            candidates.append(candidate)
    corpus_sha256 = (
        fresh_identity["corpus_sha256"]
        if fresh_identity is not None
        else _qmd_collection_hash(collection)
    )
    if not errors and not candidates and corpus_sha256 is None:
        errors.append("LOCAL_ZERO_CORPUS_HASH_UNAVAILABLE")
    return {
        "provider": collection, "query": query,
        "query_sha256": hashlib.sha256(query.encode()).hexdigest(),
        "status": "INCOMPLETE" if errors else ("CANDIDATES" if candidates else "LOCAL_ZERO_AT_CORPUS_HASH"),
        "corpus_sha256": corpus_sha256,
        "collection_identity": (
            fresh_identity["collection_identity"] if fresh_identity is not None else None
        ),
        "candidates": candidates, "errors": errors,
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def _qmd_collection_hash(collection: str) -> str | None:
    """Hash the exact active qmd document identities used by a collection."""
    if not QMD_INDEX.is_file():
        return None
    try:
        connection = sqlite3.connect(f"file:{QMD_INDEX}?mode=ro", uri=True)
        rows = connection.execute(
            "SELECT path, title, hash FROM documents "
            "WHERE collection = ? AND active = 1 ORDER BY path",
            (collection,),
        ).fetchall()
        connection.close()
    except sqlite3.Error:
        return None
    if not rows:
        return None
    documents: list[dict[str, str]] = []
    for path, title, content_hash in rows:
        if not all(isinstance(value, str) for value in (path, title, content_hash)):
            return None
        documents.append({"path": path, "title": title, "content_hash": content_hash})
    return _canonical_hash({"collection": collection, "documents": documents})


def _local_exact_fit(intent: dict[str, Any]) -> dict[str, Any] | None:
    if intent["mode"] != "ADMISSION":
        return None
    admission = intent["admission"]
    try:
        fit = _load_module("q3_supplier_fit_search_intent", FIT)
        environment = fit.environment_freshness()
        if environment.get("status") != "PASS":
            return {"status": "INCOMPLETE", "reason": "local elaborated environment is stale", "environment": environment}
        index = fit.load_index()
        candidate_name, candidate_row = fit.resolve_declaration(admission["theorem"], index)
        target_name, target_row = fit.resolve_declaration(
            admission["target_declaration"], index
        )
        if candidate_name != admission["theorem"] or target_name != admission["target_declaration"]:
            return {
                "status": "INCOMPLETE",
                "reason": "ADMISSION_ELABORATED_DECLARATION_IDENTITY_MISMATCH",
            }
        target_type_identity = _canonical_hash(
            {"name": target_name, "type": target_row.get("type")}
        )
        if target_type_identity != admission["target_type_sha256"]:
            return {
                "status": "INCOMPLETE",
                "reason": "ADMISSION_ELABORATED_TARGET_TYPE_IDENTITY_MISMATCH",
            }
        candidate = fit.declaration_properties(candidate_name, candidate_row)
        comparison = fit.direct_type_fit(candidate_name, target_name)
    except Exception as exc:
        return {"status": "INCOMPLETE", "reason": str(exc)}
    status = comparison.get("status")
    comparison_candidate = comparison.get("candidate")
    comparison_target = comparison.get("target")
    if status in {"EXACT_FIT", "REJECTED"} and (
        not isinstance(comparison_candidate, dict)
        or comparison_candidate.get("name") != admission["theorem"]
        or not isinstance(comparison_target, dict)
        or comparison_target.get("name") != admission["target_declaration"]
    ):
        return {
            "status": "INCOMPLETE",
            "reason": "ADMISSION_ELABORATED_COMPARISON_IDENTITY_MISMATCH",
        }
    if admission["candidate_provenance"] != "SOURCE_DECLARED" and status == "EXACT_FIT":
        return {"status": "INCOMPLETE", "reason": "CANDIDATE_PROVENANCE_EVIDENCE_REQUIRED"}
    return {"status": status, "candidate": candidate, "comparison": comparison}


def _knowledge_aliases(surface_terms: set[str]) -> list[dict[str, str]]:
    database = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"
    rows: list[tuple[str, str]] = []
    if database.is_file():
        try:
            connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
            rows.extend((str(row[0]), "search_term:strong") for row in connection.execute("SELECT DISTINCT term FROM search_term WHERE verdict='strong' ORDER BY term LIMIT 200"))
            rows.extend((str(row[0]), "kill_alias") for row in connection.execute("SELECT DISTINCT alias FROM kill_alias ORDER BY alias LIMIT 200"))
            connection.close()
        except sqlite3.Error:
            pass
    translation = REPO / "docs" / "cartographer" / "TRANSLATION_DICTIONARY.md"
    if translation.is_file():
        for line in translation.read_text(encoding="utf-8", errors="ignore").splitlines():
            folded = line.casefold()
            if any(token in folded for token in surface_terms):
                rows.extend((term, "translation_dictionary") for term in re.findall(r"`([^`]{2,120})`", line)[:4])
    equivalence = REPO / "q3.lean.aristotle" / "ACTIVE" / "pipeline" / "EQUIVALENCE_GRAPH.json"
    if equivalence.is_file():
        try:
            graph = json.loads(equivalence.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            graph = None

        def strings(value: object):
            if isinstance(value, str):
                yield value
            elif isinstance(value, list):
                for item in value:
                    yield from strings(item)
            elif isinstance(value, dict):
                for item in value.values():
                    yield from strings(item)

        for value in list(strings(graph))[:500]:
            folded = value.casefold()
            if 2 <= len(value) <= 120 and any(token in folded for token in surface_terms):
                rows.append((value, "equivalence_graph:speculative"))
    result = []
    for term, provenance in rows:
        folded = term.casefold()
        if any(token in folded for token in surface_terms):
            result.append({"kind": "UNVERIFIED_ALIAS_HYPOTHESIS", "term": term[:120], "provenance": provenance})
    return result


def _feedback_aliases(intent: dict[str, Any], candidates: list[dict[str, Any]]) -> list[dict[str, str]]:
    surface = intent["desired_consumer"]
    word_pattern = r"[^\W\d_][\w-]{2,}"
    anchors = {
        token.casefold()
        for field in ("object", "domain", "output")
        for token in re.findall(word_pattern, surface[field], flags=re.UNICODE)
    }
    stop = {
        "theorem", "lemma", "proof", "using", "with", "from", "that", "this",
        "paper", "study", "result", "теорема", "лемма", "доказательство",
        "используя", "результат", "статья", "und", "oder", "satz", "beweis",
    }
    scored: dict[str, tuple[int, str]] = {}
    for row in candidates:
        text = f"{row.get('title', '')} {row.get('excerpt', '')}"
        words = re.findall(word_pattern, text, flags=re.UNICODE)
        for width in (2, 3, 4):
            for index in range(max(0, len(words) - width + 1)):
                phrase_words = words[index:index + width]
                folded_words = {word.casefold() for word in phrase_words}
                if folded_words & stop or len(folded_words) < 2:
                    continue
                phrase = " ".join(phrase_words)[:120]
                score = len(folded_words & anchors) * 10 + width
                current = scored.get(phrase.casefold())
                if current is None or score > current[0]:
                    scored[phrase.casefold()] = (score, str(row.get("metadata_sha256", "")))
    combined = _knowledge_aliases(anchors)
    for phrase, (score, provenance) in sorted(scored.items(), key=lambda item: (-item[1][0], item[0])):
        combined.append({"kind": "UNVERIFIED_ALIAS_HYPOTHESIS", "term": phrase, "provenance": f"candidate:{provenance}"})
    deduped: list[dict[str, str]] = []
    seen: set[str] = set()
    for row in combined:
        folded = row["term"].casefold()
        if folded not in seen:
            seen.add(folded)
            deduped.append(row)
        if len(deduped) == 8:
            break
    return deduped


def _dedupe_candidates(rows: list[dict[str, Any]], false_friends: list[dict[str, str]]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    seen: set[tuple[str, str]] = set()
    friend_terms = [row["term"].casefold() for row in false_friends]
    for row in rows:
        key = (str(row.get("provider")), str(row.get("provider_id") or row.get("url") or row.get("metadata_sha256")))
        if key in seen:
            continue
        seen.add(key)
        text = f"{row.get('title', '')} {row.get('excerpt', '')}".casefold()
        result.append({**row, "classification": "KNOWN_FALSE_FRIEND" if any(term in text for term in friend_terms) else "UNVERIFIED_CANDIDATE"})
        if len(result) == MAX_GLOBAL_CANDIDATES:
            break
    return result


def run_search_intent(intent_value: object) -> dict[str, Any]:
    started = time.monotonic()
    observed_at = datetime.now(timezone.utc).isoformat()
    errors: list[str] = []
    try:
        intent = validate_search_intent(intent_value)
        initial = generate_search_queries(intent)
    except SearchIntentError as exc:
        return {"schema": SEARCH_EVIDENCE_SCHEMA, "status": "INCOMPLETE", "decision": "INCOMPLETE", "errors": [str(exc)], "boundary": BOUNDARY}
    intent_id = _canonical_hash(intent)
    deadline = started + LOCAL_BUDGET_SECONDS
    ledger: list[dict[str, Any]] = []
    all_candidates: list[dict[str, Any]] = []
    canonical_query = initial[0]["query"]
    remaining = deadline - time.monotonic()
    local_ask = _run_local_ask(canonical_query, timeout=remaining)
    ledger.append(local_ask)
    all_candidates.extend(local_ask.get("candidates", []))
    if local_ask.get("errors"):
        errors.extend(str(item) for item in local_ask["errors"])
    exact_fit = _local_exact_fit(intent)
    if (
        not errors
        and exact_fit
        and exact_fit.get("status") == "EXACT_FIT"
        and intent["purpose"] == "RESOLVE_SUPPLIER"
    ):
        return {
            "schema": SEARCH_EVIDENCE_SCHEMA, "intent_id": intent_id,
            "observed_at": observed_at,
            "mode": intent["mode"], "purpose": intent["purpose"],
            "status": "PASS", "decision": "EXACT_FIT", "queries": initial,
            "provider_ledger": ledger, "literature": [], "external_lean": None,
            "candidates": [], "alias_hypotheses": [],
            "exact_fit": exact_fit, "errors": errors,
            "metrics": {"qmd_subprocesses": 0, "external_lean_batches": 0, "web_batches": 0, "elapsed_seconds": round(time.monotonic() - started, 6)},
            "boundary": BOUNDARY,
        }
    qmd_count = 0
    executed_pairs = {("ask-local-cascade", canonical_query.casefold())}
    for row in local_ask.get("provider_rows", []):
        provider = row.get("provider")
        query = row.get("query")
        if provider in SEARCH_COLLECTIONS and isinstance(query, str):
            executed_pairs.add((str(provider), query.casefold()))
    primary = intent["collections"][0]
    requested_qmd_pairs = {
        *((primary, row["query"].casefold()) for row in initial),
        *((collection, canonical_query.casefold()) for collection in intent["collections"][1:]),
    }
    scheduled_pairs = [
        (collection, query_row)
        for query_row in initial
        for collection in intent["collections"]
        if (collection, query_row["query"].casefold()) in requested_qmd_pairs
    ]
    for collection, query_row in scheduled_pairs:
        if qmd_count >= MAX_QMD_PROCESSES:
            break
        pair = (collection, query_row["query"].casefold())
        if pair in executed_pairs:
            continue
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            errors.append("LOCAL_MONOTONIC_BUDGET_EXHAUSTED")
            break
        receipt = _run_qmd(query_row["query"], collection, timeout=remaining)
        executed_pairs.add(pair)
        qmd_count += 1
        ledger.append(receipt)
        all_candidates.extend(receipt.get("candidates", []))
        if receipt.get("errors"):
            errors.extend(str(item) for item in receipt["errors"])
    executed_qmd_pairs = {
        pair for pair in executed_pairs if pair[0] in SEARCH_COLLECTIONS
    }
    if executed_qmd_pairs != requested_qmd_pairs:
        errors.append("QMD_PROCESS_CAP_OR_BUDGET_REACHED")

    literature_module = _load_module("q3_literature_discovery", LITERATURE_DISCOVERY)
    local_complete = not errors and executed_qmd_pairs == requested_qmd_pairs
    network_allowed = intent["network_policy"] == "ALLOW_FREE_METADATA" or (
        intent["network_policy"] == "AFTER_LOCAL_COMPLETE_NO_EXACT_FIT"
        and local_complete
        and (exact_fit is None or exact_fit.get("status") != "EXACT_FIT")
    )
    literature_receipts: list[dict[str, Any]] = []
    web_batches = 0
    if network_allowed:
        first_queries = [row["query"] for row in initial]
        first = literature_module.discover(first_queries)
        literature_receipts.append(first)
        web_batches += 1
        valid_literature, literature_errors = literature_module.validate_receipt(
            first, expected_queries=first_queries
        )
        if valid_literature:
            all_candidates.extend(first.get("candidates", []))
        else:
            errors.extend(literature_errors)
        if first.get("status") == "INCOMPLETE":
            errors.extend(str(item) for item in first.get("errors", []))

    feedback = _feedback_aliases(intent, all_candidates)
    final_queries = list(initial)
    known = {row["query"].casefold() for row in final_queries}
    for alias in feedback:
        query = _query([alias["term"], intent["desired_consumer"]["output"]])
        if query.casefold() not in known:
            known.add(query.casefold())
            final_queries.append({"kind": "UNVERIFIED_ALIAS_HYPOTHESIS", "query": query, "query_sha256": hashlib.sha256(query.encode()).hexdigest()})
        if len(final_queries) == MAX_QUERY_FAMILY:
            break
    if network_allowed and len(final_queries) > len(initial):
        feedback_queries = [row["query"] for row in final_queries[len(initial):]]
        second = literature_module.discover(feedback_queries)
        literature_receipts.append(second)
        web_batches += 1
        valid_literature, literature_errors = literature_module.validate_receipt(
            second, expected_queries=feedback_queries
        )
        if valid_literature:
            all_candidates.extend(second.get("candidates", []))
        else:
            errors.extend(literature_errors)
        if second.get("status") == "INCOMPLETE":
            errors.extend(str(item) for item in second.get("errors", []))

    external_module = _load_module("q3_external_lean_batch", SEARCH_EXTERNAL)
    admission = intent.get("admission") or {}
    local_spent = sum(
        float(row.get("elapsed_seconds", 0.0))
        for row in ledger
        if isinstance(row, dict)
    )
    external = external_module.search_registry_batch(
        [row["query"] for row in final_queries],
        candidate=admission.get("theorem"),
        candidate_provenance=admission.get("candidate_provenance"),
        budget_seconds=max(0.001, min(15.0, LOCAL_BUDGET_SECONDS - local_spent)),
        max_matches_per_query=8,
    )
    valid_external, external_errors = external_module.validate_batch_receipt(
        external,
        expected_queries=[row["query"] for row in final_queries],
        expected_candidate=admission.get("theorem"),
        expected_candidate_provenance=admission.get("candidate_provenance"),
    )
    if not valid_external:
        errors.extend(external_errors)
    for query_row in external.get("queries", []):
        for row in query_row.get("matches", []):
            candidate = {
                "provider": "external_lean", "query": query_row.get("query"),
                "provider_id": f"{row.get('base_id')}:{row.get('path')}:{row.get('line')}",
                "title": str(row.get("declaration_name") or "")[:300],
                "excerpt": str(row.get("snippet") or "")[:1200],
                "url": str(row.get("path") or "")[:500],
            }
            candidate["metadata_sha256"] = _canonical_hash(candidate)
            all_candidates.append(candidate)
    candidates = _dedupe_candidates(all_candidates, intent["known_false_friends"])
    unique_candidate_keys = {
        (str(row.get("provider")), str(row.get("provider_id") or row.get("url") or row.get("metadata_sha256")))
        for row in all_candidates
    }
    if len(unique_candidate_keys) > MAX_GLOBAL_CANDIDATES:
        errors.append("GLOBAL_CANDIDATE_CAP_REACHED")
    decision = "CANDIDATES" if candidates else "LOCAL_COMPLETE_NO_EXACT_FIT"
    if errors:
        status = "INCOMPLETE"
        decision = "INCOMPLETE"
    else:
        status = "PASS"
    return {
        "schema": SEARCH_EVIDENCE_SCHEMA, "intent_id": intent_id,
        "observed_at": observed_at,
        "mode": intent["mode"], "purpose": intent["purpose"],
        "status": status, "decision": decision, "queries": final_queries,
        "provider_ledger": ledger, "literature": literature_receipts,
        "external_lean": external, "candidates": candidates,
        "alias_hypotheses": feedback, "exact_fit": exact_fit,
        "errors": sorted(set(errors)),
        "metrics": {"qmd_subprocesses": qmd_count, "external_lean_batches": 1, "web_batches": web_batches, "elapsed_seconds": round(time.monotonic() - started, 6)},
        "boundary": BOUNDARY,
    }


def bounded_evidence_json(payload: dict[str, Any]) -> str:
    compact = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    if len(compact.encode("utf-8")) <= STDOUT_MAX_BYTES:
        return compact
    reduced = json.loads(json.dumps(payload, ensure_ascii=False))
    for candidate in reduced.get("candidates", []):
        candidate["excerpt"] = ""
    reduced["provider_ledger"] = [
        {key: row.get(key) for key in ("provider", "query", "query_sha256", "status", "errors", "elapsed_seconds")}
        for row in reduced.get("provider_ledger", [])
    ]
    reduced["errors"] = sorted(set([*reduced.get("errors", []), "STDOUT_BUDGET_COMPACTION"]))
    reduced["status"] = "INCOMPLETE"
    reduced["decision"] = "INCOMPLETE"
    compact = json.dumps(reduced, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    if len(compact.encode("utf-8")) > STDOUT_MAX_BYTES:
        reduced["candidates"] = reduced.get("candidates", [])[:8]
        reduced["literature"] = []
        reduced["external_lean"] = {"schema": "q3_external_lean_search.v3", "status": "OMITTED_FROM_STDOUT_BUDGET"}
        compact = json.dumps(reduced, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    if len(compact.encode("utf-8")) > STDOUT_MAX_BYTES:
        raise RuntimeError("SEARCH_EVIDENCE_STDOUT_BUDGET_EXCEEDED")
    return compact


def _validate_owned_oracle_card(oracle_card: str, owned_paths: list[str]) -> Path:
    card_value = Path(oracle_card)
    if card_value.is_absolute():
        try:
            card_relative = card_value.relative_to(REPO).as_posix()
        except ValueError as exc:
            raise SearchIntentError("SEARCH_EVIDENCE_CARD_OUTSIDE_REPO") from exc
    else:
        card_relative = card_value.as_posix()
    card_path = _safe_repo_file(REPO, card_relative, label="oracle_card")
    normalized_owned: set[str] = set()
    for value in owned_paths:
        candidate = Path(value)
        if candidate.is_absolute():
            try:
                normalized_owned.add(candidate.relative_to(REPO).as_posix())
            except ValueError as exc:
                raise SearchIntentError("SEARCH_EVIDENCE_OWNED_PATH_OUTSIDE_REPO") from exc
        elif "\\" in value or ".." in candidate.parts:
            raise SearchIntentError("SEARCH_EVIDENCE_OWNED_PATH_INVALID")
        else:
            normalized_owned.add(candidate.as_posix())
    if card_relative not in normalized_owned:
        raise SearchIntentError("SEARCH_EVIDENCE_CARD_NOT_EXACTLY_OWNED")
    return card_path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query")
    parser.add_argument("--candidate")
    parser.add_argument("--target")
    parser.add_argument("--candidate-provenance", choices=sorted(PROVENANCE_CLASSES))
    parser.add_argument("--search-intent", type=Path)
    parser.add_argument("--record-evidence", action="store_true")
    parser.add_argument("--oracle-card")
    parser.add_argument("--owned-path", action="append", default=[])
    parser.add_argument("--inherited-writer-lock-fd", type=int)
    args = parser.parse_args()
    if args.search_intent is not None:
        if args.record_evidence and args.inherited_writer_lock_fd is None:
            parser.error("--record-evidence requires --inherited-writer-lock-fd")
        if args.query or args.candidate or args.target or args.candidate_provenance:
            parser.error("--search-intent cannot be combined with legacy scalar options")
        intent: object | None = None
        try:
            intent = validate_search_intent_runtime(
                json.loads(args.search_intent.read_text(encoding="utf-8"))
            )
        except (OSError, json.JSONDecodeError, SearchIntentError) as exc:
            payload = {"schema": SEARCH_EVIDENCE_SCHEMA, "status": "INCOMPLETE", "decision": "INCOMPLETE", "errors": [f"SEARCH_INTENT_UNREADABLE:{exc}"], "boundary": BOUNDARY}
        else:
            if args.record_evidence and args.inherited_writer_lock_fd is not None:
                try:
                    oracle_module = _load_module(
                        "q3_oracle_writer_lock_route", ORACLE_QUESTIONS
                    )
                    oracle_module._validate_inherited_writer_lock(
                        args.inherited_writer_lock_fd
                    )
                except Exception as exc:
                    print(str(exc), file=sys.stderr)
                    return 2
            payload = run_search_intent(intent)
        rendered = bounded_evidence_json(payload)
        if args.record_evidence:
            if not args.oracle_card or not args.owned_path:
                parser.error("--record-evidence requires --oracle-card and --owned-path")
            if args.inherited_writer_lock_fd is None:
                parser.error("--record-evidence requires --inherited-writer-lock-fd")
            if intent is None:
                print("cannot record unreadable search intent", file=sys.stderr)
                return 2
            try:
                _validate_owned_oracle_card(args.oracle_card, args.owned_path)
            except SearchIntentError as exc:
                print(str(exc), file=sys.stderr)
                return 2
            with tempfile.TemporaryDirectory(prefix="q3-search-evidence-") as temp_dir:
                temp = Path(temp_dir)
                intent_path = temp / "intent.json"
                evidence_path = temp / "evidence.json"
                intent_path.write_text(json.dumps(intent, ensure_ascii=False, sort_keys=True), encoding="utf-8")
                evidence_path.write_text(
                    json.dumps(payload, ensure_ascii=False, sort_keys=True),
                    encoding="utf-8",
                )
                writer_command = [
                    sys.executable,
                    str(ORACLE_QUESTIONS),
                    "record-evidence",
                    "--card",
                    args.oracle_card,
                    "--intent",
                    str(intent_path),
                    "--evidence",
                    str(evidence_path),
                    "--inherited-writer-lock-fd",
                    str(args.inherited_writer_lock_fd),
                ]
                writer = subprocess.run(
                    writer_command,
                    cwd=REPO,
                    capture_output=True,
                    text=True,
                    check=False,
                    pass_fds=(args.inherited_writer_lock_fd,),
                )
                if writer.returncode != 0:
                    print(writer.stderr or writer.stdout, file=sys.stderr)
                    return 2
        print(rendered)
        rendered_status = json.loads(rendered).get("status")
        return 2 if rendered_status == "INCOMPLETE" else 0
    if not args.query:
        parser.error("--query or --search-intent is required")
    if (
        args.record_evidence
        or args.oracle_card
        or args.owned_path
        or args.inherited_writer_lock_fd is not None
    ):
        parser.error("evidence recording is available only with --search-intent")
    payload = run_preflight(
        args.query,
        candidate=args.candidate,
        target=args.target,
        candidate_provenance=args.candidate_provenance,
    )
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return STATUS_EXIT[payload["status"]]


if __name__ == "__main__":
    raise SystemExit(main())
