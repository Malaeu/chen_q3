#!/usr/bin/env python3
"""Build and verify the bounded Q3 project-state projection.

The physical bus and route-local runtime files remain component state.  This
module verifies them, composes the two typed stores and append-only event log,
and emits the sole project-level authoritative manifest plus bounded human
views.  It never selects or dispatches work.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


REPO = Path(__file__).resolve().parents[1]
SCHEMA = REPO / "docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json"
REGISTRY = REPO / "docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json"
FACTS = REPO / "orchestrator/state/PROJECT_FACTS.json"
EXECUTION = REPO / "orchestrator/state/PROJECT_EXECUTION_STATE.json"
EVENTS = REPO / "orchestrator/state/PROJECT_STATE_EVENTS.jsonl"
STATE = REPO / "orchestrator/state/PROJECT_STATE.json"
PROJECT_STATUS = REPO / "docs/generated/PROJECT_STATUS.md"
WORK_QUEUE = REPO / "docs/generated/WORK_QUEUE.md"
PUBLIC_ROUTE_GRAPH = REPO / "docs/generated/PUBLIC_ROUTE_GRAPH.md"
README = REPO / "README.md"
ORCHESTRATOR = REPO / "q3.lean.aristotle/PROJECT_ORCHESTRATOR.md"

BLOCK_START = "<!-- PROJECT_STATE:START -->"
BLOCK_END = "<!-- PROJECT_STATE:END -->"
VALID_ROLES = {
    "AUTHORITATIVE_STATE", "SELECTOR", "COMPONENT_STATE", "FACT",
    "GENERATED_VIEW", "EVENT_LOG", "HISTORICAL",
}
STATUS_NAME = re.compile(
    r"(?:^|[^A-Z0-9])(?:CURRENT|STATE|STATUS|MONITOR|QUEUE|DEPS|GRAPH)(?:[^A-Z0-9]|$)", re.I
)

CANONICAL_OWNER_LABEL_CROSSWALK = {
    "owner_label": "P5_SINGLE_MACHINE_STATE_SCHEMA_V1",
    "phase_text": "Phase P5 — one authoritative state, generated views",
    "board_acceptance_ids": [
        "P5.001", "P5.002", "P5.003", "P5.004", "P5.005",
        "P5.006", "P5.007", "P5.008", "P4.008",
    ],
    "acceptance_text": [
        "Complete status-surface map.",
        "Exact precedence and schema are frozen.",
        "Facts and mutable selectors live in distinct typed stores.",
        "Generated headers include source state hash.",
        "No historical monitor can select work.",
        "Manual divergence is detected.",
        "Corrections never erase registered predictions or old verdicts.",
        "Active state is small; history remains queryable.",
        "Generated views match machine state.",
    ],
    "failure_codes": [
        "STATUS_SURFACE_INVENTORY_INCOMPLETE", "STATE_AUTHORITY_AMBIGUOUS",
        "FACT_STATE_CONFLATION", "GENERATED_VIEW_WITHOUT_SOURCE_HASH",
        "STALE_MONITOR_SELECTED_WORK", "GENERATED_VIEW_DRIFT_UNDETECTED",
        "RETROACTIVE_STATE_REPAIR", "STATE_DUPLICATION_PERSISTS",
        "CI_STATE_DRIFT_MISSING",
    ],
}
CANONICAL_P5_CROSSWALK = {
    "meta": {
        "migration_label": "P5.000_FULL_LABEL_CROSSWALK",
        "failure_code": "MIGRATION_LABEL_CROSSWALK_INCOMPLETE",
    },
    "rows": [
        {"migration_label": "P5.001_STATUS_SURFACE_INVENTORY", "board_items": [{"board_id": "P5.001", "acceptance_text": "Complete status-surface map.", "failure_code": "STATUS_SURFACE_INVENTORY_INCOMPLETE"}]},
        {"migration_label": "P5.002_AUTHORITATIVE_STATE_MANIFEST", "board_items": [{"board_id": "P5.002", "acceptance_text": "Exact precedence and schema are frozen.", "failure_code": "STATE_AUTHORITY_AMBIGUOUS"}]},
        {"migration_label": "P5.003_FACT_EXECUTION_SPLIT", "board_items": [{"board_id": "P5.003", "acceptance_text": "Facts and mutable selectors live in distinct typed stores.", "failure_code": "FACT_STATE_CONFLATION"}]},
        {"migration_label": "P5.004_HASHED_GENERATED_VIEWS", "board_items": [{"board_id": "P5.004", "acceptance_text": "Generated headers include source state hash.", "failure_code": "GENERATED_VIEW_WITHOUT_SOURCE_HASH"}]},
        {"migration_label": "P5.005_NON_SELECTOR_METADATA", "board_items": [{"board_id": "P5.005", "acceptance_text": "No historical monitor can select work.", "failure_code": "STALE_MONITOR_SELECTED_WORK"}]},
        {"migration_label": "P5.006_VIEW_DRIFT_CHECKER", "board_items": [
            {"board_id": "P5.006", "acceptance_text": "Manual divergence is detected.", "failure_code": "GENERATED_VIEW_DRIFT_UNDETECTED"},
            {"board_id": "P4.008", "acceptance_text": "Generated views match machine state.", "failure_code": "CI_STATE_DRIFT_MISSING"},
        ]},
        {"migration_label": "P5.007_APPEND_ONLY_EVENTS", "board_items": [{"board_id": "P5.007", "acceptance_text": "Corrections never erase registered predictions or old verdicts.", "failure_code": "RETROACTIVE_STATE_REPAIR"}]},
        {"migration_label": "P5.008_BOUNDED_ACTIVE_VIEWS", "board_items": [{"board_id": "P5.008", "acceptance_text": "Active state is small; history remains queryable.", "failure_code": "STATE_DUPLICATION_PERSISTS"}]},
    ],
}
EVENT_AUTHORITY_POLICY = {
    "history_mode": "GIT_FIRST_PARENT",
    "registration_rule": "EVENT_REGISTERED_ONLY_ON_CANONICAL_FIRST_PARENT_CHAIN",
    "merge_rule": "MERGE_RESULT_MUST_PREFIX_EXTEND_PREMERGE_FIRST_PARENT",
    "side_branch_rule": "SIDE_BRANCH_EVENT_IS_DRAFT_UNTIL_CANONICAL_ADMISSION",
}
REQUIRED_FOREIGN_EXACT_PATHS: set[str] = set()
REQUIRED_FOREIGN_GLOB_PATTERNS = {"orchestrator/state/*.db"}
CANONICAL_SURFACES_SHA256 = "9b42dfb8489c87b5b1a0d7eb4ddc0ed5f81027ab346262dae574328bbc6bb96f"
P5_PROSPECTIVE_PATHS = {
    "docs/generated/PROJECT_STATUS.md",
    "docs/generated/PUBLIC_ROUTE_GRAPH.md",
    "docs/generated/WORK_QUEUE.md",
    "docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json",
    "docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json",
    "orchestrator/project_state.py",
    "orchestrator/state/PROJECT_EXECUTION_STATE.json",
    "orchestrator/state/PROJECT_FACTS.json",
    "orchestrator/state/PROJECT_STATE.json",
    "orchestrator/state/PROJECT_STATE_EVENTS.jsonl",
    "orchestrator/tests/test_project_state.py",
}
REQUIRED_FACT_RECEIPT_PATHS = {
    "docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md",
    "docs/semantic_quarantine/MODULE_CLASS_REGISTRY_v1.json",
}
CANONICAL_COVERAGE_RULES = [
    {"path_prefix": "docs/routeB_bus/", "role": "HISTORICAL", "exception_glob": "docs/routeB_bus/[0-9][0-9][0-9]_*.goal.md", "exception_paths": ["docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"], "note": "Immutable bus receipts are history; goal files are content-aware seeds and executable OPEN goals require an exact component-state row."},
    {"path_prefix": "q3.lean.aristotle/ACTIVE/requests/", "role": "HISTORICAL", "exception_paths": ["q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json", "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md"], "note": "Request packets and old state snapshots do not select project work."},
    {"path_prefix": "orchestrator/state/queue/", "role": "HISTORICAL", "note": "Legacy queue history."},
    {"path_prefix": "orchestrator/state/inbox/", "role": "HISTORICAL", "note": "Ingest receipts, not selectors."},
    {"path_prefix": "q3.lean.aristotle/ACTIVE/graphs/", "role": "GENERATED_VIEW", "note": "Sensor outputs never select work."},
    {"path_prefix": "q3.lean.aristotle/ACTIVE/pipeline/", "role": "HISTORICAL", "note": "Pipeline registries and reports are component evidence, not project selectors."},
    {"path_prefix": "q3.lean.aristotle/ACTIVE/aristotle/", "role": "HISTORICAL", "note": "Aristotle queues and receipts do not select project work."},
    {"path_prefix": "q3.lean.aristotle/ACTIVE/refs/", "role": "HISTORICAL", "note": "Reference snapshots do not select work."},
    {"path_prefix": "docs/Aristotle_models_training/", "role": "HISTORICAL", "note": "Training-analysis graphs are historical evidence."},
    {"path_prefix": "docs/GLOWER_ODD_FLOOR_10_08_2026/", "role": "HISTORICAL", "note": "Packet archive is not a selector."},
    {"path_prefix": "full/archive_latex_2026_01_29/", "role": "HISTORICAL", "note": "Archived manuscript state."},
    {"path_prefix": "paper/output/", "role": "GENERATED_VIEW", "note": "Paper build outputs are generated views."},
    {"path_prefix": "q3.lean.aristotle/docs/insights/", "role": "HISTORICAL", "note": "Dated insight audits are evidence, not selectors."},
    {"path_prefix": "research_swarm/workers/", "role": "HISTORICAL", "note": "Worker test status files are noncanonical experiment receipts."},
    {"path_prefix": "q3.lean.aristotle/archive/", "role": "HISTORICAL", "note": "Archive never selects work."},
    {"path_prefix": "archive/", "role": "HISTORICAL", "note": "Archive never selects work."},
]
STATIC_COMPONENT_MAP = {
    "SESSION_ENTRY_ROUTER": ("SESSION_ENTRY.md", "SCOPED_SELECTOR_ALIAS"),
    "SESSION_ENTRY_ROUTER_CANONICAL": ("q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md", "SCOPED_SELECTOR_CANONICAL"),
    "CODEX_CURRENT": ("docs/Codex/CURRENT.md", "SCOPED_SELECTOR"),
    "CHANNEL_RUNTIME": ("orchestrator/state/CHANNEL_RUNTIME.json", "RUNTIME_COMPONENT"),
    "SEMANTIC_QUARANTINE": ("orchestrator/state/SEMANTIC_QUARANTINE.json", "SEMANTIC_COMPONENT"),
    "ROUTE_B_EXECUTION_STATE": ("q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json", "RUNTIME_COMPONENT"),
    "ROUTE_B_FACT_HISTORY": ("q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md", "FACT_HISTORY"),
}


class StateError(RuntimeError):
    """Fail-closed project-state validation error."""


def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise StateError(f"DUPLICATE_JSON_KEY: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicates)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise StateError(f"INVALID_JSON: {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise StateError(f"INVALID_JSON_ROOT: {path}")
    return value


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_path(value: str) -> PurePosixPath:
    if not isinstance(value, str):
        raise StateError(f"NONCANONICAL_REPO_PATH: {value!r}")
    path = PurePosixPath(value)
    if path.is_absolute() or re.search(r"(^|/)\.{1,2}(/|$)", value) or "\\" in value:
        raise StateError(f"NONCANONICAL_REPO_PATH: {value}")
    if not value or value.endswith("/") or "//" in value:
        raise StateError(f"NONCANONICAL_REPO_PATH: {value}")
    return path


def require_sha256(value: Any, label: str) -> None:
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
        raise StateError(f"STATE_SCHEMA_INVALID: {label} sha256")


def validate_hash_ref(value: Any, label: str) -> None:
    if not isinstance(value, dict):
        raise StateError(f"STATE_SCHEMA_INVALID: {label} hash ref")
    require_exact_keys(value, {"path", "sha256"}, label)
    canonical_path(value["path"])
    require_sha256(value["sha256"], label)


def validate_schema(document: dict[str, Any], schema: dict[str, Any]) -> None:
    validate_document_shape(document)
    try:
        import jsonschema
    except ImportError:
        return
    errors = sorted(jsonschema.Draft202012Validator(schema).iter_errors(document), key=lambda e: list(e.path))
    if errors:
        detail = "; ".join(error.message for error in errors[:4])
        raise StateError(f"STATE_SCHEMA_INVALID: {detail}")


def require_exact_keys(document: dict[str, Any], required: set[str], label: str) -> None:
    if set(document) != required:
        raise StateError(f"STATE_SCHEMA_INVALID: {label} keys")


def validate_document_shape(document: dict[str, Any]) -> None:
    """Validate without optional dependencies and always fail as StateError."""
    try:
        _validate_document_shape(document)
    except StateError:
        raise
    except (TypeError, KeyError, AttributeError, ValueError) as exc:
        raise StateError(f"STATE_SCHEMA_INVALID: malformed nested value: {exc}") from exc


def _validate_document_shape(document: dict[str, Any]) -> None:
    """Dependency-free fail-closed validator for the four admitted documents."""
    kind = document.get("schema")
    if kind == "q3_project_facts.v1":
        require_exact_keys(document, {"schema", "version", "public_claims", "route_facts", "receipts"}, kind)
        require_exact_keys(document["public_claims"], {"unconditional_rh_proof", "compiled_broad_cone_export", "public_canonical_export"}, kind)
        require_exact_keys(document["route_facts"], {"route_b_rank", "route_b_rh_status", "owner_boundary"}, kind)
        if document["version"] != 1 or document["public_claims"] != {
            "unconditional_rh_proof": False,
            "compiled_broad_cone_export": "CONDITIONAL_LEGACY",
            "public_canonical_export": "OPEN",
        } or document["route_facts"] != {
            "route_b_rank": "CHALLENGER",
            "route_b_rh_status": "NOT_RH",
            "owner_boundary": "PX_RH_CLAIM",
        }:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} constants")
        if not isinstance(document["receipts"], list) or len(document["receipts"]) != 2:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} receipts")
        for receipt in document["receipts"]:
            validate_hash_ref(receipt, kind)
        receipt_paths = [receipt["path"] for receipt in document["receipts"]]
        if len(set(receipt_paths)) != 2 or set(receipt_paths) != REQUIRED_FACT_RECEIPT_PATHS:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} receipt contract")
    elif kind == "q3_project_execution_state.v1":
        require_exact_keys(document, {"schema", "version", "selector", "authority_domains", "component_states"}, kind)
        require_exact_keys(document["selector"], {"action", "selected_goal_id", "selected_goal_path", "phase_key_sha256", "selector_program"}, kind)
        selector = document["selector"]
        if document["version"] != 1 or selector.get("action") != "SELECT_EXACT_GOAL" or selector.get("selector_program") != "orchestrator/goal_runtime.py":
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} constants")
        if not isinstance(selector.get("selected_goal_id"), str) or not re.fullmatch(r"[0-9]{3}", selector["selected_goal_id"]):
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} goal id")
        canonical_path(selector["selected_goal_path"])
        require_sha256(selector["phase_key_sha256"], kind)
        if not isinstance(document["authority_domains"], list) or len(document["authority_domains"]) != 2:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority domains")
        domains: set[str] = set()
        for domain in document["authority_domains"]:
            require_exact_keys(domain, {"domain", "authority_order", "component_ids", "aggregate_role"}, kind)
            if domain["domain"] not in {"PROJECT_GOAL_SELECTION", "CODEX_TASK_SELECTION"} or domain["domain"] in domains:
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority domain")
            domains.add(domain["domain"])
            if not isinstance(domain["authority_order"], list) or not domain["authority_order"] or len(set(domain["authority_order"])) != len(domain["authority_order"]):
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority order")
            if not isinstance(domain["component_ids"], list) or not domain["component_ids"] or len(set(domain["component_ids"])) != len(domain["component_ids"]):
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority components")
            if domain["aggregate_role"] != "PROJECT_STATE_AGGREGATES_BUT_DOES_NOT_REPLACE_DOMAIN_AUTHORITY":
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority constants")
        if not isinstance(document["component_states"], list) or len(document["component_states"]) != 8:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} components")
        component_roles = {"SELECTOR_INPUT", "SCOPED_SELECTOR", "SCOPED_SELECTOR_ALIAS", "SCOPED_SELECTOR_CANONICAL", "RUNTIME_COMPONENT", "SEMANTIC_COMPONENT", "FACT_HISTORY"}
        component_ids: set[str] = set()
        for component in document["component_states"]:
            required_keys = {"id", "role"} if component.get("id") == "PHYSICAL_BUS_GOAL" else {"id", "path", "role"}
            require_exact_keys(component, required_keys, kind)
            if not re.fullmatch(r"[A-Z0-9_]+", component["id"]) or component["id"] in component_ids or component["role"] not in component_roles:
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} component")
            component_ids.add(component["id"])
            if "path" in component:
                canonical_path(component["path"])
        expected = dict(STATIC_COMPONENT_MAP)
        expected["PHYSICAL_BUS_GOAL"] = (None, "SELECTOR_INPUT")
        actual = {row["id"]: (row.get("path"), row["role"]) for row in document["component_states"]}
        if actual != expected:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} exact component map")
        expected_domain_components = {
            "PROJECT_GOAL_SELECTION": ["PHYSICAL_BUS_GOAL"],
            "CODEX_TASK_SELECTION": ["CODEX_CURRENT"],
        }
        if {row["domain"]: row["component_ids"] for row in document["authority_domains"]} != expected_domain_components:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority component map")
        expected_authority_order = {
            "PROJECT_GOAL_SELECTION": ["PHYSICAL_BUS", "GOAL_RUNTIME", "PROJECT_EXECUTION_STATE"],
            "CODEX_TASK_SELECTION": ["CODEX_CURRENT"],
        }
        if {row["domain"]: row["authority_order"] for row in document["authority_domains"]} != expected_authority_order:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority order map")
    elif kind == "q3_project_state.v1":
        require_exact_keys(document, {"schema", "version", "authority", "source_hashes", "event_log", "component_hashes", "projection"}, kind)
        if document["version"] != 1 or document["authority"] != "AUTHORITATIVE_STATE":
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} authority")
        if set(document["source_hashes"]) != {"facts", "execution", "events", "surface_registry", "schema", "builder_program", "selector_program"}:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} source hashes")
        for source in document["source_hashes"].values():
            validate_hash_ref(source, kind)
        if not isinstance(document["component_hashes"], list):
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} component hashes")
        for component in document["component_hashes"]:
            validate_hash_ref(component, kind)
        require_exact_keys(document["event_log"], {"count", "tail_sha256"}, kind)
        if not isinstance(document["event_log"]["count"], int) or document["event_log"]["count"] < 1:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} event count")
        require_sha256(document["event_log"]["tail_sha256"], kind)
        require_exact_keys(document["projection"], {"selected_goal_id", "selected_goal_path", "route_b_rank", "route_b_rh_status", "unconditional_rh_proof", "public_export_receipt_path"}, kind)
        projection = document["projection"]
        if not isinstance(projection["selected_goal_id"], str) or not re.fullmatch(r"[0-9]{3}", projection["selected_goal_id"]):
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} goal id")
        canonical_path(projection["selected_goal_path"])
        canonical_path(projection["public_export_receipt_path"])
        if projection["route_b_rank"] != "CHALLENGER" or projection["route_b_rh_status"] != "NOT_RH" or projection["unconditional_rh_proof"] is not False:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} projection")
    elif kind == "q3_status_surface_registry.v1":
        require_exact_keys(document, {"schema", "version", "owner_label_crosswalk", "event_authority_policy", "p5_000_crosswalk", "surfaces", "coverage_rules", "foreign_worktree_denylist"}, kind)
        if document["version"] != 1 or len(document["surfaces"]) < 20:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} inventory")
        owner = document["owner_label_crosswalk"]
        if owner != CANONICAL_OWNER_LABEL_CROSSWALK:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} owner crosswalk")
        if document["event_authority_policy"] != EVENT_AUTHORITY_POLICY:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} event authority policy")
        if document["p5_000_crosswalk"] != CANONICAL_P5_CROSSWALK:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} exact crosswalk")
        for row in document["surfaces"]:
            required = {"path", "role", "selector_effect", "source_store", "consumers", "drift_risk"}
            allowed = required | {"required_marker"}
            if not required.issubset(row) or not set(row).issubset(allowed):
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} keys")
            if row["role"] not in VALID_ROLES or row["selector_effect"] not in {"ACTIVE", "COMPONENT_ONLY", "NONE"}:
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} surface")
            canonical_path(row["path"])
            if not isinstance(row["source_store"], str) or not row["source_store"] or not isinstance(row["consumers"], list) or not all(isinstance(item, str) and item for item in row["consumers"]) or not isinstance(row["drift_risk"], str) or not row["drift_risk"]:
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} surface fields")
            if "required_marker" in row:
                if row["role"] != "HISTORICAL" or not isinstance(row["required_marker"], str) or not row["required_marker"]:
                    raise StateError(f"STATE_SCHEMA_INVALID: {kind} required marker")
        if sha256_bytes(canonical_json(document["surfaces"])) != CANONICAL_SURFACES_SHA256:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} surface policy digest")
        for row in document["coverage_rules"]:
            allowed = {"path_prefix", "role", "note", "exception_glob", "exception_paths"}
            if not {"path_prefix", "role", "note"}.issubset(row) or not set(row).issubset(allowed):
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} coverage")
            if row["role"] not in {"GENERATED_VIEW", "HISTORICAL"}:
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} coverage role")
            prefix = row["path_prefix"]
            if not isinstance(prefix, str) or prefix in {"", "/", "./"} or not prefix.endswith("/") or prefix.startswith("/") or re.search(r"(^|/)\.{1,2}/", prefix) or "//" in prefix or "\\" in prefix:
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} coverage prefix")
            if not isinstance(row["note"], str) or not row["note"]:
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} coverage note")
            if "exception_glob" in row and (not isinstance(row["exception_glob"], str) or not row["exception_glob"]):
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} exception glob")
            exception_paths = row.get("exception_paths", [])
            if not isinstance(exception_paths, list) or len(exception_paths) != len(set(exception_paths)):
                raise StateError(f"STATE_SCHEMA_INVALID: {kind} exception paths")
            for path in exception_paths:
                canonical_path(path)
        if document["coverage_rules"] != CANONICAL_COVERAGE_RULES:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} coverage contract")
        denylist = document["foreign_worktree_denylist"]
        require_exact_keys(denylist, {"exact_paths", "glob_patterns"}, f"{kind} denylist")
        exact_paths = denylist["exact_paths"]
        glob_patterns = denylist["glob_patterns"]
        if not isinstance(exact_paths, list) or exact_paths or len(set(exact_paths)) != len(exact_paths):
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} denylist exact paths")
        if not isinstance(glob_patterns, list) or len(glob_patterns) != 1 or len(set(glob_patterns)) != len(glob_patterns):
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} denylist glob patterns")
        for path in exact_paths:
            canonical_path(path)
        if set(exact_paths) != REQUIRED_FOREIGN_EXACT_PATHS or set(glob_patterns) != REQUIRED_FOREIGN_GLOB_PATTERNS:
            raise StateError(f"STATE_SCHEMA_INVALID: {kind} denylist contract")
    else:
        raise StateError(f"STATE_SCHEMA_INVALID: unknown schema {kind!r}")


def load_events(path: Path = EVENTS) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    event_ids: set[str] = set()
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip():
            raise StateError(f"EMPTY_EVENT_LINE: {line_number}")
        try:
            event = json.loads(raw, object_pairs_hook=reject_duplicates)
        except (json.JSONDecodeError, StateError) as exc:
            raise StateError(f"INVALID_EVENT_JSON: {line_number}: {exc}") from exc
        if not isinstance(event, dict):
            raise StateError(f"INVALID_EVENT_ROOT: {line_number}")
        required = {
            "schema", "event_id", "recorded_at", "kind", "summary",
            "prev_event_sha256", "event_sha256",
        }
        if set(event) != required or event["schema"] != "q3_project_state_event.v1":
            raise StateError(f"EVENT_SCHEMA_INVALID: {line_number}")
        event_id = event["event_id"]
        kind = event["kind"]
        summary = event["summary"]
        recorded_at = event["recorded_at"]
        if not isinstance(event_id, str) or not re.fullmatch(r"[A-Z0-9][A-Z0-9._-]*", event_id) or event_id in event_ids:
            raise StateError(f"EVENT_SCHEMA_INVALID: {line_number}: event_id")
        if not isinstance(kind, str) or not re.fullmatch(r"[A-Z][A-Z0-9_]*", kind):
            raise StateError(f"EVENT_SCHEMA_INVALID: {line_number}: kind")
        if not isinstance(summary, str) or not summary.strip():
            raise StateError(f"EVENT_SCHEMA_INVALID: {line_number}: summary")
        if not isinstance(recorded_at, str):
            raise StateError(f"EVENT_SCHEMA_INVALID: {line_number}: recorded_at")
        try:
            timestamp = datetime.fromisoformat(recorded_at)
        except ValueError as exc:
            raise StateError(f"EVENT_SCHEMA_INVALID: {line_number}: recorded_at") from exc
        if timestamp.tzinfo is None or timestamp.utcoffset() is None:
            raise StateError(f"EVENT_SCHEMA_INVALID: {line_number}: recorded_at timezone")
        payload = dict(event)
        claimed = payload.pop("event_sha256")
        actual = sha256_bytes(canonical_json(payload))
        if claimed != actual:
            raise StateError(f"EVENT_HASH_INVALID: {line_number}")
        expected_prev = events[-1]["event_sha256"] if events else None
        if event["prev_event_sha256"] != expected_prev:
            raise StateError(f"EVENT_CHAIN_INVALID: {line_number}")
        events.append(event)
        event_ids.add(event_id)
    if not events:
        raise StateError("EVENT_LOG_EMPTY")
    return events


def tracked_paths(root: Path = REPO) -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "-z"], cwd=root, check=True, capture_output=True
    ).stdout.decode("utf-8").split("\0")
    tracked = {item for item in result if item}
    tracked.update(path for path in P5_PROSPECTIVE_PATHS if (root / path).is_file())
    return sorted(tracked)


def candidate_status_surface(path: str) -> bool:
    name = PurePosixPath(path).name
    if name == "SESSION_ENTRY.md":
        return True
    if path in {"README.md", "TASK.md", "Q3_OBSTRUCTION_ATLAS.md", "q3.lean.aristotle/PROJECT_ORCHESTRATOR.md"}:
        return True
    if path.startswith("docs/routeB_bus/") and path.endswith(".goal.md"):
        return True
    if not name.lower().endswith((".md", ".json", ".jsonl", ".yaml", ".yml")):
        return False
    return bool(STATUS_NAME.search(name))


def covered_by_rule(path: str, rules: Iterable[dict[str, Any]]) -> bool:
    for rule in rules:
        if not path.startswith(str(rule.get("path_prefix", ""))):
            continue
        if path in rule.get("exception_paths", []):
            continue
        pattern = rule.get("exception_glob")
        if pattern and PurePosixPath(path).match(str(pattern)):
            continue
        return True
    return False


def goal_status(root: Path | None, relative: str) -> str | None:
    if root is None:
        return None
    path = root / relative
    if not path.is_file():
        return None
    if relative.endswith(".goal.md"):
        answer = root / (relative[:-len(".goal.md")] + ".answer.md")
        if answer.is_file():
            return "CLOSED"
    head = "\n".join(path.read_text(encoding="utf-8").splitlines()[:40])
    match = re.search(r"(?m)^STATUS:\s*([A-Z0-9_]+)\s*$", head)
    return match.group(1) if match else None


def validate_registry(registry: dict[str, Any], tracked: Iterable[str], *, root: Path | None = None) -> None:
    if registry.get("owner_label_crosswalk") != CANONICAL_OWNER_LABEL_CROSSWALK:
        raise StateError("MIGRATION_LABEL_CROSSWALK_INCOMPLETE: owner crosswalk")
    if registry.get("p5_000_crosswalk") != CANONICAL_P5_CROSSWALK:
        raise StateError("MIGRATION_LABEL_CROSSWALK_INCOMPLETE: exact crosswalk")
    if registry.get("event_authority_policy") != EVENT_AUTHORITY_POLICY:
        raise StateError("RETROACTIVE_STATE_REPAIR: event authority policy")
    surfaces = registry.get("surfaces", [])
    exact: dict[str, dict[str, Any]] = {}
    for surface in surfaces:
        path = str(surface.get("path", ""))
        canonical_path(path)
        if path in exact:
            raise StateError(f"STATUS_SURFACE_DUPLICATE: {path}")
        if surface.get("role") not in VALID_ROLES:
            raise StateError(f"STATUS_SURFACE_ROLE_INVALID: {path}")
        if surface.get("role") == "HISTORICAL" and surface.get("selector_effect") != "NONE":
            raise StateError(f"STALE_MONITOR_SELECTED_WORK: {path}")
        exact[path] = surface

    tracked_set = set(tracked)
    denylist = registry.get("foreign_worktree_denylist", {})
    for denied in denylist.get("exact_paths", []):
        canonical_path(denied)
        if denied in tracked_set:
            raise StateError(f"FOREIGN_WORKTREE_FILE_TRACKED: {denied}")
    for pattern in denylist.get("glob_patterns", []):
        if pattern not in REQUIRED_FOREIGN_GLOB_PATTERNS:
            raise StateError(f"STATE_SCHEMA_INVALID: foreign glob pattern: {pattern}")
        matched = sorted(path for path in tracked_set if PurePosixPath(path).match(pattern))
        if matched:
            raise StateError(f"FOREIGN_WORKTREE_FILE_TRACKED: {matched[0]}")

    missing: list[str] = []
    for path in tracked_set:
        name = PurePosixPath(path).name
        routeb_root = PurePosixPath(path).parent.as_posix() == "docs/routeB_bus"
        sensitive_routeb_name = routeb_root and (
            "CURRENT" in name.upper()
            or re.match(r"(?i)^(?:ACTIVE|NEXT)(?:[^A-Z0-9]|$)", name) is not None
        )
        if sensitive_routeb_name and path not in exact:
            missing.append(path)
            continue
        if not candidate_status_surface(path):
            continue
        if path in exact:
            continue
        if name == "SESSION_ENTRY.md" or (path.startswith("docs/routeB_bus/") and "CURRENT" in name.upper()):
            missing.append(path)
            continue
        if path.startswith("docs/routeB_bus/") and path.endswith(".goal.md"):
            if goal_status(root, path) in {"CLOSED", "PAUSED_RESTORABLE"}:
                continue
            missing.append(path)
            continue
        if covered_by_rule(path, registry.get("coverage_rules", [])):
            continue
        missing.append(path)
    if missing:
        raise StateError("STATUS_SURFACE_INVENTORY_INCOMPLETE: " + ", ".join(sorted(missing)[:20]))


def component_path(execution: dict[str, Any], component: dict[str, Any]) -> str:
    if component["id"] == "PHYSICAL_BUS_GOAL":
        return execution["selector"]["selected_goal_path"]
    return component["path"]


def validate_selector_registry(execution: dict[str, Any], registry: dict[str, Any]) -> None:
    exact = {row["path"]: row for row in registry["surfaces"]}
    selected = execution["selector"]["selected_goal_path"]
    selected_row = exact.get(selected)
    if not selected_row or selected_row["role"] != "COMPONENT_STATE" or selected_row["selector_effect"] != "COMPONENT_ONLY":
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: selected goal lacks exact component-state registry row")
    component_roles = {
        "SELECTOR_INPUT": {"COMPONENT_STATE"},
        "SCOPED_SELECTOR": {"SELECTOR"},
        "SCOPED_SELECTOR_ALIAS": {"SELECTOR"},
        "SCOPED_SELECTOR_CANONICAL": {"SELECTOR"},
        "RUNTIME_COMPONENT": {"COMPONENT_STATE"},
        "SEMANTIC_COMPONENT": {"COMPONENT_STATE"},
        "FACT_HISTORY": {"FACT"},
    }
    for component in execution["component_states"]:
        path = component_path(execution, component)
        row = exact.get(path)
        if not row or row["role"] not in component_roles[component["role"]]:
            raise StateError(f"STATE_AUTHORITY_AMBIGUOUS: component registry mismatch: {path}")
    if selected not in {component_path(execution, row) for row in execution["component_states"] if row["role"] == "SELECTOR_INPUT"}:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: selected goal is not a selector-input component")
    scoped_roles = {"SCOPED_SELECTOR", "SCOPED_SELECTOR_ALIAS", "SCOPED_SELECTOR_CANONICAL"}
    expected_active = {
        "orchestrator/state/PROJECT_STATE.json",
        "orchestrator/state/PROJECT_EXECUTION_STATE.json",
    } | {
        component_path(execution, row) for row in execution["component_states"]
        if row["role"] in scoped_roles
    }
    actual_active = {
        row["path"] for row in registry["surfaces"]
        if row["selector_effect"] == "ACTIVE"
    }
    if actual_active != expected_active:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: closed ACTIVE selector set mismatch")


def validate_session_entry_alias(
    root: Path,
    execution: dict[str, Any],
    registry: dict[str, Any],
    *,
    tracked: set[str] | None = None,
) -> None:
    active_alias = root / "ACTIVE"
    session_alias = root / "SESSION_ENTRY.md"
    canonical = root / "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md"
    if not active_alias.is_symlink() or os.readlink(active_alias) != "q3.lean.aristotle/ACTIVE":
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: ACTIVE alias target")
    if not session_alias.is_symlink() or os.readlink(session_alias) != "ACTIVE/SESSION_ENTRY.md":
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: SESSION_ENTRY alias target")
    if not canonical.is_file() or canonical.is_symlink():
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: canonical SESSION_ENTRY is not a regular file")
    root_real = root.resolve()
    try:
        canonical_real = canonical.resolve(strict=True)
        alias_real = session_alias.resolve(strict=True)
        canonical_real.relative_to(root_real)
    except (OSError, ValueError) as exc:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: SESSION_ENTRY realpath") from exc
    if alias_real != canonical_real or session_alias.read_bytes() != canonical.read_bytes():
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: SESSION_ENTRY alias divergence")
    tracked_set = tracked if tracked is not None else set(tracked_paths(root))
    required_tracked = {"ACTIVE", "SESSION_ENTRY.md", "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md"}
    if not required_tracked.issubset(tracked_set):
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: SESSION_ENTRY alias is not fully tracked")
    component_roles = {component_path(execution, row): row["role"] for row in execution["component_states"]}
    if component_roles.get("SESSION_ENTRY.md") != "SCOPED_SELECTOR_ALIAS" or component_roles.get("q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md") != "SCOPED_SELECTOR_CANONICAL":
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: SESSION_ENTRY component typing")
    surface_roles = {row["path"]: (row["role"], row["selector_effect"]) for row in registry["surfaces"]}
    for path in ("SESSION_ENTRY.md", "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md"):
        if surface_roles.get(path) != ("SELECTOR", "ACTIVE"):
            raise StateError("STATE_AUTHORITY_AMBIGUOUS: SESSION_ENTRY registry typing")


def read_codex_current_status(root: Path = REPO) -> str:
    text = (root / "docs/Codex/CURRENT.md").read_text(encoding="utf-8")
    match = re.search(r"(?m)^status:\s*([A-Z_]+)\s*$", text)
    if not match:
        raise StateError("CODEX_CURRENT_STATUS_INVALID")
    return match.group(1)


def read_routeb_status(root: Path = REPO) -> dict[str, str]:
    program = root / "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py"
    result = subprocess.run([sys.executable, str(program), "--check"], cwd=root, check=False, capture_output=True, text=True)
    if result.returncode != 0:
        raise StateError(f"ROUTEB_STATUS_FAILED: {result.stderr.strip() or result.stdout.strip()}")
    match = re.search(r"(?m)^BUS:.*\bactive=([0-9]{3}|NONE)\b.*\bselected-next=([0-9]{3}|NONE)\b", result.stdout)
    if not match:
        raise StateError("ROUTEB_STATUS_OUTPUT_INVALID")
    return {"active": match.group(1), "selected_next": match.group(2)}


def validate_scoped_precedence(root: Path, execution: dict[str, Any]) -> None:
    domains = {row["domain"]: row for row in execution["authority_domains"]}
    if domains.get("PROJECT_GOAL_SELECTION", {}).get("authority_order") != ["PHYSICAL_BUS", "GOAL_RUNTIME", "PROJECT_EXECUTION_STATE"]:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: project goal precedence")
    codex = domains.get("CODEX_TASK_SELECTION")
    if not codex or codex["authority_order"] != ["CODEX_CURRENT"]:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: Codex CURRENT precedence")
    if read_codex_current_status(root) not in {"ACTIVE", "EMPTY", "CLOSED"}:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: Codex CURRENT status")
    selected = execution["selector"]["selected_goal_id"]
    routeb = read_routeb_status(root)
    if routeb != {"active": selected, "selected_next": selected}:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: routeb_status disagrees with selected goal")
    physical_status = goal_status(root, execution["selector"]["selected_goal_path"])
    if physical_status != "OPEN":
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: selected physical goal is not OPEN")


def validate_store_separation(facts: dict[str, Any], execution: dict[str, Any]) -> None:
    if "selector" in facts or "component_states" in facts:
        raise StateError("FACT_STATE_CONFLATION")
    if "public_claims" in execution or "route_facts" in execution:
        raise StateError("FACT_STATE_CONFLATION")


def validate_fact_receipts(root: Path, facts: dict[str, Any]) -> None:
    for receipt in facts["receipts"]:
        path = root / canonical_path(receipt["path"])
        if not path.is_file() or sha256(path) != receipt["sha256"]:
            raise StateError(f"FACT_RECEIPT_DRIFT: {receipt['path']}")


def assert_generated_content(actual: str | None, expected: str, label: str) -> None:
    if actual != expected:
        raise StateError(f"GENERATED_VIEW_DRIFT_UNDETECTED: {label}")


def ensure_append_only(old: bytes, current: bytes) -> None:
    if not current.startswith(old):
        raise StateError("RETROACTIVE_STATE_REPAIR")


def read_live_selector(root: Path = REPO) -> dict[str, Any]:
    result = subprocess.run(
        [sys.executable, "orchestrator/goal_runtime.py", "--json"],
        cwd=root, check=False, capture_output=True, text=True,
    )
    if result.returncode != 0:
        raise StateError(f"GOAL_RUNTIME_FAILED: {result.stderr.strip() or result.stdout.strip()}")
    try:
        payload = json.loads(result.stdout, object_pairs_hook=reject_duplicates)
        selected = payload["result"]
    except (json.JSONDecodeError, KeyError, TypeError, StateError) as exc:
        raise StateError("GOAL_RUNTIME_OUTPUT_INVALID") from exc
    absolute = Path(str(selected.get("selected_goal_path", "")))
    try:
        relative = absolute.resolve().relative_to(root.resolve()).as_posix()
    except (OSError, ValueError) as exc:
        raise StateError("GOAL_RUNTIME_PATH_OUTSIDE_REPO") from exc
    return {
        "action": selected.get("action"),
        "selected_goal_id": selected.get("selected_goal_id"),
        "selected_goal_path": relative,
        "phase_key_sha256": selected.get("mathematical_phase_key_sha256"),
        "selector_program": "orchestrator/goal_runtime.py",
    }


def validate_sources(root: Path = REPO) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    schema = load_json(root / SCHEMA.relative_to(REPO))
    facts = load_json(root / FACTS.relative_to(REPO))
    execution = load_json(root / EXECUTION.relative_to(REPO))
    registry = load_json(root / REGISTRY.relative_to(REPO))
    for document in (facts, execution, registry):
        validate_schema(document, schema)
    validate_store_separation(facts, execution)
    events = load_events(root / EVENTS.relative_to(REPO))
    validate_registry(registry, tracked_paths(root), root=root)
    validate_selector_registry(execution, registry)
    validate_session_entry_alias(root, execution, registry)
    validate_scoped_precedence(root, execution)
    check_event_append_only(root)

    validate_fact_receipts(root, facts)
    for component in execution["component_states"]:
        relative = component_path(execution, component)
        path = root / canonical_path(relative)
        if not path.is_file():
            raise StateError(f"COMPONENT_STATE_MISSING: {relative}")
    live = read_live_selector(root)
    if execution["selector"] != live:
        raise StateError("STATE_AUTHORITY_AMBIGUOUS: PROJECT_EXECUTION_STATE != goal_runtime.py")
    return facts, execution, registry, events


def hash_ref(root: Path, relative: str) -> dict[str, str]:
    canonical_path(relative)
    return {"path": relative, "sha256": sha256(root / relative)}


def build_state(root: Path = REPO) -> dict[str, Any]:
    facts, execution, _registry, events = validate_sources(root)
    source_paths = {
        "facts": "orchestrator/state/PROJECT_FACTS.json",
        "execution": "orchestrator/state/PROJECT_EXECUTION_STATE.json",
        "events": "orchestrator/state/PROJECT_STATE_EVENTS.jsonl",
        "surface_registry": "docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json",
        "schema": "docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json",
        "builder_program": "orchestrator/project_state.py",
        "selector_program": "orchestrator/goal_runtime.py",
    }
    receipts_by_path = {receipt["path"]: receipt for receipt in facts["receipts"]}
    public_receipt_path = "docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md"
    if public_receipt_path not in receipts_by_path:
        raise StateError("FACT_RECEIPT_MISSING: public export receipt")
    state = {
        "schema": "q3_project_state.v1",
        "version": 1,
        "authority": "AUTHORITATIVE_STATE",
        "source_hashes": {name: hash_ref(root, path) for name, path in source_paths.items()},
        "event_log": {"count": len(events), "tail_sha256": events[-1]["event_sha256"]},
        "component_hashes": [hash_ref(root, component_path(execution, item)) for item in execution["component_states"]],
        "projection": {
            "selected_goal_id": execution["selector"]["selected_goal_id"],
            "selected_goal_path": execution["selector"]["selected_goal_path"],
            "route_b_rank": facts["route_facts"]["route_b_rank"],
            "route_b_rh_status": facts["route_facts"]["route_b_rh_status"],
            "unconditional_rh_proof": facts["public_claims"]["unconditional_rh_proof"],
            "public_export_receipt_path": public_receipt_path,
        },
    }
    validate_schema(state, load_json(root / SCHEMA.relative_to(REPO)))
    return state


def source_header(state: dict[str, Any], manifest_sha: str) -> list[str]:
    hashes = state["source_hashes"]
    return [
        "<!-- GENERATED: orchestrator/project_state.py; DO NOT EDIT -->",
        f"<!-- project_state_sha256: {manifest_sha} -->",
        f"<!-- facts_sha256: {hashes['facts']['sha256']} -->",
        f"<!-- execution_sha256: {hashes['execution']['sha256']} -->",
        f"<!-- events_sha256: {hashes['events']['sha256']} -->",
        f"<!-- event_tail_sha256: {state['event_log']['tail_sha256']} -->",
        f"<!-- schema_sha256: {hashes['schema']['sha256']} -->",
        f"<!-- builder_program_sha256: {hashes['builder_program']['sha256']} -->",
        f"<!-- selector_program_sha256: {hashes['selector_program']['sha256']} -->",
    ]


def render_views(state: dict[str, Any], manifest_sha: str) -> dict[str, str]:
    p = state["projection"]
    header = source_header(state, manifest_sha)
    project = header + [
        "", "# Project Status", "",
        f"- Unconditional RH proof: `{'YES' if p['unconditional_rh_proof'] else 'NO'}`",
        "- Compiled broad-cone export: `CONDITIONAL_LEGACY`",
        "- Public canonical export: `OPEN`",
        f"- Route B: `{p['route_b_rank']} / {p['route_b_rh_status']}`",
        f"- Selected physical goal: `{p['selected_goal_id']}` (`{p['selected_goal_path']}`)",
        "- Authority: `orchestrator/state/PROJECT_STATE.json`",
        "- Event authority: `GIT_FIRST_PARENT`; side-branch events are drafts until canonical admission.",
        f"- Public-export receipt: [`{p['public_export_receipt_path']}`](../semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md)",
        "",
    ]
    queue = header + [
        "", "# Work Queue", "",
        "This is a bounded projection, not an independent queue.", "",
        f"- Action: `SELECT_EXACT_GOAL`",
        f"- Goal: `{p['selected_goal_id']}`",
        f"- Physical source: `{p['selected_goal_path']}`",
        "- Historical monitors and manual queues have no selector effect.",
        "",
    ]
    graph = header + [
        "", "# Public Route Graph", "", "```text",
        "corrected square-class interfaces [OPEN]",
        "    -> PUBLIC_CANONICAL export [NOT ESTABLISHED]",
        "", "compiled broad-cone route [CONDITIONAL_LEGACY]",
        "", f"Route B [{p['route_b_rank']} / {p['route_b_rh_status']}]",
        "```", "",
        "This status graph is not the Lean proof graph and not a proof verdict.", "",
    ]
    return {
        "docs/generated/PROJECT_STATUS.md": "\n".join(project),
        "docs/generated/WORK_QUEUE.md": "\n".join(queue),
        "docs/generated/PUBLIC_ROUTE_GRAPH.md": "\n".join(graph),
    }


def bounded_block(state: dict[str, Any], manifest_sha: str) -> str:
    p = state["projection"]
    return "\n".join([
        BLOCK_START,
        f"<!-- project_state_sha256: {manifest_sha} -->",
        "Project-level current status is generated from",
        "`orchestrator/state/PROJECT_STATE.json`.",
        "Human views: `docs/generated/PROJECT_STATUS.md` and",
        "`docs/generated/WORK_QUEUE.md`.",
        f"Current projection: RH proof `NO`; Route B `{p['route_b_rank']} / {p['route_b_rh_status']}`; goal `{p['selected_goal_id']}`.",
        BLOCK_END,
    ])


def replace_block(text: str, block: str) -> str:
    if text.count(BLOCK_START) != 1 or text.count(BLOCK_END) != 1:
        raise StateError("GENERATED_BLOCK_MARKERS_INVALID")
    before, rest = text.split(BLOCK_START, 1)
    _old, after = rest.split(BLOCK_END, 1)
    return before + block + after


def atomic_write(path: Path, data: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(data)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def build_all(root: Path = REPO) -> None:
    state = build_state(root)
    state_text = json.dumps(state, indent=2, ensure_ascii=False) + "\n"
    atomic_write(root / STATE.relative_to(REPO), state_text)
    manifest_sha = sha256_bytes(state_text.encode("utf-8"))
    for relative, content in render_views(state, manifest_sha).items():
        atomic_write(root / relative, content)
    block = bounded_block(state, manifest_sha)
    for target in (root / README.relative_to(REPO), root / ORCHESTRATOR.relative_to(REPO)):
        atomic_write(target, replace_block(target.read_text(encoding="utf-8"), block))


def check_views(root: Path = REPO) -> None:
    expected_state = build_state(root)
    state_path = root / STATE.relative_to(REPO)
    expected_text = json.dumps(expected_state, indent=2, ensure_ascii=False) + "\n"
    if not state_path.is_file() or state_path.read_text(encoding="utf-8") != expected_text:
        raise StateError("AUTHORITATIVE_STATE_DRIFT")
    manifest_sha = sha256_bytes(expected_text.encode("utf-8"))
    for relative, content in render_views(expected_state, manifest_sha).items():
        path = root / relative
        actual = path.read_text(encoding="utf-8") if path.is_file() else None
        assert_generated_content(actual, content, relative)
    block = bounded_block(expected_state, manifest_sha)
    for target in (root / README.relative_to(REPO), root / ORCHESTRATOR.relative_to(REPO)):
        text = target.read_text(encoding="utf-8")
        if replace_block(text, block) != text:
            raise StateError(f"GENERATED_VIEW_DRIFT_UNDETECTED: {target.relative_to(root)}")


def check_event_append_only(root: Path = REPO) -> None:
    """Enforce the project-authoritative first-parent append-only contract.

    Side-branch event history is not project authority before merge.  Each
    first-parent snapshot must extend its predecessor, and the merge/worktree
    result must extend the last first-parent snapshot.  No history means the
    initial bootstrap is admitted.
    """
    load_events(root / EVENTS.relative_to(REPO))
    relative = EVENTS.relative_to(REPO).as_posix()
    history = subprocess.run(
        ["git", "rev-list", "--first-parent", "--reverse", "HEAD", "--", relative],
        cwd=root, check=True, capture_output=True, text=True,
    ).stdout.splitlines()
    previous: bytes | None = None
    for commit in history:
        snapshot = subprocess.run(
            ["git", "show", f"{commit}:{relative}"], cwd=root, check=True, capture_output=True
        ).stdout
        if previous is not None:
            ensure_append_only(previous, snapshot)
        previous = snapshot
    current = (root / relative).read_bytes()
    if previous is not None:
        ensure_append_only(previous, current)


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("build")
    sub.add_parser("validate")
    sub.add_parser("check-views")
    inventory = sub.add_parser("inventory")
    inventory.add_argument("--check-complete", action="store_true", required=True)
    events = sub.add_parser("check-events")
    events.add_argument("--append-only", action="store_true", required=True)
    args = parser.parse_args()
    try:
        if args.command == "build":
            build_all()
        elif args.command == "validate":
            validate_sources()
            check_views()
        elif args.command == "check-views":
            check_views()
        elif args.command == "inventory":
            registry = load_json(REGISTRY)
            validate_document_shape(registry)
            validate_registry(registry, tracked_paths(), root=REPO)
        elif args.command == "check-events":
            check_event_append_only()
    except (StateError, subprocess.CalledProcessError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        return 2
    print(f"OK: {args.command}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
