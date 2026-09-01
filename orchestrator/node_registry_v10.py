#!/usr/bin/env python3
"""Scoped theorem-to-consumer registry and fail-closed v10 shadow gate."""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import stat
import subprocess
import unicodedata
from collections.abc import Iterable, Iterator, Mapping, Sequence
from contextlib import contextmanager
from pathlib import Path, PurePosixPath
from typing import Any

from orchestrator import lean_dependency_runtime

SCHEMA = "q3_node_registry.v10"
SUMMARY_SCHEMA = "q3_node_registry_gate_summary.v1"
ALGORITHM_VERSION = "NODE_REGISTRY_V10_ALGORITHM_1"
DEFAULT_PATH = "orchestrator/state/NODE_REGISTRY_V10.json"
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
HEX_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_BLOB_RE = re.compile(r"^[0-9a-f]{40,64}$")
PHYSICAL_GOAL_NAME_RE = re.compile(r"^[0-9]{3}[A-Za-z]*_.+\.goal\.md$")
LIFECYCLES = {"HISTORICAL_V9", "HISTORICAL_V9_UNMAPPED", "CANDIDATE", "ADMITTED"}
CLASSES = {"HELPER", "SEMANTIC_BRIDGE", "ROOF_CHANGE"}
REVIEWERS = {"OWNER_SIGNOFF", "ADVERSARIAL_READ_ONLY", "EXTERNAL_SIGNED"}
ALLOWED_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
ROOF_THEOREM = "Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots"
ROOF_SOURCE = (
    "q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean"
)
SEMANTIC_TRIGGER_FIELDS = {
    "object",
    "domain",
    "normalization",
    "quantifiers",
    "assumptions",
    "provenance",
    "exact_edges",
}
HISTORICAL_ENTRY_BINDING_FIELDS = (
    "domain",
    "normalization",
    "quantifiers",
    "terminal_consumer",
    "theorem_ids",
    "hypothesis_provenance",
    "hypothesis_provenance_sha256",
    "admitted_scope",
    "closes",
    "opens",
    "source_commit",
    "source_git_blob",
    "source_path",
    "task_blob",
    "task_path",
    "semantic_attestation_id",
    "status",
)


class NodeRegistryError(RuntimeError):
    """Fail-closed registry/gate error."""


def _reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise NodeRegistryError(f"NODE_REGISTRY_DUPLICATE_JSON_KEY: {key}")
        result[key] = value
    return result


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value)).hexdigest()


def _semantic_review_digest(
    semantic_inputs: Mapping[str, Any], edges_by_id: Mapping[str, Mapping[str, Any]]
) -> str:
    payload = dict(semantic_inputs)
    payload["exact_edges"] = [
        _semantic_edge_payload(edges_by_id[edge_id])
        for edge_id in semantic_inputs["exact_edges"]
    ]
    return digest(payload)


def _semantic_edge_payload(edge: Mapping[str, Any]) -> dict[str, Any]:
    """Semantic edge identity; source bytes and consumer blobs are validation-only."""

    return {
        "edge_id": edge["edge_id"],
        "theorem": edge["theorem"],
        "consumer": edge["consumer"],
        "relation": edge["relation"],
        "path": edge["path"],
        "hypothesis_port": edge["hypothesis_port"],
    }


def _validation_digest(
    validation_inputs: Mapping[str, Any],
    exact_edge_ids: Iterable[str],
    edges_by_id: Mapping[str, Mapping[str, Any]],
) -> str:
    """Bind reproducibility inputs plus exact consumer artifact blobs."""

    consumer_artifacts = [
        {
            "edge_id": edge_id,
            "consumer_path": edges_by_id[edge_id]["consumer_path"],
            "consumer_blob": edges_by_id[edge_id]["consumer_blob"],
        }
        for edge_id in exact_edge_ids
    ]
    return digest(
        {
            "validation_inputs": validation_inputs,
            "consumer_artifacts": consumer_artifacts,
        }
    )


def _dependency_edge_payload(edge: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "theorem": edge["theorem"],
        "consumer": edge["consumer"],
        "relation": edge["relation"],
        "path": edge["path"],
        "hypothesis_port": edge["hypothesis_port"],
    }


def _edge_key(edge: Mapping[str, Any]) -> tuple[Any, Any, Any, Any]:
    port = edge.get("hypothesis_port")
    if not isinstance(port, Mapping):
        return edge.get("theorem"), edge.get("consumer"), None, None
    return (
        edge.get("theorem"),
        edge.get("consumer"),
        port.get("surface"),
        port.get("direct_reference"),
    )


def _historical_entry_binding_digest(
    entry: Mapping[str, Any], node: Mapping[str, Any], edges_by_id: Mapping[str, Mapping[str, Any]]
) -> str:
    return digest(
        {
            "entry": {field: entry[field] for field in HISTORICAL_ENTRY_BINDING_FIELDS},
            "exact_edges": [
                edges_by_id[edge_id]
                for edge_id in node["semantic_review_inputs"]["exact_edges"]
            ],
        }
    )


def _canonical_path(value: Any) -> str:
    if not isinstance(value, str) or unicodedata.normalize("NFC", value) != value:
        raise NodeRegistryError(f"NODE_REGISTRY_PATH_INVALID: {value!r}")
    path = PurePosixPath(value)
    if (
        not value
        or path.is_absolute()
        or "\\" in value
        or "//" in value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise NodeRegistryError(f"NODE_REGISTRY_PATH_INVALID: {value!r}")
    return value


def _exact_keys(value: Any, keys: set[str], label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or set(value) != keys:
        raise NodeRegistryError(f"NODE_REGISTRY_SCHEMA_INVALID: {label}")
    return value


def _hex(value: Any, label: str, *, git_blob: bool = False) -> str:
    regex = GIT_BLOB_RE if git_blob else HEX_RE
    if not isinstance(value, str) or not regex.fullmatch(value):
        raise NodeRegistryError(f"NODE_REGISTRY_HASH_INVALID: {label}")
    return value


def _expr_fingerprint(value: Any, label: str, *, nullable: bool = False) -> Any:
    if nullable and value is None:
        return None
    row = _exact_keys(value, {"algorithm", "value"}, label)
    if (
        row["algorithm"] != "LEAN_EXPR_HASH_V1"
        or not isinstance(row["value"], str)
        or not row["value"].isdigit()
    ):
        raise NodeRegistryError(f"NODE_REGISTRY_EXPR_FINGERPRINT_INVALID: {label}")
    return value


def classify_node(semantic_inputs: Mapping[str, Any], *, roof_change: bool = False) -> str:
    """Auto-classify HELPERS only when every semantic trigger is genuinely absent."""

    if roof_change:
        return "ROOF_CHANGE"
    present = []
    ambiguous = False
    for field in SEMANTIC_TRIGGER_FIELDS:
        value = semantic_inputs.get(field)
        if value in (None, "", [], {}):
            continue
        present.append(field)
        if isinstance(value, str) and value in {"UNKNOWN", "AMBIGUOUS", "UNMAPPED"}:
            ambiguous = True
    if not present:
        return "HELPER"
    # Ambiguity is deliberately semantic, never a reason to auto-open a helper path.
    return "SEMANTIC_BRIDGE" if ambiguous or present else "HELPER"


def _node_changes_roof(node: Mapping[str, Any]) -> bool:
    """Detect a roof-contract edit from source identity, not the claimed class."""

    source = node.get("source")
    source_path = source.get("path") if isinstance(source, Mapping) else None
    theorem_ids = node.get("theorem_ids")
    return source_path == ROOF_SOURCE or (
        isinstance(theorem_ids, list) and ROOF_THEOREM in theorem_ids
    )


def required_reviews(node_class: str) -> dict[str, Any]:
    if node_class == "HELPER":
        return {"minimum": 0, "owner_required": False, "second_review_required": False}
    if node_class == "SEMANTIC_BRIDGE":
        return {"minimum": 1, "owner_required": False, "second_review_required": False}
    if node_class == "ROOF_CHANGE":
        return {"minimum": 2, "owner_required": True, "second_review_required": True}
    raise NodeRegistryError("NODE_REGISTRY_CLASS_INVALID")


def _validate_review(node: Mapping[str, Any]) -> None:
    review = _exact_keys(
        node["review"],
        {"state", "reviewers", "historical_receipt", "transport", "evidence"},
        "review",
    )
    reviewers = review["reviewers"]
    if not isinstance(reviewers, list) or len(reviewers) != len(set(reviewers)):
        raise NodeRegistryError("NODE_REGISTRY_REVIEW_INVALID")
    if "SELF_REVIEW" in reviewers or any(value not in REVIEWERS for value in reviewers):
        raise NodeRegistryError("NODE_REGISTRY_SELF_REVIEW_FORBIDDEN")
    if review["transport"] != "OFFLINE_EMBEDDED_NO_SOCKET":
        raise NodeRegistryError("NODE_REGISTRY_REVIEW_TRANSPORT_INVALID")
    evidence = review["evidence"]
    if not isinstance(evidence, list):
        raise NodeRegistryError("NODE_REGISTRY_REVIEW_EVIDENCE_INVALID")
    evidence_classes: list[str] = []
    for row in evidence:
        _exact_keys(
            row,
            {
                "reviewer_class",
                "reviewer_id",
                "verdict",
                "exact_payload_hash",
                "signed",
                "converged",
                "read_only",
                "principal",
                "key_id",
                "signature",
            },
            "review evidence",
        )
        reviewer_class = row["reviewer_class"]
        if reviewer_class not in REVIEWERS or reviewer_class == "SELF_REVIEW":
            raise NodeRegistryError("NODE_REGISTRY_SELF_REVIEW_FORBIDDEN")
        if row["verdict"] != "APPROVE" or row["exact_payload_hash"] != node["semantic_review_hash"]:
            raise NodeRegistryError("NODE_REGISTRY_REVIEW_PAYLOAD_DRIFT")
        if reviewer_class == "EXTERNAL_SIGNED":
            if row["signed"] is not True or not all(
                isinstance(row[field], str) and row[field]
                for field in ("principal", "key_id", "signature")
            ):
                raise NodeRegistryError("NODE_REGISTRY_EXTERNAL_REVIEW_UNSIGNED")
            raise NodeRegistryError("NODE_REGISTRY_EXTERNAL_REVIEW_VERIFIER_UNAVAILABLE")
        if reviewer_class == "ADVERSARIAL_READ_ONLY" and (
            row["converged"] is not True or row["read_only"] is not True
        ):
            raise NodeRegistryError("NODE_REGISTRY_ADVERSARIAL_REVIEW_NOT_CONVERGED")
        if reviewer_class == "OWNER_SIGNOFF" and row["converged"] is not True:
            raise NodeRegistryError("NODE_REGISTRY_OWNER_EXACT_REVIEW_MISSING")
        evidence_classes.append(reviewer_class)
    if sorted(reviewers) != sorted(set(evidence_classes)):
        raise NodeRegistryError("NODE_REGISTRY_REVIEW_EVIDENCE_CLASS_DRIFT")
    policy = required_reviews(str(node["node_class"]))
    if review["state"] == "OPEN":
        raise NodeRegistryError("NODE_REGISTRY_REVIEW_OPEN_FORBIDDEN")
    historical = review["historical_receipt"]
    is_historical = str(node["lifecycle"]).startswith("HISTORICAL_V9")
    if is_historical:
        if not isinstance(historical, Mapping) or set(historical) != {
            "kind",
            "schema",
            "entry_id",
            "entry_sha256",
        }:
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
        if historical["kind"] not in {"HISTORICAL_V9_LOCAL_RECEIPT", "OWNER_SIGNOFF"}:
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
        if historical["schema"] != "q3_semantic_quarantine.v1":
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
        _hex(historical["entry_sha256"], "historical_receipt.entry_sha256")
    elif historical is not None:
        raise NodeRegistryError("NODE_REGISTRY_NATIVE_HISTORICAL_RECEIPT_FORBIDDEN")
    if (
        node["lifecycle"] == "ADMITTED"
        and node["node_class"] in {"SEMANTIC_BRIDGE", "ROOF_CHANGE"}
        and review["state"] == "NOT_OPENED"
    ):
        raise NodeRegistryError("NODE_REGISTRY_ADMITTED_REVIEW_NOT_OPENED")
    if review["state"] == "CLOSED_HISTORICAL":
        if not is_historical:
            raise NodeRegistryError("NODE_REGISTRY_NATIVE_REVIEW_STATE_INVALID")
        grandfathered = (
            historical["kind"] == "HISTORICAL_V9_LOCAL_RECEIPT"
            and node["node_class"] != "ROOF_CHANGE"
        )
        if not grandfathered and len(reviewers) < policy["minimum"]:
            raise NodeRegistryError("NODE_REGISTRY_REVIEW_INSUFFICIENT")
        if policy["owner_required"] and "OWNER_SIGNOFF" not in reviewers:
            raise NodeRegistryError("NODE_REGISTRY_ROOF_OWNER_REVIEW_REQUIRED")
        if policy["second_review_required"] and len(reviewers) < 2:
            raise NodeRegistryError("NODE_REGISTRY_ROOF_SECOND_REVIEW_REQUIRED")
    elif review["state"] == "CLOSED":
        if is_historical:
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_REVIEW_STATE_INVALID")
        if len(reviewers) < policy["minimum"]:
            raise NodeRegistryError("NODE_REGISTRY_REVIEW_INSUFFICIENT")
        if policy["owner_required"] and "OWNER_SIGNOFF" not in reviewers:
            raise NodeRegistryError("NODE_REGISTRY_ROOF_OWNER_REVIEW_REQUIRED")
        if policy["second_review_required"] and len(reviewers) < 2:
            raise NodeRegistryError("NODE_REGISTRY_ROOF_SECOND_REVIEW_REQUIRED")
    elif review["state"] == "NOT_OPENED":
        if evidence or reviewers:
            raise NodeRegistryError("NODE_REGISTRY_REVIEW_NOT_OPENED_HAS_EVIDENCE")
    else:
        raise NodeRegistryError("NODE_REGISTRY_REVIEW_STATE_INVALID")


def _validate_registry_inner(registry: Mapping[str, Any]) -> None:
    _exact_keys(
        registry,
        {
            "schema",
            "algorithm_version",
            "mode",
            "project",
            "review_policy",
            "nodes",
            "edges",
            "registry_hash",
        },
        "top-level",
    )
    if (
        registry["schema"] != SCHEMA
        or registry["algorithm_version"] != ALGORITHM_VERSION
        or registry["mode"] != "SHADOW_V10_READ_ONLY"
    ):
        raise NodeRegistryError("NODE_REGISTRY_SCHEMA_INVALID: identity")
    project = _exact_keys(
        registry["project"],
        {
            "roots",
            "root_count",
            "file_count",
            "project_dependency_tree_hash",
        },
        "project",
    )
    if not isinstance(project["roots"], list) or project["root_count"] != len(project["roots"]):
        raise NodeRegistryError("NODE_REGISTRY_PROJECT_ROOT_COUNT_INVALID")
    if not isinstance(project["file_count"], int) or project["file_count"] < 1:
        raise NodeRegistryError("NODE_REGISTRY_PROJECT_FILE_COUNT_INVALID")
    _hex(
        project["project_dependency_tree_hash"],
        "project.project_dependency_tree_hash",
    )
    for root in project["roots"]:
        _canonical_path(root)
    policy = _exact_keys(
        registry["review_policy"],
        {
            "allowed_reviewers",
            "self_review",
            "helper_auto_rule",
            "ambiguous_rule",
            "roof_change_rule",
            "historical_receipt_transport",
            "forbidden_claim",
        },
        "review_policy",
    )
    if (
        policy["allowed_reviewers"] != ["OWNER_SIGNOFF", "ADVERSARIAL_READ_ONLY", "EXTERNAL_SIGNED"]
        or policy["self_review"] != "NEVER_OPENS"
        or policy["helper_auto_rule"] != "ONLY_WHEN_ALL_SEMANTIC_TRIGGERS_ABSENT"
        or policy["ambiguous_rule"] != "SEMANTIC_BRIDGE"
        or policy["roof_change_rule"] != "OWNER_PLUS_SECOND_REVIEW"
        or policy["historical_receipt_transport"] != "OFFLINE_EMBEDDED_NO_SOCKET"
        or policy["forbidden_claim"] != "PX_RH_CLAIM"
    ):
        raise NodeRegistryError("NODE_REGISTRY_REVIEW_POLICY_INVALID")
    if not isinstance(registry["nodes"], list) or not isinstance(registry["edges"], list):
        raise NodeRegistryError("NODE_REGISTRY_SCHEMA_INVALID: arrays")
    edge_ids: set[str] = set()
    edge_pairs: set[tuple[str, str, str, str]] = set()
    for edge in registry["edges"]:
        _exact_keys(
            edge,
            {
                "edge_id",
                "theorem",
                "consumer",
                "relation",
                "path",
                "hypothesis_port",
                "consumer_path",
                "consumer_blob",
            },
            "edge",
        )
        if edge["edge_id"] in edge_ids:
            raise NodeRegistryError("NODE_REGISTRY_EDGE_DUPLICATE")
        edge_ids.add(edge["edge_id"])
        theorem = str(edge["theorem"])
        consumer = str(edge["consumer"])
        if not NAME_RE.fullmatch(theorem) or not NAME_RE.fullmatch(consumer):
            raise NodeRegistryError("NODE_REGISTRY_EDGE_NAME_INVALID")
        if edge["relation"] not in {"DIRECT", "TRANSITIVE"}:
            raise NodeRegistryError("NODE_REGISTRY_EDGE_RELATION_INVALID")
        path = edge["path"]
        if (
            not isinstance(path, list)
            or len(path) < 2
            or path[0] != consumer
            or path[-1] != theorem
            or (len(path) == 2) != (edge["relation"] == "DIRECT")
        ):
            raise NodeRegistryError("NODE_REGISTRY_EDGE_PATH_INVALID")
        port = _exact_keys(
            edge["hypothesis_port"], {"surface", "direct_reference"}, "hypothesis_port"
        )
        if port["surface"] not in {
            "ELABORATED_VALUE",
            "ELABORATED_TYPE",
            "ELABORATED_TYPE_AND_VALUE",
        }:
            raise NodeRegistryError("NODE_REGISTRY_HYPOTHESIS_PORT_INVALID")
        if port["direct_reference"] != path[1]:
            raise NodeRegistryError("NODE_REGISTRY_HYPOTHESIS_PORT_DRIFT")
        edge_key = (
            theorem,
            consumer,
            str(port["surface"]),
            str(port["direct_reference"]),
        )
        if edge_key in edge_pairs:
            raise NodeRegistryError("NODE_REGISTRY_EDGE_DUPLICATE")
        edge_pairs.add(edge_key)
        _canonical_path(edge["consumer_path"])
        _hex(edge["consumer_blob"], "consumer_blob", git_blob=True)
    edges_by_id = {edge["edge_id"]: edge for edge in registry["edges"]}
    node_ids: set[str] = set()
    theorem_owners: dict[str, str] = {}
    for node in registry["nodes"]:
        _exact_keys(
            node,
            {
                "node_id",
                "lifecycle",
                "source",
                "theorem_ids",
                "terminal_consumer",
                "node_class",
                "semantic_triggers",
                "validation_inputs",
                "validation_hash",
                "semantic_review_inputs",
                "semantic_review_hash",
                "review",
                "px_rh_claim",
            },
            "node",
        )
        node_id = node["node_id"]
        if not isinstance(node_id, str) or node_id in node_ids:
            raise NodeRegistryError("NODE_REGISTRY_NODE_DUPLICATE")
        node_ids.add(node_id)
        if node["lifecycle"] not in LIFECYCLES or node["node_class"] not in CLASSES:
            raise NodeRegistryError("NODE_REGISTRY_NODE_STATE_INVALID")
        if node["px_rh_claim"] is not False:
            raise NodeRegistryError("NODE_REGISTRY_PX_RH_CLAIM_FORBIDDEN")
        source = _exact_keys(node["source"], {"path", "commit", "blob"}, "source")
        _canonical_path(source["path"])
        _hex(source["blob"], "source.blob", git_blob=True)
        if not isinstance(source["commit"], str) or not GIT_BLOB_RE.fullmatch(source["commit"]):
            raise NodeRegistryError("NODE_REGISTRY_SOURCE_COMMIT_INVALID")
        theorem_ids = node["theorem_ids"]
        if not isinstance(theorem_ids, list) or not theorem_ids:
            raise NodeRegistryError("NODE_REGISTRY_THEOREM_IDS_INVALID")
        for theorem in theorem_ids:
            if not isinstance(theorem, str) or not NAME_RE.fullmatch(theorem):
                raise NodeRegistryError("NODE_REGISTRY_THEOREM_IDS_INVALID")
            if theorem in theorem_owners:
                raise NodeRegistryError("NODE_REGISTRY_THEOREM_OWNER_AMBIGUOUS")
            theorem_owners[theorem] = node_id
        triggers = node["semantic_triggers"]
        if not isinstance(triggers, list) or any(
            value not in SEMANTIC_TRIGGER_FIELDS for value in triggers
        ):
            raise NodeRegistryError("NODE_REGISTRY_SEMANTIC_TRIGGERS_INVALID")
        inferred = classify_node(
            node["semantic_review_inputs"], roof_change=_node_changes_roof(node)
        )
        if node["node_class"] != inferred:
            raise NodeRegistryError("NODE_REGISTRY_CLASSIFICATION_DRIFT")
        validation_inputs = _exact_keys(
            node["validation_inputs"],
            {
                "source_bytes",
                "toolchain",
                "build",
                "holes",
                "axioms",
                "dependency_graph",
                "task_path",
                "physical_goal_path",
            },
            "validation_inputs",
        )
        source_bytes = _exact_keys(
            validation_inputs["source_bytes"], {"git_blob", "sha256"}, "source_bytes"
        )
        _hex(source_bytes["git_blob"], "source_bytes.git_blob", git_blob=True)
        _hex(source_bytes["sha256"], "source_bytes.sha256")
        toolchain = _exact_keys(
            validation_inputs["toolchain"], {"path", "sha256"}, "toolchain"
        )
        _canonical_path(toolchain["path"])
        _hex(toolchain["sha256"], "toolchain.sha256")
        build = _exact_keys(
            validation_inputs["build"],
            {"status", "lakefile_sha256", "manifest_sha256"},
            "build",
        )
        _hex(build["lakefile_sha256"], "build.lakefile_sha256")
        _hex(build["manifest_sha256"], "build.manifest_sha256")
        holes = _exact_keys(validation_inputs["holes"], {"status", "sha256"}, "holes")
        _hex(holes["sha256"], "holes.sha256")
        axioms = _exact_keys(validation_inputs["axioms"], {"status", "sha256"}, "axioms")
        _hex(axioms["sha256"], "axioms.sha256")
        dependency_graph = validation_inputs["dependency_graph"]
        dependency_keys = {
            "algorithm_version",
            "coverage",
            "project_dependency_tree_hash",
            "sha256",
        }
        if str(node["lifecycle"]).startswith("HISTORICAL_V9"):
            dependency_keys.add("historical_entry_binding_sha256")
        dependency_graph = _exact_keys(
            dependency_graph, dependency_keys, "dependency_graph"
        )
        _hex(
            dependency_graph["project_dependency_tree_hash"],
            "dependency_graph.project_dependency_tree_hash",
        )
        if (
            dependency_graph["project_dependency_tree_hash"]
            != project["project_dependency_tree_hash"]
        ):
            raise NodeRegistryError(
                "NODE_REGISTRY_PROJECT_DEPENDENCY_BINDING_DRIFT"
            )
        _hex(dependency_graph["sha256"], "dependency_graph.sha256")
        if "historical_entry_binding_sha256" in dependency_graph:
            _hex(
                dependency_graph["historical_entry_binding_sha256"],
                "dependency_graph.historical_entry_binding_sha256",
            )
        _canonical_path(validation_inputs["task_path"])
        physical_goal_path = _canonical_path(validation_inputs["physical_goal_path"])
        physical_goal = PurePosixPath(physical_goal_path)
        if (
            physical_goal.parent != PurePosixPath("docs/routeB_bus")
            or not PHYSICAL_GOAL_NAME_RE.fullmatch(physical_goal.name)
        ):
            raise NodeRegistryError("NODE_REGISTRY_PHYSICAL_GOAL_BINDING_INVALID")
        semantic_inputs = node["semantic_review_inputs"]
        if "proof_body" in semantic_inputs or "elaborated_value" in semantic_inputs:
            raise NodeRegistryError("NODE_REGISTRY_SEMANTIC_HASH_INCLUDES_PROOF_BODY")
        required_semantic = {
            "elaborated_types",
            "definitions",
            "object",
            "domain",
            "normalization",
            "quantifiers",
            "assumptions",
            "provenance",
            "exact_edges",
        }
        if set(semantic_inputs) != required_semantic:
            raise NodeRegistryError("NODE_REGISTRY_SEMANTIC_INPUTS_INVALID")
        definitions = semantic_inputs["definitions"]
        if not isinstance(definitions, list):
            raise NodeRegistryError("NODE_REGISTRY_DEFINITIONS_INVALID")
        definition_names: set[str] = set()
        for definition in definitions:
            if not isinstance(definition, Mapping):
                raise NodeRegistryError("NODE_REGISTRY_DEFINITIONS_INVALID")
            name = definition.get("name")
            if (
                not isinstance(name, str)
                or not NAME_RE.fullmatch(name)
                or name in definition_names
            ):
                raise NodeRegistryError("NODE_REGISTRY_DEFINITIONS_INVALID")
            definition_names.add(name)
            if set(definition) == {"name", "type_fingerprint", "value_fingerprint"}:
                _expr_fingerprint(
                    definition["type_fingerprint"], "definition.type_fingerprint"
                )
                _expr_fingerprint(
                    definition["value_fingerprint"],
                    "definition.value_fingerprint",
                    nullable=True,
                )
            elif set(definition) == {"name", "status"}:
                if (
                    definition["status"] != "HISTORICAL_V9_NOT_REPROBED"
                    or not str(node["lifecycle"]).startswith("HISTORICAL_V9")
                ):
                    raise NodeRegistryError("NODE_REGISTRY_DEFINITIONS_INVALID")
            else:
                raise NodeRegistryError("NODE_REGISTRY_DEFINITIONS_INVALID")
        if (
            not definitions
            and not str(node["lifecycle"]).startswith("HISTORICAL_V9")
            and node["node_class"] != "HELPER"
        ):
            raise NodeRegistryError("NODE_REGISTRY_DEFINITIONS_MISSING")
        elaborated_types = semantic_inputs["elaborated_types"]
        historical_type_placeholder = [
            {"status": "HISTORICAL_V9_NOT_REPROBED"}
        ]
        if elaborated_types == historical_type_placeholder:
            if not str(node["lifecycle"]).startswith("HISTORICAL_V9"):
                raise NodeRegistryError("NODE_REGISTRY_ELABORATED_TYPES_INVALID")
        elif (
            not isinstance(elaborated_types, list)
            or len(elaborated_types) != len(theorem_ids)
            or {
                row.get("theorem")
                for row in elaborated_types
                if isinstance(row, Mapping)
            }
            != set(theorem_ids)
        ):
            raise NodeRegistryError("NODE_REGISTRY_ELABORATED_TYPES_INVALID")
        else:
            for row in elaborated_types:
                if not isinstance(row, Mapping) or set(row) != {
                    "theorem",
                    "type_fingerprint",
                }:
                    raise NodeRegistryError("NODE_REGISTRY_ELABORATED_TYPES_INVALID")
                if not isinstance(row["theorem"], str) or not NAME_RE.fullmatch(
                    row["theorem"]
                ):
                    raise NodeRegistryError("NODE_REGISTRY_ELABORATED_TYPES_INVALID")
                _expr_fingerprint(row["type_fingerprint"], "elaborated_type")
        if node["semantic_review_hash"] != _semantic_review_digest(semantic_inputs, edges_by_id):
            raise NodeRegistryError("NODE_REGISTRY_SEMANTIC_REVIEW_HASH_DRIFT")
        mapped_edges = set(semantic_inputs["exact_edges"])
        if not mapped_edges <= edge_ids:
            raise NodeRegistryError("NODE_REGISTRY_EDGE_REFERENCE_INVALID")
        if node["validation_hash"] != _validation_digest(
            validation_inputs, semantic_inputs["exact_edges"], edges_by_id
        ):
            raise NodeRegistryError("NODE_REGISTRY_VALIDATION_HASH_DRIFT")
        expected_lifecycle = "HISTORICAL_V9" if mapped_edges else "HISTORICAL_V9_UNMAPPED"
        if (
            node["lifecycle"].startswith("HISTORICAL_V9")
            and node["lifecycle"] != expected_lifecycle
        ):
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_MAPPING_INVALID")
        terminal_consumers = node["terminal_consumer"]
        if not isinstance(terminal_consumers, list) or any(
            not isinstance(value, str) or not NAME_RE.fullmatch(value)
            for value in terminal_consumers
        ):
            raise NodeRegistryError("NODE_REGISTRY_TERMINAL_CONSUMER_INVALID")
        node_edges = [edge for edge in registry["edges"] if edge["edge_id"] in mapped_edges]
        if any(edge["theorem"] not in theorem_ids for edge in node_edges):
            raise NodeRegistryError("NODE_REGISTRY_THEOREM_CROSS_NODE_LAUNDERING")
        transitive_intermediates = {
            declaration
            for edge in node_edges
            if edge["relation"] == "TRANSITIVE"
            for declaration in edge["path"][1:-1]
        }
        if not transitive_intermediates <= definition_names:
            missing = ",".join(sorted(transitive_intermediates - definition_names))
            raise NodeRegistryError(
                "NODE_REGISTRY_TRANSITIVE_DEFINITION_COVERAGE_INCOMPLETE: " + missing
            )
        if set(terminal_consumers) != {edge["consumer"] for edge in node_edges}:
            raise NodeRegistryError("NODE_REGISTRY_TERMINAL_CONSUMER_EDGE_DRIFT")
        _validate_review(node)
    for edge in registry["edges"]:
        if edge["theorem"] not in theorem_owners:
            raise NodeRegistryError("NODE_REGISTRY_EDGE_THEOREM_UNREGISTERED")
    expected_hash = digest(
        {key: value for key, value in registry.items() if key != "registry_hash"}
    )
    if registry["registry_hash"] != expected_hash:
        raise NodeRegistryError("NODE_REGISTRY_CANONICAL_HASH_DRIFT")


def _validate_registry(registry: Mapping[str, Any]) -> None:
    """Validate fail-closed without leaking raw container/type exceptions."""

    try:
        _validate_registry_inner(registry)
    except NodeRegistryError:
        raise
    except (AttributeError, KeyError, TypeError, ValueError) as exc:
        raise NodeRegistryError(
            f"NODE_REGISTRY_SCHEMA_INVALID: malformed value: {type(exc).__name__}"
        ) from exc


def _parse_registry_bytes(raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(raw, object_pairs_hook=_reject_duplicates)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise NodeRegistryError(f"NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID: {exc}") from exc
    if not isinstance(value, dict):
        raise NodeRegistryError("NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID: root")
    try:
        _validate_registry(value)
    except NodeRegistryError:
        raise
    except (AttributeError, KeyError, TypeError, ValueError) as exc:
        raise NodeRegistryError(
            f"NODE_REGISTRY_SCHEMA_INVALID: malformed value: {type(exc).__name__}"
        ) from exc
    return value


def _read_registry_document(repo: Path | str, path: Path | str | None = None) -> dict[str, Any]:
    repo_path = Path(repo).resolve()
    selected = Path(path) if path is not None else Path(DEFAULT_PATH)
    selected = selected if selected.is_absolute() else repo_path / selected
    try:
        rel = _canonical_path(selected.relative_to(repo_path).as_posix())
    except ValueError as exc:
        raise NodeRegistryError("NODE_REGISTRY_STRUCTURAL_PATH_OUTSIDE_REPO") from exc
    if _path_has_symlink(repo_path, rel):
        raise NodeRegistryError("NODE_REGISTRY_STRUCTURAL_SYMLINK_FORBIDDEN")
    try:
        raw = selected.read_bytes()
    except OSError as exc:
        raise NodeRegistryError(f"NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID: {exc}") from exc
    return _parse_registry_bytes(raw)


def load_registry(repo: Path | str, path: Path | str | None = None) -> dict[str, Any]:
    """Load only a clean, non-symlinked registry whose exact bytes are at HEAD."""

    repo_path = Path(repo).resolve()
    selected = Path(path) if path is not None else Path(DEFAULT_PATH)
    selected = selected if selected.is_absolute() else repo_path / selected
    try:
        rel = _canonical_path(selected.relative_to(repo_path).as_posix())
    except ValueError as exc:
        raise NodeRegistryError("NODE_REGISTRY_AUTHORITY_PATH_INVALID") from exc
    if _path_has_symlink(repo_path, rel):
        raise NodeRegistryError("NODE_REGISTRY_AUTHORITY_SYMLINK_FORBIDDEN")
    if _dirty_paths(repo_path, [rel]):
        raise NodeRegistryError("NODE_REGISTRY_AUTHORITY_DIRTY")
    try:
        working_bytes = selected.read_bytes()
    except OSError as exc:
        raise NodeRegistryError("NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID") from exc
    head_bytes = _git_bytes(repo_path, "show", f"HEAD:{rel}")
    if working_bytes != head_bytes:
        raise NodeRegistryError("NODE_REGISTRY_AUTHORITY_HEAD_BLOB_DRIFT")
    return _parse_registry_bytes(working_bytes)


def _validate_historical_receipts(
    repo_path: Path,
    value: Mapping[str, Any],
    scoped_nodes: Sequence[Mapping[str, Any]] | None = None,
) -> None:
    """Deep-only local v9 binding; this is not an external or signed review."""

    historical_nodes = [
        node
        for node in (value["nodes"] if scoped_nodes is None else scoped_nodes)
        if str(node["lifecycle"]).startswith("HISTORICAL_V9")
    ]
    if not historical_nodes:
        return

    quarantine_path = repo_path / "orchestrator/state/SEMANTIC_QUARANTINE.json"
    if quarantine_path.is_symlink() or not quarantine_path.is_file():
        raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
    try:
        quarantine_bytes = quarantine_path.read_bytes()
        quarantine = json.loads(quarantine_bytes, object_pairs_hook=_reject_duplicates)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID") from exc
    if set(quarantine) != {
        "active_lease",
        "control_version",
        "entries",
        "event_ledger",
        "schema",
        "tactical_repairs",
    } or (
        quarantine.get("schema") != "q3_semantic_quarantine.v1"
        or quarantine.get("control_version") != 9
        or not isinstance(quarantine.get("entries"), list)
    ):
        raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
    head_bytes = _git_bytes(
        repo_path, "show", "HEAD:orchestrator/state/SEMANTIC_QUARANTINE.json"
    )
    if head_bytes != quarantine_bytes:
        raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_FILE_DRIFT")
    entry_keys = {
        "admitted_scope",
        "closes",
        "domain",
        "entry_id",
        "hypothesis_provenance",
        "hypothesis_provenance_sha256",
        "normalization",
        "opens",
        "quantifiers",
        "semantic_attestation_id",
        "source_commit",
        "source_git_blob",
        "source_path",
        "status",
        "task_blob",
        "task_path",
        "terminal_consumer",
        "theorem_ids",
    }
    entries: dict[str, Mapping[str, Any]] = {}
    for entry in quarantine["entries"]:
        if not isinstance(entry, Mapping) or set(entry) != entry_keys:
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
        entry_id = entry.get("entry_id")
        if not isinstance(entry_id, str) or entry_id in entries:
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
        entries[entry_id] = entry
    edges_by_id = {edge["edge_id"]: edge for edge in value["edges"]}
    for node in historical_nodes:
        receipt = node["review"]["historical_receipt"]
        entry = entries.get(node["node_id"])
        if receipt["entry_id"] != node["node_id"] or entry is None:
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_INVALID")
        if receipt["entry_sha256"] != digest(entry):
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_BLOB_DRIFT")
        binding_hash = node["validation_inputs"]["dependency_graph"].get(
            "historical_entry_binding_sha256"
        )
        if binding_hash != _historical_entry_binding_digest(entry, node, edges_by_id):
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_CROSS_FIELD_DRIFT")
        provenance = node["semantic_review_inputs"]["provenance"]
        expected_kind = (
            "OWNER_SIGNOFF"
            if provenance.get("source") == "OWNER_EXPLICIT_SEMANTIC_WAIVER"
            else "HISTORICAL_V9_LOCAL_RECEIPT"
        )
        if (
            receipt["kind"] != expected_kind
            or entry["status"] != "SEMANTICALLY_ADMITTED"
            or entry["source_path"] != node["source"]["path"]
            or entry["source_commit"] != node["source"]["commit"]
            or entry["source_git_blob"] != node["source"]["blob"]
            or entry["task_path"] != node["validation_inputs"]["task_path"]
            or entry["theorem_ids"] != node["theorem_ids"]
            or entry["semantic_attestation_id"] != provenance.get("attestation_id")
        ):
            raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_RECEIPT_CROSS_FIELD_DRIFT")


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(["git", *args], cwd=repo, text=True, capture_output=True, check=False)
    if proc.returncode:
        raise NodeRegistryError(f"NODE_REGISTRY_GIT_UNAVAILABLE: {proc.stderr.strip()}")
    return proc.stdout.strip()


def _git_bytes(repo: Path, *args: str) -> bytes:
    proc = subprocess.run(["git", *args], cwd=repo, capture_output=True, check=False)
    if proc.returncode:
        raise NodeRegistryError(
            f"NODE_REGISTRY_GIT_UNAVAILABLE: {proc.stderr.decode(errors='replace').strip()}"
        )
    return proc.stdout


@contextmanager
def _writer_read_lock(repo: Path) -> Iterator[None]:
    """Hold the canonical writer lock shared for the complete deep read gate."""

    raw = _git(repo, "rev-parse", "--git-path", "q3-three-body.writer.lock")
    lock_path = Path(raw)
    lock_path = lock_path if lock_path.is_absolute() else repo / lock_path
    parent_fd = -1
    lock_fd = -1
    handle = None

    def identity(value: os.stat_result) -> tuple[int, int, int]:
        return value.st_dev, value.st_ino, value.st_mode

    def parent_epoch(value: os.stat_result) -> tuple[int, int, int, int]:
        return value.st_dev, value.st_ino, value.st_mtime_ns, value.st_ctime_ns

    try:
        parent_fd = os.open(
            lock_path.parent,
            os.O_RDONLY
            | getattr(os, "O_CLOEXEC", 0)
            | getattr(os, "O_DIRECTORY", 0)
            | getattr(os, "O_NOFOLLOW", 0),
        )
        initial_parent = parent_epoch(os.fstat(parent_fd))
        initial_lock = os.stat(
            lock_path.name, dir_fd=parent_fd, follow_symlinks=False
        )
        if not stat.S_ISREG(initial_lock.st_mode):
            raise NodeRegistryError("NODE_REGISTRY_WRITER_LOCK_UNAVAILABLE")
        lock_fd = os.open(
            lock_path.name,
            os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=parent_fd,
        )
        if identity(os.fstat(lock_fd)) != identity(initial_lock):
            raise NodeRegistryError("NODE_REGISTRY_WRITER_LOCK_IDENTITY_CHANGED")
        handle = os.fdopen(lock_fd, "rb", closefd=True)
        lock_fd = -1
        fcntl.flock(handle.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
        observed_lock = os.stat(
            lock_path.name, dir_fd=parent_fd, follow_symlinks=False
        )
        if (
            identity(observed_lock) != identity(initial_lock)
            or identity(os.fstat(handle.fileno())) != identity(initial_lock)
            or parent_epoch(os.fstat(parent_fd)) != initial_parent
        ):
            raise NodeRegistryError("NODE_REGISTRY_WRITER_LOCK_IDENTITY_CHANGED")
        try:
            yield
        finally:
            try:
                observed_lock = os.stat(
                    lock_path.name, dir_fd=parent_fd, follow_symlinks=False
                )
                stable = (
                    identity(observed_lock) == identity(initial_lock)
                    and identity(os.fstat(handle.fileno())) == identity(initial_lock)
                    and parent_epoch(os.fstat(parent_fd)) == initial_parent
                )
            except OSError:
                stable = False
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            finally:
                handle.close()
                handle = None
            if not stable:
                raise NodeRegistryError("NODE_REGISTRY_WRITER_LOCK_IDENTITY_CHANGED")
    except BlockingIOError as exc:
        raise NodeRegistryError("NODE_REGISTRY_WRITER_LOCK_COLLISION") from exc
    except NodeRegistryError:
        raise
    except OSError as exc:
        raise NodeRegistryError("NODE_REGISTRY_WRITER_LOCK_UNAVAILABLE") from exc
    finally:
        if handle is not None:
            handle.close()
        if lock_fd >= 0:
            os.close(lock_fd)
        if parent_fd >= 0:
            os.close(parent_fd)


def _project_tree_at_head(repo: Path, roots: Sequence[str]) -> tuple[list[str], int, str]:
    for root in roots:
        _canonical_path(root)
    raw = _git_bytes(repo, "ls-tree", "-rz", "HEAD", "--", *roots)
    rows: list[tuple[str, str]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        try:
            header, path_raw = record.split(b"\t", 1)
            _mode, kind, blob = header.decode("ascii").split()
            path = path_raw.decode("utf-8")
        except (ValueError, UnicodeError) as exc:
            raise NodeRegistryError("NODE_REGISTRY_PROJECT_TREE_INVALID") from exc
        if kind == "blob" and path.endswith(".lean"):
            rows.append((_canonical_path(path), blob))
    rows.sort()
    payload = "".join(f"{path}\t{blob}\n" for path, blob in rows).encode("utf-8")
    return [path for path, _blob in rows], len(rows), hashlib.sha256(payload).hexdigest()


def _path_has_symlink(repo: Path, rel: str) -> bool:
    current = repo
    for part in PurePosixPath(rel).parts:
        current = current / part
        if current.is_symlink():
            return True
    return False


def _resolve_scope(
    registry: Mapping[str, Any], selected: Path | str | None
) -> tuple[list[dict[str, Any]], set[str], str]:
    """Resolve a physical summary scope or one exact node/edge/consumer scope."""

    nodes = list(registry["nodes"])
    edges = list(registry["edges"])
    if selected is None:
        return nodes, {
            edge_id
            for node in nodes
            for edge_id in node["semantic_review_inputs"]["exact_edges"]
        }, "GLOBAL"
    token = str(selected)
    exact_nodes = [
        node
        for node in nodes
        if token
        in {
            node["node_id"],
            node["source"]["path"],
            node["validation_inputs"].get("task_path"),
        }
    ]
    if exact_nodes:
        return exact_nodes, {
            edge_id
            for node in exact_nodes
            for edge_id in node["semantic_review_inputs"]["exact_edges"]
        }, "EXACT_NODE"
    exact_edges = {edge["edge_id"] for edge in edges if edge["edge_id"] == token}
    kind = "EXACT_EDGE"
    if not exact_edges:
        exact_edges = {edge["edge_id"] for edge in edges if edge["consumer"] == token}
        kind = "EXACT_CONSUMER"
    if exact_edges:
        scoped = [
            node
            for node in nodes
            if exact_edges.intersection(node["semantic_review_inputs"]["exact_edges"])
        ]
        return scoped, exact_edges, kind
    physical_nodes = [
        node
        for node in nodes
        if token == node["validation_inputs"].get("physical_goal_path")
    ]
    if physical_nodes:
        return physical_nodes, {
            edge_id
            for node in physical_nodes
            for edge_id in node["semantic_review_inputs"]["exact_edges"]
        }, "PHYSICAL_GOAL"
    return [], set(), "UNREGISTERED"


def _resolve_exact_edge_pin(
    registry: Mapping[str, Any],
    selected_goal_path: Path | str | None,
    exact_node_pin: str | None,
    exact_theorem_pin: str | None,
    exact_consumer_pin: str | None,
) -> tuple[list[dict[str, Any]], set[str], str]:
    pins = (exact_node_pin, exact_theorem_pin, exact_consumer_pin)
    if not all(isinstance(pin, str) and pin for pin in pins):
        raise NodeRegistryError("NODE_REGISTRY_EXACT_EDGE_PIN_INCOMPLETE")
    node_matches = [
        node for node in registry["nodes"] if node["node_id"] == exact_node_pin
    ]
    if len(node_matches) != 1:
        raise NodeRegistryError("NODE_REGISTRY_EXACT_EDGE_PIN_INVALID")
    node = node_matches[0]
    if selected_goal_path is not None and str(selected_goal_path) not in {
        node["validation_inputs"]["physical_goal_path"],
        node["validation_inputs"]["task_path"],
    }:
        raise NodeRegistryError("NODE_REGISTRY_EXACT_EDGE_PIN_GOAL_DRIFT")
    edge_matches = [
        edge
        for edge in registry["edges"]
        if edge["edge_id"] in node["semantic_review_inputs"]["exact_edges"]
        and edge["theorem"] == exact_theorem_pin
        and edge["consumer"] == exact_consumer_pin
    ]
    if not edge_matches:
        raise NodeRegistryError("NODE_REGISTRY_EXACT_EDGE_PIN_INVALID")
    # A theorem may enter one consumer through more than one first-hop port.
    # The public triple pins the complete registered port set for that pair;
    # it must never select one port by list order or silently collapse the set.
    return [node], {edge["edge_id"] for edge in edge_matches}, "PINNED_EXACT_EDGE"


def _dirty_paths(repo: Path, paths: Sequence[str]) -> set[str]:
    if not paths:
        return set()
    output = _git_bytes(repo, "status", "--porcelain=v1", "-z", "--", *sorted(set(paths)))
    dirty: set[str] = set()
    records = output.split(b"\0")
    index = 0
    while index < len(records):
        record = records[index]
        index += 1
        if not record:
            continue
        try:
            status = record[:2].decode("ascii")
            path = record[3:].decode("utf-8")
        except UnicodeError as exc:
            raise NodeRegistryError("NODE_REGISTRY_GIT_STATUS_INVALID") from exc
        dirty.add(_canonical_path(path))
        if "R" in status or "C" in status:
            if index >= len(records) or not records[index]:
                raise NodeRegistryError("NODE_REGISTRY_GIT_STATUS_INVALID")
            dirty.add(_canonical_path(records[index].decode("utf-8")))
            index += 1
    return dirty


def startup_gate_summary(
    repo: Path | str,
    selected_goal_path: Path | str | None,
    owned_paths: Iterable[Path | str] = (),
    *,
    exact_node_pin: str | None = None,
    exact_theorem_pin: str | None = None,
    exact_consumer_pin: str | None = None,
) -> dict[str, Any]:
    """Return the zero-git structural/scope summary; authority belongs to deep gate."""

    repo_path = Path(repo).resolve()
    base = {
        "schema": SUMMARY_SCHEMA,
        "status": "FATAL",
        "code": "NODE_REGISTRY_V10_UNAVAILABLE_OR_INVALID",
        "registry_hash": None,
        "node_count": 0,
        "edge_count": 0,
        "historical_v9_unmapped": 0,
        "consumption_status": "NOT_RUN_STARTUP_FAST_PATH",
    }
    try:
        registry = _read_registry_document(repo_path)
        pins = (exact_node_pin, exact_theorem_pin, exact_consumer_pin)
        if any(pin is not None for pin in pins):
            scoped, _edge_ids, scope_kind = _resolve_exact_edge_pin(
                registry,
                selected_goal_path,
                exact_node_pin,
                exact_theorem_pin,
                exact_consumer_pin,
            )
        else:
            scoped, _edge_ids, scope_kind = _resolve_scope(registry, selected_goal_path)
        base.update(
            registry_hash=registry["registry_hash"],
            node_count=len(scoped),
            edge_count=len(registry["edges"]),
            historical_v9_unmapped=sum(
                node["lifecycle"] == "HISTORICAL_V9_UNMAPPED" for node in scoped
            ),
        )
        if selected_goal_path is not None and not scoped:
            base["code"] = "NODE_REGISTRY_SELECTED_SCOPE_UNREGISTERED"
            return base
        if scope_kind in {"GLOBAL", "PHYSICAL_GOAL"}:
            base.update(
                status="HOLD",
                code="NODE_REGISTRY_EXACT_EDGE_REQUIRED",
            )
            return base
        if any(node["lifecycle"] == "HISTORICAL_V9_UNMAPPED" for node in scoped):
            base.update(
                status="HOLD",
                code="NODE_REGISTRY_HISTORICAL_V9_UNMAPPED",
            )
            return base
        base.update(status="PASS", code="NODE_REGISTRY_STARTUP_SCOPE_PASS")
        return base
    except NodeRegistryError as exc:
        base["detail"] = str(exc)
        return base


def _blobs_at_head(repo: Path, paths: Iterable[str]) -> dict[str, str | None]:
    requested = sorted({_canonical_path(path) for path in paths})
    if not requested:
        return {}
    output = _git_bytes(repo, "ls-tree", "-rz", "HEAD", "--", *requested)
    records = [record for record in output.split(b"\0") if record]
    result: dict[str, str | None] = dict.fromkeys(requested)
    for record in records:
        try:
            header, path_raw = record.split(b"\t", 1)
            _mode, kind, blob = header.decode("ascii").split()
            path = path_raw.decode("utf-8")
        except (ValueError, UnicodeError) as exc:
            raise NodeRegistryError("NODE_REGISTRY_LS_TREE_INVALID") from exc
        if kind != "blob" or path not in result or result[path] is not None:
            raise NodeRegistryError("NODE_REGISTRY_LS_TREE_PATH_DRIFT")
        result[path] = blob
    return result


def _blob_at_commit(repo: Path, commit: str, path: str) -> str | None:
    output = _git_bytes(repo, "ls-tree", "-z", commit, "--", path)
    records = [record for record in output.split(b"\0") if record]
    if not records:
        return None
    try:
        header, path_raw = records[0].split(b"\t", 1)
        _mode, kind, blob = header.decode("ascii").split()
    except (ValueError, UnicodeError) as exc:
        raise NodeRegistryError("NODE_REGISTRY_SOURCE_COMMIT_TREE_INVALID") from exc
    if len(records) != 1 or kind != "blob" or path_raw.decode("utf-8") != path:
        raise NodeRegistryError("NODE_REGISTRY_SOURCE_COMMIT_TREE_INVALID")
    return blob


def _is_ancestor(repo: Path, commit: str) -> bool:
    proc = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=repo,
        capture_output=True,
        check=False,
    )
    if proc.returncode == 0:
        return True
    if proc.returncode == 1:
        return False
    raise NodeRegistryError("NODE_REGISTRY_SOURCE_COMMIT_UNAVAILABLE")


def _file_sha256(path: Path) -> str:
    if not path.is_file() or path.is_symlink():
        raise NodeRegistryError(f"NODE_REGISTRY_INPUT_FILE_INVALID: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _module_from_path(path: str) -> str:
    prefix = "q3.lean.aristotle/"
    if not path.startswith(prefix) or not path.endswith(".lean"):
        raise NodeRegistryError(f"NODE_REGISTRY_MODULE_PATH_INVALID: {path}")
    return path[len(prefix) : -5].replace("/", ".")


def _actual_semantic_evidence(
    node: Mapping[str, Any],
    snapshot: Mapping[str, Any],
    actual_edges: Mapping[tuple[Any, Any, Any, Any], Any],
) -> tuple[bool, list[dict[str, Any]], dict[str, list[str]], str]:
    declarations = {row.get("name"): row for row in snapshot.get("declarations", [])}
    expected_types = node["semantic_review_inputs"]["elaborated_types"]
    validation_required = expected_types == [{"status": "HISTORICAL_V9_NOT_REPROBED"}]
    if not validation_required and (
        not isinstance(expected_types, list)
        or any(
            not isinstance(row, Mapping)
            or set(row) != {"theorem", "type_fingerprint"}
            for row in expected_types
        )
    ):
        raise NodeRegistryError("NODE_REGISTRY_ACTUAL_SEMANTIC_EVIDENCE_REQUIRED")
    actual_types = []
    for theorem in node["theorem_ids"]:
        row = declarations.get(theorem)
        if not isinstance(row, Mapping):
            raise NodeRegistryError("NODE_REGISTRY_ACTUAL_TYPE_EVIDENCE_MISSING")
        type_fingerprint = row.get("type_fingerprint")
        _expr_fingerprint(type_fingerprint, "runtime.type_fingerprint")
        actual_types.append(
            {
                "theorem": theorem,
                "type_fingerprint": type_fingerprint,
            }
        )
    semantic_refresh_required = validation_required or expected_types != actual_types
    axiom_map = {
        theorem: sorted(set(declarations[theorem].get("axioms", [])))
        for theorem in node["theorem_ids"]
    }
    node_edge_ids = node["semantic_review_inputs"]["exact_edges"]
    node_consumptions = sorted(
        (
            _dependency_edge_payload(row)
            for pair, row in actual_edges.items()
            if pair[0] in set(node["theorem_ids"])
        ),
        key=lambda row: (
            row["theorem"],
            row["consumer"],
            row["hypothesis_port"]["surface"],
            row["hypothesis_port"]["direct_reference"],
        ),
    )
    if bool(node_edge_ids) != bool(node_consumptions):
        raise NodeRegistryError("NODE_REGISTRY_HISTORICAL_MAPPING_MUTATION")
    return (
        semantic_refresh_required,
        actual_types,
        axiom_map,
        digest(node_consumptions),
    )


def _actual_definition_evidence(
    node: Mapping[str, Any], snapshot: Mapping[str, Any]
) -> tuple[bool, list[dict[str, Any]]]:
    declarations = {row.get("name"): row for row in snapshot.get("declarations", [])}
    expected = node["semantic_review_inputs"]["definitions"]
    if not expected:
        # An empty list is an explicitly reviewed empty semantic surface.  An
        # unknown historical surface uses named HISTORICAL_V9_NOT_REPROBED
        # rows, so there is no discoverable anonymous surface to refresh here.
        return False, []
    actual: list[dict[str, Any]] = []
    validation_required = False
    for definition in expected:
        name = definition["name"]
        row = declarations.get(name)
        if not isinstance(row, Mapping):
            raise NodeRegistryError(f"NODE_REGISTRY_DEFINITION_MISSING: {name}")
        type_fingerprint = row.get("type_fingerprint")
        value_fingerprint = row.get("value_fingerprint")
        _expr_fingerprint(type_fingerprint, "runtime.definition.type_fingerprint")
        _expr_fingerprint(
            value_fingerprint,
            "runtime.definition.value_fingerprint",
            nullable=True,
        )
        actual_row = {
            "name": name,
            "type_fingerprint": type_fingerprint,
            "value_fingerprint": value_fingerprint,
        }
        actual.append(actual_row)
        if set(definition) == {"name", "status"}:
            validation_required = True
        elif definition != actual_row:
            validation_required = True
    return validation_required, sorted(actual, key=lambda item: item["name"])


def _exact_scope_required(
    registry: Mapping[str, Any], selected: Path | str | None, scoped: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    node_ids = {node["node_id"] for node in scoped}
    edges = [
        edge
        for edge in registry["edges"]
        if any(
            edge["edge_id"] in node["semantic_review_inputs"]["exact_edges"] for node in scoped
        )
    ]
    return {
        "schema": "q3_node_registry_consumption_gate.v1",
        "status": "EXACT_EDGE_REQUIRED",
        "code": "NODE_REGISTRY_EXACT_EDGE_REQUIRED",
        "selected_scope": None if selected is None else str(selected),
        "candidate_node_ids": sorted(node_ids),
        "candidate_edge_ids": sorted(edge["edge_id"] for edge in edges),
        "candidate_consumers": sorted({edge["consumer"] for edge in edges}),
    }


def _runtime_source_closure(
    repo: Path,
    runtime_evidence: Mapping[str, Any],
    *,
    expected_root_paths: Sequence[str],
    project_paths: Sequence[str],
    project: Mapping[str, Any],
) -> tuple[list[str], str]:
    source_paths = runtime_evidence.get("source_paths")
    fingerprints = runtime_evidence.get("source_fingerprints")
    if (
        not isinstance(source_paths, list)
        or source_paths != sorted(set(source_paths))
        or not isinstance(fingerprints, list)
        or len(fingerprints) != len(source_paths)
    ):
        raise NodeRegistryError("NODE_REGISTRY_SOURCE_CLOSURE_EVIDENCE_INVALID")
    expected_fingerprints: list[dict[str, str]] = []
    tree_rows: list[tuple[str, str]] = []
    head_blobs = _blobs_at_head(repo, source_paths)
    for rel in source_paths:
        rel = _canonical_path(rel)
        if not rel.startswith("q3.lean.aristotle/Q3/") or not rel.endswith(".lean"):
            raise NodeRegistryError("NODE_REGISTRY_SOURCE_CLOSURE_EVIDENCE_INVALID")
        if _path_has_symlink(repo, rel):
            raise NodeRegistryError("NODE_REGISTRY_SYMLINK_MUTATION")
        expected_fingerprints.append({"path": rel, "sha256": _file_sha256(repo / rel)})
        blob = head_blobs[rel]
        if blob is None:
            raise NodeRegistryError("NODE_REGISTRY_IMPORT_CLOSURE_UNTRACKED")
        tree_rows.append((rel, blob))
    if fingerprints != expected_fingerprints:
        raise NodeRegistryError("NODE_REGISTRY_SOURCE_CLOSURE_BYTES_MUTATION")
    expected_roots = sorted(set(expected_root_paths))
    root_source_paths = runtime_evidence.get("root_source_paths")
    expected_by_path = {row["path"]: row for row in expected_fingerprints}
    if (
        root_source_paths != expected_roots
        or any(path not in expected_by_path for path in expected_roots)
    ):
        raise NodeRegistryError("NODE_REGISTRY_PREBUILD_SOURCE_EVIDENCE_INVALID")
    expected_prebuild = [expected_by_path[path] for path in expected_roots]
    if runtime_evidence.get("prebuild_root_source_fingerprints") != expected_prebuild:
        raise NodeRegistryError("NODE_REGISTRY_PREBUILD_SOURCE_EVIDENCE_INVALID")
    project_baseline = runtime_evidence.get("project_source_baseline")
    if (
        not isinstance(project_baseline, Mapping)
        or set(project_baseline)
        != {"root_path", "file_count", "algorithm", "tree_sha256"}
        or len(project["roots"]) != 1
        or project_baseline.get("root_path") != project["roots"][0]
        or project_baseline.get("file_count") != project["file_count"]
        or project_baseline.get("algorithm")
        != "PATH_TAB_CONTENT_SHA256_NEWLINE_V1"
        or not isinstance(project_baseline.get("tree_sha256"), str)
        or not HEX_RE.fullmatch(project_baseline["tree_sha256"])
        or not set(source_paths) <= set(project_paths)
    ):
        raise NodeRegistryError("NODE_REGISTRY_PROJECT_SOURCE_BASELINE_INVALID")
    source_map_hash = hashlib.sha256(
        canonical_json(expected_fingerprints)
    ).hexdigest()
    if runtime_evidence.get("source_map_sha256") != source_map_hash:
        raise NodeRegistryError("NODE_REGISTRY_SOURCE_CLOSURE_MAP_DRIFT")
    tree_payload = "".join(f"{path}\t{blob}\n" for path, blob in tree_rows).encode("utf-8")
    return source_paths, hashlib.sha256(tree_payload).hexdigest()


def _validate_candidate_receipts(
    repo: Path, dirty_paths: Sequence[str], receipts: Any
) -> list[Mapping[str, Any]]:
    expected_paths = sorted(set(dirty_paths))
    expected_set = [
        {"path": path, "sha256": _file_sha256(repo / path)}
        for path in expected_paths
    ]
    expected_set_sha256 = hashlib.sha256(
        json.dumps(expected_set, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    if not isinstance(receipts, list) or len(receipts) != len(expected_paths):
        raise NodeRegistryError("NODE_REGISTRY_CANDIDATE_RECEIPT_INVALID")
    validated: list[Mapping[str, Any]] = []
    required_keys = {
        "command",
        "returncode",
        "stdout_sha256",
        "stderr_sha256",
        "path",
        "bytes_sha256",
        "candidate_set",
        "candidate_set_sha256",
    }
    for expected_path, expected_candidate, receipt in zip(
        expected_paths, expected_set, receipts, strict=True
    ):
        if not isinstance(receipt, Mapping) or set(receipt) != required_keys:
            raise NodeRegistryError("NODE_REGISTRY_CANDIDATE_RECEIPT_INVALID")
        row = receipt
        try:
            candidate_path = _canonical_path(row["path"])
        except NodeRegistryError as exc:
            raise NodeRegistryError(
                "NODE_REGISTRY_CANDIDATE_RECEIPT_INVALID"
            ) from exc
        if (
            candidate_path != expected_path
            or row["command"]
            != ["lake", "env", "lean", candidate_path.removeprefix("q3.lean.aristotle/")]
            or row["returncode"] != 0
            or row["candidate_set"] != expected_set
            or row["candidate_set_sha256"] != expected_set_sha256
            or any(
                not isinstance(row[key], str) or not HEX_RE.fullmatch(row[key])
                for key in (
                    "stdout_sha256",
                    "stderr_sha256",
                    "bytes_sha256",
                    "candidate_set_sha256",
                )
            )
        ):
            raise NodeRegistryError("NODE_REGISTRY_CANDIDATE_RECEIPT_INVALID")
        if row["bytes_sha256"] != expected_candidate["sha256"]:
            raise NodeRegistryError(
                "NODE_REGISTRY_CANDIDATE_BYTES_MUTATION_DURING_PROBE"
            )
        validated.append(row)
    return validated


def _verify_consumption(
    repo: Path | str,
    registry: Mapping[str, Any] | None = None,
    *,
    selected_goal_path: Path | str | None = None,
    owned_paths: Iterable[Path | str] = (),
    dependency_snapshot: Mapping[str, Any] | None = None,
    exact_node_pin: str | None = None,
    exact_theorem_pin: str | None = None,
    exact_consumer_pin: str | None = None,
    require_external_review_authority: bool = False,
) -> dict[str, Any]:
    """Private implementation; dependency_snapshot exists only for isolated tests."""

    repo_path = Path(repo).resolve()
    current = dict(registry) if registry is not None else load_registry(repo_path)
    _validate_registry(current)
    pins = (exact_node_pin, exact_theorem_pin, exact_consumer_pin)
    if any(pin is not None for pin in pins):
        scoped, scoped_edge_ids, scope_kind = _resolve_exact_edge_pin(
            current,
            selected_goal_path,
            exact_node_pin,
            exact_theorem_pin,
            exact_consumer_pin,
        )
    else:
        scoped, scoped_edge_ids, scope_kind = _resolve_scope(current, selected_goal_path)
    if selected_goal_path is not None and not scoped:
        raise NodeRegistryError("NODE_REGISTRY_SELECTED_SCOPE_UNREGISTERED")
    if scope_kind in {"GLOBAL", "PHYSICAL_GOAL"}:
        return _exact_scope_required(current, selected_goal_path, scoped)
    if require_external_review_authority and any(
        node["lifecycle"] == "ADMITTED" for node in scoped
    ):
        raise NodeRegistryError("NODE_REGISTRY_NATIVE_ADMISSION_AUTHORITY_UNAVAILABLE")
    _validate_historical_receipts(repo_path, current, scoped)
    if any(
        node["lifecycle"]
        not in {"HISTORICAL_V9", "HISTORICAL_V9_UNMAPPED", "CANDIDATE", "ADMITTED"}
        for node in scoped
    ):
        raise NodeRegistryError("NODE_REGISTRY_NODE_NOT_CONSUMABLE")
    validation_refresh_by_node: dict[str, dict[str, Any]] = {
        node["node_id"]: {"node_id": node["node_id"]} for node in scoped
    }
    validation_stale = False
    semantic_review_required = False
    head_before = _git(repo_path, "rev-parse", "HEAD")
    project_paths, file_count, project_dependency_tree_hash = _project_tree_at_head(
        repo_path, current["project"]["roots"]
    )
    if file_count < 1:
        raise NodeRegistryError("NODE_REGISTRY_PROJECT_TREE_INVALID")
    if (
        file_count != current["project"]["file_count"]
        or project_dependency_tree_hash
        != current["project"]["project_dependency_tree_hash"]
    ):
        validation_stale = True
        for evidence in validation_refresh_by_node.values():
            evidence["project_dependency_tree"] = {
                "file_count": file_count,
                "project_dependency_tree_hash": project_dependency_tree_hash,
            }
    expected_edges = {
        _edge_key(edge): edge
        for edge in current["edges"]
        if edge["edge_id"] in scoped_edge_ids
    }
    registered_node_edges = {
        _edge_key(edge): edge
        for edge in current["edges"]
        if any(
            edge["edge_id"] in node["semantic_review_inputs"]["exact_edges"] for node in scoped
        )
    }
    probe_root_paths = {
        node["source"]["path"] for node in scoped
    } | {edge["consumer_path"] for edge in expected_edges.values()}
    relevant_paths = set(probe_root_paths)
    relevant_paths.update(
        {
            "q3.lean.aristotle/lean-toolchain",
            "q3.lean.aristotle/lakefile.toml",
            "q3.lean.aristotle/lake-manifest.json",
        }
    )
    owned = {_canonical_path(str(path)) for path in owned_paths}
    dirty = _dirty_paths(repo_path, sorted(relevant_paths))
    foreign = dirty - owned
    if foreign:
        raise NodeRegistryError(
            "NODE_REGISTRY_FOREIGN_RELEVANT_DIRTY: " + ",".join(sorted(foreign))
        )
    if any(_path_has_symlink(repo_path, path) for path in relevant_paths):
        raise NodeRegistryError("NODE_REGISTRY_SYMLINK_MUTATION")
    candidate_dirty: set[str] = set()
    candidate_runs: list[dict[str, Any]] = []
    if dirty:
        dirty_lean = sorted(path for path in dirty if path.endswith(".lean"))
        if set(dirty_lean) != dirty:
            raise NodeRegistryError("NODE_REGISTRY_OWNED_CANDIDATE_INPUT_UNVALIDATED")
        candidate_dirty = set(dirty_lean)
    scoped_head_paths = {node["source"]["path"] for node in scoped}
    scoped_head_paths.update(edge["consumer_path"] for edge in expected_edges.values())
    scoped_head_blobs = _blobs_at_head(repo_path, scoped_head_paths)
    for node in scoped:
        if not _is_ancestor(repo_path, node["source"]["commit"]):
            raise NodeRegistryError("NODE_REGISTRY_SOURCE_COMMIT_UNREACHABLE")
        if (
            _blob_at_commit(repo_path, node["source"]["commit"], node["source"]["path"])
            != node["source"]["blob"]
        ):
            raise NodeRegistryError("NODE_REGISTRY_SOURCE_COMMIT_BLOB_MUTATION")
        blob = scoped_head_blobs[node["source"]["path"]]
        if blob is None:
            raise NodeRegistryError("NODE_REGISTRY_SOURCE_BLOB_MISSING")
        if blob != node["source"]["blob"]:
            validation_stale = True
            validation_refresh_by_node[node["node_id"]]["source_blob"] = blob
    for edge in expected_edges.values():
        consumer_blob = scoped_head_blobs[edge["consumer_path"]]
        if consumer_blob is None:
            raise NodeRegistryError("NODE_REGISTRY_CONSUMER_MISSING")
        if consumer_blob != edge["consumer_blob"]:
            validation_stale = True
            for node in scoped:
                if edge["edge_id"] in node["semantic_review_inputs"]["exact_edges"]:
                    validation_refresh_by_node[node["node_id"]].setdefault(
                        "consumer_blobs", {}
                    )[edge["edge_id"]] = consumer_blob
    if dependency_snapshot is None:
        modules = sorted(_module_from_path(path) for path in probe_root_paths)
        targets = sorted({theorem for node in scoped for theorem in node["theorem_ids"]})
        semantic_declarations = sorted(
            {
                definition["name"]
                for node in scoped
                for definition in node["semantic_review_inputs"]["definitions"]
            }
        )
        try:
            dependency_snapshot = lean_dependency_runtime.inspect_dependencies(
                repo_path,
                import_modules=modules,
                target_declarations=targets,
                semantic_declarations=semantic_declarations,
            )
        except lean_dependency_runtime.LeanDependencyError as exc:
            raise NodeRegistryError(str(exc)) from exc
        dependency_snapshot["project_dependency_tree_hash"] = (
            project_dependency_tree_hash
        )
    expected_modules = sorted(_module_from_path(path) for path in probe_root_paths)
    expected_targets = sorted({theorem for node in scoped for theorem in node["theorem_ids"]})
    expected_semantic_declarations = sorted(
        {
            definition["name"]
            for node in scoped
            for definition in node["semantic_review_inputs"]["definitions"]
        }
    )
    if (
        dependency_snapshot.get("schema") != lean_dependency_runtime.SCHEMA
        or dependency_snapshot.get("algorithm_version") != lean_dependency_runtime.ALGORITHM_VERSION
        or dependency_snapshot.get("import_modules") != expected_modules
        or dependency_snapshot.get("target_declarations") != expected_targets
        or dependency_snapshot.get("semantic_declarations")
        != expected_semantic_declarations
        or dependency_snapshot.get("project_dependency_tree_hash")
        != project_dependency_tree_hash
    ):
        raise NodeRegistryError("NODE_REGISTRY_DEPENDENCY_SNAPSHOT_INVALID")
    runtime_evidence = dependency_snapshot.get("runtime_evidence")
    if not isinstance(runtime_evidence, Mapping):
        raise NodeRegistryError("NODE_REGISTRY_RUNTIME_EVIDENCE_MISSING")
    build_run = runtime_evidence.get("build_run")
    if (
        not isinstance(build_run, Mapping)
        or build_run.get("command") != ["lake", "build", *expected_modules]
        or build_run.get("returncode") != 0
    ):
        raise NodeRegistryError("NODE_REGISTRY_BUILD_ACTION_EVIDENCE_INVALID")
    for run_name in ("graph_run", "metadata_run"):
        run = runtime_evidence.get(run_name)
        if (
            not isinstance(run, Mapping)
            or run.get("command") != ["lake", "env", "lean", "--stdin"]
            or run.get("returncode") != 0
        ):
            raise NodeRegistryError("NODE_REGISTRY_LEAN_ACTION_EVIDENCE_INVALID")
    holes = runtime_evidence.get("holes")
    if not isinstance(holes, list):
        raise NodeRegistryError("NODE_REGISTRY_HOLE_EVIDENCE_INVALID")
    if holes:
        if any(not isinstance(row, Mapping) for row in holes):
            raise NodeRegistryError("NODE_REGISTRY_HOLE_EVIDENCE_INVALID")
        raise NodeRegistryError("NODE_REGISTRY_RELEVANT_CLOSURE_HOLE_PRESENT")
    actions = [
        {
            "name": name.removesuffix("_run"),
            "command": list(run["command"]),
            "exit_code": run["returncode"],
        }
        for name, run in (
            ("build_run", build_run),
            ("graph_run", runtime_evidence["graph_run"]),
            ("metadata_run", runtime_evidence["metadata_run"]),
        )
    ]
    for node in scoped:
        validation_refresh_by_node[node["node_id"]].update(
            modules=expected_modules,
            theorem_ids=sorted(node["theorem_ids"]),
            semantic_declarations=sorted(
                definition["name"]
                for definition in node["semantic_review_inputs"]["definitions"]
            ),
            actions=actions,
            holes=holes,
            axiom_policy_sha256=digest(sorted(ALLOWED_AXIOMS)),
            project_dependency_tree={
                "file_count": file_count,
                "project_dependency_tree_hash": project_dependency_tree_hash,
            },
        )
    closure_paths, closure_tree_hash = _runtime_source_closure(
        repo_path,
        runtime_evidence,
        expected_root_paths=sorted(probe_root_paths),
        project_paths=project_paths,
        project=current["project"],
    )
    for evidence in validation_refresh_by_node.values():
        evidence["project_source_baseline"] = dict(
            runtime_evidence["project_source_baseline"]
        )
    if not probe_root_paths <= set(closure_paths):
        raise NodeRegistryError("NODE_REGISTRY_IMPORT_CLOSURE_INCOMPLETE")
    closure_dirty = _dirty_paths(repo_path, closure_paths)
    closure_foreign = closure_dirty - owned
    if closure_foreign:
        raise NodeRegistryError(
            "NODE_REGISTRY_FOREIGN_RELEVANT_DIRTY: "
            + ",".join(sorted(closure_foreign))
        )
    if closure_dirty:
        dirty_lean = sorted(path for path in closure_dirty if path.endswith(".lean"))
        if set(dirty_lean) != closure_dirty:
            raise NodeRegistryError("NODE_REGISTRY_OWNED_CANDIDATE_INPUT_UNVALIDATED")
        try:
            candidate_runs = lean_dependency_runtime.validate_candidate_sources(
                repo_path, dirty_lean
            )
        except lean_dependency_runtime.LeanDependencyError as exc:
            raise NodeRegistryError(str(exc)) from exc
        candidate_runs = _validate_candidate_receipts(
            repo_path, dirty_lean, candidate_runs
        )
        candidate_dirty = set(closure_dirty)
        candidate_actions = [
            {
                "name": "candidate_compile",
                "command": list(run.get("command", [])),
                "exit_code": run.get("returncode"),
                "path": run.get("path"),
            }
            for run in candidate_runs
        ]
        for evidence in validation_refresh_by_node.values():
            evidence["actions"] = [*evidence["actions"], *candidate_actions]
    declarations = dependency_snapshot.get("declarations")
    if not isinstance(declarations, list):
        raise NodeRegistryError("NODE_REGISTRY_AXIOM_EVIDENCE_INVALID")
    for declaration in declarations:
        axioms = declaration.get("axioms") if isinstance(declaration, Mapping) else None
        if not isinstance(axioms, list) or any(not isinstance(axiom, str) for axiom in axioms):
            raise NodeRegistryError("NODE_REGISTRY_AXIOM_EVIDENCE_INVALID")
        forbidden_axioms = set(axioms) - ALLOWED_AXIOMS
        if forbidden_axioms:
            raise NodeRegistryError(
                "NODE_REGISTRY_AXIOM_POLICY_VIOLATION: "
                + ",".join(sorted(forbidden_axioms))
            )
    for node in scoped:
        inputs = node["validation_inputs"]
        source_bytes_hash = _file_sha256(repo_path / node["source"]["path"])
        if source_bytes_hash != inputs["source_bytes"]["sha256"]:
            validation_stale = True
            validation_refresh_by_node[node["node_id"]]["source_bytes_sha256"] = (
                source_bytes_hash
            )
        toolchain_sha256 = _file_sha256(repo_path / inputs["toolchain"]["path"])
        validation_refresh_by_node[node["node_id"]]["toolchain"] = {
            "path": inputs["toolchain"]["path"],
            "sha256": toolchain_sha256,
        }
        if toolchain_sha256 != inputs["toolchain"]["sha256"]:
            raise NodeRegistryError("NODE_REGISTRY_TOOLCHAIN_MUTATION")
        if (
            _file_sha256(repo_path / "q3.lean.aristotle/lakefile.toml")
            != inputs["build"]["lakefile_sha256"]
            or _file_sha256(repo_path / "q3.lean.aristotle/lake-manifest.json")
            != inputs["build"]["manifest_sha256"]
            or inputs["build"]["status"] not in {"KERNEL_GREEN", "HISTORICAL_V9_KERNEL_GREEN"}
        ):
            raise NodeRegistryError("NODE_REGISTRY_BUILD_EVIDENCE_MUTATION")
        graph_input = inputs["dependency_graph"]
        if (
            graph_input.get("algorithm_version") != lean_dependency_runtime.ALGORITHM_VERSION
            or graph_input.get("coverage") != "ALL_PROJECT_ROOTS"
        ):
            raise NodeRegistryError("NODE_REGISTRY_IMPORT_CLOSURE_MUTATION")
        if (
            graph_input.get("project_dependency_tree_hash")
            != project_dependency_tree_hash
        ):
            validation_stale = True
            validation_refresh_by_node[node["node_id"]][
                "project_dependency_tree_hash"
            ] = project_dependency_tree_hash
    consumptions = dependency_snapshot.get("consumptions")
    if not isinstance(consumptions, list) or any(
        not isinstance(row, Mapping) for row in consumptions
    ):
        raise NodeRegistryError("NODE_REGISTRY_DEPENDENCY_CONSUMPTIONS_INVALID")
    actual_edges = {_edge_key(row): row for row in consumptions}
    if len(actual_edges) != len(consumptions):
        raise NodeRegistryError("NODE_REGISTRY_DEPENDENCY_CONSUMPTION_DUPLICATE")
    expected_pair_ports: dict[tuple[Any, Any], set[tuple[Any, Any]]] = {}
    for edge in expected_edges.values():
        port = edge["hypothesis_port"]
        expected_pair_ports.setdefault(
            (edge["theorem"], edge["consumer"]), set()
        ).add((port["surface"], port["direct_reference"]))
    for actual in actual_edges.values():
        pair = (actual.get("theorem"), actual.get("consumer"))
        actual_port = actual.get("hypothesis_port")
        actual_port_key = (
            actual_port.get("surface") if isinstance(actual_port, Mapping) else None,
            actual_port.get("direct_reference")
            if isinstance(actual_port, Mapping)
            else None,
        )
        if (
            pair in expected_pair_ports
            and actual_port_key not in expected_pair_ports[pair]
        ):
            raise NodeRegistryError("NODE_REGISTRY_HYPOTHESIS_PORT_DRIFT")
    unregistered = set(actual_edges) - set(registered_node_edges)
    missing = set(expected_edges) - set(actual_edges)
    if unregistered:
        raise NodeRegistryError(
            "NODE_REGISTRY_UNREGISTERED_CONSUMPTION: "
            + ",".join(
                f"{theorem}->{consumer}@{surface}:{direct_reference}"
                for theorem, consumer, surface, direct_reference in sorted(unregistered)
            )
        )
    if missing:
        raise NodeRegistryError(
            "NODE_REGISTRY_EXPECTED_CONSUMPTION_MISSING: "
            + ",".join(
                f"{theorem}->{consumer}@{surface}:{direct_reference}"
                for theorem, consumer, surface, direct_reference in sorted(missing)
            )
        )
    declaration_map = {
        declaration.get("name"): declaration
        for declaration in declarations
        if isinstance(declaration, Mapping)
    }
    if len(declaration_map) != len(declarations):
        raise NodeRegistryError("NODE_REGISTRY_DECLARATION_MODULE_BINDING_INVALID")
    for node in scoped:
        expected_module = _module_from_path(node["source"]["path"])
        if any(
            declaration_map.get(theorem, {}).get("module") != expected_module
            for theorem in node["theorem_ids"]
        ):
            raise NodeRegistryError("NODE_REGISTRY_DECLARATION_MODULE_BINDING_DRIFT")
    for edge in expected_edges.values():
        expected_module = _module_from_path(edge["consumer_path"])
        if declaration_map.get(edge["consumer"], {}).get("module") != expected_module:
            raise NodeRegistryError("NODE_REGISTRY_DECLARATION_MODULE_BINDING_DRIFT")
    for key, expected in expected_edges.items():
        actual = actual_edges[key]
        if actual.get("relation") != expected["relation"] or actual.get("path") != expected["path"]:
            raise NodeRegistryError("NODE_REGISTRY_WRAPPER_LAUNDERING")
        # Exact tuple comparison prevents theorem A from authorizing theorem B.
        if actual.get("theorem") != expected["theorem"]:
            raise NodeRegistryError("NODE_REGISTRY_THEOREM_IDENTITY_DRIFT")
    for node in scoped:
        (
            types_stale,
            actual_types,
            actual_axiom_map,
            actual_dependency_sha256,
        ) = _actual_semantic_evidence(node, dependency_snapshot, actual_edges)
        refreshed_semantic_inputs = dict(node["semantic_review_inputs"])
        changed_semantic_fields: list[str] = []
        if types_stale:
            validation_stale = True
            refreshed_semantic_inputs["elaborated_types"] = actual_types
            changed_semantic_fields.append("elaborated_types")
            validation_refresh_by_node[node["node_id"]]["elaborated_type_fingerprints"] = (
                actual_types
            )
        definitions_stale, definition_fingerprints = _actual_definition_evidence(
            node, dependency_snapshot
        )
        if definitions_stale:
            validation_stale = True
            refreshed_semantic_inputs["definitions"] = definition_fingerprints
            changed_semantic_fields.append("definitions")
            validation_refresh_by_node[node["node_id"]].update(
                definitions_status="VALIDATION_REQUIRED_DEFINITION_FINGERPRINTS",
                definition_fingerprints=definition_fingerprints,
            )
        actual_axiom_sha256 = digest(actual_axiom_map)
        if node["validation_inputs"]["axioms"]["sha256"] != actual_axiom_sha256:
            validation_stale = True
            validation_refresh_by_node[node["node_id"]]["axioms_sha256"] = (
                actual_axiom_sha256
            )
        if (
            node["validation_inputs"]["dependency_graph"]["sha256"]
            != actual_dependency_sha256
        ):
            validation_stale = True
            validation_refresh_by_node[node["node_id"]][
                "dependency_graph_sha256"
            ] = actual_dependency_sha256
        if changed_semantic_fields:
            refreshed_semantic_hash = _semantic_review_digest(
                refreshed_semantic_inputs,
                {edge["edge_id"]: edge for edge in current["edges"]},
            )
            current_semantic_hash = node["semantic_review_hash"]
            validation_refresh_by_node[node["node_id"]]["semantic_review"] = {
                "status": (
                    "UNCHANGED"
                    if refreshed_semantic_hash == current_semantic_hash
                    else "REVIEW_REQUIRED"
                ),
                "changed_fields": sorted(changed_semantic_fields),
                "current_hash": current_semantic_hash,
                "candidate_hash": refreshed_semantic_hash,
            }
            semantic_review_required = (
                semantic_review_required
                or refreshed_semantic_hash != current_semantic_hash
            )
        declaration_map = {row.get("name"): row for row in declarations}
        theorem_axioms = {
            theorem: sorted(set(declaration_map[theorem]["axioms"]))
            for theorem in node["theorem_ids"]
        }
        validation_refresh_by_node[node["node_id"]].update(
            dependency_closure_tree_hash=closure_tree_hash,
            source_map_sha256=runtime_evidence["source_map_sha256"],
            theorem_axioms=theorem_axioms,
            dependency_result={
                "status": "EXACT",
                "edges": sorted(
                    (
                        _dependency_edge_payload(actual_edges[key])
                        for key in expected_edges
                        if key[0] in set(node["theorem_ids"])
                    ),
                    key=lambda row: (
                        row["theorem"],
                        row["consumer"],
                        row["hypothesis_port"]["surface"],
                        row["hypothesis_port"]["direct_reference"],
                    ),
                ),
            },
        )
    if _git(repo_path, "rev-parse", "HEAD") != head_before:
        raise NodeRegistryError("NODE_REGISTRY_HEAD_MUTATION")
    project_paths_after, file_count_after, tree_hash_after = _project_tree_at_head(
        repo_path, current["project"]["roots"]
    )
    if (
        project_paths_after != project_paths
        or file_count_after != file_count
        or tree_hash_after != project_dependency_tree_hash
    ):
        raise NodeRegistryError("NODE_REGISTRY_PROJECT_TREE_MUTATION_DURING_PROBE")
    closure_paths_after, closure_tree_hash_after = _runtime_source_closure(
        repo_path,
        runtime_evidence,
        expected_root_paths=sorted(probe_root_paths),
        project_paths=project_paths_after,
        project=current["project"],
    )
    if closure_paths_after != closure_paths or closure_tree_hash_after != closure_tree_hash:
        raise NodeRegistryError("NODE_REGISTRY_IMPORT_CLOSURE_MUTATION_DURING_PROBE")
    protected_paths = sorted(relevant_paths | set(closure_paths))
    dirty_after = _dirty_paths(repo_path, protected_paths)
    if dirty_after != candidate_dirty:
        raise NodeRegistryError(
            "NODE_REGISTRY_RELEVANT_DIRTY_DURING_PROBE: "
            + ",".join(sorted(dirty_after.symmetric_difference(candidate_dirty)))
        )
    if any(_path_has_symlink(repo_path, path) for path in protected_paths):
        raise NodeRegistryError("NODE_REGISTRY_SYMLINK_MUTATION")
    scoped_head_blobs_after = _blobs_at_head(repo_path, scoped_head_paths)
    for node in scoped:
        current_blob = scoped_head_blobs_after[node["source"]["path"]]
        expected_blob = validation_refresh_by_node[node["node_id"]].get(
            "source_blob", node["source"]["blob"]
        )
        if current_blob != expected_blob:
            raise NodeRegistryError("NODE_REGISTRY_SOURCE_BLOB_MUTATION_DURING_PROBE")
    for edge in expected_edges.values():
        expected_consumer_blob = edge["consumer_blob"]
        for node in scoped:
            expected_consumer_blob = validation_refresh_by_node[node["node_id"]].get(
                "consumer_blobs", {}
            ).get(edge["edge_id"], expected_consumer_blob)
        if scoped_head_blobs_after[edge["consumer_path"]] != expected_consumer_blob:
            raise NodeRegistryError("NODE_REGISTRY_CONSUMER_MUTATION_DURING_PROBE")
    if semantic_review_required:
        return {
            "schema": "q3_node_registry_consumption_gate.v1",
            "status": "HOLD",
            "code": "NODE_REGISTRY_SEMANTIC_REVIEW_REQUIRED",
            "dirty_owned_paths": sorted(candidate_dirty),
            "edge_count": len(expected_edges),
            "semantic_review_hash_unchanged": False,
            "validation_evidence": [
                validation_refresh_by_node[node["node_id"]] for node in scoped
            ],
        }
    if any(node["lifecycle"] == "HISTORICAL_V9_UNMAPPED" for node in scoped):
        return {
            "schema": "q3_node_registry_consumption_gate.v1",
            "status": "HOLD",
            "code": "NODE_REGISTRY_HISTORICAL_V9_UNMAPPED",
            "dirty_owned_paths": sorted(candidate_dirty),
            "edge_count": len(expected_edges),
            "validation_evidence": [
                validation_refresh_by_node[node["node_id"]] for node in scoped
            ],
        }
    if any(node["lifecycle"] == "CANDIDATE" for node in scoped) or candidate_dirty:
        return {
            "schema": "q3_node_registry_consumption_gate.v1",
            "status": "CANDIDATE_VALIDATED_NOT_CONSUMABLE",
            "code": "NODE_REGISTRY_CANDIDATE_NOT_CONSUMABLE",
            "dirty_owned_paths": sorted(candidate_dirty),
            "candidate_compile_receipts": candidate_runs,
            "edge_count": len(expected_edges),
            "validation_evidence": [
                validation_refresh_by_node[node["node_id"]] for node in scoped
            ],
        }
    if validation_stale:
        return {
            "schema": "q3_node_registry_consumption_gate.v1",
            "status": "VALIDATION_REQUIRED",
            "code": "NODE_REGISTRY_HISTORICAL_VALIDATION_REFRESH_REQUIRED",
            "dirty_owned_paths": [],
            "edge_count": len(expected_edges),
            "semantic_review_hash_unchanged": True,
            "validation_evidence": [
                validation_refresh_by_node[node["node_id"]] for node in scoped
            ],
        }
    return {
        "schema": "q3_node_registry_consumption_gate.v1",
        "status": "PASS",
        "code": "NODE_REGISTRY_CONSUMPTION_EXACT",
        "dirty_owned_paths": [],
        "edge_count": len(expected_edges),
        "validation_evidence": [
            validation_refresh_by_node[node["node_id"]] for node in scoped
        ],
    }


def verify_consumption(
    repo: Path | str,
    *,
    selected_goal_path: Path | str | None = None,
    owned_paths: Iterable[Path | str] = (),
    exact_node_pin: str | None = None,
    exact_theorem_pin: str | None = None,
    exact_consumer_pin: str | None = None,
) -> dict[str, Any]:
    """Deep public authority path; always obtains fresh build and Lean evidence."""

    pins = (exact_node_pin, exact_theorem_pin, exact_consumer_pin)
    if not all(isinstance(pin, str) and pin for pin in pins):
        raise NodeRegistryError("NODE_REGISTRY_EXACT_EDGE_PIN_INCOMPLETE")
    repo_path = Path(repo).resolve()
    with _writer_read_lock(repo_path):
        return _verify_consumption(
            repo_path,
            None,
            selected_goal_path=selected_goal_path,
            owned_paths=owned_paths,
            dependency_snapshot=None,
            exact_node_pin=exact_node_pin,
            exact_theorem_pin=exact_theorem_pin,
            exact_consumer_pin=exact_consumer_pin,
            require_external_review_authority=True,
        )
