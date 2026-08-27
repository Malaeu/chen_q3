#!/usr/bin/env python3
"""Validate the P3 module-class registry and its declared tracked coverage."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


REPO = Path(__file__).resolve().parents[1]
SCHEMA_PATH = REPO / "docs/semantic_quarantine/MODULE_CLASS_SCHEMA_v1.json"
REGISTRY_PATH = REPO / "docs/semantic_quarantine/MODULE_CLASS_REGISTRY_v1.json"

MODULE_CLASSES = (
    "CORE_SHARED",
    "PUBLIC_CANONICAL",
    "CHALLENGER",
    "CONDITIONAL_COMPILED",
    "LEGACY",
    "EXPERIMENT",
    "ARCHIVE",
    "GENERATED_VIEW",
)
ARTIFACT_KINDS = ("LEAN_MODULE", "STATUS_DOCUMENT")
LIFECYCLE_STATUSES = (
    "ACTIVE",
    "CANDIDATE",
    "COMPATIBILITY_ONLY",
    "BROKEN",
    "HISTORICAL",
    "GENERATED",
)
TRAITS = ("PROJECT_AXIOMS", "LEGACY_BROAD_CONE", "BROKEN_BUILD")

RULE_ID_RE = re.compile(r"[a-z0-9_]+", flags=re.ASCII)
LEAN_SEGMENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*", flags=re.ASCII)
SCHEMA_V1_CANONICAL_SHA256 = (
    "cca686669e173ceec238bf3cf5d8a430a6f141995bb42acc1c9e9af9a16e87a1"
)

Q3_BASIC_DEFS_IDENTITY = {
    "source_root": "q3.lean.aristotle",
    "repo_relative_path": "q3.lean.aristotle/Q3/Basic/Defs.lean",
    "lean_module": "Q3.Basic.Defs",
}
Q3_ROOT_IDENTITY = {
    "source_root": "q3.lean.aristotle",
    "repo_relative_path": "q3.lean.aristotle/Q3.lean",
    "lean_module": "Q3",
}
FROZEN_Q3_BASIC_DEFS_OVERRIDES = {
    "Q3.Weil_cone",
    "Q3.Weil_cone_K",
    "Q3.W_K",
    "Q3.W_K_subset_Weil_cone_K",
}


class RegistryError(ValueError):
    """A fail-closed module registry validation error."""


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RegistryError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_unique_object
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise RegistryError(f"cannot load JSON {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise RegistryError(f"top-level JSON object required: {path}")
    return payload


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise RegistryError(f"{where}: object required")
    return value


def _array(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise RegistryError(f"{where}: array required")
    return value


def _keys(
    obj: dict[str, Any], *, allowed: Iterable[str], required: Iterable[str], where: str
) -> None:
    allowed_set = set(allowed)
    required_set = set(required)
    unknown = set(obj) - allowed_set
    missing = required_set - set(obj)
    if unknown:
        raise RegistryError(f"{where}: unknown keys: {sorted(unknown)}")
    if missing:
        raise RegistryError(f"{where}: missing keys: {sorted(missing)}")


def _closed_token(value: Any, allowed: tuple[str, ...], where: str) -> str:
    if not isinstance(value, str) or value not in allowed:
        raise RegistryError(f"{where}: unknown closed-enum token {value!r}")
    return value


def _string(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise RegistryError(f"{where}: nonempty string required")
    return value


def _rule_id(value: Any, where: str) -> str:
    if not isinstance(value, str) or RULE_ID_RE.fullmatch(value) is None:
        raise RegistryError(f"{where}: rule id must match ASCII [a-z0-9_]+")
    return value


def _lean_module(value: Any, where: str, *, prefix: bool = False) -> str:
    module = _string(value, where)
    if prefix:
        if not module.endswith("."):
            raise RegistryError(f"{where}: Lean module prefix must end in '.'")
        module = module[:-1]
    parts = module.split(".")
    if not parts or any(LEAN_SEGMENT_RE.fullmatch(part) is None for part in parts):
        raise RegistryError(f"{where}: invalid ASCII Lean module name")
    return f"{module}." if prefix else module


def _canonical_path(value: Any, where: str, *, directory_prefix: bool = False) -> str:
    """Enforce lexical POSIX canonicalization beyond the JSON Schema pattern.

    The schema pattern rejects broad shape errors. This executable layer is the
    authority for dot segments, repeated separators, and PurePosixPath identity.
    """
    path = _string(value, where)
    if "\\" in path or "\n" in path or "\r" in path or path.startswith("/"):
        raise RegistryError(f"{where}: noncanonical POSIX repo-relative path: {path!r}")
    if directory_prefix:
        if not path.endswith("/"):
            raise RegistryError(f"{where}: directory prefix must end in '/'")
        canonical_part = path[:-1]
    else:
        if path.endswith("/"):
            raise RegistryError(f"{where}: file/source-root path must not end in '/'")
        canonical_part = path
    pure = PurePosixPath(canonical_part)
    if not canonical_part or any(part in ("", ".", "..") for part in pure.parts):
        raise RegistryError(f"{where}: noncanonical POSIX repo-relative path: {path!r}")
    if str(pure) != canonical_part:
        raise RegistryError(f"{where}: noncanonical POSIX repo-relative path: {path!r}")
    return path


def _assert_inside_repo(repo: Path, path: str, where: str, *, must_exist: bool) -> None:
    repo_real = repo.resolve()
    candidate = repo / path
    if must_exist and not candidate.exists():
        raise RegistryError(f"{where}: registered path does not exist: {path}")
    try:
        candidate.resolve(strict=False).relative_to(repo_real)
    except ValueError as exc:
        raise RegistryError(f"{where}: symlink escape outside repository: {path}") from exc


def _assert_tracked_leaf(repo: Path, path: str, where: str) -> None:
    """Reject broken/escaping symlinks and anything that is not a regular file."""
    candidate = repo / path
    try:
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, RuntimeError, OSError) as exc:
        raise RegistryError(f"{where}: tracked leaf is missing or a broken symlink: {path}") from exc
    try:
        resolved.relative_to(repo.resolve())
    except ValueError as exc:
        raise RegistryError(f"{where}: tracked leaf symlink escape: {path}") from exc
    if not resolved.is_file():
        raise RegistryError(f"{where}: tracked leaf is not a regular file: {path}")


def module_from_path(source_root: str, repo_relative_path: str) -> str:
    source = _canonical_path(source_root, "module identity source_root")
    path = _canonical_path(repo_relative_path, "module identity repo_relative_path")
    prefix = f"{source}/"
    if not path.startswith(prefix) or not path.endswith(".lean"):
        raise RegistryError(
            "module identity: Lean path must be a .lean file below source_root"
        )
    relative = path[len(prefix) : -len(".lean")]
    parts = PurePosixPath(relative).parts
    if not parts or any(LEAN_SEGMENT_RE.fullmatch(part) is None for part in parts):
        raise RegistryError(f"module identity: path cannot derive a Lean module: {path}")
    return ".".join(parts)


def _module_identity(
    value: Any, where: str, repo: Path, *, require_exists: bool
) -> dict[str, str]:
    identity = _object(value, where)
    _keys(
        identity,
        allowed=("source_root", "repo_relative_path", "lean_module"),
        required=("source_root", "repo_relative_path", "lean_module"),
        where=where,
    )
    source = _canonical_path(identity["source_root"], f"{where}.source_root")
    path = _canonical_path(
        identity["repo_relative_path"], f"{where}.repo_relative_path"
    )
    module = _lean_module(identity["lean_module"], f"{where}.lean_module")
    derived = module_from_path(source, path)
    if module != derived:
        raise RegistryError(
            f"{where}: module/path mismatch: declared {module}, derived {derived}"
        )
    _assert_inside_repo(repo, source, f"{where}.source_root", must_exist=require_exists)
    _assert_inside_repo(repo, path, f"{where}.repo_relative_path", must_exist=require_exists)
    return {"source_root": source, "repo_relative_path": path, "lean_module": module}


def _traits(value: Any, where: str) -> tuple[str, ...]:
    rows = _array(value, where)
    result = tuple(_closed_token(row, TRAITS, f"{where}[]") for row in rows)
    if len(set(result)) != len(result):
        raise RegistryError(f"{where}: duplicate trait")
    return result


def validate_schema_payload(schema: dict[str, Any]) -> None:
    _keys(
        schema,
        allowed=("$schema", "$id", "title", "type", "additionalProperties", "required", "properties", "$defs"),
        required=("$schema", "$id", "title", "type", "additionalProperties", "required", "properties", "$defs"),
        where="schema",
    )
    if (
        schema["$schema"] != "https://json-schema.org/draft/2020-12/schema"
        or schema["$id"] != "q3_module_class_registry.schema.v1"
        or schema["type"] != "object"
        or schema["additionalProperties"] is not False
    ):
        raise RegistryError("schema: root structural contract drift")
    if tuple(schema["required"]) != (
        "schema", "schema_ref", "version", "rules", "declared_coverage"
    ):
        raise RegistryError("schema: root required-field contract drift")
    root_properties = _object(schema["properties"], "schema.properties")
    if set(root_properties) != {
        "schema", "schema_ref", "version", "rules", "declared_coverage"
    }:
        raise RegistryError("schema: root property contract drift")
    if root_properties["schema"] != {"const": "q3_module_class_registry.v1"}:
        raise RegistryError("schema.properties.schema: const drift")
    if root_properties["schema_ref"] != {
        "const": "docs/semantic_quarantine/MODULE_CLASS_SCHEMA_v1.json"
    }:
        raise RegistryError("schema.properties.schema_ref: const drift")
    if root_properties["version"] != {"const": 1}:
        raise RegistryError("schema.properties.version: const drift")
    rules_schema = _object(root_properties["rules"], "schema.properties.rules")
    if (
        rules_schema.get("type") != "object"
        or rules_schema.get("additionalProperties") is not False
        or tuple(rules_schema.get("required", ())) != ("exact", "prefix")
        or set(_object(rules_schema.get("properties"), "schema.properties.rules.properties"))
        != {"exact", "prefix"}
    ):
        raise RegistryError("schema.properties.rules: structural contract drift")
    coverage_schema = _object(
        root_properties["declared_coverage"], "schema.properties.declared_coverage"
    )
    if coverage_schema.get("type") != "array" or coverage_schema.get("items") != {
        "$ref": "#/$defs/coverageRule"
    }:
        raise RegistryError("schema.properties.declared_coverage: structural contract drift")
    definitions = _object(schema["$defs"], "schema.$defs")
    expected_definitions = {
        "moduleClass",
        "artifactKind",
        "lifecycleStatus",
        "trait",
        "canonicalPath",
        "canonicalDirectoryPrefix",
        "ruleId",
        "leanModule",
        "leanModulePrefix",
        "moduleIdentity",
        "documentIdentity",
        "declarationOverride",
        "exactRule",
        "prefixRule",
        "coverageRule",
    }
    if set(definitions) != expected_definitions:
        raise RegistryError("schema.$defs: definition set drift")
    enum_contracts = {
        "moduleClass": MODULE_CLASSES,
        "artifactKind": ARTIFACT_KINDS,
        "lifecycleStatus": LIFECYCLE_STATUSES,
        "trait": TRAITS,
    }
    for name, expected in enum_contracts.items():
        definition = _object(definitions[name], f"schema.$defs.{name}")
        if set(definition) != {"enum"} or tuple(definition.get("enum", ())) != expected:
            raise RegistryError(f"schema.$defs.{name}: closed enum drift")
    object_contracts = {
        "moduleIdentity": (
            ("source_root", "repo_relative_path", "lean_module"),
            {"source_root", "repo_relative_path", "lean_module"},
        ),
        "documentIdentity": (
            ("repo_relative_path",), {"repo_relative_path"},
        ),
        "declarationOverride": (
            ("declaration", "module_class", "lifecycle_status", "traits", "source_identity"),
            {"declaration", "module_class", "lifecycle_status", "traits", "source_identity"},
        ),
        "exactRule": (
            ("id", "artifact_kind", "identity", "module_class", "lifecycle_status", "traits"),
            {
                "id", "artifact_kind", "identity", "module_class",
                "lifecycle_status", "traits", "physical_split",
                "declaration_overrides",
            },
        ),
        "prefixRule": (
            ("id", "artifact_kind", "match", "module_class", "lifecycle_status", "traits"),
            {"id", "artifact_kind", "match", "module_class", "lifecycle_status", "traits"},
        ),
        "coverageRule": (
            (
                "id", "artifact_kind", "source_root", "tracked_path_prefix",
                "lean_module_prefix", "expected_module_class",
            ),
            {
                "id", "artifact_kind", "source_root", "tracked_path_prefix",
                "lean_module_prefix", "expected_module_class",
            },
        ),
    }
    for name, (required, properties) in object_contracts.items():
        definition = _object(definitions[name], f"schema.$defs.{name}")
        expected_keys = {
            "type", "additionalProperties", "required", "properties"
        }
        if name == "exactRule":
            expected_keys.add("allOf")
        if (
            set(definition) != expected_keys
            or
            definition.get("type") != "object"
            or definition.get("additionalProperties") is not False
            or tuple(definition.get("required", ())) != required
            or set(_object(definition.get("properties"), f"schema.$defs.{name}.properties"))
            != properties
        ):
            raise RegistryError(f"schema.$defs.{name}: structural contract drift")
    leaf_contracts = {
        "canonicalPath": {
            "type": "string",
            "minLength": 1,
            "pattern": r"^[^/\\](?:[^\\]*[^/\\])?$",
            "$comment": (
                "This pattern excludes absolute paths, backslashes, and trailing "
                "separators. Dot segments and repeated separators are rejected by "
                "the executable canonical-path validator."
            ),
        },
        "canonicalDirectoryPrefix": {
            "type": "string",
            "minLength": 2,
            "pattern": r"^[^/\\](?:[^\\]*/)$",
        },
        "ruleId": {"type": "string", "pattern": "^[a-z0-9_]+$"},
        "leanModule": {
            "type": "string",
            "pattern": r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$",
        },
        "leanModulePrefix": {
            "type": "string",
            "pattern": r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\.$",
        },
    }
    for name, expected in leaf_contracts.items():
        if definitions[name] != expected:
            raise RegistryError(f"schema.$defs.{name}: leaf contract drift")
    expected_exact_discriminator = [
        {
            "if": {
                "properties": {"artifact_kind": {"const": "LEAN_MODULE"}},
                "required": ["artifact_kind"],
            },
            "then": {
                "properties": {
                    "identity": {"$ref": "#/$defs/moduleIdentity"}
                }
            },
        },
        {
            "if": {
                "properties": {"artifact_kind": {"const": "STATUS_DOCUMENT"}},
                "required": ["artifact_kind"],
            },
            "then": {
                "properties": {
                    "identity": {"$ref": "#/$defs/documentIdentity"},
                    "declaration_overrides": {"maxItems": 0},
                },
                "not": {"required": ["physical_split"]},
            },
        },
    ]
    if definitions["exactRule"].get("allOf") != expected_exact_discriminator:
        raise RegistryError("schema.$defs.exactRule: discriminator contract drift")
    reference_contracts = {
        ("moduleIdentity", "lean_module"): {"$ref": "#/$defs/leanModule"},
        ("exactRule", "id"): {"$ref": "#/$defs/ruleId"},
        ("exactRule", "identity"): {},
        ("prefixRule", "id"): {"$ref": "#/$defs/ruleId"},
        ("coverageRule", "id"): {"$ref": "#/$defs/ruleId"},
        ("coverageRule", "tracked_path_prefix"): {
            "$ref": "#/$defs/canonicalDirectoryPrefix"
        },
        ("coverageRule", "lean_module_prefix"): {
            "$ref": "#/$defs/leanModulePrefix"
        },
    }
    for (definition_name, property_name), expected in reference_contracts.items():
        actual = definitions[definition_name]["properties"][property_name]
        if actual != expected:
            raise RegistryError(
                f"schema.$defs.{definition_name}.properties.{property_name}: reference contract drift"
            )
    match_schema = _object(
        definitions["prefixRule"]["properties"]["match"],
        "schema.$defs.prefixRule.properties.match",
    )
    if (
        match_schema.get("type") != "object"
        or match_schema.get("additionalProperties") is not False
        or tuple(match_schema.get("required", ()))
        != ("source_root", "repo_relative_path_prefix", "lean_module_prefix")
        or set(_object(match_schema.get("properties"), "schema prefix match properties"))
        != {"source_root", "repo_relative_path_prefix", "lean_module_prefix"}
    ):
        raise RegistryError("schema.$defs.prefixRule.properties.match: structural contract drift")
    match_reference_contracts = {
        "repo_relative_path_prefix": {
            "$ref": "#/$defs/canonicalDirectoryPrefix"
        },
        "lean_module_prefix": {"$ref": "#/$defs/leanModulePrefix"},
    }
    for property_name, expected in match_reference_contracts.items():
        if match_schema["properties"][property_name] != expected:
            raise RegistryError(
                "schema.$defs.prefixRule.properties.match."
                f"{property_name}: reference contract drift"
            )
    canonical_schema = json.dumps(
        schema, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    if hashlib.sha256(canonical_schema).hexdigest() != SCHEMA_V1_CANONICAL_SHA256:
        raise RegistryError("schema: canonical v1 structural contract drift")


def _validate_exact_rule(
    value: Any, where: str, repo: Path, *, require_exists: bool
) -> dict[str, Any]:
    rule = _object(value, where)
    _keys(
        rule,
        allowed=(
            "id", "artifact_kind", "identity", "module_class",
            "lifecycle_status", "traits", "physical_split",
            "declaration_overrides",
        ),
        required=(
            "id", "artifact_kind", "identity", "module_class",
            "lifecycle_status", "traits",
        ),
        where=where,
    )
    rule_id = _rule_id(rule["id"], f"{where}.id")
    kind = _closed_token(rule["artifact_kind"], ARTIFACT_KINDS, f"{where}.artifact_kind")
    module_class = _closed_token(rule["module_class"], MODULE_CLASSES, f"{where}.module_class")
    lifecycle = _closed_token(rule["lifecycle_status"], LIFECYCLE_STATUSES, f"{where}.lifecycle_status")
    traits = _traits(rule["traits"], f"{where}.traits")
    overrides = rule.get("declaration_overrides", [])
    if kind == "LEAN_MODULE":
        identity = _module_identity(rule["identity"], f"{where}.identity", repo, require_exists=require_exists)
        if "physical_split" in rule and not isinstance(rule["physical_split"], bool):
            raise RegistryError(f"{where}.physical_split: boolean required")
    else:
        identity = _object(rule["identity"], f"{where}.identity")
        _keys(identity, allowed=("repo_relative_path",), required=("repo_relative_path",), where=f"{where}.identity")
        path = _canonical_path(identity["repo_relative_path"], f"{where}.identity.repo_relative_path")
        _assert_inside_repo(repo, path, f"{where}.identity.repo_relative_path", must_exist=require_exists)
        identity = {"repo_relative_path": path}
        if "physical_split" in rule or overrides:
            raise RegistryError(f"{where}: document rules cannot carry module split/overrides")
    checked_overrides: list[dict[str, Any]] = []
    for index, raw_override in enumerate(_array(overrides, f"{where}.declaration_overrides")):
        owhere = f"{where}.declaration_overrides[{index}]"
        override = _object(raw_override, owhere)
        _keys(
            override,
            allowed=("declaration", "module_class", "lifecycle_status", "traits", "source_identity"),
            required=("declaration", "module_class", "lifecycle_status", "traits", "source_identity"),
            where=owhere,
        )
        source_identity = _module_identity(
            override["source_identity"], f"{owhere}.source_identity", repo,
            require_exists=require_exists,
        )
        if source_identity != identity:
            raise RegistryError(f"{owhere}: override source mismatch")
        checked_overrides.append({
            "declaration": _string(override["declaration"], f"{owhere}.declaration"),
            "module_class": _closed_token(override["module_class"], MODULE_CLASSES, f"{owhere}.module_class"),
            "lifecycle_status": _closed_token(override["lifecycle_status"], LIFECYCLE_STATUSES, f"{owhere}.lifecycle_status"),
            "traits": _traits(override["traits"], f"{owhere}.traits"),
            "source_identity": source_identity,
        })
    declarations = [row["declaration"] for row in checked_overrides]
    if len(declarations) != len(set(declarations)):
        raise RegistryError(f"{where}: duplicate declaration override")
    return {
        "id": rule_id, "artifact_kind": kind, "identity": identity,
        "module_class": module_class, "lifecycle_status": lifecycle,
        "traits": traits, "physical_split": rule.get("physical_split"),
        "declaration_overrides": checked_overrides,
    }


def _validate_prefix_rule(
    value: Any, where: str, repo: Path, *, require_exists: bool
) -> dict[str, Any]:
    rule = _object(value, where)
    _keys(
        rule,
        allowed=("id", "artifact_kind", "match", "module_class", "lifecycle_status", "traits"),
        required=("id", "artifact_kind", "match", "module_class", "lifecycle_status", "traits"),
        where=where,
    )
    if rule["artifact_kind"] != "LEAN_MODULE":
        raise RegistryError(f"{where}.artifact_kind: prefix rules require LEAN_MODULE")
    match = _object(rule["match"], f"{where}.match")
    _keys(
        match,
        allowed=("source_root", "repo_relative_path_prefix", "lean_module_prefix"),
        required=("source_root", "repo_relative_path_prefix", "lean_module_prefix"),
        where=f"{where}.match",
    )
    source = _canonical_path(match["source_root"], f"{where}.match.source_root")
    path_prefix = _canonical_path(
        match["repo_relative_path_prefix"],
        f"{where}.match.repo_relative_path_prefix", directory_prefix=True,
    )
    module_prefix = _lean_module(
        match["lean_module_prefix"], f"{where}.match.lean_module_prefix",
        prefix=True,
    )
    source_path_prefix = f"{source}/"
    if not path_prefix.startswith(source_path_prefix):
        raise RegistryError(f"{where}.match: path prefix is outside source_root")
    relative = path_prefix[len(source_path_prefix) : -1]
    derived_prefix = ".".join(PurePosixPath(relative).parts) + "."
    if module_prefix != derived_prefix:
        raise RegistryError(
            f"{where}.match: module/path prefix mismatch: declared {module_prefix}, derived {derived_prefix}"
        )
    _assert_inside_repo(repo, source, f"{where}.match.source_root", must_exist=require_exists)
    _assert_inside_repo(repo, path_prefix[:-1], f"{where}.match.repo_relative_path_prefix", must_exist=require_exists)
    return {
        "id": _rule_id(rule["id"], f"{where}.id"),
        "artifact_kind": "LEAN_MODULE",
        "match": {"source_root": source, "repo_relative_path_prefix": path_prefix, "lean_module_prefix": module_prefix},
        "module_class": _closed_token(rule["module_class"], MODULE_CLASSES, f"{where}.module_class"),
        "lifecycle_status": _closed_token(rule["lifecycle_status"], LIFECYCLE_STATUSES, f"{where}.lifecycle_status"),
        "traits": _traits(rule["traits"], f"{where}.traits"),
    }


def tracked_lean_paths(repo: Path) -> list[str]:
    try:
        raw = subprocess.run(
            ["git", "ls-files", "-z", "--", "*.lean"],
            cwd=repo, check=True, capture_output=True,
        ).stdout
    except subprocess.CalledProcessError as exc:
        raise RegistryError("cannot enumerate tracked Lean paths with git") from exc
    return sorted(path for path in raw.decode("utf-8").split("\0") if path)


def _identity_for_tracked_path(source_root: str, path: str) -> dict[str, str]:
    return {
        "source_root": source_root,
        "repo_relative_path": path,
        "lean_module": module_from_path(source_root, path),
    }


def resolve_module_rule(
    checked: dict[str, Any], identity: dict[str, str]
) -> dict[str, Any] | None:
    exact = [
        rule for rule in checked["exact"]
        if rule["artifact_kind"] == "LEAN_MODULE" and rule["identity"] == identity
    ]
    if len(exact) > 1:
        raise RegistryError("resolution: duplicate exact module identity")
    if exact:
        return exact[0]
    matches = []
    for rule in checked["prefix"]:
        match = rule["match"]
        if (
            identity["source_root"] == match["source_root"]
            and identity["repo_relative_path"].startswith(match["repo_relative_path_prefix"])
            and identity["lean_module"].startswith(match["lean_module_prefix"])
        ):
            matches.append(rule)
    if not matches:
        return None
    longest = max(len(rule["match"]["repo_relative_path_prefix"]) for rule in matches)
    winners = [rule for rule in matches if len(rule["match"]["repo_relative_path_prefix"]) == longest]
    if len(winners) != 1:
        raise RegistryError("resolution: equal-specificity prefix conflict")
    return winners[0]


def validate_registry_payload(
    registry: dict[str, Any], schema: dict[str, Any], *, repo: Path = REPO,
    tracked_paths: list[str] | None = None, require_exists: bool = True,
) -> dict[str, Any]:
    validate_schema_payload(schema)
    _keys(
        registry,
        allowed=("schema", "schema_ref", "version", "rules", "declared_coverage"),
        required=("schema", "schema_ref", "version", "rules", "declared_coverage"),
        where="registry",
    )
    if registry["schema"] != "q3_module_class_registry.v1":
        raise RegistryError("registry.schema: unsupported schema")
    if registry["schema_ref"] != "docs/semantic_quarantine/MODULE_CLASS_SCHEMA_v1.json":
        raise RegistryError("registry.schema_ref: drift")
    if registry["version"] != 1 or isinstance(registry["version"], bool):
        raise RegistryError("registry.version: expected integer 1")
    rules = _object(registry["rules"], "registry.rules")
    _keys(rules, allowed=("exact", "prefix"), required=("exact", "prefix"), where="registry.rules")
    exact = [
        _validate_exact_rule(row, f"registry.rules.exact[{index}]", repo, require_exists=require_exists)
        for index, row in enumerate(_array(rules["exact"], "registry.rules.exact"))
    ]
    prefix = [
        _validate_prefix_rule(row, f"registry.rules.prefix[{index}]", repo, require_exists=require_exists)
        for index, row in enumerate(_array(rules["prefix"], "registry.rules.prefix"))
    ]
    coverage_raw = _array(registry["declared_coverage"], "registry.declared_coverage")
    coverage: list[dict[str, str]] = []
    for index, raw in enumerate(coverage_raw):
        where = f"registry.declared_coverage[{index}]"
        row = _object(raw, where)
        _keys(
            row,
            allowed=("id", "artifact_kind", "source_root", "tracked_path_prefix", "lean_module_prefix", "expected_module_class"),
            required=("id", "artifact_kind", "source_root", "tracked_path_prefix", "lean_module_prefix", "expected_module_class"),
            where=where,
        )
        if row["artifact_kind"] != "LEAN_MODULE":
            raise RegistryError(f"{where}.artifact_kind: coverage requires LEAN_MODULE")
        source = _canonical_path(row["source_root"], f"{where}.source_root")
        path_prefix = _canonical_path(row["tracked_path_prefix"], f"{where}.tracked_path_prefix", directory_prefix=True)
        module_prefix = _lean_module(
            row["lean_module_prefix"], f"{where}.lean_module_prefix", prefix=True
        )
        source_prefix = f"{source}/"
        if not path_prefix.startswith(source_prefix):
            raise RegistryError(f"{where}: coverage prefix is outside source_root")
        derived_prefix = ".".join(PurePosixPath(path_prefix[len(source_prefix):-1]).parts) + "."
        if module_prefix != derived_prefix:
            raise RegistryError(f"{where}: coverage module/path prefix mismatch")
        coverage.append({
            "id": _rule_id(row["id"], f"{where}.id"), "artifact_kind": "LEAN_MODULE",
            "source_root": source, "tracked_path_prefix": path_prefix,
            "lean_module_prefix": module_prefix,
            "expected_module_class": _closed_token(row["expected_module_class"], MODULE_CLASSES, f"{where}.expected_module_class"),
        })

    all_ids = [rule["id"] for rule in exact + prefix] + [row["id"] for row in coverage]
    if len(all_ids) != len(set(all_ids)):
        raise RegistryError("registry: duplicate rule/coverage id")
    module_exact = [rule for rule in exact if rule["artifact_kind"] == "LEAN_MODULE"]
    exact_paths = [rule["identity"]["repo_relative_path"] for rule in exact]
    if len(exact_paths) != len(set(exact_paths)):
        raise RegistryError("registry: duplicate exact path")
    exact_modules = [rule["identity"]["lean_module"] for rule in module_exact]
    if len(exact_modules) != len(set(exact_modules)):
        raise RegistryError("registry: duplicate exact Lean module")
    prefix_keys = [
        (rule["match"]["source_root"], rule["match"]["repo_relative_path_prefix"], rule["match"]["lean_module_prefix"])
        for rule in prefix
    ]
    if len(prefix_keys) != len(set(prefix_keys)):
        raise RegistryError("registry: equal-specificity prefix conflict")

    root_rules = [rule for rule in module_exact if rule["identity"] == Q3_ROOT_IDENTITY]
    if len(root_rules) != 1:
        raise RegistryError("registry: exactly one Q3 root rule required")
    root_rule = root_rules[0]
    if (
        root_rule["module_class"] != "CONDITIONAL_COMPILED"
        or root_rule["lifecycle_status"] != "ACTIVE"
        or root_rule["traits"] != ("PROJECT_AXIOMS", "LEGACY_BROAD_CONE")
    ):
        raise RegistryError("registry: Q3 root classification contract drift")

    defs_rules = [rule for rule in module_exact if rule["identity"] == Q3_BASIC_DEFS_IDENTITY]
    if len(defs_rules) != 1:
        raise RegistryError("registry: exactly one Q3.Basic.Defs rule required")
    defs_rule = defs_rules[0]
    if defs_rule["module_class"] != "CORE_SHARED" or defs_rule["physical_split"] is not False:
        raise RegistryError("registry: Q3.Basic.Defs must be unsplit CORE_SHARED")
    declarations = {row["declaration"] for row in defs_rule["declaration_overrides"]}
    if declarations != FROZEN_Q3_BASIC_DEFS_OVERRIDES:
        raise RegistryError("registry: frozen Q3.Basic.Defs override set drift")
    for row in defs_rule["declaration_overrides"]:
        if (
            row["source_identity"] != Q3_BASIC_DEFS_IDENTITY
            or row["module_class"] != "LEGACY"
            or row["lifecycle_status"] != "COMPATIBILITY_ONLY"
            or row["traits"] != ("LEGACY_BROAD_CONE",)
        ):
            raise RegistryError("registry: Q3.Basic.Defs override contract drift")

    checked = {"exact": exact, "prefix": prefix}
    live_paths = tracked_lean_paths(repo) if tracked_paths is None else sorted(tracked_paths)
    coverage_counts: dict[str, int] = {}
    for row in coverage:
        paths = [
            path for path in live_paths
            if path.startswith(row["tracked_path_prefix"]) and path.endswith(".lean")
        ]
        if not paths:
            raise RegistryError(f"coverage {row['id']}: no tracked Lean modules")
        for path in paths:
            _canonical_path(path, f"coverage {row['id']} tracked leaf")
            _assert_tracked_leaf(repo, path, f"coverage {row['id']}")
            identity = _identity_for_tracked_path(row["source_root"], path)
            if not identity["lean_module"].startswith(row["lean_module_prefix"]):
                raise RegistryError(f"coverage {row['id']}: tracked module prefix mismatch: {path}")
            resolved = resolve_module_rule(checked, identity)
            if resolved is None:
                raise RegistryError(f"coverage {row['id']}: unclassified tracked module: {path}")
            if resolved["module_class"] != row["expected_module_class"]:
                raise RegistryError(
                    f"coverage {row['id']}: {path} resolved as {resolved['module_class']}, expected {row['expected_module_class']}"
                )
        coverage_counts[row["id"]] = len(paths)

    return {
        "schema": registry["schema"],
        "exact_rules": len(exact),
        "prefix_rules": len(prefix),
        "coverage": coverage_counts,
        "q3_root_class": root_rule["module_class"],
        "frozen_q3_basic_defs_overrides": len(FROZEN_Q3_BASIC_DEFS_OVERRIDES),
        "success": "MODULE_CLASS_SCHEMA_AND_REGISTRY_CONTRACT_VALID",
    }


def validate_registry(
    *, repo: Path = REPO, schema_path: Path = SCHEMA_PATH,
    registry_path: Path = REGISTRY_PATH,
) -> dict[str, Any]:
    return validate_registry_payload(
        load_json(registry_path), load_json(schema_path), repo=repo
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate the registry")
    parser.add_argument("--json", action="store_true", help="emit compact JSON")
    args = parser.parse_args()
    if not args.check:
        parser.error("--check is required")
    result = validate_registry()
    if args.json:
        print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
