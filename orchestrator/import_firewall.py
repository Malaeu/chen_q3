#!/usr/bin/env python3
"""Build and verify the P6 Lean import and declaration-use firewall."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

import jsonschema

REPO = Path(__file__).resolve().parents[1]
POLICY_PATH = REPO / "docs/semantic_quarantine/IMPORT_FIREWALL_POLICY_v1.json"
RECEIPT_PATH = REPO / "docs/semantic_quarantine/IMPORT_FIREWALL_RECEIPT_v1.json"
CHECKER_PATH = REPO / "orchestrator/import_firewall.py"
TOOLCHAIN_PATH = REPO / "q3.lean.aristotle/lean-toolchain"
RUNTIME_INPUT_PATHS = {
    "launcher": REPO / "scripts/check_import_firewall.sh",
    "python_project": REPO / "pyproject.toml",
    "python_lock": REPO / "uv.lock",
    "lakefile": REPO / "q3.lean.aristotle/lakefile.toml",
    "lake_manifest": REPO / "q3.lean.aristotle/lake-manifest.json",
}

MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")
IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\s*$"
)
IMPORT_PREFIX_RE = re.compile(r"^\s*(?:public\s+)?import\b")


class FirewallError(RuntimeError):
    """Fail-closed import-firewall error."""


@dataclass(frozen=True)
class ModuleRule:
    module: str
    path: str
    module_class: str
    lifecycle_status: str


def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise FirewallError(f"DUPLICATE_JSON_KEY: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicates)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FirewallError(f"INVALID_JSON: {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise FirewallError(f"INVALID_JSON_ROOT: {path}")
    return value


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode(
        "utf-8"
    )


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_path(value: Any) -> str:
    if not isinstance(value, str):
        raise FirewallError(f"NONCANONICAL_REPO_PATH: {value!r}")
    path = PurePosixPath(value)
    if (
        not value
        or path.is_absolute()
        or "\\" in value
        or "//" in value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise FirewallError(f"NONCANONICAL_REPO_PATH: {value!r}")
    return value


def validate_policy(policy: dict[str, Any]) -> None:
    required = {
        "schema",
        "version",
        "registry_path",
        "registry_schema_path",
        "source_root",
        "public_root_class",
        "external_import_policy",
        "local_reachability_policy",
        "allowed_class_edges",
        "forbidden_public_target_classes",
        "semantic_declaration_audit",
        "required_plants",
        "positive_controls",
    }
    if (
        set(policy) != required
        or policy.get("schema") != "q3_import_firewall_policy.v1"
        or policy.get("version") != 1
    ):
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: top-level contract")
    for key in ("registry_path", "registry_schema_path", "source_root"):
        canonical_path(policy[key])
    if policy["public_root_class"] != "PUBLIC_CANONICAL":
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: public root class")
    if (
        policy["external_import_policy"] != "ALLOW_UNCLASSIFIED_NONLOCAL"
        or policy["local_reachability_policy"] != "REQUIRE_CLASSIFICATION"
    ):
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: reachability policy")
    expected_edges = {
        "PUBLIC_CANONICAL": ["CORE_SHARED", "PUBLIC_CANONICAL"],
        "CORE_SHARED": ["CORE_SHARED"],
    }
    if policy["allowed_class_edges"] != expected_edges:
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: class edge contract")
    semantic = policy["semantic_declaration_audit"]
    if set(semantic) != {
        "enabled",
        "engine",
        "inspect",
        "forbidden_override_classes",
        "mixed_module_rule",
    }:
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: semantic contract")
    if (
        semantic["enabled"] is not True
        or semantic["engine"] != "LEAN_ENVIRONMENT_TRANSITIVE_CONSTANT_REFERENCES"
        or semantic["inspect"] != ["TYPE", "VALUE"]
    ):
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: semantic engine")
    expected_forbidden = [
        "ARCHIVE",
        "CHALLENGER",
        "CONDITIONAL_COMPILED",
        "EXPERIMENT",
        "GENERATED_VIEW",
        "LEGACY",
    ]
    if policy["forbidden_public_target_classes"] != expected_forbidden:
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: forbidden target classes")
    if semantic["forbidden_override_classes"] != expected_forbidden:
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: forbidden override classes")
    if (
        semantic["mixed_module_rule"]
        != "MODULE_EDGE_ALLOWED_ONLY_IF_FORBIDDEN_DECLARATION_CLOSURE_IS_EMPTY"
    ):
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: mixed module rule")
    if policy["required_plants"] != [
        "PUBLIC_IMPORTS_LEGACY_MODULE",
        "PUBLIC_DECLARATION_USES_LEGACY_OVERRIDE",
        "PUBLIC_TRANSITIVE_DECLARATION_USES_LEGACY_OVERRIDE",
        "PUBLIC_TYPE_USES_LEGACY_OVERRIDE",
        "UNPARSED_IMPORT_FAIL_CLOSED",
    ]:
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: plant contract")
    if policy["positive_controls"] != [
        "CURRENT_PUBLIC_CANONICAL_SLICE",
        "LEGACY_COMPATIBILITY_CLASS_REMAINS_SEPARATE",
    ]:
        raise FirewallError("IMPORT_FIREWALL_POLICY_INVALID: positive controls")


def validate_registry(registry: dict[str, Any], schema: dict[str, Any]) -> None:
    errors = sorted(
        jsonschema.Draft202012Validator(schema).iter_errors(registry),
        key=lambda error: list(error.path),
    )
    if errors:
        raise FirewallError(f"MODULE_CLASS_SCHEMA_INVALID: {errors[0].message}")
    ids: set[str] = set()
    modules: set[str] = set()
    paths: set[str] = set()
    for rule in registry["rules"]["exact"]:
        if rule["id"] in ids:
            raise FirewallError(f"MODULE_CLASS_DUPLICATE_ID: {rule['id']}")
        ids.add(rule["id"])
        if rule["artifact_kind"] != "LEAN_MODULE":
            continue
        identity = rule["identity"]
        canonical_path(identity["repo_relative_path"])
        if identity["lean_module"] in modules or identity["repo_relative_path"] in paths:
            raise FirewallError(f"MODULE_CLASS_DUPLICATE_IDENTITY: {rule['id']}")
        modules.add(identity["lean_module"])
        paths.add(identity["repo_relative_path"])
        if not MODULE_RE.fullmatch(identity["lean_module"]):
            raise FirewallError(f"MODULE_CLASS_INVALID_MODULE: {identity['lean_module']}")


def tracked_lean_modules(source_root: str) -> dict[str, str]:
    raw = subprocess.run(
        ["git", "ls-files", "-z"], cwd=REPO, check=True, capture_output=True
    ).stdout.decode("utf-8")
    result: dict[str, str] = {}
    prefix = source_root + "/"
    for path in raw.split("\0"):
        if not path.startswith(prefix) or not path.endswith(".lean"):
            continue
        relative = path[len(prefix) : -len(".lean")]
        parts = relative.split("/")
        if not parts or not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", part) for part in parts):
            continue
        module = ".".join(parts)
        if module in result and result[module] != path:
            raise FirewallError(f"IMPORT_GRAPH_DUPLICATE_MODULE: {module}")
        result[module] = path
    return result


def local_lean_modules(source_root: str) -> dict[str, str]:
    """Return tracked and on-disk local modules, including untracked worktree sources."""
    result = tracked_lean_modules(source_root)
    root = REPO / source_root
    for candidate in root.rglob("*.lean"):
        relative_parts = candidate.relative_to(root).parts
        if not relative_parts or ".lake" in relative_parts:
            continue
        stem_parts = list(relative_parts)
        stem_parts[-1] = Path(stem_parts[-1]).stem
        if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", part) for part in stem_parts):
            continue
        module = ".".join(stem_parts)
        path = candidate.relative_to(REPO).as_posix()
        previous = result.get(module)
        if previous is not None and previous != path:
            raise FirewallError(f"IMPORT_GRAPH_DUPLICATE_MODULE: {module}")
        result[module] = path
    return result


def strip_lean_comments(text: str, *, source: str) -> str:
    """Remove nested Lean comments while preserving line structure."""
    result: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if line_comment:
            if char == "\n":
                line_comment = False
                result.append(char)
            else:
                result.append(" ")
            index += 1
            continue
        if block_depth:
            if pair == "/-":
                block_depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if pair == "--":
            line_comment = True
            result.extend("  ")
            index += 2
        elif pair == "/-":
            block_depth = 1
            result.extend("  ")
            index += 2
        else:
            result.append(char)
            index += 1
    if block_depth:
        raise FirewallError(f"UNTERMINATED_LEAN_COMMENT: {source}")
    return "".join(result)


def imports_from_text(text: str, *, source: str) -> list[str]:
    imports: list[str] = []
    for line_number, line in enumerate(strip_lean_comments(text, source=source).splitlines(), 1):
        match = IMPORT_RE.fullmatch(line)
        if match:
            imports.append(match.group(1))
        elif IMPORT_PREFIX_RE.match(line):
            raise FirewallError(f"UNPARSED_IMPORT: {source}:{line_number}: {line.strip()}")
    return imports


def imports_for(path: str) -> list[str]:
    try:
        text = (REPO / path).read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise FirewallError(f"IMPORT_SOURCE_UNREADABLE: {path}: {exc}") from exc
    return imports_from_text(text, source=path)


def exact_rules(registry: dict[str, Any]) -> dict[str, ModuleRule]:
    result: dict[str, ModuleRule] = {}
    for rule in registry["rules"]["exact"]:
        if rule["artifact_kind"] != "LEAN_MODULE":
            continue
        identity = rule["identity"]
        result[identity["lean_module"]] = ModuleRule(
            identity["lean_module"],
            identity["repo_relative_path"],
            rule["module_class"],
            rule["lifecycle_status"],
        )
    return result


def classify_module(
    module: str, path: str, registry: dict[str, Any], exact: dict[str, ModuleRule]
) -> ModuleRule | None:
    matches: list[ModuleRule] = []
    for rule in registry["rules"]["prefix"]:
        match = rule["match"]
        if module.startswith(match["lean_module_prefix"]) and path.startswith(
            match["repo_relative_path_prefix"]
        ):
            matches.append(ModuleRule(module, path, rule["module_class"], rule["lifecycle_status"]))
    if module in exact:
        rule = exact[module]
        if rule.path != path:
            raise FirewallError(f"MODULE_CLASS_PATH_MISMATCH: {module}: {path} != {rule.path}")
        if matches:
            raise FirewallError(f"MODULE_CLASS_AMBIGUOUS: exact and prefix: {module}")
        return rule
    if len(matches) > 1:
        raise FirewallError(f"MODULE_CLASS_AMBIGUOUS: {module}")
    return matches[0] if matches else None


def build_graph(
    policy: dict[str, Any],
    registry: dict[str, Any],
    *,
    module_paths: dict[str, str] | None = None,
    source_texts: dict[str, str] | None = None,
) -> dict[str, Any]:
    source_root = policy["source_root"]
    modules = local_lean_modules(source_root) if module_paths is None else module_paths
    exact = exact_rules(registry)
    for rule in exact.values():
        if rule.module_class != policy["public_root_class"]:
            continue
        if modules.get(rule.module) != rule.path:
            raise FirewallError(
                f"PUBLIC_CANONICAL_MODULE_MISSING: {rule.module}: expected {rule.path}"
            )
    roots = sorted(
        module
        for module, path in modules.items()
        if (rule := classify_module(module, path, registry, exact)) is not None
        and rule.module_class == policy["public_root_class"]
    )
    if not roots:
        raise FirewallError("PUBLIC_REACHABILITY_UNCLASSIFIED: no public roots")
    allowed = {source: set(targets) for source, targets in policy["allowed_class_edges"].items()}
    local_namespaces = {module.partition(".")[0] for module in modules}
    reachable: dict[str, ModuleRule] = {}
    local_edges: set[tuple[str, str, str, str]] = set()
    external_edges: set[tuple[str, str]] = set()
    pending = list(reversed(roots))
    while pending:
        module = pending.pop()
        path = modules.get(module)
        if path is None:
            raise FirewallError(f"IMPORT_GRAPH_MODULE_MISSING: {module}")
        source_rule = classify_module(module, path, registry, exact)
        if source_rule is None:
            raise FirewallError(f"PUBLIC_REACHABILITY_UNCLASSIFIED: {module}")
        if module in reachable:
            continue
        reachable[module] = source_rule
        if source_texts is None:
            imports = imports_for(path)
        else:
            if path not in source_texts:
                raise FirewallError(f"IMPORT_SOURCE_UNREADABLE: {path}")
            imports = imports_from_text(source_texts[path], source=path)
        for target in imports:
            target_path = modules.get(target)
            if target_path is None:
                if target.partition(".")[0] in local_namespaces:
                    raise FirewallError(f"IMPORT_GRAPH_LOCAL_MODULE_MISSING: {module} -> {target}")
                external_edges.add((module, target))
                continue
            target_rule = classify_module(target, target_path, registry, exact)
            if target_rule is None:
                raise FirewallError(f"PUBLIC_REACHABILITY_UNCLASSIFIED: {module} -> {target}")
            local_edges.add((module, source_rule.module_class, target, target_rule.module_class))
            if target_rule.module_class not in allowed.get(source_rule.module_class, set()):
                raise FirewallError(
                    f"FORBIDDEN_IMPORT_EDGE_SURVIVED: {module} [{source_rule.module_class}] -> "
                    f"{target} [{target_rule.module_class}]"
                )
            pending.append(target)
    return {
        "public_roots": roots,
        "reachable_modules": [
            {"module": rule.module, "path": rule.path, "module_class": rule.module_class}
            for rule in sorted(reachable.values(), key=lambda item: item.module)
        ],
        "local_edges": [
            {
                "source": source,
                "source_class": source_class,
                "target": target,
                "target_class": target_class,
            }
            for source, source_class, target, target_class in sorted(local_edges)
        ],
        "external_imports": [
            {"source": source, "target": target} for source, target in sorted(external_edges)
        ],
    }


def forbidden_declarations(
    registry: dict[str, Any], policy: dict[str, Any], reachable_modules: set[str]
) -> tuple[list[str], list[str]]:
    forbidden_classes = set(policy["semantic_declaration_audit"]["forbidden_override_classes"])
    declarations: set[str] = set()
    mixed_modules: set[str] = set()
    for rule in registry["rules"]["exact"]:
        if rule["artifact_kind"] != "LEAN_MODULE":
            continue
        module = rule["identity"]["lean_module"]
        if module not in reachable_modules:
            continue
        for override in rule.get("declaration_overrides", []):
            if override["module_class"] in forbidden_classes:
                declaration = override["declaration"]
                if not MODULE_RE.fullmatch(declaration):
                    raise FirewallError(f"SEMANTIC_AUDIT_INVALID_DECLARATION: {declaration}")
                declarations.add(declaration)
                mixed_modules.add(module)
    return sorted(declarations), sorted(mixed_modules)


def lean_name(value: str) -> str:
    if not MODULE_RE.fullmatch(value):
        raise FirewallError(f"SEMANTIC_AUDIT_INVALID_NAME: {value}")
    return "`" + value


def semantic_source(
    public_modules: list[str],
    traversed_modules: list[str],
    forbidden: list[str],
    *,
    plant: str | None,
) -> str:
    imports = "\n".join(f"import {module}" for module in public_modules)
    public_names = ", ".join(lean_name(name) for name in public_modules)
    traversed_names = ", ".join(lean_name(name) for name in traversed_modules)
    forbidden_names = ", ".join(lean_name(name) for name in forbidden)
    plant_decl = ""
    explicit_roots = "#[]"
    explicit_allowed = ""
    if plant == "DIRECT_VALUE":
        plant_decl = "\nnamespace Q3\ndef ImportFirewallDirectValuePlant := Weil_cone\nend Q3\n"
        explicit_roots = "#[`Q3.ImportFirewallDirectValuePlant]"
        explicit_allowed = "`Q3.ImportFirewallDirectValuePlant"
    elif plant == "TRANSITIVE_VALUE":
        plant_decl = (
            "\nnamespace Q3\n"
            "def ImportFirewallTransitiveHelper := Weil_cone\n"
            "def ImportFirewallTransitiveValuePlant := ImportFirewallTransitiveHelper\n"
            "end Q3\n"
        )
        explicit_roots = "#[`Q3.ImportFirewallTransitiveValuePlant]"
        explicit_allowed = (
            "`Q3.ImportFirewallTransitiveValuePlant, `Q3.ImportFirewallTransitiveHelper"
        )
    elif plant == "TYPE":
        plant_decl = (
            "\nnamespace Q3\naxiom ImportFirewallTypePlant : Weil_cone = Weil_cone\nend Q3\n"
        )
        explicit_roots = "#[`Q3.ImportFirewallTypePlant]"
        explicit_allowed = "`Q3.ImportFirewallTypePlant"
    return f"""{imports}
import Lean
{plant_decl}
open Lean Elab Command

private def moduleNameFor? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

private def refsOf (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  match ci.value? true with
  | some value => fromType ++ value.getUsedConstants
  | none => fromType

private partial def visit
    (env : Environment) (traversed forbidden explicitAllowed : Std.HashSet Name)
    (n : Name) (path : List Name) :
    StateT (Std.HashSet Name) (Except String) Nat := do
  if forbidden.contains n then
    let rendered := String.intercalate " -> " ((n :: path).reverse.map toString)
    throw s!"FORBIDDEN_DECLARATION_USE: {{rendered}}"
  if !path.isEmpty && !explicitAllowed.contains n &&
      !(moduleNameFor? env n).any traversed.contains then return 0
  let seen ← get
  if seen.contains n then return 0
  set (seen.insert n)
  match env.find? n with
  | none => return 0
  | some ci =>
    let mut count := 1
    for ref in refsOf ci do
      count := count + (← visit env traversed forbidden explicitAllowed ref (n :: path))
    return count

private def declarationsForModule (env : Environment) (m : Name) : Array Name :=
  match env.header.moduleNames.findIdx? (· == m) with
  | some idx => env.header.moduleData[idx]!.constNames
  | none => #[]

run_cmd do
  let env ← getEnv
  let publicModuleList := #[{public_names}]
  let traversed : Std.HashSet Name := Std.HashSet.ofList [{traversed_names}]
  let forbidden : Std.HashSet Name := Std.HashSet.ofList [{forbidden_names}]
  let explicitAllowed : Std.HashSet Name := Std.HashSet.ofList [{explicit_allowed}]
  let moduleRoots := publicModuleList.foldl (fun acc m => acc ++ declarationsForModule env m) #[]
  let roots := moduleRoots ++ {explicit_roots}
  let action : StateT (Std.HashSet Name) (Except String) Nat := do
    let mut checked := 0
    for root in roots do
      checked := checked + (← visit env traversed forbidden explicitAllowed root [])
    return checked
  match action.run {{}} with
  | .error msg => throwError msg
  | .ok (checked, _) =>
    logInfo m!"IMPORT_FIREWALL_SEMANTIC_PASS \
public_declarations={{moduleRoots.size}} checked_declarations={{checked}}"
"""


def run_semantic_audit(
    graph: dict[str, Any],
    registry: dict[str, Any],
    policy: dict[str, Any],
    *,
    plant: str | None = None,
) -> dict[str, Any]:
    reachable = {row["module"] for row in graph["reachable_modules"]}
    forbidden, mixed_modules = forbidden_declarations(registry, policy, reachable)
    if not forbidden:
        raise FirewallError("SEMANTIC_AUDIT_FORBIDDEN_SET_EMPTY")
    source = semantic_source(graph["public_roots"], sorted(reachable), forbidden, plant=plant)
    env = dict(os.environ)
    env.pop("LD_LIBRARY_PATH", None)
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=REPO / policy["source_root"],
        input=source,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )
    output = (result.stdout + "\n" + result.stderr).strip()
    if plant is not None:
        if result.returncode == 0 or "FORBIDDEN_DECLARATION_USE" not in output:
            raise FirewallError(f"IMPORT_FIREWALL_PLANT_ESCAPED: semantic plant: {output[-1000:]}")
        names = {
            "DIRECT_VALUE": "PUBLIC_DECLARATION_USES_LEGACY_OVERRIDE",
            "TRANSITIVE_VALUE": "PUBLIC_TRANSITIVE_DECLARATION_USES_LEGACY_OVERRIDE",
            "TYPE": "PUBLIC_TYPE_USES_LEGACY_OVERRIDE",
        }
        return {"plant": names[plant], "status": "REJECTED"}
    if result.returncode != 0:
        raise FirewallError(f"FORBIDDEN_DECLARATION_USE: {output[-2000:]}")
    match = re.search(
        r"IMPORT_FIREWALL_SEMANTIC_PASS public_declarations=([0-9]+) checked_declarations=([0-9]+)",
        output,
    )
    if not match:
        raise FirewallError(f"SEMANTIC_AUDIT_OUTPUT_INVALID: {output[-1000:]}")
    return {
        "engine": policy["semantic_declaration_audit"]["engine"],
        "public_declarations": int(match.group(1)),
        "checked_declarations": int(match.group(2)),
        "mixed_modules": mixed_modules,
        "forbidden_declarations": forbidden,
        "status": "PASS",
    }


def build_public_roots(graph: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    roots = graph["public_roots"]
    if not roots:
        raise FirewallError("PUBLIC_REACHABILITY_UNCLASSIFIED: no public roots")
    env = dict(os.environ)
    env.pop("LD_LIBRARY_PATH", None)
    result = subprocess.run(
        ["lake", "build", *roots],
        cwd=REPO / policy["source_root"],
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )
    if result.returncode != 0:
        output = (result.stdout + "\n" + result.stderr).strip()
        raise FirewallError(f"PUBLIC_ROOT_FRESH_BUILD_FAILED: {output[-2000:]}")
    return {"roots": roots, "status": "PASS"}


def run_import_edge_plant(policy: dict[str, Any]) -> dict[str, str]:
    plant_registry = {
        "rules": {
            "exact": [
                {
                    "id": "plant_public",
                    "artifact_kind": "LEAN_MODULE",
                    "identity": {
                        "lean_module": "Plant.Public",
                        "repo_relative_path": "plant/Plant/Public.lean",
                    },
                    "module_class": "PUBLIC_CANONICAL",
                    "lifecycle_status": "CANDIDATE",
                },
                {
                    "id": "plant_legacy",
                    "artifact_kind": "LEAN_MODULE",
                    "identity": {
                        "lean_module": "Plant.Legacy",
                        "repo_relative_path": "plant/Plant/Legacy.lean",
                    },
                    "module_class": "LEGACY",
                    "lifecycle_status": "COMPATIBILITY_ONLY",
                },
            ],
            "prefix": [],
        }
    }
    paths = {
        "Plant.Public": "plant/Plant/Public.lean",
        "Plant.Legacy": "plant/Plant/Legacy.lean",
    }
    sources = {
        "plant/Plant/Public.lean": "import Plant.Legacy\n",
        "plant/Plant/Legacy.lean": "",
    }
    try:
        build_graph(policy, plant_registry, module_paths=paths, source_texts=sources)
    except FirewallError as exc:
        if "FORBIDDEN_IMPORT_EDGE_SURVIVED" not in str(exc):
            raise
        return {"plant": "PUBLIC_IMPORTS_LEGACY_MODULE", "status": "REJECTED"}
    raise FirewallError("IMPORT_FIREWALL_PLANT_ESCAPED: import plant")


def run_unparsed_import_plant() -> dict[str, str]:
    try:
        imports_from_text("import Plant.Good Plant.Hidden\n", source="plant/unparsed.lean")
    except FirewallError as exc:
        if "UNPARSED_IMPORT" not in str(exc):
            raise
        return {"plant": "UNPARSED_IMPORT_FAIL_CLOSED", "status": "REJECTED"}
    raise FirewallError("IMPORT_FIREWALL_PLANT_ESCAPED: unparsed import plant")


def load_inputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    policy = load_json(POLICY_PATH)
    validate_policy(policy)
    registry_path = REPO / canonical_path(policy["registry_path"])
    schema_path = REPO / canonical_path(policy["registry_schema_path"])
    registry = load_json(registry_path)
    schema = load_json(schema_path)
    validate_registry(registry, schema)
    return policy, registry, schema


def build_receipt(*, run_plants: bool = True) -> dict[str, Any]:
    policy, registry, _schema = load_inputs()
    graph = build_graph(policy, registry)
    public_build = build_public_roots(graph, policy)
    semantic = run_semantic_audit(graph, registry, policy)
    plants = []
    if run_plants:
        plants = [
            run_import_edge_plant(policy),
            run_semantic_audit(graph, registry, policy, plant="DIRECT_VALUE"),
            run_semantic_audit(graph, registry, policy, plant="TRANSITIVE_VALUE"),
            run_semantic_audit(graph, registry, policy, plant="TYPE"),
            run_unparsed_import_plant(),
        ]
    legacy_rules = [
        rule["identity"]["lean_module"]
        for rule in registry["rules"]["exact"]
        if rule["artifact_kind"] == "LEAN_MODULE" and rule["module_class"] == "LEGACY"
    ]
    if not legacy_rules or set(legacy_rules) & set(graph["public_roots"]):
        raise FirewallError("LEGACY_COMPAT_BUILD_BROKEN: compatibility class is not separate")
    receipt = {
        "schema": "q3_import_firewall_receipt.v1",
        "version": 1,
        "inputs": {
            "policy": {
                "path": POLICY_PATH.relative_to(REPO).as_posix(),
                "sha256": sha256(POLICY_PATH),
            },
            "registry": {
                "path": policy["registry_path"],
                "sha256": sha256(REPO / policy["registry_path"]),
            },
            "registry_schema": {
                "path": policy["registry_schema_path"],
                "sha256": sha256(REPO / policy["registry_schema_path"]),
            },
            "checker": {
                "path": CHECKER_PATH.relative_to(REPO).as_posix(),
                "sha256": sha256(CHECKER_PATH),
            },
            "lean_toolchain": {
                "path": TOOLCHAIN_PATH.relative_to(REPO).as_posix(),
                "sha256": sha256(TOOLCHAIN_PATH),
            },
            **{
                name: {
                    "path": path.relative_to(REPO).as_posix(),
                    "sha256": sha256(path),
                }
                for name, path in RUNTIME_INPUT_PATHS.items()
            },
        },
        "graph": graph,
        "graph_sha256": hashlib.sha256(canonical_json(graph)).hexdigest(),
        "public_root_fresh_build": public_build,
        "semantic_declaration_audit": semantic,
        "plants": plants,
        "positive_controls": {
            "current_public_canonical_slice": "PASS",
            "legacy_compatibility_class_remains_separate": "PASS",
        },
        "status": "PASS",
    }
    return receipt


def write_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    mode = 0o664
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        handle.write(text)
        temporary = Path(handle.name)
    os.replace(temporary, path)
    path.chmod(mode)


def check_receipt() -> None:
    expected = build_receipt()
    actual = load_json(RECEIPT_PATH)
    if actual != expected:
        raise FirewallError("IMPORT_FIREWALL_RECEIPT_DRIFT")


def run_plants() -> None:
    policy, registry, _schema = load_inputs()
    graph = build_graph(policy, registry)
    build_public_roots(graph, policy)
    results = [
        run_import_edge_plant(policy),
        run_semantic_audit(graph, registry, policy, plant="DIRECT_VALUE"),
        run_semantic_audit(graph, registry, policy, plant="TRANSITIVE_VALUE"),
        run_semantic_audit(graph, registry, policy, plant="TYPE"),
        run_unparsed_import_plant(),
    ]
    print(json.dumps({"status": "PASS", "plants": results}, sort_keys=True))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("build", "check", "report", "plants"))
    args = parser.parse_args()
    try:
        if args.command == "build":
            receipt = build_receipt()
            write_atomic(RECEIPT_PATH, json.dumps(receipt, indent=2, ensure_ascii=False) + "\n")
            print("OK: import-firewall build")
        elif args.command == "check":
            check_receipt()
            print("OK: import-firewall check")
        elif args.command == "report":
            print(json.dumps(build_receipt(), indent=2, ensure_ascii=False))
        else:
            run_plants()
        return 0
    except (FirewallError, KeyError, TypeError, ValueError, subprocess.SubprocessError) as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
