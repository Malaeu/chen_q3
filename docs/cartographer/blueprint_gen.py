#!/usr/bin/env python3
"""Generate the compact, evidence-bound Route-B internal blueprint.

One model produces the Markdown dashboard and the TeX blueprint. An assembly
row is green only when READY is backed by one exact proven proof-registry row
and by the matching public, safe declaration in the Route-B environment dump.
Validation, open mathematics, and unresolved READY receipts remain non-green.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import re
import sqlite3
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path, PurePosixPath
from typing import Mapping, Sequence

_IMPORT_ROOT = Path(__file__).resolve().parents[2]
if str(_IMPORT_ROOT) not in sys.path:
    sys.path.insert(0, str(_IMPORT_ROOT))
from docs.cartographer.atom_describe import namespace_at  # noqa: E402
from docs.cartographer.lean_env import envdump as lean_envdump  # noqa: E402
from orchestrator import node_registry_v10, spine, startup_runtime  # noqa: E402

ROOT = _IMPORT_ROOT
LEAN_ROOT = ROOT / "q3.lean.aristotle"
KB_PATH = LEAN_ROOT / "aristotle_db" / "knowledge.db"
PDB_PATH = LEAN_ROOT / "aristotle_db" / "aristotle_proofs.db"
ENV_PATH = LEAN_ROOT / ".qmd_cache/routeb_registry_env_index.jsonl"
ENV_DUMP = ROOT / "docs/cartographer/lean_env/envdump.py"
ENV_RECEIPT_PATH = LEAN_ROOT / ".qmd_cache/routeb_env_index_receipt.json"
PREVIEW_PATH = ROOT / "full/blueprint/blueprint.md"
BP_ROOT = LEAN_ROOT / "blueprint"
SRC = BP_ROOT / "src"
MANIFEST_PATH = BP_ROOT / "blueprint_manifest.json"

SCHEMA = "q3_blueprint.v2"
NODE_REGISTRY_PATH = Path("orchestrator/state/NODE_REGISTRY_V10.json")
CHANNEL_RUNTIME_PATH = Path("orchestrator/state/CHANNEL_RUNTIME.json")
EXECUTION_STATE_PATH = Path(
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
)
BIBLIOGRAPHY_INPUTS = (
    Path("docs/routeB_bus/litreview/references.bib"),
    Path("docs/routeB_bus/litreview/REFERENCES.md"),
)
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
ENV_FIELDS = frozenset(
    {
        "name", "kind", "type", "levelParams", "numBinders", "file", "line",
        "doc", "typeConsts", "axioms", "isPrivate", "isUnsafe",
    }
)
TRACKED_INPUTS = (
    "q3.lean.aristotle/aristotle_db/knowledge.db",
    "q3.lean.aristotle/aristotle_db/aristotle_proofs.db",
    "q3.lean.aristotle/Q3/Basic/Defs.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB",
    "orchestrator/state/NODE_REGISTRY_V10.json",
    "orchestrator/state/CHANNEL_RUNTIME.json",
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json",
    "docs/routeB_bus/litreview/references.bib",
    "docs/routeB_bus/litreview/REFERENCES.md",
)
ENV_SOURCE_INPUTS = (
    KB_PATH,
    PDB_PATH,
    LEAN_ROOT / "lean-toolchain",
    LEAN_ROOT / "lakefile.toml",
    LEAN_ROOT / "lake-manifest.json",
    ENV_DUMP,
    ROOT / "docs/cartographer/lean_env/EnvDump.lean",
    ROOT / "orchestrator/state/NODE_REGISTRY_V10.json",
)
INTERFACE_TARGETS = (
    (
        "rh_iff_centeredXi_zeros_real",
        "q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean",
    ),
    (
        "rh_of_canonical_strip_slots",
        "q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean",
    ),
)
CHAIN_TITLES = {
    "PSD_CERTIFICATE_FOR_CCM_CELL": "Pillar G2 — finite-cell validation package",
    "SIMPLE_EVEN_GROUND_TO_REAL_ZEROS": "Pillar G3 — real-zeros bridge",
    "G3_CVS_PORT": "Pillar G3 — de Branges/CvS port",
    "G5_CRITICAL_MOMENT": "Pillar G5 — critical-moment budget",
    "GOAL057_CONTINUUM_NUMERATOR_BRIDGE": "Pillar G6 — continuum numerator and edge",
    "REALZERO_GROUND_DIAGONAL_TO_XI": "Goal 058 — ground diagonal to centered Xi",
}


class BlueprintError(RuntimeError):
    """The current sources cannot support an honest generated blueprint."""


def routeb_source_closure(root: Path = ROOT) -> list[Path]:
    lean_root = root / "q3.lean.aristotle"
    pending = list((lean_root / "Q3/Proofs/RouteB").glob("*.lean"))
    seen: set[Path] = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for module in re.findall(
            r"^import\s+(Q3(?:\.[A-Za-z0-9_']+)*)\s*$",
            path.read_text(encoding="utf-8"),
            re.MULTILINE,
        ):
            dependency = lean_root / (module.replace(".", "/") + ".lean")
            if not dependency.is_file():
                raise BlueprintError(f"local import source missing: {module}")
            pending.append(dependency)
    return sorted(seen)


def routeb_env_source_fingerprint() -> dict[str, str]:
    paths = [*ENV_SOURCE_INPUTS, *routeb_source_closure()]
    return {
        path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in paths
    }


def env_result_modules_sha256(env_path: Path) -> str:
    env, _raw = load_env(env_path)
    modules = tuple(sorted({record["file"] for record in env.values()}))
    return hashlib.sha256(canonical_bytes(modules)).hexdigest()


def env_receipt_matches() -> bool:
    if not ENV_PATH.is_file() or not ENV_RECEIPT_PATH.is_file():
        return False
    try:
        receipt = json.loads(ENV_RECEIPT_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    build_state = lean_envdump.module_content_fingerprint("Q3.Proofs.RouteB")
    dependency_digest = lean_envdump.dependency_content_digest()
    frozen_state = {
        "route_modules": build_state,
        "dependency_digest": dependency_digest,
    }
    try:
        registry = node_registry_v10.load_registry(ROOT, NODE_REGISTRY_PATH)
        bindings = required_env_targets(
            registry, load_assembly(), load_proofs(), ROOT
        )
        env, _raw = load_env(ENV_PATH)
        validate_required_env_coverage(env, bindings)
        result_modules_sha256 = env_result_modules_sha256(ENV_PATH)
    except (node_registry_v10.NodeRegistryError, BlueprintError):
        return False
    targets_sha256 = hashlib.sha256(
        canonical_bytes({"declaration_modules": bindings})
    ).hexdigest()
    return receipt == {
        "schema": "q3_routeb_env_index_receipt.v3",
        "inputs": routeb_env_source_fingerprint(),
        "build_state_sha256": hashlib.sha256(canonical_bytes(frozen_state)).hexdigest(),
        "targets_sha256": targets_sha256,
        "env_index_sha256": hashlib.sha256(ENV_PATH.read_bytes()).hexdigest(),
        "result_modules_sha256": result_modules_sha256,
    }


def prepare_env_index() -> None:
    if env_receipt_matches():
        print("Route-B EnvDump current: source fingerprint unchanged")
        return
    source_inputs = routeb_env_source_fingerprint()
    build = subprocess.run(
        ["lake", "query", "Q3"],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        diagnostics = "\n".join(
            [*build.stdout.splitlines()[-20:], *build.stderr.splitlines()[-20:]]
        )
        raise BlueprintError(
            f"Route-B library build failed: {build.returncode}\n{diagnostics}"
        )
    if routeb_env_source_fingerprint() != source_inputs:
        raise BlueprintError("Route-B sources changed during lake query Q3")
    print("Route-B library build current")
    try:
        registry = node_registry_v10.load_registry(ROOT, NODE_REGISTRY_PATH)
    except node_registry_v10.NodeRegistryError as exc:
        raise BlueprintError(f"NODE_REGISTRY_V10 invalid: {exc}") from exc
    bindings = required_env_targets(
        registry, load_assembly(), load_proofs(), ROOT
    )
    names = tuple(name for name, _path, _module in bindings)
    modules = tuple(sorted({module for _name, _path, module in bindings}))
    targets_sha256 = hashlib.sha256(
        canonical_bytes({"declaration_modules": bindings})
    ).hexdigest()
    build_state = lean_envdump.module_content_fingerprint("Q3.Proofs.RouteB")
    dependency_digest = lean_envdump.dependency_content_digest()
    expected_state = {
        "schema": lean_envdump.EXPECTED_STATE_SCHEMA,
        "prefix": "Q3.Proofs.RouteB",
        "entries": build_state,
        "dependency_digest": dependency_digest,
    }
    environment = os.environ.copy()
    environment.pop("LD_LIBRARY_PATH", None)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", suffix=".json", delete=False
    ) as state_file:
        json.dump(expected_state, state_file, ensure_ascii=False, separators=(",", ":"))
        state_path = Path(state_file.name)
    try:
        command = [
            sys.executable,
            str(ENV_DUMP),
            "--expected-state",
            str(state_path),
            "--out",
            str(ENV_PATH),
        ]
        for module in modules:
            command.extend(("--module", module))
        for name in names:
            command.extend(("--name", name))
        dump = subprocess.run(
            command,
            cwd=ROOT,
            env=environment,
        )
    finally:
        state_path.unlink(missing_ok=True)
    if dump.returncode != 0 or not ENV_PATH.is_file():
        raise BlueprintError(f"Route-B EnvDump failed: {dump.returncode}")
    generated_env, _raw = load_env(ENV_PATH)
    validate_required_env_coverage(generated_env, bindings)
    if routeb_env_source_fingerprint() != source_inputs:
        raise BlueprintError("Route-B sources changed during EnvDump")
    if lean_envdump.module_content_fingerprint("Q3.Proofs.RouteB") != build_state:
        raise BlueprintError("Route-B source/build state changed during EnvDump")
    if lean_envdump.dependency_content_digest() != dependency_digest:
        raise BlueprintError("Route-B dependency closure changed during EnvDump")
    frozen_state = {
        "route_modules": build_state,
        "dependency_digest": dependency_digest,
    }
    receipt = {
        "schema": "q3_routeb_env_index_receipt.v3",
        "inputs": source_inputs,
        "build_state_sha256": hashlib.sha256(canonical_bytes(frozen_state)).hexdigest(),
        "targets_sha256": targets_sha256,
        "env_index_sha256": hashlib.sha256(ENV_PATH.read_bytes()).hexdigest(),
        "result_modules_sha256": env_result_modules_sha256(ENV_PATH),
    }
    ENV_RECEIPT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=ENV_RECEIPT_PATH.parent, delete=False
    ) as handle:
        json.dump(receipt, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
        temporary = Path(handle.name)
    os.replace(temporary, ENV_RECEIPT_PATH)


@dataclasses.dataclass(frozen=True)
class AssemblyRow:
    chain: str
    step: int
    requirement: str
    required_by: str | None
    supplied_by: str | None
    supplier_file: str | None
    supplier_line: int | None
    status: str
    note: str | None
    objects: str | None

    @property
    def identity(self) -> tuple[str, int, str]:
        return self.chain, self.step, self.requirement


@dataclasses.dataclass(frozen=True)
class ProofRow:
    lemma_id: str
    name: str
    status: str
    statement: str | None
    doc_path: str


@dataclasses.dataclass(frozen=True)
class Receipt:
    proof: ProofRow
    full_name: str
    module: str
    axioms: tuple[str, ...]


@dataclasses.dataclass(frozen=True)
class Node:
    row: AssemblyRow
    publication_status: str
    receipt: Receipt | None
    reason: str

    @property
    def label(self) -> str:
        payload = json.dumps(self.row.identity, ensure_ascii=False, separators=(",", ":"))
        suffix = hashlib.sha256(payload.encode()).hexdigest()[:12]
        stem = re.sub(r"[^A-Za-z0-9]+", "-", self.row.chain).strip("-").lower()
        return f"assembly:{stem}-{self.row.step}-{suffix}"


@dataclasses.dataclass(frozen=True)
class Model:
    nodes: tuple[Node, ...]
    interfaces: tuple[Receipt, ...]
    assembly_rows_digest: str
    proof_statement_digest: str
    env_index_digest: str
    generator_digest: str
    git_head: str
    registry: dict[str, object] = dataclasses.field(default_factory=dict)
    declarations: tuple[dict[str, object], ...] = ()
    theorem_axioms: dict[str, tuple[str, ...]] = dataclasses.field(default_factory=dict)
    dependency_appendix: tuple[dict[str, object], ...] = ()
    bibliography_hashes: dict[str, str] = dataclasses.field(default_factory=dict)
    route_phase: dict[str, object] = dataclasses.field(default_factory=dict)

    @property
    def counts(self) -> dict[str, int]:
        result = {
            "assembly_rows": len(self.nodes),
            "green": 0,
            "validation_only": 0,
            "open_math": 0,
            "unresolved_receipt": 0,
            "interface_green": len(self.interfaces),
        }
        keys = {
            "GREEN": "green",
            "VALIDATION_ONLY": "validation_only",
            "OPEN_MATH": "open_math",
            "READY_WITHOUT_EXACT_DECLARATION_RECEIPT": "unresolved_receipt",
        }
        for node in self.nodes:
            result[keys[node.publication_status]] += 1
        return result


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_bytes(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()


def load_json_object(path: Path, expected_schema: str | None = None) -> tuple[dict, bytes]:
    if not path.is_file():
        raise BlueprintError(f"missing JSON input: {path}")
    raw = path.read_bytes()
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise BlueprintError(f"{path}: invalid JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise BlueprintError(f"{path}: root is not an object")
    if expected_schema is not None and value.get("schema") != expected_schema:
        raise BlueprintError(
            f"{path}: schema {value.get('schema')!r} != {expected_schema!r}"
        )
    return value, raw


def confined_repo_file(root: Path, value: str | Path, *, required: bool = True) -> Path:
    """Resolve one lexical repo path without following a symlink component."""
    root = root.resolve()
    candidate = Path(value)
    if candidate.is_absolute():
        raise BlueprintError(f"absolute repository path forbidden: {candidate}")
    relative = candidate
    posix = PurePosixPath(relative.as_posix())
    if posix.is_absolute() or ".." in posix.parts or "\\" in posix.as_posix():
        raise BlueprintError(f"non-canonical repository path: {value}")
    current = root
    for part in posix.parts:
        current = current / part
        if current.is_symlink():
            raise BlueprintError(f"symlink component forbidden: {posix.as_posix()}")
    if required and not current.is_file():
        raise BlueprintError(f"missing repository file: {posix.as_posix()}")
    if current.exists() and not current.is_file():
        raise BlueprintError(f"repository path is not a file: {posix.as_posix()}")
    return current


def git_blob_digest(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode()
    return hashlib.sha1(header + data).hexdigest()


def registry_declaration_names(registry: Mapping[str, object]) -> tuple[str, ...]:
    """Return only declarations that participate in a registered proof edge."""
    names: set[str] = set()
    edges = registry.get("edges")
    if not isinstance(edges, list):
        raise BlueprintError("NODE_REGISTRY_V10 edges must be an array")
    for edge in edges:
        if not isinstance(edge, dict):
            raise BlueprintError("NODE_REGISTRY_V10 edge is not an object")
        for field in ("theorem", "consumer"):
            value = edge.get(field)
            if not isinstance(value, str) or not value:
                raise BlueprintError(f"NODE_REGISTRY_V10 edge {field} is invalid")
            names.add(value)
        path = edge.get("path")
        if not isinstance(path, list) or not all(isinstance(x, str) for x in path):
            raise BlueprintError("NODE_REGISTRY_V10 edge path is invalid")
        names.update(path)
        port = edge.get("hypothesis_port")
        if not isinstance(port, dict) or not isinstance(port.get("direct_reference"), str):
            raise BlueprintError("NODE_REGISTRY_V10 hypothesis_port is invalid")
        names.add(port["direct_reference"])
    return tuple(sorted(names))


def _module_from_source_path(value: object) -> str:
    if not isinstance(value, str):
        raise BlueprintError("registry declaration source path is invalid")
    prefix = "q3.lean.aristotle/"
    if not value.startswith(prefix) or not value.endswith(".lean"):
        raise BlueprintError(f"registry declaration source is not Lean: {value}")
    relative = value[len(prefix):-len(".lean")]
    if not relative or ".." in PurePosixPath(relative).parts:
        raise BlueprintError(f"registry declaration source is non-canonical: {value}")
    return relative.replace("/", ".")


def _source_path_from_module(module: object) -> str:
    if not isinstance(module, str) or not module.startswith("Q3."):
        raise BlueprintError(f"EnvDump declaration module is invalid: {module!r}")
    return "q3.lean.aristotle/" + module.replace(".", "/") + ".lean"


def registry_env_targets(
    registry: Mapping[str, object],
) -> tuple[tuple[str, str, str], ...]:
    """Resolve the exact declarations and minimal source modules for blueprint."""
    sources: dict[str, str] = {}
    nodes = registry.get("nodes")
    edges = registry.get("edges")
    if not isinstance(nodes, list) or not isinstance(edges, list):
        raise BlueprintError("NODE_REGISTRY_V10 nodes/edges are invalid")
    for node in nodes:
        if not isinstance(node, dict) or not isinstance(node.get("source"), dict):
            raise BlueprintError("NODE_REGISTRY_V10 node source is invalid")
        path = node["source"].get("path")
        theorem_ids = node.get("theorem_ids")
        if not isinstance(theorem_ids, list):
            raise BlueprintError("NODE_REGISTRY_V10 theorem_ids are invalid")
        for theorem in theorem_ids:
            if not isinstance(theorem, str):
                raise BlueprintError("NODE_REGISTRY_V10 theorem id is invalid")
            previous = sources.setdefault(theorem, str(path))
            if previous != path:
                raise BlueprintError(f"declaration source ambiguity: {theorem}")
    for edge in edges:
        if not isinstance(edge, dict):
            raise BlueprintError("NODE_REGISTRY_V10 edge is invalid")
        consumer = edge.get("consumer")
        path = edge.get("consumer_path")
        if not isinstance(consumer, str):
            raise BlueprintError("NODE_REGISTRY_V10 consumer is invalid")
        previous = sources.setdefault(consumer, str(path))
        if previous != path:
            raise BlueprintError(f"declaration source ambiguity: {consumer}")
    names = registry_declaration_names(registry)
    missing = sorted(set(names) - sources.keys())
    if missing:
        raise BlueprintError(
            "registry declarations lack exact source modules: " + ", ".join(missing)
        )
    return tuple(
        (name, sources[name], _module_from_source_path(sources[name]))
        for name in names
    )


_LEAN_DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)


def exact_source_declaration_target(
    requested: str,
    source_path: str,
    root: Path = ROOT,
) -> tuple[str, str, str]:
    """Resolve one proof-registry name to its exact source declaration."""
    source = confined_repo_file(root, source_path)
    lines = source.read_text(encoding="utf-8").splitlines()
    matches: list[str] = []
    for line_no, line in enumerate(lines, 1):
        match = _LEAN_DECLARATION.match(line)
        if match is None:
            continue
        declared = match.group(1)
        namespace = namespace_at(lines, line_no)
        full_name = declared if declared.startswith("Q3.") else ".".join(
            part for part in (namespace, declared) if part
        )
        if (
            full_name == requested
            or (not requested.startswith("Q3.") and declared == requested)
        ):
            matches.append(full_name)
    unique = tuple(sorted(set(matches)))
    if len(unique) != 1:
        raise BlueprintError(
            f"{requested}: expected one exact source declaration in "
            f"{source_path}, found {len(unique)}"
        )
    return unique[0], source_path, _module_from_source_path(source_path)


def required_env_targets(
    registry: Mapping[str, object],
    assembly: Sequence[AssemblyRow],
    proofs: Sequence[ProofRow],
    root: Path = ROOT,
) -> tuple[tuple[str, str, str], ...]:
    """Build the complete focused EnvDump denominator used by build_model."""
    targets: dict[str, tuple[str, str]] = {}

    def add(target: tuple[str, str, str]) -> None:
        name, source_path, import_module = target
        binding = (source_path, import_module)
        previous = targets.setdefault(name, binding)
        if previous != binding:
            raise BlueprintError(
                f"required EnvDump target provenance ambiguity: {name}"
            )

    for target in registry_env_targets(registry):
        add(target)
    for name, source_path in INTERFACE_TARGETS:
        add(exact_source_declaration_target(name, source_path, root))

    by_name = proof_index(proofs)
    for row in assembly:
        if row.status != "READY" or not row.supplied_by or not row.supplier_file:
            continue
        name = row.supplied_by.strip()
        source_path = row.supplier_file.strip()
        matches = tuple(by_name.get(name, ()))
        if len(matches) != 1:
            continue
        proof = matches[0]
        if proof.status != "proven" or proof.doc_path != normalize_path(source_path):
            continue
        add(exact_source_declaration_target(name, source_path, root))
    return tuple(
        (name, source_path, import_module)
        for name, (source_path, import_module) in sorted(targets.items())
    )


def validate_required_env_coverage(
    env: Mapping[str, dict],
    targets: Sequence[tuple[str, str, str]],
) -> None:
    missing = sorted(name for name, _path, _module in targets if name not in env)
    if missing:
        sample = ", ".join(missing[:5])
        raise BlueprintError(
            "EnvDump lacks required build-model declarations; run --prepare-env: "
            f"{len(missing)} missing ({sample})"
        )


def project_registry(
    registry_path: Path,
    env: Mapping[str, dict],
    root: Path = ROOT,
) -> tuple[dict[str, object], tuple[dict[str, object], ...], dict[str, tuple[str, ...]], tuple[dict[str, object], ...]]:
    registry_path = confined_repo_file(root, registry_path)
    try:
        registry = node_registry_v10.load_registry(
            root, registry_path.relative_to(root.resolve())
        )
    except node_registry_v10.NodeRegistryError as exc:
        raise BlueprintError(f"NODE_REGISTRY_V10 invalid: {exc}") from exc
    raw = registry_path.read_bytes()
    project = registry.get("project")
    if not isinstance(project, dict):
        raise BlueprintError("NODE_REGISTRY_V10 project is invalid")
    try:
        _project_paths, current_file_count, current_tree_hash = (
            node_registry_v10._project_tree_at_head(root, project["roots"])
        )
    except (KeyError, TypeError, node_registry_v10.NodeRegistryError) as exc:
        raise BlueprintError(f"NODE_REGISTRY_V10 project tree invalid: {exc}") from exc
    if (
        current_file_count != project.get("file_count")
        or current_tree_hash != project.get("project_dependency_tree_hash")
    ):
        raise BlueprintError("registry project dependency tree drift")
    registry_anchors = {
        name: (path, module)
        for name, path, module in registry_env_targets(registry)
    }
    closure_paths = {
        path.relative_to(root.resolve()).as_posix()
        for path in routeb_source_closure(root)
    }
    declarations = []
    theorem_axioms: dict[str, tuple[str, ...]] = {}
    missing = []
    for name in registry_declaration_names(registry):
        record = env.get(name)
        if record is None:
            missing.append(name)
            continue
        registry_anchor_path, _import_module = registry_anchors[name]
        actual_module = record.get("file")
        actual_source_path = _source_path_from_module(actual_module)
        if actual_source_path not in closure_paths:
            raise BlueprintError(
                "EnvDump declaration module is outside current Route-B source closure: "
                f"{name}: {actual_module!r} -> {actual_source_path}"
            )
        confined_repo_file(root, actual_source_path)
        if not isinstance(record.get("axioms"), list):
            raise BlueprintError(f"EnvDump axioms are invalid for {name}")
        axioms = tuple(sorted(str(item) for item in record.get("axioms", [])))
        unexpected_axioms = sorted(set(axioms) - STANDARD_AXIOMS)
        taint_reasons = [f"axiom:{axiom}" for axiom in unexpected_axioms]
        if record.get("isPrivate") is not False:
            taint_reasons.append("private")
        if record.get("isUnsafe") is not False:
            taint_reasons.append("unsafe")
        declarations.append(
            {
                "name": name,
                "kind": record.get("kind"),
                "type": record.get("type"),
                "module": actual_module,
                "registry_anchor_path": registry_anchor_path,
                "actual_declaration_source_path": actual_source_path,
                "source_line": record.get("line"),
                "axioms": list(axioms),
                "taint": {
                    "status": "TAINTED" if taint_reasons else "CLEAN",
                    "reasons": taint_reasons,
                },
            }
        )
        theorem_axioms[name] = axioms
    if missing:
        sample = ", ".join(missing[:5])
        raise BlueprintError(
            "EnvDump lacks registry-relevant declarations; run --prepare-env: "
            f"{len(missing)} missing ({sample})"
        )

    node_projection = []
    verified_commits: dict[str, bool] = {}
    for node in registry["nodes"]:
        source = node["source"]
        source_path = confined_repo_file(root, source["path"])
        commit = source["commit"]
        try:
            if commit not in verified_commits:
                verified_commits[commit] = node_registry_v10._is_ancestor(root, commit)
            is_ancestor = verified_commits[commit]
            recorded_commit_blob = node_registry_v10._blob_at_commit(
                root, commit, source["path"]
            )
        except node_registry_v10.NodeRegistryError as exc:
            raise BlueprintError(f"registry source commit invalid: {exc}") from exc
        if not is_ancestor:
            raise BlueprintError(f"registry source commit is not an ancestor: {commit}")
        if recorded_commit_blob != source.get("blob"):
            raise BlueprintError(
                f"registry source commit/blob drift: {commit}:{source['path']}"
            )
        current_blob = git_blob_digest(source_path.read_bytes())
        if current_blob != source.get("blob"):
            raise BlueprintError(f"registry source blob drift: {source['path']}")
        node_projection.append(
            {
                "node_id": node["node_id"],
                "node_class": node["node_class"],
                "lifecycle": node["lifecycle"],
                "theorem_ids": node["theorem_ids"],
                "terminal_consumer": node["terminal_consumer"],
                "source": {
                    **source,
                    "recorded_commit_blob": recorded_commit_blob,
                    "recorded_commit_is_ancestor": is_ancestor,
                    "current_git_blob": current_blob,
                    "recorded_blob_matches_current": current_blob == source.get("blob"),
                },
                "semantic_review_hash": node["semantic_review_hash"],
                "validation_hash": node["validation_hash"],
                "semantic_review_inputs": node["semantic_review_inputs"],
                "validation_inputs": node["validation_inputs"],
                "review": node["review"],
            }
        )
    edge_projection = []
    appendix = []
    for edge in registry["edges"]:
        consumer_path = confined_repo_file(root, edge["consumer_path"])
        current_blob = git_blob_digest(consumer_path.read_bytes())
        if current_blob != edge.get("consumer_blob"):
            raise BlueprintError(f"registry consumer blob drift: {edge['consumer_path']}")
        projected = {
            **edge,
            "current_consumer_blob": current_blob,
            "recorded_consumer_blob_matches_current": current_blob == edge.get("consumer_blob"),
        }
        edge_projection.append(projected)
        appendix.append(
            {
                "edge_id": edge["edge_id"],
                "supplier": edge["theorem"],
                "consumer": edge["consumer"],
                "relation": edge["relation"],
                "path": edge["path"],
                "hypothesis_port": edge["hypothesis_port"],
            }
        )
    projection = {
        "schema": registry["schema"],
        "algorithm_version": registry.get("algorithm_version"),
        "mode": registry.get("mode"),
        "registry_hash": registry.get("registry_hash"),
        "registry_file_sha256": digest(raw),
        "project_dependency_tree_hash": registry.get("project", {}).get(
            "project_dependency_tree_hash"
        ),
        "review_policy": registry.get("review_policy"),
        "nodes": node_projection,
        "edges": edge_projection,
    }
    return projection, tuple(declarations), theorem_axioms, tuple(appendix)


def bibliography_digests(paths: Sequence[Path], root: Path = ROOT) -> dict[str, str]:
    result = {}
    for value in paths:
        path = confined_repo_file(root, value)
        result[path.relative_to(root.resolve()).as_posix()] = digest(path.read_bytes())
    return result


def load_route_phase(
    execution_path: Path,
    channel_path: Path,
    root: Path = ROOT,
) -> dict[str, object]:
    execution_path = confined_repo_file(root, execution_path)
    channel_path = confined_repo_file(root, channel_path)
    try:
        execution = startup_runtime._load_unique_json(execution_path)
        channel = startup_runtime._load_unique_json(channel_path)
        spine.validate_runtime(channel)
    except (startup_runtime.StartupRuntimeError, ValueError, KeyError, TypeError) as exc:
        raise BlueprintError(f"route/phase runtime invalid: {exc}") from exc
    execution_raw = execution_path.read_bytes()
    channel_raw = channel_path.read_bytes()
    if execution.get("schema_version") != "route_b_execution_state.v3_live_bus":
        raise BlueprintError("execution state schema invalid")
    current = execution.get("current")
    phase = channel.get("active_proshka_phase")
    if not isinstance(current, dict) or not isinstance(phase, dict):
        raise BlueprintError("route/phase current state is missing")
    architecture = execution.get("architecture")
    if (
        not isinstance(architecture, dict)
        or architecture.get("route_b_rh_status") != "NOT_RH"
        or current.get("route_promotion") is not False
        or current.get("rh_claimed") is not False
    ):
        raise BlueprintError("route/phase honesty state drift")
    try:
        phase_key = spine.validate_phase_key(phase.get("phase_key"))
    except (ValueError, KeyError, TypeError) as exc:
        raise BlueprintError(f"phase key invalid: {exc}") from exc
    if execution.get("route_id") != phase_key.get("route_id"):
        raise BlueprintError("execution route_id does not match active phase key")
    goal_rel = current.get("selected_bus_goal_path")
    if not isinstance(goal_rel, str):
        raise BlueprintError("execution state has no selected physical goal")
    goal_path = confined_repo_file(root, goal_rel)
    goal_relative = goal_path.relative_to(root.resolve())
    if goal_relative.parent != Path("docs/routeB_bus"):
        raise BlueprintError("selected physical goal is outside canonical docs/routeB_bus")
    try:
        goal_header = startup_runtime._goal_header(goal_path)
        goal_id = startup_runtime._goal_id(goal_path, goal_header)
        goal_node, _source_pin, _theorem_pin, goal_consumer = (
            startup_runtime._pins(goal_header)
        )
    except startup_runtime.StartupRuntimeError as exc:
        raise BlueprintError(f"selected physical goal invalid: {exc}") from exc
    if current.get("selected_bus_goal_nnn") != goal_id[:3]:
        raise BlueprintError("execution state selected goal identity drift")
    if goal_node is None:
        raise BlueprintError("selected physical goal has no exact node")
    terminal_consumer = phase_key.get("terminal_consumer_id")
    if not isinstance(terminal_consumer, str) or not terminal_consumer:
        raise BlueprintError("active phase has no terminal consumer")
    if goal_consumer is not None and goal_consumer != terminal_consumer:
        raise BlueprintError("selected physical goal terminal consumer drift")
    goal_status = goal_header.get("STATUS")
    if goal_status not in startup_runtime.KNOWN_GOAL_STATUSES:
        raise BlueprintError(f"selected physical goal status invalid: {goal_status}")

    stem = goal_path.name.removesuffix(".goal.md")
    answer_path = confined_repo_file(
        root, goal_relative.with_name(stem + ".answer.md"), required=False
    )
    answer_payload = None
    if answer_path.is_file():
        try:
            startup_runtime._validate_modern_answer(goal_path, goal_header, answer_path)
        except startup_runtime.StartupRuntimeError as exc:
            raise BlueprintError(f"matching answer invalid: {exc}") from exc
        answer_payload = {
            "path": answer_path.relative_to(root.resolve()).as_posix(),
            "sha256": digest(answer_path.read_bytes()),
        }
    elif goal_status in startup_runtime.TERMINAL_GOAL_STATUSES:
        raise BlueprintError("terminal selected goal has no matching answer")

    goal_receipt_path = confined_repo_file(
        root, goal_relative.with_name(stem + ".goal-close.json"), required=False
    )
    phase_receipt_path = confined_repo_file(
        root, goal_relative.with_name(stem + ".phase-close.json"), required=False
    )
    receipts: dict[str, object] = {}
    goal_receipt = None
    if goal_receipt_path.is_file():
        if not answer_path.is_file():
            raise BlueprintError("goal-close receipt has no matching answer")
        try:
            goal_receipt = startup_runtime.validate_goal_close_receipt(
                goal_path, answer_path, goal_receipt_path
            )
        except startup_runtime.StartupRuntimeError as exc:
            raise BlueprintError(f"goal-close receipt invalid: {exc}") from exc
        receipts["goal_close"] = {
            "path": goal_receipt_path.relative_to(root.resolve()).as_posix(),
            "sha256": digest(goal_receipt_path.read_bytes()),
            "schema": goal_receipt["schema"],
        }
    elif goal_status in startup_runtime.TERMINAL_GOAL_STATUSES:
        raise BlueprintError("terminal selected goal has no goal-close receipt")
    if phase_receipt_path.is_file():
        if goal_receipt is None or goal_receipt.get("phase_close_required") is not True:
            raise BlueprintError("phase-close receipt is not applicable")
        try:
            phase_receipt = startup_runtime.validate_phase_close_receipt(
                goal_path, goal_receipt_path, phase_receipt_path
            )
        except startup_runtime.StartupRuntimeError as exc:
            raise BlueprintError(f"phase-close receipt invalid: {exc}") from exc
        receipts["phase_close"] = {
            "path": phase_receipt_path.relative_to(root.resolve()).as_posix(),
            "sha256": digest(phase_receipt_path.read_bytes()),
            "schema": phase_receipt["schema"],
        }
    return {
        "execution_schema": execution.get("schema_version"),
        "execution_state_sha256": digest(execution_raw),
        "route_id": execution.get("route_id"),
        "operational_status": execution.get("operational_status"),
        "selected_goal": goal_rel,
        "selected_goal_id": goal_id,
        "selected_goal_node": goal_node,
        "terminal_consumer": terminal_consumer,
        "selected_goal_sha256": digest(goal_path.read_bytes()),
        "selected_goal_status": goal_status,
        "matching_answer": answer_payload,
        "stage_id": current.get("stage_id"),
        "contract_obligation": current.get("contract_obligation"),
        "terminal_route_state": architecture,
        "channel_runtime_sha256": digest(channel_raw),
        "phase_status": phase.get("status"),
        "phase_id": phase.get("phase_id"),
        "phase_key": phase_key,
        "honesty_state": phase_key.get("honesty_state"),
        "px_rh_claim_state": channel.get("px_rh_claim_state"),
        "close_receipts": receipts,
        "close_state": (
            "PHASE_CLOSED" if "phase_close" in receipts else
            "PHASE_CLOSE_PENDING" if goal_receipt and goal_receipt.get("phase_close_required") else
            "GOAL_CLOSED" if "goal_close" in receipts else
            "OPEN"
        ),
    }


def connect_ro(path: Path) -> sqlite3.Connection:
    if not path.is_file():
        raise BlueprintError(f"missing database: {path}")
    conn = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    return conn


def load_assembly(path: Path = KB_PATH) -> tuple[AssemblyRow, ...]:
    with connect_ro(path) as conn:
        rows = conn.execute(
            "SELECT chain,step,requirement,required_by,supplied_by,supplier_file,"
            "supplier_line,status,note,objects FROM assembly "
            "ORDER BY chain,step,requirement"
        ).fetchall()
    if not rows:
        raise BlueprintError("assembly is empty")
    result = tuple(AssemblyRow(**dict(row)) for row in rows)
    if len({row.identity for row in result}) != len(result):
        raise BlueprintError("duplicate assembly identity")
    return result


def load_proofs(path: Path = PDB_PATH) -> tuple[ProofRow, ...]:
    with connect_ro(path) as conn:
        rows = conn.execute(
            "SELECT l.lemma_id,l.name,l.status,l.statement,d.path AS doc_path "
            "FROM lemmas l JOIN docs d ON d.doc_id=l.doc_id ORDER BY l.lemma_id"
        ).fetchall()
    if not rows:
        raise BlueprintError("proof registry is empty")
    return tuple(ProofRow(**dict(row)) for row in rows)


def load_env(path: Path = ENV_PATH) -> tuple[dict[str, dict], bytes]:
    if not path.is_file():
        raise BlueprintError(
            f"missing {path}; run env -u LD_LIBRARY_PATH python3 "
            "docs/cartographer/lean_env/envdump.py"
        )
    raw = path.read_bytes()
    records: dict[str, dict] = {}
    for line_no, line in enumerate(raw.decode().splitlines(), 1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            raise BlueprintError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
        if not isinstance(record, dict):
            raise BlueprintError(f"{path}:{line_no}: record is not an object")
        missing = ENV_FIELDS - record.keys()
        if missing:
            raise BlueprintError(
                f"{path}:{line_no}: missing fields {', '.join(sorted(missing))}"
            )
        name = record.get("name")
        if not isinstance(name, str) or not name:
            raise BlueprintError(f"{path}:{line_no}: empty declaration name")
        if name in records:
            raise BlueprintError(f"{path}:{line_no}: duplicate declaration {name}")
        if not isinstance(record.get("axioms"), list):
            raise BlueprintError(f"{path}:{line_no}: axioms is not a list")
        records[name] = record
    if not records:
        raise BlueprintError(f"{path}: no declarations")
    return records, raw


def normalize_path(path: str) -> str:
    prefix = "q3.lean.aristotle/"
    return path[len(prefix):] if path.startswith(prefix) else path


def module_for(path: str) -> str:
    normalized = normalize_path(path)
    if not normalized.startswith("Q3/Proofs/RouteB/") or not normalized.endswith(".lean"):
        raise BlueprintError(f"not a Route-B Lean source: {path}")
    return normalized.removesuffix(".lean").replace("/", ".")


def resolve_receipt(
    name: str,
    expected_file: str,
    proofs_by_name: Mapping[str, Sequence[ProofRow]],
    env: Mapping[str, dict],
    env_mtime: float,
    root: Path = ROOT,
) -> Receipt | None:
    """Return None only for true absence; contradictory receipts fail closed."""
    matches = tuple(proofs_by_name.get(name, ()))
    if not matches:
        return None
    if len(matches) != 1:
        raise BlueprintError(f"duplicate proof-registry name: {name}")
    proof = matches[0]
    if proof.status != "proven":
        raise BlueprintError(f"{name}: status {proof.status!r}, not proven")
    if proof.statement is None or not proof.statement.strip():
        raise BlueprintError(f"{name}: empty statement")
    if "\\end{verbatim}" in proof.statement or "\\end{Verbatim}" in proof.statement:
        raise BlueprintError(f"{name}: statement terminates verbatim")
    expected = normalize_path(expected_file)
    if proof.doc_path != expected:
        raise BlueprintError(
            f"{name}: proof path {proof.doc_path!r} != assembly path {expected!r}"
        )
    module = module_for(proof.doc_path)
    candidates = [
        rec for full, rec in env.items()
        if rec.get("file") == module and (full == name or full.endswith(f".{name}"))
    ]
    if len(candidates) != 1:
        raise BlueprintError(
            f"{name}: expected one declaration in {module}, found {len(candidates)}"
        )
    record = candidates[0]
    full_name = str(record["name"])
    source = root / "q3.lean.aristotle" / proof.doc_path
    if not source.is_file():
        raise BlueprintError(f"{name}: source missing: {source}")
    if source.stat().st_mtime > env_mtime:
        raise BlueprintError(f"{name}: source is newer than env_index")
    if record.get("isPrivate") is not False:
        raise BlueprintError(f"{full_name}: private declaration")
    if record.get("isUnsafe") is not False:
        raise BlueprintError(f"{full_name}: unsafe declaration")
    axioms = tuple(sorted(str(item) for item in record["axioms"]))
    unexpected = set(axioms) - STANDARD_AXIOMS
    if unexpected:
        raise BlueprintError(f"{full_name}: nonstandard axioms {sorted(unexpected)}")
    return Receipt(proof, full_name, module, axioms)


def proof_index(proofs: Sequence[ProofRow]) -> dict[str, list[ProofRow]]:
    result: dict[str, list[ProofRow]] = defaultdict(list)
    for proof in proofs:
        result[proof.name].append(proof)
    return result


def classify(
    assembly: Sequence[AssemblyRow],
    proofs: Sequence[ProofRow],
    env: Mapping[str, dict],
    env_mtime: float,
    root: Path = ROOT,
) -> tuple[Node, ...]:
    by_name = proof_index(proofs)
    nodes = []
    for row in assembly:
        if row.status == "VALIDATION":
            nodes.append(Node(row, "VALIDATION_ONLY", None, "not a Lean proof authority"))
        elif row.status != "READY":
            nodes.append(Node(row, "OPEN_MATH", None, f"assembly status {row.status}"))
        elif not row.supplied_by or not row.supplier_file:
            nodes.append(
                Node(
                    row, "READY_WITHOUT_EXACT_DECLARATION_RECEIPT", None,
                    "READY has no exact supplier name and source path",
                )
            )
        else:
            receipt = resolve_receipt(
                row.supplied_by.strip(), row.supplier_file.strip(), by_name,
                env, env_mtime, root,
            )
            if receipt is None:
                nodes.append(
                    Node(
                        row, "READY_WITHOUT_EXACT_DECLARATION_RECEIPT", None,
                        "no unique exact name in aristotle_proofs.db",
                    )
                )
            else:
                nodes.append(Node(row, "GREEN", receipt, "exact proven receipt"))
    return tuple(nodes)


def load_interfaces(
    proofs: Sequence[ProofRow],
    env: Mapping[str, dict],
    env_mtime: float,
    root: Path = ROOT,
) -> tuple[Receipt, ...]:
    by_name = proof_index(proofs)
    result = []
    for name, path in INTERFACE_TARGETS:
        receipt = resolve_receipt(name, path, by_name, env, env_mtime, root)
        if receipt is None:
            raise BlueprintError(f"missing interface receipt: {name}")
        result.append(receipt)
    return tuple(result)


def tracked_input_head(
    root: Path = ROOT, extra_inputs: Sequence[str] = ()
) -> str:
    proc = subprocess.run(
        ["git", "log", "-1", "--format=%H", "--", *TRACKED_INPUTS, *extra_inputs],
        cwd=root, capture_output=True, text=True, check=False,
    )
    head = proc.stdout.strip()
    if proc.returncode or not re.fullmatch(r"[0-9a-f]{40}", head):
        raise BlueprintError(f"cannot resolve input commit: {proc.stderr.strip()}")
    return head


def build_model(
    kb: Path = KB_PATH,
    pdb: Path = PDB_PATH,
    env_path: Path = ENV_PATH,
    root: Path = ROOT,
    generator: Path | None = None,
    registry_path: Path | None = None,
    execution_path: Path | None = None,
    channel_path: Path | None = None,
    bibliography_paths: Sequence[Path] | None = None,
) -> Model:
    if env_path == ENV_PATH and root == ROOT and not env_receipt_matches():
        raise BlueprintError("Route-B EnvDump receipt is stale; run --prepare-env")
    assembly = load_assembly(kb)
    proofs = load_proofs(pdb)
    env, env_raw = load_env(env_path)
    env_mtime = env_path.stat().st_mtime if env_path.is_file() else 0.0
    generator = generator or Path(__file__).resolve()
    registry_path = registry_path or NODE_REGISTRY_PATH
    execution_path = execution_path or EXECUTION_STATE_PATH
    channel_path = channel_path or CHANNEL_RUNTIME_PATH
    bibliography_paths = bibliography_paths or BIBLIOGRAPHY_INPUTS
    registry_file = confined_repo_file(root, registry_path)
    try:
        registry_input = node_registry_v10.load_registry(
            root, registry_file.relative_to(root.resolve())
        )
    except node_registry_v10.NodeRegistryError as exc:
        raise BlueprintError(f"NODE_REGISTRY_V10 invalid: {exc}") from exc
    env_targets = required_env_targets(registry_input, assembly, proofs, root)
    validate_required_env_coverage(env, env_targets)
    registry, declarations, theorem_axioms, appendix = project_registry(
        registry_path, env, root
    )
    route_phase = load_route_phase(execution_path, channel_path, root)
    dynamic_inputs = [str(route_phase["selected_goal"])]
    answer = route_phase.get("matching_answer")
    if isinstance(answer, dict) and isinstance(answer.get("path"), str):
        dynamic_inputs.append(answer["path"])
    close_receipts = route_phase.get("close_receipts")
    if isinstance(close_receipts, dict):
        dynamic_inputs.extend(
            value["path"] for value in close_receipts.values()
            if isinstance(value, dict) and isinstance(value.get("path"), str)
        )
    return Model(
        classify(assembly, proofs, env, env_mtime, root),
        load_interfaces(proofs, env, env_mtime, root),
        digest(canonical_bytes([dataclasses.asdict(row) for row in assembly])),
        digest(canonical_bytes([dataclasses.asdict(row) for row in proofs])),
        digest(env_raw),
        digest(generator.read_bytes()),
        tracked_input_head(root, dynamic_inputs),
        registry,
        declarations,
        theorem_axioms,
        appendix,
        bibliography_digests(bibliography_paths, root),
        route_phase,
    )


def tex_escape(text: str) -> str:
    table = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
        "#": r"\#", "_": r"\_\allowbreak{}", "{": r"\{", "}": r"\}",
        "/": r"/\allowbreak{}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    }
    return "".join(table.get(char, char) for char in text)


def verbatim(statement: str) -> str:
    if "\\end{verbatim}" in statement or "\\end{Verbatim}" in statement:
        raise BlueprintError("statement terminates verbatim")
    newline = "" if statement.endswith("\n") else "\n"
    return (
        "\\mbox{}\\par\\smallskip\n"
        "\\begin{Verbatim}[breaklines=true,breakanywhere=true,fontsize=\\small]\n"
        + statement + newline + "\\end{Verbatim}\n"
        "\\smallskip\n"
    )


def render_node(node: Node) -> str:
    row = node.row
    environment = "validation" if node.publication_status == "VALIDATION_ONLY" else "lemma"
    lines = [
        f"\\begin{{{environment}}}[{tex_escape(row.chain)} / step {row.step}]"
        f"\\label{{{node.label}}}"
    ]
    if node.receipt:
        lines += [f"\\lean{{{node.receipt.full_name}}}", "\\leanok"]
    else:
        lines.append("\\notready")
    lines += [
        f"\\textbf{{Publication state:}} "
        f"\\texttt{{{tex_escape(node.publication_status)}}}.\\par",
        tex_escape(row.requirement) + "\\par",
    ]
    if row.supplied_by:
        lines.append(
            "\\textbf{Assembly supplier field:} "
            f"\\texttt{{{tex_escape(row.supplied_by)}}}.\\par"
        )
    if node.receipt:
        lines.append(verbatim(node.receipt.proof.statement or "").rstrip("\n"))
    else:
        lines.append(f"\\textbf{{Open receipt:}} {tex_escape(node.reason)}.\\par")
        if row.note:
            lines.append(f"\\textbf{{Recorded note:}} {tex_escape(row.note)}\\par")
    lines.append(f"\\end{{{environment}}}")
    if node.receipt:
        lines += [
            "\\begin{proof}", "\\leanok",
            "The proof term is checked in the declaration named above. "
            "This receipt does not strengthen its statement.",
            "\\end{proof}",
        ]
    return "\n".join(lines)


def render_content(model: Model) -> str:
    bridge, roof = model.interfaces
    lines = [
        "% Generated by docs/cartographer/blueprint_gen.py. DO NOT EDIT.",
        "% PX_RH_CLAIM: NOT_MADE",
        r"\section{Definitions and faithfulness interface}",
        r"\textbf{Route status: CHALLENGER / NOT\_RH.}\par",
        r"\textbf{PX\_RH\_CLAIM: NOT\_MADE.}\par",
        (
            r"The project proposition \texttt{Q3.RH} is the classical open-strip "
            r"Riemann Hypothesis over Mathlib's \texttt{riemannZeta}: every zero "
            r"with real part strictly between zero and one has real part one half."
        ),
        r"\begin{definition}[Project RH proposition]\label{def:q3-rh}",
        r"\lean{Q3.RH}",
        r"\texttt{Q3.RH} is defined in \texttt{Q3/Basic/Defs.lean}. "
        r"This records definition identity and does not assert a proof.",
        r"\end{definition}",
        r"\begin{theorem}[Centered-Xi faithfulness bridge]\label{thm:rh-centered-xi}",
        f"\\lean{{{bridge.full_name}}}", r"\leanok",
        verbatim(bridge.proof.statement or "").rstrip("\n"),
        r"\end{theorem}",
        r"\begin{proof}\leanok The proof term is checked by Lean.\end{proof}",
        "This equivalence of formulations is not a proof of either side.",
        r"\section{Conditional roof}",
        r"\begin{theorem}[Canonical strip-slot assembly]\label{thm:conditional-roof}",
        f"\\lean{{{roof.full_name}}}", r"\leanok",
        verbatim(roof.proof.statement or "").rstrip("\n"),
        r"\end{theorem}",
        r"\begin{proof}\leanok The proof term is checked by Lean.\end{proof}",
        "The conclusion is conditional on every named hypothesis in the statement.",
    ]
    grouped: dict[str, list[Node]] = defaultdict(list)
    for node in model.nodes:
        grouped[node.row.chain].append(node)
    for chain in sorted(grouped):
        lines += ["", f"\\section{{{tex_escape(CHAIN_TITLES.get(chain, chain))}}}"]
        for node in grouped[chain]:
            lines += ["", render_node(node)]
    lines += [
        "", r"\section{Registered semantic edges}",
        (
            r"This compact appendix lists only declarations on exact registered "
            r"supplier-to-consumer paths; unrelated helper declarations are omitted."
        ),
    ]
    for edge in model.dependency_appendix:
        lines += [
            r"\begin{lemma}[Registered edge " + tex_escape(str(edge["edge_id"])) + "]",
            r"\textbf{Supplier:} \texttt{" + tex_escape(str(edge["supplier"])) + r"}.\par",
            r"\textbf{Consumer:} \texttt{" + tex_escape(str(edge["consumer"])) + r"}.\par",
            r"\textbf{Relation:} \texttt{" + tex_escape(str(edge["relation"])) + r"}.\par",
            r"\end{lemma}",
        ]
    lines += [
        "", r"\section{Bibliography}", r"\nocite{*}", r"\bibliographystyle{plain}",
        r"\bibliography{references}", "",
    ]
    return "\n".join(lines)


def render_preview(model: Model) -> str:
    counts = model.counts
    lines = [
        "# Route B publication blueprint", "",
        "Generated by docs/cartographer/blueprint_gen.py; do not edit by hand.", "",
        "- Route status: CHALLENGER / NOT_RH",
        "- PX_RH_CLAIM: NOT_MADE",
        f"- Assembly rows: {counts['assembly_rows']}",
        f"- Publication-green exact receipts: {counts['green']}",
        f"- Validation-only rows: {counts['validation_only']}",
        f"- Open mathematical rows: {counts['open_math']}",
        f"- READY rows without exact declaration receipt: {counts['unresolved_receipt']}",
        "", "## Definitions and faithfulness interface", "",
        "Q3.RH is the classical open-strip RH proposition over Mathlib riemannZeta.",
        "Q3.RouteB.rh_iff_centeredXi_zeros_real is an equivalence, not a proof of RH.",
        "", "## Conditional roof", "",
        "Q3.RouteB.rh_of_canonical_strip_slots is kernel-checked and conditional.",
        "It does not close any open assembly row.",
        "", "## Registered semantic surface", "",
        f"- Registry nodes: {len(model.registry.get('nodes', []))}",
        f"- Exact edges: {len(model.registry.get('edges', []))}",
        f"- Proof-relevant EnvDump declarations: {len(model.declarations)}",
    ]
    grouped: dict[str, list[Node]] = defaultdict(list)
    for node in model.nodes:
        grouped[node.row.chain].append(node)
    for chain in sorted(grouped):
        lines += ["", f"## {CHAIN_TITLES.get(chain, chain)}", ""]
        for node in grouped[chain]:
            row = node.row
            lines += [
                f"### Step {row.step}: {node.publication_status} — {row.requirement}", ""
            ]
            if node.receipt:
                lines += [
                    f"- Lean: {node.receipt.full_name}",
                    f"- Source module: {node.receipt.module}",
                    "- Axioms: " + (", ".join(node.receipt.axioms) or "none"),
                    "", "~~~lean", node.receipt.proof.statement or "", "~~~",
                ]
            else:
                lines.append(f"- Non-green reason: {node.reason}")
                if row.supplied_by:
                    lines.append(f"- Assembly supplier field: {row.supplied_by}")
                if row.note:
                    lines.append(f"- Recorded note: {row.note}")
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_manifest(model: Model) -> str:
    value = {
        "schema": SCHEMA,
        "git_head": model.git_head,
        "git_head_semantics": "latest commit touching tracked blueprint data inputs",
        "assembly_rows_digest": model.assembly_rows_digest,
        "proof_statement_digest": model.proof_statement_digest,
        "env_index_digest": model.env_index_digest,
        "generator_digest": model.generator_digest,
        "bibliography_path": "docs/routeB_bus/litreview/references.bib",
        "counts": model.counts,
        "route_status": "CHALLENGER",
        "rh_status": "NOT_RH",
        "PX_RH_CLAIM": "NOT_MADE",
        "node_registry": model.registry,
        "proof_relevant_declarations": list(model.declarations),
        "theorem_axiom_map": {
            name: list(axioms) for name, axioms in sorted(model.theorem_axioms.items())
        },
        "dependency_appendix": list(model.dependency_appendix),
        "bibliography_hashes": model.bibliography_hashes,
        "route_phase": model.route_phase,
    }
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"


def outputs(model: Model) -> dict[Path, bytes]:
    files = {
        PREVIEW_PATH: render_preview(model),
        MANIFEST_PATH: render_manifest(model),
        SRC / "content.tex": render_content(model),
        SRC / "print.tex": r"""% Generated blueprint print driver.
\documentclass[11pt,a4paper]{article}
\usepackage[a4paper,margin=30mm]{geometry}
\usepackage{expl3}
\usepackage{amssymb,amsthm,mathtools}
\usepackage{fvextra}
\usepackage[unicode,colorlinks=true,linkcolor=blue,urlcolor=magenta,citecolor=blue]{hyperref}
\usepackage{fontspec}
\setmainfont{FreeSerif}
\setmonofont{FreeMono}
\input{macros/common}
\input{macros/print}
\title{Operator Methods for the Riemann Hypothesis: Route B Blueprint}
\author{}\date{}
\begin{document}\maketitle
\setlength{\emergencystretch}{3em}\sloppy
\input{content}\end{document}
""",
        SRC / "web.tex": r"""% Generated blueprint web driver.
\documentclass{article}
\usepackage{amssymb,amsthm,amsmath}
\usepackage{fvextra}
\usepackage{hyperref}
\usepackage[dep_graph]{blueprint}
\input{macros/common}
\input{macros/web}
\title{Operator Methods for the Riemann Hypothesis: Route B Blueprint}
\author{}
\begin{document}\maketitle\input{content}\end{document}
""",
        SRC / "blueprint.sty": "\\DeclareOption*{}\n\\ProcessOptions\n"
        "\\newcommand{\\graphcolor}[3]{}\n",
        SRC / "plastex.cfg": """[general]
renderer=HTML5
copy-theme-extras=yes
plugins=plastexdepgraph leanblueprint

[document]
toc-depth=2
toc-non-files=True

[files]
directory=../web/
split-level=2

[html5]
localtoc-level=1
extra-css=extra_styles.css
mathjax-dollars=False
""",
        SRC / "latexmkrc": "use Cwd qw(abs_path);\n"
        "my $q3_bib_dir = abs_path('../../../docs/routeB_bus/litreview');\n"
        "$ENV{'BIBINPUTS'} = $q3_bib_dir . ':' . ($ENV{'BIBINPUTS'} // '');\n"
        "$pdf_mode = 1;\n"
        "$pdflatex = 'xelatex -interaction=nonstopmode -halt-on-error -synctex=1 %O %S';\n"
        "@default_files = ('print.tex');\n",
        SRC / "macros/common.tex": r"""\theoremstyle{definition}
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{validation}[theorem]{Validation record}
""",
        SRC / "macros/print.tex": r"""\newcommand{\lean}[1]{}
\newcommand{\discussion}[1]{}
\newcommand{\leanok}{}
\newcommand{\mathlibok}{}
\newcommand{\notready}{}
\ExplSyntaxOn
\NewDocumentCommand{\uses}{m}
 {\clist_map_inline:nn{#1}{\vphantom{\ref{##1}}}\ignorespaces}
\NewDocumentCommand{\proves}{m}
 {\clist_map_inline:nn{#1}{\vphantom{\ref{##1}}}\ignorespaces}
\ExplSyntaxOff
""",
        SRC / "macros/web.tex": "% Web-only macros.\n",
        SRC / "extra_styles.css": (
            "/* Validation records are evidence, not proof nodes. */\n"
            ".validation { border-left: .35rem solid #d97706; padding-left: .75rem; }\n"
        ),
    }
    return {path: text.encode() for path, text in files.items()}


def validate(model: Model, rendered: Mapping[Path, bytes]) -> None:
    counts = model.counts
    partition = (
        counts["green"] + counts["validation_only"] + counts["open_math"]
        + counts["unresolved_receipt"]
    )
    if partition != counts["assembly_rows"]:
        raise BlueprintError("publication categories do not partition assembly")
    for node in model.nodes:
        if (node.publication_status == "GREEN") != (node.receipt is not None):
            raise BlueprintError(f"receipt/status mismatch: {node.row.identity}")
    for path in (PREVIEW_PATH, SRC / "content.tex"):
        if b"PX_RH_CLAIM: NOT_MADE" not in rendered[path]:
            raise BlueprintError(f"honesty token missing from {path}")
    manifest = json.loads(rendered[MANIFEST_PATH])
    if manifest.get("schema") != "q3_blueprint.v2":
        raise BlueprintError("blueprint v2 schema missing from manifest")
    if manifest.get("PX_RH_CLAIM") != "NOT_MADE":
        raise BlueprintError("honesty token missing from manifest")
    if model.route_phase and model.route_phase.get("honesty_state") != "CHALLENGER_NOT_RH":
        raise BlueprintError("route phase honesty state is not CHALLENGER_NOT_RH")
    if model.registry:
        if not model.registry.get("registry_hash"):
            raise BlueprintError("NODE_REGISTRY_V10 registry_hash missing")
        if len(model.declarations) != len(model.theorem_axioms):
            raise BlueprintError("theorem-to-axiom map does not cover relevant declarations")
        for declaration in model.declarations:
            if not declaration.get("type"):
                raise BlueprintError(
                    f"missing elaborated type: {declaration.get('name')}"
                )


def publish(rendered: Mapping[Path, bytes]) -> None:
    staged = []
    for path, data in rendered.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            mode="wb", dir=path.parent, prefix=f".{path.name}.",
            suffix=".tmp", delete=False,
        ) as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
            staged.append((Path(handle.name), path))
    staged.sort(key=lambda pair: pair[1] == MANIFEST_PATH)
    for temporary, destination in staged:
        os.replace(temporary, destination)


def stale_paths(rendered: Mapping[Path, bytes]) -> list[Path]:
    return [
        path for path, expected in rendered.items()
        if not path.is_file() or path.read_bytes() != expected
    ]


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="read-only stale check")
    parser.add_argument(
        "--prepare-env",
        action="store_true",
        help="compile Route B and refresh EnvDump if its byte fingerprint changed",
    )
    args = parser.parse_args(argv)
    try:
        if args.check and args.prepare_env:
            raise BlueprintError("--check and --prepare-env are mutually exclusive")
        if args.prepare_env:
            prepare_env_index()
        model = build_model()
        rendered = outputs(model)
        validate(model, rendered)
        if args.check:
            stale = stale_paths(rendered)
            for path in stale:
                print(f"STALE: {path.relative_to(ROOT)}", file=sys.stderr)
            if stale:
                return 1
            print("blueprint check: OK")
            return 0
        publish(rendered)
        counts = model.counts
        print(
            f"blueprint generated: rows={counts['assembly_rows']} "
            f"green={counts['green']} validation={counts['validation_only']} "
            f"open={counts['open_math']} "
            f"unresolved_receipt={counts['unresolved_receipt']}"
        )
        return 0
    except (BlueprintError, OSError, sqlite3.Error, UnicodeError) as exc:
        print(f"blueprint generation failed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
