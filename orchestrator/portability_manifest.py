#!/usr/bin/env python3
"""Build and verify the deterministic Q3 portability inventory."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
from functools import lru_cache
from pathlib import Path, PurePosixPath
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs/semantic_quarantine/PORTABILITY_MANIFEST_v1.json"
SCHEMA = ROOT / "docs/semantic_quarantine/PORTABILITY_MANIFEST_SCHEMA_v1.json"
RECEIPT = ROOT / "docs/semantic_quarantine/PORTABILITY_RECEIPT_v1.json"
RELOCATION_SCHEMA = ROOT / "docs/semantic_quarantine/PORTABILITY_RELOCATION_SUCCESSOR_SCHEMA_v1.json"
RELOCATION = ROOT / "docs/semantic_quarantine/PORTABILITY_RELOCATION_SUCCESSOR_v1.json"
RELOCATION_RECEIPT = ROOT / "docs/semantic_quarantine/PORTABILITY_RELOCATION_SUCCESSOR_RECEIPT_v1.json"
P9_RECEIPT = ROOT / "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_RECEIPT_v1.json"
WRAPPER = ROOT / "scripts/check_portability.sh"
TOOLCHAIN = ROOT / "q3.lean.aristotle/lean-toolchain"
CURRENT_HEAD = subprocess.check_output(
    ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True
).strip()

# Concatenation keeps the gate from becoming one of its own byte-level hits.
PATTERNS = {
    "HOME_USERS": ("/" + "Users" + "/").encode(),
    "MOUNT_ROOT": ("/" + "mnt" + "/").encode(),
    "HOME_ROOT": ("/" + "home" + "/").encode(),
    "STALE_REPO_MAC": ("rh_" + "lean_01_2026").encode(),
}

ACTIVE_CLEAN_PATHS = (
    "docs/HEAVY_BUILD_RUNBOOK.md",
    "docs/routeB_bus/phase4_scripts/glower_beta_cocycle_check.py",
    "docs/routeB_bus/phase4_scripts/glower_gram_form_check.py",
    "docs/routeB_bus/phase4_scripts/glower_relative_form_check.py",
    "q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/exact_residual_gap_ground_to_trial_one_control_cell.py",
    "q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/validate_exact_residual_gap_ground_to_trial_one_control_cell.py",
    "q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/sync_proshka_github_channel.py",
    "q3.lean.aristotle/scripts/q3_psdpd_step33_endpoint_first_row_context_bundle.py",
    "specs_docs/hooks/q3-toolbelt.sh",
    "specs_docs/systemd/q3-attestation-broker.service",
    "src/energy_functional.py",
    "src/h1_filtered_bulk_match.py",
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json",
    "orchestrator/README.md",
    "orchestrator/ARISTOTLE.md",
    "specs_docs/hooks/README.md",
    "docs/CODEX_CONTROL.md",
    "docs/cartographer/TOOLS.yaml",
    "q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md",
    "q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md",
    "q3.lean.aristotle/ACTIVE/pipeline/PIPELINE_GUIDE.md",
    "q3.lean.aristotle/ACTIVE/pipeline/RESEARCH_ORACLE.md",
)

SCANNER_BOOTSTRAP_PATHS = (
    "docs/semantic_quarantine/PORTABILITY_MANIFEST_SCHEMA_v1.json",
    "docs/semantic_quarantine/PORTABILITY_MANIFEST_v1.json",
    "docs/semantic_quarantine/PORTABILITY_RECEIPT_v1.json",
    "orchestrator/portability_manifest.py",
    "orchestrator/tests/test_portability_manifest.py",
    "scripts/check_portability.sh",
)

MACHINE_LOCAL_REGISTRIES = ("docs/cartographer/lean_bases.yaml",)
APPEND_HISTORY_SURFACES = ("docs/routeB_bus/PROSHKA_QUEUE.md",)

MANAGED_PATHS = (
    frozenset(ACTIVE_CLEAN_PATHS)
    | {
        "docs/semantic_quarantine/PORTABILITY_MANIFEST_SCHEMA_v1.json",
        "docs/semantic_quarantine/PORTABILITY_MANIFEST_v1.json",
        "docs/semantic_quarantine/PORTABILITY_RECEIPT_v1.json",
        "orchestrator/portability_manifest.py",
        "orchestrator/tests/test_portability_manifest.py",
        "scripts/check_portability.sh",
        "q3.lean.aristotle/ACTIVE/aristotle/models_knowledge",
        "q3.lean.aristotle/ACTIVE/refs/specs/spec_critical_constants_rh_q3.md",
        "q3.lean.aristotle/ACTIVE/refs/specs/spec_formalizing_rh_insights.md",
        "q3.lean.aristotle/ACTIVE/refs/specs/spec_high_ers_constants.md",
        "q3.lean.aristotle/ACTIVE/refs/specs/spec_rh_q3_decomposition.md",
    }
    | set(MACHINE_LOCAL_REGISTRIES)
)

P7_ALLOWED_PATHS = frozenset(MANAGED_PATHS - set(MACHINE_LOCAL_REGISTRIES))
P7_REQUIRED_CHANGED_PATHS = P7_ALLOWED_PATHS - {str(RECEIPT.relative_to(ROOT))}


def live_head() -> str:
    return subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()


def origin_head() -> str:
    return subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "origin/rh_clean"], text=True
    ).strip()


def fetch_origin() -> None:
    subprocess.run(
        ["git", "-C", str(ROOT), "fetch", "origin", "rh_clean"],
        check=True,
        stdout=subprocess.DEVNULL,
    )


def assert_freeze_head(expected: str) -> str:
    current_live = live_head()
    current_origin = origin_head()
    if current_live != expected or current_origin != expected:
        raise PortabilityError(
            f"P7_FREEZE_HEAD_ORIGIN_DRIFT:{expected}:{current_live}:{current_origin}"
        )
    return current_live


def prospective_tree() -> str:
    """Build a frozen candidate tree in a private index, excluding only its receipt."""
    with tempfile.TemporaryDirectory() as td:
        index = Path(td) / "index"
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(index)
        subprocess.run(
            ["git", "-C", str(ROOT), "read-tree", CURRENT_HEAD],
            env=env,
            check=True,
            stdout=subprocess.DEVNULL,
        )
        candidates = sorted(
            path
            for path in MANAGED_PATHS
            if path != str(RECEIPT.relative_to(ROOT))
            and ((ROOT / path).exists() or (ROOT / path).is_symlink())
        )
        subprocess.run(
            ["git", "-C", str(ROOT), "add", "--", *candidates],
            env=env,
            check=True,
            stdout=subprocess.DEVNULL,
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "rm",
                "--cached",
                "--ignore-unmatch",
                "--",
                str(RECEIPT.relative_to(ROOT)),
            ],
            env=env,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return subprocess.check_output(
            ["git", "-C", str(ROOT), "write-tree"], env=env, text=True
        ).strip()


class PortabilityError(RuntimeError):
    pass


P7_V1_IMMUTABLE_HASHES = {
    "manifest": "a1ed7662a59fe95a48c1efe2a0199f7645e0d49f63f850713e25ae7d5bc9bd9f",
    "receipt": "c5f8af3e895bfd8019f2cd9e6c1c6e550ac795b3561feb11f12c9ca7496c38ec",
}


def validate_relocation_row(payload: dict[str, Any], original: dict[str, Any]) -> None:
    source = ".codex_browser_snapshot_proshka.md"  # P9_TYPED relocation source
    target = "archive/root_artifacts/browser_snapshots/.codex_browser_snapshot_proshka.md"  # P9_TYPED relocation target
    if len(payload.get("relocations", [])) != 1:
        raise PortabilityError("P7_RELOCATION_COUNT_DRIFT")
    row = payload["relocations"][0]
    expected_successor = dict(original)
    expected_successor["path"] = target
    expected_successor["classification_basis"] = "P7_V1_EXACT_HASH_RELOCATED_BY_P9"
    if (
        row.get("source") != source
        or row.get("target") != target
        or row.get("original_row") != original
        or row.get("successor_row") != expected_successor
        or row.get("blob_sha256_preserved") is not True
    ):
        raise PortabilityError("P7_RELOCATION_ROW_DRIFT")


def exact_tree_entry(treeish: str, path: str) -> tuple[str, str, str] | None:
    raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-tree", treeish, "--", path], text=True
    ).strip()
    if not raw:
        return None
    mode, kind, oid = raw.split("\t", 1)[0].split()
    return mode, kind, oid


def verify_relocation_successor(treeish: str | None = None) -> None:
    for label, path in {"manifest": MANIFEST, "receipt": RECEIPT}.items():
        if sha256(path.read_bytes()) != P7_V1_IMMUTABLE_HASHES[label]:
            raise PortabilityError(f"P7_V1_IMMUTABLE_PREDECESSOR_DRIFT:{label}")
    if not all(path.is_file() for path in (RELOCATION_SCHEMA, RELOCATION, RELOCATION_RECEIPT, P9_RECEIPT)):
        raise PortabilityError("P7_RELOCATION_SUCCESSOR_MISSING")
    payload = json.loads(RELOCATION.read_text())
    try:
        import jsonschema
    except ImportError as exc:
        raise PortabilityError("P7_RELOCATION_JSONSCHEMA_UNAVAILABLE") from exc
    try:
        jsonschema.Draft202012Validator(json.loads(RELOCATION_SCHEMA.read_text())).validate(payload)
    except jsonschema.ValidationError as exc:
        raise PortabilityError(f"P7_RELOCATION_SCHEMA_INVALID:{exc.message}") from exc
    source = ".codex_browser_snapshot_proshka.md"  # P9_TYPED relocation source
    target = "archive/root_artifacts/browser_snapshots/.codex_browser_snapshot_proshka.md"  # P9_TYPED relocation target
    original = next(
        item for item in json.loads(MANIFEST.read_text())["historical_hits"] if item["path"] == source
    )
    validate_relocation_row(payload, original)
    row = payload["relocations"][0]
    expected_successor = row["successor_row"]
    p9 = json.loads(P9_RECEIPT.read_text())
    selected = treeish
    if selected is None:
        selected = CURRENT_HEAD if exact_tree_entry(CURRENT_HEAD, source) is None else p9.get("prospective_tree_excluding_receipt")
    if not isinstance(selected, str):
        raise PortabilityError("P7_RELOCATION_TREE_MISSING")
    if exact_tree_entry(selected, source) is not None:
        raise PortabilityError("P7_RELOCATION_SOURCE_RESURRECTED")
    target_entry = exact_tree_entry(selected, target)
    if target_entry is None or target_entry[0] != "100644":
        raise PortabilityError("P7_RELOCATION_TARGET_MISSING_OR_MODE")
    data = tree_blob(selected, target)
    if sha256(data) != original["sha256"] or sha256(data) != expected_successor["sha256"]:
        raise PortabilityError("P7_RELOCATION_SHA256_NOT_PRESERVED")
    successor_receipt = json.loads(RELOCATION_RECEIPT.read_text())
    if successor_receipt.get("predecessor_hashes") != P7_V1_IMMUTABLE_HASHES:
        raise PortabilityError("P7_RELOCATION_RECEIPT_PREDECESSOR_DRIFT")
    if successor_receipt.get("hashes", {}).get("successor") != sha256(RELOCATION.read_bytes()):
        raise PortabilityError("P7_RELOCATION_RECEIPT_HASH_DRIFT")


def run_relocation_plants() -> None:
    verify_relocation_successor()
    payload = json.loads(RELOCATION.read_text())
    original = payload["relocations"][0]["original_row"]
    poisoned = json.loads(json.dumps(payload))
    poisoned["relocations"][0]["successor_row"]["sha256"] = "0" * 64
    try:
        validate_relocation_row(poisoned, original)
    except PortabilityError as exc:
        if str(exc) != "P7_RELOCATION_ROW_DRIFT":
            raise
    else:
        raise PortabilityError("PLANT_MISSED:P7_RELOCATION_ROW_DRIFT")


def run_git(*args: str, text: bool = False) -> bytes | str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=text)


@lru_cache(maxsize=1)
def head_snapshot() -> tuple[frozenset[str], dict[str, bytes], dict[str, str]]:
    """Read one captured commit with one grep, one tree walk, and one blob batch."""
    treeish = prospective_tree()
    grep_cmd = ["git", "-C", str(ROOT), "grep", "-Il", "-z"]
    for token in PATTERNS.values():
        grep_cmd.extend(("-e", token.decode()))
    grep_cmd.extend((treeish, "--"))
    raw_hits = subprocess.check_output(grep_cmd)
    prefix = (treeish + ":").encode()
    hit_paths = {
        item.removeprefix(prefix).decode("utf-8", "surrogateescape")
        for item in raw_hits.split(b"\0")
        if item
    }

    raw_tree = subprocess.check_output(["git", "-C", str(ROOT), "ls-tree", "-r", "-z", treeish])
    tree: dict[str, tuple[str, str]] = {}
    for item in raw_tree.split(b"\0"):
        if not item:
            continue
        meta, raw_path = item.split(b"\t", 1)
        mode, _kind, oid = meta.decode().split()
        tree[raw_path.decode("utf-8", "surrogateescape")] = (mode, oid)

    needed = sorted(hit_paths | {path for path, (mode, _) in tree.items() if mode == "120000"})
    request = "".join(tree[path][1] + "\n" for path in needed).encode()
    proc = subprocess.Popen(
        ["git", "-C", str(ROOT), "cat-file", "--batch"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    )
    stdout, _ = proc.communicate(request)
    if proc.returncode != 0:
        raise PortabilityError("HEAD_BLOB_BATCH_READ_FAILED")
    cursor = 0
    blobs: dict[str, bytes] = {}
    for path in needed:
        end = stdout.index(b"\n", cursor)
        header = stdout[cursor:end].decode().split()
        if len(header) != 3 or header[1] != "blob":
            raise PortabilityError(f"TRACKED_BYTE_READ_FAILED:{path}")
        size = int(header[2])
        start = end + 1
        blobs[path] = stdout[start : start + size]
        cursor = start + size + 1
    hits = {path: blobs[path] for path in hit_paths}
    symlinks = {
        path: blobs[path].decode("utf-8") for path, (mode, _) in tree.items() if mode == "120000"
    }
    return frozenset(tree), hits, symlinks


def tracked_paths() -> list[str]:
    paths, _, _ = head_snapshot()
    return sorted(
        set(paths) | {p for p in MANAGED_PATHS if (ROOT / p).exists() or (ROOT / p).is_symlink()}
    )


def effective_bytes(path: str) -> bytes:
    local = ROOT / path
    if path in MANAGED_PATHS:
        if local.is_symlink():
            return os.readlink(local).encode("utf-8")
        return local.read_bytes()
    _, hits, symlinks = head_snapshot()
    if path in hits:
        return hits[path]
    if path in symlinks:
        return symlinks[path].encode("utf-8")
    raise PortabilityError(f"NONHIT_HEAD_BYTES_NOT_RETAINED:{path}")


def effective_symlinks(paths: list[str]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    _, _, head_links = head_snapshot()
    for path in paths:
        local = ROOT / path
        managed_link = path in MANAGED_PATHS and local.is_symlink()
        if not managed_link and path not in head_links:
            continue
        target = os.readlink(local) if managed_link else head_links[path]
        rows.append(
            {
                "path": path,
                "class": "TRACKED_RELATIVE_SYMLINK",
                "target": target,
                "sha256": sha256(target.encode()),
            }
        )
    return sorted(rows, key=lambda row: row["path"])


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def validate_machine_local_registry(path: str, data: bytes) -> dict[str, str]:
    import yaml

    payload = yaml.safe_load(data)

    def walk(value: Any, field_path: tuple[str | int, ...] = ()) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                walk(child, (*field_path, str(key)))
        elif isinstance(value, list):
            for index, child in enumerate(value):
                walk(child, (*field_path, index))
        elif isinstance(value, str) and hit_ids(value.encode()):
            allowed = (
                len(field_path) == 4
                and field_path[0] == "bases"
                and isinstance(field_path[1], int)
                and field_path[2] == "paths"
                and isinstance(field_path[3], int)
            )
            if not allowed:
                rendered = ".".join(str(part) for part in field_path)
                raise PortabilityError(
                    f"MACHINE_LOCAL_REGISTRY_HIT_OUTSIDE_ALLOWED_FIELD:{path}:{rendered}"
                )

    walk(payload)
    return {
        "path": path,
        "class": "ACTIVE_MACHINE_LOCAL_REGISTRY",
        "allowed_candidate_path_field": "bases[*].paths",
        "evidence": "MACHINE_CANDIDATES_ONLY_NOT_CANONICAL_REPO_LOCATORS",
        "sha256": sha256(data),
    }


def validate_append_history_surface(path: str, data: bytes) -> dict[str, Any]:
    data.decode("utf-8")
    return {
        "path": path,
        "class": "ACTIVE_APPEND_ONLY_HISTORY",
        "classification_basis": "P5_STATUS_SURFACE_REGISTRY_HISTORICAL_APPEND_QUEUE",
        "validation": "FIRST_PARENT_FULL_BYTE_PREFIX_CHAIN_ANCHORED_AT_FREEZE",
    }


def tree_blob(treeish: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{treeish}:{path}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if result.returncode != 0:
        raise PortabilityError(f"CANDIDATE_TREE_BLOB_MISSING:{path}")
    return result.stdout


def tree_mode(treeish: str, path: str) -> str:
    raw = subprocess.run(
        ["git", "-C", str(ROOT), "ls-tree", treeish, "--", path],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
    )
    if raw.returncode != 0 or not raw.stdout.strip():
        raise PortabilityError(f"CANDIDATE_TREE_PATH_MISSING:{path}")
    return raw.stdout.split(None, 1)[0]


def normalize_repo_path(path: PurePosixPath, *, link_path: str) -> PurePosixPath:
    normalized: list[str] = []
    for part in path.parts:
        if part in ("", "."):
            continue
        if part == "..":
            if not normalized:
                raise PortabilityError(f"ESCAPING_SYMLINK:{link_path}")
            normalized.pop()
        else:
            normalized.append(part)
    return PurePosixPath(*normalized)


def resolve_manifest_link(
    path: str, target: str, links: dict[str, str], tree_paths: set[str]
) -> str:
    candidate = normalize_repo_path(PurePosixPath(path).parent / target, link_path=path)
    for _ in range(len(links) + 1):
        parts = candidate.parts
        replacement: PurePosixPath | None = None
        for index in range(1, len(parts) + 1):
            prefix = PurePosixPath(*parts[:index]).as_posix()
            if prefix not in links:
                continue
            replacement = normalize_repo_path(
                PurePosixPath(prefix).parent / links[prefix] / PurePosixPath(*parts[index:]),
                link_path=path,
            )
            break
        if replacement is None:
            rendered = candidate.as_posix()
            if rendered not in tree_paths and not any(
                item.startswith(rendered + "/") for item in tree_paths
            ):
                raise PortabilityError(f"PORTABILITY_CANDIDATE_BROKEN_SYMLINK:{path}")
            return rendered
        candidate = replacement
    raise PortabilityError(f"PORTABILITY_CANDIDATE_SYMLINK_CYCLE:{path}")


def queue_anchor(commit: str = CURRENT_HEAD) -> dict[str, Any]:
    path = APPEND_HISTORY_SURFACES[0]
    data = tree_blob(commit, path)
    return {
        "path": path,
        "commit": commit,
        "byte_length": len(data),
        "sha256": sha256(data),
    }


def validate_full_byte_prefix_chain(blobs: list[bytes]) -> None:
    for previous, current in zip(blobs, blobs[1:], strict=False):
        if len(current) < len(previous):
            raise PortabilityError("APPEND_HISTORY_SHORTENED")
        if not current.startswith(previous):
            raise PortabilityError("APPEND_HISTORY_BYTE_REWRITE")


def verify_append_history_anchor(
    anchor: dict[str, Any], *, head: str | None = None, worktree_bytes: bytes | None = None
) -> None:
    required = {"path", "commit", "byte_length", "sha256"}
    if not isinstance(anchor, dict) or set(anchor) != required:
        raise PortabilityError("APPEND_HISTORY_ANCHOR_INVALID")
    path = anchor["path"]
    commit = anchor["commit"]
    if path not in APPEND_HISTORY_SURFACES or not isinstance(commit, str):
        raise PortabilityError("APPEND_HISTORY_ANCHOR_INVALID")
    anchored = tree_blob(commit, path)
    if anchor["byte_length"] != len(anchored) or anchor["sha256"] != sha256(anchored):
        raise PortabilityError("APPEND_HISTORY_ANCHOR_BLOB_DRIFT")
    current = CURRENT_HEAD if head is None else head
    first_parent = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-list", "--first-parent", current], text=True
    ).splitlines()
    if commit not in first_parent:
        raise PortabilityError("APPEND_HISTORY_ANCHOR_NOT_ON_FIRST_PARENT_CHAIN")
    commits = subprocess.check_output(
        [
            "git",
            "-C",
            str(ROOT),
            "rev-list",
            "--first-parent",
            "--reverse",
            f"{commit}..{current}",
        ],
        text=True,
    ).splitlines()
    blobs = [anchored, *(tree_blob(revision, path) for revision in commits)]
    live = (ROOT / path).read_bytes() if worktree_bytes is None else worktree_bytes
    blobs.append(live)
    validate_full_byte_prefix_chain(blobs)


def hit_ids(data: bytes) -> list[str]:
    return [name for name, token in PATTERNS.items() if token in data]


def classify_hit(path: str, data: bytes, manifest: dict[str, Any]) -> str:
    hits = hit_ids(data)
    if not hits:
        return "NO_PATTERN_HIT"
    active = {row["path"] for row in manifest["active_clean_paths"]}
    historical = {row["path"]: row for row in manifest["historical_hits"]}
    if path in active:
        raise PortabilityError(f"HISTORICAL_PATH_MUTATED_OR_ACTIVE:{path}")
    if path not in historical:
        raise PortabilityError(f"ABSOLUTE_PATH_UNCLASSIFIED:{path}")
    row = historical[path]
    if row["sha256"] != sha256(data) or row["pattern_ids"] != hits:
        raise PortabilityError(f"HISTORICAL_BYTES_OR_CLASS_DRIFT:{path}")
    return "HISTORICAL_PINNED"


def build_inventory() -> dict[str, Any]:
    paths = tracked_paths()
    historical: list[dict[str, Any]] = []
    active = set(ACTIVE_CLEAN_PATHS)
    _, head_hits, _ = head_snapshot()
    specially_classified = set(MACHINE_LOCAL_REGISTRIES) | set(APPEND_HISTORY_SURFACES)
    candidates = (set(head_hits) - specially_classified) | {
        path
        for path in MANAGED_PATHS
        if path not in MACHINE_LOCAL_REGISTRIES
        and (ROOT / path).exists()
        and not (ROOT / path).is_symlink()
    }
    for path in sorted(candidates):
        data = effective_bytes(path)
        hits = hit_ids(data)
        if path in active:
            if hits:
                raise PortabilityError(f"ACTIVE_PATH_NOT_PORTABLE:{path}:{','.join(hits)}")
        elif hits:
            historical.append(
                {
                    "path": path,
                    "class": "HISTORICAL_PINNED",
                    "classification_basis": "EXACT_PATH_AND_SHA256_P7_REVIEWED_BASELINE",
                    "sha256": sha256(data),
                    "pattern_ids": hits,
                }
            )
    return {
        "schema_version": "q3.portability_manifest.v1",
        "pattern_ids": list(PATTERNS),
        "scanner_bootstrap_paths": [
            {"path": path, "class": "SCANNER_BOOTSTRAP"} for path in SCANNER_BOOTSTRAP_PATHS
        ],
        "active_clean_paths": [
            {
                "path": path,
                "class": "ACTIVE_PORTABLE",
                **(
                    {"repo_relative_to": "GIT_TOPLEVEL", "canonical_repo_path_consumer_count": 0}
                    if path.endswith("ROUTE_B_EXECUTION_STATE.json")
                    else {}
                ),
            }
            for path in ACTIVE_CLEAN_PATHS
        ],
        "active_machine_local_registries": [
            validate_machine_local_registry(path, effective_bytes(path))
            for path in MACHINE_LOCAL_REGISTRIES
        ],
        "active_append_history_surfaces": [
            validate_append_history_surface(path, effective_bytes(path))
            for path in APPEND_HISTORY_SURFACES
        ],
        "historical_hits": historical,
        "symlinks": effective_symlinks(paths),
    }


def validate_shape(data: dict[str, Any]) -> None:
    try:
        import jsonschema
    except ImportError as exc:
        raise PortabilityError("JSONSCHEMA_UNAVAILABLE") from exc
    schema = json.loads(SCHEMA.read_text())
    try:
        jsonschema.Draft202012Validator(schema).validate(data)
    except jsonschema.ValidationError as exc:
        raise PortabilityError(f"MANIFEST_SCHEMA_INVALID:{exc.message}") from exc


def resolved_link(path: str, target: str) -> Path:
    if PurePosixPath(target).is_absolute():
        raise PortabilityError(f"ABSOLUTE_SYMLINK:{path}")
    candidate = (ROOT / path).parent / target
    resolved = candidate.resolve(strict=False)
    try:
        resolved.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise PortabilityError(f"ESCAPING_SYMLINK:{path}") from exc
    if not resolved.exists():
        raise PortabilityError(f"BROKEN_SYMLINK:{path}")
    return resolved


def check_wrapper(path: Path) -> None:
    if not path.exists():
        raise PortabilityError("WRAPPER_MISSING")
    if not os.access(path, os.X_OK):
        raise PortabilityError("WRAPPER_NOT_EXECUTABLE")


def staged_symlink_plant(target: str) -> None:
    """Insert a synthetic link in a private index and require the scanner to reject it."""
    oid = (
        subprocess.check_output(
            ["git", "-C", str(ROOT), "hash-object", "-w", "--stdin"],
            input=target.encode(),
        )
        .decode()
        .strip()
    )
    with tempfile.TemporaryDirectory() as td:
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(Path(td) / "index")
        subprocess.run(["git", "-C", str(ROOT), "read-tree", CURRENT_HEAD], env=env, check=True)
        plant_path = "q3.lean.aristotle/ACTIVE/refs/portability-plant-link"
        subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "update-index",
                "--add",
                "--cacheinfo",
                "120000",
                oid,
                plant_path,
            ],
            env=env,
            check=True,
        )
        tree = subprocess.check_output(
            ["git", "-C", str(ROOT), "write-tree"], env=env, text=True
        ).strip()
        scanned = subprocess.check_output(
            ["git", "-C", str(ROOT), "show", f"{tree}:{plant_path}"], text=True
        )
        resolved_link(plant_path, scanned)


def verify(manifest: dict[str, Any]) -> None:
    validate_shape(manifest)
    expected = build_inventory()
    historical = {row["path"]: row for row in manifest["historical_hits"]}
    actual_historical = {row["path"]: row for row in expected["historical_hits"]}
    if historical.keys() != actual_historical.keys():
        missing = sorted(actual_historical.keys() - historical.keys())
        stale = sorted(historical.keys() - actual_historical.keys())
        raise PortabilityError(f"INVENTORY_INCOMPLETE:missing={missing}:stale={stale}")
    for path, row in historical.items():
        if row != actual_historical[path]:
            raise PortabilityError(f"HISTORICAL_BYTES_OR_CLASS_DRIFT:{path}")
    if manifest["scanner_bootstrap_paths"] != expected["scanner_bootstrap_paths"]:
        raise PortabilityError("SCANNER_BOOTSTRAP_SET_DRIFT")
    if manifest["active_clean_paths"] != expected["active_clean_paths"]:
        raise PortabilityError("ACTIVE_PATH_SET_DRIFT")
    if manifest["active_machine_local_registries"] != expected["active_machine_local_registries"]:
        raise PortabilityError("MACHINE_LOCAL_REGISTRY_DRIFT")
    if manifest["active_append_history_surfaces"] != expected["active_append_history_surfaces"]:
        raise PortabilityError("APPEND_HISTORY_SURFACE_DRIFT")
    if manifest["symlinks"] != expected["symlinks"]:
        raise PortabilityError("SYMLINK_INVENTORY_DRIFT")
    if len(manifest["symlinks"]) != 35:
        raise PortabilityError(f"SYMLINK_COUNT_DRIFT:{len(manifest['symlinks'])}")
    for row in manifest["symlinks"]:
        resolved_link(row["path"], row["target"])
    check_wrapper(WRAPPER)
    check_staged_scope()


def check_staged_scope(index_file: Path | None = None) -> None:
    env = os.environ.copy()
    if index_file is not None:
        env["GIT_INDEX_FILE"] = str(index_file)
    raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "diff", "--cached", "--name-only", "-z", live_head(), "--"],
        env=env,
    )
    staged = {item.decode("utf-8", "surrogateescape") for item in raw.split(b"\0") if item}
    outside = sorted(staged - P7_ALLOWED_PATHS)
    if outside:
        raise PortabilityError(f"P7_STAGED_SCOPE_DRIFT:{outside}")


def staged_scope_plant() -> None:
    oid = (
        subprocess.check_output(
            ["git", "-C", str(ROOT), "hash-object", "-w", "--stdin"], input=b"README.md"
        )
        .decode()
        .strip()
    )
    with tempfile.TemporaryDirectory() as td:
        index = Path(td) / "index"
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(index)
        subprocess.run(["git", "-C", str(ROOT), "read-tree", CURRENT_HEAD], env=env, check=True)
        subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "update-index",
                "--add",
                "--cacheinfo",
                "120000",
                oid,
                "outside-p7-staged-link",
            ],
            env=env,
            check=True,
        )
        check_staged_scope(index)


def receipt(manifest: dict[str, Any], provenance: dict[str, Any] | None = None) -> dict[str, Any]:
    source_commit = CURRENT_HEAD if provenance is None else provenance["source_commit"]
    candidate_tree = (
        prospective_tree()
        if provenance is None
        else provenance["prospective_tree_excluding_receipt"]
    )
    append_anchor = (
        queue_anchor(CURRENT_HEAD) if provenance is None else provenance["append_history_anchor"]
    )
    return {
        "schema_version": "q3.portability_receipt.v1",
        "status": "PASS",
        "source_commit": source_commit,
        "prospective_tree_excluding_receipt": candidate_tree,
        "append_history_anchor": append_anchor,
        "historical_hit_file_count": len(manifest["historical_hits"]),
        "active_clean_path_count": len(manifest["active_clean_paths"]),
        "active_machine_local_registry_count": len(manifest["active_machine_local_registries"]),
        "active_append_history_surface_count": len(manifest["active_append_history_surfaces"]),
        "symlink_count": len(manifest["symlinks"]),
        "hashes": {
            "manifest": sha256(MANIFEST.read_bytes()),
            "schema": sha256(SCHEMA.read_bytes()),
            "checker": sha256(Path(__file__).read_bytes()),
            "tests": sha256(
                (ROOT / "orchestrator/tests/test_portability_manifest.py").read_bytes()
            ),
            "wrapper": sha256(WRAPPER.read_bytes()),
            "lean_toolchain": sha256(TOOLCHAIN.read_bytes()),
        },
        "plants": [
            "ACTIVE_ABSOLUTE_PATH",
            "ACTIVE_STALE_REPO_NAME",
            "ABSOLUTE_PATH_UNCLASSIFIED",
            "INVENTORY_INCOMPLETE",
            "HISTORICAL_PATH_MUTATED_OR_ACTIVE",
            "ABSOLUTE_SYMLINK",
            "ESCAPING_SYMLINK",
            "BROKEN_SYMLINK",
            "WRAPPER_MISSING",
            "WRAPPER_NOT_EXECUTABLE",
            "P7_STAGED_SCOPE_DRIFT",
        ],
    }


def verify_candidate_tree(payload: dict[str, Any]) -> None:
    source = payload["source_commit"]
    tree = payload["prospective_tree_excluding_receipt"]
    changed_raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "diff", "--name-only", "-z", source, tree, "--"]
    )
    changed = {item.decode("utf-8", "surrogateescape") for item in changed_raw.split(b"\0") if item}
    if changed != P7_REQUIRED_CHANGED_PATHS:
        missing = sorted(P7_REQUIRED_CHANGED_PATHS - changed)
        outside = sorted(changed - P7_REQUIRED_CHANGED_PATHS)
        raise PortabilityError(
            f"PORTABILITY_CANDIDATE_TREE_EXACT_SCOPE_DRIFT:missing={missing}:outside={outside}"
        )

    hash_paths = {
        "manifest": str(MANIFEST.relative_to(ROOT)),
        "schema": str(SCHEMA.relative_to(ROOT)),
        "checker": str(Path(__file__).relative_to(ROOT)),
        "tests": "orchestrator/tests/test_portability_manifest.py",
        "wrapper": str(WRAPPER.relative_to(ROOT)),
        "lean_toolchain": str(TOOLCHAIN.relative_to(ROOT)),
    }
    hashes = payload.get("hashes")
    if not isinstance(hashes, dict) or set(hashes) != set(hash_paths):
        raise PortabilityError("PORTABILITY_RECEIPT_HASH_SET_INVALID")
    for label, path in hash_paths.items():
        if hashes[label] != sha256(tree_blob(tree, path)):
            raise PortabilityError(f"PORTABILITY_CANDIDATE_TREE_HASH_MISMATCH:{label}")

    candidate_manifest = json.loads(tree_blob(tree, str(MANIFEST.relative_to(ROOT))))
    symlink_rows = candidate_manifest.get("symlinks", [])
    links = {row["path"]: row["target"] for row in symlink_rows}
    raw_tree = subprocess.check_output(["git", "-C", str(ROOT), "ls-tree", "-r", "-z", tree])
    tree_paths = {
        item.split(b"\t", 1)[1].decode("utf-8", "surrogateescape")
        for item in raw_tree.split(b"\0")
        if item
    }
    for row in symlink_rows:
        path = row["path"]
        if tree_mode(tree, path) != "120000":
            raise PortabilityError(f"PORTABILITY_CANDIDATE_SYMLINK_MODE_DRIFT:{path}")
        target = tree_blob(tree, path)
        if target != row["target"].encode() or sha256(target) != row["sha256"]:
            raise PortabilityError(f"PORTABILITY_CANDIDATE_SYMLINK_TARGET_DRIFT:{path}")
        resolve_manifest_link(path, row["target"], links, tree_paths)

    anchor = payload.get("append_history_anchor")
    if not isinstance(anchor, dict):
        raise PortabilityError("APPEND_HISTORY_ANCHOR_INVALID")
    if tree_blob(tree, anchor.get("path", "")) != tree_blob(
        anchor.get("commit", ""), anchor.get("path", "")
    ):
        raise PortabilityError("PORTABILITY_CANDIDATE_QUEUE_ANCHOR_DRIFT")


def verify_receipt_provenance(payload: dict[str, Any], head: str | None = None) -> None:
    source = payload.get("source_commit")
    tree = payload.get("prospective_tree_excluding_receipt")
    if not isinstance(source, str) or not isinstance(tree, str):
        raise PortabilityError("PORTABILITY_PROVENANCE_MISSING")
    for object_name, suffix, code in (
        (source, "^{commit}", "PORTABILITY_SOURCE_COMMIT_MISSING"),
        (tree, "^{tree}", "PORTABILITY_CANDIDATE_TREE_MISSING"),
    ):
        result = subprocess.run(
            ["git", "-C", str(ROOT), "cat-file", "-e", object_name + suffix],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if result.returncode != 0:
            raise PortabilityError(code)
    current = (
        head
        or subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    )
    if (
        subprocess.run(
            ["git", "-C", str(ROOT), "merge-base", "--is-ancestor", source, current],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode
        != 0
    ):
        raise PortabilityError("PORTABILITY_SOURCE_NOT_ANCESTOR")
    verify_candidate_tree(payload)
    verify_append_history_anchor(payload.get("append_history_anchor"), head=current)


def p7_candidate_dirty() -> bool:
    raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "status", "--porcelain=v1", "-z", "--", *sorted(P7_ALLOWED_PATHS)]
    )
    return bool(raw)


def verify_precommit_provenance(
    payload: dict[str, Any], *, dirty: bool | None = None, current_head: str | None = None
) -> None:
    is_dirty = p7_candidate_dirty() if dirty is None else dirty
    current = CURRENT_HEAD if current_head is None else current_head
    if is_dirty and payload.get("source_commit") != current:
        raise PortabilityError("PORTABILITY_PRECOMMIT_PROVENANCE_STALE")
    if is_dirty and payload.get("prospective_tree_excluding_receipt") != prospective_tree():
        raise PortabilityError("PORTABILITY_PRECOMMIT_CANDIDATE_TREE_STALE")


def freeze_provenance(manifest: dict[str, Any]) -> None:
    fetch_origin()
    current_live_head = assert_freeze_head(CURRENT_HEAD)
    verify(manifest)
    check_staged_scope()
    frozen = receipt(
        manifest,
        {
            "source_commit": CURRENT_HEAD,
            "prospective_tree_excluding_receipt": prospective_tree(),
            "append_history_anchor": queue_anchor(CURRENT_HEAD),
        },
    )
    write_json(RECEIPT, frozen)
    fetch_origin()
    post_write_head = assert_freeze_head(current_live_head)
    verify_receipt_provenance(frozen, head=post_write_head)
    verify_precommit_provenance(frozen)


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


def run_plants() -> None:
    active_abs = b"prefix " + PATTERNS["HOME_USERS"] + b"person/project"
    if "HOME_USERS" not in hit_ids(active_abs):
        raise PortabilityError("PLANT_MISSED:ACTIVE_ABSOLUTE_PATH")
    if "STALE_REPO_MAC" not in hit_ids(PATTERNS["STALE_REPO_MAC"]):
        raise PortabilityError("PLANT_MISSED:ACTIVE_STALE_REPO_NAME")
    manifest = json.loads(MANIFEST.read_text())
    try:
        classify_hit("scripts/new_active.py", active_abs, manifest)
    except PortabilityError as exc:
        if not str(exc).startswith("ABSOLUTE_PATH_UNCLASSIFIED"):
            raise
    else:
        raise PortabilityError("PLANT_MISSED:ABSOLUTE_PATH_UNCLASSIFIED")
    historical = manifest["historical_hits"][0]
    promoted = json.loads(json.dumps(manifest))
    promoted["historical_hits"] = [
        row for row in promoted["historical_hits"] if row["path"] != historical["path"]
    ]
    promoted["active_clean_paths"].append({"path": historical["path"], "class": "ACTIVE_PORTABLE"})
    try:
        classify_hit(historical["path"], effective_bytes(historical["path"]), promoted)
    except PortabilityError as exc:
        if not str(exc).startswith("HISTORICAL_PATH_MUTATED_OR_ACTIVE"):
            raise
    else:
        raise PortabilityError("PLANT_MISSED:HISTORICAL_PATH_MUTATED_OR_ACTIVE")
    omitted = json.loads(json.dumps(manifest))
    omitted["historical_hits"] = omitted["historical_hits"][1:]
    try:
        verify(omitted)
    except PortabilityError as exc:
        if not str(exc).startswith("INVENTORY_INCOMPLETE"):
            raise
    else:
        raise PortabilityError("PLANT_MISSED:INVENTORY_INCOMPLETE")
    with tempfile.TemporaryDirectory(dir=ROOT) as td:
        base = Path(td)
        good = base / "target"
        good.write_text("ok")
        rel = str(base.relative_to(ROOT) / "link")
        for target, code in (
            (str(good), "ABSOLUTE_SYMLINK"),
            ("../../../../outside", "ESCAPING_SYMLINK"),
            ("missing", "BROKEN_SYMLINK"),
        ):
            try:
                resolved_link(rel, target)
            except PortabilityError as exc:
                if not str(exc).startswith(code):
                    raise
            else:
                raise PortabilityError(f"PLANT_MISSED:{code}")
    try:
        staged_symlink_plant(PATTERNS["HOME_USERS"].decode() + "plant/target")
    except PortabilityError as exc:
        if not str(exc).startswith("ABSOLUTE_SYMLINK"):
            raise
    else:
        raise PortabilityError("PLANT_MISSED:STAGED_ABSOLUTE_SYMLINK")
    try:
        staged_scope_plant()
    except PortabilityError as exc:
        if not str(exc).startswith("P7_STAGED_SCOPE_DRIFT"):
            raise
    else:
        raise PortabilityError("PLANT_MISSED:P7_STAGED_SCOPE_DRIFT")
    with tempfile.TemporaryDirectory() as td:
        missing = Path(td) / "missing-wrapper"
        try:
            check_wrapper(missing)
        except PortabilityError as exc:
            if str(exc) != "WRAPPER_MISSING":
                raise
        else:
            raise PortabilityError("PLANT_MISSED:WRAPPER_MISSING")
        missing.write_text("#!/bin/sh\n")
        missing.chmod(0o600)
        try:
            check_wrapper(missing)
        except PortabilityError as exc:
            if str(exc) != "WRAPPER_NOT_EXECUTABLE":
                raise
        else:
            raise PortabilityError("PLANT_MISSED:WRAPPER_NOT_EXECUTABLE")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("build", "check", "plants", "freeze-provenance"))
    args = parser.parse_args()
    try:
        if args.command == "build":
            if RELOCATION.exists():
                verify_relocation_successor()
            elif MANIFEST.exists():
                previous = json.loads(MANIFEST.read_text())
                validate_shape(previous)
                verify(previous)
                prior_receipt = json.loads(RECEIPT.read_text()) if RECEIPT.exists() else None
                if prior_receipt is not None:
                    verify_receipt_provenance(prior_receipt)
                write_json(RECEIPT, receipt(previous, prior_receipt))
            else:
                data = build_inventory()
                validate_shape(data)
                write_json(MANIFEST, data)
                verify(data)
                write_json(RECEIPT, receipt(data))
            print("PORTABILITY_MANIFEST_BUILD_PASS")
        elif args.command == "check":
            if RELOCATION.exists():
                verify_relocation_successor()
            else:
                data = json.loads(MANIFEST.read_text())
                verify(data)
                actual_receipt = json.loads(RECEIPT.read_text())
                verify_receipt_provenance(actual_receipt)
                verify_precommit_provenance(actual_receipt)
                expected_receipt = receipt(data, actual_receipt)
                if actual_receipt != expected_receipt:
                    raise PortabilityError("PORTABILITY_RECEIPT_DRIFT")
            print("PORTABILITY_MANIFEST_CHECK_PASS")
        elif args.command == "plants":
            if RELOCATION.exists():
                run_relocation_plants()
            else:
                run_plants()
            print("PORTABILITY_MANIFEST_PLANTS_PASS")
        else:
            if RELOCATION.exists():
                raise PortabilityError("P7_V1_FREEZE_FORBIDDEN_AFTER_RELOCATION_SUCCESSOR")
            data = json.loads(MANIFEST.read_text())
            freeze_provenance(data)
            print("PORTABILITY_PROVENANCE_FREEZE_PASS")
    except (OSError, json.JSONDecodeError, PortabilityError) as exc:
        print(f"PORTABILITY_MANIFEST_FAIL:{exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
