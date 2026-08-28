#!/usr/bin/env python3
"""Build and verify the P8 root-artifact classification contract."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import tempfile
import unicodedata
from pathlib import Path, PurePosixPath
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
CLASSIFICATION = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_v1.json"
SCHEMA = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_SCHEMA_v1.json"
RECEIPT = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_RECEIPT_v1.json"
CLASSIFICATION_V2 = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_v2.json"
SCHEMA_V2 = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_SCHEMA_v2.json"
RECEIPT_V2 = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_RECEIPT_v2.json"
P9_RECEIPT = ROOT / "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_RECEIPT_v1.json"
TESTS = ROOT / "orchestrator/tests/test_root_artifact_classification.py"
WRAPPER = ROOT / "scripts/check_root_artifacts.sh"
CURRENT_HEAD = subprocess.check_output(
    ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True
).strip()

ARCHIVE_PATHS = frozenset(
    {
        ".codex_browser_snapshot_proshka.md",  # P9_TYPED predecessor declaration
        "FINDINGS_SUMMARY.md",
        "IMPLEMENTATION_PLAN.md",
        "ORCHESTRATION_DESIGN.md",
        "PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean",
        "Q3_OBSTRUCTION_ATLAS.md",
        "Q_STAR_DEFINITIONS.md",
        "TASK.md",
        "bellman_bmo.py",
        "codex_4af2_uncommitted_20260727.patch",  # P9_TYPED predecessor declaration
        "idei dla.txt",
        "louise-current-snapshot.md",
        "louise-current-tab.png",  # P9_TYPED predecessor declaration
        "louise-last-response.md",  # P9_TYPED predecessor declaration
        "memo.md",
        "project_tree.txt",
        "run.jsonl",  # P9_TYPED predecessor declaration
        "verify_phase0.py",
        "verify_q_tail.py",
        "verify_variant_b.py",
    }
)

ARCHIVE_GROUPS = {
    "browser_snapshots": {
        ".codex_browser_snapshot_proshka.md",  # P9_TYPED predecessor group
        "louise-current-snapshot.md",
        "louise-current-tab.png",  # P9_TYPED predecessor group
        "louise-last-response.md",  # P9_TYPED predecessor group
    },
    "generated_lean": {
        "PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean"
    },
    "historical_docs": {
        "FINDINGS_SUMMARY.md",
        "IMPLEMENTATION_PLAN.md",
        "ORCHESTRATION_DESIGN.md",
        "Q3_OBSTRUCTION_ATLAS.md",
        "Q_STAR_DEFINITIONS.md",
        "TASK.md",
    },
    "experimental_scripts": {
        "bellman_bmo.py",
        "verify_phase0.py",
        "verify_q_tail.py",
        "verify_variant_b.py",
    },
    "provenance": {
        "codex_4af2_uncommitted_20260727.patch",  # P9_TYPED predecessor group
        "project_tree.txt",
        "run.jsonl",  # P9_TYPED predecessor group
    },
    "research_notes": {"idei dla.txt", "memo.md"},
}

P8_ALLOWED_PATHS = frozenset(
    {
        str(CLASSIFICATION.relative_to(ROOT)),
        str(SCHEMA.relative_to(ROOT)),
        str(RECEIPT.relative_to(ROOT)),
        str(Path(__file__).relative_to(ROOT)),
        str(TESTS.relative_to(ROOT)),
        str(WRAPPER.relative_to(ROOT)),
    }
)
P8_CANDIDATE_PATHS = P8_ALLOWED_PATHS - {str(RECEIPT.relative_to(ROOT))}

PYTHON_ROOT_OUTPUT_PATTERNS = (
    re.compile(
        r"\b(?:Path|PurePath)\(\s*['\"]([^/'\"]+)['\"]\s*\)"
        r"\s*\.\s*(?:write_text|write_bytes|touch|open)\s*\("
    ),
    re.compile(r"\bopen\(\s*['\"]([^/'\"]+)['\"]\s*,\s*['\"][^'\"]*[wax+]"),
    re.compile(r"\.(?:to_csv|to_json|savefig|save)\(\s*['\"]([^/'\"]+)['\"]"),
)
SHELL_TEE_PATTERN = re.compile(
    r"\btee(?:\s+-a)?\s+['\"]?([A-Za-z0-9][A-Za-z0-9_.-]*)['\"]?(?:\s|$)"
)
SCRIPT_OUTPUT_EXCEPTIONS = {
    ("q3.lean.aristotle/scripts/build_docs.sh", "docbuild.log"): (
        "OUTPUT_AFTER_EXPLICIT_CD_TO_NONROOT_DOCBUILD_DIR"
    )
}


class RootArtifactError(RuntimeError):
    pass


P8_V1_IMMUTABLE_HASHES = {
    "schema": "69ee67954fc0292f174aeacd722fe5e03897f3979d619254c6606d4b7d7c55c0",
    "classification": "80243d5da2ffc0f0f7a4ed1226025c724fbd6d73fab0ccd176a2d25b7c39cd56",
    "receipt": "ba070b4ab0cd1498e2a83e35997249bf1d5cc96f21e90ce3793135220369b844",
}
P8_V2_EXECUTED_MAPPING = {
    ".codex_browser_snapshot_proshka.md": "archive/root_artifacts/browser_snapshots/.codex_browser_snapshot_proshka.md",  # P9_TYPED exact mapping
    "louise-current-tab.png": "archive/root_artifacts/browser_snapshots/louise-current-tab.png",  # P9_TYPED exact mapping
    "louise-last-response.md": "archive/root_artifacts/browser_snapshots/louise-last-response.md",  # P9_TYPED exact mapping
    "run.jsonl": "archive/root_artifacts/provenance/run.jsonl",  # P9_TYPED exact mapping
    "codex_4af2_uncommitted_20260727.patch": "archive/root_artifacts/provenance/codex_4af2_uncommitted_20260727.patch",  # P9_TYPED exact mapping
}


def validate_v2_executed_mapping(payload: dict[str, Any]) -> None:
    actual = {row.get("source"): row.get("target") for row in payload.get("executed_moves", [])}
    if actual != P8_V2_EXECUTED_MAPPING or len(payload.get("executed_moves", [])) != 5:
        raise RootArtifactError("P8_V2_EXECUTED_MAPPING_DRIFT")


def verify_v2_transition(treeish: str | None = None) -> None:
    if not all(path.is_file() for path in (CLASSIFICATION_V2, SCHEMA_V2, RECEIPT_V2, P9_RECEIPT)):
        raise RootArtifactError("P8_V2_ARTIFACT_MISSING")
    for label, path in {
        "schema": SCHEMA,
        "classification": CLASSIFICATION,
        "receipt": RECEIPT,
    }.items():
        if sha256(path.read_bytes()) != P8_V1_IMMUTABLE_HASHES[label]:
            raise RootArtifactError(f"P8_V1_IMMUTABLE_PREDECESSOR_DRIFT:{label}")
    payload = json.loads(CLASSIFICATION_V2.read_text())
    schema = json.loads(SCHEMA_V2.read_text())
    try:
        import jsonschema
    except ImportError as exc:
        raise RootArtifactError("P8_V2_JSONSCHEMA_UNAVAILABLE") from exc
    try:
        jsonschema.Draft202012Validator(schema).validate(payload)
    except jsonschema.ValidationError as exc:
        raise RootArtifactError(f"P8_V2_SCHEMA_INVALID:{exc}") from exc
    if payload.get("counts") != {
        "live_root_entries": 64,
        "keep": 49,
        "archive_pending": 15,
        "executed": 5,
    }:
        raise RootArtifactError("P8_V2_COUNT_DRIFT")
    validate_v2_executed_mapping(payload)
    v1 = json.loads(CLASSIFICATION.read_text())
    moved = {row["source"] for row in payload.get("executed_moves", [])}
    expected_entries = [row for row in v1["entries"] if row["path"] not in moved]
    if payload.get("entries") != expected_entries or len(moved) != 5:
        raise RootArtifactError("P8_V2_PREDECESSOR_TRANSITION_DRIFT")
    p9 = json.loads(P9_RECEIPT.read_text())
    candidate = p9.get("prospective_tree_excluding_receipt")
    selected = treeish
    if selected is None:
        live_paths = root_entries(CURRENT_HEAD)
        selected = CURRENT_HEAD if moved.isdisjoint(live_paths) else candidate
    if not isinstance(selected, str):
        raise RootArtifactError("P8_V2_CANDIDATE_TREE_MISSING")
    live = root_entries(selected)
    registered = {row["path"]: row for row in payload["entries"]}
    if live.keys() != registered.keys():
        raise RootArtifactError("P8_V2_LIVE_ROOT_SET_DRIFT")
    for path, row in registered.items():
        current = live[path]
        if current["object_kind"] != row["object_kind"] or current["git_mode"] != row["git_mode"]:
            raise RootArtifactError(f"P8_V2_ROOT_KIND_MODE_DRIFT:{path}")
        if row["drift_class"] in {"ARCHIVE_DEFERRED", "KEEP_PINNED"} and current["source_oid"] != row["source_oid"]:
            raise RootArtifactError(f"P8_V2_PINNED_OBJECT_DRIFT:{path}")
    for row in payload["executed_moves"]:
        if exact_tree_entry(selected, row["source"]) is not None:
            raise RootArtifactError(f"P8_V2_SOURCE_RESURRECTED:{row['source']}")
        target = exact_tree_entry(selected, row["target"])
        if target is None or target[0] != row["git_mode"] or target[2] != row["source_oid"]:
            raise RootArtifactError(f"P8_V2_TARGET_DRIFT:{row['target']}")
    receipt_v2 = json.loads(RECEIPT_V2.read_text())
    if receipt_v2.get("predecessor_hashes") != {
        "schema": P8_V1_IMMUTABLE_HASHES["schema"],
        "manifest": P8_V1_IMMUTABLE_HASHES["classification"],
        "receipt": P8_V1_IMMUTABLE_HASHES["receipt"],
    }:
        raise RootArtifactError("P8_V2_RECEIPT_PREDECESSOR_DRIFT")
    if receipt_v2.get("hashes", {}).get("manifest_v2") != sha256(CLASSIFICATION_V2.read_bytes()):
        raise RootArtifactError("P8_V2_RECEIPT_MANIFEST_HASH_DRIFT")


def run_v2_plants() -> None:
    verify_v2_transition()
    payload = json.loads(CLASSIFICATION_V2.read_text())
    poisoned = json.loads(json.dumps(payload))
    poisoned["executed_moves"][0]["target"] = "archive/wrong-target"
    try:
        validate_v2_executed_mapping(poisoned)
    except RootArtifactError as exc:
        if str(exc) != "P8_V2_EXECUTED_MAPPING_DRIFT":
            raise
    else:
        raise RootArtifactError("PLANT_MISSED:P8_V2_EXECUTED_MAPPING_DRIFT")


def exact_tree_entry(treeish: str, path: str) -> tuple[str, str, str] | None:
    raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-tree", treeish, "--", path], text=True
    ).strip()
    if not raw:
        return None
    mode, kind, oid = raw.split("\t", 1)[0].split()
    return mode, kind, oid


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_output(*args: str, text: bool = False) -> bytes | str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=text)


def live_head() -> str:
    return str(git_output("rev-parse", "HEAD", text=True)).strip()


def origin_head() -> str:
    return str(git_output("rev-parse", "origin/rh_clean", text=True)).strip()


def fetch_origin() -> None:
    subprocess.run(
        ["git", "-C", str(ROOT), "fetch", "origin", "rh_clean"],
        check=True,
        stdout=subprocess.DEVNULL,
    )


def tree_blob(treeish: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{treeish}:{path}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if result.returncode != 0:
        raise RootArtifactError(f"TREE_BLOB_MISSING:{path}")
    return result.stdout


def root_entries(treeish: str) -> dict[str, dict[str, Any]]:
    raw = bytes(git_output("ls-tree", "-z", treeish))
    entries: dict[str, dict[str, Any]] = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        meta, raw_path = item.split(b"\t", 1)
        mode, git_kind, oid = meta.decode().split()
        path = raw_path.decode("utf-8", "surrogateescape")
        object_kind = "tree" if git_kind == "tree" else "symlink" if mode == "120000" else "blob"
        row: dict[str, Any] = {
            "path": path,
            "object_kind": object_kind,
            "git_mode": mode,
            "source_oid": oid,
        }
        if object_kind != "tree":
            data = tree_blob(treeish, path)
            row.update({"sha256": sha256(data), "byte_size": len(data)})
            if object_kind == "symlink":
                row["symlink_target"] = data.decode("utf-8")
        entries[path] = row
    return entries


def archive_target(path: str) -> str:
    groups = [group for group, paths in ARCHIVE_GROUPS.items() if path in paths]
    if len(groups) != 1:
        raise RootArtifactError(f"ARCHIVE_GROUP_AMBIGUOUS:{path}:{groups}")
    return f"archive/root_artifacts/{groups[0]}/{path}"


def build_classification(source_commit: str = CURRENT_HEAD) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for path, source in sorted(root_entries(source_commit).items()):
        row = dict(source)
        if path in ARCHIVE_PATHS:
            row.update(
                {
                    "classification": "ARCHIVE",
                    "drift_class": "ARCHIVE_DEFERRED",
                    "reason": (
                        "Root artifact is noncanonical; physical archival is deferred to P9 "
                        "after a zero-reference receipt."
                    ),
                    "target": archive_target(path),
                    "zero_reference_status": "PENDING",
                }
            )
        elif source["object_kind"] == "tree":
            row.update(
                {
                    "classification": "KEEP",
                    "drift_class": "ROOT_STRUCTURE",
                    "reason": (
                        "Tracked root directory is retained as repository structure; descendant "
                        "churn does not change this classification."
                    ),
                    "zero_reference_status": "NOT_APPLICABLE",
                }
            )
        elif source["object_kind"] == "symlink":
            row.update(
                {
                    "classification": "KEEP",
                    "drift_class": "KEEP_PINNED",
                    "reason": (
                        "Canonical root compatibility link is retained with an exact pinned target."
                    ),
                    "zero_reference_status": "NOT_APPLICABLE",
                }
            )
        else:
            row.update(
                {
                    "classification": "KEEP",
                    "drift_class": "KEEP_MUTABLE",
                    "reason": (
                        "Root file remains part of the active or continuity surface; source bytes "
                        "are provenance, not a permanent content lock."
                    ),
                    "zero_reference_status": "NOT_APPLICABLE",
                }
            )
        rows.append(row)
    return {
        "schema_version": "q3.root_artifact_classification.v1",
        "source_commit": source_commit,
        "scope": "ALL_TRACKED_IMMEDIATE_ROOT_ENTRIES",
        "physical_moves_performed": False,
        "target_availability_status": "PENDING_P9_RECHECK",
        "future_session_protocol_policy": {
            "closed_root": True,
            "existing_root_action": "KEEP",
            "future_directory": "docs/session_protocols",
            "filename_regex": r"^SESSION_PROTOKOLL_[0-9]{4}-[0-9]{2}-[0-9]{2}\.md$",
        },
        "script_output_policy": {
            "status": "LITERAL_STATIC_PREFLIGHT_ONLY",
            "assurance": "NOT_A_COMPLETE_RUNTIME_PROOF",
            "runtime_root_diff_guard_required_before_P9": True,
            "typed_exceptions": [
                {
                    "path": "q3.lean.aristotle/scripts/build_docs.sh",
                    "literal": "docbuild.log",
                    "basis": "OUTPUT_AFTER_EXPLICIT_CD_TO_NONROOT_DOCBUILD_DIR",
                }
            ],
        },
        "entries": rows,
    }


def validate_schema(payload: dict[str, Any]) -> None:
    try:
        import jsonschema
    except ImportError as exc:
        raise RootArtifactError("JSONSCHEMA_UNAVAILABLE") from exc
    schema = json.loads(SCHEMA.read_text())
    try:
        jsonschema.Draft202012Validator(schema).validate(payload)
    except jsonschema.ValidationError as exc:
        raise RootArtifactError(f"ROOT_CLASSIFICATION_SCHEMA_INVALID:{exc.message}") from exc


def validate_targets(payload: dict[str, Any]) -> None:
    source = payload["source_commit"]
    source_entries = root_entries(source)
    targets: dict[str, str] = {}
    portable_targets: dict[str, str] = {}
    recursive_paths = str(
        git_output("ls-tree", "-r", "--name-only", source, text=True)
    ).splitlines()
    portable_source_paths = {
        unicodedata.normalize("NFC", item).casefold(): item for item in recursive_paths
    }
    for row in payload["entries"]:
        path = row["path"]
        classification = row["classification"]
        if classification == "IGNORE":
            raise RootArtifactError(f"TRACKED_IGNORE_FORBIDDEN:{path}")
        if classification not in {"ARCHIVE", "MOVE"}:
            if "target" in row:
                raise RootArtifactError(f"ARCHIVE_TARGET_ON_KEEP:{path}")
            continue
        target = row.get("target")
        if not isinstance(target, str):
            raise RootArtifactError(f"ARCHIVE_TARGET_MISSING:{path}")
        pure = PurePosixPath(target)
        if (
            pure.is_absolute()
            or ".." in pure.parts
            or pure.as_posix() != target
            or unicodedata.normalize("NFC", target) != target
        ):
            raise RootArtifactError(f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:{target}")
        if target in targets:
            raise RootArtifactError(
                f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:duplicate-with={targets[target]}"
            )
        portable = unicodedata.normalize("NFC", target).casefold()
        if portable in portable_targets:
            raise RootArtifactError(
                f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:portable-duplicate-with={portable_targets[portable]}"
            )
        if portable in portable_source_paths:
            raise RootArtifactError(
                f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:portable-existing={portable_source_paths[portable]}"
            )
        targets[target] = path
        portable_targets[portable] = path
        result = subprocess.run(
            ["git", "-C", str(ROOT), "cat-file", "-e", f"{source}:{target}"],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if result.returncode == 0:
            raise RootArtifactError(f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:exists")
        parts = pure.parts
        for index in range(1, len(parts)):
            ancestor = PurePosixPath(*parts[:index]).as_posix()
            entry = source_entries.get(ancestor)
            if entry is not None and entry["object_kind"] != "tree":
                raise RootArtifactError(
                    f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:ancestor-file={ancestor}"
                )
            portable_ancestor = unicodedata.normalize("NFC", ancestor).casefold()
            existing_ancestor = portable_source_paths.get(portable_ancestor)
            if existing_ancestor is not None:
                result = subprocess.run(
                    ["git", "-C", str(ROOT), "cat-file", "-t", f"{source}:{existing_ancestor}"],
                    check=False,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL,
                    text=True,
                )
                if result.returncode == 0 and result.stdout.strip() != "tree":
                    raise RootArtifactError(
                        f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:portable-ancestor-file={existing_ancestor}"
                    )
        if (
            target != archive_target(path)
            or pure.name != PurePosixPath(path).name
            or target == path
        ):
            raise RootArtifactError(f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:{target}")
        worktree_collision = portable_worktree_collision(ROOT, target)
        if worktree_collision is not None:
            raise RootArtifactError(
                f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{path}:worktree-existing={worktree_collision}"
            )
    ordered = sorted(targets)
    for index, target in enumerate(ordered):
        for other in ordered[index + 1 :]:
            if other.startswith(target + "/"):
                raise RootArtifactError(
                    f"ARCHIVE_TARGET_COLLISION_OR_ESCAPE:{targets[other]}:prefix={target}"
                )


def portable_worktree_collision(root: Path, target: str) -> str | None:
    current = root
    actual_parts: list[str] = []
    for part in PurePosixPath(target).parts:
        if not current.is_dir():
            return "/".join(actual_parts) if actual_parts else None
        wanted = unicodedata.normalize("NFC", part).casefold()
        matches = [
            child
            for child in current.iterdir()
            if unicodedata.normalize("NFC", child.name).casefold() == wanted
        ]
        if not matches:
            return None
        chosen = sorted(matches, key=lambda item: item.name)[0]
        actual_parts.append(chosen.name)
        current = chosen
    return "/".join(actual_parts)


def verify_source_snapshot(payload: dict[str, Any]) -> None:
    expected = build_classification(payload["source_commit"])
    if payload != expected:
        raise RootArtifactError("ROOT_SOURCE_SNAPSHOT_DRIFT")


def verify_live_classification(payload: dict[str, Any], treeish: str | None = None) -> None:
    treeish = CURRENT_HEAD if treeish is None else treeish
    live = root_entries(treeish)
    registered = {row["path"]: row for row in payload["entries"]}
    if live.keys() != registered.keys():
        missing = sorted(live.keys() - registered.keys())
        stale = sorted(registered.keys() - live.keys())
        forbidden_protocols = [
            path
            for path in missing
            if re.fullmatch(r"SESSION_PROTOKOLL_[0-9]{4}-[0-9]{2}-[0-9]{2}\.md", path)
        ]
        if forbidden_protocols:
            raise RootArtifactError(
                f"ROOT_SESSION_PROTOCOL_CREATION_FORBIDDEN:{forbidden_protocols}"
            )
        raise RootArtifactError(f"ROOT_ARTIFACT_UNCLASSIFIED:missing={missing}:stale={stale}")
    for path, current in live.items():
        row = registered[path]
        if current["object_kind"] != row["object_kind"] or current["git_mode"] != row["git_mode"]:
            raise RootArtifactError(f"ROOT_ARTIFACT_KIND_OR_MODE_DRIFT:{path}")
        if row["drift_class"] == "ARCHIVE_DEFERRED" and (
            current["source_oid"] != row["source_oid"]
            or current["sha256"] != row["sha256"]
            or current["byte_size"] != row["byte_size"]
        ):
            raise RootArtifactError(f"ARCHIVE_DEFERRED_BYTES_DRIFT:{path}")
        if row["drift_class"] == "KEEP_PINNED" and (
            current["source_oid"] != row["source_oid"]
            or current.get("symlink_target") != row.get("symlink_target")
        ):
            raise RootArtifactError(f"ROOT_SYMLINK_DRIFT:{path}")
    expected_links = {
        "ACTIVE": "q3.lean.aristotle/ACTIVE",
        "SESSION_ENTRY.md": "ACTIVE/SESSION_ENTRY.md",
    }
    actual_links = {
        path: row.get("symlink_target")
        for path, row in registered.items()
        if row["object_kind"] == "symlink"
    }
    if actual_links != expected_links:
        raise RootArtifactError(f"ROOT_SYMLINK_DRIFT:{actual_links}")
    for resolved in (
        "q3.lean.aristotle/ACTIVE",
        "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md",
    ):
        if subprocess.run(
            ["git", "-C", str(ROOT), "cat-file", "-e", f"{treeish}:{resolved}"],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode:
            raise RootArtifactError(f"ROOT_SYMLINK_DRIFT:broken={resolved}")
    verify_future_session_protocols(treeish)


def verify_future_session_protocols(treeish: str) -> None:
    directory = "docs/session_protocols"
    raw = bytes(git_output("ls-tree", "-r", "-z", treeish, "--", directory))
    if not raw:
        return
    if (
        subprocess.check_output(
            ["git", "-C", str(ROOT), "cat-file", "-t", f"{treeish}:{directory}"],
            text=True,
        ).strip()
        != "tree"
    ):
        raise RootArtifactError("FUTURE_SESSION_PROTOCOL_POLICY_DRIFT:not-directory")
    prefix = directory + "/"
    for item in raw.split(b"\0"):
        if not item:
            continue
        meta, raw_path = item.split(b"\t", 1)
        mode, kind, _oid = meta.decode().split()
        path = raw_path.decode("utf-8", "surrogateescape")
        relative = path.removeprefix(prefix)
        if (
            "/" in relative
            or kind != "blob"
            or mode != "100644"
            or re.fullmatch(r"SESSION_PROTOKOLL_[0-9]{4}-[0-9]{2}-[0-9]{2}\.md", relative) is None
        ):
            raise RootArtifactError(f"FUTURE_SESSION_PROTOCOL_POLICY_DRIFT:{path}:{mode}:{kind}")


def script_root_output_hits(treeish: str, path: str, data: bytes) -> list[str]:
    if not (path.endswith(".py") or path.endswith(".sh")):
        return []
    if path.startswith("archive/") or "/archive/" in path:
        return []
    if path.startswith("orchestrator/tests/") or "/tests/" in path:
        return []
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return []
    hits: list[str] = []
    if path.endswith(".py"):
        for pattern in PYTHON_ROOT_OUTPUT_PATTERNS:
            hits.extend(match.group(1) for match in pattern.finditer(text))
    else:
        hits.extend(match.group(1) for match in SHELL_TEE_PATTERN.finditer(text))
    return sorted(output for output in hits if (path, output) not in SCRIPT_OUTPUT_EXCEPTIONS)


def verify_script_outputs(treeish: str | None = None) -> None:
    treeish = CURRENT_HEAD if treeish is None else treeish
    paths = str(git_output("ls-tree", "-r", "--name-only", treeish, text=True)).splitlines()
    violations: list[str] = []
    for path in paths:
        if not (path.endswith(".py") or path.endswith(".sh")):
            continue
        for output in script_root_output_hits(treeish, path, tree_blob(treeish, path)):
            violations.append(f"{path}:{output}")
    if violations:
        raise RootArtifactError(f"LITERAL_SCRIPT_ROOT_OUTPUT_PREFLIGHT:{violations}")
    verify_docbuild_exception(tree_blob(treeish, "q3.lean.aristotle/scripts/build_docs.sh"))


def verify_docbuild_exception(data: bytes) -> None:
    lines = data.decode("utf-8").splitlines()
    cd_positions = [
        index for index, line in enumerate(lines) if line.strip() == 'cd "$DOCBUILD_DIR"'
    ]
    tee_positions = [index for index, line in enumerate(lines) if "tee docbuild.log" in line]
    if len(cd_positions) != 1 or len(tee_positions) != 1:
        raise RootArtifactError("LITERAL_SCRIPT_OUTPUT_EXCEPTION_DRIFT:docbuild.log")
    cd_index = cd_positions[0]
    tee_index = tee_positions[0]
    intervening_cd = any(line.strip().startswith("cd ") for line in lines[cd_index + 1 : tee_index])
    if cd_index >= tee_index or intervening_cd:
        raise RootArtifactError("LITERAL_SCRIPT_OUTPUT_EXCEPTION_DRIFT:docbuild.log")


def verify(payload: dict[str, Any], treeish: str | None = None) -> None:
    treeish = CURRENT_HEAD if treeish is None else treeish
    validate_schema(payload)
    if len(payload["entries"]) != 69:
        raise RootArtifactError(f"ROOT_ARTIFACT_COUNT_DRIFT:{len(payload['entries'])}")
    paths = [row["path"] for row in payload["entries"]]
    if len(paths) != len(set(paths)):
        raise RootArtifactError("ROOT_ARTIFACT_DUPLICATE_PATH")
    counts = {
        "KEEP": sum(row["classification"] == "KEEP" for row in payload["entries"]),
        "ARCHIVE": sum(row["classification"] == "ARCHIVE" for row in payload["entries"]),
        "MOVE": sum(row["classification"] == "MOVE" for row in payload["entries"]),
        "IGNORE": sum(row["classification"] == "IGNORE" for row in payload["entries"]),
    }
    if counts != {"KEEP": 49, "ARCHIVE": 20, "MOVE": 0, "IGNORE": 0}:
        raise RootArtifactError(f"ROOT_CLASSIFICATION_COUNT_DRIFT:{counts}")
    verify_source_snapshot(payload)
    validate_targets(payload)
    verify_live_classification(payload, treeish)
    verify_script_outputs(treeish)
    check_wrapper()
    check_staged_scope()


def check_wrapper() -> None:
    if not WRAPPER.exists():
        raise RootArtifactError("ROOT_WRAPPER_MISSING")
    if not os.access(WRAPPER, os.X_OK):
        raise RootArtifactError("ROOT_WRAPPER_NOT_EXECUTABLE")


def prospective_tree() -> str:
    with tempfile.TemporaryDirectory() as td:
        index = Path(td) / "index"
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(index)
        subprocess.run(["git", "-C", str(ROOT), "read-tree", CURRENT_HEAD], env=env, check=True)
        subprocess.run(
            ["git", "-C", str(ROOT), "add", "--", *sorted(P8_CANDIDATE_PATHS)],
            env=env,
            check=True,
        )
        return str(
            subprocess.check_output(["git", "-C", str(ROOT), "write-tree"], env=env, text=True)
        ).strip()


def check_staged_scope(index: Path | None = None) -> None:
    env = os.environ.copy()
    if index is not None:
        env["GIT_INDEX_FILE"] = str(index)
    raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "diff", "--cached", "--name-only", "-z", live_head(), "--"],
        env=env,
    )
    staged = {item.decode("utf-8", "surrogateescape") for item in raw.split(b"\0") if item}
    outside = sorted(staged - P8_ALLOWED_PATHS)
    if outside:
        raise RootArtifactError(f"FOREIGN_DIRTY_PATH_MUTATION:staged={outside}")


def file_fingerprint(path: str) -> dict[str, Any]:
    full = ROOT / path
    if not full.exists() and not full.is_symlink():
        return {"path": path, "kind": "deleted"}
    mode = stat.S_IMODE(full.lstat().st_mode)
    if full.is_symlink():
        data = os.readlink(full).encode()
        kind = "symlink"
    elif full.is_dir():
        return {"path": path, "kind": "directory", "mode": mode}
    else:
        data = full.read_bytes()
        kind = "file"
    return {
        "path": path,
        "kind": kind,
        "mode": mode,
        "sha256": sha256(data),
        "byte_size": len(data),
    }


def foreign_dirty_snapshot() -> list[dict[str, Any]]:
    tracked_raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "diff", "--name-only", "-z", "HEAD", "--"]
    )
    untracked_raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--others", "--exclude-standard", "-z"]
    )
    paths = {
        item.decode("utf-8", "surrogateescape")
        for raw in (tracked_raw, untracked_raw)
        for item in raw.split(b"\0")
        if item
    } - P8_ALLOWED_PATHS
    return [file_fingerprint(path) for path in sorted(paths)]


def verify_foreign_dirty_snapshot(
    expected: list[dict[str, Any]], actual: list[dict[str, Any]]
) -> None:
    if expected != actual:
        raise RootArtifactError("FOREIGN_DIRTY_PATH_MUTATION")


def receipt(payload: dict[str, Any], provenance: dict[str, Any] | None = None) -> dict[str, Any]:
    source = CURRENT_HEAD if provenance is None else provenance["source_commit"]
    candidate = (
        prospective_tree()
        if provenance is None
        else provenance["prospective_tree_excluding_receipt"]
    )
    foreign = (
        foreign_dirty_snapshot() if provenance is None else provenance["foreign_dirty_snapshot"]
    )
    return {
        "schema_version": "q3.root_artifact_classification_receipt.v1",
        "status": "PASS",
        "source_commit": source,
        "prospective_tree_excluding_receipt": candidate,
        "root_entry_count": len(payload["entries"]),
        "keep_count": sum(row["classification"] == "KEEP" for row in payload["entries"]),
        "archive_count": sum(row["classification"] == "ARCHIVE" for row in payload["entries"]),
        "move_count": sum(row["classification"] == "MOVE" for row in payload["entries"]),
        "ignore_count": sum(row["classification"] == "IGNORE" for row in payload["entries"]),
        "foreign_dirty_snapshot": foreign,
        "hashes": {
            "classification": sha256(CLASSIFICATION.read_bytes()),
            "schema": sha256(SCHEMA.read_bytes()),
            "checker": sha256(Path(__file__).read_bytes()),
            "tests": sha256(TESTS.read_bytes()),
            "wrapper": sha256(WRAPPER.read_bytes()),
        },
        "plants": [
            "ROOT_ARTIFACT_UNCLASSIFIED",
            "TRACKED_IGNORE_FORBIDDEN",
            "ARCHIVE_TARGET_COLLISION_OR_ESCAPE",
            "LITERAL_SCRIPT_ROOT_OUTPUT_PREFLIGHT",
            "ROOT_SYMLINK_DRIFT",
            "FOREIGN_DIRTY_PATH_MUTATION",
        ],
        "script_output_gate_scope": "LITERAL_STATIC_PREFLIGHT_ONLY",
        "script_output_assurance": "NOT_A_COMPLETE_RUNTIME_PROOF",
    }


def verify_candidate_tree(receipt_payload: dict[str, Any]) -> None:
    source = receipt_payload["source_commit"]
    tree = receipt_payload["prospective_tree_excluding_receipt"]
    changed_raw = bytes(git_output("diff", "--name-only", "-z", source, tree, "--"))
    changed = {item.decode("utf-8", "surrogateescape") for item in changed_raw.split(b"\0") if item}
    if changed != P8_CANDIDATE_PATHS:
        raise RootArtifactError(f"P8_CANDIDATE_SCOPE_DRIFT:{sorted(changed)}")
    hash_paths = {
        "classification": str(CLASSIFICATION.relative_to(ROOT)),
        "schema": str(SCHEMA.relative_to(ROOT)),
        "checker": str(Path(__file__).relative_to(ROOT)),
        "tests": str(TESTS.relative_to(ROOT)),
        "wrapper": str(WRAPPER.relative_to(ROOT)),
    }
    if set(receipt_payload.get("hashes", {})) != set(hash_paths):
        raise RootArtifactError("P8_RECEIPT_HASH_SET_DRIFT")
    for label, path in hash_paths.items():
        if receipt_payload["hashes"][label] != sha256(tree_blob(tree, path)):
            raise RootArtifactError(f"P8_CANDIDATE_HASH_DRIFT:{label}")
    source_root = root_entries(source)
    candidate_root = root_entries(tree)
    source_semantics = {
        path: (row["object_kind"], row["git_mode"]) for path, row in source_root.items()
    }
    candidate_semantics = {
        path: (row["object_kind"], row["git_mode"]) for path, row in candidate_root.items()
    }
    if source_semantics != candidate_semantics:
        raise RootArtifactError("P8_CANDIDATE_ROOT_SEMANTIC_DIFF")
    verify_future_session_protocols(tree)
    verify_script_outputs(tree)


def verify_receipt_provenance(
    receipt_payload: dict[str, Any],
    classification_payload: dict[str, Any],
    head: str | None = None,
) -> None:
    source = receipt_payload.get("source_commit")
    tree = receipt_payload.get("prospective_tree_excluding_receipt")
    if not isinstance(source, str) or not isinstance(tree, str):
        raise RootArtifactError("P8_RECEIPT_PROVENANCE_MISSING")
    if source != classification_payload.get("source_commit"):
        raise RootArtifactError("P8_RECEIPT_CLASSIFICATION_SOURCE_CROSS")
    for object_name, suffix in ((source, "^{commit}"), (tree, "^{tree}")):
        result = subprocess.run(
            ["git", "-C", str(ROOT), "cat-file", "-e", object_name + suffix],
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if result.returncode != 0:
            raise RootArtifactError("P8_RECEIPT_PROVENANCE_OBJECT_MISSING")
    current = live_head() if head is None else head
    if subprocess.run(
        ["git", "-C", str(ROOT), "merge-base", "--is-ancestor", source, current],
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ).returncode:
        raise RootArtifactError("P8_SOURCE_NOT_ANCESTOR")
    verify_candidate_tree(receipt_payload)
    stored_classification = json.loads(tree_blob(tree, str(CLASSIFICATION.relative_to(ROOT))))
    if stored_classification.get("source_commit") != source:
        raise RootArtifactError("P8_CANDIDATE_CLASSIFICATION_SOURCE_CROSS")


def p8_dirty() -> bool:
    raw = subprocess.check_output(
        ["git", "-C", str(ROOT), "status", "--porcelain=v1", "-z", "--", *sorted(P8_ALLOWED_PATHS)]
    )
    return bool(raw)


def verify_precommit(receipt_payload: dict[str, Any]) -> None:
    if not p8_dirty():
        return
    if receipt_payload["source_commit"] != CURRENT_HEAD:
        raise RootArtifactError("P8_PRECOMMIT_SOURCE_STALE")
    if receipt_payload["prospective_tree_excluding_receipt"] != prospective_tree():
        raise RootArtifactError("P8_PRECOMMIT_TREE_STALE")
    verify_foreign_dirty_snapshot(
        receipt_payload["foreign_dirty_snapshot"], foreign_dirty_snapshot()
    )


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


def build_or_verify() -> None:
    if CLASSIFICATION.exists():
        payload = json.loads(CLASSIFICATION.read_text())
        verify(payload)
        if not RECEIPT.exists():
            raise RootArtifactError("ROOT_ARTIFACT_RECEIPT_MISSING")
        actual_receipt = json.loads(RECEIPT.read_text())
        verify_receipt_provenance(actual_receipt, payload)
        verify_precommit(actual_receipt)
        if actual_receipt != receipt(payload, actual_receipt):
            raise RootArtifactError("ROOT_ARTIFACT_RECEIPT_DRIFT")
        return
    payload = build_classification()
    validate_schema(payload)
    verify(payload)
    write_json(CLASSIFICATION, payload)
    write_json(RECEIPT, receipt(payload))


def semantic_contract(payload: dict[str, Any]) -> dict[str, Any]:
    ignored_row_fields = {"source_oid", "sha256", "byte_size"}
    return {
        key: value for key, value in payload.items() if key not in {"source_commit", "entries"}
    } | {
        "entries": [
            {key: value for key, value in row.items() if key not in ignored_row_fields}
            for row in payload["entries"]
        ]
    }


def freeze(payload: dict[str, Any]) -> None:
    fetch_origin()
    if live_head() != CURRENT_HEAD or origin_head() != CURRENT_HEAD:
        raise RootArtifactError("P8_FREEZE_HEAD_ORIGIN_DRIFT")
    verify(payload)
    refreshed = build_classification(CURRENT_HEAD)
    validate_schema(refreshed)
    if semantic_contract(payload) != semantic_contract(refreshed):
        raise RootArtifactError("P8_FREEZE_SEMANTIC_REBASE_FORBIDDEN")
    write_json(CLASSIFICATION, refreshed)
    frozen = receipt(
        refreshed,
        {
            "source_commit": CURRENT_HEAD,
            "prospective_tree_excluding_receipt": prospective_tree(),
            "foreign_dirty_snapshot": foreign_dirty_snapshot(),
        },
    )
    write_json(RECEIPT, frozen)
    fetch_origin()
    post = live_head()
    if post != CURRENT_HEAD or origin_head() != CURRENT_HEAD:
        raise RootArtifactError("P8_FREEZE_HEAD_ORIGIN_DRIFT")
    verify(refreshed)
    verify_receipt_provenance(frozen, refreshed, head=post)
    verify_precommit(frozen)


def run_plants() -> None:
    payload = json.loads(CLASSIFICATION.read_text())
    omitted = json.loads(json.dumps(payload))
    omitted["entries"] = omitted["entries"][1:]
    try:
        verify_live_classification(omitted)
    except RootArtifactError as exc:
        if not str(exc).startswith("ROOT_ARTIFACT_UNCLASSIFIED"):
            raise
    else:
        raise RootArtifactError("PLANT_MISSED:ROOT_ARTIFACT_UNCLASSIFIED")
    ignored = json.loads(json.dumps(payload))
    row = next(row for row in ignored["entries"] if row["classification"] == "KEEP")
    row["classification"] = "IGNORE"
    try:
        validate_targets(ignored)
    except RootArtifactError as exc:
        if not str(exc).startswith("TRACKED_IGNORE_FORBIDDEN"):
            raise
    else:
        raise RootArtifactError("PLANT_MISSED:TRACKED_IGNORE_FORBIDDEN")
    escaped = json.loads(json.dumps(payload))
    row = next(row for row in escaped["entries"] if row["classification"] == "ARCHIVE")
    row["target"] = "../outside/" + row["path"]
    try:
        validate_targets(escaped)
    except RootArtifactError as exc:
        if not str(exc).startswith("ARCHIVE_TARGET_COLLISION_OR_ESCAPE"):
            raise
    else:
        raise RootArtifactError("PLANT_MISSED:ARCHIVE_TARGET_COLLISION_OR_ESCAPE")
    if not script_root_output_hits(
        CURRENT_HEAD,
        "scripts/plant.py",
        b'from pathlib import Path\nPath("root-' + b'output.json").write_text("x")\n',
    ):
        raise RootArtifactError("PLANT_MISSED:LITERAL_SCRIPT_ROOT_OUTPUT_PREFLIGHT")
    links = json.loads(json.dumps(payload))
    row = next(row for row in links["entries"] if row["path"] == "ACTIVE")
    row["symlink_target"] = "wrong-target"
    try:
        verify_live_classification(links)
    except RootArtifactError as exc:
        if not str(exc).startswith("ROOT_SYMLINK_DRIFT"):
            raise
    else:
        raise RootArtifactError("PLANT_MISSED:ROOT_SYMLINK_DRIFT")
    expected = foreign_dirty_snapshot()
    mutated = json.loads(json.dumps(expected))
    if mutated:
        mutated[0]["sha256"] = "0" * 64
    else:
        mutated.append({"path": "foreign", "kind": "file", "sha256": "0" * 64, "byte_size": 0})
    try:
        verify_foreign_dirty_snapshot(expected, mutated)
    except RootArtifactError as exc:
        if str(exc) != "FOREIGN_DIRTY_PATH_MUTATION":
            raise
    else:
        raise RootArtifactError("PLANT_MISSED:FOREIGN_DIRTY_PATH_MUTATION")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("build", "check", "plants", "freeze-provenance"))
    args = parser.parse_args()
    try:
        if args.command == "build":
            if CLASSIFICATION_V2.exists():
                verify_v2_transition()
            else:
                build_or_verify()
            print("ROOT_ARTIFACT_CLASSIFICATION_BUILD_PASS")
        elif args.command == "check":
            if CLASSIFICATION_V2.exists():
                verify_v2_transition()
            else:
                payload = json.loads(CLASSIFICATION.read_text())
                verify(payload)
                actual_receipt = json.loads(RECEIPT.read_text())
                verify_receipt_provenance(actual_receipt, payload)
                verify_precommit(actual_receipt)
                if actual_receipt != receipt(payload, actual_receipt):
                    raise RootArtifactError("ROOT_ARTIFACT_RECEIPT_DRIFT")
            print("ROOT_ARTIFACT_CLASSIFICATION_CHECK_PASS")
        elif args.command == "plants":
            if CLASSIFICATION_V2.exists():
                run_v2_plants()
            else:
                run_plants()
            print("ROOT_ARTIFACT_CLASSIFICATION_PLANTS_PASS")
        else:
            if CLASSIFICATION_V2.exists():
                raise RootArtifactError("P8_V1_FREEZE_FORBIDDEN_AFTER_V2")
            payload = json.loads(CLASSIFICATION.read_text())
            freeze(payload)
            print("ROOT_ARTIFACT_CLASSIFICATION_FREEZE_PASS")
    except (OSError, json.JSONDecodeError, RootArtifactError) as exc:
        print(f"ROOT_ARTIFACT_CLASSIFICATION_FAIL:{exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
