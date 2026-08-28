#!/usr/bin/env python3
"""P9 exact post-move archive transaction and falsifiable evidence checker.

The checker is deliberately tree-based.  It reconstructs the candidate from a
receipt-pinned commit and pinned blob objects; it never treats the current
worktree as the proof object.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import stat
import subprocess
import tempfile
import unicodedata
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
BASELINE_COMMIT = "1c5988c3d97c46c1cb97bdb8a7019fd52a429c1f"

SCHEMA = ROOT / "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_SCHEMA_v1.json"
RECEIPT = ROOT / "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_RECEIPT_v1.json"
TESTS = ROOT / "orchestrator/tests/test_root_archive_moves.py"
WRAPPER = ROOT / "scripts/check_root_archive_preflight.sh"
CHECKER = Path(__file__).resolve()
UMBRELLA = ROOT / "docs/semantic_quarantine/ROOT_ARCHIVE_EXECUTION_UMBRELLA_v1.json"

P8_V1_SCHEMA = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_SCHEMA_v1.json"
P8_V1_MANIFEST = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_v1.json"
P8_V1_RECEIPT = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_RECEIPT_v1.json"
P8_V2_SCHEMA = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_SCHEMA_v2.json"
P8_V2_MANIFEST = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_v2.json"
P8_V2_RECEIPT = ROOT / "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_RECEIPT_v2.json"
P8_CHECKER = ROOT / "orchestrator/root_artifact_classification.py"
P8_TESTS = ROOT / "orchestrator/tests/test_root_artifact_classification.py"

P7_V1_MANIFEST = ROOT / "docs/semantic_quarantine/PORTABILITY_MANIFEST_v1.json"
P7_V1_RECEIPT = ROOT / "docs/semantic_quarantine/PORTABILITY_RECEIPT_v1.json"
P7_SUCCESSOR_SCHEMA = (
    ROOT / "docs/semantic_quarantine/PORTABILITY_RELOCATION_SUCCESSOR_SCHEMA_v1.json"
)
P7_SUCCESSOR = ROOT / "docs/semantic_quarantine/PORTABILITY_RELOCATION_SUCCESSOR_v1.json"
P7_SUCCESSOR_RECEIPT = (
    ROOT / "docs/semantic_quarantine/PORTABILITY_RELOCATION_SUCCESSOR_RECEIPT_v1.json"
)
P7_CHECKER = ROOT / "orchestrator/portability_manifest.py"
P7_TESTS = ROOT / "orchestrator/tests/test_portability_manifest.py"

COHORT = {
    ".codex_browser_snapshot_proshka.md": (
        "archive/root_artifacts/browser_snapshots/.codex_browser_snapshot_proshka.md"
    ),
    "louise-current-tab.png": "archive/root_artifacts/browser_snapshots/louise-current-tab.png",
    "louise-last-response.md": "archive/root_artifacts/browser_snapshots/louise-last-response.md",
    "run.jsonl": "archive/root_artifacts/provenance/run.jsonl",
    "codex_4af2_uncommitted_20260727.patch": (
        "archive/root_artifacts/provenance/codex_4af2_uncommitted_20260727.patch"
    ),
}

SUPPORT_PATHS = frozenset(
    {
        str(path.relative_to(ROOT))
        for path in (
            SCHEMA,
            CHECKER,
            TESTS,
            WRAPPER,
            P8_V2_SCHEMA,
            P8_V2_MANIFEST,
            P8_V2_RECEIPT,
            P8_CHECKER,
            P8_TESTS,
            P7_SUCCESSOR_SCHEMA,
            P7_SUCCESSOR,
            P7_SUCCESSOR_RECEIPT,
            P7_CHECKER,
            P7_TESTS,
        )
    }
)
TRANSACTION_PATHS = (
    SUPPORT_PATHS
    | frozenset({str(RECEIPT.relative_to(ROOT)), str(UMBRELLA.relative_to(ROOT))})
    | frozenset(COHORT)
    | frozenset(COHORT.values())
)
CANDIDATE_PATHS = SUPPORT_PATHS | frozenset(COHORT) | frozenset(COHORT.values())

SOURCE_TOKENS = tuple(COHORT)
P8_V1_HASHES = {
    "schema": "69ee67954fc0292f174aeacd722fe5e03897f3979d619254c6606d4b7d7c55c0",
    "manifest": "80243d5da2ffc0f0f7a4ed1226025c724fbd6d73fab0ccd176a2d25b7c39cd56",
    "receipt": "ba070b4ab0cd1498e2a83e35997249bf1d5cc96f21e90ce3793135220369b844",
}
P7_V1_HASHES = {
    "manifest": "a1ed7662a59fe95a48c1efe2a0199f7645e0d49f63f850713e25ae7d5bc9bd9f",
    "receipt": "c5f8af3e895bfd8019f2cd9e6c1c6e550ac795b3561feb11f12c9ca7496c38ec",
}
PLANT_IDS = [
    "EXECUTABLE_CONTROL_REFERENCE",
    "WHOLE_FILE_EXCLUSION",
    "RAW_BINARY_REFERENCE",
    "PYTHON_STEM_IMPORT",
    "GENERATED_INDEX_REFERENCE",
    "ROOT_GLOB_OR_ENUMERATION",
    "DESTINATION_BYTE_OR_MODE_DRIFT",
    "SOURCE_SYMLINK_OR_STUB_RESURRECTION",
    "CASEFOLD_OR_NFC_COLLISION",
    "FOREIGN_DIRTY_DRIFT",
    "HISTORY_ONLY_REFERENCE_NONBLOCK",
    "TYPED_SELF_REFERENCE_NONBLOCK",
    "P7_PROVENANCE_PRESERVATION",
]
EVOLUTION_CONTRACT = {
    "p7": "TYPED_RELOCATION_SUCCESSOR_PRESERVES_V1_ROW_AND_SHA256",
    "p8": "V1_IMMUTABLE_PREDECESSOR_PLUS_V2_64_LIVE_5_EXECUTED",
    "p5": "NO_REGENERATION_REQUIRED_NO_DIRECT_COHORT_DEPENDENCY",
}
SCOPED_SELECTOR_LINE_HASHES = {
    ("docs/cartographer/comparator/fit.py", "a94a728f0bb70b96c4ae59b88fdc363a4a29918ab7275a87117f2e580614335f"),
    ("docs/cartographer/comparator/port_matcher.py", "4f866d9160cdcb85096695326cb6c607cf9d1b486b79420022c5755e6febfb22"),
    ("q3.lean.aristotle/monitor_server.py", "aa4bc1aaf693c83a0868cd257d200b3bc8e993e195a22e462035b557bfeb82fc"),
    ("q3.lean.aristotle/scripts/ingest_incoming_notes.py", "83fe1c5165229926b2f5ea5fc92bedd2ae7e474080b91864d48d30d172439b7e"),
    ("q3.lean.aristotle/scripts/ingest_incoming_notes.py", "2804d0b27eb1e43555f0c89700c4b09f5d52a29d6b354598f37b8f83a3370052"),
    ("q3.lean.aristotle/scripts/ingest_incoming_notes.py", "36d2be22b14babc80ac5d7bbc5ad17159c5f14a3a909055c91d66fd06333d01c"),
}


class ArchiveMoveError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str, input_data: bytes | None = None, env: dict[str, str] | None = None) -> bytes:
    return subprocess.check_output(
        ["git", "-C", str(ROOT), *args], input=input_data, env=env
    )


def live_head() -> str:
    return git("rev-parse", "HEAD").decode().strip()


def tree_entry(treeish: str, path: str) -> tuple[str, str, str] | None:
    raw = git("ls-tree", treeish, "--", path).decode().strip()
    if not raw:
        return None
    meta = raw.split("\t", 1)[0]
    mode, kind, oid = meta.split()
    return mode, kind, oid


def tree_blob(treeish: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{treeish}:{path}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    if result.returncode:
        raise ArchiveMoveError(f"P9_TREE_BLOB_MISSING:{treeish}:{path}")
    return result.stdout


def all_tree_entries(treeish: str) -> list[tuple[str, str, str, str]]:
    rows: list[tuple[str, str, str, str]] = []
    for item in git("ls-tree", "-r", "-z", treeish).split(b"\0"):
        if not item:
            continue
        meta, raw_path = item.split(b"\t", 1)
        mode, kind, oid = meta.decode().split()
        rows.append((mode, kind, oid, raw_path.decode("utf-8", "surrogateescape")))
    return rows


def all_blob_bytes(
    treeish: str, path_predicate: Any | None = None
) -> Iterable[tuple[str, str, bytes]]:
    oid_paths: dict[str, list[str]] = {}
    for _mode, kind, oid, path in all_tree_entries(treeish):
        if kind == "blob" and (path_predicate is None or path_predicate(path)):
            oid_paths.setdefault(oid, []).append(path)
    rows = [(paths, oid) for oid, paths in oid_paths.items()]
    for begin in range(0, len(rows), 64):
        chunk = rows[begin : begin + 64]
        result = subprocess.run(
            ["git", "-C", str(ROOT), "cat-file", "--batch"],
            input=b"".join((oid + "\n").encode() for _paths, oid in chunk),
            stdout=subprocess.PIPE,
            check=True,
        )
        output = result.stdout
        cursor = 0
        for paths, expected_oid in chunk:
            path = paths[0]
            end = output.find(b"\n", cursor)
            if end < 0:
                raise ArchiveMoveError(f"P9_RAW_BLOB_SCAN_PROTOCOL:{path}:missing-header")
            header = output[cursor:end].decode()
            oid, kind, raw_size = header.split()
            if oid != expected_oid or kind != "blob":
                raise ArchiveMoveError(f"P9_RAW_BLOB_SCAN_PROTOCOL:{path}:{header}")
            size = int(raw_size)
            start = end + 1
            data = output[start : start + size]
            cursor = start + size
            if output[cursor : cursor + 1] != b"\n" or len(data) != size:
                raise ArchiveMoveError(f"P9_RAW_BLOB_SCAN_TRUNCATED:{path}")
            cursor += 1
            for candidate_path in paths:
                yield candidate_path, oid, data
        if cursor != len(output):
            raise ArchiveMoveError("P9_RAW_BLOB_SCAN_TRAILING_BYTES")


def file_object(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    mode = "100755" if os.access(path, os.X_OK) else "100644"
    oid = git("hash-object", "-w", "--stdin", input_data=data).decode().strip()
    return {"mode": mode, "oid": oid, "sha256": sha256(data), "byte_size": len(data)}


def baseline_move_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for source, target in sorted(COHORT.items()):
        entry = tree_entry(BASELINE_COMMIT, source)
        if entry is None:
            raise ArchiveMoveError(f"P9_BASELINE_SOURCE_MISSING:{source}")
        mode, kind, oid = entry
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise ArchiveMoveError(f"P9_BASELINE_SOURCE_KIND:{source}:{mode}:{kind}")
        data = tree_blob(BASELINE_COMMIT, source)
        rows.append(
            {
                "source": source,
                "target": target,
                "git_mode": mode,
                "source_oid": oid,
                "target_oid": oid,
                "sha256": sha256(data),
                "byte_size": len(data),
                "status": "EXECUTED",
                "zero_reference_status": (
                    "ZERO_ACTIVE_CONSUMERS_WITH_CONTROL_PLANE_MIGRATION_REFS"
                ),
            }
        )
    return rows


def canonical_json(payload: Any) -> bytes:
    return (json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def write_json(path: Path, payload: Any) -> None:
    path.write_bytes(canonical_json(payload))


def immutable_hashes(paths: dict[str, Path], expected: dict[str, str], code: str) -> None:
    for label, path in paths.items():
        actual = sha256(path.read_bytes())
        if actual != expected[label]:
            raise ArchiveMoveError(f"{code}:{label}:{actual}")


def build_p8_v2() -> tuple[dict[str, Any], dict[str, Any]]:
    v1 = json.loads(P8_V1_MANIFEST.read_text())
    remaining = [row for row in v1["entries"] if row["path"] not in COHORT]
    if len(remaining) != 64:
        raise ArchiveMoveError(f"P8_V2_ROOT_COUNT:{len(remaining)}")
    pending = [row for row in remaining if row["classification"] == "ARCHIVE"]
    keep = [row for row in remaining if row["classification"] == "KEEP"]
    moves = baseline_move_rows()
    payload = {
        "schema_version": "q3.root_artifact_classification.v2",
        "status": "P9_EXECUTED_TRANSITION",
        "predecessor": {
            "schema_version": "q3.root_artifact_classification.v1",
            "source_commit": v1["source_commit"],
            "hashes": P8_V1_HASHES,
        },
        "baseline_commit": BASELINE_COMMIT,
        "scope": "ALL_TRACKED_IMMEDIATE_ROOT_ENTRIES_PLUS_EXECUTED_LEDGER",
        "physical_moves_performed": True,
        "counts": {"live_root_entries": 64, "keep": 49, "archive_pending": 15, "executed": 5},
        "future_session_protocol_policy": v1["future_session_protocol_policy"],
        "script_output_policy": v1["script_output_policy"] | {
            "runtime_root_diff_guard_required_before_P9": False
        },
        "entries": remaining,
        "executed_moves": moves,
    }
    receipt = {
        "schema_version": "q3.root_artifact_classification_receipt.v2",
        "status": "PASS",
        "baseline_commit": BASELINE_COMMIT,
        "predecessor_hashes": P8_V1_HASHES,
        "hashes": {
            "schema_v2": sha256(P8_V2_SCHEMA.read_bytes()),
            "manifest_v2": sha256(canonical_json(payload)),
            "p9_schema": sha256(SCHEMA.read_bytes()),
            "p9_checker": sha256(Path(__file__).read_bytes()),
            "p9_tests": sha256(TESTS.read_bytes()),
            "p9_wrapper": sha256(WRAPPER.read_bytes()),
        },
        "counts": payload["counts"],
    }
    return payload, receipt


def build_p7_successor() -> tuple[dict[str, Any], dict[str, Any]]:
    p7 = json.loads(P7_V1_MANIFEST.read_text())
    original = next(
        row
        for row in p7["historical_hits"]
        if row["path"] == ".codex_browser_snapshot_proshka.md"
    )
    target = COHORT[original["path"]]
    relocated = dict(original)
    relocated["path"] = target
    relocated["classification_basis"] = "P7_V1_EXACT_HASH_RELOCATED_BY_P9"
    payload = {
        "schema_version": "q3.portability_relocation_successor.v1",
        "status": "TYPED_RELOCATION_SUCCESSOR",
        "baseline_commit": BASELINE_COMMIT,
        "predecessor": {
            "schema_version": p7["schema_version"],
            "hashes": P7_V1_HASHES,
        },
        "relocations": [
            {
                "source": original["path"],
                "target": target,
                "original_row": original,
                "successor_row": relocated,
                "blob_sha256_preserved": True,
            }
        ],
    }
    receipt = {
        "schema_version": "q3.portability_relocation_successor_receipt.v1",
        "status": "PASS",
        "baseline_commit": BASELINE_COMMIT,
        "predecessor_hashes": P7_V1_HASHES,
        "hashes": {
            "schema": sha256(P7_SUCCESSOR_SCHEMA.read_bytes()),
            "successor": sha256(canonical_json(payload)),
        },
        "relocation_count": 1,
    }
    return payload, receipt


def support_objects() -> dict[str, dict[str, Any]]:
    missing = [path for path in SUPPORT_PATHS if not (ROOT / path).is_file()]
    if missing:
        raise ArchiveMoveError(f"P9_SUPPORT_PATH_MISSING:{sorted(missing)}")
    return {path: file_object(ROOT / path) for path in sorted(SUPPORT_PATHS)}


def prospective_tree(objects: dict[str, dict[str, Any]]) -> str:
    with tempfile.TemporaryDirectory() as td:
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(Path(td) / "index")
        subprocess.run(
            ["git", "-C", str(ROOT), "read-tree", BASELINE_COMMIT], env=env, check=True
        )
        for source, target in sorted(COHORT.items()):
            subprocess.run(
                ["git", "-C", str(ROOT), "update-index", "--force-remove", "--", source],
                env=env,
                check=True,
            )
            mode, _kind, oid = tree_entry(BASELINE_COMMIT, source) or ("", "", "")
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(ROOT),
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    mode,
                    oid,
                    target,
                ],
                env=env,
                check=True,
            )
        for path, row in sorted(objects.items()):
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(ROOT),
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    row["mode"],
                    row["oid"],
                    path,
                ],
                env=env,
                check=True,
            )
        return git("write-tree", env=env).decode().strip()


def portable_key(path: str) -> str:
    return "/".join(unicodedata.normalize("NFC", part).casefold() for part in path.split("/"))


def reference_variants(token: str) -> list[tuple[str, bytes]]:
    rows: list[tuple[str, bytes]] = [("EXACT", token.encode())]
    folded = token.casefold()
    if folded != token:
        rows.append(("CASEFOLD", folded.encode()))
    decomposed = unicodedata.normalize("NFD", token)
    if decomposed != token:
        rows.append(("NFD", decomposed.encode()))
    encoded = "".join(
        character if character.isalnum() or character in "_-~" else f"%{ord(character):02X}"
        for character in token
    )
    rows.append(("URL_ENCODED", encoded.encode()))
    rows.append(("CASE_VARIANT", token.upper().encode()))
    stem = PurePosixPath(token).stem.lstrip(".")
    module = re.sub(r"[^A-Za-z0-9]+", "_", stem).strip("_")
    if len(module) >= 12:
        rows.append(("PYTHON_STEM", module.encode()))
        rows.append(("LEAN_MODULE", module.replace("_", ".").encode()))
    unique: dict[bytes, str] = {}
    for kind, needle in rows:
        unique.setdefault(needle, kind)
    return [(kind, needle) for needle, kind in unique.items()]


def validate_mapping() -> None:
    targets = sorted(COHORT.values())
    if len(targets) != len(set(targets)):
        raise ArchiveMoveError("P9_TARGET_DUPLICATE")
    portable: dict[str, str] = {}
    for source, target in COHORT.items():
        pure = PurePosixPath(target)
        if (
            pure.is_absolute()
            or ".." in pure.parts
            or pure.name != PurePosixPath(source).name
            or unicodedata.normalize("NFC", target) != target
        ):
            raise ArchiveMoveError(f"P9_TARGET_INVALID:{source}:{target}")
        key = portable_key(target)
        if key in portable:
            raise ArchiveMoveError(f"P9_TARGET_PORTABLE_DUPLICATE:{portable[key]}:{target}")
        portable[key] = target
    for index, target in enumerate(targets):
        for other in targets[index + 1 :]:
            if other.startswith(target + "/") or target.startswith(other + "/"):
                raise ArchiveMoveError(f"P9_TARGET_PREFIX_COLLISION:{target}:{other}")


def verify_portable_tree(treeish: str) -> None:
    seen: dict[str, str] = {}
    for _mode, _kind, _oid, path in all_tree_entries(treeish):
        if unicodedata.normalize("NFC", path) != path:
            raise ArchiveMoveError(f"P9_PORTABLE_NFC_PATH:{path}")
        key = portable_key(path)
        if key in seen and seen[key] != path:
            raise ArchiveMoveError(f"P9_PORTABLE_COLLISION:{seen[key]}:{path}")
        seen[key] = path
    for target in COHORT.values():
        parts = PurePosixPath(target).parts
        for index in range(1, len(parts)):
            ancestor = PurePosixPath(*parts[:index]).as_posix()
            entry = tree_entry(treeish, ancestor)
            if entry is not None and entry[0] == "120000":
                raise ArchiveMoveError(f"P9_TARGET_SYMLINK_ANCESTOR:{target}:{ancestor}")


def line_context(data: bytes, offset: int) -> tuple[int | None, str | None]:
    try:
        prefix = data[:offset].decode("utf-8")
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return None, None
    line_no = prefix.count("\n") + 1
    line = text.splitlines()[line_no - 1] if text.splitlines() else ""
    return line_no, line


def occurrence_role(
    path: str, token: str, variant_kind: str, line: str | None
) -> tuple[str, bool]:
    if path == str(TESTS.relative_to(ROOT)) and line and "P9_PLANT" in line:
        return "P9_NEGATIVE_PLANT_LITERAL", False
    if path == str(TESTS.relative_to(ROOT)) and line and "P9_TYPED_TEST" in line:
        return "P9_TYPED_POSITIVE_TEST_LITERAL", False
    if variant_kind != "EXACT":
        return f"UNTYPED_{variant_kind}_REFERENCE", True
    executable = path.endswith((".py", ".sh", ".lean")) and bool(
        line
        and re.search(
            r"(?:open|read_text|read_bytes|load|include|import|require)\s*\(?[^#\n]*"
            + re.escape(token),
            line,
            re.IGNORECASE,
        )
    )
    if executable:
        return "EXECUTABLE_REFERENCE", True
    if path == str(P8_V1_MANIFEST.relative_to(ROOT)):
        return "P8_V1_IMMUTABLE_PREDECESSOR_ROW", False
    if path == str(P7_V1_MANIFEST.relative_to(ROOT)):
        return "P7_V1_IMMUTABLE_HISTORICAL_ROW", False
    if path in {str(P8_V2_MANIFEST.relative_to(ROOT)), str(P8_V2_RECEIPT.relative_to(ROOT))}:
        return "P8_V2_TYPED_TRANSITION_ROW", False
    if path in {
        str(P7_SUCCESSOR.relative_to(ROOT)),
        str(P7_SUCCESSOR_RECEIPT.relative_to(ROOT)),
    }:
        return "P7_TYPED_RELOCATION_SUCCESSOR_ROW", False
    if path == str(Path(__file__).relative_to(ROOT)):
        return "P9_EXACT_MAPPING_OR_TYPED_SCANNER_LITERAL", False
    if path in {str(P8_CHECKER.relative_to(ROOT)), str(P8_TESTS.relative_to(ROOT))}:
        if line and "P9_TYPED" in line:
            return "P8_VERSIONED_PREDECESSOR_OR_SUCCESSOR_LITERAL", False
        return "P8_UNMARKED_CONTROL_LITERAL", True
    if path in {str(P7_CHECKER.relative_to(ROOT)), str(P7_TESTS.relative_to(ROOT))}:
        if line and "P9_TYPED" in line:
            return "P7_VERSIONED_PREDECESSOR_OR_SUCCESSOR_LITERAL", False
        return "P7_UNMARKED_CONTROL_LITERAL", True
    target = COHORT.get(token)
    if target == path:
        return "ARCHIVED_PAYLOAD_HISTORY_CONTENT", False
    return "UNCLASSIFIED_ACTIVE_REFERENCE", True


def raw_occurrence_inventory(
    treeish: str, blobs: Iterable[tuple[str, str, bytes]] | None = None
) -> list[dict[str, Any]]:
    if blobs is None:
        return git_grep_occurrence_inventory(treeish)
    inventory: list[dict[str, Any]] = []
    source = all_blob_bytes(treeish) if blobs is None else blobs
    for path, oid, data in source:
        for token in SOURCE_TOKENS:
            exact_needle = token.encode()
            exact_spans: list[tuple[int, int]] = []
            exact_start = 0
            while True:
                exact_offset = data.find(exact_needle, exact_start)
                if exact_offset < 0:
                    break
                exact_spans.append((exact_offset, exact_offset + len(exact_needle)))
                exact_start = exact_offset + len(exact_needle)
            for variant_kind, needle in reference_variants(token):
                start = 0
                while True:
                    offset = data.find(needle, start)
                    if offset < 0:
                        break
                    if variant_kind != "EXACT" and any(
                        begin <= offset and offset + len(needle) <= end
                        for begin, end in exact_spans
                    ):
                        start = offset + len(needle)
                        continue
                    line_no, line = line_context(data, offset)
                    role, blocks = occurrence_role(path, token, variant_kind, line)
                    inventory.append(
                        {
                            "path": path,
                            "blob_oid": oid,
                            "token": token,
                            "variant": variant_kind,
                            "byte_offset": offset,
                            "line": line_no,
                            "line_sha256": sha256(line.encode()) if line is not None else None,
                            "role": role,
                            "blocks_move": blocks,
                        }
                    )
                    start = offset + len(needle)
    blockers = [row for row in inventory if row["blocks_move"]]
    if blockers:
        raise ArchiveMoveError(f"P9_ACTIVE_OR_UNTYPED_REFERENCE:{blockers}")
    return inventory


def git_grep_occurrence_inventory(treeish: str) -> list[dict[str, Any]]:
    variants: dict[bytes, list[tuple[str, str]]] = {}
    for token in SOURCE_TOKENS:
        for kind, needle in reference_variants(token):
            variants.setdefault(needle, []).append((token, kind))
    cmd = ["git", "-C", str(ROOT), "grep", "-a", "-z", "-n", "-F"]
    for needle in variants:
        cmd.extend(["-e", needle.decode()])
    cmd.extend([treeish, "--"])
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if result.returncode not in (0, 1):
        raise ArchiveMoveError(f"P9_RAW_GIT_GREP_FAILED:{result.stderr.decode(errors='replace')}")
    inventory: list[dict[str, Any]] = []
    oid_by_path = {path: oid for _mode, kind, oid, path in all_tree_entries(treeish) if kind == "blob"}
    prefix = (treeish + ":").encode()
    for record in result.stdout.splitlines():
        fields = record.split(b"\0", 2)
        if len(fields) != 3:
            raise ArchiveMoveError("P9_RAW_GIT_GREP_PROTOCOL")
        raw_path, raw_line, content = fields
        if raw_path.startswith(prefix):
            raw_path = raw_path[len(prefix) :]
        path = raw_path.decode("utf-8", "surrogateescape")
        line_no = int(raw_line)
        exact_spans_by_token: dict[str, list[tuple[int, int]]] = {}
        for token in SOURCE_TOKENS:
            needle = token.encode()
            spans: list[tuple[int, int]] = []
            start = 0
            while True:
                offset = content.find(needle, start)
                if offset < 0:
                    break
                spans.append((offset, offset + len(needle)))
                start = offset + len(needle)
            exact_spans_by_token[token] = spans
        for needle, token_kinds in variants.items():
            start = 0
            while True:
                offset = content.find(needle, start)
                if offset < 0:
                    break
                for token, kind in token_kinds:
                    if kind != "EXACT" and any(
                        begin <= offset and offset + len(needle) <= end
                        for begin, end in exact_spans_by_token[token]
                    ):
                        continue
                    line = content.decode("utf-8", "replace")
                    role, blocks = occurrence_role(path, token, kind, line)
                    inventory.append(
                        {
                            "path": path,
                            "blob_oid": oid_by_path[path],
                            "token": token,
                            "variant": kind,
                            "line_byte_offset": offset,
                            "line": line_no,
                            "line_sha256": sha256(content),
                            "role": role,
                            "blocks_move": blocks,
                        }
                    )
                start = offset + len(needle)
    inventory.sort(key=lambda row: (row["path"], row["line"], row["line_byte_offset"], row["token"], row["variant"]))
    blockers = [row for row in inventory if row["blocks_move"]]
    if blockers:
        raise ArchiveMoveError(f"P9_ACTIVE_OR_UNTYPED_REFERENCE:{blockers}")
    return inventory


def scan_evidence(treeish: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Raw `git grep -a` plus a typed scan of executable/registry blobs only."""
    occurrences = git_grep_occurrence_inventory(treeish)
    selectors = git_grep_selector_inventory(treeish)
    return occurrences, selectors


GENERIC_PATTERNS = (
    re.compile(r"(?:Path\.cwd\(\)|\bROOT\b|\bREPO\b|\brepo\b)\s*\.\s*(?:glob|rglob|iterdir)\s*\("),
    re.compile(r"\bos\.(?:listdir|scandir)\s*\(\s*(?:ROOT|REPO|repo|Path\.cwd\(\))"),
    re.compile(r"\bgit\s+ls-files\b(?![^\n]*(?:--|/))"),
    re.compile(r"\bfor\s+[A-Za-z_][A-Za-z0-9_]*\s+in\s+\*(?:\s|;|$)"),
    re.compile(r"\bfind\s+\.\s+(?:-|$)"),
)


def generic_selector_inventory(
    treeish: str, blobs: Iterable[tuple[str, str, bytes]] | None = None
) -> list[dict[str, Any]]:
    if blobs is None:
        return git_grep_selector_inventory(treeish)
    rows: list[dict[str, Any]] = []
    source = all_blob_bytes(treeish) if blobs is None else blobs
    for path, oid, data in source:
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            continue
        for line_no, line in enumerate(text.splitlines(), 1):
            if not any(pattern.search(line) for pattern in GENERIC_PATTERNS):
                continue
            if path == str(Path(__file__).relative_to(ROOT)):
                role, blocks = "P9_SCANNER_IMPLEMENTATION", False
            elif path == "scripts/build_proshka_brief.py" and "repo.glob(g)" in line:
                role, blocks = "USER_SUPPLIED_SELECTOR_NO_FIXED_CONSUMER", False
            elif path in {
                str(P8_CHECKER.relative_to(ROOT)),
                str(P8_TESTS.relative_to(ROOT)),
                str(TESTS.relative_to(ROOT)),
            }:
                role, blocks = "VERSIONED_CONTROL_OR_PLANT_SELECTOR", False
            elif path.startswith("archive/") or "/archive/" in path:
                role, blocks = "HISTORICAL_TEXT_ONLY", False
            elif fixed_selector_disjoint(line):
                role, blocks = "FIXED_SELECTOR_DISJOINT_FROM_COHORT", False
            else:
                role, blocks = "UNCLASSIFIED_ROOT_SELECTOR", True
            rows.append(
                {
                    "path": path,
                    "blob_oid": oid,
                    "line": line_no,
                    "line_sha256": sha256(line.encode()),
                    "role": role,
                    "blocks_move": blocks,
                }
            )
    blockers = [row for row in rows if row["blocks_move"]]
    if blockers:
        raise ArchiveMoveError(f"P9_GENERIC_SELECTOR_REFERENCE:{blockers}")
    return rows


def selector_decision(
    path: str, line: str, mode: str, shebang_paths: set[str]
) -> tuple[str, bool]:
    if path == str(Path(__file__).relative_to(ROOT)):
        return "P9_SCANNER_IMPLEMENTATION", False
    if path == "scripts/build_proshka_brief.py" and "repo.glob(g)" in line:
        return "USER_SUPPLIED_SELECTOR_NO_FIXED_CONSUMER", False
    if path in {
        str(P8_CHECKER.relative_to(ROOT)),
        str(P8_TESTS.relative_to(ROOT)),
        str(TESTS.relative_to(ROOT)),
    }:
        return "VERSIONED_CONTROL_OR_PLANT_SELECTOR", False
    if path.startswith("archive/") or "/archive/" in path:
        return "HISTORICAL_TEXT_ONLY", False
    if (path, sha256(line.encode())) in SCOPED_SELECTOR_LINE_HASHES:
        return "SCOPED_SELECTOR_PROVEN_BY_LOCAL_BASE_BINDING", False
    if fixed_selector_disjoint(line):
        return "FIXED_SELECTOR_DISJOINT_FROM_COHORT", False
    selector_domain = (
        mode == "100755"
        or path in shebang_paths
        or path.endswith(
            (".py", ".sh", ".bash", ".lean", ".yaml", ".yml", ".toml", ".json")
        )
    )
    if not selector_domain:
        return "NONEXECUTABLE_NONREGISTRY_DOCUMENTATION", False
    return "UNCLASSIFIED_ROOT_SELECTOR", True


def git_grep_selector_inventory(treeish: str) -> list[dict[str, Any]]:
    patterns = (
        r"(Path\.cwd\(\)|ROOT|REPO|repo)[[:space:]]*\.[[:space:]]*(glob|rglob|iterdir)[[:space:]]*\(",
        r"os\.(listdir|scandir)[[:space:]]*\(",
        r"git[[:space:]]+ls-files",
        r"for[[:space:]]+[A-Za-z_][A-Za-z0-9_]*[[:space:]]+in[[:space:]]+\*",
        r"find[[:space:]]+\.[[:space:]]+(-|$)",
    )
    cmd = ["git", "-C", str(ROOT), "grep", "-a", "-z", "-n", "-E"]
    for pattern in patterns:
        cmd.extend(["-e", pattern])
    cmd.extend([treeish, "--"])
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if result.returncode not in (0, 1):
        raise ArchiveMoveError(f"P9_SELECTOR_GIT_GREP_FAILED:{result.stderr.decode(errors='replace')}")
    entries = {
        path: (mode, oid)
        for mode, kind, oid, path in all_tree_entries(treeish)
        if kind == "blob"
    }
    shebang_result = subprocess.run(
        ["git", "-C", str(ROOT), "grep", "-a", "-l", "-E", r"^#!", treeish, "--"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
        text=True,
    )
    shebang_paths = {
        row.removeprefix(treeish + ":") for row in shebang_result.stdout.splitlines()
    }
    prefix = (treeish + ":").encode()
    rows: list[dict[str, Any]] = []
    for record in result.stdout.splitlines():
        fields = record.split(b"\0", 2)
        if len(fields) != 3:
            raise ArchiveMoveError("P9_SELECTOR_GIT_GREP_PROTOCOL")
        raw_path, raw_line, content = fields
        if raw_path.startswith(prefix):
            raw_path = raw_path[len(prefix) :]
        path = raw_path.decode("utf-8", "surrogateescape")
        line = content.decode("utf-8", "replace")
        mode, oid = entries[path]
        role, blocks = selector_decision(path, line, mode, shebang_paths)
        rows.append(
            {
                "path": path,
                "blob_oid": oid,
                "line": int(raw_line),
                "line_sha256": sha256(content),
                "role": role,
                "blocks_move": blocks,
            }
        )
    blockers = [row for row in rows if row["blocks_move"]]
    if blockers:
        raise ArchiveMoveError(f"P9_GENERIC_SELECTOR_REFERENCE:{blockers}")
    return rows


def fixed_selector_disjoint(line: str) -> bool:
    literals = re.findall(r"[\"']([^\"']*[*?][^\"']*)[\"']", line)
    if not literals:
        return False
    names = set(COHORT) | {PurePosixPath(path).name for path in COHORT.values()}
    return all(not any(fnmatch.fnmatchcase(name, pattern) for name in names) for pattern in literals)


def root_fingerprint(path: str) -> dict[str, Any]:
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


def dirty_paths() -> set[str]:
    tracked = git("diff", "--name-only", "-z", "HEAD", "--")
    staged = git("diff", "--cached", "--name-only", "-z", "HEAD", "--")
    untracked = git("ls-files", "--others", "--exclude-standard", "-z")
    return {
        item.decode("utf-8", "surrogateescape")
        for raw in (tracked, staged, untracked)
        for item in raw.split(b"\0")
        if item
    }


def foreign_dirty_snapshot() -> list[dict[str, Any]]:
    return [root_fingerprint(path) for path in sorted(dirty_paths() - TRANSACTION_PATHS)]


def verify_foreign_snapshot(expected: list[dict[str, Any]]) -> None:
    if expected != foreign_dirty_snapshot():
        raise ArchiveMoveError("P9_FOREIGN_DIRTY_DRIFT")


def validate_destination_parents(root: Path, target: str) -> None:
    target_path = root / target
    if target_path.exists() or target_path.is_symlink():
        raise ArchiveMoveError(f"P9_TARGET_EXISTS:{target}")
    current = root
    for part in PurePosixPath(target).parts[:-1]:
        current /= part
        if current.is_symlink():
            raise ArchiveMoveError(f"P9_TARGET_PARENT_SYMLINK:{target}:{current}")
        if current.exists() and not current.is_dir():
            raise ArchiveMoveError(f"P9_TARGET_PARENT_NOT_DIRECTORY:{target}:{current}")


def verify_move_invariants(treeish: str) -> None:
    for row in baseline_move_rows():
        source = tree_entry(treeish, row["source"])
        target = tree_entry(treeish, row["target"])
        if source is not None:
            raise ArchiveMoveError(f"P9_SOURCE_RESURRECTED:{row['source']}:{source}")
        if target is None:
            raise ArchiveMoveError(f"P9_TARGET_MISSING:{row['target']}")
        mode, kind, oid = target
        if kind != "blob" or mode != row["git_mode"] or oid != row["source_oid"]:
            raise ArchiveMoveError(f"P9_TARGET_OBJECT_DRIFT:{row['target']}:{target}")
        data = tree_blob(treeish, row["target"])
        if sha256(data) != row["sha256"] or len(data) != row["byte_size"]:
            raise ArchiveMoveError(f"P9_TARGET_BYTES_DRIFT:{row['target']}")


def verify_candidate_scope(treeish: str) -> None:
    changed = {
        item.decode("utf-8", "surrogateescape")
        for item in git("diff", "--no-renames", "--name-only", "-z", BASELINE_COMMIT, treeish, "--").split(b"\0")
        if item
    }
    if changed != CANDIDATE_PATHS:
        raise ArchiveMoveError(
            f"P9_CANDIDATE_SCOPE_DRIFT:missing={sorted(CANDIDATE_PATHS-changed)}:"
            f"outside={sorted(changed-CANDIDATE_PATHS)}"
        )


def validate_support_artifacts() -> None:
    immutable_hashes(
        {"schema": P8_V1_SCHEMA, "manifest": P8_V1_MANIFEST, "receipt": P8_V1_RECEIPT},
        P8_V1_HASHES,
        "P8_V1_IMMUTABLE_PREDECESSOR_DRIFT",
    )
    immutable_hashes(
        {"manifest": P7_V1_MANIFEST, "receipt": P7_V1_RECEIPT},
        P7_V1_HASHES,
        "P7_V1_IMMUTABLE_PREDECESSOR_DRIFT",
    )
    p8, p8_receipt = build_p8_v2()
    if json.loads(P8_V2_MANIFEST.read_text()) != p8:
        raise ArchiveMoveError("P8_V2_MANIFEST_DRIFT")
    if json.loads(P8_V2_RECEIPT.read_text()) != p8_receipt:
        raise ArchiveMoveError("P8_V2_RECEIPT_DRIFT")
    p7, p7_receipt = build_p7_successor()
    if json.loads(P7_SUCCESSOR.read_text()) != p7:
        raise ArchiveMoveError("P7_RELOCATION_SUCCESSOR_DRIFT")
    if json.loads(P7_SUCCESSOR_RECEIPT.read_text()) != p7_receipt:
        raise ArchiveMoveError("P7_RELOCATION_RECEIPT_DRIFT")


def assemble_receipt(
    objects: dict[str, dict[str, Any]],
    treeish: str,
    occurrences: list[dict[str, Any]],
    selectors: list[dict[str, Any]],
    foreign: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema_version": "q3.root_archive_zero_reference_receipt.v1",
        "status": "ZERO_ACTIVE_CONSUMERS_WITH_CONTROL_PLANE_MIGRATION_REFS",
        "baseline_commit": BASELINE_COMMIT,
        "prospective_tree_excluding_receipt": treeish,
        "candidate_objects": objects,
        "cohort": baseline_move_rows(),
        "occurrences": occurrences,
        "generic_selectors": selectors,
        "active_consumer_count": 0,
        "foreign_dirty_snapshot": foreign,
        "rollback_mapping": [
            {"from": target, "to": source, "git_operation": "git mv"}
            for source, target in sorted(COHORT.items())
        ],
        "evolution_contract": EVOLUTION_CONTRACT,
        "plants": PLANT_IDS,
    }


def validate_schema_payload(payload: dict[str, Any]) -> None:
    try:
        import jsonschema
    except ImportError as exc:
        raise ArchiveMoveError("P9_JSONSCHEMA_UNAVAILABLE") from exc
    try:
        jsonschema.Draft202012Validator(json.loads(SCHEMA.read_text())).validate(payload)
    except jsonschema.ValidationError as exc:
        raise ArchiveMoveError(f"P9_RECEIPT_SCHEMA_INVALID:{exc.message}") from exc


def build_receipt() -> dict[str, Any]:
    validate_mapping()
    validate_support_artifacts()
    objects = support_objects()
    treeish = prospective_tree(objects)
    verify_candidate_scope(treeish)
    verify_move_invariants(treeish)
    verify_portable_tree(treeish)
    occurrences, selectors = scan_evidence(treeish)
    payload = assemble_receipt(
        objects, treeish, occurrences, selectors, foreign_dirty_snapshot()
    )
    validate_schema_payload(payload)
    return payload


def verify_receipt(payload: dict[str, Any]) -> None:
    validate_schema_payload(payload)
    if payload.get("baseline_commit") != BASELINE_COMMIT:
        raise ArchiveMoveError("P9_BASELINE_DRIFT")
    objects = payload.get("candidate_objects")
    if not isinstance(objects, dict) or set(objects) != SUPPORT_PATHS:
        raise ArchiveMoveError("P9_CANDIDATE_OBJECT_SET_DRIFT")
    for path, row in objects.items():
        actual = file_object(ROOT / path)
        if actual != row:
            raise ArchiveMoveError(f"P9_SUPPORT_OBJECT_DRIFT:{path}")
    treeish = prospective_tree(objects)
    if treeish != payload.get("prospective_tree_excluding_receipt"):
        raise ArchiveMoveError("P9_PROSPECTIVE_TREE_DRIFT")
    verify_candidate_scope(treeish)
    verify_move_invariants(treeish)
    verify_portable_tree(treeish)
    occurrences, selectors = scan_evidence(treeish)
    if occurrences != payload.get("occurrences"):
        raise ArchiveMoveError("P9_OCCURRENCE_INVENTORY_DRIFT")
    if selectors != payload.get("generic_selectors"):
        raise ArchiveMoveError("P9_GENERIC_SELECTOR_INVENTORY_DRIFT")
    foreign = foreign_dirty_snapshot()
    verify_foreign_snapshot(payload.get("foreign_dirty_snapshot", []))
    expected_rollback = [
        {"from": target, "to": source, "git_operation": "git mv"}
        for source, target in sorted(COHORT.items())
    ]
    if payload.get("rollback_mapping") != expected_rollback:
        raise ArchiveMoveError("P9_ROLLBACK_MAPPING_DRIFT")
    expected = assemble_receipt(objects, treeish, occurrences, selectors, foreign)
    if expected != payload:
        raise ArchiveMoveError("P9_RECEIPT_DRIFT")


def execute_moves(payload: dict[str, Any]) -> None:
    verify_receipt(payload)
    verify_umbrella(payload)
    subprocess.run(
        ["git", "-C", str(ROOT), "fetch", "origin", "rh_clean"],
        check=True,
        stdout=subprocess.DEVNULL,
    )
    origin = git("rev-parse", "origin/rh_clean").decode().strip()
    if live_head() != BASELINE_COMMIT or origin != BASELINE_COMMIT:
        raise ArchiveMoveError(
            f"P9_EXECUTION_HEAD_ORIGIN_DRIFT:head={live_head()}:origin={origin}"
        )
    staged = {
        item.decode("utf-8", "surrogateescape")
        for item in git("diff", "--cached", "--name-only", "-z", "HEAD", "--").split(b"\0")
        if item
    }
    if staged:
        raise ArchiveMoveError(f"P9_EXECUTION_STAGED_PATHS_PRESENT:{sorted(staged)}")
    rows = {row["source"]: row for row in baseline_move_rows()}
    for source, target in sorted(COHORT.items()):
        source_path = ROOT / source
        source_stat = source_path.lstat()
        parent_stat = source_path.parent.lstat()
        if stat.S_ISLNK(source_stat.st_mode) or stat.S_ISLNK(parent_stat.st_mode):
            raise ArchiveMoveError(f"P9_SOURCE_OR_PARENT_SYMLINK:{source}")
        if not stat.S_ISREG(source_stat.st_mode):
            raise ArchiveMoveError(f"P9_SOURCE_NOT_REGULAR:{source}")
        row = rows[source]
        data = source_path.read_bytes()
        live_mode = "100755" if source_stat.st_mode & stat.S_IXUSR else "100644"
        live_oid = git("hash-object", "--stdin", input_data=data).decode().strip()
        if (
            live_mode != row["git_mode"]
            or live_oid != row["source_oid"]
            or sha256(data) != row["sha256"]
            or len(data) != row["byte_size"]
        ):
            raise ArchiveMoveError(f"P9_LIVE_SOURCE_DRIFT:{source}")
        validate_destination_parents(ROOT, target)
    moved: list[tuple[str, str]] = []
    staged_support = sorted(SUPPORT_PATHS)
    try:
        subprocess.run(
            ["git", "-C", str(ROOT), "add", "--", *staged_support], check=True
        )
        for source, target in sorted(COHORT.items()):
            (ROOT / target).parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                ["git", "-C", str(ROOT), "mv", "--", source, target], check=True
            )
            moved.append((source, target))
        staged_tree = git("write-tree").decode().strip()
        if staged_tree != payload["prospective_tree_excluding_receipt"]:
            raise ArchiveMoveError(
                f"P9_POSTMOVE_INDEX_TREE_DRIFT:{staged_tree}:"
                f"{payload['prospective_tree_excluding_receipt']}"
            )
        verify_move_invariants(staged_tree)
        verify_portable_tree(staged_tree)
        verify_foreign_snapshot(payload["foreign_dirty_snapshot"])
        subprocess.run(
            ["git", "-C", str(ROOT), "fetch", "origin", "rh_clean"],
            check=True,
            stdout=subprocess.DEVNULL,
        )
        if live_head() != BASELINE_COMMIT or git("rev-parse", "origin/rh_clean").decode().strip() != BASELINE_COMMIT:
            raise ArchiveMoveError("P9_EXECUTION_HEAD_ORIGIN_DRIFT_AFTER_MOVE")
    except Exception:
        for source, target in reversed(moved):
            if (ROOT / target).exists() and not (ROOT / source).exists():
                subprocess.run(
                    ["git", "-C", str(ROOT), "mv", "--", target, source], check=False
                )
        subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "restore",
                "--staged",
                f"--source={BASELINE_COMMIT}",
                "--",
                *staged_support,
            ],
            check=False,
        )
        raise


def write_support_artifacts() -> None:
    p8_schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "q3.root_artifact_classification.v2",
        "type": "object",
        "required": ["schema_version", "status", "predecessor", "baseline_commit", "scope", "physical_moves_performed", "counts", "future_session_protocol_policy", "script_output_policy", "entries", "executed_moves"],
        "additionalProperties": False,
        "properties": {
            "schema_version": {"const": "q3.root_artifact_classification.v2"},
            "status": {"const": "P9_EXECUTED_TRANSITION"},
            "predecessor": {"type": "object"},
            "baseline_commit": {"const": BASELINE_COMMIT},
            "scope": {"const": "ALL_TRACKED_IMMEDIATE_ROOT_ENTRIES_PLUS_EXECUTED_LEDGER"},
            "physical_moves_performed": {"const": True},
            "counts": {"type": "object"},
            "future_session_protocol_policy": {"type": "object"},
            "script_output_policy": {"type": "object"},
            "entries": {"type": "array", "minItems": 64, "maxItems": 64},
            "executed_moves": {"type": "array", "minItems": 5, "maxItems": 5},
        },
    }
    p7_schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "q3.portability_relocation_successor.v1",
        "type": "object",
        "required": ["schema_version", "status", "baseline_commit", "predecessor", "relocations"],
        "additionalProperties": False,
        "properties": {
            "schema_version": {"const": "q3.portability_relocation_successor.v1"},
            "status": {"const": "TYPED_RELOCATION_SUCCESSOR"},
            "baseline_commit": {"const": BASELINE_COMMIT},
            "predecessor": {"type": "object"},
            "relocations": {"type": "array", "minItems": 1, "maxItems": 1},
        },
    }
    receipt_schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "q3.root_archive_zero_reference_receipt.v1",
        "type": "object",
        "required": ["schema_version", "status", "baseline_commit", "prospective_tree_excluding_receipt", "candidate_objects", "cohort", "occurrences", "generic_selectors", "active_consumer_count", "foreign_dirty_snapshot", "rollback_mapping", "evolution_contract", "plants"],
        "additionalProperties": False,
        "properties": {
            "schema_version": {"const": "q3.root_archive_zero_reference_receipt.v1"},
            "status": {"const": "ZERO_ACTIVE_CONSUMERS_WITH_CONTROL_PLANE_MIGRATION_REFS"},
            "baseline_commit": {"const": BASELINE_COMMIT},
            "prospective_tree_excluding_receipt": {"type": "string", "pattern": "^[0-9a-f]{40,64}$"},
            "candidate_objects": {"type": "object"},
            "cohort": {"type": "array", "minItems": 5, "maxItems": 5},
            "occurrences": {"type": "array"},
            "generic_selectors": {"type": "array"},
            "active_consumer_count": {"const": 0},
            "foreign_dirty_snapshot": {"type": "array"},
            "rollback_mapping": {"type": "array", "minItems": 5, "maxItems": 5},
            "evolution_contract": {"type": "object"},
            "plants": {"type": "array", "minItems": 13, "maxItems": 13},
        },
    }
    write_json(P8_V2_SCHEMA, p8_schema)
    write_json(P7_SUCCESSOR_SCHEMA, p7_schema)
    write_json(SCHEMA, receipt_schema)
    p8, p8_receipt = build_p8_v2()
    write_json(P8_V2_MANIFEST, p8)
    write_json(P8_V2_RECEIPT, p8_receipt)
    p7, p7_receipt = build_p7_successor()
    write_json(P7_SUCCESSOR, p7)
    write_json(P7_SUCCESSOR_RECEIPT, p7_receipt)


def execution_umbrella(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_version": "q3.root_archive_execution_umbrella.v1",
        "status": "EXACT_TWO_STAGE_BINDING",
        "baseline_commit": BASELINE_COMMIT,
        "prospective_tree_excluding_receipts": payload[
            "prospective_tree_excluding_receipt"
        ],
        "hashes": {
            "p9_execution_receipt": sha256(RECEIPT.read_bytes()),
            "p8_v2_receipt": sha256(P8_V2_RECEIPT.read_bytes()),
            "p7_relocation_receipt": sha256(P7_SUCCESSOR_RECEIPT.read_bytes()),
        },
        "cohort_digest": sha256(canonical_json(baseline_move_rows())),
    }


def verify_umbrella(payload: dict[str, Any]) -> None:
    if not UMBRELLA.is_file():
        raise ArchiveMoveError("P9_EXECUTION_UMBRELLA_MISSING")
    if json.loads(UMBRELLA.read_text()) != execution_umbrella(payload):
        raise ArchiveMoveError("P9_EXECUTION_UMBRELLA_DRIFT")


def expected_postmove_tree(payload: dict[str, Any]) -> str:
    with tempfile.TemporaryDirectory() as td:
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(Path(td) / "index")
        subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "read-tree",
                payload["prospective_tree_excluding_receipt"],
            ],
            env=env,
            check=True,
        )
        for path in (RECEIPT, UMBRELLA):
            data = path.read_bytes()
            oid = git("hash-object", "--stdin", input_data=data).decode().strip()
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(ROOT),
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    "100644",
                    oid,
                    str(path.relative_to(ROOT)),
                ],
                env=env,
                check=True,
            )
        return git("write-tree", env=env).decode().strip()


def verify_postmove(payload: dict[str, Any]) -> None:
    verify_receipt(payload)
    verify_umbrella(payload)
    head = live_head()
    parent = git("rev-parse", "HEAD^").decode().strip() if head != BASELINE_COMMIT else None
    origin = git("rev-parse", "origin/rh_clean").decode().strip()
    if origin != BASELINE_COMMIT or (head != BASELINE_COMMIT and parent != BASELINE_COMMIT):
        raise ArchiveMoveError(
            f"P9_POSTMOVE_HEAD_ORIGIN_DRIFT:head={head}:parent={parent}:origin={origin}"
        )
    staged_paths = {
        item.decode("utf-8", "surrogateescape")
        for item in git(
            "diff",
            "--cached",
            "--no-renames",
            "--name-only",
            "-z",
            BASELINE_COMMIT,
            "--",
        ).split(b"\0")
        if item
    }
    if staged_paths != TRANSACTION_PATHS:
        raise ArchiveMoveError(
            f"P9_POSTMOVE_STAGED_SCOPE_DRIFT:missing={sorted(TRANSACTION_PATHS-staged_paths)}:"
            f"outside={sorted(staged_paths-TRANSACTION_PATHS)}"
        )
    staged_tree = git("write-tree").decode().strip()
    expected_tree = expected_postmove_tree(payload)
    if staged_tree != expected_tree:
        raise ArchiveMoveError(f"P9_POSTMOVE_FINAL_TREE_DRIFT:{staged_tree}:{expected_tree}")
    verify_move_invariants(staged_tree)
    verify_portable_tree(staged_tree)
    verify_foreign_snapshot(payload["foreign_dirty_snapshot"])
    rows = {row["source"]: row for row in payload["cohort"]}
    for source, target in sorted(COHORT.items()):
        if (ROOT / source).exists() or (ROOT / source).is_symlink():
            raise ArchiveMoveError(f"P9_POSTMOVE_SOURCE_PRESENT:{source}")
        target_path = ROOT / target
        if not target_path.is_file() or target_path.is_symlink():
            raise ArchiveMoveError(f"P9_POSTMOVE_TARGET_NOT_REGULAR:{target}")
        data = target_path.read_bytes()
        row = rows[source]
        mode = "100755" if target_path.stat().st_mode & stat.S_IXUSR else "100644"
        oid = git("hash-object", "--stdin", input_data=data).decode().strip()
        if (
            mode != row["git_mode"]
            or oid != row["source_oid"]
            or sha256(data) != row["sha256"]
            or len(data) != row["byte_size"]
        ):
            raise ArchiveMoveError(f"P9_POSTMOVE_TARGET_WORKTREE_DRIFT:{target}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=(
            "prepare-artifacts",
            "build-preflight",
            "check-preflight",
            "check-postmove",
            "execute-moves",
        ),
    )
    args = parser.parse_args()
    try:
        if args.command == "prepare-artifacts":
            write_support_artifacts()
            print("ROOT_ARCHIVE_SUPPORT_ARTIFACTS_PASS")
        elif args.command == "build-preflight":
            payload = build_receipt()
            write_json(RECEIPT, payload)
            write_json(UMBRELLA, execution_umbrella(payload))
            print("ROOT_ARCHIVE_ZERO_REFERENCE_BUILD_PASS")
        elif args.command == "check-preflight":
            payload = json.loads(RECEIPT.read_text())
            verify_receipt(payload)
            verify_umbrella(payload)
            print("ROOT_ARCHIVE_ZERO_REFERENCE_CHECK_PASS")
        elif args.command == "check-postmove":
            payload = json.loads(RECEIPT.read_text())
            verify_postmove(payload)
            print("ROOT_ARCHIVE_POSTMOVE_CHECK_PASS")
        else:
            execute_moves(json.loads(RECEIPT.read_text()))
            print("ROOT_ARCHIVE_EXACT_MOVES_PASS")
    except (OSError, json.JSONDecodeError, ArchiveMoveError) as exc:
        print(f"ROOT_ARCHIVE_ZERO_REFERENCE_FAIL:{exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
