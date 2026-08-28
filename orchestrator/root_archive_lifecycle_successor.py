#!/usr/bin/env python3
"""Additive lifecycle successor for the immutable P9 archive transaction."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import subprocess
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TRANSACTION_COMMIT = "c450773bd63b295439df2174da12fafa16958f1f"
BASELINE_COMMIT = "1c5988c3d97c46c1cb97bdb8a7019fd52a429c1f"
TRANSACTION_TREE = "cc0717eea10b9ea00c50c0db8b8870de11fd80d1"

SCHEMA = ROOT / "docs/semantic_quarantine/ROOT_ARCHIVE_LIFECYCLE_SUCCESSOR_SCHEMA_v1.json"
RECEIPT = ROOT / "docs/semantic_quarantine/ROOT_ARCHIVE_LIFECYCLE_SUCCESSOR_RECEIPT_v1.json"
CHECKER = Path(__file__).resolve()
TESTS = ROOT / "orchestrator/tests/test_root_archive_lifecycle_successor.py"
WRAPPER = ROOT / "scripts/check_root_archive_lifecycle_successor.sh"

SUCCESSOR_SUPPORT_PATHS = frozenset(
    str(path.relative_to(ROOT)) for path in (SCHEMA, CHECKER, TESTS, WRAPPER)
)
SUCCESSOR_PATHS = SUCCESSOR_SUPPORT_PATHS | {str(RECEIPT.relative_to(ROOT))}

ORIGINAL_ARTIFACT_HASHES = {
    "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_RECEIPT_v1.json": (
        "99c8d54feae0f019a182b8aa5439370f198c452c0ee68e993d597d55d482b03e"
    ),
    "docs/semantic_quarantine/ROOT_ARCHIVE_EXECUTION_UMBRELLA_v1.json": (
        "1160da2aa2f5297926edfaf6501aca1f5301c35b778de9f2d83a8d0c29ed57e8"
    ),
    "orchestrator/root_archive_moves.py": (
        "4e62c798ec3396420dcd7461fa31a17be750e564ada1afed11aeb92c2646f3ea"
    ),
    "orchestrator/tests/test_root_archive_moves.py": (
        "3af4f8c705e976591f5078f7f98e797f368bdca88c1d12ea7c0f28978bb258fc"
    ),
    "scripts/check_root_archive_preflight.sh": (
        "604c94d0994be1f48f4ec0935da92993107cc04babe3bd0e731d8e96cea7d412"
    ),
}

EXPECTED_MOVES = {
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

PLANTS = ["UNRELATED_CHILD_PATH", "WRONG_TRANSACTION_TREE", "SUCCESSOR_OBJECT_HASH_DRIFT"]


class LifecycleError(RuntimeError):
    pass


def git(*args: str, env: dict[str, str] | None = None, input_data: bytes | None = None) -> bytes:
    return subprocess.check_output(
        ["git", "-C", str(ROOT), *args], env=env, input=input_data
    )


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json(payload: Any) -> bytes:
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def tree_blob(commit: str, path: str) -> bytes:
    try:
        return git("show", f"{commit}:{path}")
    except subprocess.CalledProcessError as exc:
        raise LifecycleError(f"P9_SUCCESSOR_TRANSACTION_OBJECT_MISSING:{path}") from exc


def tree_entry(commit: str, path: str) -> tuple[str, str, str] | None:
    raw = git("ls-tree", commit, "--", path).decode().strip()
    if not raw:
        return None
    mode, kind, oid = raw.split("\t", 1)[0].split()
    return mode, kind, oid


def file_object(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    mode = "100755" if path.stat().st_mode & stat.S_IXUSR else "100644"
    oid = git("hash-object", "-w", "--stdin", input_data=data).decode().strip()
    return {"mode": mode, "oid": oid, "sha256": sha256(data), "byte_size": len(data)}


def transaction_paths() -> list[str]:
    return sorted(
        item.decode("utf-8", "surrogateescape")
        for item in git(
            "diff",
            "--no-renames",
            "--name-only",
            "-z",
            BASELINE_COMMIT,
            TRANSACTION_COMMIT,
            "--",
        ).split(b"\0")
        if item
    )


def transaction_artifacts() -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for path, expected_hash in sorted(ORIGINAL_ARTIFACT_HASHES.items()):
        data = tree_blob(TRANSACTION_COMMIT, path)
        entry = tree_entry(TRANSACTION_COMMIT, path)
        if entry is None or entry[1] != "blob" or sha256(data) != expected_hash:
            raise LifecycleError(f"P9_SUCCESSOR_ORIGINAL_ARTIFACT_DRIFT:{path}")
        rows[path] = {
            "mode": entry[0],
            "oid": entry[2],
            "sha256": expected_hash,
            "byte_size": len(data),
        }
    return rows


def original_transaction_receipt() -> dict[str, Any]:
    return json.loads(
        tree_blob(
            TRANSACTION_COMMIT,
            "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_RECEIPT_v1.json",
        )
    )


def verify_foreign_dirty_snapshot() -> str:
    snapshot = original_transaction_receipt().get("foreign_dirty_snapshot")
    if not isinstance(snapshot, list):
        raise LifecycleError("P9_SUCCESSOR_FOREIGN_SNAPSHOT_MISSING")
    for expected in snapshot:
        path = ROOT / expected["path"]
        if not path.is_file() or path.is_symlink():
            raise LifecycleError(f"P9_SUCCESSOR_FOREIGN_DIRTY_DRIFT:{expected['path']}")
        data = path.read_bytes()
        actual = {
            "path": expected["path"],
            "kind": "file",
            "mode": stat.S_IMODE(path.stat().st_mode),
            "sha256": sha256(data),
            "byte_size": len(data),
        }
        if actual != expected:
            raise LifecycleError(f"P9_SUCCESSOR_FOREIGN_DIRTY_DRIFT:{expected['path']}")
    return sha256(canonical_json(snapshot))


def executed_moves() -> list[dict[str, Any]]:
    old_receipt = original_transaction_receipt()
    rows = {row["source"]: row for row in old_receipt.get("cohort", [])}
    if set(rows) != set(EXPECTED_MOVES):
        raise LifecycleError("P9_SUCCESSOR_MOVE_SET_DRIFT")
    result: list[dict[str, Any]] = []
    for source, target in sorted(EXPECTED_MOVES.items()):
        row = rows[source]
        if row.get("target") != target or row.get("status") != "EXECUTED":
            raise LifecycleError(f"P9_SUCCESSOR_MOVE_MAPPING_DRIFT:{source}")
        source_entry = tree_entry(TRANSACTION_COMMIT, source)
        target_entry = tree_entry(TRANSACTION_COMMIT, target)
        data = tree_blob(TRANSACTION_COMMIT, target)
        if source_entry is not None or target_entry is None:
            raise LifecycleError(f"P9_SUCCESSOR_MOVE_TREE_DRIFT:{source}")
        if (
            target_entry[0] != row["git_mode"]
            or target_entry[1] != "blob"
            or target_entry[2] != row["source_oid"]
            or sha256(data) != row["sha256"]
            or len(data) != row["byte_size"]
        ):
            raise LifecycleError(f"P9_SUCCESSOR_MOVE_OBJECT_DRIFT:{source}")
        result.append(
            {
                "source": source,
                "target": target,
                "mode": row["git_mode"],
                "oid": row["source_oid"],
                "sha256": row["sha256"],
                "byte_size": row["byte_size"],
            }
        )
    return result


def apply_objects(base: str, objects: dict[str, dict[str, Any]]) -> str:
    with tempfile.TemporaryDirectory() as td:
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(Path(td) / "index")
        subprocess.run(["git", "-C", str(ROOT), "read-tree", base], env=env, check=True)
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


def synthetic_child(base_tree: str, path: str, data: bytes, mode: str = "100644") -> str:
    oid = git("hash-object", "-w", "--stdin", input_data=data).decode().strip()
    tree = apply_objects(
        base_tree,
        {path: {"mode": mode, "oid": oid, "sha256": sha256(data), "byte_size": len(data)}},
    )
    return git("commit-tree", tree, "-p", TRANSACTION_COMMIT, "-m", "P9 successor plant").decode().strip()


def assemble_receipt() -> dict[str, Any]:
    parent = git("rev-parse", f"{TRANSACTION_COMMIT}^").decode().strip()
    tree = git("rev-parse", f"{TRANSACTION_COMMIT}^{{tree}}").decode().strip()
    if parent != BASELINE_COMMIT or tree != TRANSACTION_TREE:
        raise LifecycleError(
            f"P9_SUCCESSOR_TRANSACTION_IDENTITY_DRIFT:parent={parent}:tree={tree}"
        )
    paths = transaction_paths()
    if len(paths) != 26:
        raise LifecycleError(f"P9_SUCCESSOR_TRANSACTION_SCOPE_COUNT_DRIFT:{len(paths)}")
    missing = [path for path in SUCCESSOR_SUPPORT_PATHS if not (ROOT / path).is_file()]
    if missing:
        raise LifecycleError(f"P9_SUCCESSOR_SUPPORT_MISSING:{sorted(missing)}")
    objects = {path: file_object(ROOT / path) for path in sorted(SUCCESSOR_SUPPORT_PATHS)}
    return {
        "schema_version": "q3.root_archive_lifecycle_successor_receipt.v1",
        "status": "CANONICAL_POSTCOMMIT_LIFECYCLE_BOUND",
        "transaction_commit": TRANSACTION_COMMIT,
        "baseline_commit": BASELINE_COMMIT,
        "transaction_tree": TRANSACTION_TREE,
        "transaction_paths_no_renames": paths,
        "transaction_artifacts": transaction_artifacts(),
        "foreign_dirty_snapshot_sha256": verify_foreign_dirty_snapshot(),
        "executed_moves": executed_moves(),
        "successor_objects": objects,
        "expected_successor_tree_excluding_receipt": apply_objects(TRANSACTION_COMMIT, objects),
        "successor_paths": sorted(SUCCESSOR_PATHS),
        "plants": PLANTS,
    }


def validate_schema(payload: dict[str, Any]) -> None:
    try:
        import jsonschema
    except ImportError as exc:
        raise LifecycleError("P9_SUCCESSOR_JSONSCHEMA_UNAVAILABLE") from exc
    try:
        jsonschema.Draft202012Validator(json.loads(SCHEMA.read_text())).validate(payload)
    except jsonschema.ValidationError as exc:
        raise LifecycleError(f"P9_SUCCESSOR_SCHEMA_INVALID:{exc.message}") from exc


def expected_final_tree(payload: dict[str, Any]) -> str:
    return apply_objects(
        payload["expected_successor_tree_excluding_receipt"],
        {str(RECEIPT.relative_to(ROOT)): file_object(RECEIPT)},
    )


def verify_payload(payload: dict[str, Any]) -> None:
    validate_schema(payload)
    expected = assemble_receipt()
    if payload != expected:
        raise LifecycleError("P9_SUCCESSOR_RECEIPT_DRIFT")


def validate_canonical_state(
    *,
    head: str,
    origin: str,
    parent: str,
    paths: set[str],
    committed_tree: str,
    staged_tree: str,
    final_tree: str,
) -> None:
    if origin != head or parent != TRANSACTION_COMMIT:
        raise LifecycleError(
            f"P9_SUCCESSOR_CANONICAL_HISTORY_DRIFT:head={head}:origin={origin}:parent={parent}"
        )
    if paths != SUCCESSOR_PATHS:
        raise LifecycleError("P9_SUCCESSOR_CANONICAL_SCOPE_DRIFT")
    if committed_tree != final_tree or staged_tree != committed_tree:
        raise LifecycleError("P9_SUCCESSOR_CANONICAL_TREE_DRIFT")


def verify_canonical_commit(head: str, origin: str, final_tree: str) -> None:
    parent = git("rev-parse", f"{head}^").decode().strip()
    committed_tree = git("rev-parse", f"{head}^{{tree}}").decode().strip()
    paths = {
        item.decode("utf-8", "surrogateescape")
        for item in git(
            "diff", "--name-only", "-z", TRANSACTION_COMMIT, head, "--"
        ).split(b"\0")
        if item
    }
    validate_canonical_state(
        head=head,
        origin=origin,
        parent=parent,
        paths=paths,
        committed_tree=committed_tree,
        staged_tree=committed_tree,
        final_tree=final_tree,
    )


def verify_state(payload: dict[str, Any]) -> None:
    verify_payload(payload)
    head = git("rev-parse", "HEAD").decode().strip()
    origin = git("rev-parse", "origin/rh_clean").decode().strip()
    final_tree = expected_final_tree(payload)
    staged_tree = git("write-tree").decode().strip()
    if head == TRANSACTION_COMMIT:
        if origin != TRANSACTION_COMMIT:
            raise LifecycleError("P9_SUCCESSOR_PREFLIGHT_ORIGIN_DRIFT")
        actual_paths = {
            item.decode("utf-8", "surrogateescape")
            for item in git(
                "diff", "--cached", "--name-only", "-z", TRANSACTION_COMMIT, "--"
            ).split(b"\0")
            if item
        }
        if actual_paths != SUCCESSOR_PATHS or staged_tree != final_tree:
            raise LifecycleError("P9_SUCCESSOR_PREFLIGHT_SCOPE_OR_TREE_DRIFT")
        return
    verify_canonical_commit(head, origin, final_tree)
    if staged_tree != git("rev-parse", "HEAD^{tree}").decode().strip():
        raise LifecycleError("P9_SUCCESSOR_CANONICAL_INDEX_DRIFT")


def write_receipt() -> None:
    payload = assemble_receipt()
    validate_schema(payload)
    RECEIPT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def run_plants() -> None:
    payload = json.loads(RECEIPT.read_text())
    verify_payload(payload)
    unrelated = json.loads(json.dumps(payload))
    unrelated["successor_paths"][0] = "README.md"
    try:
        verify_payload(unrelated)
    except LifecycleError as exc:
        if str(exc) != "P9_SUCCESSOR_RECEIPT_DRIFT":
            raise
    else:
        raise LifecycleError("P9_SUCCESSOR_PLANT_ESCAPED:UNRELATED_CHILD_PATH")
    wrong_tree = json.loads(json.dumps(payload))
    wrong_tree["transaction_tree"] = "0" * 40
    try:
        verify_payload(wrong_tree)
    except LifecycleError as exc:
        if str(exc) != "P9_SUCCESSOR_RECEIPT_DRIFT":
            raise
    else:
        raise LifecycleError("P9_SUCCESSOR_PLANT_ESCAPED:WRONG_TRANSACTION_TREE")
    wrong_hash = json.loads(json.dumps(payload))
    path = next(iter(wrong_hash["successor_objects"]))
    wrong_hash["successor_objects"][path]["sha256"] = "0" * 64
    try:
        verify_payload(wrong_hash)
    except LifecycleError as exc:
        if str(exc) != "P9_SUCCESSOR_RECEIPT_DRIFT":
            raise
    else:
        raise LifecycleError("P9_SUCCESSOR_PLANT_ESCAPED:SUCCESSOR_OBJECT_HASH_DRIFT")
    wrong_mode = json.loads(json.dumps(payload))
    path = next(iter(wrong_mode["successor_objects"]))
    wrong_mode["successor_objects"][path]["mode"] = "100755"
    try:
        verify_payload(wrong_mode)
    except LifecycleError as exc:
        if str(exc) != "P9_SUCCESSOR_RECEIPT_DRIFT":
            raise
    else:
        raise LifecycleError("P9_SUCCESSOR_PLANT_ESCAPED:SUCCESSOR_OBJECT_MODE_DRIFT")
    final_tree = expected_final_tree(payload)
    unrelated_commit = synthetic_child(final_tree, "README.md", b"unrelated child plant\n")
    try:
        verify_canonical_commit(unrelated_commit, unrelated_commit, final_tree)
    except LifecycleError as exc:
        if str(exc) != "P9_SUCCESSOR_CANONICAL_SCOPE_DRIFT":
            raise
    else:
        raise LifecycleError("P9_SUCCESSOR_PLANT_ESCAPED:UNRELATED_CHILD_PATH_STATE")
    wrong_tree_commit = synthetic_child(
        final_tree, str(CHECKER.relative_to(ROOT)), b"wrong committed tree plant\n"
    )
    try:
        verify_canonical_commit(wrong_tree_commit, wrong_tree_commit, final_tree)
    except LifecycleError as exc:
        if str(exc) != "P9_SUCCESSOR_CANONICAL_TREE_DRIFT":
            raise
    else:
        raise LifecycleError("P9_SUCCESSOR_PLANT_ESCAPED:WRONG_TRANSACTION_TREE_STATE")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("build", "check", "plants"))
    args = parser.parse_args()
    try:
        if args.command == "build":
            write_receipt()
            print("ROOT_ARCHIVE_LIFECYCLE_SUCCESSOR_BUILD_PASS")
        elif args.command == "check":
            verify_state(json.loads(RECEIPT.read_text()))
            print("ROOT_ARCHIVE_LIFECYCLE_SUCCESSOR_CHECK_PASS")
        else:
            run_plants()
            print("ROOT_ARCHIVE_LIFECYCLE_SUCCESSOR_PLANTS_PASS")
    except (OSError, json.JSONDecodeError, LifecycleError, subprocess.CalledProcessError) as exc:
        print(f"ROOT_ARCHIVE_LIFECYCLE_SUCCESSOR_FAIL:{exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
