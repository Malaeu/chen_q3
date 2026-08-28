#!/usr/bin/env python3
"""Evergreen historical verifier for the closed P9/P10 quarantine chain."""

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
P9_ARCHIVE = "c450773bd63b295439df2174da12fafa16958f1f"
P9_LIFECYCLE = "a9934dc476a26f29d232749a3ec5c272109aa810"
P10_TOPOLOGY = "72377c2a12b17a3590b5f460b039e9cbe4d6d9b7"

TRANSACTION_SPECS = (
    {
        "id": "P9_ARCHIVE_TRANSACTION",
        "commit": P9_ARCHIVE,
        "parent": "1c5988c3d97c46c1cb97bdb8a7019fd52a429c1f",
        "tree": "cc0717eea10b9ea00c50c0db8b8870de11fd80d1",
        "path_count": 26,
    },
    {
        "id": "P9_ARCHIVE_LIFECYCLE_SUCCESSOR",
        "commit": P9_LIFECYCLE,
        "parent": P9_ARCHIVE,
        "tree": "79289a2bc967edb3533949101aeb4c8329491bb0",
        "path_count": 5,
    },
    {
        "id": "P10_REPOSITORY_TOPOLOGY",
        "commit": P10_TOPOLOGY,
        "parent": P9_LIFECYCLE,
        "tree": "3f13ce024eedfb116830e144475aef4d457558c4",
        "path_count": 8,
    },
)

P10_PATHS = frozenset(
    {
        "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_DECISION_SCHEMA_v1.json",
        "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_DECISION_v1.json",
        "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_RATIONALE_v1.md",
        "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_RECEIPT_SCHEMA_v1.json",
        "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_RECEIPT_v1.json",
        "orchestrator/repository_topology_decision.py",
        "orchestrator/tests/test_repository_topology_decision.py",
        "scripts/check_repository_topology_decision.sh",
    }
)

SCHEMA = ROOT / "docs/semantic_quarantine/SEMANTIC_QUARANTINE_HISTORY_SUCCESSOR_SCHEMA_v1.json"
RECEIPT = ROOT / "docs/semantic_quarantine/SEMANTIC_QUARANTINE_HISTORY_SUCCESSOR_RECEIPT_v1.json"
CHECKER = Path(__file__).resolve()
TESTS = ROOT / "orchestrator/tests/test_semantic_quarantine_history_successor.py"
WRAPPER = ROOT / "scripts/check_semantic_quarantine_history_successor.sh"
SUPPORT_PATHS = frozenset(str(path.relative_to(ROOT)) for path in (SCHEMA, CHECKER, TESTS, WRAPPER))
SUCCESSOR_PATHS = SUPPORT_PATHS | {str(RECEIPT.relative_to(ROOT))}

PLANTS = [
    "WRONG_TRANSACTION_PARENT",
    "WRONG_TRANSACTION_TREE",
    "WRONG_TRANSACTION_SCOPE",
    "WRONG_TRANSACTION_ARTIFACT",
    "WRONG_ANCESTRY_ORDER",
    "TOPOLOGY_NOT_ANCESTOR",
    "UNRELATED_PRECOMMIT_STAGED_PATH",
    "DUPLICATE_JSON_KEY",
    "NONCANONICAL_JSON_BYTES",
    "CANONICAL_FIRST_PARENT_MERGE",
]


class HistoryError(RuntimeError):
    pass


def git(*args: str, env: dict[str, str] | None = None, input_data: bytes | None = None) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], env=env, input=input_data)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_digest(payload: Any) -> bytes:
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def artifact_json(payload: Any) -> bytes:
    return (json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def strict_json(data: bytes, code: str) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise HistoryError(f"{code}_DUPLICATE_KEY:{key}")
            result[key] = value
        return result

    try:
        return json.loads(data, object_pairs_hook=pairs_hook)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HistoryError(f"{code}_JSON_INVALID") from exc


def parse_artifact(data: bytes, code: str) -> Any:
    payload = strict_json(data, code)
    if data != artifact_json(payload):
        raise HistoryError(f"{code}_NONCANONICAL_BYTES")
    return payload


def load_artifact(path: Path, code: str) -> Any:
    return parse_artifact(path.read_bytes(), code)


def tree_blob(commit: str, path: str) -> bytes:
    try:
        return git("show", f"{commit}:{path}")
    except subprocess.CalledProcessError as exc:
        raise HistoryError(f"HISTORY_OBJECT_MISSING:{commit}:{path}") from exc


def tree_entry(commit: str, path: str) -> tuple[str, str, str] | None:
    raw = git("ls-tree", commit, "--", path).decode().strip()
    if not raw:
        return None
    mode, kind, oid = raw.split("\t", 1)[0].split()
    return mode, kind, oid


def changed_paths(parent: str, commit: str) -> list[str]:
    return sorted(
        item.decode("utf-8", "surrogateescape")
        for item in git("diff", "--no-renames", "--name-only", "-z", parent, commit, "--").split(
            b"\0"
        )
        if item
    )


def transaction_artifact(commit: str, path: str) -> dict[str, Any]:
    entry = tree_entry(commit, path)
    if entry is None:
        return {"kind": "absent"}
    if entry[1] != "blob":
        raise HistoryError(f"HISTORY_NONBLOB_ARTIFACT:{commit}:{path}")
    data = tree_blob(commit, path)
    return {
        "kind": "blob",
        "mode": entry[0],
        "oid": entry[2],
        "sha256": sha256(data),
        "byte_size": len(data),
    }


def transaction_record(spec: dict[str, Any]) -> dict[str, Any]:
    commit = spec["commit"]
    parent = git("rev-parse", f"{commit}^").decode().strip()
    tree = git("rev-parse", f"{commit}^{{tree}}").decode().strip()
    if parent != spec["parent"]:
        raise HistoryError(f"HISTORY_PARENT_DRIFT:{spec['id']}")
    if tree != spec["tree"]:
        raise HistoryError(f"HISTORY_TREE_DRIFT:{spec['id']}")
    paths = changed_paths(parent, commit)
    if len(paths) != spec["path_count"]:
        raise HistoryError(f"HISTORY_SCOPE_COUNT_DRIFT:{spec['id']}:{len(paths)}")
    if spec["id"] == "P10_REPOSITORY_TOPOLOGY" and set(paths) != P10_PATHS:
        raise HistoryError("HISTORY_P10_SCOPE_DRIFT")
    return {
        "id": spec["id"],
        "commit": commit,
        "parent": parent,
        "tree": tree,
        "paths": paths,
        "artifacts": {path: transaction_artifact(commit, path) for path in paths},
    }


def verify_ancestry_order(head: str) -> None:
    order = (P9_ARCHIVE, P9_LIFECYCLE, P10_TOPOLOGY, head)
    for ancestor, descendant in zip(order, order[1:]):
        result = subprocess.run(
            ["git", "-C", str(ROOT), "merge-base", "--is-ancestor", ancestor, descendant],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if result.returncode:
            raise HistoryError(f"HISTORY_ANCESTRY_ORDER_DRIFT:{ancestor}:{descendant}")
    first_parent = git("rev-list", "--first-parent", head).decode().splitlines()
    if P10_TOPOLOGY not in first_parent:
        raise HistoryError("HISTORY_TOPOLOGY_NOT_FIRST_PARENT_ANCESTOR")


def file_object(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    mode = "100755" if path.stat().st_mode & stat.S_IXUSR else "100644"
    oid = git("hash-object", "-w", "--stdin", input_data=data).decode().strip()
    return {"mode": mode, "oid": oid, "sha256": sha256(data), "byte_size": len(data)}


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


def dirty_paths() -> list[str]:
    raw = git("status", "--porcelain=v1", "-z", "--untracked-files=all")
    fields = raw.split(b"\0")
    paths: list[str] = []
    index = 0
    while index < len(fields):
        field = fields[index]
        index += 1
        if not field:
            continue
        status_code = field[:2].decode()
        path = field[3:].decode("utf-8", "surrogateescape")
        if "R" in status_code or "C" in status_code:
            if index >= len(fields):
                raise HistoryError("HISTORY_DIRTY_RENAME_PARSE_FAIL")
            index += 1
        if path not in SUCCESSOR_PATHS:
            paths.append(path)
    return sorted(paths)


def path_snapshot(path_text: str) -> dict[str, Any]:
    path = ROOT / path_text
    try:
        info = path.lstat()
    except FileNotFoundError:
        return {
            "path": path_text,
            "kind": "absent",
            "mode": 0,
            "sha256": sha256(b""),
            "byte_size": 0,
        }
    if stat.S_ISREG(info.st_mode):
        kind, data = "file", path.read_bytes()
    elif stat.S_ISLNK(info.st_mode):
        kind, data = "symlink", os.readlink(path).encode()
    else:
        raise HistoryError(f"HISTORY_FOREIGN_UNSUPPORTED_TYPE:{path_text}")
    return {
        "path": path_text,
        "kind": kind,
        "mode": stat.S_IMODE(info.st_mode),
        "sha256": sha256(data),
        "byte_size": len(data),
    }


def current_foreign_snapshot() -> list[dict[str, Any]]:
    return [path_snapshot(path) for path in dirty_paths()]


def support_objects() -> dict[str, dict[str, Any]]:
    missing = [path for path in SUPPORT_PATHS if not (ROOT / path).is_file()]
    if missing:
        raise HistoryError(f"HISTORY_SUPPORT_MISSING:{sorted(missing)}")
    return {path: file_object(ROOT / path) for path in sorted(SUPPORT_PATHS)}


def expected_receipt() -> dict[str, Any]:
    transactions = [transaction_record(spec) for spec in TRANSACTION_SPECS]
    objects = support_objects()
    foreign = current_foreign_snapshot()
    return {
        "schema_version": "q3.semantic_quarantine_history_successor.v1",
        "status": "P9_P10_HISTORY_BOUND_DESCENDANTS_ALLOWED",
        "topology_commit": P10_TOPOLOGY,
        "transactions": transactions,
        "transaction_chain_digest": sha256(canonical_digest(transactions)),
        "superseded_transaction_state_wrappers": [
            "scripts/check_root_archive_preflight.sh",
            "scripts/check_root_archive_lifecycle_successor.sh",
            "scripts/check_repository_topology_decision.sh",
        ],
        "canonical_future_wrapper": "scripts/check_semantic_quarantine_history_successor.sh",
        "no_second_state_lifecycle": True,
        "descendant_policy": "ARBITRARY_DESCENDANTS_AND_STAGED_CHANGES_ALLOWED_NOT_ATTESTED",
        "precommit_foreign_snapshot": foreign,
        "precommit_foreign_snapshot_sha256": sha256(canonical_digest(foreign)),
        "successor_objects": objects,
        "prospective_tree_excluding_receipt": apply_objects(P10_TOPOLOGY, objects),
        "successor_paths": sorted(SUCCESSOR_PATHS),
        "plants": PLANTS,
    }


def validate_schema(payload: dict[str, Any], schema_bytes: bytes | None = None) -> None:
    try:
        import jsonschema
    except ImportError as exc:
        raise HistoryError("HISTORY_JSONSCHEMA_UNAVAILABLE") from exc
    schema = strict_json(
        SCHEMA.read_bytes() if schema_bytes is None else schema_bytes,
        "HISTORY_SCHEMA",
    )
    try:
        jsonschema.Draft202012Validator(schema).validate(payload)
    except jsonschema.ValidationError as exc:
        raise HistoryError(f"HISTORY_SCHEMA_INVALID:{exc.message}") from exc


def verify_payload(payload: dict[str, Any], *, verify_foreign: bool) -> None:
    expected = expected_receipt()
    if not verify_foreign:
        expected["precommit_foreign_snapshot"] = payload["precommit_foreign_snapshot"]
        expected["precommit_foreign_snapshot_sha256"] = payload["precommit_foreign_snapshot_sha256"]
    verify_precommit_candidate(
        payload,
        expected,
        expected["precommit_foreign_snapshot"],
    )


def verify_precommit_candidate(
    payload: dict[str, Any],
    expected: dict[str, Any],
    actual_snapshot: list[dict[str, Any]],
) -> None:
    validate_schema(payload)
    verify_precommit_foreign_snapshot(payload, actual_snapshot)
    if payload != expected:
        raise HistoryError("HISTORY_RECEIPT_DRIFT")


def verify_frozen_foreign_snapshot(payload: dict[str, Any]) -> None:
    snapshot = payload["precommit_foreign_snapshot"]
    if payload["precommit_foreign_snapshot_sha256"] != sha256(canonical_digest(snapshot)):
        raise HistoryError("HISTORY_FOREIGN_SNAPSHOT_DIGEST_DRIFT")


def verify_precommit_foreign_snapshot(
    payload: dict[str, Any], actual_snapshot: list[dict[str, Any]]
) -> None:
    verify_frozen_foreign_snapshot(payload)
    if payload["precommit_foreign_snapshot"] != actual_snapshot:
        raise HistoryError("HISTORY_FOREIGN_SNAPSHOT_DRIFT")


def object_record(data: bytes, mode: str = "100644") -> dict[str, Any]:
    oid = git("hash-object", "-w", "--stdin", input_data=data).decode().strip()
    return {"mode": mode, "oid": oid, "sha256": sha256(data), "byte_size": len(data)}


def frozen_final_tree(payload: dict[str, Any], receipt_bytes: bytes) -> str:
    prospective = apply_objects(P10_TOPOLOGY, payload["successor_objects"])
    if prospective != payload["prospective_tree_excluding_receipt"]:
        raise HistoryError("HISTORY_FROZEN_PROSPECTIVE_TREE_DRIFT")
    return apply_objects(
        prospective,
        {str(RECEIPT.relative_to(ROOT)): object_record(receipt_bytes)},
    )


def expected_final_tree() -> str:
    payload = load_artifact(RECEIPT, "HISTORY_RECEIPT")
    return apply_objects(
        payload["prospective_tree_excluding_receipt"],
        {str(RECEIPT.relative_to(ROOT)): file_object(RECEIPT)},
    )


def first_descendant(head: str) -> str:
    commits = [
        item
        for item in git("rev-list", "--first-parent", "--reverse", f"{P10_TOPOLOGY}..{head}")
        .decode()
        .splitlines()
        if item
    ]
    if not commits:
        raise HistoryError("HISTORY_SUCCESSOR_COMMIT_MISSING")
    return commits[0]


def verify_historical_payload(candidate: dict[str, Any], head: str) -> tuple[str, str]:
    successor = first_descendant(head)
    receipt_path = str(RECEIPT.relative_to(ROOT))
    receipt_bytes = tree_blob(successor, receipt_path)
    committed = parse_artifact(receipt_bytes, "HISTORY_COMMITTED_SUCCESSOR_RECEIPT")
    if candidate != committed:
        raise HistoryError("HISTORY_RECEIPT_COMMIT_DRIFT")
    schema_path = str(SCHEMA.relative_to(ROOT))
    validate_schema(candidate, tree_blob(successor, schema_path))
    verify_frozen_foreign_snapshot(candidate)
    transactions = [transaction_record(spec) for spec in TRANSACTION_SPECS]
    if candidate["transactions"] != transactions:
        raise HistoryError("HISTORY_TRANSACTION_RECEIPT_DRIFT")
    if candidate["transaction_chain_digest"] != sha256(canonical_digest(transactions)):
        raise HistoryError("HISTORY_TRANSACTION_CHAIN_DIGEST_DRIFT")
    if set(candidate["successor_objects"]) != SUPPORT_PATHS:
        raise HistoryError("HISTORY_FROZEN_SUPPORT_SCOPE_DRIFT")
    for path, expected in candidate["successor_objects"].items():
        actual = transaction_artifact(successor, path)
        actual.pop("kind", None)
        if actual != expected:
            raise HistoryError(f"HISTORY_FROZEN_SUPPORT_ARTIFACT_DRIFT:{path}")
    final_tree = frozen_final_tree(candidate, receipt_bytes)
    validate_successor_commit(successor, final_tree)
    return successor, final_tree


def validate_successor_commit(commit: str, final_tree: str) -> None:
    parent = git("rev-parse", f"{commit}^").decode().strip()
    tree = git("rev-parse", f"{commit}^{{tree}}").decode().strip()
    paths = set(changed_paths(parent, commit))
    if parent != P10_TOPOLOGY:
        raise HistoryError("HISTORY_SUCCESSOR_PARENT_DRIFT")
    if tree != final_tree:
        raise HistoryError("HISTORY_SUCCESSOR_TREE_DRIFT")
    if paths != SUCCESSOR_PATHS:
        raise HistoryError("HISTORY_SUCCESSOR_SCOPE_DRIFT")


def validate_precommit_state(paths: set[str], staged_tree: str, final_tree: str) -> None:
    if paths != SUCCESSOR_PATHS or staged_tree != final_tree:
        raise HistoryError("HISTORY_PREFLIGHT_SCOPE_OR_TREE_DRIFT")


def verify_state() -> None:
    head = git("rev-parse", "HEAD").decode().strip()
    origin = git("rev-parse", "origin/rh_clean").decode().strip()
    if head == P10_TOPOLOGY:
        payload = load_artifact(RECEIPT, "HISTORY_RECEIPT")
        if origin != P10_TOPOLOGY:
            raise HistoryError("HISTORY_PREFLIGHT_ORIGIN_DRIFT")
        verify_payload(payload, verify_foreign=True)
        paths = {
            item.decode("utf-8", "surrogateescape")
            for item in git("diff", "--cached", "--name-only", "-z", P10_TOPOLOGY, "--").split(
                b"\0"
            )
            if item
        }
        validate_precommit_state(paths, git("write-tree").decode().strip(), expected_final_tree())
        return
    successor = first_descendant(head)
    payload = parse_artifact(
        tree_blob(successor, str(RECEIPT.relative_to(ROOT))),
        "HISTORY_COMMITTED_SUCCESSOR_RECEIPT",
    )
    verify_historical_payload(payload, head)
    verify_ancestry_order(head)
    if origin != head:
        raise HistoryError("HISTORY_CANONICAL_ORIGIN_DRIFT")
    validate_successor_commit(successor, git("rev-parse", f"{successor}^{{tree}}").decode().strip())


def write_receipt() -> None:
    payload = expected_receipt()
    validate_schema(payload)
    RECEIPT.write_bytes(artifact_json(payload))


def synthetic_commit(base: str, path: str, data: bytes, message: str) -> str:
    oid = git("hash-object", "-w", "--stdin", input_data=data).decode().strip()
    tree = apply_objects(
        git("rev-parse", f"{base}^{{tree}}").decode().strip(),
        {path: {"mode": "100644", "oid": oid, "sha256": sha256(data), "byte_size": len(data)}},
    )
    return git("commit-tree", tree, "-p", base, "-m", message).decode().strip()


def synthetic_merge(first_parent: str, second_parent: str, message: str) -> str:
    tree = git("rev-parse", f"{first_parent}^{{tree}}").decode().strip()
    return (
        git("commit-tree", tree, "-p", first_parent, "-p", second_parent, "-m", message)
        .decode()
        .strip()
    )


def run_plants() -> None:
    head = git("rev-parse", "HEAD").decode().strip()
    precommit = head == P10_TOPOLOGY
    if precommit:
        payload = load_artifact(RECEIPT, "HISTORY_RECEIPT")
        expected = expected_receipt()
        actual_snapshot = current_foreign_snapshot()
        verify_precommit_candidate(payload, expected, actual_snapshot)
    else:
        successor = first_descendant(head)
        payload = parse_artifact(
            tree_blob(successor, str(RECEIPT.relative_to(ROOT))),
            "HISTORY_COMMITTED_SUCCESSOR_RECEIPT",
        )
        verify_historical_payload(payload, head)
    mutations = []
    for field in ("parent", "tree"):
        poisoned = json.loads(json.dumps(payload))
        poisoned["transactions"][2][field] = "0" * 40
        mutations.append(poisoned)
    scope = json.loads(json.dumps(payload))
    scope["transactions"][2]["paths"][0] = "README.md"
    mutations.append(scope)
    artifact = json.loads(json.dumps(payload))
    path = next(iter(artifact["transactions"][2]["artifacts"]))
    artifact["transactions"][2]["artifacts"][path]["sha256"] = "0" * 64
    mutations.append(artifact)
    lifecycle = json.loads(json.dumps(payload))
    lifecycle["no_second_state_lifecycle"] = False
    mutations.append(lifecycle)
    foreign_digest = json.loads(json.dumps(payload))
    foreign_digest["precommit_foreign_snapshot_sha256"] = "0" * 64
    mutations.append(foreign_digest)
    for index, poisoned in enumerate(mutations):
        try:
            if precommit:
                verify_precommit_candidate(poisoned, expected, actual_snapshot)
            else:
                verify_historical_payload(poisoned, head)
        except HistoryError:
            continue
        raise HistoryError(f"HISTORY_PLANT_ESCAPED:{index}")
    poisoned_snapshot = json.loads(json.dumps(payload["precommit_foreign_snapshot"]))
    poisoned_snapshot[0]["sha256"] = "0" * 64
    try:
        verify_precommit_foreign_snapshot(payload, poisoned_snapshot)
    except HistoryError:
        pass
    else:
        raise HistoryError("HISTORY_PLANT_ESCAPED:PRECOMMIT_FOREIGN_SNAPSHOT")
    if precommit:
        final_tree = expected_final_tree()
    else:
        successor = first_descendant(head)
        final_tree = git("rev-parse", f"{successor}^{{tree}}").decode().strip()
    wrong_parent = synthetic_commit(
        P9_LIFECYCLE, "README.md", b"wrong parent plant\n", "wrong parent"
    )
    try:
        validate_successor_commit(wrong_parent, final_tree)
    except HistoryError:
        pass
    else:
        raise HistoryError("HISTORY_PLANT_ESCAPED:WRONG_TRANSACTION_PARENT")
    off_chain = synthetic_commit(P9_ARCHIVE, "README.md", b"off-chain plant\n", "off chain")
    try:
        verify_ancestry_order(off_chain)
    except HistoryError:
        pass
    else:
        raise HistoryError("HISTORY_PLANT_ESCAPED:TOPOLOGY_NOT_ANCESTOR")
    try:
        validate_precommit_state(SUCCESSOR_PATHS | {"README.md"}, final_tree, final_tree)
    except HistoryError:
        pass
    else:
        raise HistoryError("HISTORY_PLANT_ESCAPED:UNRELATED_PRECOMMIT_STAGED_PATH")
    for code, data in (
        ("DUPLICATE", b'{"status":"x","status":"x"}\n'),
        ("WHITESPACE", artifact_json(payload) + b"\n"),
    ):
        try:
            parse_artifact(data, f"HISTORY_PLANT_{code}")
        except HistoryError:
            continue
        raise HistoryError(f"HISTORY_PLANT_ESCAPED:{code}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("build", "check", "plants"))
    args = parser.parse_args()
    try:
        if args.command == "build":
            write_receipt()
            print("SEMANTIC_QUARANTINE_HISTORY_SUCCESSOR_BUILD_PASS")
        elif args.command == "check":
            verify_state()
            print("SEMANTIC_QUARANTINE_HISTORY_SUCCESSOR_CHECK_PASS")
        else:
            run_plants()
            print("SEMANTIC_QUARANTINE_HISTORY_SUCCESSOR_PLANTS_PASS")
    except (OSError, json.JSONDecodeError, HistoryError, subprocess.CalledProcessError) as exc:
        print(f"SEMANTIC_QUARANTINE_HISTORY_SUCCESSOR_FAIL:{exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
