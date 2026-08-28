from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "root_archive_lifecycle_successor",
    ROOT / "orchestrator/root_archive_lifecycle_successor.py",
)
assert SPEC and SPEC.loader
pm = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pm)


def receipt() -> dict:
    return json.loads(pm.RECEIPT.read_text())


def test_transaction_identity_scope_and_original_artifacts_are_exact() -> None:
    payload = pm.assemble_receipt()
    assert payload["transaction_commit"] == pm.TRANSACTION_COMMIT
    assert payload["baseline_commit"] == pm.BASELINE_COMMIT
    assert payload["transaction_tree"] == pm.TRANSACTION_TREE
    assert len(payload["transaction_paths_no_renames"]) == 26
    assert set(payload["transaction_artifacts"]) == set(pm.ORIGINAL_ARTIFACT_HASHES)
    assert {
        path: row["sha256"] for path, row in payload["transaction_artifacts"].items()
    } == pm.ORIGINAL_ARTIFACT_HASHES


def test_five_moves_remain_exact_and_source_free() -> None:
    rows = {row["source"]: row for row in pm.executed_moves()}
    assert {source: row["target"] for source, row in rows.items()} == pm.EXPECTED_MOVES
    for source, target in pm.EXPECTED_MOVES.items():
        assert pm.tree_entry(pm.TRANSACTION_COMMIT, source) is None
        assert pm.tree_entry(pm.TRANSACTION_COMMIT, target) is not None


def test_receipt_schema_payload_and_candidate_tree_are_exact() -> None:
    payload = receipt()
    pm.verify_payload(payload)
    assert payload == pm.assemble_receipt()
    assert set(payload["successor_objects"]) == pm.SUCCESSOR_SUPPORT_PATHS
    assert set(payload["successor_paths"]) == pm.SUCCESSOR_PATHS
    assert pm.expected_final_tree(payload) == pm.git("write-tree").decode().strip()
    assert payload["foreign_dirty_snapshot_sha256"] == pm.verify_foreign_dirty_snapshot()


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("transaction_tree", "0" * 40),
        ("baseline_commit", "1" * 40),
        ("transaction_commit", "2" * 40),
    ],
)
def test_transaction_identity_poison_is_rejected(field: str, value: str) -> None:
    poisoned = json.loads(json.dumps(receipt()))
    poisoned[field] = value
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_RECEIPT_DRIFT"):
        pm.verify_payload(poisoned)


def test_successor_hash_poison_is_rejected() -> None:
    poisoned = json.loads(json.dumps(receipt()))
    path = next(iter(poisoned["successor_objects"]))
    poisoned["successor_objects"][path]["sha256"] = "0" * 64
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_RECEIPT_DRIFT"):
        pm.verify_payload(poisoned)


@pytest.mark.parametrize(
    ("field", "value"),
    [("transaction_commit", 7), ("transaction_tree", None)],
)
def test_non_string_commit_or_hash_is_schema_rejected(field: str, value: object) -> None:
    poisoned = json.loads(json.dumps(receipt()))
    poisoned[field] = value
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_SCHEMA_INVALID"):
        pm.validate_schema(poisoned)


def test_non_string_successor_hash_is_schema_rejected() -> None:
    poisoned = json.loads(json.dumps(receipt()))
    path = next(iter(poisoned["successor_objects"]))
    poisoned["successor_objects"][path]["sha256"] = 9
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_SCHEMA_INVALID"):
        pm.validate_schema(poisoned)


@pytest.mark.parametrize("field", ["sha256", "mode"])
def test_foreign_byte_or_mode_drift_is_rejected(
    field: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    original = pm.original_transaction_receipt()
    poisoned = json.loads(json.dumps(original))
    poisoned["foreign_dirty_snapshot"][0][field] = (
        "0" * 64 if field == "sha256" else 0
    )
    monkeypatch.setattr(pm, "original_transaction_receipt", lambda: poisoned)
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_FOREIGN_DIRTY_DRIFT"):
        pm.verify_foreign_dirty_snapshot()


def test_actual_unrelated_child_and_wrong_tree_commits_are_rejected() -> None:
    tree = pm.expected_final_tree(receipt())
    unrelated = pm.synthetic_child(tree, "README.md", b"unrelated child test\n")
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_CANONICAL_SCOPE_DRIFT"):
        pm.verify_canonical_commit(unrelated, unrelated, tree)
    wrong_tree = pm.synthetic_child(
        tree, str(pm.CHECKER.relative_to(ROOT)), b"wrong committed tree test\n"
    )
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_CANONICAL_TREE_DRIFT"):
        pm.verify_canonical_commit(wrong_tree, wrong_tree, tree)


def test_wrong_parent_or_origin_is_rejected() -> None:
    tree = pm.expected_final_tree(receipt())
    with pytest.raises(pm.LifecycleError, match="P9_SUCCESSOR_CANONICAL_HISTORY_DRIFT"):
        pm.validate_canonical_state(
            head="1" * 40,
            origin="2" * 40,
            parent="3" * 40,
            paths=set(pm.SUCCESSOR_PATHS),
            committed_tree=tree,
            staged_tree=tree,
            final_tree=tree,
        )
