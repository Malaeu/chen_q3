from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "semantic_quarantine_history_successor",
    ROOT / "orchestrator/semantic_quarantine_history_successor.py",
)
assert SPEC and SPEC.loader
pm = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pm)


def receipt() -> dict:
    return pm.load_artifact(pm.RECEIPT, "HISTORY_RECEIPT")


def exact_successor_commit() -> str:
    return (
        pm.git(
            "commit-tree",
            pm.expected_final_tree(),
            "-p",
            pm.P10_TOPOLOGY,
            "-m",
            "semantic quarantine history successor test",
        )
        .decode()
        .strip()
    )


def test_three_transactions_are_exact_and_ordered() -> None:
    rows = receipt()["transactions"]
    assert [row["commit"] for row in rows] == [pm.P9_ARCHIVE, pm.P9_LIFECYCLE, pm.P10_TOPOLOGY]
    assert [row["parent"] for row in rows[1:]] == [pm.P9_ARCHIVE, pm.P9_LIFECYCLE]
    assert [len(row["paths"]) for row in rows] == [26, 5, 8]
    assert set(rows[2]["paths"]) == pm.P10_PATHS
    for row in rows:
        assert pm.git("rev-parse", f"{row['commit']}^{{tree}}").decode().strip() == row["tree"]


def test_all_transaction_paths_have_exact_historical_artifacts() -> None:
    for row in receipt()["transactions"]:
        assert set(row["artifacts"]) == set(row["paths"])
        for path, artifact in row["artifacts"].items():
            assert artifact == pm.transaction_artifact(row["commit"], path)


def test_payload_schema_canonical_bytes_and_precommit_foreign_snapshot() -> None:
    payload = receipt()
    pm.verify_payload(payload, verify_foreign=True)
    assert pm.RECEIPT.read_bytes() == pm.artifact_json(payload)
    assert payload["no_second_state_lifecycle"] is True
    assert payload["precommit_foreign_snapshot"] == pm.current_foreign_snapshot()


def test_exact_successor_then_arbitrary_descendants_are_allowed() -> None:
    successor = exact_successor_commit()
    descendant_one = pm.synthetic_commit(
        successor, "README.md", b"later unrelated descendant\n", "later one"
    )
    descendant_two = pm.synthetic_commit(
        descendant_one,
        "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_RATIONALE_v1.md",
        b"later versioned P10 path change\n",
        "later two",
    )
    pm.verify_ancestry_order(descendant_two)
    assert pm.first_descendant(descendant_two) == successor
    pm.validate_successor_commit(successor, pm.expected_final_tree())


def test_first_parent_successor_survives_legitimate_merge() -> None:
    successor = exact_successor_commit()
    side = pm.synthetic_commit(pm.P10_TOPOLOGY, "README.md", b"side branch\n", "side")
    merge = pm.synthetic_merge(successor, side, "legitimate merge")
    assert pm.first_descendant(merge) == successor
    pm.verify_ancestry_order(merge)
    pm.validate_successor_commit(successor, pm.expected_final_tree())


def test_wrong_successor_parent_tree_and_scope_are_rejected() -> None:
    successor = exact_successor_commit()
    wrong_parent = pm.synthetic_commit(
        pm.P9_LIFECYCLE, "README.md", b"wrong parent\n", "wrong parent"
    )
    with pytest.raises(pm.HistoryError, match="SUCCESSOR_PARENT_DRIFT"):
        pm.validate_successor_commit(wrong_parent, pm.expected_final_tree())
    wrong_tree = pm.synthetic_commit(successor, "README.md", b"wrong tree\n", "wrong tree")
    with pytest.raises(pm.HistoryError, match="SUCCESSOR_PARENT_DRIFT|SUCCESSOR_TREE_DRIFT"):
        pm.validate_successor_commit(wrong_tree, pm.expected_final_tree())
    scope_tree = pm.apply_objects(
        pm.P10_TOPOLOGY,
        {"README.md": pm.file_object(ROOT / "README.md")},
    )
    wrong_scope = (
        pm.git("commit-tree", scope_tree, "-p", pm.P10_TOPOLOGY, "-m", "wrong scope")
        .decode()
        .strip()
    )
    with pytest.raises(pm.HistoryError, match="SUCCESSOR_TREE_DRIFT|SUCCESSOR_SCOPE_DRIFT"):
        pm.validate_successor_commit(wrong_scope, scope_tree)


def test_not_ancestor_and_wrong_order_are_rejected() -> None:
    with pytest.raises(pm.HistoryError, match="ANCESTRY_ORDER_DRIFT"):
        pm.verify_ancestry_order(pm.P9_LIFECYCLE)
    off_chain = pm.synthetic_commit(pm.P9_ARCHIVE, "README.md", b"off chain\n", "off chain")
    with pytest.raises(pm.HistoryError, match="ANCESTRY_ORDER_DRIFT"):
        pm.verify_ancestry_order(off_chain)


def test_payload_mutations_duplicate_keys_and_whitespace_are_rejected() -> None:
    payload = receipt()
    poisoned = json.loads(json.dumps(payload))
    poisoned["transactions"][2]["tree"] = "0" * 40
    with pytest.raises(pm.HistoryError, match="HISTORY_RECEIPT_DRIFT"):
        pm.verify_payload(poisoned, verify_foreign=True)
    with pytest.raises(pm.HistoryError, match="DUPLICATE_KEY"):
        pm.parse_artifact(b'{"status":"x","status":"x"}\n', "TEST")
    with pytest.raises(pm.HistoryError, match="NONCANONICAL_BYTES"):
        pm.parse_artifact(pm.artifact_json(payload) + b"\n", "TEST")


def test_precommit_unrelated_staged_path_is_not_in_successor_scope() -> None:
    assert "README.md" not in pm.SUCCESSOR_PATHS
    assert set(receipt()["successor_paths"]) == pm.SUCCESSOR_PATHS
    with pytest.raises(pm.HistoryError, match="PREFLIGHT_SCOPE_OR_TREE_DRIFT"):
        pm.validate_precommit_state(
            pm.SUCCESSOR_PATHS | {"README.md"},
            pm.expected_final_tree(),
            pm.expected_final_tree(),
        )


def test_plants_fire() -> None:
    pm.run_plants()
