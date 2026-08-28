from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "repository_topology_decision", ROOT / "orchestrator/repository_topology_decision.py"
)
assert SPEC and SPEC.loader
pm = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pm)


def decision() -> dict:
    return json.loads(pm.DECISION.read_text())


def receipt() -> dict:
    return json.loads(pm.RECEIPT.read_text())


def test_exact_no_new_repo_decision_and_five_zones() -> None:
    payload = decision()
    pm.verify_decision(payload)
    assert payload["selected_pattern"] == "STRANGLER_MONOREPO_WITH_IMPORT_FIREWALL"
    assert payload["create_new_repository_now"] is False
    assert payload["physical_extraction_authorized"] is False
    assert payload["public_claim_boundary"] == {
        "default_target": "CONDITIONAL_COMPILED",
        "public_canonical_export": "OPEN_CONDITIONAL",
        "route_b": "CHALLENGER_NOT_RH",
        "unconditional_rh_proof": False,
    }
    assert payload["state_authority_policy"] == {
        "authoritative_state": "orchestrator/state/PROJECT_STATE.json",
        "duplicate_lifecycle_authorized": False,
        "selector_writes_to_superseded_authority_authorized": False,
    }
    assert {row["id"] for row in payload["zones"]} == {
        "PUBLIC_CORE",
        "ROUTE_B",
        "PROOF_CERTIFICATES",
        "Q3_DISCOVERY",
        "LEGACY_ARCHIVE",
    }
    assert all(row["split_now"] is False for row in payload["zones"])


def test_zone_dispositions_are_exact() -> None:
    zones = {row["id"]: row["disposition"] for row in decision()["zones"]}
    assert zones == {
        "PUBLIC_CORE": "KEEP_PROOF_MONOREPO_WITH_HARD_FIREWALL",
        "ROUTE_B": "DO_NOT_SPLIT_LIVE_CHALLENGER",
        "PROOF_CERTIFICATES": "DO_NOT_SPLIT_FROM_CONSUMERS",
        "Q3_DISCOVERY": "HOLD_SAME_REPO_SHADOW_SIDECAR",
        "LEGACY_ARCHIVE": "HOLD_QUARANTINED_IN_PLACE",
    }


def test_future_gate_candidates_are_unique_and_exact() -> None:
    rows = decision()["future_split_gates"]
    assert [row["candidate"] for row in rows] == [
        "PUBLIC_CORE_EMERGENCY_EXTRACTION",
        "ROUTE_B",
        "Q3_DISCOVERY",
        "LEGACY_ARCHIVE",
    ]
    assert rows[0]["status"] == "NOT_TRIGGERED"
    assert rows[1]["status"] == "FORBIDDEN_LIVE"
    assert rows[2]["status"] == rows[3]["status"] == "HOLD_GATES_OPEN"
    authority_gates = {
        "AUTHORITATIVE_STATE_MIGRATION_COMPLETE",
        "ZERO_SELECTOR_WRITES_TO_SUPERSEDED_AUTHORITY",
        "SINGLE_LIFECYCLE_VALIDATOR_PASS",
    }
    for row in rows[:3]:
        assert authority_gates <= set(row["required_gates"])


def test_evidence_ids_paths_commits_and_hashes_are_exact_git_objects() -> None:
    expected = pm.evidence_pins()
    assert decision()["evidence_pins"] == expected
    assert len({row["id"] for row in expected}) == len(pm.EVIDENCE_SPECS)
    for row in expected:
        assert pm.sha256(pm.tree_blob(row["commit"], row["path"])) == row["sha256"]


def test_p2_through_p9_and_successor_are_bound() -> None:
    phases = {row["phase"] for row in decision()["evidence_pins"]}
    assert {"P2", "P3", "P4", "P5", "P6", "P7", "P8", "P9", "P9_SUCCESSOR"} <= phases


def test_firewall_route_and_discovery_semantics_pass_at_pin() -> None:
    pm.verify_semantic_evidence()
    route = json.loads(
        pm.tree_blob(
            pm.BASELINE_COMMIT,
            "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json",
        )
    )
    assert route["architecture"]["route_b_rh_status"] == "NOT_RH"
    assert route["current"]["route_promotion"] is False
    assert route["current"]["rh_claimed"] is False
    evidence = {row["id"]: row for row in decision()["evidence_pins"]}
    assert (
        evidence["P10_SELECTED_GOAL_STATE"]["path"]
        == "orchestrator/state/PROJECT_EXECUTION_STATE.json"
    )
    assert (
        evidence["P10_GOAL058_CONTRACT"]["path"]
        == "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"
    )
    assert evidence["P10_SAME_FAMILY_LEAN_SOURCE"]["path"].endswith("CanonicalRHRouteSkeleton.lean")
    assert evidence["P10_SAME_FAMILY_PROOF_RECEIPT"]["path"].endswith(
        "056_k8_muntz_v3_slot_s2_bridge.answer.md"
    )


def test_receipt_candidate_object_set_hashes_and_tree_are_exact() -> None:
    payload = receipt()
    pm.verify_receipt(payload)
    assert set(payload["candidate_objects"]) == pm.SUPPORT_PATHS
    assert payload["prospective_tree_excluding_receipt"] == pm.apply_objects(
        pm.BASELINE_COMMIT, payload["candidate_objects"]
    )
    final_tree = pm.expected_final_tree(payload)
    assert len(final_tree) == 40
    assert final_tree == pm.apply_objects(
        payload["prospective_tree_excluding_receipt"],
        {str(pm.RECEIPT.relative_to(pm.ROOT)): pm.file_object(pm.RECEIPT)},
    )
    assert payload["foreign_dirty_snapshot"] == pm.original_foreign_dirty_snapshot()
    assert payload["foreign_dirty_snapshot_sha256"] == pm.sha256(
        pm.canonical_json(payload["foreign_dirty_snapshot"])
    )


@pytest.mark.parametrize(
    "mutator",
    [
        lambda p: p.__setitem__("create_new_repository_now", True),
        lambda p: p["zones"][1].__setitem__("disposition", "SPLIT_NOW"),
        lambda p: p["zones"][2].__setitem__("split_now", True),
        lambda p: p["future_split_gates"][2].__setitem__("status", "NOT_TRIGGERED"),
        lambda p: p["evidence_pins"][0].__setitem__("path", "README.md"),
        lambda p: p["state_authority_policy"].__setitem__("duplicate_lifecycle_authorized", True),
        lambda p: p["public_claim_boundary"].__setitem__("unconditional_rh_proof", True),
    ],
)
def test_semantic_decision_poison_is_rejected(mutator) -> None:
    poisoned = json.loads(json.dumps(decision()))
    mutator(poisoned)
    with pytest.raises(pm.TopologyError):
        pm.verify_decision(poisoned)


def test_duplicate_zone_and_gate_ids_are_rejected_by_exact_contract() -> None:
    poisoned = json.loads(json.dumps(decision()))
    poisoned["zones"][1]["id"] = "PUBLIC_CORE"
    with pytest.raises(pm.TopologyError, match="P10_DECISION_DRIFT"):
        pm.verify_decision(poisoned)
    poisoned = json.loads(json.dumps(decision()))
    poisoned["future_split_gates"][1]["candidate"] = "PUBLIC_CORE_EMERGENCY_EXTRACTION"
    with pytest.raises(pm.TopologyError, match="P10_DECISION_DRIFT"):
        pm.verify_decision(poisoned)


def test_missing_or_extra_evidence_pin_is_rejected() -> None:
    missing = json.loads(json.dumps(decision()))
    missing["evidence_pins"].pop()
    with pytest.raises(pm.TopologyError):
        pm.verify_decision(missing)
    extra = json.loads(json.dumps(decision()))
    extra["evidence_pins"].append(extra["evidence_pins"][0])
    with pytest.raises(pm.TopologyError):
        pm.verify_decision(extra)


def test_non_string_commit_and_hash_are_schema_rejected() -> None:
    poisoned = json.loads(json.dumps(decision()))
    poisoned["baseline_commit"] = 1
    with pytest.raises(pm.TopologyError, match="P10_DECISION_SCHEMA_INVALID"):
        pm.validate_schema(poisoned, pm.DECISION_SCHEMA, "P10_DECISION")
    poisoned = json.loads(json.dumps(receipt()))
    poisoned["decision_sha256"] = None
    with pytest.raises(pm.TopologyError, match="P10_RECEIPT_SCHEMA_INVALID"):
        pm.validate_schema(poisoned, pm.RECEIPT_SCHEMA, "P10_RECEIPT")


def test_branch_required_check_is_explicitly_open() -> None:
    assert "BRANCH_REQUIRED_CHECK_REMAINS_OPEN" in decision()["invariants"]
    rationale = pm.RATIONALE.read_text()
    assert (
        "does not\nclaim that GitHub branch protection or required checks have been configured"
        in rationale
    )


def test_single_authority_and_public_open_invariants_are_explicit() -> None:
    invariants = set(decision()["invariants"])
    assert "SINGLE_AUTHORITATIVE_STATE_NO_DUPLICATE_LIFECYCLE" in invariants
    assert "PUBLIC_CANONICAL_EXPORT_REMAINS_CONDITIONAL_OPEN" in invariants
    assert "UNCONDITIONAL_RH_PROOF_FALSE" in invariants


def test_foreign_dirty_byte_mode_or_type_drift_is_rejected() -> None:
    expected = pm.original_foreign_dirty_snapshot()
    for field, value in (("sha256", "0" * 64), ("mode", 0), ("kind", "symlink")):
        poisoned = json.loads(json.dumps(expected))
        poisoned[0][field] = value
        with pytest.raises(pm.TopologyError, match="P10_FOREIGN_DIRTY_DRIFT"):
            pm.verify_foreign_snapshot_rows(expected, poisoned)


def test_duplicate_json_keys_and_noncanonical_bytes_are_rejected() -> None:
    with pytest.raises(pm.TopologyError, match="DUPLICATE_KEY"):
        pm.parse_artifact_json(b'{"schema_version":"x","schema_version":"x"}\n', "P10_TEST")
    with pytest.raises(pm.TopologyError, match="NONCANONICAL_BYTES"):
        pm.parse_artifact_json(pm.artifact_json(decision()) + b"\n", "P10_TEST")


def test_decision_and_receipt_raw_bytes_are_canonical() -> None:
    assert pm.DECISION.read_bytes() == pm.artifact_json(decision())
    assert pm.RECEIPT.read_bytes() == pm.artifact_json(receipt())


def test_plants_all_fire() -> None:
    pm.run_plants()
