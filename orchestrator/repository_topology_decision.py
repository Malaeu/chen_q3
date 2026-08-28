#!/usr/bin/env python3
"""Evidence-bound P10 repository topology decision and receipt checker."""

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
BASELINE_COMMIT = "a9934dc476a26f29d232749a3ec5c272109aa810"

DECISION_SCHEMA = ROOT / "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_DECISION_SCHEMA_v1.json"
DECISION = ROOT / "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_DECISION_v1.json"
RECEIPT_SCHEMA = ROOT / "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_RECEIPT_SCHEMA_v1.json"
RECEIPT = ROOT / "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_RECEIPT_v1.json"
RATIONALE = ROOT / "docs/semantic_quarantine/REPOSITORY_TOPOLOGY_RATIONALE_v1.md"
CHECKER = Path(__file__).resolve()
TESTS = ROOT / "orchestrator/tests/test_repository_topology_decision.py"
WRAPPER = ROOT / "scripts/check_repository_topology_decision.sh"

SUPPORT_PATHS = frozenset(
    str(path.relative_to(ROOT))
    for path in (DECISION_SCHEMA, DECISION, RECEIPT_SCHEMA, RATIONALE, CHECKER, TESTS, WRAPPER)
)
TRANSACTION_PATHS = SUPPORT_PATHS | {str(RECEIPT.relative_to(ROOT))}

EVIDENCE_SPECS = (
    (
        "P2_PUBLIC_EXPORT_RECEIPT",
        "P2",
        "9716df6cab7936fbb442797367b88c6c8aee96ae",
        "docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md",
        "0db7e17e3c31f064bd66d2c6bef4e8992ea4f2fa5bb6555fc0f0875bff14c293",
        "PUBLIC_HONESTY_AND_AXIOM_BOUNDARY",
    ),
    (
        "P3_MODULE_SCHEMA",
        "P3",
        "4d0cde95137dfbf4fc983afc454e53d2fbcd8ac3",
        "docs/semantic_quarantine/MODULE_CLASS_SCHEMA_v1.json",
        "555c47cbb826cd343e0df81f5e59638610b707f3c04283fb7e1a795fa8083920",
        "MODULE_CLASS_CLOSED_ENUM",
    ),
    (
        "P3_MODULE_REGISTRY",
        "P3",
        "4d0cde95137dfbf4fc983afc454e53d2fbcd8ac3",
        "docs/semantic_quarantine/MODULE_CLASS_REGISTRY_v1.json",
        "0ad8a71ec42d123ec8956740b73816d29ccd1662338ea31ec51d8db24c7f0caf",
        "PUBLIC_ROUTE_LEGACY_CLASSIFICATION",
    ),
    (
        "P4_ARCH_FLOOR_QUARANTINE",
        "P4",
        "6eaee9b6f7bed4a09fc034ed017cdfaf2c60b2ee",
        "docs/semantic_quarantine/ARCH_FLOOR_SEMANTIC_QUARANTINE_v1.md",
        "dcb526c556f4dfd4ca3383d5977a294decae3d5c6ac4f4fc588156259ea3b9df",
        "ARCH_FLOOR_SEMANTIC_BOUNDARY",
    ),
    (
        "P5_STATE_SCHEMA",
        "P5",
        "c7cd20c6ceb63fb6f9ffca3c68d080001e6d140e",
        "docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json",
        "50bf0390395411e2b11cf98455e67db1b050452027c24d79ca3f76a9d78dd144",
        "SINGLE_MACHINE_STATE_CONTRACT",
    ),
    (
        "P5_STATUS_REGISTRY",
        "P5",
        "c7cd20c6ceb63fb6f9ffca3c68d080001e6d140e",
        "docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json",
        "042641c0059fda3e82ad193feec5b55c9e7a2d033f6a1a9fd5e8a924210ecd56",
        "STATUS_SURFACE_AUTHORITY",
    ),
    (
        "P6_FIREWALL_POLICY",
        "P6",
        "4b49c8013547cfe0686087beb1b467ac322aacac",
        "docs/semantic_quarantine/IMPORT_FIREWALL_POLICY_v1.json",
        "9aae6afe0068dacca6a8cb20b99fbcbd5f3887fac8a19bebed0361314ce5dc73",
        "PUBLIC_IMPORT_EDGE_POLICY",
    ),
    (
        "P6_FIREWALL_RECEIPT",
        "P6",
        "4b49c8013547cfe0686087beb1b467ac322aacac",
        "docs/semantic_quarantine/IMPORT_FIREWALL_RECEIPT_v1.json",
        "33bbd1a01e836dc865f22c8a4b2e170689a627b383c8a30e01157d40aa31c072",
        "SEMANTIC_DECLARATION_AUDIT_PASS",
    ),
    (
        "P7_PORTABILITY_RECEIPT",
        "P7",
        "d3eb9923e028f5be24890eadd899b8dbc0a510b7",
        "docs/semantic_quarantine/PORTABILITY_RECEIPT_v1.json",
        "c5f8af3e895bfd8019f2cd9e6c1c6e550ac795b3561feb11f12c9ca7496c38ec",
        "PORTABLE_MONOREPO_BOUNDARY",
    ),
    (
        "P8_ROOT_CLASSIFICATION_RECEIPT",
        "P8",
        "190b268fce2380592e323a4f3304e82b56037b1c",
        "docs/semantic_quarantine/ROOT_ARTIFACT_CLASSIFICATION_RECEIPT_v1.json",
        "ba070b4ab0cd1498e2a83e35997249bf1d5cc96f21e90ce3793135220369b844",
        "ROOT_SURFACE_CLASSIFICATION",
    ),
    (
        "P9_ARCHIVE_RECEIPT",
        "P9",
        "c450773bd63b295439df2174da12fafa16958f1f",
        "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_RECEIPT_v1.json",
        "99c8d54feae0f019a182b8aa5439370f198c452c0ee68e993d597d55d482b03e",
        "ZERO_REFERENCE_ARCHIVE_TRANSACTION",
    ),
    (
        "P9_ARCHIVE_UMBRELLA",
        "P9",
        "c450773bd63b295439df2174da12fafa16958f1f",
        "docs/semantic_quarantine/ROOT_ARCHIVE_EXECUTION_UMBRELLA_v1.json",
        "1160da2aa2f5297926edfaf6501aca1f5301c35b778de9f2d83a8d0c29ed57e8",
        "P7_P8_P9_TWO_STAGE_BINDING",
    ),
    (
        "P9_LIFECYCLE_SUCCESSOR",
        "P9_SUCCESSOR",
        BASELINE_COMMIT,
        "docs/semantic_quarantine/ROOT_ARCHIVE_LIFECYCLE_SUCCESSOR_RECEIPT_v1.json",
        "5c718470e8d707edae3180473db2ac8abc6bb1a5f6145989a6eb4cdc77e0d56c",
        "CANONICAL_POSTCOMMIT_BINDING",
    ),
    (
        "P10_TOPOLOGY_SOURCE",
        "P10_SOURCE",
        BASELINE_COMMIT,
        "docs/routeB_bus/proshka/PROSHKA_VERDICT_REPOSITORY_TOPOLOGY_SEMANTIC_QUARANTINE_AND_TODO_2026-08-27.md",
        "724657329593fd161dad8d098cc9ec1f90b4d3dec706c35567aad3810cb0b315",
        "OWNER_RATIFIED_TOPOLOGY_SOURCE",
    ),
    (
        "P10_ROUTE_B_STATE",
        "P10_SOURCE",
        BASELINE_COMMIT,
        "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json",
        "0c747255ff2653c6ff696b1b25af43bf67076d8f49e2980dc9aa297f89d1693c",
        "HISTORICAL_LIVE_CHALLENGER_STATE",
    ),
    (
        "P10_DISCOVERY_MANDATE",
        "P10_SOURCE",
        BASELINE_COMMIT,
        "docs/routeB_bus/proshka/ARSENAL_MANDATE_2026-08-23_MODULAR_DISCOVERY_COMPILER_SHADOW.md",
        "58d736888d788e3fcf7f44b8cdf9d2b15ab79da2ca86db8fbe1a02427cd02f25",
        "SHADOW_SIDECAR_EXTRACTION_CONDITIONAL",
    ),
    (
        "P10_SELECTED_GOAL_STATE",
        "P10_SOURCE",
        BASELINE_COMMIT,
        "orchestrator/state/PROJECT_EXECUTION_STATE.json",
        "b065c763d272256551b3ecdd9014678d11eb796d97ceef15902f26fa064a9657",
        "EXACT_GOAL058_SELECTOR",
    ),
    (
        "P10_GOAL058_CONTRACT",
        "P10_SOURCE",
        BASELINE_COMMIT,
        "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md",
        "eb418123c65320ad54769d8021717594fb4135488201d93f3ff0c88ca35423ff",
        "ONE_FAMILY_STOP_CONTRACT",
    ),
    (
        "P10_SAME_FAMILY_LEAN_SOURCE",
        "P10_SOURCE",
        BASELINE_COMMIT,
        "q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean",
        "2e849d677e0ec771c47a436abdf657690e833e52555af8c8698185e30274536b",
        "TYPED_SAME_COFINAL_GUARD",
    ),
    (
        "P10_SAME_FAMILY_PROOF_RECEIPT",
        "P10_SOURCE",
        BASELINE_COMMIT,
        "docs/routeB_bus/056_k8_muntz_v3_slot_s2_bridge.answer.md",
        "3c6be71662fddcfd7cdef9e4446772816ac9b03862b4c957f7726da607d25baa",
        "LEAN_STANDARD_AXIOM_TRIPLE_RECEIPT",
    ),
)

PLANTS = [
    "NEW_REPOSITORY_NOW_TRUE",
    "DUPLICATE_OR_MISSING_ZONE",
    "ROUTE_B_SPLIT_WHILE_LIVE",
    "CERTIFICATE_CONSUMER_SPLIT",
    "DISCOVERY_EXTRACTION_WITH_OPEN_GATES",
    "LEGACY_EXTRACTION_WITHOUT_ZERO_IMPORTS",
    "EVIDENCE_ID_PATH_OR_HASH_DRIFT",
    "BRANCH_REQUIRED_CHECK_FALSELY_CLOSED",
    "SECOND_LIFECYCLE_AUTHORIZED",
    "FOREIGN_DIRTY_BYTE_MODE_OR_TYPE_DRIFT",
    "DUPLICATE_JSON_KEY",
    "NONCANONICAL_JSON_BYTES",
]

P9_RECEIPT_COMMIT = "c450773bd63b295439df2174da12fafa16958f1f"
P9_RECEIPT_PATH = "docs/semantic_quarantine/ROOT_ARCHIVE_ZERO_REFERENCE_RECEIPT_v1.json"


class TopologyError(RuntimeError):
    pass


def git(*args: str, env: dict[str, str] | None = None, input_data: bytes | None = None) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], env=env, input=input_data)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json(payload: Any) -> bytes:
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def artifact_json(payload: Any) -> bytes:
    return (json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def strict_json(data: bytes, code: str) -> Any:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise TopologyError(f"{code}_DUPLICATE_KEY:{key}")
            result[key] = value
        return result

    try:
        return json.loads(data, object_pairs_hook=reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise TopologyError(f"{code}_JSON_INVALID") from exc


def parse_artifact_json(data: bytes, code: str) -> Any:
    payload = strict_json(data, code)
    if data != artifact_json(payload):
        raise TopologyError(f"{code}_NONCANONICAL_BYTES")
    return payload


def load_artifact_json(path: Path, code: str) -> Any:
    return parse_artifact_json(path.read_bytes(), code)


def tree_blob(commit: str, path: str) -> bytes:
    try:
        return git("show", f"{commit}:{path}")
    except subprocess.CalledProcessError as exc:
        raise TopologyError(f"P10_EVIDENCE_OBJECT_MISSING:{path}") from exc


def file_object(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    mode = "100755" if path.stat().st_mode & stat.S_IXUSR else "100644"
    oid = git("hash-object", "-w", "--stdin", input_data=data).decode().strip()
    return {"mode": mode, "oid": oid, "sha256": sha256(data), "byte_size": len(data)}


def original_foreign_dirty_snapshot() -> list[dict[str, Any]]:
    receipt = strict_json(tree_blob(P9_RECEIPT_COMMIT, P9_RECEIPT_PATH), "P10_P9_RECEIPT")
    snapshot = receipt.get("foreign_dirty_snapshot")
    if not isinstance(snapshot, list):
        raise TopologyError("P10_P9_FOREIGN_DIRTY_SNAPSHOT_MISSING")
    return snapshot


def current_foreign_dirty_snapshot(paths: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for expected in paths:
        path = ROOT / expected["path"]
        try:
            info = path.lstat()
        except FileNotFoundError as exc:
            raise TopologyError(f"P10_FOREIGN_DIRTY_DRIFT:{expected['path']}") from exc
        if stat.S_ISREG(info.st_mode):
            kind = "file"
            data = path.read_bytes()
        elif stat.S_ISLNK(info.st_mode):
            kind = "symlink"
            data = os.readlink(path).encode()
        elif stat.S_ISDIR(info.st_mode):
            kind = "directory"
            data = b""
        else:
            kind = "other"
            data = b""
        rows.append(
            {
                "path": expected["path"],
                "kind": kind,
                "mode": stat.S_IMODE(info.st_mode),
                "sha256": sha256(data),
                "byte_size": len(data),
            }
        )
    return rows


def verify_foreign_snapshot_rows(
    expected: list[dict[str, Any]], current: list[dict[str, Any]]
) -> None:
    if current != expected:
        raise TopologyError("P10_FOREIGN_DIRTY_DRIFT")


def verify_foreign_dirty_snapshot() -> list[dict[str, Any]]:
    expected = original_foreign_dirty_snapshot()
    verify_foreign_snapshot_rows(expected, current_foreign_dirty_snapshot(expected))
    return expected


def evidence_pins() -> list[dict[str, str]]:
    rows = []
    for evidence_id, phase, commit, path, expected_hash, role in EVIDENCE_SPECS:
        data = tree_blob(commit, path)
        if sha256(data) != expected_hash:
            raise TopologyError(f"P10_EVIDENCE_HASH_DRIFT:{evidence_id}")
        if subprocess.run(
            ["git", "-C", str(ROOT), "merge-base", "--is-ancestor", commit, BASELINE_COMMIT],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        ).returncode:
            raise TopologyError(f"P10_EVIDENCE_NOT_ANCESTOR:{evidence_id}")
        rows.append(
            {
                "id": evidence_id,
                "phase": phase,
                "commit": commit,
                "path": path,
                "sha256": expected_hash,
                "role": role,
            }
        )
    return rows


def expected_decision() -> dict[str, Any]:
    return {
        "schema_version": "q3.repository_topology_decision.v1",
        "status": "EVIDENCE_BOUND_NO_NEW_REPO_NOW",
        "baseline_commit": BASELINE_COMMIT,
        "selected_pattern": "STRANGLER_MONOREPO_WITH_IMPORT_FIREWALL",
        "create_new_repository_now": False,
        "physical_extraction_authorized": False,
        "public_claim_boundary": {
            "unconditional_rh_proof": False,
            "public_canonical_export": "OPEN_CONDITIONAL",
            "default_target": "CONDITIONAL_COMPILED",
            "route_b": "CHALLENGER_NOT_RH",
        },
        "state_authority_policy": {
            "authoritative_state": "orchestrator/state/PROJECT_STATE.json",
            "duplicate_lifecycle_authorized": False,
            "selector_writes_to_superseded_authority_authorized": False,
        },
        "zones": [
            {
                "id": "PUBLIC_CORE",
                "disposition": "KEEP_PROOF_MONOREPO_WITH_HARD_FIREWALL",
                "split_now": False,
                "boundary": [
                    "Q3.Basic.WeilDirectRoute",
                    "Q3.Basic.WeilSquareClass",
                    "Q3.Basic.Defs:allowed-declaration-closure-only",
                ],
                "reason": (
                    "The executable import and declaration firewall separates the current "
                    "public canonical slice from challenger and legacy declarations."
                ),
                "future_policy": "EXTRACT_ONLY_IF_CANONICAL_FIREWALL_CANNOT_REMAIN_ENFORCEABLE",
            },
            {
                "id": "ROUTE_B",
                "disposition": "DO_NOT_SPLIT_LIVE_CHALLENGER",
                "split_now": False,
                "boundary": [
                    "q3.lean.aristotle/Q3/Proofs/RouteB/",
                    "docs/routeB_bus/",
                    "same-family source locks",
                ],
                "reason": (
                    "Goal058 was source-open and NOT_RH at the pinned decision snapshot; "
                    "crosswalks and bus receipts require atomic history."
                ),
                "future_policy": "RECONSIDER_ONLY_AFTER_LIVE_BUS_AND_SAME_FAMILY_CROSSWALKS_CLOSE",
            },
            {
                "id": "PROOF_CERTIFICATES",
                "disposition": "DO_NOT_SPLIT_FROM_CONSUMERS",
                "split_now": False,
                "boundary": [
                    "Lean source",
                    "proof certificates",
                    "axiom receipts",
                    "source-lock receipts",
                ],
                "reason": (
                    "Separating a certificate from its exact consumer destroys atomic "
                    "source provenance."
                ),
                "future_policy": "COLOCATE_WITH_CONSUMER_IN_ANY_FUTURE_TOPOLOGY",
            },
            {
                "id": "Q3_DISCOVERY",
                "disposition": "HOLD_SAME_REPO_SHADOW_SIDECAR",
                "split_now": False,
                "boundary": ["docs/cartographer/", "typed discovery schemas", "shadow backtests"],
                "reason": (
                    "The mandate authorizes same-repository shadow mode and makes extraction "
                    "conditional on measured independent value."
                ),
                "future_policy": "CONDITIONAL_EXTRACTION_AFTER_ALL_DISCOVERY_GATES",
            },
            {
                "id": "LEGACY_ARCHIVE",
                "disposition": "HOLD_QUARANTINED_IN_PLACE",
                "split_now": False,
                "boundary": ["CONDITIONAL_COMPILED", "LEGACY", "ARCHIVE"],
                "reason": (
                    "Logical quarantine exists, but zero active imports, frozen content, and "
                    "history-preserving extraction are not evidenced for the whole legacy layer."
                ),
                "future_policy": "CONDITIONAL_READ_ONLY_ARCHIVE_AFTER_ALL_LEGACY_GATES",
            },
        ],
        "future_split_gates": [
            {
                "candidate": "PUBLIC_CORE_EMERGENCY_EXTRACTION",
                "status": "NOT_TRIGGERED",
                "required_gates": [
                    "IMPORT_FIREWALL_UNENFORCEABLE_ON_CANONICAL_BRANCH",
                    "MINIMAL_PUBLIC_SLICE_COMPLETE",
                    "CERTIFICATE_ATOMICITY_PRESERVED",
                    "AUTHORITATIVE_STATE_MIGRATION_COMPLETE",
                    "ZERO_SELECTOR_WRITES_TO_SUPERSEDED_AUTHORITY",
                    "SINGLE_LIFECYCLE_VALIDATOR_PASS",
                    "OWNER_RATIFIED_REEVALUATION",
                ],
                "failure_code": "PREMATURE_PUBLIC_CORE_EXTRACTION",
            },
            {
                "candidate": "ROUTE_B",
                "status": "FORBIDDEN_LIVE",
                "required_gates": [
                    "NO_LIVE_BUS_DEPENDENCY",
                    "SAME_FAMILY_CROSSWALKS_VERSIONED",
                    "ZERO_PUBLIC_CANONICAL_IMPORTS",
                    "CERTIFICATES_REMAIN_COLOCATED",
                    "AUTHORITATIVE_STATE_MIGRATION_COMPLETE",
                    "ZERO_SELECTOR_WRITES_TO_SUPERSEDED_AUTHORITY",
                    "SINGLE_LIFECYCLE_VALIDATOR_PASS",
                    "OWNER_RATIFIED_REEVALUATION",
                ],
                "failure_code": "ROUTEB_LIVE_SPLIT_FORBIDDEN",
            },
            {
                "candidate": "Q3_DISCOVERY",
                "status": "HOLD_GATES_OPEN",
                "required_gates": [
                    "STABLE_VERSIONED_SCHEMA",
                    "INDEPENDENT_CLI_OR_PACKAGE_BOUNDARY",
                    "BLINDED_HOLDOUT_BACKTEST_VALUE",
                    "ZERO_LIVE_ROUTE_WRITES",
                    "MAINTENANCE_COST_BELOW_SAVED_WORK",
                    "AUTHORITATIVE_STATE_MIGRATION_COMPLETE",
                    "ZERO_SELECTOR_WRITES_TO_SUPERSEDED_AUTHORITY",
                    "SINGLE_LIFECYCLE_VALIDATOR_PASS",
                    "OWNER_RATIFIED_REEVALUATION",
                ],
                "failure_code": "PREMATURE_DISCOVERY_REPO",
            },
            {
                "candidate": "LEGACY_ARCHIVE",
                "status": "HOLD_GATES_OPEN",
                "required_gates": [
                    "ZERO_ACTIVE_IMPORTS",
                    "ZERO_PUBLIC_EXPORTS",
                    "FROZEN_READ_ONLY_CONTENT",
                    "HISTORY_PRESERVATION_PLAN",
                    "MAIN_REPO_POINTER_MANIFEST",
                    "OWNER_RATIFIED_REEVALUATION",
                ],
                "failure_code": "PREMATURE_LEGACY_REPO",
            },
        ],
        "evidence_pins": evidence_pins(),
        "invariants": [
            "NO_NEW_REPOSITORY_CREATED",
            "NO_REPOSITORY_SETTINGS_CHANGED",
            "NO_PHYSICAL_EXTRACTION_PERFORMED",
            "PUBLIC_CANONICAL_IMPORT_FIREWALL_PASS_AT_PIN",
            "PUBLIC_CANONICAL_EXPORT_REMAINS_CONDITIONAL_OPEN",
            "UNCONDITIONAL_RH_PROOF_FALSE",
            "ROUTE_B_CHALLENGER_NOT_RH_AT_PIN",
            "PROOF_CERTIFICATE_CONSUMER_ATOMICITY",
            "SINGLE_AUTHORITATIVE_STATE_NO_DUPLICATE_LIFECYCLE",
            "FUTURE_SPLIT_REQUIRES_NEW_EXPLICIT_REEVALUATION",
            "BRANCH_REQUIRED_CHECK_REMAINS_OPEN",
        ],
        "plants": PLANTS,
    }


def validate_schema(payload: dict[str, Any], schema_path: Path, code: str) -> None:
    try:
        import jsonschema
    except ImportError as exc:
        raise TopologyError(f"{code}_JSONSCHEMA_UNAVAILABLE") from exc
    try:
        jsonschema.Draft202012Validator(
            strict_json(schema_path.read_bytes(), f"{code}_SCHEMA")
        ).validate(payload)
    except jsonschema.ValidationError as exc:
        raise TopologyError(f"{code}_SCHEMA_INVALID:{exc.message}") from exc


def verify_semantic_evidence() -> None:
    public_receipt = tree_blob(
        "9716df6cab7936fbb442797367b88c6c8aee96ae",
        "docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md",
    )
    for token in (
        b"unconditional_rh_proof: false",
        b"default_target_class: CONDITIONAL_COMPILED",
        b"route_b: CHALLENGER_NOT_RH",
        b"canonical_public_entrypoint_established: false",
    ):
        if token not in public_receipt:
            raise TopologyError("P10_PUBLIC_CLAIM_BOUNDARY_DRIFT")
    registry = strict_json(
        tree_blob(BASELINE_COMMIT, "docs/semantic_quarantine/MODULE_CLASS_REGISTRY_v1.json"),
        "P10_MODULE_REGISTRY",
    )
    prefix = registry["rules"]["prefix"]
    if not any(
        row.get("module_class") == "CHALLENGER"
        and row.get("match", {}).get("repo_relative_path_prefix")
        == "q3.lean.aristotle/Q3/Proofs/RouteB/"
        for row in prefix
    ):
        raise TopologyError("P10_ROUTEB_CLASSIFICATION_MISSING")
    policy = strict_json(
        tree_blob(BASELINE_COMMIT, "docs/semantic_quarantine/IMPORT_FIREWALL_POLICY_v1.json"),
        "P10_FIREWALL_POLICY",
    )
    if policy.get("allowed_class_edges", {}).get("PUBLIC_CANONICAL") != [
        "CORE_SHARED",
        "PUBLIC_CANONICAL",
    ] or set(policy.get("forbidden_public_target_classes", [])) != {
        "ARCHIVE",
        "CHALLENGER",
        "CONDITIONAL_COMPILED",
        "EXPERIMENT",
        "GENERATED_VIEW",
        "LEGACY",
    }:
        raise TopologyError("P10_FIREWALL_POLICY_SEMANTIC_DRIFT")
    firewall = strict_json(
        tree_blob(BASELINE_COMMIT, "docs/semantic_quarantine/IMPORT_FIREWALL_RECEIPT_v1.json"),
        "P10_FIREWALL_RECEIPT",
    )
    if (
        firewall.get("public_root_fresh_build", {}).get("status") != "PASS"
        or firewall.get("semantic_declaration_audit", {}).get("status") != "PASS"
        or {row.get("status") for row in firewall.get("plants", [])} != {"REJECTED"}
    ):
        raise TopologyError("P10_FIREWALL_RECEIPT_NOT_PASS")
    route = strict_json(
        tree_blob(
            BASELINE_COMMIT,
            "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json",
        ),
        "P10_ROUTE_B_STATE",
    )
    if (
        route.get("architecture", {}).get("route_b_rh_status") != "NOT_RH"
        or route.get("current", {}).get("route_promotion") is not False
        or route.get("current", {}).get("rh_claimed") is not False
    ):
        raise TopologyError("P10_ROUTEB_NOT_CHALLENGER_AT_PIN")
    execution = strict_json(
        tree_blob(BASELINE_COMMIT, "orchestrator/state/PROJECT_EXECUTION_STATE.json"),
        "P10_EXECUTION_STATE",
    )
    selector = execution.get("selector", {})
    if (
        selector.get("action") != "SELECT_EXACT_GOAL"
        or selector.get("selected_goal_id") != "058"
        or selector.get("selected_goal_path")
        != "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"
    ):
        raise TopologyError("P10_GOAL058_SELECTOR_DRIFT")
    goal = tree_blob(BASELINE_COMMIT, "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md")
    for token in (
        b"GOAL: 058",
        b"STATUS: OPEN",
        b"STOP: TWO_DIFFERENT_FAMILIES_USED",
        b"SUCCESS: ONE_NORMALIZED_GROUND_FAMILY_REAL_ZEROS_AND_LOCALLY_UNIFORM_LIMIT",
        b"ROUTE: CHALLENGER_NOT_RH",
    ):
        if token not in goal:
            raise TopologyError("P10_GOAL058_CONTRACT_DRIFT")
    lean = tree_blob(
        BASELINE_COMMIT, "q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean"
    )
    for token in (
        b"def sameCofinalGuard",
        b"theorem sameCofinalGuard_s2Sequence",
        b"fun k => C.parent (C.extract k) := rfl",
        b"#print axioms sameCofinalGuard_s2Sequence",
    ):
        if token not in lean:
            raise TopologyError("P10_SAME_FAMILY_LEAN_SOURCE_DRIFT")
    proof_receipt = tree_blob(
        BASELINE_COMMIT, "docs/routeB_bus/056_k8_muntz_v3_slot_s2_bridge.answer.md"
    )
    for token in (
        b"rh_of_canonical_strip_slots",
        b"CanonicalRHRouteSkeleton.lean: PASS_STANDARD_TRIPLE",
    ):
        if token not in proof_receipt:
            raise TopologyError("P10_SAME_FAMILY_PROOF_RECEIPT_DRIFT")
    discovery = tree_blob(
        BASELINE_COMMIT,
        "docs/routeB_bus/proshka/ARSENAL_MANDATE_2026-08-23_MODULAR_DISCOVERY_COMPILER_SHADOW.md",
    )
    for token in (
        b"initial_home: SAME_REPOSITORY_SHADOW_MODE",
        b"future_extraction_to_separate_repository: CONDITIONAL_ON_V0_VALUE",
        b"live_lean_edits_authorized: false",
    ):
        if token not in discovery:
            raise TopologyError("P10_DISCOVERY_MANDATE_DRIFT")


def verify_decision(payload: dict[str, Any]) -> None:
    validate_schema(payload, DECISION_SCHEMA, "P10_DECISION")
    verify_semantic_evidence()
    if payload != expected_decision():
        raise TopologyError("P10_DECISION_DRIFT")


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


def support_objects() -> dict[str, dict[str, Any]]:
    missing = [path for path in SUPPORT_PATHS if not (ROOT / path).is_file()]
    if missing:
        raise TopologyError(f"P10_SUPPORT_MISSING:{sorted(missing)}")
    return {path: file_object(ROOT / path) for path in sorted(SUPPORT_PATHS)}


def expected_receipt() -> dict[str, Any]:
    objects = support_objects()
    decision = load_artifact_json(DECISION, "P10_DECISION")
    foreign = verify_foreign_dirty_snapshot()
    return {
        "schema_version": "q3.repository_topology_receipt.v1",
        "status": "NO_NEW_REPO_NOW_DECISION_VERIFIED",
        "baseline_commit": BASELINE_COMMIT,
        "decision_sha256": sha256(DECISION.read_bytes()),
        "evidence_digest": sha256(canonical_json(decision["evidence_pins"])),
        "foreign_dirty_snapshot": foreign,
        "foreign_dirty_snapshot_sha256": sha256(canonical_json(foreign)),
        "candidate_objects": objects,
        "prospective_tree_excluding_receipt": apply_objects(BASELINE_COMMIT, objects),
        "checks": [
            "EVIDENCE_GIT_OBJECTS_HASHED",
            "PUBLIC_CLAIM_BOUNDARY_CONDITIONAL_OPEN",
            "PUBLIC_FIREWALL_SEMANTICS_PASS_AT_PIN",
            "GOAL058_ONE_FAMILY_CONTRACT_BOUND",
            "SAME_FAMILY_LEAN_AND_PROOF_RECEIPT_BOUND",
            "ROUTEB_NOT_RH_AT_PIN",
            "DISCOVERY_SHADOW_CONDITIONAL",
            "EXACT_FIVE_ZONE_DECISION",
            "STATE_AUTHORITY_EXIT_GATES_EXPLICIT",
            "FOREIGN_DIRTY_BYTE_MODE_TYPE_BOUND",
            "NO_GITHUB_OR_EXTRACTION_MUTATION",
        ],
        "plants": PLANTS,
    }


def expected_final_tree(receipt: dict[str, Any]) -> str:
    return apply_objects(
        receipt["prospective_tree_excluding_receipt"],
        {str(RECEIPT.relative_to(ROOT)): file_object(RECEIPT)},
    )


def verify_receipt(receipt: dict[str, Any]) -> None:
    validate_schema(receipt, RECEIPT_SCHEMA, "P10_RECEIPT")
    if receipt != expected_receipt():
        raise TopologyError("P10_RECEIPT_DRIFT")


def verify_state() -> None:
    decision = load_artifact_json(DECISION, "P10_DECISION")
    receipt = load_artifact_json(RECEIPT, "P10_RECEIPT")
    verify_decision(decision)
    verify_receipt(receipt)
    head = git("rev-parse", "HEAD").decode().strip()
    origin = git("rev-parse", "origin/rh_clean").decode().strip()
    final_tree = expected_final_tree(receipt)
    index_tree = git("write-tree").decode().strip()
    if head == BASELINE_COMMIT:
        paths = {
            item.decode("utf-8", "surrogateescape")
            for item in git("diff", "--cached", "--name-only", "-z", BASELINE_COMMIT, "--").split(
                b"\0"
            )
            if item
        }
        if origin != BASELINE_COMMIT or paths != TRANSACTION_PATHS or index_tree != final_tree:
            raise TopologyError("P10_PREFLIGHT_SCOPE_OR_TREE_DRIFT")
        return
    parent = git("rev-parse", "HEAD^").decode().strip()
    paths = {
        item.decode("utf-8", "surrogateescape")
        for item in git("diff", "--name-only", "-z", BASELINE_COMMIT, "HEAD", "--").split(b"\0")
        if item
    }
    if (
        origin != head
        or parent != BASELINE_COMMIT
        or paths != TRANSACTION_PATHS
        or git("rev-parse", "HEAD^{tree}").decode().strip() != final_tree
        or index_tree != final_tree
    ):
        raise TopologyError("P10_CANONICAL_SCOPE_HISTORY_OR_TREE_DRIFT")


def write_artifacts() -> None:
    decision = expected_decision()
    validate_schema(decision, DECISION_SCHEMA, "P10_DECISION")
    DECISION.write_bytes(artifact_json(decision))
    receipt = expected_receipt()
    validate_schema(receipt, RECEIPT_SCHEMA, "P10_RECEIPT")
    RECEIPT.write_bytes(artifact_json(receipt))


def run_plants() -> None:
    base = load_artifact_json(DECISION, "P10_DECISION")
    mutations = []
    new_repo = json.loads(json.dumps(base))
    new_repo["create_new_repository_now"] = True
    mutations.append(new_repo)
    duplicate = json.loads(json.dumps(base))
    duplicate["zones"][1]["id"] = "PUBLIC_CORE"
    mutations.append(duplicate)
    route_split = json.loads(json.dumps(base))
    route_split["zones"][1]["disposition"] = "SPLIT_NOW"
    mutations.append(route_split)
    cert_split = json.loads(json.dumps(base))
    cert_split["zones"][2]["split_now"] = True
    mutations.append(cert_split)
    discovery = json.loads(json.dumps(base))
    discovery["future_split_gates"][2]["status"] = "NOT_TRIGGERED"
    mutations.append(discovery)
    legacy = json.loads(json.dumps(base))
    legacy["future_split_gates"][3]["required_gates"] = ["OWNER_RATIFIED_REEVALUATION"]
    mutations.append(legacy)
    evidence = json.loads(json.dumps(base))
    evidence["evidence_pins"][0]["path"] = "README.md"
    mutations.append(evidence)
    branch = json.loads(json.dumps(base))
    branch["invariants"].remove("BRANCH_REQUIRED_CHECK_REMAINS_OPEN")
    mutations.append(branch)
    lifecycle = json.loads(json.dumps(base))
    lifecycle["state_authority_policy"]["duplicate_lifecycle_authorized"] = True
    mutations.append(lifecycle)
    for index, poisoned in enumerate(mutations):
        try:
            verify_decision(poisoned)
        except TopologyError:
            continue
        raise TopologyError(f"P10_PLANT_ESCAPED:{index}")
    foreign = original_foreign_dirty_snapshot()
    drifted = json.loads(json.dumps(foreign))
    drifted[0]["mode"] ^= 0o100
    try:
        verify_foreign_snapshot_rows(foreign, drifted)
    except TopologyError:
        pass
    else:
        raise TopologyError("P10_PLANT_ESCAPED:FOREIGN_DIRTY")
    for code, data in (
        ("DUPLICATE_KEY", b'{"schema_version":"x","schema_version":"x"}\n'),
        ("WHITESPACE", artifact_json(base) + b"\n"),
    ):
        try:
            parse_artifact_json(data, f"P10_PLANT_{code}")
        except TopologyError:
            continue
        raise TopologyError(f"P10_PLANT_ESCAPED:{code}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("build", "check", "plants"))
    args = parser.parse_args()
    try:
        if args.command == "build":
            write_artifacts()
            print("REPOSITORY_TOPOLOGY_DECISION_BUILD_PASS")
        elif args.command == "check":
            verify_state()
            print("REPOSITORY_TOPOLOGY_DECISION_CHECK_PASS")
        else:
            run_plants()
            print("REPOSITORY_TOPOLOGY_DECISION_PLANTS_PASS")
    except (OSError, json.JSONDecodeError, TopologyError, subprocess.CalledProcessError) as exc:
        print(f"REPOSITORY_TOPOLOGY_DECISION_FAIL:{exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
