#!/usr/bin/env python3
"""Fail-closed validation for D0.7e.5a consumer/orientation audit."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_7E_5A_CERTIFICATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.7e.5a", "D0_7E_5A_CERT_NODE_MISMATCH")
    require(
        cert["node_role"] == "CANONICAL_ACTIVE_CHILD_AFTER_OWNER_R1_R5_RATIFICATION",
        "D0_7E_5A_GOVERNANCE_DRIFT",
    )
    require(cert["proof_status"] == "BLOCKED", "D0_7E_5A_FALSE_PASS")
    require(cert["stop_code"] == "D0_7E_WPRIME_CONSUMER_MISSING", "D0_7E_5A_STOP_MISMATCH")
    require(cert["success_code_not_issued"] == "D0_7E_B_ORIENTATION_LOCKED", "D0_7E_5A_SUCCESS_SMUGGLED")
    require(cert["rh_status"] == "NOT_RH", "D0_7E_5A_RH_FIREWALL_MISSING")
    require(
        cert["owner_ratification"]["status"] == "OWNER_RATIFICATION_R1_R5_LOCKED",
        "D0_7E_5A_OWNER_RATIFICATION_MISSING",
    )

    checked: list[str] = []
    for group in ("dependency_pins", "source_pins", "review_pins", "artifacts"):
        for pin in cert[group]:
            path = REPO_ROOT / pin["path"]
            require(path.is_file(), f"D0_7E_5A_PIN_MISSING:{pin['path']}")
            require(sha256(path) == pin["sha256"], f"D0_7E_5A_PIN_DRIFT:{pin['path']}")
            checked.append(pin["path"])

    domain = cert["domain_lock"]
    require(domain["base_domain"] == "TrialNonzero", "D0_7E_5A_BASE_DOMAIN_DRIFT")
    require("c0(k1_m_N)!=0" in domain["central_domain"], "D0_7E_5A_CENTRAL_LOCUS_MISSING")
    require(domain["trial_implies_central_nonzero"] is False, "D0_7E_TRIALNONZERO_NOT_CENTRALNONZERO")
    require("BDetNonzero" in domain["equivalent_domains"], "D0_7E_5A_LOCUS_ALIAS_GAP")
    require(domain["even_inclusion"] == "CentralValueNonzero_SUBSET_EvenTrialNonzero", "D0_7E_5A_EVEN_INCLUSION_GAP")

    orientation = cert["orientation_lock"]
    require("Fhat_m_N(0)/Xi(0)" in orientation["calibration_ratio"], "D0_7E_5A_BCAL_DRIFT")
    require("bCal_m_N^(-1)" in orientation["normalizing_multiplier"], "D0_7E_5A_INVERSE_MISSING")
    require("bZeoMul_m_N*Fhat_m_N" in orientation["normalized_object"], "D0_7E_5A_MULTIPLIER_IDENTITY_MISSING")
    require(orientation["historical_wprime_b_orientation"] == "UNPINNED", "D0_7E_5A_ORIENTATION_OVERCLAIM")

    consumer = cert["consumer_audit"]
    require(consumer["scope"].startswith("AUDITED_PINNED_SNAPSHOT"), "D0_7E_5A_GLOBAL_ABSENCE_OVERCLAIM")
    require(consumer["history_snapshot_commit"] == "33101a9221ef692dd44c9f6d79f4fe0b525c5293", "D0_7E_5A_HISTORY_SNAPSHOT_DRIFT")
    require(consumer["history_exact_name_search"] == "NO_FZEO_F_ZEO_BCAL_BZEO_COMMITS_REACHABLE_AT_SNAPSHOT", "D0_7E_5A_HISTORY_SEARCH_OVERCLAIM")
    require(consumer["FZeo_definition"] == "NOT_FOUND_IN_AUDITED_PINNED_SNAPSHOT", "D0_7E_5A_FZEO_SMUGGLED")
    require(consumer["WPrime_definition"] == "NO_INDEPENDENT_CONSUMER_FOUND_IN_AUDITED_PINNED_SNAPSHOT", "D0_7E_5A_WPRIME_SMUGGLED")
    require(consumer["historical_formula_status"] == "SKETCH_OPEN_CRITICAL", "D0_7E_5A_SKETCH_PROMOTED")
    require("NOT_INDEPENDENT_CONSUMER" in consumer["owner_option_b_status"], "D0_7E_5A_OWNER_AUTHORITY_OVERCLAIM")
    require(consumer["contract_v2_status"] == "TARGET_CONTRACT_NOT_PROOF_OR_CONSUMER_SOURCE", "D0_7E_5A_CONTRACT_PROMOTED")
    require(consumer["alpha_demand_status"] == "NOT_A_DEFINITION_SOURCE_AND_B_MISSING", "D0_7E_5A_ALPHA_AUDIT_PROMOTED")
    require(consumer["ladder_law_status"] == "DIAGNOSTIC_FIT_NOT_LAW", "D0_7E_5A_DIAGNOSTIC_PROMOTED")
    require(consumer["t0_corpus_mining_status"] == "NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE", "D0_7E_5A_T0_SOURCE_SMUGGLED")
    require(consumer["standing_order_status"] == "ACTIVE_BUT_NO_ELIGIBLE_CANDIDATE", "D0_7E_5A_STANDING_ORDER_OVERCLAIM")

    audit = (REQUEST_DIR / "D0_7E_5A_WPRIME_CONSUMER_ORIENTATION_AUDIT.md").read_text(encoding="utf-8")
    for token in (
        "D0_7E_CENTRAL_NONZERO_LOCUS_LOCKED",
        "D0_7E_BCAL_INVERSE_NORMALIZER_IDENTITY_LOCKED",
        "CentralValueNonzero subset EvenTrialNonzero",
        "bZeoMul_(m,N) = bCal_(m,N)^(-1)",
        "D0_7E_WPRIME_CONSUMER_MISSING",
        "NOT_FOUND_IN_AUDITED_PINNED_SNAPSHOT",
        "No H3c/H4 import: CONFIRMED",
        "No Bus 010: CONFIRMED",
        "NOT_RH: CONFIRMED",
        "CANONICAL_ACTIVE_LEAF",
    ):
        require(token in audit, f"D0_7E_5A_AUDIT_TOKEN_MISSING:{token}")

    primary = (REPO_ROOT / cert["source_pins"][0]["path"]).read_text(encoding="utf-8")
    require("WPrime" not in primary and "FZeo" not in primary, "D0_7E_5A_PRIMARY_SOURCE_CONSUMER_UNAUDITED")

    contract_v2 = (REPO_ROOT / "q3.lean.aristotle/docs/ROUTE_B_THEOREM_CONTRACT_v2.md").read_text(encoding="utf-8")
    alpha_demand = (REPO_ROOT / "q3.lean.aristotle/docs/ALPHA_DEMAND_AUDIT.md").read_text(encoding="utf-8")
    ladder = (REPO_ROOT / "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ladder_law_v1.md").read_text(encoding="utf-8")
    require("детектор: W′" in contract_v2 and "НЕ утверждение о доказанности" in contract_v2, "D0_7E_5A_CONTRACT_CLASSIFICATION_DRIFT")
    require("NOT_A_DEFINITION_SOURCE" in alpha_demand and "b_λ — MISSING" in alpha_demand, "D0_7E_5A_ALPHA_SOURCE_CLASSIFICATION_DRIFT")
    require("FIT_NOT_LAW" in ladder, "D0_7E_5A_LADDER_CLASSIFICATION_DRIFT")

    candidates = (REQUEST_DIR / "D0_7E_5A_CONSUMER_SOURCE_CANDIDATES.md").read_text(encoding="utf-8")
    require("NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE" in candidates, "D0_7E_5A_T0_VERDICT_MISSING")
    require("No definition or crosswalk" in candidates, "D0_7E_5A_T0_RECONSTRUCTION_FIREWALL_MISSING")

    # Deterministic plants.
    coeffs = (1 / math.sqrt(2), 0.0, 1 / math.sqrt(2))
    require(math.isclose(sum(x * x for x in coeffs), 1.0), "D0_7E_5A_UNIT_PLANT_BAD")
    require(coeffs[1] == 0.0, "D0_7E_TRIAL_CENTRAL_ZERO_PLANT_INERT")
    b_cal = 2.0
    b_mul = 1.0 / b_cal
    require(b_cal != b_mul, "D0_7E_BCAL_BZEO_ALIAS_PLANT_INERT")
    require(abs(b_cal) != abs(b_mul), "D0_7E_WPRIME_ORIENTATION_PLANT_INERT")
    require(
        "NO_INDEPENDENT_WPRIME_DEFINITION_FOUND_IN_AUDITED_SNAPSHOT" in cert["explicit_nonclaims"],
        "D0_7E_WPRIME_CONSUMER_PLANT_INERT",
    )
    require(
        "NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE_IN_T0_CORPUS" in cert["explicit_nonclaims"],
        "D0_7E_WPRIME_T0_CONSUMER_PLANT_INERT",
    )

    require(not any(BUS_DIR.glob("010_*.goal.md")), "D0_7E_5A_BUS_010_CREATED")
    require("NO_H3C_IMPORT" in cert["explicit_nonclaims"], "D0_7E_5A_H3C_IMPORT")
    require("NO_H4_IMPORT" in cert["explicit_nonclaims"], "D0_7E_5A_H4_IMPORT")

    result = {
        "node": "D0.7e.5a",
        "verdict": "STOP",
        "primary_code": cert["stop_code"],
        "proof_status": "BLOCKED",
        "node_role": "CANONICAL_ACTIVE_CHILD",
        "partial_exits": cert["partial_exit_codes"],
        "consumer": "NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE",
        "normalized_multiplier": "bCal^(-1)_ON_CentralValueNonzero",
        "wprime_b_orientation": "UNPINNED",
        "pins_checked": checked,
        "plants": list(cert["plants"].values()),
        "h3c_h4_import": "NONE",
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
