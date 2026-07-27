#!/usr/bin/env python3
"""Fail-closed validator for Route B SOFT_0 paper gate."""

from __future__ import annotations

import hashlib
import json
import math
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "SOFT_0_ROOF_AND_S2_TYPECHECK_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"
FORBIDDEN_LEAN = re.compile(r"\b(sorry|admit)\b|exact\?")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def pinned(record: dict[str, object], code: str) -> Path:
    path = REPO_ROOT / str(record["path"])
    require(path.is_file(), f"{code}_MISSING:{record['path']}")
    require(sha256(path) == record["sha256"], f"{code}_HASH_DRIFT:{record['path']}")
    return path


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))

    require(cert["revision_target"] == 42, "SOFT_0_CERT_REVISION_DRIFT")
    require(state["revision"] >= 42, "SOFT_0_STATE_REVISION_TOO_OLD")
    allowed = cert["allowed_output_codes"]
    require(len(allowed) == 5 and len(set(allowed)) == 5, "SOFT_0_OUTPUT_MENU_DRIFT")
    require(cert["output_code"] in allowed, "SOFT_0_OUTPUT_NOT_IN_PRO_MENU")
    require(cert["output_code"] == "SOFT_SUBSEQUENCE_CLOSURE_TYPED", "SOFT_0_WRONG_OUTPUT")
    require(cert["rh_status"] == "NOT_RH", "SOFT_0_RH_OVERCLAIM")

    authority = pinned(cert["authority"], "SOFT_0_AUTHORITY")
    authority_text = authority.read_text(encoding="utf-8")
    for code in allowed:
        require(code in authority_text, f"SOFT_0_PRO_MENU_CODE_MISSING:{code}")

    paper = pinned(cert["paper_artifact"], "SOFT_0_PAPER")
    paper_text = paper.read_text(encoding="utf-8")
    for token in (
        "Theorem `SoftSubsequenceZeroEscape`",
        "Montel's theorem",
        "identity theorem",
        "Hurwitz's theorem",
        "Splus",
        "Sminus",
        "rh_iff_centeredXi_zeros_real",
        "SOFT_ROOF_BODY_MISSING",
        "GAMMA_SOURCE_LOCKED_ZERO_FREE",
        "OFF_AXIS_PROBE_NONDECISIVE_FALSIFIER_PASS",
        "MINT_MENU_FALSIFIED",
        "NON_CRITICAL_PENDING_SOFT_0",
        "NOT_RH",
    ):
        require(token in paper_text, f"SOFT_0_PAPER_TOKEN_MISSING:{token}")

    theorem = cert["abstract_theorem"]
    require(theorem["proof_status"] == "PROVED_PAPER", "SOFT_0_ABSTRACT_THEOREM_NOT_PROVED")
    require(theorem["quantitative_h4_used"] is False, "SOFT_0_H4_SMUGGLED_IN_ABSTRACT_PROOF")
    require("HURWITZ_ON_CONNECTED_UPPER_HALF_STRIP" in theorem["proof_steps"], "SOFT_0_UPPER_HURWITZ_MISSING")
    require("HURWITZ_ON_CONNECTED_LOWER_HALF_STRIP" in theorem["proof_steps"], "SOFT_0_LOWER_HURWITZ_MISSING")

    roof = cert["finite_roof_audit"]
    require(roof["h4_dependency_cycle_found"] is False, "SOFT_ROOF_H4_DEPENDENCY_CYCLE")
    require(roof["forbidden_dependencies_found"] == [], "SOFT_ROOF_FORBIDDEN_DEPENDENCY")
    require(roof["pass_code_issued"] is False, "SOFT_ROOF_FALSE_PASS")
    require(roof["current_code"] == "SOFT_ROOF_BODY_MISSING", "SOFT_ROOF_BODY_STATUS_DRIFT")
    nodes = state["nodes"]
    require("simple isolated even global ground" in nodes["H2a3"]["statement"], "SOFT_ROOF_H2A_ROLE_DRIFT")
    require(nodes["H1"]["proof_status"] == "OPEN", "SOFT_ROOF_H1_FALSE_CLOSURE")
    require(nodes["H2a"]["proof_status"] == "OPEN", "SOFT_ROOF_H2A_FALSE_CLOSURE")
    require(nodes["H2b"]["proof_status"] == "CONDITIONAL", "SOFT_ROOF_H2B_STATUS_DRIFT")
    require(nodes["H2c"]["dependencies"] == ["H2a", "H2b"], "SOFT_ROOF_H2C_DEPENDENCY_DRIFT")
    require(nodes["H2"]["proof_status"] == "OPEN", "SOFT_ROOF_H2_FALSE_CLOSURE")

    gamma = cert["gamma_lock"]
    require(gamma["exit_code"] == "GAMMA_SOURCE_LOCKED_ZERO_FREE", "SOFT_GAMMA_EXIT_DRIFT")
    source_lock_path = pinned(gamma["source_lock"], "SOFT_GAMMA_LOCK")
    source_lock = json.loads(source_lock_path.read_text(encoding="utf-8"))
    require(source_lock["status"] == "ANALYTIC_UNIT_LOCKED_OBJECT_ROLE_OPEN", "SOFT_GAMMA_ROLE_OVERCLAIM")
    require(source_lock["domain"]["boundary_excluded"] is True, "SOFT_GAMMA_BOUNDARY_SMUGGLED")
    require(source_lock["operand_lock"]["lambda_phase_occurrences"] == 1, "SOFT_GAMMA_PHASE_COUNT_DRIFT")
    require("NO_POSTHOC_QUOTIENT" in source_lock["firewalls"], "SOFT_GAMMA_POSTHOC_FIREWALL_MISSING")
    require("NO_DOUBLE_COMPLETION" in source_lock["firewalls"], "SOFT_GAMMA_DOUBLE_COMPLETION_FIREWALL_MISSING")
    for index, source in enumerate(source_lock["source_pins"]):
        pinned(source, f"SOFT_GAMMA_SOURCE_{index}")
    lean_path = pinned(gamma["lean_artifact"], "SOFT_GAMMA_LEAN")
    lean_text = lean_path.read_text(encoding="utf-8")
    require(FORBIDDEN_LEAN.search(lean_text) is None, "SOFT_GAMMA_LEAN_HOLE")
    for token in ("def gammaSoft", "gammaC_centered_ne_zero", "gammaSoft_ne_zero", "Complex.exp_ne_zero", "#print axioms"):
        require(token in lean_text, f"SOFT_GAMMA_LEAN_TOKEN_MISSING:{token}")
    require(gamma["s2_identification_proved"] is False, "SOFT_GAMMA_S2_SMUGGLED")
    require(gamma["posthoc_quotient_allowed"] is False, "SOFT_GAMMA_POSTHOC_ALLOWED")

    probe = cert["probe_recode"]
    result_path = pinned(probe["result"], "SOFT_0_PROBE")
    result = json.loads(result_path.read_text(encoding="utf-8"))
    require(result["verdict_code"] == "OFF_AXIS_PROBE_NONDECISIVE_FALSIFIER_PASS", "SOFT_0_PROBE_CODE_DRIFT")
    require(result["interpretation_lock"]["completion_class_invariant"] is False, "SOFT_0_PROBE_INVARIANCE_OVERCLAIM")
    require(math.isclose(result["fit"]["slope"], probe["slope"], rel_tol=0, abs_tol=1e-15), "SOFT_0_PROBE_SLOPE_DRIFT")
    require(result["next_normalization_policy"]["code"] == "CENTRAL_ANCHOR_NORMALIZATION_LOCKED", "SOFT_0_CENTRAL_ANCHOR_MISSING")

    mint = cert["mint_r3"]
    require(mint["code"] == "MINT_MENU_FALSIFIED", "SOFT_0_MINT_R3_CODE_DRIFT")
    draft_path = pinned(mint["draft"], "SOFT_0_MINT_DRAFT_R3")
    draft_text = draft_path.read_text(encoding="utf-8")
    require("Revision: R3" in draft_text, "SOFT_0_MINT_R3_MISSING")
    require("NO_VARIANT_RATIFIABLE" in draft_text, "SOFT_0_MINT_VARIANT_STILL_RATIFIABLE")
    require("templates inert" in draft_text, "SOFT_0_MINT_OLD_TEMPLATE_LIVE")
    battery_path = pinned(mint["battery"], "SOFT_0_MINT_BATTERY")
    battery = json.loads(battery_path.read_text(encoding="utf-8"))
    ratios = [row["two_level_rayleigh_alpha_closure_ratio_bCal"] for row in battery["scores"]["P2"]["cells"]]
    require(all(math.isclose(a, b, rel_tol=1e-15) for a, b in zip(ratios, mint["variant_A"]["closure_ratios"])), "SOFT_0_MINT_A_NUMBER_DRIFT")
    require(battery["scores"]["P3"]["code"] == "SLOT_VACUITY", "SOFT_0_MINT_B_PLANT_DRIFT")
    require(mint["mint_activated"] is False, "SOFT_0_MINT_ACTIVATED")

    state_gate = state["soft_0_roof_and_s2_typecheck"]
    require(state_gate["output_code"] == cert["output_code"], "SOFT_0_STATE_OUTPUT_DRIFT")
    require(state_gate["certificate_sha256"] == sha256(CERT_PATH), "SOFT_0_STATE_CERT_HASH_DRIFT")
    node = nodes["D0.7e.5a"]
    require(node["proof_status"] == "BLOCKED", "SOFT_0_5A_FALSE_CLOSURE")
    require(node["activity"] == "ACTIVE", "SOFT_0_5A_ACTIVITY_DRIFT")
    require(
        node["scheduler_marker"] in {
            "NON_CRITICAL_PENDING_SOFT_0",
            "NON_CRITICAL_PENDING_SOFT_1",
            "NON_CRITICAL_PENDING_SOFT_2",
        },
        "SOFT_0_5A_MARKER_MISSING",
    )
    require(node["mint_menu_status"] == "MINT_MENU_FALSIFIED", "SOFT_0_5A_MENU_STATUS_DRIFT")
    require(node["mint_activated"] is False, "SOFT_0_5A_MINT_ACTIVATED")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "SOFT_0_BUS_010_CREATED")
    require(not any(BUS_DIR.glob("010_*.answer.md")), "SOFT_0_BUS_010_ANSWER_CREATED")
    require("NO_RH" in cert["explicit_nonclaims"], "SOFT_0_RH_FIREWALL_MISSING")

    print(json.dumps({
        "output_code": cert["output_code"],
        "abstract_theorem": "PROVED_PAPER",
        "finite_roof": "SOFT_ROOF_BODY_MISSING_NO_H4_CYCLE",
        "gamma": gamma["exit_code"],
        "probe": probe["new_code"],
        "mint": mint["code"],
        "D0.7e.5a": f"BLOCKED_{node['scheduler_marker']}",
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
