#!/usr/bin/env python3
"""Fail-closed validation of SOFT_L2 Round13Integration."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent.parent


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    certificate = json.loads((HERE / "SOFT_L2_ROUND13_INTEGRATION_CERTIFICATE.json").read_text())
    contract_path = HERE / certificate["contract"]["file"]
    authority_path = HERE / certificate["authority"]["file"]
    lean_path = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB/SoftL2Round13Integration.lean"
    plants_path = HERE / certificate["optional_leaf"]["plants_file"]
    tail_path = HERE / certificate["tail_check"]["record"]
    soft1_path = HERE / "SOFT_1_GATE_CONTRACT.md"

    require(certificate["status"] == "SOFT_L2_ROUND13_INTEGRATION_LOCKED", "ROUND13_STATUS_MISMATCH")
    require(sha256(authority_path) == certificate["authority"]["sha256"], "ROUND13_AUTHORITY_HASH_MISMATCH")
    require(sha256(contract_path) == certificate["contract"]["sha256"], "ROUND13_CONTRACT_HASH_MISMATCH")
    require(sha256(lean_path) == certificate["lean"]["sha256"], "ROUND13_LEAN_HASH_MISMATCH")
    require(sha256(plants_path) == certificate["optional_leaf"]["plants_sha256"], "ROUND13_PLANTS_HASH_MISMATCH")
    require(sha256(tail_path) == certificate["tail_check"]["record_sha256"], "ROUND13_TAIL_HASH_MISMATCH")

    contract = contract_path.read_text()
    lean = lean_path.read_text()
    soft1 = soft1_path.read_text()
    for token in (
        "SOFT_SAME_COFINAL_SUBSEQUENCE",
        "SOFT_COFINAL_SUBSEQUENCE_MISMATCH",
        "GlobalPositiveDefiniteUniqueness",
        "SourceCompactnessToFullAutocorrelation",
        "FALSE_WALL_REMOVED_ROUND13",
    ):
        require(token in contract, f"ROUND13_CONTRACT_TOKEN_MISSING:{token}")
    require("SOFT_SAME_COFINAL_SUBSEQUENCE" in soft1, "SOFT1_GUARD_NOT_INTEGRATED")
    require("SOFT_COFINAL_SUBSEQUENCE_MISMATCH" in soft1, "SOFT1_FAILURE_CODE_NOT_INTEGRATED")
    require(len(certificate["l2_2"]["inputs"]) == 5, "L2_2_INPUT_COUNT_MISMATCH")
    require(certificate["l2_2"]["status"] == "TYPED_OPEN_NOT_PROVED", "L2_2_FALSE_CLOSURE")
    require(certificate["l2_2"]["tail_input"] is False, "TAIL_SMUGGLED_INTO_L2_2")
    require(certificate["l2_2"]["edge_mass_input"] is False, "EDGE_MASS_SMUGGLED_INTO_L2_2")
    require(len(certificate["optional_leaf"]["inputs"]) == 2, "SOURCE_COMPACTNESS_INPUT_COUNT_MISMATCH")
    require(certificate["optional_leaf"]["feeds_l2_2"] is False, "OPTIONAL_LEAF_SMUGGLED_INTO_L2_2")

    plants = json.loads(plants_path.read_text())
    require(plants["all_plants_live"] is True, "SOURCE_COMPACTNESS_PLANT_MISS")
    require(plants["l2_2_evidence"] is False, "PLANTS_MISCODED_AS_L2_2_EVIDENCE")
    require(
        [p["code"] for p in plants["plants"]]
        == certificate["optional_leaf"]["plant_codes"],
        "SOURCE_COMPACTNESS_PLANT_CODE_MISMATCH",
    )
    require(all(p["status"] == "FIRED" for p in plants["plants"]), "SOURCE_COMPACTNESS_PLANT_NOT_FIRED")

    tail = json.loads(tail_path.read_text())
    require(tail["verdict"] == "TAIL_DOMINATED", "TAIL_VERDICT_DRIFT")
    require(tail["round13_role"] == certificate["tail_check"]["round13_role"], "TAIL_ROLE_DRIFT")
    require(tail["l2_2_input"] is False, "TAIL_IS_L2_2_INPUT")
    require(tail["supplies_uniform_translation_continuity"] is False, "TAIL_FALSE_REGULARITY_CLAIM")
    require(tail["map_recode"] == "FALSE_WALL_REMOVED_ROUND13", "FALSE_WALL_NOT_REMOVED")

    require("simpleGround_canonicalPhaseIndependentAutocorrelation" in lean, "PHASE_COROLLARY_LEAN_MISSING")
    require("def GlobalPositiveDefiniteUniqueness" in lean, "L2_2_LEAN_TYPE_MISSING")
    require("def SourceCompactnessToFullAutocorrelation" in lean, "SOURCE_COMPACTNESS_LEAN_TYPE_MISSING")
    require(not any(x in lean for x in ("sorry", "exact?", "admit")), "ROUND13_LEAN_HOLE")

    bus = REPO / "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/bus"
    require(not list(bus.glob("010_*")), "BUS_010_CREATED")
    require(certificate["RH"] is False, "ROUND13_RH_OVERCLAIM")
    print("SOFT_L2_ROUND13_INTEGRATION_LOCKED")


if __name__ == "__main__":
    main()
