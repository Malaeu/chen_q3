#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-17 H1c2 closure."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H1C2_RAW_INTEGRAL_CROSSWALK_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"
FORBIDDEN = re.compile(r"\b(sorry|admit)\b|exact\?")


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

    require(cert["revision_target"] == 17, "H1C2_CERT_REVISION_DRIFT")
    require(state["revision"] >= 17, "H1C2_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H1C2_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H1C2_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H1C2_SOURCE_{index}")
    pinned(cert["artifact"], "H1C2_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H1C2_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H1C2_LEAN_HOLE")
    require("#print axioms" in proof_text, "H1C2_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H1C2_THEOREM_MISSING:{theorem}")

    for token in (
        "integral_exp_mul_complex",
        "rawModeCenteredIntegral_at_pole",
        "proposition59PoleKernel_at_pole",
        "finiteRawCenteredIntegral_eq_mode_sum",
        "finiteFplusCenteredIntegral_eq_proposition59RawTransform_neg",
    ):
        require(token in proof_text, f"H1C2_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h1c2 = nodes["H1c2"]
    require(h1c2["proof_status"] == "PROVED", "H1C2_NODE_NOT_PROVED")
    require(h1c2["activity"] == "INACTIVE", "H1C2_NODE_ACTIVE")
    require(not h1c2["eligibility"]["eligible"], "H1C2_NODE_STILL_ELIGIBLE")
    require(
        h1c2["validation"] == "RAW_INTEGRAL_PROPOSITION59_RHS_EXACT_CROSSWALK",
        "H1C2_VERDICT_DRIFT",
    )
    require(
        h1c2["proof_artifact"] == "Q3/Proofs/RouteB/RawIntegralRhsCrosswalk.lean",
        "H1C2_PROOF_ARTIFACT_DRIFT",
    )

    require(nodes["H1c"]["proof_status"] == "OPEN", "H1C_PARENT_FALSE_PASS")
    require(nodes["H1c3"]["proof_status"] == "OPEN", "H1C3_FALSE_PASS")
    require(not nodes["H1c3"]["eligibility"]["eligible"], "H1C3_FALSE_ELIGIBILITY")
    require(nodes["H1c4"]["proof_status"] == "OPEN", "H1C4_FALSE_PASS")
    require(nodes["H1"]["proof_status"] == "OPEN", "H1_FALSE_PASS")
    require(
        "H1C_RAW_INTEGRAL_RHS_CROSSWALK_MISSING" not in nodes["H1c"]["failure_codes"],
        "H1C_PARENT_RESOLVED_STOP_NOT_REMOVED",
    )
    require(
        "H1_MASTER_ARCHITECTURE_CHOICE_REQUIRED" in nodes["H1c3"]["failure_codes"],
        "H1C3_OWNER_STOP_MISSING",
    )
    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H1C2_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")
    require(
        state["h1c2_raw_integral_crosswalk"]["next_worker_leaf"] is None,
        "H1C2_NEXT_WORKER_LEAF_NOT_NULL",
    )

    if state["revision"] == 17:
        counts: dict[str, int] = {}
        for node in nodes.values():
            status = node["proof_status"]
            counts[status] = counts.get(status, 0) + 1
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H1C2_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H1C2_NODE_COUNT_DRIFT:{status}")
    else:
        counts = {}
        for node in nodes.values():
            status = node["proof_status"]
            counts[status] = counts.get(status, 0) + 1

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H1C2_ACTIVE_LEAF_DRIFT")
    require(
        state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING",
        "H1C2_ACTIVE_STOP_DRIFT",
    )
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H1C2_BUS_010_CREATED")
    require("NO_RH" in cert["explicit_nonclaims"], "H1C2_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H1C2_RAW_INTEGRAL_CROSSWALK_REV17_VALID",
        "h1c2": "PROVED_ALL_Z_INCLUDING_LATTICE",
        "finite_fplus_centered_integral": "EXPLICIT_RAW_AT_NEGATED_ARGUMENT",
        "h1c3": "OPEN_MASTER_ARCHITECTURE_CHOICE_REQUIRED",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
