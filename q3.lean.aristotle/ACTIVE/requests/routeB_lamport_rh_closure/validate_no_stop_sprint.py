#!/usr/bin/env python3
"""Fail-closed integration validator for the owner-launched T0--T5 sprint."""

from __future__ import annotations

import csv
import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def pinned(path: str, expected: str, code: str) -> Path:
    target = REPO_ROOT / path
    require(target.is_file(), f"{code}_MISSING:{path}")
    require(sha256(target) == expected, f"{code}_HASH_DRIFT:{path}")
    return target


def main() -> None:
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))
    sprint = state["no_stop_sprint"]
    queue = sprint["queue"]

    require(state["revision"] >= 13, "NOSTOP_STATE_REVISION_TOO_OLD")
    require(sprint["status"] == "COMPLETED_FAIL_CLOSED_NOT_RH", "NOSTOP_SPRINT_NOT_COMPLETE")
    require(sprint["rh_status"] == "NOT_RH", "NOSTOP_RH_OVERCLAIM")
    pinned(
        "q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/CODEX_NOSTOP_SPRINT_2026-07-12.md",
        sprint["authority_sha256"],
        "NOSTOP_AUTHORITY",
    )

    t0 = queue["T0"]
    t0_path = pinned(
        f"q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/{t0['artifact']}",
        t0["sha256"],
        "NOSTOP_T0",
    )
    t0_text = t0_path.read_text(encoding="utf-8")
    require(t0["code"] == "NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE", "NOSTOP_T0_CODE_DRIFT")
    require(t0["code"] in t0_text, "NOSTOP_T0_VERDICT_MISSING")

    t1 = queue["T1"]
    t1_path = pinned(
        f"q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/{t1['certificate']}",
        t1["certificate_sha256"],
        "NOSTOP_T1_CERT",
    )
    t1_cert = json.loads(t1_path.read_text(encoding="utf-8"))
    require(t1_cert["overall_status"] == "PARTIAL_BLOCKED_MISSING_LAMBDA17_PERSISTED_VECTOR", "NOSTOP_T1_OVERCLAIM")
    require(t1_cert["judges"]["J2_N_stability_13_90_vs_120"]["pass"] is True, "NOSTOP_T1_N_STABILITY_FAIL")
    require(t1_cert["judges"]["J4_central_zero_plant"]["status"] == "B_CENTRAL_ZERO_CELL_FIRES", "NOSTOP_T1_PLANT_INERT")
    require(t1_cert["judges"]["P3_abs_bDet_sqrt_lambda_factor3"]["score_status"] == "NOT_FULLY_SCORED_LAMBDA17_MISSING", "NOSTOP_T1_P3_PROMOTED")

    t2 = queue["T2"]
    t2_path = pinned(
        f"q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/{t2['artifact']}",
        t2["sha256"],
        "NOSTOP_T2",
    )
    raw_path = pinned(
        f"q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/{t2['raw']}",
        t2["raw_sha256"],
        "NOSTOP_T2_RAW",
    )
    require(t2["code"] in t2_path.read_text(encoding="utf-8"), "NOSTOP_T2_CODE_MISSING")
    with raw_path.open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    require(len(rows) == 3, "NOSTOP_T2_RAW_ROW_DRIFT")
    require(all(row["calibration_status"] == "NOT_RUN_INPUT_MISSING" for row in rows), "NOSTOP_T2_VALUE_SMUGGLED")

    nodes = state["nodes"]
    require(nodes["D0.7e.5a"]["proof_status"] == "BLOCKED", "NOSTOP_5A_FALSE_PASS")
    require(nodes["D0.7e.5b"]["proof_status"] == "PROVED", "NOSTOP_5B_NOT_PROVED")
    require(nodes["D0.7e.5c"]["proof_status"] == "OPEN", "NOSTOP_5C_FALSE_PASS")
    require(nodes["D0.7e.5d"]["proof_status"] == "PROVED", "NOSTOP_5D_NOT_PROVED")
    require(nodes["H3e"]["proof_status"] == "OPEN", "NOSTOP_H3E_FALSE_PASS")
    require(nodes["H3e"].get("name") == "H3e_ExactWPrimeTrackingTheorem", "NOSTOP_H3E_LABEL_DRIFT")

    t5 = queue["T5"]
    require(t5["blocked"] == "ZETA_HALF_ETA_CONTINUATION_BRIDGE_MISSING", "NOSTOP_T5A_BLOCKER_DRIFT")
    forbidden = re.compile(r"\b(sorry|admit)\b|exact\?")
    for name, record in t5["proved_lean"].items():
        path = pinned(record["path"], record["sha256"], f"NOSTOP_T5_{name}")
        text = path.read_text(encoding="utf-8")
        require(forbidden.search(text) is None, f"NOSTOP_T5_HOLE:{name}")
        require("#print axioms" in text, f"NOSTOP_T5_AXIOM_PRINT_MISSING:{name}")
    require(t5["holes"] == 0, "NOSTOP_T5_HOLE_COUNT_DRIFT")

    order = state["owner_authorization"]["wprime_candidate_standing_order"]
    require(order["status"] == "ACTIVE_OWNER_RATIFIED", "NOSTOP_STANDING_ORDER_INACTIVE")
    require(order["ratified_order_sha256"] == "5bf99950fbd6fdca6f1ebae786f98098ac83a0b024e3a04f602b19a24295695b", "NOSTOP_STANDING_ORDER_AUTHORITY_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "NOSTOP_BUS_010_CREATED")
    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "NOSTOP_ACTIVE_LEAF_DRIFT")

    counts: dict[str, int] = {}
    for node in nodes.values():
        counts[node["proof_status"]] = counts.get(node["proof_status"], 0) + 1
    print(json.dumps({
        "verdict": "NOSTOP_SPRINT_T0_T5_COMPLETE_FAIL_CLOSED",
        "queue": {
            "T0": t0["status"],
            "T1": t1["status"],
            "T2": t2["status"],
            "T3": queue["T3"]["status"],
            "T4": queue["T4"]["status"],
            "T5": t5["status"],
        },
        "node_counts": counts,
        "active_leaf": active[0],
        "current_stop": state["resume"]["current_stop"],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
