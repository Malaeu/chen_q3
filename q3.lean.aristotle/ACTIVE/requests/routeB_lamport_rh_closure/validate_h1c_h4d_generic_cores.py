#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-16 H1c/H4d generic cores."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H1C_H4D_GENERIC_CORES_CERTIFICATE.json"
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

    require(cert["revision_target"] == 16, "H1CH4D_CERT_REVISION_DRIFT")
    require(state["revision"] >= 16, "H1CH4D_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H1CH4D_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H1CH4D_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H1CH4D_SOURCE_{index}")
    pinned(cert["artifact"], "H1CH4D_ARTIFACT")

    lean_texts: dict[str, str] = {}
    for index, proof in enumerate(cert["proof_artifacts"]):
        path = pinned(proof, f"H1CH4D_LEAN_{index}")
        text = path.read_text(encoding="utf-8")
        lean_texts[path.name] = text
        require(FORBIDDEN.search(text) is None, f"H1CH4D_LEAN_HOLE:{path.name}")
        require("#print axioms" in text, f"H1CH4D_AXIOM_PRINT_MISSING:{path.name}")
        for theorem in proof["proved"]:
            require(theorem in text, f"H1CH4D_THEOREM_MISSING:{theorem}")

    h1_text = lean_texts["Proposition59EntireTransform.lean"]
    for token in ("dslope", "Complex.differentiableOn_dslope", "proposition59PoleKernel_at_pole"):
        require(token in h1_text, f"H1C_REMOVABLE_MECHANISM_MISSING:{token}")
    h4_text = lean_texts["SafeRateAssembly.lean"]
    for token in ("[NeBot l]", "hWsq", "sq_le_sq₀", "squeeze_zero'"):
        require(token in h4_text, f"H4D_COFINAL_CORE_TOKEN_MISSING:{token}")

    nodes = state["nodes"]
    h1c = nodes["H1c"]
    require(h1c["kind"] == "AND", "H1C_PARENT_NOT_AND")
    require(h1c["ordered_children"] == ["H1c1", "H1c2", "H1c3"], "H1C_CHILD_ORDER_DRIFT")
    require(h1c["assembly_theorem_id"] == "H1c4", "H1C_ASSEMBLY_ADDRESS_DRIFT")
    for node_id in cert["h1c_repair"]["proved"]:
        require(nodes[node_id]["proof_status"] == "PROVED", f"H1C_PROVED_NODE_DRIFT:{node_id}")
    require(nodes["H1c1"]["validation"] == "PROPOSITION59_RHS_ENTIRE", "H1C1_VERDICT_DRIFT")
    require(
        "H1C_RAW_INTEGRAL_RHS_CROSSWALK_MISSING" in nodes["H1c2"]["failure_codes"],
        "H1C2_RESIDUAL_CROSSWALK_NOT_REGISTERED",
    )

    h4d1 = nodes["H4d1"]
    require(h4d1["kind"] == "AND", "H4D1_PARENT_NOT_AND")
    require(h4d1["ordered_children"] == ["H4d1a", "H4d1b"], "H4D1_CHILD_ORDER_DRIFT")
    require(h4d1["assembly_theorem_id"] == "H4d1c", "H4D1_ASSEMBLY_ADDRESS_DRIFT")
    for node_id in cert["h4d_repair"]["proved"]:
        require(nodes[node_id]["proof_status"] == "PROVED", f"H4D1_PROVED_NODE_DRIFT:{node_id}")
    require(nodes["H4d1b"]["validation"] == "LEAN_SAFE_RATE_COFINAL_SQUARE_CORE", "H4D1B_VERDICT_DRIFT")
    require(
        "H4D_WPRIME_SQUARE_ENVELOPE_MISSING" in nodes["H4d2"]["failure_codes"],
        "H4D2_EXACT_ENVELOPE_GAP_NOT_REGISTERED",
    )

    if state["revision"] == 16:
        for node_id in cert["h1c_repair"]["open"] + cert["h4d_repair"]["open"]:
            require(nodes[node_id]["proof_status"] == "OPEN", f"REV16_EXACT_NODE_FALSE_PASS:{node_id}")
        counts: dict[str, int] = {}
        for node in nodes.values():
            status = node["proof_status"]
            counts[status] = counts.get(status, 0) + 1
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H1CH4D_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H1CH4D_NODE_COUNT_DRIFT:{status}")
    else:
        counts = {}
        for node in nodes.values():
            status = node["proof_status"]
            counts[status] = counts.get(status, 0) + 1

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H1CH4D_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H1CH4D_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H1CH4D_BUS_010_CREATED")
    require("NO_RH" in cert["explicit_nonclaims"], "H1CH4D_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H1C_H4D_GENERIC_CORES_REV16_VALID",
        "h1c": "PROPOSITION59_RHS_ENTIRE_INTEGRAL_AND_MASTER_OPEN",
        "h4d1": "COFINAL_SQUARE_RATE_PACKAGE_PROVED_EXACT_ENVELOPE_OPEN",
        "node_counts": counts,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
