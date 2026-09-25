#!/usr/bin/env python3
"""Current-HEAD reverse ledger for the canonical Route-B roof.

Canonical roof (owner decision 2026-09-25): the Goal058 consumer
``Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi``.  It turns one entire
real-zero family ``F`` converging locally uniformly to ``centeredXi`` on the
centered critical strip into ``Q3.RH``.  The older 7-port canonical-slots
roof is historical.

The legacy ``assembly`` table is useful bookkeeping, but it is not a proof
percentage.  This module reads the roof declaration, its axiom receipt, the
active phase key, and the legacy assembly rows without mutating any of them.
It exposes the three formal roof inputs under the one shared family ``F``.
"""

from __future__ import annotations

import argparse
from contextlib import closing
import json
import re
import sqlite3
import subprocess
import sys
from pathlib import Path
from typing import Any


SCHEMA = "q3_roof_port_supplier_ledger.v2"
ROOF_THEOREM = "Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi"
ROOF_SHORT_NAME = "rh_of_real_zero_family_tendsto_centeredXi"
ROOF_SOURCE = Path("q3.lean.aristotle/Q3/Proofs/RouteB/Goal058DirectGroundZeroEscape.lean")
AXIOM_RECEIPT = Path("docs/semantic_quarantine/GOAL058_ROOF_AXIOM_RECEIPT.md")
CHANNEL_RUNTIME = Path("orchestrator/state/CHANNEL_RUNTIME.json")
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
SEMANTIC_SLOTS = ["real zeros", "entire", "locally uniform convergence to centeredXi"]
BUNDLED_CONTEXT = ["F : ℕ → ℂ → ℂ"]
TAIL_REINDEX = "q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTailReindex.lean"
TRACKED_TRANSFORM = "q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean"
TRACKED_FAMILY = "selectedFerrersTrackedGroundTransformAt P (φ n) beta hfloorAt"
SHARED_UNIFIER = "F n = tracked ground transform at φ n"
SOURCE_FAMILY = "SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM"
NORMALIZATION = "GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z"


PORT_SPECS: tuple[dict[str, Any], ...] = (
    {
        "port": "hzeros",
        "semantic_role": "real zeros",
        "exact_type": "∀ k, ZerosRealOn Set.univ (F k)",
        "downstream_consumer": f"{ROOF_THEOREM}.hzeros",
        "supplier_term": "Q3.RouteB.D0Pstar.selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors",
        "candidates": [
            (
                TAIL_REINDEX,
                "selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors",
                "ZerosRealOn Set.univ",
            )
        ],
        "adapters": [],
        "shared_unifier": SHARED_UNIFIER,
        "source_family": SOURCE_FAMILY,
        "normalization": NORMALIZATION,
        "scope": "tail φ n, given eventual floors",
        "status": "CONDITIONAL_CANDIDATE_FLOORS_OPEN",
        "missing_obligation": "G1 floors: hfloorEv, hoddEv, hratioEv.",
        "assembly_aliases": ["hzeros"],
    },
    {
        "port": "hentire",
        "semantic_role": "entire",
        "exact_type": "∀ k, Differentiable ℂ (F k)",
        "downstream_consumer": f"{ROOF_THEOREM}.hentire",
        "supplier_term": "Q3.RouteB.D0Pstar.differentiable_selectedFerrersTrackedGroundTransformAt",
        "candidates": [
            (
                TRACKED_TRANSFORM,
                "differentiable_selectedFerrersTrackedGroundTransformAt",
                "Differentiable ℂ",
            )
        ],
        "adapters": [],
        "shared_unifier": SHARED_UNIFIER,
        "source_family": SOURCE_FAMILY,
        "normalization": NORMALIZATION,
        "scope": "every index and every floor witness",
        "status": "SUPPLIER_PROVED_FAMILY_UNBOUND",
        "missing_obligation": "Bind the same F.",
        "assembly_aliases": ["hentire"],
    },
    {
        "port": "hconv",
        "semantic_role": "locally uniform convergence to centeredXi",
        "exact_type": "TendstoLocallyUniformlyOn F centeredXi Filter.atTop centeredCriticalStrip",
        "downstream_consumer": f"{ROOF_THEOREM}.hconv",
        "supplier_term": None,
        "candidates": [],
        "adapters": [],
        "shared_unifier": SHARED_UNIFIER,
        "source_family": SOURCE_FAMILY,
        "normalization": NORMALIZATION,
        "scope": "compact subsets of centeredCriticalStrip",
        "status": "NO_SUPPLIER",
        "missing_obligation": "G3 compact decay; G3c/G4 trial to Xi (hmode, hχ/hθ); assembly to hconv.",
        "assembly_aliases": ["hconv"],
    },
)


def _git(repo: Path, *args: str) -> str | None:
    proc = subprocess.run(
        ["git", *args], cwd=repo, text=True, capture_output=True, check=False
    )
    return proc.stdout.strip() if proc.returncode == 0 else None


def _normalized(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _tracked_binding(repo: Path, rel: Path) -> dict[str, Any]:
    head_blob = _git(repo, "rev-parse", f"HEAD:{rel.as_posix()}")
    worktree_blob = (
        _git(repo, "hash-object", rel.as_posix()) if (repo / rel).is_file() else None
    )
    return {
        "path": rel.as_posix(),
        "head_blob": head_blob,
        "worktree_blob": worktree_blob,
        "status": (
            "HEAD_LOCKED"
            if head_blob and head_blob == worktree_blob
            else "WORKTREE_OR_TRACKING_DRIFT"
        ),
    }


def _roof_source_contract(repo: Path) -> dict[str, Any]:
    binding = _tracked_binding(repo, ROOF_SOURCE)
    path = repo / ROOF_SOURCE
    source = path.read_text(encoding="utf-8") if path.is_file() else ""
    normalized = _normalized(source)
    required_fragments = [
        "theorem rh_of_real_zero_family_tendsto_centeredXi (F : ℕ → ℂ → ℂ) (hzeros : ∀ k, ZerosRealOn Set.univ (F k)) (hentire : ∀ k, Differentiable ℂ (F k)) (hconv : TendstoLocallyUniformlyOn F centeredXi Filter.atTop centeredCriticalStrip) : Q3.RH",
        "#print axioms rh_of_real_zero_family_tendsto_centeredXi",
    ]
    missing = [
        fragment for fragment in required_fragments if fragment not in normalized
    ]
    binding["contract_status"] = (
        "EXACT_SIGNATURE_PRESENT" if not missing else "SIGNATURE_DRIFT"
    )
    binding["missing_fragments"] = missing
    return binding


def _axiom_receipt(repo: Path, roof_binding: dict[str, Any]) -> dict[str, Any]:
    path = repo / AXIOM_RECEIPT
    text = path.read_text(encoding="utf-8") if path.is_file() else ""
    head_match = re.search(r"(?m)^audited_baseline_head:\s*([0-9a-f]{40})\s*$", text)
    audited_head = head_match.group(1) if head_match else None
    audited_blob = (
        _git(repo, "rev-parse", f"{audited_head}:{ROOF_SOURCE.as_posix()}")
        if audited_head
        else None
    )
    exact_line = (
        f"'{ROOF_THEOREM}' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]"
    )
    current_blob = roof_binding.get("head_blob")
    status = "CURRENT_SOURCE_MATCHES_AUDITED_AXIOM_RECEIPT"
    if not audited_blob or audited_blob != current_blob or exact_line not in text:
        status = "AXIOM_RECEIPT_STALE_OR_MISSING"
    return {
        "path": AXIOM_RECEIPT.as_posix(),
        "audited_baseline_head": audited_head,
        "audited_source_blob": audited_blob,
        "current_source_blob": current_blob,
        "axioms": EXPECTED_AXIOMS,
        "status": status,
    }


def _phase_binding(repo: Path) -> dict[str, Any]:
    path = repo / CHANNEL_RUNTIME
    try:
        runtime = json.loads(path.read_text(encoding="utf-8"))
        phase = runtime.get("active_proshka_phase") or {}
        key = phase.get("phase_key") or {}
    except (OSError, json.JSONDecodeError):
        return {"status": "UNAVAILABLE"}
    terminal = key.get("terminal_consumer_id")
    return {
        "status": (
            "BOUND_TO_ROOF"
            if terminal == ROOF_THEOREM
            else "TERMINAL_CONSUMER_MISMATCH"
        ),
        "phase_id": phase.get("phase_id"),
        "source_object_family_id": key.get("source_object_family_id"),
        "terminal_consumer_id": terminal,
        "convention_lock_id": key.get("convention_lock_id"),
        "honesty_state": key.get("honesty_state"),
    }


def _candidate_receipts(
    repo: Path, candidates: list[tuple[str, str, str]]
) -> list[dict[str, Any]]:
    receipts: list[dict[str, Any]] = []
    for raw_path, declaration, target in candidates:
        rel = Path(raw_path)
        binding = _tracked_binding(repo, rel)
        source_path = repo / rel
        source = (
            source_path.read_text(encoding="utf-8") if source_path.is_file() else ""
        )
        start = source.find(declaration)
        window = source[start : start + 5000] if start >= 0 else ""
        signature_present = start >= 0 and target in window
        axiom_probe_present = f"#print axioms {declaration}" in source
        receipts.append(
            {
                **binding,
                "declaration": declaration,
                "target_fragment": target,
                "signature_status": (
                    "TARGET_PRESENT" if signature_present else "TARGET_MISSING"
                ),
                "axiom_probe": "PRESENT" if axiom_probe_present else "NOT_PRESENT",
            }
        )
    return receipts


def _assembly_projection(db_path: Path) -> dict[str, Any]:
    unavailable = {
        "status": "UNAVAILABLE",
        "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
        "global": {},
        "latest_run_ids": [],
        "port_edges": {},
        "quarantined_edges": [],
    }
    if not db_path.is_file():
        return unavailable
    try:
        with closing(sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)) as conn:
            conn.row_factory = sqlite3.Row
            total, ready, validation = conn.execute(
                "SELECT COUNT(*), "
                "SUM(CASE WHEN status='READY' THEN 1 ELSE 0 END), "
                "SUM(CASE WHEN status='VALIDATION' THEN 1 ELSE 0 END) FROM assembly"
            ).fetchone()
            rows = conn.execute(
                "SELECT chain,step,status,requirement,required_by,supplied_by,"
                "supplier_file,objects,run_id FROM assembly ORDER BY chain,step"
            ).fetchall()
    except sqlite3.Error as exc:
        return {**unavailable, "reason": f"ASSEMBLY_DB_INVALID:{exc}"}

    port_edges: dict[str, list[dict[str, Any]]] = {
        spec["port"]: [] for spec in PORT_SPECS
    }
    quarantined: list[dict[str, Any]] = []
    for row in rows:
        record = dict(row)
        required_by = str(record.get("required_by") or "")
        for spec in PORT_SPECS:
            if any(alias in required_by for alias in spec["assembly_aliases"]):
                port_edges[spec["port"]].append(record)
        supplied_by = str(record.get("supplied_by") or "")
        if (
            record["status"] in {"READY", "VALIDATION"}
            and ROOF_SHORT_NAME in supplied_by
        ):
            quarantined.append(
                {
                    "address": f"{record['chain']}:{record['step']}",
                    "legacy_status": record["status"],
                    "reason": "CONDITIONAL_ROOF_WRAPPER_HAS_UNBOUND_DIRECT_PREMISES",
                    "action": "EXCLUDED_FROM_ROOF_PORT_CLOSURE; LEGACY_ROW_PRESERVED",
                }
            )
    fixed = int(ready or 0) + int(validation or 0)
    return {
        "status": "AVAILABLE",
        "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
        "global": {
            "total": int(total or 0),
            "fixed": fixed,
            "ready": int(ready or 0),
            "validation": int(validation or 0),
            "open": int(total or 0) - fixed,
        },
        "latest_run_ids": sorted({str(row["run_id"]) for row in rows}),
        "port_edges": port_edges,
        "quarantined_edges": quarantined,
    }


def build(repo: Path, db_path: Path) -> dict[str, Any]:
    """Build the source-locked dependent roof ledger without writing state."""
    repo = repo.resolve()
    head = _git(repo, "rev-parse", "HEAD")
    roof_binding = _roof_source_contract(repo)
    receipt = _axiom_receipt(repo, roof_binding)
    phase = _phase_binding(repo)
    assembly = _assembly_projection(db_path.resolve())
    ports: list[dict[str, Any]] = []
    candidate_count = 0
    no_supplier_count = 0
    for spec in PORT_SPECS:
        candidates = _candidate_receipts(repo, spec["candidates"])
        candidate_source_locked = bool(candidates) and all(
            row["status"] == "HEAD_LOCKED"
            and row["signature_status"] == "TARGET_PRESENT"
            for row in candidates
        )
        status = spec["status"]
        if candidates and not candidate_source_locked:
            status = "CANDIDATE_SOURCE_DRIFT"
        if spec["supplier_term"] is None:
            no_supplier_count += 1
        else:
            candidate_count += 1
        ports.append(
            {
                "port": spec["port"],
                "semantic_role": spec["semantic_role"],
                "exact_type": spec["exact_type"],
                "bundled_context": list(BUNDLED_CONTEXT),
                "downstream_consumer": spec["downstream_consumer"],
                "supplier_term": spec["supplier_term"],
                "adapters": list(spec["adapters"]),
                "shared_unifier": spec["shared_unifier"],
                "source_family": spec["source_family"],
                "normalization": spec["normalization"],
                "scope": spec["scope"],
                "verifier": candidates,
                "axioms": "EXACT_PROFILE_REQUIRES_THE_CANDIDATE_FILE_PRINT_PROBE; ROOF_PROFILE_IS_SOURCE_LOCKED_SEPARATELY",
                "status": status,
                "incoming_assembly_edges": assembly.get("port_edges", {}).get(
                    spec["port"], []
                ),
                "unused_incoming_edges": [],
                "missing_obligation": spec["missing_obligation"],
            }
        )

    integrity = "HEAD_LOCKED"
    integrity_reasons: list[str] = []
    if not head:
        integrity_reasons.append("HEAD_UNAVAILABLE")
    if roof_binding.get("status") != "HEAD_LOCKED":
        integrity_reasons.append("ROOF_SOURCE_NOT_HEAD_LOCKED")
    if roof_binding.get("contract_status") != "EXACT_SIGNATURE_PRESENT":
        integrity_reasons.append("ROOF_SIGNATURE_DRIFT")
    if receipt.get("status") != "CURRENT_SOURCE_MATCHES_AUDITED_AXIOM_RECEIPT":
        integrity_reasons.append("ROOF_AXIOM_RECEIPT_DRIFT")
    if phase.get("status") != "BOUND_TO_ROOF":
        integrity_reasons.append("ACTIVE_PHASE_TERMINAL_CONSUMER_MISMATCH")
    if integrity_reasons:
        integrity = "INVALID"

    return {
        "schema": SCHEMA,
        "generated_from_head": head,
        "integrity_status": integrity,
        "integrity_reasons": integrity_reasons,
        "honesty_state": "CHALLENGER_NOT_RH",
        "roof_theorem": ROOF_THEOREM,
        "semantic_slot_count": len(SEMANTIC_SLOTS),
        "semantic_slots": list(SEMANTIC_SLOTS),
        "direct_proof_input_count": len(PORT_SPECS),
        "assembly_beam": "hconv / TendstoLocallyUniformlyOn F centeredXi",
        "shared_dependent_context": {
            "binder": "F : ℕ → ℂ → ℂ",
            "fields": list(BUNDLED_CONTEXT),
            "selected_family": TRACKED_FAMILY,
            "joint_binding_status": "UNBOUND_CONCRETE_F",
        },
        "roof_source": roof_binding,
        "axiom_receipt": receipt,
        "active_phase_binding": phase,
        "ports": ports,
        "port_summary": {
            "jointly_bound": 0,
            "candidate_supplier_terms": candidate_count,
            "without_exact_supplier": no_supplier_count,
            "total": len(PORT_SPECS),
            "status": "OPEN_SHARED_FAMILY_UNBOUND",
        },
        "assembly_bookkeeping": {
            key: value for key, value in assembly.items() if key != "port_edges"
        },
        "proof_percentage_interpretation": "REJECTED",
        "closed_audit_gap": "EXACT_ROOF_PORT_TO_SUPPLIER_LEDGER_AT_CURRENT_HEAD",
        "current_minimal_gap": "BIND_ONE_CONCRETE_FAMILY_F_ACROSS_ALL_THREE_ROOF_INPUTS",
        "PX_RH_CLAIM": "NOT_MADE",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    parser.add_argument(
        "--db",
        type=Path,
        default=Path("q3.lean.aristotle/aristotle_db/knowledge.db"),
    )
    args = parser.parse_args()
    repo = args.root.resolve()
    db = args.db if args.db.is_absolute() else repo / args.db
    result = build(repo, db)
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    return 0 if result["integrity_status"] == "HEAD_LOCKED" else 2


if __name__ == "__main__":
    raise SystemExit(main())
