#!/usr/bin/env python3
"""Pure consumer-first proof-loop contract shared by startup and runtime.

The module compiles current physical state into a machine-readable operating
card.  It selects no mathematical route, writes nothing, and never promotes a
candidate into proof.  Missing contract data remains explicit and fail-closed.
"""

from __future__ import annotations

from contextlib import closing
import sqlite3
from pathlib import Path
from typing import Any


SCHEMA = "q3_proof_loop.v1"
MODE = "CONSUMER_FIRST"
FINAL_CONSUMER = "PX_RH_CLAIM"
EXACT_CONSUMER_FIELDS = (
    "object",
    "space",
    "quantifiers",
    "normalization",
    "hypotheses",
    "output",
)
SELECTION_COST_FACTORS = (
    "proof_difficulty",
    "semantic_gap",
    "lean_formalization_cost",
    "dependency_risk",
    "unverified_assumptions",
)
CYCLE = (
    "SESSION_RADAR",
    "SELECT_ONE_JOINT",
    "EXACT_CONSUMER_CONTRACT",
    "SHELF_AND_LEDGER_SEARCH",
    "SUPPLIER_PREFLIGHT",
    "MINIMAL_BRIDGE",
    "LEAN_CERTIFICATION",
    "TRANSACTIONAL_CLOSE",
    "GRAPH_RECOMPUTATION",
)
TOOL_SUPPLIERS = {
    "planning": ("cartographer-brief", "cheap-closure-finder", "goal-run-selector"),
    "discovery": ("ask-shelf", "kb-query"),
    "compatibility": ("supplier-preflight",),
    "gap_solving": ("research-debt-challenge", "workflow-runtime"),
    "certification": ("lean-validation", "three-body-loop"),
    "closure": (
        "knowledge-spine-step-close",
        "workflow-session-close",
        "workflow-phase-close",
    ),
    "publication": ("blueprint-skeleton-generator",),
}


def goal_assembly_chain(goal_path: Path | None) -> str | None:
    if goal_path is None or not goal_path.is_file():
        return None
    for line in goal_path.read_text(encoding="utf-8").splitlines():
        if line.startswith("ASSEMBLY_CHAIN:"):
            value = line.partition(":")[2].strip()
            return value or None
    return None


def assembly_snapshot(db_path: Path, *, chain: str | None = None) -> dict[str, Any]:
    """Return read-only legacy assembly bookkeeping and open addresses.

    These row counts are never a proof percentage.  Exact roof closure lives in
    ``roof_port_ledger`` and requires seven terms under one dependent context.
    """
    empty = {
        "status": "UNAVAILABLE",
        "global": {
            "total": None,
            "fixed": None,
            "proved": None,
            "validation": None,
            "open": None,
        },
        "selected_chain": None,
        "open_joints": [],
        "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
    }
    if not db_path.is_file():
        return dict(empty, reason="ASSEMBLY_DB_MISSING")
    uri = f"file:{db_path}?mode=ro"
    try:
        with closing(sqlite3.connect(uri, uri=True)) as conn:
            total, proved, validation = conn.execute(
                "SELECT COUNT(*), "
                "SUM(CASE WHEN status = 'READY' THEN 1 ELSE 0 END), "
                "SUM(CASE WHEN status = 'VALIDATION' THEN 1 ELSE 0 END) "
                "FROM assembly"
            ).fetchone()
            proved = int(proved or 0)
            validation = int(validation or 0)
            fixed = proved + validation
            selected = None
            joints: list[dict[str, Any]] = []
            if chain:
                chain_total, chain_proved, chain_validation = conn.execute(
                    "SELECT COUNT(*), "
                    "SUM(CASE WHEN status = 'READY' THEN 1 ELSE 0 END), "
                    "SUM(CASE WHEN status = 'VALIDATION' THEN 1 ELSE 0 END) "
                    "FROM assembly WHERE chain = ?",
                    (chain,),
                ).fetchone()
                chain_proved = int(chain_proved or 0)
                chain_validation = int(chain_validation or 0)
                chain_fixed = chain_proved + chain_validation
                selected = {
                    "chain": chain,
                    "total": int(chain_total),
                    "fixed": chain_fixed,
                    "proved": chain_proved,
                    "validation": chain_validation,
                    "open": int(chain_total) - chain_fixed,
                }
                rows = conn.execute(
                    "SELECT chain, step, status, requirement, required_by, supplied_by, "
                    "supplier_file, objects FROM assembly "
                    "WHERE chain = ? AND status NOT IN ('READY', 'VALIDATION') "
                    "ORDER BY step",
                    (chain,),
                ).fetchall()
                joints = [
                    {
                        "address": f"{row_chain}:{step}",
                        "chain": row_chain,
                        "step": step,
                        "status": status,
                        "requirement": requirement,
                        "required_by": required_by,
                        "supplied_by": supplied_by,
                        "supplier_file": supplier_file,
                        "objects": objects,
                    }
                    for (
                        row_chain,
                        step,
                        status,
                        requirement,
                        required_by,
                        supplied_by,
                        supplier_file,
                        objects,
                    ) in rows
                ]
    except sqlite3.Error as exc:
        return dict(empty, reason=f"ASSEMBLY_DB_INVALID:{exc}")
    return {
        "status": "AVAILABLE",
        "global": {
            "total": int(total),
            "fixed": fixed,
            "proved": proved,
            "validation": validation,
            "open": int(total) - fixed,
        },
        "selected_chain": selected,
        "open_joints": joints,
        "interpretation": "BOOKKEEPING_ONLY_NOT_PROOF_PERCENTAGE",
    }


def _debt_joints(assembly_debt: list[str]) -> list[dict[str, Any]]:
    joints: list[dict[str, Any]] = []
    for item in assembly_debt:
        parts = item.split(":", 2)
        if len(parts) != 3:
            continue
        chain, step, status = parts
        if status == "VALIDATION":
            continue
        joints.append(
            {
                "address": f"{chain}:{step}",
                "chain": chain,
                "step": step,
                "status": status,
            }
        )
    return joints


def compile_contract(
    *,
    goal_binding: dict[str, Any],
    holds: list[str],
    assembly_debt: list[str],
    assembly: dict[str, Any] | None = None,
    roof_ledger: dict[str, Any] | None = None,
    route: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Compile one honest operating card without inventing a theorem contract."""
    route = route or {}
    action = str(goal_binding.get("action", "HOLD"))
    selected_goal_id = (
        goal_binding.get("selected_goal_id")
        or goal_binding.get("selected_bus_goal_nnn")
        or route.get("goal")
    )
    selected_goal_path = (
        goal_binding.get("selected_goal_path")
        or goal_binding.get("selected_bus_goal_path")
        or route.get("selected_goal_path")
    )
    exact = goal_binding.get("exact_consumer_contract")
    exact_bound = isinstance(exact, dict) and all(
        isinstance(exact.get(field), str) and exact[field].strip()
        for field in EXACT_CONSUMER_FIELDS
    )
    exact_contract = {
        "status": "BOUND" if exact_bound else "UNBOUND",
        **{
            field: exact.get(field) if exact_bound else None
            for field in EXACT_CONSUMER_FIELDS
        },
    }

    assembly = assembly or {
        "status": "UNAVAILABLE",
        "global": {
            "total": None,
            "fixed": None,
            "proved": None,
            "validation": None,
            "open": None,
        },
        "selected_chain": None,
        "open_joints": _debt_joints(assembly_debt),
    }
    candidates = list(assembly.get("open_joints") or _debt_joints(assembly_debt))
    blocking = sorted(set(item for item in holds if item))
    if blocking or action == "HOLD":
        joint = {
            "status": "BLOCKED",
            "address": None,
            "selection_reason": "canonical hold prevents mathematical dispatch",
            "candidates": candidates,
        }
    elif not exact_bound:
        joint = {
            "status": "CONTRACT_REQUIRED",
            "address": None,
            "selection_reason": (
                "physical goal is selected; brief and cheap rank candidates, then the "
                "exact consumer contract must be bound before proof work"
            ),
            "candidates": candidates,
        }
    else:
        joint = {
            "status": "READY_FOR_PREFLIGHT",
            "address": goal_binding.get("joint_address"),
            "selection_reason": "exact consumer contract is bound",
            "candidates": candidates,
        }

    return {
        "schema": SCHEMA,
        "mode": MODE,
        "policy_change": False,
        "honesty_state": "CHALLENGER_NOT_RH",
        "final_consumer": FINAL_CONSUMER,
        "verified_frontier": {
            "status": (
                "ASSEMBLY_CHAIN_BOUND"
                if isinstance(assembly.get("selected_chain"), dict)
                else "UNBOUND"
            ),
            "selected_chain": assembly.get("selected_chain"),
            "selected_goal_id": selected_goal_id,
            "selected_goal_path": selected_goal_path,
            "active_dependency_root": route.get("dependency_root"),
            "stage_id": route.get("stage_id"),
            "route_status": route.get("status"),
            "selector_action": action,
        },
        "cords": assembly,
        "roof_port_ledger": roof_ledger or {
            "schema": "q3_roof_port_supplier_ledger.v1",
            "integrity_status": "UNAVAILABLE",
            "semantic_slot_count": 6,
            "direct_proof_input_count": 7,
            "port_summary": {
                "jointly_bound": None,
                "candidate_supplier_terms": None,
                "without_exact_supplier": None,
                "total": 7,
                "status": "UNAVAILABLE",
            },
            "proof_percentage_interpretation": "REJECTED",
        },
        "exact_consumer_contract": exact_contract,
        "next_joint": joint,
        "selection_cost_factors": list(SELECTION_COST_FACTORS),
        "cycle": list(CYCLE),
        "tool_suppliers": {key: list(value) for key, value in TOOL_SUPPLIERS.items()},
        "recompute_after_close": True,
        "holds": blocking,
        "PX_RH_CLAIM": "NOT_MADE",
    }


def render_battle_brief(contract: dict[str, Any]) -> str:
    cords = contract.get("cords", {}).get("global", {})
    roof = contract.get("roof_port_ledger", {})
    port_summary = roof.get("port_summary", {})
    frontier = contract.get("verified_frontier", {})
    exact = contract.get("exact_consumer_contract", {})
    joint = contract.get("next_joint", {})
    selected_chain = frontier.get("selected_chain")
    ports = roof.get("ports") or []
    candidate_ports = [row.get("port") for row in ports if row.get("supplier_term")]
    no_supplier_ports = [row.get("port") for row in ports if not row.get("supplier_term")]
    if isinstance(selected_chain, dict):
        frontier_text = (
            f"{selected_chain.get('chain')} · {selected_chain.get('fixed')}/"
            f"{selected_chain.get('total')} fixed rows"
        )
    else:
        frontier_text = frontier.get("status", "UNBOUND")
    lines = [
        "Q3 PROOF LOOP — BATTLE BRIEF",
        (
            "  assembly bookkeeping (not proof %): fixed rows "
            f"{cords.get('fixed') if cords.get('fixed') is not None else '—'}/"
            f"{cords.get('total') if cords.get('total') is not None else '—'} · "
            f"READY rows {cords.get('proved') if cords.get('proved') is not None else '—'} · "
            f"validation {cords.get('validation') if cords.get('validation') is not None else '—'} · "
            f"open rows {cords.get('open') if cords.get('open') is not None else '—'}"
        ),
        (
            "  roof ports: "
            f"{port_summary.get('jointly_bound') if port_summary.get('jointly_bound') is not None else '—'}/"
            f"{port_summary.get('total', 7)} jointly bound · "
            f"{port_summary.get('candidate_supplier_terms') if port_summary.get('candidate_supplier_terms') is not None else '—'} candidate suppliers · "
            f"{port_summary.get('without_exact_supplier') if port_summary.get('without_exact_supplier') is not None else '—'} without exact supplier"
        ),
        (
            "  roof contract: "
            f"{roof.get('semantic_slot_count', 6)} semantic slots · "
            f"{roof.get('direct_proof_input_count', 7)} direct proof inputs · "
            f"{roof.get('integrity_status', 'UNAVAILABLE')}"
        ),
        (
            "  roof quarantine: "
            f"{len(roof.get('assembly_bookkeeping', {}).get('quarantined_edges', []))} "
            "legacy fixed edge(s) excluded from roof closure"
        ),
        f"  candidate roof ports: {', '.join(candidate_ports) if candidate_ports else '—'}",
        f"  no exact supplier: {', '.join(no_supplier_ports) if no_supplier_ports else '—'}",
        f"  live goal: {frontier.get('selected_goal_id') or '—'}",
        f"  verified frontier: {frontier_text}",
        f"  active dependency root: {frontier.get('active_dependency_root') or '—'}",
        f"  exact consumer contract: {exact.get('status', 'UNBOUND')}",
        f"  next joint: {joint.get('status', 'BLOCKED')}",
    ]
    if joint.get("address"):
        lines.append(f"  joint address: {joint['address']}")
    holds = contract.get("holds") or []
    lines.append(f"  route blocker: {holds[0] if holds else 'NONE'}")
    lines.append("  control gate: strict startup result is authoritative")
    lines.append("  loop: contract → suppliers → preflight → bridge → Lean → close → recompute")
    return "\n".join(lines) + "\n"
