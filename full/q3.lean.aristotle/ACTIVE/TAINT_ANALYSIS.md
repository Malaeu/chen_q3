# Taint Analysis (FRI‑Style)

**Purpose:** Bubble up errors from leaves to the root so we don’t spend effort on tainted proofs.
**Current status (1–3 lines):**
- Implemented file‑level taint propagation across Q3 import graph.
**Next action (1–2 lines):**
- Add numeric checks for critical nodes (PrimeCert, A3 floor) and re‑run taint graph.
**Links (3–6):**
- `ACTIVE/TAINT_GRAPH.json`
- `ACTIVE/NUMERIC_CHECKS.json`
- `ACTIVE/NUMERIC_CHECKS_REPORT.json`
- `ACTIVE/SORRY_FRONTIER.md`
- `ACTIVE/PROOF_GRAPH.md`

---

## Status Model

- **VERIFIED**: no local `sorry`, no tainted dependencies.
- **SORRY**: file contains `sorry`.
- **TAINTED**: file itself is clean, but depends on SORRY/TAINTED.
- **BROKEN**: numeric counterexample or failed sanity check.
- **DOOMED**: kill‑switch state (BROKEN or excessive risk score).

## Pipeline

1. `./scripts/numeric_sanity_check.py --write-back` *(optional)*
2. `./scripts/build_taint_graph.py`
3. `./scripts/build_proof_graph.py`

## Planner Rule

Agent should target only **lowest‑level SORRY nodes** with `numeric_check=PASS`.
Do **not** work on VERIFIED/TAINTED nodes.

## Risk Model

- Config: `ACTIVE/RISK_MODEL.json`
- `risk_score = intrinsic_risk + sum(dependencies)`
- If `risk_score > risk_threshold` and `kill_switch_on_risk=true`, node becomes **DOOMED**.
