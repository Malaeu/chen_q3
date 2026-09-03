# Task — Goal 058: winding lock on a fixed compact (paper + source, READ-ONLY)

Date: 2026-09-04 · Status: `AUTHORIZED_BY_JUDGE_AND_OWNER` (verdict LEAKAGE, RANKED_NEXT_ACTION `PAPER_PREFLIGHT_P59_ANCHORED_LOG_DERIVATIVE_FIXED_COMPACT`; owner: Opus agent) · Lean execution NOT authorized.

```yaml
TASK_ID: GOAL058_P59_ANCHORED_LOG_DERIVATIVE_FIXED_COMPACT_PREFLIGHT
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
EXACT_TARGET: P59_FIXED_COMPACT_LOG_DERIVATIVE_WINDING_LOCK
SUFFICIENT_INTERFACE: boundary nonvanishing of both transforms + length(∂D)/(2π) · sup_{∂D} |F_g'/F_g − F_t'/F_t| < 1  ⇒  equal zero counts with multiplicity inside D
DISCRIMINATOR: P59_FIXED_COMPACT_WINDING_NUMBER_DIFFERENCE (argument principle; planted failure F·(1 − z²/a²) renormalized at the anchor: count change +2)
```
Required: (1) the exact statement (Rouché / argument-principle form) in the project's objects, with the common P59 lattice factor
`2 L^{-1/2} sin(zL/2)` cancelled in the log-derivative difference (judge: "cancel the common P59 lattice factor and compare finite
numerator divisors"); (2) which pairs it applies to: ground vs trial (CCM §7 prolate trial as built in `edge_ledger_relritz.py`), ground vs
Xi-sample row (its transform has complex zeros: state where the boundary guard fails), ground vs Ξ itself (target crosswalk: Ξ is not a
P59 transform — what replaces the cancelled lattice factor); (3) what source input would bound `sup_{∂D}|Δ log-derivative|` without a
full inverse or a floor (name the first uncontrolled term); (4) the planted failure and two more plants; (5) an interval-test design for a
production cell (which boundary, which precision, how to certify boundary nonvanishing); (6) Lean-ready vs new analytic (Mathlib has
Jensen's formula and the argument principle? check `Mathlib/Analysis/Complex/` for winding numbers / argument principle and name what exists).
Forbidden: numerics; Lean edits; assuming the desired convergence; complement floors; `‖(K−λ₁)⁻¹‖`.
Report: `docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_WINDING_LOCK_FIXED_COMPACT_PREFLIGHT.md`.
