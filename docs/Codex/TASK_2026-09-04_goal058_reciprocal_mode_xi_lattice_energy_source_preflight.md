# Task — Goal 058: reciprocal-mode ξ-lattice energy source preflight (paper + source, READ-ONLY)

Date: 2026-09-04
Status: `AUTHORIZED_BY_JUDGE_AND_OWNER` — `CHEAPEST_NEXT_ACTION` of verdict `99927f01` (`REQ-2026-09-03-SHELLSEARCH`); owner: run with an Opus agent, do not wait for Codex
Refines (does not replace): `TASK_2026-09-04_goal058_normalized_xi_lattice_eigen_equation_preflight.md` and its report
`docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md`
(code `P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP`; identities LATTICE-1/2/3; new object
`P59_ARCH_PRIME_DIAGONAL_DEFECT_NONDEGENERACY`)

```yaml
TASK_ID: GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
TARGET_ATOM: P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND   # Σ_{n≤N}|Δ_n|²/n² ≤ C/L⁴
JUDGE_PREDICTION: [P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP, 0.40]   # preserved, not re-registered
SUCCESS_CODE: P59_RECIPROCAL_MODE_XI_LATTICE_ENERGY_IDENTITY
FAILURE_CODE: P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
```

## Objects (verdict §Q1 H1, §Q2, CODEX DIRECTIVE)

Even block `K̃` (parity_blocks coordinates), ground row `x = ξ/ξ_0`, target row
`y_n = (−1)^n · centeredXi(x_n)/centeredXi(0)` (so `|x_n − y_n| = |Δ_n|`), `y_0 = 1`,
`R = diag(1/n)`, center-normalized residual `𝓡(u)_n = (K̃u)_n − u_n (K̃u)_0`, `𝓡(x) = 0`.

## Return (judge)

1. the exact target row `y` from centeredXi samples, in source coordinates;
2. the exact residual `𝓡(y)` written in source entries (reuse LATTICE-1/2/3 of the previous report);
3. an identity or a one-sided inequality whose LEFT side is `Σ_{n≤N}|x_n − y_n|²/n² = ‖R(x−y)‖²`
   (e.g. from the quadratic form `⟨R(x−y), K̃-something⟩`, the displacement equation, or the
   reciprocal-mode Gram structure `D R − R D = b rᵀ − r bᵀ` of verdict 3dc82357);
4. the first uncontrolled source term;
5. exactly one code.

## Forbidden (judge + owner)

Lean edits; numerical runs; full resolvent norms `‖(K̃−λ₁)⁻¹‖`, `‖(D−λ₁)⁻¹‖`; absolute or odd-sector
floors; pole/Arch–Prime splitting; post-hoc schedule changes; assuming the target bound under another
name (e.g. bounding `‖R(x−y)‖` by `‖𝓡(y)‖` through a stability constant that is itself `1/λ₂`).
Two-by-two plant `K_t = [[λ+b²/t, b],[b, λ+t]]`: any argument that bounds `‖R(x−y)‖` for the plant is
generic and must be rejected. If the derivation's first quantitative step is any of the above, issue
the failure code with the exact term.

## Report

`docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT.md`:
items 1–5, the plant check, what is Lean-ready vs NEW_ANALYTIC, and one paragraph for the numerical
companion (which quadratic form to evaluate on m = 13..163 to test the identity to working precision).
