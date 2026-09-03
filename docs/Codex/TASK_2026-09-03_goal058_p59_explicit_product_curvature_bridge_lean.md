# Codex task — Goal 058: formalize the P59 explicit-product curvature bridge (Lean)

Date: 2026-09-03 (late evening)
Status: `AUTHORIZED_BY_JUDGE_CODEX_DIRECTIVE`
Parent: verdict `926c1865` (`REQ-2026-09-03-CURVBRIDGE`, `FORMALIZE_P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE`)
Author: Linux-Claude (observer), transcribing the judge's CODEX DIRECTIVE; the paper proof at Lean granularity is in the verdict §2.1–2.7
Worktree: Codex's own, rebased on `origin/rh_clean`; prefix `[Linux-Codex][rh_clean][Goal058]`; push the branch and name it, Linux-Claude fast-forwards `rh_clean`
Priority: this task supersedes Part B of `TASK_2026-09-03_goal058_curvature_bordered_secular_source_preflight.md` where they overlap; Parts A and C of that task stand.

```yaml
TASK_ID: GOAL058_P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
CLOSES: [P59_SPECIFIC_CURVATURE_TO_LOCAL_BOUNDEDNESS, CODEX_ITEM_5_MATHLIB_GAP_NAMED]
OPENS: []
```

## Theorem to formalize (verdict §2.1, Lean-typed)

Let `L > 0`, `I_N = Icc (-N) N`, `x_k = 2πk/L`, `v : ℤ → ℝ` with `v (-k) = v k`,
`F = proposition59RawTransform L I_N (fun k => (v k : ℂ))`. Assume `ZerosRealOn Set.univ F`
and `F 0 ≠ 0`. Then there is a real `κ_F ≥ 0` with
- `-(iteratedDeriv 2 F 0) / (2 * F 0) = (κ_F : ℂ)`  (κ is REAL; do not order a complex number);
- `κ_F = Σ_{ρ ∈ R_N⁺} 1/ρ² + (L²/(4π²)) Σ_{k>N} 1/k²`, `R_N⁺` the multiset of positive roots of the
  finite Cauchy numerator `P_N`;
- `∀ z, ‖F z‖ ≤ ‖F 0‖ * Real.exp (κ_F * ‖z‖²)`;
- `κ_F = (L²/2) * (1/12 + (1/(2π² v 0)) Σ_{k ≠ 0} v k / k²)`.

## Target file and imports (judge)

`q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean`
imports: `Q3.Proofs.RouteB.Proposition59EntireTransform`,
`Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge`,
`Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd`, `Mathlib.NumberTheory.ZetaValues`.
Mathlib facts named by the judge: `Complex.tendsto_euler_sin_prod`,
`Polynomial.Splits.eq_prod_roots_of_monic`, `Polynomial.Splits.eval_eq_prod_roots_of_monic`,
`Real.prod_one_add_le_exp_sum`, `hasSum_zeta_two`.

## Prove in this order (judge), each kernel-green before the next

1. `P59_FINITE_CAUCHY_NUMERATOR_IDENTITY` — define `D_N(z) = Π_{k∈I_N}(z − x_k)` and `P_N`;
   prove the off-lattice Cauchy quotient `Σ v_k/(z − x_k) = P_N(z)/D_N(z)` and
   `P_N(x_j) = v_j Π_{k≠j}(x_j − x_k)`.
2. `P59_NUMERATOR_ROOT_IMP_TRANSFORM_ROOT` — split included-lattice and off-lattice cases; use
   `proposition59PoleKernel_at_lattice_sign` for the included case (exact sampling
   `F(x_j) = √L (−1)^j v_j`). Never cancel the sine against the denominator globally.
3. `P59_EVEN_REAL_ROOTED_POLYNOMIAL_QUADRATIC_PRODUCT` — from real coefficients, evenness,
   `P_N(0) ≠ 0`, real roots: the positive-root multiset and `P_N(z)/P_N(0) = Π (1 − z²/ρ²)`.
   Use `Polynomial.Splits.eq_prod_roots_of_monic`; no Hadamard.
4. `P59_NORMALIZED_EULER_TAIL_PRODUCT` — `Complex.tendsto_euler_sin_prod`; cancel only off the
   finite lattice; extend to all `z` by continuity/density:
   `F(z)/F(0) = Π_{ρ∈R⁺}(1 − z²/ρ²) · Π_{k>N}(1 − z²/x_k²)`.
5. `P59_CURVATURE_SECOND_JET_REAL` — the complex second-jet identity and `κ_F ≥ 0`.
6. `P59_CURVATURE_ZERO_SUM` — `hasSum_zeta_two` plus the existing exact P59 second derivative
   (`proposition59RawTransform_secondDerivative_zero`).
7. `P59_CURVATURE_COMPACT_ENVELOPE` — for compact `K` and `κ_F ≤ C`:
   `sup_{z∈K} ‖F z / F 0‖ ≤ exp(C R_K²)`.

## Mandatory plants (judge)

A. `N=1, v_0=1, v_{±1}=0`: the included `±x_1` factors must come from `P_N`.
B. `N=1, v_{−1}=v_0=v_1=1`: included lattice values are nonzero and must not remain as sine zeros.
C. Non-even row: the paired quadratic product theorem must be unavailable.
D. `F(0)=0`: the normalization theorem must be unavailable.

## Forbidden (judge)

new axiom, `sorry`, `admit`, `exact?`; generic Hadamard factorization; an entire-function order
predicate; global denominator cancellation at removable nodes; defining κ as an ordered complex
number; claiming a cofinal bound from the finite theorem.

## Validation (judge)

```
q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
                   lake build Q3.Proofs.RouteB.Proposition59ExplicitProductCurvatureBridge
repo root:         scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
axioms:            [propext, Classical.choice, Quot.sound]
```
SUCCESS `P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE_KERNEL_GREEN`; FAILURE exactly one smallest code:
`P59_PRODUCT_BRIDGE_REMOVABLE_NODE_MISMATCH`, `P59_EVEN_ROOT_MULTISET_PAIRING_API_GAP`,
`P59_EULER_TAIL_LIMIT_API_GAP`, `P59_CURVATURE_SECOND_JET_NORMAL_FORM_GAP`.

## Report

`docs/routeB_bus/CODEX_REPORT_2026-09-03_GOAL058_P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE.md`:
per-step status, declaration names, plant results, axiom profile, commit hashes, branch name.
No `phase5_scripts`, no precommit, no queue edits; no route promotion; no RH claim.
