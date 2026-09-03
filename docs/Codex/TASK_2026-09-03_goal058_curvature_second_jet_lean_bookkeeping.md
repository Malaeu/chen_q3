# Codex task — Goal 058 curvature route: Lean bookkeeping of the second jet and the abstract bridge

Date: 2026-09-03
Status: `AUTHORIZED_BY_JUDGE_SECTION_8`
Parent: Goal 058 / `REQ-2026-09-03-CURVRITZ` verdict `0c0a2b37` (`RUN_RELATIVE_RITZ_DECISIVE_TEST`)
Author: Linux-Claude (observer), transcribing the judge's section 8 "Lean-ready bookkeeping" into one transaction
Worktree: Codex's own (`~/.codex/worktrees/...`), rebased on `origin/rh_clean` at start; commit prefix `[Linux-Codex][rh_clean][Goal058]`

## Exact edge (theorem → consumer)

Terminal consumer: `Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi`
(`Goal058DirectGroundZeroEscape.lean:27`), hypotheses `hzeros`, `hentire`, `hconv`.
Supplier chain selected by the judge: real-zero tracked ground family
(`selectedFerrersTrackedGroundTransformAt`) + bounded normalized curvature
`κ_k = −F_k''(0)/(2F_k(0))` ⇒ local boundedness ⇒ Vitali with moving lattice ⇒ `hconv`.
This task formalizes only the source-locked FINITE and ABSTRACT pieces below. It does
not claim the cofinal bound `sup_k κ_k < ∞` and does not touch the phase key.

## Exact outcome (five items, in this order; each one kernel-checked before the next)

1. `proposition59RawTransform_secondDerivative_zero` in
   `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean` (or a sibling
   file importing it): for `0 < L`, `S = Finset.Icc (-N) N`, `v : ℤ → ℂ`,
   the second derivative at `0` of `proposition59RawTransform L S v` equals
   `-(L^2 * Real.sqrt L) * (v 0 / 12 + (1 / (2 * π^2)) * Σ_{n ∈ S, n ≠ 0} v n / n^2)`.
   Paper source: judge verdict §4 and the observer sympy check
   (`K_n''(0) = −2L/x_n²`, `K_0''(0) = −L³/12`, precommit ADDENDUM of 2026-09-03).
   Use the existing removable-pole lemmas (`proposition59PoleKernel_at_lattice`,
   `proposition59RawTransform_at_zero_eq_sqrt`) and Mathlib's `iteratedDeriv`/
   `deriv` on the entire kernel; do not introduce a new kernel definition.
2. `proposition59SecondJetFunctional_norm_sq_le_one_div_eighty`: the ℓ²-norm squared of
   the coefficient functional `n ↦ if n = 0 then 1/12 else 1/(2π²n²)` restricted to any
   `Finset.Icc (-N) N` is `≤ 1/80` (exact value `1/144 + 2·Σ_{n≥1} 1/(4π⁴n⁴)` with
   `Σ 1/n⁴ = π⁴/90`; use Mathlib's `hasSum_zeta_four` or bound the finite sum by it).
   Corollary: `‖T''_{L,N,ξ}(0) − T''_{L,N,q}(0)‖ ≤ (L^2 √L / √80) · ‖ξ − q‖₂`.
3. Finite relative Ritz theorem (judge §3), as a standalone Hermitian-matrix lemma in a
   new file `RelativeRitzFinite.lean` under `Q3/Proofs/RouteB/`: for `K` Hermitian,
   `K ξ = λ₁ ξ`, `‖ξ‖ = 1`, `0 < λ₁ < λ₂`, `∀ u ⟂ ξ, ⟨u, K u⟩ ≥ λ₂ ‖u‖²`, `‖q‖ = 1`:
   `1 − |⟨ξ, q⟩|² ≤ (⟨q, K q⟩ − λ₁) / (λ₂ − λ₁)`. This is a NEW interface, not a rewrite
   of `complexTrialComplementFloor`; do not modify the existing floor predicate.
4. Arithmetic wrapper: on the production schedule `m = N = k + 2`,
   `(Real.log (k+2))^2 / (k+2) → 0` (Filter.Tendsto atTop), and the forced-zero
   curvature contribution `(L²/(4π²)) Σ_{j > N} 1/j² ≤ L²/(4π² N)`.
5. Abstract bridge (may be P59-specific if the general Hadamard product is too costly):
   for `G` entire, even, real on `ℝ`, all zeros real, order ≤ 1, `G 0 = 1`, with
   `κ := −G''(0)/2`: `‖G z‖ ≤ Real.exp (κ * ‖z‖²)`. If Mathlib lacks the needed
   Hadamard factorization for order ≤ 1 at the pinned revision (`v4.26.0`), record the
   exact missing Mathlib declaration and stop item 5 with `MATHLIB_GAP_NAMED`; items 1–4
   still ship.

## Boundaries (from the judge's CODEX DIRECTIVE)

- No edit under `docs/routeB_bus/phase5_scripts/`, no edit of the numerical precommit,
  no edit of `docs/routeB_bus/PROSHKA_QUEUE.md` (bus transport is Linux-Claude today).
- No promotion of any finite diagnostic to a cofinal theorem; no `sorry`; no new axioms;
  standard axiom profile only; `q3_check` and the strict refresh must PASS before commit.
- No route promotion, no phase-key change, `PX_RH_CLAIM: NOT_MADE`.
- Report: one `docs/routeB_bus/CODEX_REPORT_2026-09-03_GOAL058_CURVATURE_SECOND_JET_LEAN.md`
  with per-item status (`KERNEL_GREEN` / `MATHLIB_GAP_NAMED` / `NOT_REACHED`), declaration
  names, file paths, axiom profile, and the commit hash.

## What this task does NOT do

It does not attack `P59_CURVATURE_DUAL_ANNIHILATOR_OR_SCALAR_SCHUR_IDENTITY` (new analytic
work, judge §8) and does not compute anything numerically (Linux-Claude's probes 1–5).
