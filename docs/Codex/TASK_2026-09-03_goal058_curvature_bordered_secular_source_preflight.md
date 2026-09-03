# Codex task — Goal 058 curvature: bordered secular slope, source preflight (READ-ONLY)

Date: 2026-09-03
Status: `AUTHORIZED_BY_JUDGE_CODEX_DIRECTIVE`
Parent: verdict `d7c7df36` (`REQ-2026-09-03-SCHURLOEWNER`, `TRY_SECULAR_IDENTITY_FOR_CURVATURE`)
Author: Linux-Claude (observer), transcribing the judge's CODEX DIRECTIVE
Mode: PAPER_AND_SOURCE_READ_ONLY — no Lean edit, no numerics, no commit of Lean

```yaml
TASK_ID: GOAL058_CURVATURE_BORDERED_SECULAR_SOURCE_PREFLIGHT
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Object (judge §2, exact)

Even CCM block split at the central coordinate: `K = [[a0, bᵀ],[b, D]]`, ground row
`ξ = ξ0·(1, −(D−λ1)⁻¹b)`. Curvature functional `w = (1/12, c)`, `c_n = 1/(2π²n²)`.
Rank-two bordered deformation `K(t) = K + t(e0 wᵀ + w e0ᵀ)`.
`Φ(t,z) = det(K(t) − zI)/det(D − zI) = a0 + t/6 − z − ⟨b + t c, (D − zI)⁻¹(b + t c)⟩`.
Exact identity: `1/12 − S_curv(z) = ½ ∂_t Φ(t,z)|_{t=0}`, `S_curv(z) = ⟨c,(D−z)⁻¹b⟩`;
at the ground `Φ(0, λ1) = 0`. The target theorem shape is
`|∂_t Φ(t, λ1)|_{t=0}| ≤ C / L²` on one precommitted cofinal path (equivalently
`sup_k κ_k < ∞`, since `κ = (L²/2)(1/12 − S_curv(λ1))`).

## Exact outcome

1. Read `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean`
   (`ccmWeilTau_structured_offdiag`, `ccmWeilMatFinite_structured_offdiag`,
   `ccmBetaFinite_unique`, `ccmWeilMatFinite_commutator`: `τ_nm = (β_n − β_m)/(n − m)`,
   `X K − K X = β ηᵀ − η βᵀ`, displacement rank ≤ 2),
   `CCMFiniteWeilSourceMatrixN1.lean` (`ccmQKernel`, the W02 pole split
   `W02 = 2 C_L C_Lᵀ − 2 S_L S_Lᵀ` with `C_L,n = 4√L sinh(L/4) L/(L²+16π²n²)`,
   `S_L,n = 16π√L sinh(L/4) n/(L²+16π²n²)`), `Proposition59EntireTransform.lean`
   (second jet, functional norm), and the even-block builder
   `docs/routeB_bus/phase5_scripts/edge_ledger_build.py` (`parity_blocks`, √2 scaling of the
   n=0 coordinate) for the exact coordinates of `b`, `D`, `c`.
2. Write the bordered determinant slope `∂_t Φ(t, λ1)|_{t=0}` as an exact source expression in
   the CCM entries: split `D` into `W02|_D − W_R|_D − Prime|_D` and `b` into its pole part
   (`C_L` component) and its Arch–Prime part; expand
   `⟨c,(D−λ1)⁻¹b⟩` using the displacement equation and the rank-two pole structure.
3. Decide, before any norm is taken: does the leading term of the slope cancel exactly
   (pole part of `b` against `c`, or Arch against Prime)? Name the first exact term that
   remains after that cancellation, with its source formula.
4. Run the judge's two-by-two plant `K_t = [[λ + b²/t, b],[b, λ + t]]` (ground `λ`, `S(λ) = c·b/t`
   arbitrary for `t > 0`) against every step: any lemma that would bound the slope for the
   plant is generic and must be rejected.
5. Return exactly one code:
   `P59_CURVATURE_BORDERED_SECULAR_SOURCE_IDENTITY` (an exact source identity for the slope with
   the leading term cancelled and the remainder named) or
   `R2_SECULAR_DERIVATIVE_ONLY_RENAMES_CURVATURE` (the rewrite leaves only the original mixed
   pairing, or reintroduces `‖(D−λ1)⁻¹‖`).

## Report

`docs/routeB_bus/CODEX_REPORT_2026-09-03_GOAL058_CURVATURE_BORDERED_SECULAR_PREFLIGHT.md`:
the exact expression, the cancellation decision with formulas, the first remaining term,
the plant check, the code, and what a follow-up Lean bookkeeping item would be (statement
only). Commit the report only (own worktree, rebase on `origin/rh_clean`, prefix
`[Linux-Codex][rh_clean][Goal058]`).

## Boundaries (judge)

No Lean edit. No numerical run. No `phase5_scripts`, no precommit, no queue. No use of
`‖(D−λ1)⁻¹‖`, no uniform absolute gap, no assumption of the desired curvature bound, no
operator-monotone claim for an interpolant the source does not fix. No route promotion,
no RH claim.
