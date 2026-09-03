# Codex task — Goal 058 curvature: bordered secular slope (preflight + Lean bookkeeping + Probe 7)

Date: 2026-09-03 (evening)
Status: `AUTHORIZED` — part A by the judge's CODEX DIRECTIVE in `d7c7df36`; parts B and C by the owner (Codex is the executor with full machine access; Mythos via the Fable launcher is its channel for paper reasoning)
Parent: verdict `d7c7df36` (`REQ-2026-09-03-SCHURLOEWNER`, `TRY_SECULAR_IDENTITY_FOR_CURVATURE`); Mythos note `9f185963`
Worktree: Codex's own, rebased on `origin/rh_clean`; prefix `[Linux-Codex][rh_clean][Goal058]`; push the branch AND tell the owner the branch name so Linux-Claude can fast-forward `rh_clean` (or push to `rh_clean` directly after rebase if no conflict)

```yaml
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Object (judge §2, exact)

Even CCM block split at the central coordinate: `K = [[a0, bᵀ],[b, D]]`, ground row
`ξ = ξ0·(1, −(D−λ1)⁻¹b)` under (H) `λ1 ∉ spec(D)`. Curvature functional `w = (1/12, c)`,
`c_n = 1/(2π²n²)` (n = 1..N, even-basis coordinates with the √2 scaling of n=0 exactly as in
`docs/routeB_bus/phase5_scripts/edge_ledger_build.py::parity_blocks`). Rank-two bordered
deformation `K(t) = K + t(e0 wᵀ + w e0ᵀ)`; `Φ(t,z) = det(K(t)−zI)/det(D−zI) =
a0 + t/6 − z − ⟨b + t c, (D−zI)⁻¹(b + t c)⟩`. Exact identity `1/12 − S(z) = ½ ∂_tΦ(t,z)|₀`,
`S(z) = ⟨c,(D−z)⁻¹b⟩`; `Φ(0,λ1) = 0`. Target shape: `|∂_tΦ(0,λ1)| ≤ C/L²` on ONE precommitted
cofinal path (equivalently `sup_k κ_k < ∞`, `κ = (L²/2)(1/12 − S(λ1))`).

## Part A — source preflight (READ-ONLY, judge directive)

1. Read `CCMFiniteWeilSourceCommutator.lean` (`ccmWeilTau_structured_offdiag`,
   `ccmWeilMatFinite_structured_offdiag`, `ccmBetaFinite_unique`, `ccmWeilMatFinite_commutator`),
   `CCMFiniteWeilSourceMatrixN1.lean` (`ccmQKernel`, `ccmPrimeEntryN1`, `ccmWeilTauN1`, the W02
   pole split `W02 = 2 C_L C_Lᵀ − 2 S_L S_Lᵀ`, `C_L,n = 4√L sinh(L/4) L/(L²+16π²n²)`,
   `S_L,n = 16π√L sinh(L/4) n/(L²+16π²n²)`), `Proposition59EntireTransform.lean`, and the Mythos
   note `docs/routeB_bus/MYTHOS_R2_SECULAR_IDENTITY_NOTE_2026-09-03.md` (its §§2–5 already
   establish: secular root exact; polarization identity (3.2) exact; neither evaluates S for
   free; Loewner claim source-faithful at structure scope).
2. Write `∂_tΦ(t,λ1)|₀ = 2(1/12 − S(λ1))` as an exact source expression: split `b = b_pole + b_AP`
   (pole part along `C_L`, Arch−Prime part) and `D = D_pole − D_R − D_P`; expand `S(λ1)` with the
   displacement equation `X K − K X = β ηᵀ − η βᵀ` and the rank-two pole structure.
3. Decide BEFORE any norm: does the leading term cancel exactly (pole part of `b` against `c`,
   or Arch against Prime)? Name the first exact term that survives, with its source formula.
4. Two-by-two plant `K_t = [[λ + b²/t, b],[b, λ + t]]` (ground `λ`, `S(λ) = c·b/t` arbitrary):
   any lemma that would bound the slope for the plant is generic and must be rejected.
5. Return exactly one code: `P59_CURVATURE_BORDERED_SECULAR_SOURCE_IDENTITY` or
   `R2_SECULAR_DERIVATIVE_ONLY_RENAMES_CURVATURE`.

## Part B — Lean bookkeeping (judge §7 list; each item kernel-green before the next)

1. Exact rank-two factorization of `ccmW02Entry` (`W02 = 2 C_L C_Lᵀ − 2 S_L S_Lᵀ`) as a Lean
   theorem on the finite matrix.
2. Generic center Schur determinant identity for a real symmetric block matrix:
   `det(K − z) = det(D − z)·(a0 − z − ⟨b,(D−z)⁻¹b⟩)` for `z ∉ spec(D)` (Mathlib
   `Matrix.det_fromBlocks₂₂` or the Schur complement lemma).
3. The curvature-specific rank-two deformation `K(t)` and the derivative formula
   `∂_t[det(K(t)−z)/det(D−z)]|₀ = 1/6 − 2⟨c,(D−z)⁻¹b⟩`, hence `1/12 − S(z) = ½ ∂_tΦ|₀`.
4. Finite odd Hermite interpolation / parity-block formulas: `β_n = n·h(n²)` on the finite
   index set, even-sector symbol `Φ(x) = x h(x)`, odd-sector symbol `h(x)` (exact finite
   algebra after one interpolant is fixed; do NOT claim a canonical `h`).
Standard axiom profile only; no `sorry`; `q3_check` and strict refresh PASS before each commit.

## Part C — Probe 7 (numerics, owner's channel; precommit ADDENDUM 8 is frozen in
`docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md`)

Write `docs/routeB_bus/phase5_codex/slope_split.py` (new folder, register it in
`docs/cartographer/TOOLS.yaml`; do not edit anything under `phase5_scripts/`, import from
`edge_ledger_build.py` only). For `m = N ∈ {13, 23, 43, 83}` at 240 dps in arb (360 for 83):
build the even block; split `b = b_pole + b_AP` and compute `S_pole = ⟨c,(D−λ1)⁻¹b_pole⟩`,
`S_AP = ⟨c,(D−λ1)⁻¹b_AP⟩`, `S = S_pole + S_AP`; sanity `1/12 − S = a1/ξ0` from
`out/edge_ledger_dualcert.json` to ≥ 8 digits (STOP `SLOPE_SANITY_MISMATCH` otherwise);
report `S_pole/(1/12)`, `S_AP/(1/12)`, and `(1/12 − S_pole)·L²` per cell. Verdict line by the
frozen rule of ADDENDUM 8. Solve `(D−λ1)x = b_part` with `arb_mat.solve(algorithm="precond")`
(the plain LU loses digits on this near-singular matrix — see the builder's notes); this is a
finite-cell diagnostic, NOT a bound. Output `docs/routeB_bus/phase5_codex/out/slope_split.{json,md}`.

## Report

`docs/routeB_bus/CODEX_REPORT_2026-09-03_GOAL058_CURVATURE_BORDERED_SECULAR_PREFLIGHT.md`:
Part A expression, cancellation decision, first surviving term, plant check, code; Part B
declarations, files, axiom profile, commit hashes; Part C table and verdict line; what a
follow-up analytic attack would be, in one paragraph. If Mythos is used for Part A, cite the
Fable run and mark its claims as relay until source-checked.

## Boundaries

No use of `‖(D−λ1)⁻¹‖`, no uniform absolute gap, no assumption of the desired slope bound, no
operator-monotone claim for an interpolant the source does not fix. No edit under
`phase5_scripts/`, no edit of the precommit, no queue/verdict edits (bus transport stays with
Linux-Claude today). No route promotion, no RH claim.
