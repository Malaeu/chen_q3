# CLAUDE AGENT REPORT — GOAL058 / P59 sign-free Ritz inequality

    SUCCESS CODE: P59_SIGN_FREE_RITZ_KERNEL_GREEN
    DATE:         2026-09-05
    BRANCH:       rh_clean
    REPO HEAD:    0380d382a5fea9889decf22eb2e258b64c35601d (working tree, file left UNCOMMITTED)
    DIRECTIVE:    docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNFREE_RITZ_INSIDE_CCM_UNIFORM_ERROR_ATOM_2026-09-04.md
                  sections "CODEX DIRECTIVE" and S1 (request id REQ-2026-09-04-SIGNFREE)
    NEW FILE:     /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/P59SignFreeRitz.lean
                  464 lines, sha256 c9c592d0894d28f945d6ce2a391c441b8a4648c3bf4da6b2aba09d118f0d6b5c
    MODULE:       Q3.Proofs.RouteB.P59SignFreeRitz   (namespace Q3.RouteB.SignFreeRitz)
    NO commit, no push, no edit of any pre-existing file, no new axiom.

## 1. Shelf check first (mandatory)

`./ask.sh "Ritz"` and
`rg -n "rayleigh|Ritz|projectiveDefect" q3.lean.aristotle/Q3` returned:

| Existing declaration | File | Why it does not supply (SF) |
|---|---|---|
| `Q3.RouteB.hermitian_relative_ritz_projective_defect_le_rayleigh_excess_div_gap` | `q3.lean.aristotle/Q3/Proofs/RouteB/RelativeRitzFinite.lean` | complex Hermitian, **divided** form only; head carries `_hlambda1 : 0 < lambda1` and `hgap : lambda1 < lambda2`; the hypothesis is an orthogonal Rayleigh floor, not an ordered eigenbasis |
| `Q3.RouteB.ambient_residual_eq_leakage_of_compressed_eigen` and the envelope-transfer family | `AmbientResidualSplit.lean`, `AmbientResidualEnvelopeTransfer.lean` | Ritz *equation* bookkeeping (residual = leakage), no eigenvalue-gap inequality |
| `Q3.RayleighQuotient`, `Szego_Rayleigh_lower_bound`, `A3_bridge_rayleigh*` | `Q3/Axioms.lean`, `Q3/AxiomsTheorems.lean` | Toeplitz/symbol axioms of route A, unrelated statement shape |

`ask.sh` self-reported `ASK_STATUS: INCOMPLETE` (`q3_docs` semantic-index freshness validation failed),
so "not on the shelf" is here backed by the direct `rg` sweep of the Lean tree, not by the receipt alone.

Conclusion: the *undivided, sign-free* inequality does not exist in the tree. The new file cites the
existing divided Hermitian declaration in its module docstring and supplies only what is missing.

## 2. What is proved

Setting: `E` a real inner product space, `b : OrthonormalBasis (Fin (n+2)) ℝ E`, `K : E →ₗ[ℝ] E`
with `hK : ∀ j, K (b j) = lam j • b j`, `hmono : Monotone lam` (so `lam 0 ≤ lam 1 ≤ …`),
`q : E` with `‖q‖ = 1`. Weights `w j = ⟪b j, q⟫ ^ 2`, Rayleigh `R q = ⟪q, K q⟫`.
Symmetry of `K` is *not* a hypothesis — it follows from the eigen-equations on an orthonormal basis.
`Fin (n+2)` is used so that the two indices `0` and `1` exist without side conditions.

Head statements (no `0 < lam 0`, no `0 < lam 1`, no positivity of any eigenvalue anywhere):

```lean
theorem signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess
    (b : OrthonormalBasis (Fin (n + 2)) ℝ E) (K : E →ₗ[ℝ] E)
    (lam : Fin (n + 2) → ℝ) (hK : ∀ j, K (b j) = lam j • b j)
    (hmono : Monotone lam) (q : E) (hq : ‖q‖ = 1) :
    (lam 1 - lam 0) * (1 - ⟪b 0, q⟫ ^ 2) ≤ ⟪q, K q⟫ - lam 0

theorem signFreeRitz_rayleighExcess_eq_weighted_sum … :
    ⟪q, K q⟫ - lam 0 = ∑ j, (lam j - lam 0) * ⟪b j, q⟫ ^ 2      -- middle equality of (SF)

theorem signFreeRitz_projectiveDefect_le_rayleighExcess_div_gap … (hgap : 0 < lam 1 - lam 0) :
    1 - ⟪b 0, q⟫ ^ 2 ≤ (⟪q, K q⟫ - lam 0) / (lam 1 - lam 0)     -- ONLY statement with a gap sign
```

Supporting layer (all sign-free):

* `gap_mul_defect_le_weighted_excess_sum` — the pure weighted-sum core over any `Fintype`:
  weights `≥ 0` summing to `1`, every non-bottom eigenvalue `≥ l2`. This is the whole content of S1;
  the inner-product layer only feeds it Parseval and the spectral expansion.
* `sum_sq_inner_eq_norm_sq` — Parseval, `∑ j, ⟪b j, q⟫ ^ 2 = ‖q‖ ^ 2`.
* `rayleigh_eq_weighted_eigenvalue_sum` — `⟪q, K q⟫ = ∑ j, lam j * ⟪b j, q⟫ ^ 2`.

Projective distance (S3 half of the directive), stated for unit vectors with sign alignment
`0 ≤ ⟪x, q⟫`, and specialised to the bottom eigenvector `xi = b 0`:

```lean
theorem signFreeRitz_dist_sq_eq_two_mul_one_sub_sqrt … :
    ‖x - q‖ ^ 2 = 2 * (1 - Real.sqrt (1 - (1 - ⟪x, q⟫ ^ 2)))
theorem signFreeRitz_dist_sq_le_two_mul_projectiveDefect … :
    ‖x - q‖ ^ 2 ≤ 2 * (1 - ⟪x, q⟫ ^ 2)
theorem signFreeRitz_eigenvector_dist_sq_le_two_mul_projectiveDefect (b) (q) (hq) (halign) :
    ‖b 0 - q‖ ^ 2 ≤ 2 * (1 - ⟪b 0, q⟫ ^ 2)
```

i.e. `d² = 2(1 − √(1−p)) ≤ 2p` with `p = 1 − ⟪xi, q⟫²`.

### Required controls, all in the same file

* **(i) negative-bottom equality plant.** `plantNegBottomLam = ![-2, -1]`,
  `plantNegBottomTrial t = √(1−t²) • e₀ + t • e₁` on `EuclideanSpace ℝ (Fin 2)`,
  operator `diagOp plantNegBottomLam` (diagonal via `Basis.constr`, eigen-equation proved).
  `plantNegBottom_equality_control` proves, for `0 ≤ t ≤ 1`: `lam 0 = -2`, `lam 1 = -1`,
  `‖q‖ = 1`, `p = t²`, `R − lam 0 = t²`, and **equality** `Δ · p = R − lam 0`.
  `plantNegBottom_signFree_instance` instantiates the general theorem on this strictly
  negative spectrum, so (SF) is demonstrably non-vacuous without any eigenvalue sign.
* **(ii) zero gap.** `signFreeRitz_zero_gap_control`: under `lam 1 = lam 0` the inequality
  still holds and degenerates to `0 ≤ R − lam 0`. Nothing is divided; the division corollary
  is a separate declaration and is the only one that consumes `0 < lam 1 - lam 0`.
* **(iii) three-level counterexample.** `plantThreeLevelLam m = ![0, 1, m²]`,
  `plantThreeLevelTrial m = √(1 − m⁻²) • e₀ + m⁻¹ • e₂`.
  `plantThreeLevel_defect_small_ratio_one` proves for every real `m ≥ 1`:
  `‖q‖ = 1`, `p = 1/m²`, `η = (R − lam 0)/(lam 1 − lam 0) = 1`, and (SF) still holds.
  `plantThreeLevel_defect_arbitrarily_small_ratio_one` upgrades this to: for every `ε > 0`
  there is `m ≥ 1` with `p < ε` and `η = 1`. So `p → 0` does **not** imply `η → 0`;
  the directive's `iff-ish` reading is refuted inside the kernel.

Nothing in the file mentions a window, a schedule, `L = log m`, a source rate, or any
asymptotic estimate. No `Filter` hypothesis, no compact-error claim.

## 3. Validation transcript

    WORKDIR: /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle

    $ lake env lean Q3/Proofs/RouteB/P59SignFreeRitz.lean
    (no output — no errors, no warnings, no linter complaints)
    lean_exit=0

    $ lake build Q3.Proofs.RouteB.P59SignFreeRitz
    ✔ [7743/7743] Built Q3.Proofs.RouteB.P59SignFreeRitz (18s)
    Build completed successfully (7743 jobs).
    lake_exit=0

    WORKDIR: /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean

    $ scripts/q3_check.sh Q3/Proofs/RouteB/P59SignFreeRitz.lean
    lean Q3/Proofs/RouteB/P59SignFreeRitz.lean
    scan Q3/Proofs/RouteB/P59SignFreeRitz.lean
    q3_check ok
    q3check_exit=0

Exit codes read with `${PIPESTATUS[0]}` in every case (text success is not kernel success).

## 4. Axiom profile — every exported declaration

Scratch file (outside the repository):
`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/axioms_P59SignFreeRitz.lean`
importing `Q3.Proofs.RouteB.P59SignFreeRitz` and running `#print axioms` for all 27 declarations.

Every single one printed exactly

    [propext, Classical.choice, Quot.sound]

Covered: `gap_mul_defect_le_weighted_excess_sum`, `sum_sq_inner_eq_norm_sq`,
`rayleigh_eq_weighted_eigenvalue_sum`, `signFreeRitz_rayleighExcess_eq_weighted_sum`,
`signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess`,
`signFreeRitz_projectiveDefect_le_rayleighExcess_div_gap`, `signFreeRitz_zero_gap_control`,
`signFreeRitz_dist_sq_eq_two_mul_one_sub_sqrt`, `signFreeRitz_dist_sq_le_two_mul_projectiveDefect`,
`signFreeRitz_eigenvector_dist_sq_le_two_mul_projectiveDefect`, `diagOp_apply_basisFun`,
`inner_basisFun_basisFun`, `plantNegBottomLam_monotone`, `plantNegBottom_eigen`,
`plantNegBottom_inner_zero`, `plantNegBottom_inner_one`, `plantNegBottom_norm`,
`plantNegBottom_equality_control`, `plantNegBottom_signFree_instance`,
`plantThreeLevelLam_monotone`, `plantThreeLevel_eigen`, `plantThreeLevel_inner_zero`,
`plantThreeLevel_inner_one`, `plantThreeLevel_inner_two`, `plantThreeLevel_norm`,
`plantThreeLevel_defect_small_ratio_one`, `plantThreeLevel_defect_arbitrarily_small_ratio_one`.

No `sorryAx`, no project axiom, no new axiom declaration (`q3_check` also scans the diff for one).

## 5. Second channel — numpy, independent of the Lean proof

Script: `…/scratchpad/sf_numpy_check.py` (float64, `numpy.linalg.eigh`, seed 20260905).
Different implementation, random data, no shared code path with the kernel proof.

    random symmetric trials      : 14000  (fully negative spectrum: 5743)
    max (lhs - mid)  [must be<=0]: 2.665e-15
    max |mid - (R - l1)|         : 6.128e-14
    max |d^2 - 2(1-sqrt(1-p))|   : 1.718e-12
    control (i)  diag(-2,-1): max |gap*p - (R-l1)| and |R-l1 - t^2| = 3.782e-16
    control (ii) zero gap diag(-3,-3,1): violations = 0
    control (iii) three levels:
       m=     1.0  p=1.000e+00  eta=1.000000  (SF) holds: True
       m=     2.0  p=2.500e-01  eta=1.000000  (SF) holds: True
       m=    10.0  p=1.000e-02  eta=1.000000  (SF) holds: True
       m=   100.0  p=1.000e-04  eta=1.000000  (SF) holds: True
       m=  1000.0  p=1.000e-06  eta=1.000000  (SF) holds: True

Grid: `n ∈ {2,3,4,5,8,13,30}` × spectral shifts `{0, −50, −5, +7}` and scales `{1, 0.1, 2, 1e-3}`,
400 random unit trial vectors each. 5743 of the 14000 matrices had a **fully negative** spectrum,
which is the point of the sign-free claim. The single positive residual `2.7e-15` is float noise on
an inequality that is exact in the kernel; the distance identity holds to `1.7e-12`.
This is a DIAGNOSTIC, never a proof — the proof is the kernel run in §3.

## 6. Scope — what this does NOT close

Per the directive: success closes the finite sign-free algebra only. It does **not** supply
`(P-)`, the anchor supplier, G3, the compact-error atom, or RH. Nothing here is a source estimate,
and nothing here changes the route state, the supplier count, `BUS_010`, `ROUTE`, or `PX_RH_CLAIM`.
The consumer `Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi` is untouched.

CLOSES: the S1 finite inequality as a kernel object, with its three mandatory controls.
OPENS:  nothing. No new "input" is requested and no new tool is introduced; the file consumes
        only Mathlib and stands alone (no Q3 import), so it adds no edge to the assembly graph
        beyond its own declaration.

Registration note for the observer: the file is new and **uncommitted**; a `TOOLS.yaml` /
capability-catalog entry and the commit are the owner's gate, not this agent's.
