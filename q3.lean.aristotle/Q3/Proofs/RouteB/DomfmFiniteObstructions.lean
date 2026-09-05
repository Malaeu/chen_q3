import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Q3.Proofs.RouteB.WeilGramMinusShift

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# DOM/FM finite obstructions: trade-off, absolute-Schur kill, compression gap

Source boundary (read this before citing anything from this file).

This file formalises **only** the finite items of the judge's verdict
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DOM_FM_ZERO_MARGIN_AND_TRADEOFF_LEMMA_2026-09-05.md`,
namely the finite-dimensional complex linear algebra of D1.1, D1.2, D2.4
(finite version) and D3.2.  Everything here is finite: complex inner product
spaces, finite matrices, finite sums.  No integral, no measure, no zeta, no
claim about the sign of the Weil form.

What is proved here:

* `domfm_projected_rayleigh_le` (D1.1, TRADE) — for a Hermitian `K` realised as
  a continuous linear map `Kop` on `EuclideanSpace ℂ (Fin n)` with
  `M = ‖Kop‖` (the operator norm, **not** an entrywise matrix norm), a nonzero
  `y`, a nonzero `p ∈ V` with `y - p ⟂ V`, and `d = ‖y-p‖/‖y‖`:
  `R_K(p) ≤ R_K(y) + 2 M d`.
* `domfm_restricted_min_le_projected_rayleigh` (D1.1, variational corollary) —
  the infimum of `R_K` over unit vectors of `V` is at most `R_K(p)`, together
  with `domfm_projected_rayleigh_attained_on_unit`, the statement that `R_K(p)`
  is literally attained at a unit vector of `V`.
* `domfm_eigenvector_projection_quadratic_error` (D1.2, EIG-TRADE) — with
  `Kop y = λ y` the error is exactly `Re⟪y-p, (K-λ)(y-p)⟫ / ‖p‖²` and is
  bounded by `(M+|λ|) d² / (1-d²)`, i.e. quadratic in `d`, not linear.
* `domfm_no_positive_absolute_schur_weight` (D2.4, finite version) — for a
  finite symmetric real signed edge matrix `J` with strictly negative total
  signed-degree defect `∑ᵢ (dᵢ - aᵢ) < 0`, **no** positive weight `q` satisfies
  the absolute-Schur test `dᵢ ≥ ∑ⱼ |Jᵢⱼ| qⱼ/qᵢ`.
* `domfm_absolute_schur_sufficient` (D2.4, sufficiency direction) — if such a
  `q` does exist, the signed form is nonnegative.  This is what makes the
  previous theorem a genuine *kill of a proof method*.
* `domfm_signed_three_vertex_psd_plant` (D2.4, SIGNED-PSD) — the mandatory
  plant on three vertices: `2|s₁-s₂|² + 2|s₂-s₃|² - |s₁-s₃|² = |s₁-2s₂+s₃|²`,
  hence the signed form of `J = !![0,2,-1; 2,0,2; -1,2,0]` is nonnegative,
  **while** its signed-degree defect is `-4 < 0` and no positive
  absolute-Schur weight exists.  Reading the absolute-Schur obstruction as
  negativity of the form is therefore a demonstrable logic error.
* `domfm_compressed_gram_minus_shift` (D3.2, COMP-GAP) — the exact matrix
  identity `Zᴴ K Z + e ZᴴZ = Zᴴ Γ Z - (c_L - e) ZᴴZ - 2 (Zᴴβ)(Zᴴβ)*` for
  `K = Γ - c_L I - 2ββ*` (which is `Q3.RouteB.weilShiftMatrix`), with the
  positive-semidefiniteness equivalence `domfm_compressed_gram_minus_shift_posSemidef_iff`
  and the isometric special case `domfm_compressed_gram_minus_shift_isometry`
  as corollaries.  The shift on the compressed side is carried by `ZᴴZ`, not by
  the identity matrix: redundant `Z` is allowed and no Gram matrix is inverted.
* `domfm_proper_compression_negative_complement_plant` (D3.2, plant) — with
  `K = diag(-1,1)` and `Z = (0,1)ᵀ` the compressed form is positive
  semidefinite while the full matrix is not, so a dictionary whose range is not
  proved full is not a harmless change of basis.

What is **not** proved here, and must not be read into any statement below:

* No analytic statement of any kind.  D1.3, D2.1–D2.3, D3.1, D3.3 and D4 of the
  verdict are out of scope for this file.
* Nothing about the sign of the Weil form, of `K_m`, of `Γ_m`, or of `T_ε`.
  In particular `domfm_no_positive_absolute_schur_weight` excludes a *certificate
  class*; the plant of §4 exists precisely to block the inference to negativity.
* No source crosswalk to the literal CCM entries and no route promotion.
* Nothing conditional on RH.
-/

noncomputable section

namespace Q3.RouteB.Domfm

open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Matrix

/-! ## 0. Two elementary complex facts, spelled once -/

/-- `Re z ≤ ‖z‖` for a complex number. -/
theorem re_le_norm_complex (z : ℂ) : z.re ≤ ‖z‖ := RCLike.re_le_norm (K := ℂ) z

/-- `|Re z| ≤ ‖z‖` for a complex number. -/
theorem abs_re_le_norm_complex (z : ℂ) : |z.re| ≤ ‖z‖ := RCLike.abs_re_le_norm (K := ℂ) z

/-! ## 1. Rayleigh quotients on a complex inner product space -/

section Rayleigh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `⟪x, x⟫ = ‖x‖²` with the real square explicitly coerced. -/
theorem inner_self_ofReal (x : E) : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  exact rfl

/-- The Rayleigh quotient `R_T(x) = Re⟪x, T x⟫ / ‖x‖²`.

For `x = 0` this is `0` by the junk-value convention of division; every
statement below that uses it carries a nonvanishing hypothesis. -/
def rayleigh (T : E →L[ℂ] E) (x : E) : ℝ :=
  (⟪x, T x⟫_ℂ).re / ‖x‖ ^ 2

theorem rayleigh_of_norm_one (T : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    rayleigh T x = (⟪x, T x⟫_ℂ).re := by
  simp [rayleigh, hx]

/-- The Rayleigh quotient is invariant under nonzero real rescaling. -/
theorem rayleigh_real_smul (T : E →L[ℂ] E) (x : E) {r : ℝ} (hr : r ≠ 0) :
    rayleigh T ((r : ℂ) • x) = rayleigh T x := by
  have e1 : ⟪(r : ℂ) • x, T ((r : ℂ) • x)⟫_ℂ = ((r ^ 2 : ℝ) : ℂ) * ⟪x, T x⟫_ℂ := by
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  have h1 : (⟪(r : ℂ) • x, T ((r : ℂ) • x)⟫_ℂ).re = r ^ 2 * (⟪x, T x⟫_ℂ).re := by
    rw [e1, Complex.re_ofReal_mul]
  have h2 : ‖(r : ℂ) • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, mul_pow]
    simp [sq_abs]
  rw [rayleigh, rayleigh, h1, h2, mul_div_mul_left _ _ (pow_ne_zero 2 hr)]

/-- Symmetric-operator polarisation: `Re⟪v-u, T(v+u)⟫ = R-numerators difference`.

This is the exact identity `R_K(p) - R_K(y) = Re⟪v-u, K(v+u)⟫` of D1.1 before
any normalisation is used. -/
theorem re_inner_sub_map_add (T : E →L[ℂ] E)
    (hT : (T : E →ₗ[ℂ] E).IsSymmetric) (u v : E) :
    (⟪v - u, T (v + u)⟫_ℂ).re = (⟪v, T v⟫_ℂ).re - (⟪u, T u⟫_ℂ).re := by
  have hexp : ⟪v - u, T (v + u)⟫_ℂ
      = ⟪v, T v⟫_ℂ + ⟪v, T u⟫_ℂ - ⟪u, T v⟫_ℂ - ⟪u, T u⟫_ℂ := by
    rw [map_add, inner_sub_left, inner_add_right, inner_add_right]
    ring
  have hsym : ⟪v, T u⟫_ℂ = conj (⟪u, T v⟫_ℂ) := by
    rw [inner_conj_symm]
    exact (hT v u).symm
  rw [hexp, hsym]
  simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
  ring

/-- The operator-norm bound on the Rayleigh numerator of a unit vector. -/
theorem neg_opNorm_le_rayleigh (T : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    -‖T‖ ≤ rayleigh T x := by
  rw [rayleigh_of_norm_one T hx]
  have h1 : |(⟪x, T x⟫_ℂ).re| ≤ ‖⟪x, T x⟫_ℂ‖ := abs_re_le_norm_complex _
  have h2 : ‖⟪x, T x⟫_ℂ‖ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm (𝕜 := ℂ) x (T x)
  have h3 : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  rw [hx] at h2 h3
  have := (abs_le.mp h1).1
  simp only [one_mul] at h2 h3
  linarith

/-! ### D1.1 — the abstract trade-off inequality -/

/-- **D1.1 (TRADE), abstract form.**

`T` is a symmetric continuous operator on a complex inner product space, `V` a
subspace, `y ≠ 0`, and `p ≠ 0` is the orthogonal projection of `y` onto `V`,
given by the witnesses `p ∈ V` and `∀ v ∈ V, ⟪v, y - p⟫ = 0`.  Then, with
`d = ‖y-p‖/‖y‖` and `M = ‖T‖`,

`R_T(p) ≤ R_T(y) + 2 M d`.

The proof normalises **both** compared vectors before estimating; no
denominator is dropped. -/
theorem rayleigh_le_of_projection_witness (T : E →L[ℂ] E)
    (hT : (T : E →ₗ[ℂ] E).IsSymmetric) {V : Submodule ℂ E} {y p : E}
    (hy : y ≠ 0) (hp : p ≠ 0) (hpV : p ∈ V)
    (horth : ∀ v ∈ V, ⟪v, y - p⟫_ℂ = 0) :
    rayleigh T p ≤ rayleigh T y + 2 * ‖T‖ * (‖y - p‖ / ‖y‖) := by
  have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hp0 : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hpo : ⟪p, y - p⟫_ℂ = 0 := horth p hpV
  -- `⟪p, y⟫ = ‖p‖²`
  have hpy : ⟪p, y⟫_ℂ = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_right, sub_eq_zero] at hpo
    rw [hpo]
    exact inner_self_ofReal p
  -- Pythagoras
  have hpyth : ‖y‖ ^ 2 = ‖p‖ ^ 2 + ‖y - p‖ ^ 2 := by
    have hsplit : p + (y - p) = y := by abel
    have h := norm_add_sq (𝕜 := ℂ) p (y - p)
    rw [hsplit, horth p hpV] at h
    simpa using h
  set u : E := ((‖y‖⁻¹ : ℝ) : ℂ) • y with hu
  set v : E := ((‖p‖⁻¹ : ℝ) : ℂ) • p with hv
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hy0), inv_mul_cancel₀ hy0.ne']
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp0), inv_mul_cancel₀ hp0.ne']
  -- `⟪v, u⟫ = ‖p‖/‖y‖`, a nonnegative real
  have hgamma : ⟪v, u⟫_ℂ = ((‖p‖ / ‖y‖ : ℝ) : ℂ) := by
    rw [hv, hu, inner_smul_left, inner_smul_right, hpy]
    simp only [Complex.conj_ofReal]
    push_cast
    field_simp
  have hgre : (⟪v, u⟫_ℂ).re = ‖p‖ / ‖y‖ := by rw [hgamma]; simp
  have hsub : ‖v - u‖ ^ 2 = 2 - 2 * (‖p‖ / ‖y‖) := by
    have h := norm_sub_sq (𝕜 := ℂ) v u
    simp only [RCLike.re_to_complex] at h
    rw [h, hvn, hun, hgre]; ring
  have hadd : ‖v + u‖ ^ 2 = 2 + 2 * (‖p‖ / ‖y‖) := by
    have h := norm_add_sq (𝕜 := ℂ) v u
    simp only [RCLike.re_to_complex] at h
    rw [h, hvn, hun, hgre]; ring
  have hprod : ‖v - u‖ * ‖v + u‖ = 2 * (‖y - p‖ / ‖y‖) := by
    have hsq : (‖v - u‖ * ‖v + u‖) ^ 2 = (2 * (‖y - p‖ / ‖y‖)) ^ 2 := by
      rw [mul_pow, hsub, hadd, mul_pow, div_pow]
      field_simp
      nlinarith [hpyth]
    have h1 : (0 : ℝ) ≤ ‖v - u‖ * ‖v + u‖ := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (‖y - p‖ / ‖y‖) := by positivity
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this
  have hRu : rayleigh T u = rayleigh T y := rayleigh_real_smul T y (inv_ne_zero hy0.ne')
  have hRv : rayleigh T v = rayleigh T p := rayleigh_real_smul T p (inv_ne_zero hp0.ne')
  have hid := re_inner_sub_map_add T hT u v
  have hbound : (⟪v - u, T (v + u)⟫_ℂ).re ≤ 2 * ‖T‖ * (‖y - p‖ / ‖y‖) := by
    calc (⟪v - u, T (v + u)⟫_ℂ).re
        ≤ ‖⟪v - u, T (v + u)⟫_ℂ‖ := re_le_norm_complex _
      _ ≤ ‖v - u‖ * ‖T (v + u)‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖v - u‖ * (‖T‖ * ‖v + u‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = ‖T‖ * (‖v - u‖ * ‖v + u‖) := by ring
      _ = 2 * ‖T‖ * (‖y - p‖ / ‖y‖) := by rw [hprod]; ring
  have hRu' : rayleigh T u = (⟪u, T u⟫_ℂ).re := rayleigh_of_norm_one T hun
  have hRv' : rayleigh T v = (⟪v, T v⟫_ℂ).re := rayleigh_of_norm_one T hvn
  rw [← hRv, ← hRu, hRu', hRv']
  linarith [hid, hbound]

/-- The projection defect is `< 1` as soon as the projection is nonzero.

This is the guard of D1.1: for `p = 0` the projected Rayleigh quotient is
undefined and `d = 1`. -/
theorem projection_defect_lt_one {V : Submodule ℂ E} {y p : E}
    (hy : y ≠ 0) (hp : p ≠ 0) (hpV : p ∈ V)
    (horth : ∀ v ∈ V, ⟪v, y - p⟫_ℂ = 0) :
    ‖y - p‖ / ‖y‖ < 1 := by
  have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hp0 : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hpyth : ‖y‖ ^ 2 = ‖p‖ ^ 2 + ‖y - p‖ ^ 2 := by
    have hsplit : p + (y - p) = y := by abel
    have h := norm_add_sq (𝕜 := ℂ) p (y - p)
    rw [hsplit, horth p hpV] at h
    simpa using h
  rw [div_lt_one hy0]
  nlinarith [norm_nonneg (y - p)]

/-- The Pythagoras identity behind D1.1/D1.2: `‖p‖² = (1-d²)‖y‖²`. -/
theorem norm_proj_sq_eq {V : Submodule ℂ E} {y p : E} (hpV : p ∈ V)
    (horth : ∀ v ∈ V, ⟪v, y - p⟫_ℂ = 0) :
    ‖y‖ ^ 2 = ‖p‖ ^ 2 + ‖y - p‖ ^ 2 := by
  have hsplit : p + (y - p) = y := by abel
  have h := norm_add_sq (𝕜 := ℂ) p (y - p)
  rw [hsplit, horth p hpV] at h
  simpa using h

/-! ### D1.1 — the variational corollary -/

/-- `R_T(p)` is attained at a unit vector of `V`: the normalised projection. -/
theorem domfm_projected_rayleigh_attained_on_unit (T : E →L[ℂ] E)
    {V : Submodule ℂ E} {p : E} (hp : p ≠ 0) (hpV : p ∈ V) :
    ∃ w ∈ V, ‖w‖ = 1 ∧ rayleigh T w = rayleigh T p := by
  have hp0 : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  refine ⟨((‖p‖⁻¹ : ℝ) : ℂ) • p, V.smul_mem _ hpV, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp0), inv_mul_cancel₀ hp0.ne']
  · exact rayleigh_real_smul T p (inv_ne_zero hp0.ne')

/-- **D1.1, variational corollary.**  The infimum of the Rayleigh quotient over
the unit vectors of `V` is at most the projected Rayleigh quotient `R_T(p)`.

Together with `rayleigh_le_of_projection_witness` this is the left half of
(TRADE):  `λ_min(K|_V) ≤ R_K(p) ≤ R_K(y) + 2Md`. -/
theorem domfm_restricted_min_le_projected_rayleigh (T : E →L[ℂ] E)
    {V : Submodule ℂ E} {p : E} (hp : p ≠ 0) (hpV : p ∈ V) :
    sInf (rayleigh T '' {w : E | w ∈ V ∧ ‖w‖ = 1}) ≤ rayleigh T p := by
  obtain ⟨w, hwV, hw1, hwR⟩ := domfm_projected_rayleigh_attained_on_unit T hp hpV
  have hbdd : BddBelow (rayleigh T '' {w : E | w ∈ V ∧ ‖w‖ = 1}) := by
    refine ⟨-‖T‖, ?_⟩
    rintro r ⟨z, ⟨-, hz1⟩, rfl⟩
    exact neg_opNorm_le_rayleigh T hz1
  have hmem : rayleigh T p ∈ rayleigh T '' {w : E | w ∈ V ∧ ‖w‖ = 1} :=
    ⟨w, ⟨hwV, hw1⟩, hwR⟩
  exact csInf_le hbdd hmem

/-! ### D1.2 — the eigenvector improvement -/

/-- **D1.2 (EIG-TRADE), abstract form.**

If in addition `T y = λ y` with `λ` real, the projected Rayleigh error is
*exactly* a quadratic form in the residual, and is `O(d²)`, not `O(d)`. -/
theorem eigenvector_projection_quadratic_error (T : E →L[ℂ] E)
    (hT : (T : E →ₗ[ℂ] E).IsSymmetric) {V : Submodule ℂ E} {y p : E} {lam : ℝ}
    (hy : y ≠ 0) (hp : p ≠ 0) (hpV : p ∈ V)
    (horth : ∀ v ∈ V, ⟪v, y - p⟫_ℂ = 0)
    (hev : T y = (lam : ℂ) • y) :
    rayleigh T p - lam
        = (⟪y - p, T (y - p) - (lam : ℂ) • (y - p)⟫_ℂ).re / ‖p‖ ^ 2
      ∧ |rayleigh T p - lam|
        ≤ (‖T‖ + |lam|) * (‖y - p‖ / ‖y‖) ^ 2 / (1 - (‖y - p‖ / ‖y‖) ^ 2) := by
  have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hp0 : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hpyth : ‖y‖ ^ 2 = ‖p‖ ^ 2 + ‖y - p‖ ^ 2 := norm_proj_sq_eq hpV horth
  -- abbreviation for the shifted residual
  set w : E := y - p with hw
  set X : E := T w - (lam : ℂ) • w with hX
  -- `⟪y, X⟫ = 0`
  have hyX : ⟪y, X⟫_ℂ = 0 := by
    have h1 : ⟪y, T w⟫_ℂ = ⟪T y, w⟫_ℂ := (hT y w).symm
    rw [hX, inner_sub_right, inner_smul_right, h1, hev, inner_smul_left]
    simp
  -- `T p - λ p = -(T w - λ w)`
  have hsplit : p + w = y := by rw [hw]; abel
  have hTp : T p - (lam : ℂ) • p = -X := by
    have h : T p + T w = (lam : ℂ) • p + (lam : ℂ) • w := by
      rw [← map_add, hsplit, hev, ← smul_add, hsplit]
    rw [hX]
    have := h
    abel_nf
    abel_nf at this
    linear_combination (norm := module) this
  -- the exact identity
  have hkey : ⟪p, T p - (lam : ℂ) • p⟫_ℂ = ⟪w, X⟫_ℂ := by
    have hpw : p = y - w := by rw [← hsplit]; abel
    rw [hTp, inner_neg_right, hpw, inner_sub_left, hyX]
    ring
  have hnum : (⟪p, T p⟫_ℂ).re - lam * ‖p‖ ^ 2 = (⟪w, X⟫_ℂ).re := by
    have h := congrArg Complex.re hkey
    rw [inner_sub_right, inner_smul_right, inner_self_ofReal, Complex.sub_re,
      Complex.re_ofReal_mul, Complex.ofReal_re] at h
    exact h
  have hfirst : rayleigh T p - lam = (⟪w, X⟫_ℂ).re / ‖p‖ ^ 2 := by
    rw [rayleigh, ← hnum]
    field_simp
  refine ⟨hfirst, ?_⟩
  -- the quadratic bound
  have hXnorm : ‖X‖ ≤ (‖T‖ + |lam|) * ‖w‖ := by
    calc ‖X‖ ≤ ‖T w‖ + ‖(lam : ℂ) • w‖ := by rw [hX]; exact norm_sub_le _ _
      _ ≤ ‖T‖ * ‖w‖ + |lam| * ‖w‖ := by
          have h1 : ‖T w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
          have h2 : ‖(lam : ℂ) • w‖ = |lam| * ‖w‖ := by
            rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          linarith
      _ = (‖T‖ + |lam|) * ‖w‖ := by ring
  have habs : |(⟪w, X⟫_ℂ).re| ≤ (‖T‖ + |lam|) * ‖w‖ ^ 2 := by
    have h1 : |(⟪w, X⟫_ℂ).re| ≤ ‖⟪w, X⟫_ℂ‖ := abs_re_le_norm_complex _
    have h2 : ‖⟪w, X⟫_ℂ‖ ≤ ‖w‖ * ‖X‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    have h3 : ‖w‖ * ‖X‖ ≤ ‖w‖ * ((‖T‖ + |lam|) * ‖w‖) :=
      mul_le_mul_of_nonneg_left hXnorm (norm_nonneg _)
    nlinarith
  have hdsq : (‖w‖ / ‖y‖) ^ 2 = ‖w‖ ^ 2 / ‖y‖ ^ 2 := by rw [div_pow]
  have hone : 1 - (‖w‖ / ‖y‖) ^ 2 = ‖p‖ ^ 2 / ‖y‖ ^ 2 := by
    rw [hdsq]
    field_simp
    linarith [hpyth]
  have hp2 : (0 : ℝ) < ‖p‖ ^ 2 := by positivity
  have hy2 : (0 : ℝ) < ‖y‖ ^ 2 := by positivity
  have hrhs : (‖T‖ + |lam|) * (‖w‖ ^ 2 / ‖y‖ ^ 2) / (‖p‖ ^ 2 / ‖y‖ ^ 2)
      = (‖T‖ + |lam|) * ‖w‖ ^ 2 / ‖p‖ ^ 2 := by
    field_simp
  rw [hfirst, hone, hdsq, hrhs, abs_div, abs_of_pos hp2]
  gcongr

end Rayleigh

/-! ## 2. D1.1 / D1.2 for a Hermitian matrix on `EuclideanSpace ℂ (Fin n)`

The judge's Lean-ready head asks for `K : Matrix (Fin n) (Fin n) ℂ`,
`K.IsHermitian`, and its induced continuous linear map, with the coefficient
identity between the two stated **explicitly**, and with `M := ‖Kop‖` the
operator norm.  The identity is carried as the hypothesis `hKop`; that it is
satisfiable is `toEuclideanCLM_coeff` below. -/

section MatrixHeads

variable {n : ℕ}

/-- `Matrix.toEuclideanCLM` realises the coefficient identity, so the hypothesis
`hKop` of the heads below is never vacuous. -/
theorem toEuclideanCLM_coeff (K : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) K) x i = ∑ j, K i j * x j := rfl

/-- The coefficient identity plus `K.IsHermitian` makes `Kop` symmetric. -/
theorem isSymmetric_of_isHermitian {K : Matrix (Fin n) (Fin n) ℂ} (hK : K.IsHermitian)
    {Kop : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hKop : ∀ (x : EuclideanSpace ℂ (Fin n)) (i : Fin n), Kop x i = ∑ j, K i j * x j) :
    ((Kop : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).IsSymmetric := by
  intro x z
  have hlhs : ⟪Kop x, z⟫_ℂ = ∑ i, ∑ j, conj (K i j * x j) * z i := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hKop, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hrhs : ⟪x, Kop z⟫_ℂ = ∑ i, ∑ j, conj (x i) * (K i j * z j) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hKop, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [ContinuousLinearMap.coe_coe]
  rw [hlhs, hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : conj (K j i) = K i j := by
    have hh := hK.apply i j
    simpa [RCLike.star_def] using hh
  rw [map_mul, h]
  ring

/-- **D1.1 (TRADE), Lean-ready head.**

`K` is a Hermitian complex matrix, `Kop` the induced continuous linear map on
`E = EuclideanSpace ℂ (Fin n)` — the coefficient identity is `hKop`, and
`M := ‖Kop‖` is the **operator** norm, not an entrywise matrix norm.  `V` is a
subspace, `y ≠ 0`, and `p ≠ 0` is the orthogonal projection of `y` on `V`,
given by the witnesses `p ∈ V` and `∀ v ∈ V, ⟪v, y-p⟫ = 0`.  With
`d = ‖y-p‖/‖y‖`:

`R_K(p) ≤ R_K(y) + 2 M d`. -/
theorem domfm_projected_rayleigh_le
    {K : Matrix (Fin n) (Fin n) ℂ} (hK : K.IsHermitian)
    {Kop : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hKop : ∀ (x : EuclideanSpace ℂ (Fin n)) (i : Fin n), Kop x i = ∑ j, K i j * x j)
    {V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} {y p : EuclideanSpace ℂ (Fin n)}
    (hy : y ≠ 0) (hp : p ≠ 0) (hpV : p ∈ V)
    (horth : ∀ v ∈ V, ⟪v, y - p⟫_ℂ = 0) :
    rayleigh Kop p ≤ rayleigh Kop y + 2 * ‖Kop‖ * (‖y - p‖ / ‖y‖) :=
  rayleigh_le_of_projection_witness Kop (isSymmetric_of_isHermitian hK hKop)
    hy hp hpV horth

/-- **D1.1, variational corollary, Lean-ready head.** -/
theorem domfm_restricted_min_le_projected_rayleigh_matrix
    (Kop : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    {V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} {p : EuclideanSpace ℂ (Fin n)}
    (hp : p ≠ 0) (hpV : p ∈ V) :
    sInf (rayleigh Kop '' {w : EuclideanSpace ℂ (Fin n) | w ∈ V ∧ ‖w‖ = 1})
      ≤ rayleigh Kop p :=
  domfm_restricted_min_le_projected_rayleigh Kop hp hpV

/-- **D1.2 (EIG-TRADE), Lean-ready head.** -/
theorem domfm_eigenvector_projection_quadratic_error
    {K : Matrix (Fin n) (Fin n) ℂ} (hK : K.IsHermitian)
    {Kop : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hKop : ∀ (x : EuclideanSpace ℂ (Fin n)) (i : Fin n), Kop x i = ∑ j, K i j * x j)
    {V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} {y p : EuclideanSpace ℂ (Fin n)}
    {lam : ℝ}
    (hy : y ≠ 0) (hp : p ≠ 0) (hpV : p ∈ V)
    (horth : ∀ v ∈ V, ⟪v, y - p⟫_ℂ = 0)
    (hev : Kop y = (lam : ℂ) • y) :
    rayleigh Kop p - lam
        = (⟪y - p, Kop (y - p) - (lam : ℂ) • (y - p)⟫_ℂ).re / ‖p‖ ^ 2
      ∧ |rayleigh Kop p - lam|
        ≤ (‖Kop‖ + |lam|) * (‖y - p‖ / ‖y‖) ^ 2 / (1 - (‖y - p‖ / ‖y‖) ^ 2) :=
  eigenvector_projection_quadratic_error Kop (isSymmetric_of_isHermitian hK hKop)
    hy hp hpV horth hev

end MatrixHeads

/-! ## 3. D2.4, finite version — the absolute-Schur certificate class is empty -/

section SignedSchur

variable {n : ℕ}

/-- Signed degree `dᵢ = ∑ⱼ Jᵢⱼ` of a finite signed edge matrix. -/
def signedDegree (J : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, J i j

/-- Absolute degree `aᵢ = ∑ⱼ |Jᵢⱼ|`. -/
def absoluteDegree (J : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, |J i j|

/-- The absolute-Schur test (SCHUR) in its finite form: a strictly positive
weight `q` with `dᵢ ≥ ∑ⱼ |Jᵢⱼ| qⱼ/qᵢ` for every `i`. -/
def IsAbsoluteSchurWeight (J : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) : Prop :=
  (∀ i, 0 < q i) ∧ ∀ i, ∑ j, |J i j| * (q j / q i) ≤ signedDegree J i

/-- The signed quadratic form `∑ᵢ dᵢ|sᵢ|² - ∑ᵢⱼ Jᵢⱼ Re(conj(sᵢ) sⱼ)`, with the
full double sum.  For a zero-diagonal `J` this is the `i ≠ j` sum of D2.4; see
`signedForm_eq_offDiagonal`. -/
def signedForm (J : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℂ) : ℝ :=
  (∑ i, signedDegree J i * ‖s i‖ ^ 2)
    - ∑ i, ∑ j, J i j * (conj (s i) * s j).re

/-- With zero diagonal the full double sum is the off-diagonal double sum. -/
theorem signedForm_eq_offDiagonal (J : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, J i i = 0) (s : Fin n → ℂ) :
    signedForm J s
      = (∑ i, signedDegree J i * ‖s i‖ ^ 2)
        - ∑ i, ∑ j ∈ Finset.univ.erase i, J i j * (conj (s i) * s j).re := by
  rw [signedForm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag i]
  ring

/-- The elementary edge inequality `z + 1/z ≥ 2` in its ratio form. -/
theorem two_le_ratio_add_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (2 : ℝ) ≤ b / a + a / b := by
  rw [div_add_div _ _ ha.ne' hb.ne', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (b - a)]

/-- The symmetrisation `∑ᵢⱼ |Jᵢⱼ| qⱼ/qᵢ = ∑ᵢⱼ |Jᵢⱼ| qᵢ/qⱼ` for symmetric `J`. -/
theorem schur_sum_swap (J : Matrix (Fin n) (Fin n) ℝ) (hsymm : ∀ i j, J i j = J j i)
    (q : Fin n → ℝ) :
    ∑ i, ∑ j, |J i j| * (q j / q i) = ∑ i, ∑ j, |J i j| * (q i / q j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm j i]

/-- **D2.4 (finite), impossibility.**

For a finite symmetric real signed edge matrix `J` whose total signed-degree
defect `∑ᵢ (dᵢ - aᵢ)` is strictly negative, there is **no** strictly positive
weight `q` satisfying the absolute-Schur test.

This kills the whole class of positive diagonal absolute-Schur certificates.
It is **not** a statement that the quadratic form is negative; see
`domfm_signed_three_vertex_psd_plant`. -/
theorem domfm_no_positive_absolute_schur_weight
    (J : Matrix (Fin n) (Fin n) ℝ) (hsymm : ∀ i j, J i j = J j i)
    (hdefect : ∑ i, (signedDegree J i - absoluteDegree J i) < 0) :
    ¬ ∃ q : Fin n → ℝ, IsAbsoluteSchurWeight J q := by
  rintro ⟨q, hqpos, hq⟩
  have hSle : (∑ i, ∑ j, |J i j| * (q j / q i)) ≤ ∑ i, signedDegree J i :=
    Finset.sum_le_sum fun i _ => hq i
  have hswap := schur_sum_swap J hsymm q
  have hlow : (∑ i, absoluteDegree J i) ≤ ∑ i, ∑ j, |J i j| * (q j / q i) := by
    have hstep : ∀ i : Fin n, ∀ j : Fin n,
        |J i j| * 2 ≤ |J i j| * (q j / q i) + |J i j| * (q i / q j) := by
      intro i j
      have h := two_le_ratio_add_ratio (hqpos i) (hqpos j)
      nlinarith [abs_nonneg (J i j)]
    have hsum : ∑ i, ∑ j, |J i j| * 2
        ≤ ∑ i, ∑ j, (|J i j| * (q j / q i) + |J i j| * (q i / q j)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
    have hsplit : ∑ i, ∑ j, (|J i j| * (q j / q i) + |J i j| * (q i / q j))
        = (∑ i, ∑ j, |J i j| * (q j / q i)) + ∑ i, ∑ j, |J i j| * (q i / q j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    have hleft : ∑ i, ∑ j, |J i j| * 2 = 2 * ∑ i, absoluteDegree J i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [absoluteDegree, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hleft, hsplit, ← hswap] at hsum
    linarith
  have hd : ∑ i, (signedDegree J i - absoluteDegree J i)
      = (∑ i, signedDegree J i) - ∑ i, absoluteDegree J i := by
    rw [Finset.sum_sub_distrib]
  rw [hd] at hdefect
  linarith

/-- **D2.4 (finite), sufficiency.**

If a strictly positive absolute-Schur weight `q` does exist for a symmetric
`J`, then the signed quadratic form is nonnegative for every complex `s`.

This is the mechanism that the impossibility theorem above kills. -/
theorem domfm_absolute_schur_sufficient
    (J : Matrix (Fin n) (Fin n) ℝ) (hsymm : ∀ i j, J i j = J j i)
    {q : Fin n → ℝ} (hq : IsAbsoluteSchurWeight J q) (s : Fin n → ℂ) :
    0 ≤ signedForm J s := by
  obtain ⟨hqpos, hqle⟩ := hq
  -- pointwise: `Jᵢⱼ Re(conj sᵢ sⱼ) ≤ |Jᵢⱼ| (|sᵢ|² qⱼ/qᵢ + |sⱼ|² qᵢ/qⱼ)/2`
  have hpoint : ∀ i j : Fin n,
      2 * (J i j * (conj (s i) * s j).re)
        ≤ |J i j| * (‖s i‖ ^ 2 * (q j / q i)) + |J i j| * (‖s j‖ ^ 2 * (q i / q j)) := by
    intro i j
    have h1 : J i j * (conj (s i) * s j).re ≤ |J i j| * (‖s i‖ * ‖s j‖) := by
      have hre : |(conj (s i) * s j).re| ≤ ‖s i‖ * ‖s j‖ := by
        calc |(conj (s i) * s j).re| ≤ ‖conj (s i) * s j‖ := abs_re_le_norm_complex _
          _ = ‖s i‖ * ‖s j‖ := by rw [norm_mul, RCLike.norm_conj]
      have h2 : J i j * (conj (s i) * s j).re ≤ |J i j * (conj (s i) * s j).re| :=
        le_abs_self _
      rw [abs_mul] at h2
      have h3 : |J i j| * |(conj (s i) * s j).re| ≤ |J i j| * (‖s i‖ * ‖s j‖) :=
        mul_le_mul_of_nonneg_left hre (abs_nonneg _)
      linarith
    have hAM : 2 * (‖s i‖ * ‖s j‖)
        ≤ ‖s i‖ ^ 2 * (q j / q i) + ‖s j‖ ^ 2 * (q i / q j) := by
      have hqi := hqpos i
      have hqj := hqpos j
      have hident : ‖s i‖ ^ 2 * (q j / q i) + ‖s j‖ ^ 2 * (q i / q j)
            - 2 * (‖s i‖ * ‖s j‖)
          = (‖s i‖ * q j - ‖s j‖ * q i) ^ 2 / (q i * q j) := by
        field_simp
        ring
      nlinarith [div_nonneg (sq_nonneg (‖s i‖ * q j - ‖s j‖ * q i))
        (le_of_lt (mul_pos hqi hqj))]
    nlinarith [abs_nonneg (J i j)]
  -- sum the pointwise bound
  have hT2 : ∑ i, ∑ j, |J i j| * (‖s j‖ ^ 2 * (q i / q j))
      = ∑ i, ∑ j, |J i j| * (‖s i‖ ^ 2 * (q j / q i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
  have hcross : ∑ i, ∑ j, J i j * (conj (s i) * s j).re
      ≤ ∑ i, ∑ j, |J i j| * (‖s i‖ ^ 2 * (q j / q i)) := by
    have hstep : ∑ i, ∑ j, 2 * (J i j * (conj (s i) * s j).re)
        ≤ ∑ i, ∑ j, (|J i j| * (‖s i‖ ^ 2 * (q j / q i))
            + |J i j| * (‖s j‖ ^ 2 * (q i / q j))) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
    have hL : ∑ i, ∑ j, 2 * (J i j * (conj (s i) * s j).re)
        = 2 * ∑ i, ∑ j, J i j * (conj (s i) * s j).re := by
      simp [Finset.mul_sum]
    have hsplit : ∑ i, ∑ j, (|J i j| * (‖s i‖ ^ 2 * (q j / q i))
          + |J i j| * (‖s j‖ ^ 2 * (q i / q j)))
        = (∑ i, ∑ j, |J i j| * (‖s i‖ ^ 2 * (q j / q i)))
            + ∑ i, ∑ j, |J i j| * (‖s j‖ ^ 2 * (q i / q j)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    rw [hL, hsplit, hT2] at hstep
    linarith
  -- the diagonal bound from the Schur weight
  have hdiagbound : ∑ i, ∑ j, |J i j| * (‖s i‖ ^ 2 * (q j / q i))
      ≤ ∑ i, signedDegree J i * ‖s i‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hrow : ∑ j, |J i j| * (‖s i‖ ^ 2 * (q j / q i))
        = ‖s i‖ ^ 2 * ∑ j, |J i j| * (q j / q i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrow, mul_comm (signedDegree J i)]
    exact mul_le_mul_of_nonneg_left (hqle i) (by positivity)
  rw [signedForm]
  linarith

end SignedSchur

/-! ## 4. D2.4 (SIGNED-PSD) — the mandatory nonnegativity plant -/

section SignedPlant

/-- The three-vertex signed edge matrix with `w₁₂ = w₂₃ = 2` and `w₁₃ = -1`. -/
def plantJ3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 2, -1; 2, 0, 2; -1, 2, 0]

/-- Its graph Laplacian `diag(d) - J`, the matrix displayed in D2.4. -/
def plantLaplacian3 : Matrix (Fin 3) (Fin 3) ℝ := !![1, -2, 1; -2, 4, -2; 1, -2, 1]

/-- The entry-reduction simp set for the `3 × 3` plants. -/
theorem plantJ3_symm : ∀ i j, plantJ3 i j = plantJ3 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plantJ3, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem plantJ3_diag : ∀ i, plantJ3 i i = 0 := by
  intro i
  fin_cases i <;>
    norm_num [plantJ3, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The plant has a strictly negative interaction edge. -/
theorem plantJ3_negative_edge : plantJ3 0 2 < 0 := by
  norm_num [plantJ3, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem plantLaplacian3_eq :
    plantLaplacian3 = Matrix.diagonal (signedDegree plantJ3) - plantJ3 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [plantLaplacian3, plantJ3, signedDegree, Matrix.diagonal, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The Laplacian of the plant has zero row sums. -/
theorem plantLaplacian3_row_sums (i : Fin 3) : ∑ j, plantLaplacian3 i j = 0 := by
  fin_cases i <;>
    norm_num [plantLaplacian3, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]

/-- **(SIGNED-PSD), the identity.**  For all complex `s₁ s₂ s₃`,
`2|s₁-s₂|² + 2|s₂-s₃|² - |s₁-s₃|² = |s₁ - 2s₂ + s₃|²`. -/
theorem domfm_signed_three_vertex_identity (s1 s2 s3 : ℂ) :
    2 * ‖s1 - s2‖ ^ 2 + 2 * ‖s2 - s3‖ ^ 2 - ‖s1 - s3‖ ^ 2
      = ‖s1 - 2 * s2 + s3‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The signed form of the plant is exactly `|s₁ - 2s₂ + s₃|²`. -/
theorem plantJ3_signedForm (s : Fin 3 → ℂ) :
    signedForm plantJ3 s = ‖s 0 - 2 * s 1 + s 2‖ ^ 2 := by
  simp only [signedForm, signedDegree, plantJ3, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The plant's signed form is nonnegative. -/
theorem plantJ3_signedForm_nonneg (s : Fin 3 → ℂ) : 0 ≤ signedForm plantJ3 s := by
  rw [plantJ3_signedForm]
  positivity

/-- The plant's signed-degree defect is `-4 < 0`, so the obstruction of
`domfm_no_positive_absolute_schur_weight` applies to it. -/
theorem plantJ3_defect :
    ∑ i, (signedDegree plantJ3 i - absoluteDegree plantJ3 i) = -4 := by
  norm_num [signedDegree, absoluteDegree, plantJ3, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **D2.4 (SIGNED-PSD), the mandatory plant.**

On three vertices with edge weights `w₁₂ = w₂₃ = 2`, `w₁₃ = -1`:

1. the polarisation identity holds for all complex triples;
2. the resulting Laplacian has zero row sums and a negative edge;
3. the signed-degree defect is `-4 < 0`, so **no** positive absolute-Schur
   weight exists;
4. and yet the signed quadratic form is nonnegative for every complex `s`.

Therefore reading the absolute-Schur kill (item 3) as negativity of the form
(the negation of item 4) is a demonstrable logic error. -/
theorem domfm_signed_three_vertex_psd_plant :
    (∀ s1 s2 s3 : ℂ,
        2 * ‖s1 - s2‖ ^ 2 + 2 * ‖s2 - s3‖ ^ 2 - ‖s1 - s3‖ ^ 2
          = ‖s1 - 2 * s2 + s3‖ ^ 2)
      ∧ plantLaplacian3 = Matrix.diagonal (signedDegree plantJ3) - plantJ3
      ∧ (∀ i, ∑ j, plantLaplacian3 i j = 0)
      ∧ plantJ3 0 2 < 0
      ∧ (∑ i, (signedDegree plantJ3 i - absoluteDegree plantJ3 i)) < 0
      ∧ (¬ ∃ q : Fin 3 → ℝ, IsAbsoluteSchurWeight plantJ3 q)
      ∧ (∀ s : Fin 3 → ℂ, 0 ≤ signedForm plantJ3 s) := by
  have hneg : (∑ i, (signedDegree plantJ3 i - absoluteDegree plantJ3 i)) < 0 := by
    rw [plantJ3_defect]; norm_num
  exact ⟨domfm_signed_three_vertex_identity, plantLaplacian3_eq, plantLaplacian3_row_sums,
    plantJ3_negative_edge, hneg,
    domfm_no_positive_absolute_schur_weight plantJ3 plantJ3_symm hneg,
    plantJ3_signedForm_nonneg⟩

end SignedPlant

/-! ## 5. D3.2 (COMP-GAP) — compression of `K = Γ - c_L I - 2ββ*` -/

section Compression

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- Compression of a rank-one Hermitian: `Zᴴ (ββ*) Z = (Zᴴβ)(Zᴴβ)*`. -/
theorem conjTranspose_rankOneStar_mul (β : n → ℂ) (Z : Matrix n k ℂ) :
    Zᴴ * Q3.RouteB.rankOneStar β * Z = Q3.RouteB.rankOneStar (Zᴴ *ᵥ β) := by
  refine Matrix.ext fun a b => ?_
  have hL : (Zᴴ * Q3.RouteB.rankOneStar β * Z) a b
      = ∑ j, ∑ i, conj (Z i a) * β i * conj (β j) * Z j b := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.conjTranspose_apply, Q3.RouteB.rankOneStar, Matrix.vecMulVec_apply,
      Pi.star_apply, RCLike.star_def]
    ring
  have hR : Q3.RouteB.rankOneStar (Zᴴ *ᵥ β) a b
      = ∑ i, ∑ j, conj (Z i a) * β i * conj (β j) * Z j b := by
    simp only [Q3.RouteB.rankOneStar, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
      Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum, map_mul,
      Complex.conj_conj, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hL, hR, Finset.sum_comm]

/-- **D3.2 (COMP-GAP), the exact matrix identity.**

For `K = Γ - c_L I - 2ββ*` and any synthesis matrix `Z`,

`Zᴴ K Z + e ZᴴZ = Zᴴ Γ Z - (c_L - e) ZᴴZ - 2 (Zᴴβ)(Zᴴβ)*`.

Pure algebra: no positivity, no analytic input, redundant `Z` allowed.  The
shift is carried by `ZᴴZ`, not by the identity matrix; for isometric `Z` the
two coincide, see `domfm_compressed_gram_minus_shift_isometry`. -/
theorem domfm_compressed_gram_minus_shift (Γ : Matrix n n ℂ) (cL e : ℝ) (β : n → ℂ)
    (Z : Matrix n k ℂ) :
    Zᴴ * Q3.RouteB.weilShiftMatrix Γ cL β * Z + (e : ℂ) • (Zᴴ * Z)
      = Zᴴ * Γ * Z - ((cL - e : ℝ) : ℂ) • (Zᴴ * Z)
        - (2 : ℂ) • Q3.RouteB.rankOneStar (Zᴴ *ᵥ β) := by
  rw [Q3.RouteB.weilShiftMatrix]
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, conjTranspose_rankOneStar_mul]
  push_cast
  simp only [sub_smul]
  abel

/-- **D3.2 (COMP-GAP), the equivalence.**

`Zᴴ K Z + e ZᴴZ ⪰ 0` **iff** `Zᴴ Γ Z - (c_L - e) ZᴴZ - 2 (Zᴴβ)(Zᴴβ)* ⪰ 0`.

This is an equivalence of two statements about the compressed object; it proves
neither side, exactly as `Q3.RouteB.weilShiftMatrix_posSemidef_iff` proves
neither side of (GAP-GRAM). -/
theorem domfm_compressed_gram_minus_shift_posSemidef_iff (Γ : Matrix n n ℂ) (cL e : ℝ)
    (β : n → ℂ) (Z : Matrix n k ℂ) :
    (Zᴴ * Q3.RouteB.weilShiftMatrix Γ cL β * Z + (e : ℂ) • (Zᴴ * Z)).PosSemidef
      ↔ (Zᴴ * Γ * Z - ((cL - e : ℝ) : ℂ) • (Zᴴ * Z)
          - (2 : ℂ) • Q3.RouteB.rankOneStar (Zᴴ *ᵥ β)).PosSemidef := by
  rw [domfm_compressed_gram_minus_shift]

/-- For an **isometric** synthesis matrix (`ZᴴZ = 1`) the compressed object is
again literally a `Gram minus shift`: source `Zᴴ Γ Z`, shift `c_L - e`, pole
vector `Zᴴβ`.  Redundant or non-isometric `Z` keeps the `ZᴴZ` form above; a
generalized eigenvalue reading then requires the quotient by `ker Z`. -/
theorem domfm_compressed_gram_minus_shift_isometry (Γ : Matrix n n ℂ) (cL e : ℝ)
    (β : n → ℂ) (Z : Matrix n k ℂ) (hZ : Zᴴ * Z = (1 : Matrix k k ℂ)) :
    Zᴴ * Q3.RouteB.weilShiftMatrix Γ cL β * Z + (e : ℂ) • (Zᴴ * Z)
      = Q3.RouteB.weilShiftMatrix (Zᴴ * Γ * Z) (cL - e) (Zᴴ *ᵥ β) := by
  rw [domfm_compressed_gram_minus_shift, hZ, Q3.RouteB.weilShiftMatrix]

/-! ### The proper-compression plant -/

/-- The synthesis matrix `Z = (0,1)ᵀ`, whose range is the second coordinate
line only. -/
def plantZ : Matrix (Fin 2) (Fin 1) ℂ := Matrix.of ![![0], ![1]]

theorem plantZ_compression_eq :
    plantZᴴ * (Matrix.diagonal ![(-1 : ℂ), 1]) * plantZ = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  refine Matrix.ext fun a b => ?_
  fin_cases a
  fin_cases b
  norm_num [plantZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
    Matrix.one_apply, Fin.sum_univ_two]

/-- **D3.2, the proper-compression plant.**

With `K = diag(-1,1)` — the judge's `Gram minus shift` plant, i.e.
`K = weilShiftMatrix (diag(0,2)) 1 0` — and `Z = (0,1)ᵀ`:
the compressed matrix `ZᴴKZ` is positive semidefinite while `K` is not.

Hence a dictionary is not a harmless change of basis unless its range is
proved full. -/
theorem domfm_proper_compression_negative_complement_plant :
    Q3.RouteB.weilShiftMatrix (Matrix.diagonal ![(0 : ℂ), 2]) 1 (0 : Fin 2 → ℂ)
        = Matrix.diagonal ![(-1 : ℂ), 1]
      ∧ (plantZᴴ * (Matrix.diagonal ![(-1 : ℂ), 1]) * plantZ).PosSemidef
      ∧ ¬ (Matrix.diagonal ![(-1 : ℂ), 1]).PosSemidef := by
  refine ⟨Q3.RouteB.weilShiftMatrix_plant_eq, ?_, ?_⟩
  · rw [plantZ_compression_eq]
    exact Matrix.PosSemidef.one
  · rw [← Q3.RouteB.weilShiftMatrix_plant_eq]
    exact Q3.RouteB.weilShiftMatrix_plant_not_posSemidef

end Compression

end Q3.RouteB.Domfm
