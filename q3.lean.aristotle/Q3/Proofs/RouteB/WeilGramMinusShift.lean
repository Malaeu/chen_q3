import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Fin.VecNotation

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# Finite quadratic algebra behind the Weil "Gram minus shift" assembly

Source boundary (read this before citing anything from this file).

This file formalises **only** the finite complex linear algebra of the judge's
identity (8) in
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DIRECT_WEIL_SOURCE_PROOF_2026-09-04.md`,
namely the shape

  `K = Γ − c_L · I − 2 β β*`,   `Γ ⪰ 0`.

What is proved here:

* `weil_pole_difference_of_squares` — the pole term as a difference of squares
  (identity (3) of the verdict at the level of two complex scalars).
* `weilShiftMatrix_quadForm` — part (a): the exact quadratic-form identity.
* `weilShiftMatrix_add_shift_posSemidef` — part (b): `K + c_L·I + 2ββ* ⪰ 0`
  holds unconditionally once `Γ ⪰ 0`, because that sum **is** `Γ`.
* `weilShiftMatrix_re_lower_bound` — part (c): the Cauchy–Schwarz corollary
  `c*Kc ≥ −(c_L + 2‖β‖²)‖c‖²`, i.e. a lower bound on the bottom of the spectrum.
* `weilShiftMatrix_plant_*` — part (d): the judge's plant `Γ = diag(0,2)`,
  `c_L = 1`, `β = 0` gives `K = diag(−1,1)`, an explicit witness of
  `c*Kc < 0`, hence `Γ ⪰ 0` does **not** imply `K ⪰ 0`.
* `weilShiftMatrix_posSemidef_iff` — part (e): `K ⪰ 0` is *equivalent* to the
  frame bound (GAP-GRAM) `∀c: c*Γc ≥ c_L‖c‖² + 2|β*c|²`.  The equivalence is
  trivial given (a); it does not prove either side.
* `posSemidef_gramMatrix`, `posSemidef_weighted_sum`, `weilGamma_posSemidef` —
  part (f): a Gram matrix of a finite family of vectors in a complex inner
  product space is positive semidefinite, a nonnegative finite combination of
  positive semidefinite matrices is positive semidefinite, and hence the
  assembled `Γ` is positive semidefinite.

What is **not** proved here, and must not be read into any statement below:

* No claim that `K` is positive semidefinite.  The plant theorems are in this
  file precisely to block that inference.
* No analytic input at all.  The verdict builds `Γ` as
  `∫₀^L a(t) D(t) dt + Σ_{n≤m} (Λ(n)/√n) D(log n) + 2αα*`.  Only the **finite**
  weighted-sum version is formalised here; the integral term is out of scope
  for this file and is not modelled by any declaration below.
* No source crosswalk to the literal CCM entries (`ccmQKernel`, `ccmW02Entry`,
  `ccmPrimeEntryN1`, `ccmWREntry`); that is a separate obligation.
* Nothing conditional on RH and no route promotion.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. The pole term as a difference of squares -/

/-- **Judge's head (1).**  For complex `A`, `B`,
`2 Re(A conj B) = 2|(A+B)/2|² − 2|(A−B)/2|²`.

This is the scalar content of identity (3) of the verdict: with `A = A₊`,
`B = A₋` and `C_L = (A₊+A₋)/2`, `S_L = (A₊−A₋)/2` it reads
`W₀,₂ = 2|C_L|² − 2|S_L|²`. -/
theorem weil_pole_difference_of_squares (A B : ℂ) :
    2 * (A * conj B).re = 2 * ‖(A + B) / 2‖ ^ 2 - 2 * ‖(A - B) / 2‖ ^ 2 := by
  have hdiv : ∀ z : ℂ, ‖z / 2‖ ^ 2 = ‖z‖ ^ 2 / 4 := by
    intro z
    rw [norm_div, div_pow]
    norm_num
  simp only [hdiv, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The `cosh`/`sinh` reading of the same identity: if `C = (A₊+A₋)/2` and
`S = (A₊−A₋)/2` then `2|C|² − 2|S|² = 2 Re((C+S) conj (C−S))`. -/
theorem weil_pole_difference_of_squares_cosh_sinh (C S : ℂ) :
    2 * ‖C‖ ^ 2 - 2 * ‖S‖ ^ 2 = 2 * ((C + S) * conj (C - S)).re := by
  have h := weil_pole_difference_of_squares (C + S) (C - S)
  have h1 : ((C + S) + (C - S)) / 2 = C := by ring
  have h2 : ((C + S) - (C - S)) / 2 = S := by ring
  rw [h1, h2] at h
  exact h.symm

/-! ## 2. The finite objects: rank-one shift and `K = Γ − c_L I − 2 β β*` -/

/-- The rank-one Hermitian matrix `v v*`, i.e. `(v v*)ᵢⱼ = vᵢ · conj vⱼ`. -/
def rankOneStar (v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec v (star v)

/-- The shifted matrix of the judge's identity (8):
`K = Γ − c_L · I − 2 β β*`, with `c_L` a real scalar. -/
def weilShiftMatrix (Γ : Matrix n n ℂ) (cL : ℝ) (β : n → ℂ) : Matrix n n ℂ :=
  Γ - (cL : ℂ) • (1 : Matrix n n ℂ) - (2 : ℂ) • rankOneStar β

/-- `v v* ⪰ 0`; reuses `Matrix.posSemidef_vecMulVec_self_star`. -/
theorem rankOneStar_posSemidef (v : n → ℂ) : (rankOneStar v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

/-- The quadratic form of a rank-one shift: `c*(v v*)c = conj(v*c) · (v*c)`. -/
theorem quadForm_rankOneStar (v c : n → ℂ) :
    star c ⬝ᵥ (rankOneStar v *ᵥ c) = conj (star v ⬝ᵥ c) * (star v ⬝ᵥ c) := by
  have hrow : ∀ i, (rankOneStar v *ᵥ c) i = v i * (star v ⬝ᵥ c) := by
    intro i
    simp [rankOneStar, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
      Finset.mul_sum, mul_assoc]
  calc star c ⬝ᵥ (rankOneStar v *ᵥ c)
      = ∑ i, conj (c i) * (v i * (star v ⬝ᵥ c)) := by
        simp [dotProduct, hrow]
    _ = (∑ i, conj (c i) * v i) * (star v ⬝ᵥ c) := by
        rw [Finset.sum_mul]; simp [mul_assoc]
    _ = conj (star v ⬝ᵥ c) * (star v ⬝ᵥ c) := by
        congr 1
        simp [dotProduct, map_sum, mul_comm]

/-- `c*c` is the real number `∑ᵢ ‖cᵢ‖²`. -/
theorem dotProduct_star_self (c : n → ℂ) :
    star c ⬝ᵥ c = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.ofReal_sum, ← Complex.normSq_eq_norm_sq,
    ← Complex.mul_conj, mul_comm]

/-- `conj z · z` is the real number `‖z‖²`. -/
theorem conj_mul_self_ofReal (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm]

/-! ## 3. Part (a): the exact quadratic-form identity -/

/-- **Part (a).**  For every complex vector `c`,
`c*Kc = c*Γc − c_L‖c‖² − 2|β*c|²`.

Purely algebraic: no positivity hypothesis is used. -/
theorem weilShiftMatrix_quadForm (Γ : Matrix n n ℂ) (cL : ℝ) (β c : n → ℂ) :
    star c ⬝ᵥ (weilShiftMatrix Γ cL β *ᵥ c)
      = star c ⬝ᵥ (Γ *ᵥ c) - (cL : ℂ) * (star c ⬝ᵥ c)
        - 2 * (conj (star β ⬝ᵥ c) * (star β ⬝ᵥ c)) := by
  have hone : star c ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ c) = star c ⬝ᵥ c := by
    rw [Matrix.one_mulVec]
  rw [weilShiftMatrix, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, dotProduct_sub, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, hone, quadForm_rankOneStar]
  simp [smul_eq_mul]

/-- The real form of part (a): `Re(c*Kc) = Re(c*Γc) − c_L·∑‖cᵢ‖² − 2‖β*c‖²`. -/
theorem weilShiftMatrix_re_quadForm (Γ : Matrix n n ℂ) (cL : ℝ) (β c : n → ℂ) :
    (star c ⬝ᵥ (weilShiftMatrix Γ cL β *ᵥ c)).re
      = (star c ⬝ᵥ (Γ *ᵥ c)).re - cL * (∑ i, ‖c i‖ ^ 2) - 2 * ‖star β ⬝ᵥ c‖ ^ 2 := by
  rw [weilShiftMatrix_quadForm, dotProduct_star_self, conj_mul_self_ofReal]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-! ## 4. Part (b): the unconditional shifted positivity -/

/-- Adding the shift back reproduces `Γ` exactly. -/
theorem weilShiftMatrix_add_shift (Γ : Matrix n n ℂ) (cL : ℝ) (β : n → ℂ) :
    weilShiftMatrix Γ cL β + (cL : ℂ) • (1 : Matrix n n ℂ) + (2 : ℂ) • rankOneStar β = Γ := by
  simp only [weilShiftMatrix]
  abel

/-- **Part (b).**  `K + c_L·I + 2ββ* ⪰ 0` whenever `Γ ⪰ 0`.

This is the whole certified content of the judge's identity (8).  It is *not*
`K ⪰ 0`: see `weilShiftMatrix_plant_not_posSemidef`. -/
theorem weilShiftMatrix_add_shift_posSemidef {Γ : Matrix n n ℂ} (hΓ : Γ.PosSemidef)
    (cL : ℝ) (β : n → ℂ) :
    (weilShiftMatrix Γ cL β + (cL : ℂ) • (1 : Matrix n n ℂ)
      + (2 : ℂ) • rankOneStar β).PosSemidef := by
  rw [weilShiftMatrix_add_shift]
  exact hΓ

/-! ## 5. Part (c): the Cauchy–Schwarz lower bound -/

/-- Discrete Cauchy–Schwarz on `n → ℂ`:
`‖β*c‖² ≤ (∑ᵢ‖βᵢ‖²)(∑ᵢ‖cᵢ‖²)`. -/
theorem norm_dotProduct_star_sq_le (v c : n → ℂ) :
    ‖star v ⬝ᵥ c‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * (∑ i, ‖c i‖ ^ 2) := by
  set x : EuclideanSpace ℂ n := WithLp.toLp 2 v with hx
  set y : EuclideanSpace ℂ n := WithLp.toLp 2 c with hy
  have hinner : star v ⬝ᵥ c = ⟪x, y⟫_ℂ := by
    rw [hx, hy, EuclideanSpace.inner_toLp_toLp]
    exact dotProduct_comm _ _
  have hnx : ‖x‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hny : ‖y‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := EuclideanSpace.norm_sq_eq y
  have hcs : ‖⟪x, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm (𝕜 := ℂ) x y
  calc ‖star v ⬝ᵥ c‖ ^ 2 = ‖⟪x, y⟫_ℂ‖ ^ 2 := by rw [hinner]
    _ ≤ (‖x‖ * ‖y‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ = (∑ i, ‖v i‖ ^ 2) * (∑ i, ‖c i‖ ^ 2) := by rw [mul_pow, hnx, hny]

/-- **Part (c).**  With `Γ ⪰ 0`,
`Re(c*Kc) ≥ −(c_L + 2‖β‖²)‖c‖²` for every `c`;
equivalently `λ_min(K) ≥ −(c_L + 2‖β‖²)`.

This is a *lower* bound only.  It is compatible with `K` having negative
eigenvalues and asserts nothing about the sign of `K`. -/
theorem weilShiftMatrix_re_lower_bound {Γ : Matrix n n ℂ} (hΓ : Γ.PosSemidef)
    (cL : ℝ) (β c : n → ℂ) :
    -((cL + 2 * ∑ i, ‖β i‖ ^ 2) * ∑ i, ‖c i‖ ^ 2)
      ≤ (star c ⬝ᵥ (weilShiftMatrix Γ cL β *ᵥ c)).re := by
  have hΓc : 0 ≤ (star c ⬝ᵥ (Γ *ᵥ c)).re :=
    (Complex.nonneg_iff.mp (hΓ.dotProduct_mulVec_nonneg c)).1
  have hcs := norm_dotProduct_star_sq_le β c
  rw [weilShiftMatrix_re_quadForm]
  nlinarith [hΓc, hcs, Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    sq_nonneg ‖c i‖)]

/-! ## 6. Part (e): positivity of `K` is exactly the frame bound (GAP-GRAM) -/

/-- `c_L · I` is Hermitian for real `c_L`. -/
theorem smul_one_isHermitian (cL : ℝ) :
    ((cL : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;>
    simp [Matrix.conjTranspose_apply, h, eq_comm, Matrix.smul_apply, smul_eq_mul]

/-- `K` is Hermitian as soon as `Γ` is. -/
theorem weilShiftMatrix_isHermitian {Γ : Matrix n n ℂ} (hΓ : Γ.IsHermitian)
    (cL : ℝ) (β : n → ℂ) : (weilShiftMatrix Γ cL β).IsHermitian := by
  refine Matrix.IsHermitian.sub (Matrix.IsHermitian.sub hΓ (smul_one_isHermitian cL)) ?_
  have h := (rankOneStar_posSemidef β).isHermitian
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun M : Matrix n n ℂ => M j i) h
  simp only [Matrix.conjTranspose_apply] at this ⊢
  simp [Matrix.smul_apply, smul_eq_mul, ← this]

/-- **Part (e).**  For Hermitian `Γ`, `K ⪰ 0` **iff** the frame bound holds:
`∀c: c*Γc ≥ c_L‖c‖² + 2|β*c|²`  (the judge's (GAP-GRAM) with `e_m = 0`).

The equivalence is a restatement of part (a); it proves neither side.  In
particular `Γ ⪰ 0` alone is strictly weaker than the right-hand side. -/
theorem weilShiftMatrix_posSemidef_iff {Γ : Matrix n n ℂ} (hΓ : Γ.IsHermitian)
    (cL : ℝ) (β : n → ℂ) :
    (weilShiftMatrix Γ cL β).PosSemidef ↔
      ∀ c : n → ℂ,
        (cL : ℂ) * (star c ⬝ᵥ c) + 2 * (conj (star β ⬝ᵥ c) * (star β ⬝ᵥ c))
          ≤ star c ⬝ᵥ (Γ *ᵥ c) := by
  constructor
  · intro h c
    have hnn := h.dotProduct_mulVec_nonneg c
    rw [weilShiftMatrix_quadForm, sub_sub] at hnn
    exact sub_nonneg.mp hnn
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (weilShiftMatrix_isHermitian hΓ cL β) fun c => ?_
    have := sub_nonneg.mpr (h c)
    rw [weilShiftMatrix_quadForm, sub_sub]
    exact this

/-! ## 7. Part (d): the judge's plant — `Γ ⪰ 0` does not give `K ⪰ 0` -/

/-- The plant matrix `Γ = diag(0,2)` is positive semidefinite. -/
theorem weilShiftMatrix_plant_gamma_posSemidef :
    (Matrix.diagonal ![(0 : ℂ), 2]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- With `Γ = diag(0,2)`, `c_L = 1`, `β = 0` the judge's identity gives
`K = diag(−1,1)`. -/
theorem weilShiftMatrix_plant_eq :
    weilShiftMatrix (Matrix.diagonal ![(0 : ℂ), 2]) 1 (0 : Fin 2 → ℂ)
      = Matrix.diagonal ![(-1 : ℂ), 1] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [weilShiftMatrix, rankOneStar, Matrix.diagonal, Matrix.one_apply,
      Matrix.vecMulVec_apply]

/-- **Part (d), witness form.**  On the plant there is an explicit vector with
strictly negative energy: `c = (1,0)` gives `c*Kc = −1`. -/
theorem weilShiftMatrix_plant_negative :
    ∃ c : Fin 2 → ℂ,
      (star c ⬝ᵥ (weilShiftMatrix (Matrix.diagonal ![(0 : ℂ), 2]) 1 (0 : Fin 2 → ℂ) *ᵥ c)).re
        < 0 := by
  refine ⟨![1, 0], ?_⟩
  rw [weilShiftMatrix_plant_eq]
  norm_num [dotProduct, Matrix.mulVec, Matrix.diagonal, Fin.sum_univ_two]

/-- **Part (d).**  Positive semidefiniteness of `Γ` does **not** imply positive
semidefiniteness of `K = Γ − c_L·I − 2ββ*`.  Any checker that verifies only
`Γ ⪰ 0` must reject the inference `K ⪰ 0`. -/
theorem weilShiftMatrix_plant_not_posSemidef :
    ¬ (weilShiftMatrix (Matrix.diagonal ![(0 : ℂ), 2]) 1 (0 : Fin 2 → ℂ)).PosSemidef := by
  intro h
  obtain ⟨c, hc⟩ := weilShiftMatrix_plant_negative
  exact absurd (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg c)).1 (not_le.mpr hc)

/-- The plant, packaged: `Γ ⪰ 0` and yet `K` is not positive semidefinite. -/
theorem weilShiftMatrix_plant :
    (Matrix.diagonal ![(0 : ℂ), 2]).PosSemidef ∧
      ¬ (weilShiftMatrix (Matrix.diagonal ![(0 : ℂ), 2]) 1 (0 : Fin 2 → ℂ)).PosSemidef :=
  ⟨weilShiftMatrix_plant_gamma_posSemidef, weilShiftMatrix_plant_not_posSemidef⟩

/-! ## 8. Part (f): the translation-difference Gram matrix and the assembly of `Γ` -/

/-- **Part (f), abstract form.**  For a finite family `v : n → E` of vectors in a
complex inner product space, the Gram matrix `Mⱼₖ = ⟪vⱼ, vₖ⟫` is positive
semidefinite.

Applied with `vⱼ = τ_t φⱼ − φⱼ` this is the positivity of the
translation-difference matrix `D(t)` of the verdict; the `L²` model itself is
not formalised here. -/
theorem posSemidef_gramMatrix {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : n → E) :
    (Matrix.of fun j k => ⟪v j, v k⟫_ℂ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.ext fun i j => ?_
    simp [Matrix.conjTranspose_apply, inner_conj_symm]
  · intro x
    have hq : star x ⬝ᵥ ((Matrix.of fun j k => ⟪v j, v k⟫_ℂ) *ᵥ x)
        = ⟪∑ j, x j • v j, ∑ k, x k • v k⟫_ℂ := by
      rw [sum_inner]
      simp only [inner_sum, inner_smul_left, inner_smul_right, dotProduct,
        Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hq]
    have hnn : (0 : ℝ) ≤ ‖∑ j, x j • v j‖ ^ 2 := by positivity
    have hre : ⟪∑ j, x j • v j, ∑ k, x k • v k⟫_ℂ
        = ((‖∑ j, x j • v j‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      exact rfl
    rw [hre]
    exact Complex.zero_le_real.mpr hnn

/-- The Gram matrix in the concrete `Gᴴ G` form, for reference:
`Matrix.posSemidef_conjTranspose_mul_self`. -/
theorem posSemidef_conjTranspose_mul_self' {m : Type*} [Fintype m]
    (G : Matrix m n ℂ) : (Gᴴ * G).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self G

/-- **Part (f), combination.**  A finite nonnegatively weighted sum of positive
semidefinite matrices is positive semidefinite.

Only the **finite** sum is treated.  The archimedean term of the verdict is an
integral `∫₀^L a(t) D(t) dt`; that term is deliberately out of scope for this
file and is not covered by this lemma. -/
theorem posSemidef_weighted_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (M : ι → Matrix n n ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hM : ∀ i ∈ s, (M i).PosSemidef) :
    (∑ i ∈ s, (w i : ℂ) • M i).PosSemidef :=
  Matrix.posSemidef_sum s fun i hi =>
    (hM i hi).smul (Complex.zero_le_real.mpr (hw i hi))

/-- **Part (f), assembly.**  The Weil source matrix
`Γ = Σᵢ wᵢ D(tᵢ) + 2αα*` with `wᵢ ≥ 0` and each `D(tᵢ) ⪰ 0` is positive
semidefinite.

Again: this is the finite-sum surrogate of the verdict's `Γ`; the integral
term of the true `Γ` is not represented. -/
theorem weilGamma_posSemidef {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix n n ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hD : ∀ i ∈ s, (D i).PosSemidef) (α : n → ℂ) :
    ((∑ i ∈ s, (w i : ℂ) • D i) + (2 : ℂ) • rankOneStar α).PosSemidef :=
  (posSemidef_weighted_sum s w D hw hD).add
    ((rankOneStar_posSemidef α).smul (Complex.zero_le_real (x := 2) |>.mpr (by norm_num)))

/-! ## 9. The judge's head (2), packaged -/

/-- **Judge's head (2): `weil_translation_gram_minus_shift`.**

For a positive semidefinite `Γ`, a real `c_L` and a vector `β`, with
`K = Γ − c_L·I − 2ββ*`:

* (a) `c*Kc = c*Γc − c_L‖c‖² − 2|β*c|²` for every `c`;
* (b) `K + c_L·I + 2ββ* ⪰ 0`, unconditionally;
* (c) `Re(c*Kc) ≥ −(c_L + 2‖β‖²)‖c‖²`, i.e. `λ_min(K) ≥ −(c_L + 2‖β‖²)`.

Nothing here asserts `K ⪰ 0`; `weilShiftMatrix_plant` shows the inference from
(b) to `K ⪰ 0` is false, and `weilShiftMatrix_posSemidef_iff` shows what would
have to be proved instead. -/
theorem weil_translation_gram_minus_shift {Γ : Matrix n n ℂ} (hΓ : Γ.PosSemidef)
    (cL : ℝ) (β : n → ℂ) :
    (∀ c : n → ℂ, star c ⬝ᵥ (weilShiftMatrix Γ cL β *ᵥ c)
        = star c ⬝ᵥ (Γ *ᵥ c) - (cL : ℂ) * (star c ⬝ᵥ c)
          - 2 * (conj (star β ⬝ᵥ c) * (star β ⬝ᵥ c)))
      ∧ (weilShiftMatrix Γ cL β + (cL : ℂ) • (1 : Matrix n n ℂ)
          + (2 : ℂ) • rankOneStar β).PosSemidef
      ∧ (∀ c : n → ℂ, -((cL + 2 * ∑ i, ‖β i‖ ^ 2) * ∑ i, ‖c i‖ ^ 2)
          ≤ (star c ⬝ᵥ (weilShiftMatrix Γ cL β *ᵥ c)).re) :=
  ⟨fun c => weilShiftMatrix_quadForm Γ cL β c,
    weilShiftMatrix_add_shift_posSemidef hΓ cL β,
    fun c => weilShiftMatrix_re_lower_bound hΓ cL β c⟩

end Q3.RouteB
