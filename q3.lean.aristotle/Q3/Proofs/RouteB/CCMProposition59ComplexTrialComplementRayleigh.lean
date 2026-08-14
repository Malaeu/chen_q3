import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementFloor
import Q3.Proofs.RouteB.H2aPenaltyCoercivity

set_option linter.mathlibStandardSet false

/-!
# Goal 058: a trial-complement floor gives an orthogonal Rayleigh floor

This file contains only a finite-dimensional generic receiver.  It promotes a
floor on the complement of a unit trial line to a Rayleigh floor on the
orthogonal complement of a supplied bottom eigenvector.  It makes no source,
cofinal, Route-B-promotion, or RH claim.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped ComplexOrder BigOperators

private theorem complexTrialLineProjection_mulVec_rayleigh
    {ι : Type*} [Fintype ι]
    (q v : ι → ℂ) :
    complexTrialLineProjection q *ᵥ v = (star q ⬝ᵥ v) • q := by
  ext j
  simp [complexTrialLineProjection, Matrix.mulVec, Matrix.vecMulVec_apply,
    dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem complexTrialLineComplement_mulVec_of_orthogonal_rayleigh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q v : ι → ℂ)
    (hv : star q ⬝ᵥ v = 0) :
    complexTrialLineComplement q *ᵥ v = v := by
  rw [complexTrialLineComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    complexTrialLineProjection_mulVec_rayleigh, hv, zero_smul, sub_zero]

private theorem star_dotProduct_complexTrialLineComplement_mulVec_of_orthogonal_rayleigh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q v w : ι → ℂ)
    (hv : star q ⬝ᵥ v = 0) :
    star v ⬝ᵥ (complexTrialLineComplement q *ᵥ w) =
      star v ⬝ᵥ w := by
  have hvq : star v ⬝ᵥ q = 0 := by
    rw [Matrix.star_dotProduct] at hv
    exact star_eq_zero.mp hv
  rw [complexTrialLineComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    complexTrialLineProjection_mulVec_rayleigh, dotProduct_sub,
    dotProduct_smul]
  simp [hvq]

private theorem complexTrialComplementFloor_quadratic_of_orthogonal_rayleigh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a beta : ℝ)
    (hfloor : complexTrialComplementFloor K q (a : ℂ) beta)
    (v : ι → ℂ)
    (hv : star q ⬝ᵥ v = 0) :
    beta * (star v ⬝ᵥ v).re ≤
      (star v ⬝ᵥ
        ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v)).re := by
  have h := hfloor.2 v
  let Q := complexTrialLineComplement q
  have hQv : Q *ᵥ v = v :=
    complexTrialLineComplement_mulVec_of_orthogonal_rayleigh q v hv
  have hleft :
      star v ⬝ᵥ
          (Q *ᵥ
            ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v)) =
        star v ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v) :=
    star_dotProduct_complexTrialLineComplement_mulVec_of_orthogonal_rayleigh
      q v _ hv
  change beta * (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re ≤
    (star (Q *ᵥ v) ⬝ᵥ
      ((Q *
        (K - (a : ℂ) • (1 : Matrix ι ι ℂ)) * Q) *ᵥ v)).re at h
  rw [hQv, ← Matrix.mulVec_mulVec, hQv, ← Matrix.mulVec_mulVec, hleft] at h
  exact h

private theorem hermitian_star_dotProduct_mulVec
    {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (u v : ι → ℂ) :
    star u ⬝ᵥ (K *ᵥ v) = star (K *ᵥ u) ⬝ᵥ v := by
  simp +decide [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm]
  rw [Finset.sum_comm]
  congr
  ext i
  congr
  ext j
  rw [← hK.apply]
  simp +decide [mul_comm, mul_left_comm]

/-- A positive complement floor around a unit trial line forces the stronger
`a + beta` Rayleigh floor on the orthogonal complement of any bottom
eigenvector with eigenvalue `epsilon ≤ a`.

The global bottom-Rayleigh hypothesis records that the supplied eigenpair is
actually a ground pair.  The quantitative promotion itself is the explicit
two-plane argument `z = s • xi + x`, with
`s = -⟨q,x⟩ / ⟨q,xi⟩`. -/
theorem hermitian_unit_trialLine_complementFloor_gives_orthogonalRayleigh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a beta epsilon : ℝ)
    (xi : ι → ℂ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (hbeta : 0 < beta)
    (hfloor : complexTrialComplementFloor K q (a : ℂ) beta)
    (hxi : H2aPenalty.GEig K 1 epsilon xi)
    (hepsilon : epsilon ≤ a)
    (hbottom : ∀ v : ι → ℂ,
      epsilon * (star v ⬝ᵥ v).re ≤
        (star v ⬝ᵥ (K *ᵥ v)).re) :
    ∀ x : ι → ℂ,
      star xi ⬝ᵥ x = 0 →
      (a + beta) * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (K *ᵥ x)).re := by
  have hxi_pos : 0 < (star xi ⬝ᵥ xi).re := by
    have hne := hxi.1
    simpa [Complex.normSq, dotProduct] using
      (show 0 < ∑ i, Complex.normSq (xi i) by
        exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) <|
          let ⟨i, hi⟩ := Function.ne_iff.mp hne
          ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩)
  have hqxi : star q ⬝ᵥ xi ≠ 0 := by
    intro horth
    have hbound :=
      complexTrialComplementFloor_quadratic_of_orthogonal_rayleigh
        K q a beta hfloor xi horth
    have henergy :
        (star xi ⬝ᵥ
            ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ xi)).re =
          (epsilon - a) * (star xi ⬝ᵥ xi).re := by
      have hxK : K *ᵥ xi = (epsilon : ℂ) • xi := by
        simpa using hxi.2
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        hxK, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      norm_num
      ring
    rw [henergy] at hbound
    nlinarith
  intro x hxxi
  have hxix : star x ⬝ᵥ xi = 0 := by
    rw [Matrix.star_dotProduct] at hxxi
    exact star_eq_zero.mp hxxi
  let s : ℂ := -(star q ⬝ᵥ x) / (star q ⬝ᵥ xi)
  let z : ι → ℂ := s • xi + x
  have hqz : star q ⬝ᵥ z = 0 := by
    simp only [z, dotProduct_add, dotProduct_smul, s, smul_eq_mul]
    field_simp
    ring
  have hbound :=
    complexTrialComplementFloor_quadratic_of_orthogonal_rayleigh
      K q a beta hfloor z hqz
  have hnorm :
      star z ⬝ᵥ z =
        (starRingEnd ℂ s * s) * (star xi ⬝ᵥ xi) +
          star x ⬝ᵥ x := by
    simp only [z, star_add, star_smul, dotProduct_add,
      dotProduct_smul, add_dotProduct, smul_dotProduct, hxxi, hxix,
      smul_eq_mul]
    rw [starRingEnd_apply]
    ring
  have hxi_shift_x :
      star xi ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ x) = 0 := by
    have hKcross := hermitian_star_dotProduct_mulVec K hK xi x
    have hxK : K *ᵥ xi = (epsilon : ℂ) • xi := by
      simpa using hxi.2
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul]
    rw [hKcross, hxK]
    simp [hxxi, smul_eq_mul]
  have hx_shift_xi :
      star x ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ xi) = 0 := by
    have hxK : K *ᵥ xi = (epsilon : ℂ) • xi := by
      simpa using hxi.2
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hxK, dotProduct_sub, dotProduct_smul]
    simp [hxix, smul_eq_mul]
  have henergy :
      star z ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ z) =
        (starRingEnd ℂ s * s) *
            (((epsilon - a : ℝ) : ℂ) * (star xi ⬝ᵥ xi)) +
          star x ⬝ᵥ
            ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ x) := by
    have hxK : K *ᵥ xi = (epsilon : ℂ) • xi := by
      simpa using hxi.2
    simp only [z, Matrix.mulVec_add, Matrix.mulVec_smul, star_add,
      star_smul, add_dotProduct, dotProduct_add, dotProduct_smul,
      smul_dotProduct, hxi_shift_x, hx_shift_xi, add_zero, smul_eq_mul]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hxK, dotProduct_sub, dotProduct_smul]
    push_cast
    rw [starRingEnd_apply]
    simp only [dotProduct_smul, smul_eq_mul]
    ring
  have hshift_re :
      (star x ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ x)).re =
        (star x ⬝ᵥ (K *ᵥ x)).re - a * (star x ⬝ᵥ x).re := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, Complex.mul_re]
  rw [hnorm, henergy] at hbound
  simp only [Complex.add_re] at hbound
  rw [hshift_re] at hbound
  have hs_nonneg : 0 ≤ s.re * s.re + s.im * s.im := by
    nlinarith [sq_nonneg s.re, sq_nonneg s.im]
  have hxx_nonneg : 0 ≤ (star x ⬝ᵥ x).re := by
    simpa [Complex.normSq, dotProduct] using
      (show 0 ≤ ∑ i, Complex.normSq (x i) from
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i))
  simp_all +decide
  ring_nf at hbound
  have hre_coeff :
      0 ≤ s.re ^ 2 * (star xi ⬝ᵥ xi).re :=
    mul_nonneg (sq_nonneg s.re) (le_of_lt hxi_pos)
  have him_coeff :
      0 ≤ s.im ^ 2 * (star xi ⬝ᵥ xi).re :=
    mul_nonneg (sq_nonneg s.im) (le_of_lt hxi_pos)
  have hre_drop := mul_le_mul_of_nonneg_left hepsilon hre_coeff
  have him_drop := mul_le_mul_of_nonneg_left hepsilon him_coeff
  nlinarith

#print axioms hermitian_unit_trialLine_complementFloor_gives_orthogonalRayleigh

end Q3.RouteB
