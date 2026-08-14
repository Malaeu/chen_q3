import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementFloor
import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementRayleigh
import Q3.Proofs.RouteB.CCMProposition59ComplexTrialResidualTracking
import Q3.Proofs.RouteB.HermitianUnitMinimumEigenpair
import Q3.Proofs.RouteB.H2aPenaltyCoercivity

set_option linter.mathlibStandardSet false

/-!
# Goal 058 spectral consequences of the literal complex trial-complement floor

This file proves the finite-dimensional min--max consequence selected by the
Goal 058 two-front architecture.  Its only quantitative input is the already
fixed literal complement floor.  It does not construct that floor and makes no
cofinal, source-arithmetic, Route-B-promotion, or RH claim.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped ComplexOrder BigOperators

/-- A unit eigenvector at the bottom of a Hermitian matrix, together with a
Rayleigh floor `beta` above it on its Hermitian orthogonal complement. -/
def complexHermitianGroundGapAtLeast
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (epsilon beta : ℝ) (xi : ι → ℂ) : Prop :=
  star xi ⬝ᵥ xi = 1 ∧
    K *ᵥ xi = (epsilon : ℂ) • xi ∧
    (∀ x : ι → ℂ,
      epsilon * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (K *ᵥ x)).re) ∧
    ∀ x : ι → ℂ,
      star xi ⬝ᵥ x = 0 →
      (epsilon + beta) * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (K *ᵥ x)).re

private theorem complexTrialLineProjection_mulVec_local
    {ι : Type*} [Fintype ι]
    (q v : ι → ℂ) :
    complexTrialLineProjection q *ᵥ v = (star q ⬝ᵥ v) • q := by
  ext j
  simp [complexTrialLineProjection, Matrix.mulVec, Matrix.vecMulVec_apply,
    dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem complexTrialLineComplement_mulVec_of_orthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q v : ι → ℂ)
    (hv : star q ⬝ᵥ v = 0) :
    complexTrialLineComplement q *ᵥ v = v := by
  rw [complexTrialLineComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    complexTrialLineProjection_mulVec_local, hv, zero_smul, sub_zero]

private theorem star_dotProduct_complexTrialLineComplement_mulVec_of_orthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q v w : ι → ℂ)
    (hv : star q ⬝ᵥ v = 0) :
    star v ⬝ᵥ (complexTrialLineComplement q *ᵥ w) =
      star v ⬝ᵥ w := by
  have hvq : star v ⬝ᵥ q = 0 := by
    rw [Matrix.star_dotProduct] at hv
    exact star_eq_zero.mp hv
  rw [complexTrialLineComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    complexTrialLineProjection_mulVec_local, dotProduct_sub,
    dotProduct_smul]
  simp [hvq]

private theorem complexTrialComplementFloor_quadratic_of_orthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℝ) (beta : ℝ)
    (hfloor : complexTrialComplementFloor K q (a : ℂ) beta)
    (v : ι → ℂ)
    (hv : star q ⬝ᵥ v = 0) :
    beta * (star v ⬝ᵥ v).re ≤
      (star v ⬝ᵥ ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v)).re := by
  have h := hfloor.2 v
  let Q := complexTrialLineComplement q
  have hQv : Q *ᵥ v = v :=
    complexTrialLineComplement_mulVec_of_orthogonal q v hv
  have hleft :
      star v ⬝ᵥ
          (Q *ᵥ
            ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v)) =
        star v ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v) :=
    star_dotProduct_complexTrialLineComplement_mulVec_of_orthogonal
      q v _ hv
  change beta * (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re ≤
    (star (Q *ᵥ v) ⬝ᵥ
      ((Q *
        (K - (a : ℂ) • (1 : Matrix ι ι ℂ)) * Q) *ᵥ v)).re at h
  rw [hQv, ← Matrix.mulVec_mulVec, hQv, ← Matrix.mulVec_mulVec, hleft] at h
  exact h

private theorem hermitian_unit_trialLine_floor_separates_orthogonal_eigenvectors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a beta epsilon : ℝ)
    (xi : ι → ℂ)
    (hbeta : 0 < beta)
    (hfloor : complexTrialComplementFloor K q (a : ℂ) beta)
    (hxi : H2aPenalty.GEig K 1 epsilon xi)
    (hepsilon : epsilon ≤ a)
    (mu : ℝ) (y : ι → ℂ)
    (hy : H2aPenalty.GEig K 1 mu y)
    (hxy : star xi ⬝ᵥ y = 0)
    (hyx : star y ⬝ᵥ xi = 0) :
    a + beta ≤ mu := by
  have hxi_pos : 0 < (star xi ⬝ᵥ xi).re := by
    have hne := hxi.1
    simpa [Complex.normSq, dotProduct] using
      (show 0 < ∑ i, Complex.normSq (xi i) by
        exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) <|
          let ⟨i, hi⟩ := Function.ne_iff.mp hne
          ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩)
  have hy_pos : 0 < (star y ⬝ᵥ y).re := by
    have hne := hy.1
    simpa [Complex.normSq, dotProduct] using
      (show 0 < ∑ i, Complex.normSq (y i) by
        exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) <|
          let ⟨i, hi⟩ := Function.ne_iff.mp hne
          ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩)
  by_contra hmu_floor
  have hmu_lt : mu < a + beta := lt_of_not_ge hmu_floor
  obtain ⟨s, t, hst, horth⟩ := H2aPenalty.exists_combo_Gorth
    (1 : Matrix ι ι ℂ) q xi y
  let z : ι → ℂ := s • xi + t • y
  have hz_ne : z ≠ 0 := by
    intro hz
    have hzxi := congrArg (fun w => star xi ⬝ᵥ w) hz
    have hzy := congrArg (fun w => star y ⬝ᵥ w) hz
    simp only [z, dotProduct_add, dotProduct_smul, dotProduct_zero,
      hxy, hyx, smul_zero, add_zero, zero_add] at hzxi hzy
    have hs : s = 0 := by
      exact mul_eq_zero.mp (by simpa [smul_eq_mul] using hzxi) |>.resolve_right
        (dotProduct_star_self_eq_zero.not.mpr hxi.1)
    have ht : t = 0 := by
      exact mul_eq_zero.mp (by simpa [smul_eq_mul] using hzy) |>.resolve_right
        (dotProduct_star_self_eq_zero.not.mpr hy.1)
    rcases hst with hsne | htne
    · exact hsne hs
    · exact htne ht
  have hqz : star q ⬝ᵥ z = 0 := by
    simpa [z, Matrix.one_mulVec, dotProduct_add, dotProduct_smul] using horth
  have hbound :=
    complexTrialComplementFloor_quadratic_of_orthogonal
      K q a beta hfloor z hqz
  have hnorm :
      star z ⬝ᵥ z =
        (starRingEnd ℂ s * s) * (star xi ⬝ᵥ xi) +
          (starRingEnd ℂ t * t) * (star y ⬝ᵥ y) := by
    simp only [z, star_add, star_smul, dotProduct_add,
      dotProduct_smul, add_dotProduct, smul_dotProduct, hxy, hyx,
      smul_eq_mul]
    rw [starRingEnd_apply, starRingEnd_apply]
    ring
  have henergy :
      star z ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ z) =
        (starRingEnd ℂ s * s) *
            (((epsilon - a : ℝ) : ℂ) * (star xi ⬝ᵥ xi)) +
          (starRingEnd ℂ t * t) *
            (((mu - a : ℝ) : ℂ) * (star y ⬝ᵥ y)) := by
    have hxK : K *ᵥ xi = (epsilon : ℂ) • xi := by
      simpa using hxi.2
    have hyK : K *ᵥ y = (mu : ℂ) • y := by
      simpa using hy.2
    simp only [z, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hxK, hyK,
      star_add, star_smul, add_dotProduct, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_dotProduct, hxy, hyx, smul_eq_mul]
    push_cast
    rw [starRingEnd_apply, starRingEnd_apply]
    ring
  rw [hnorm, henergy] at hbound
  simp_all +decide
  have hpositive :
      0 < s.re * s.re + s.im * s.im ∨
        0 < t.re * t.re + t.im * t.im := by
    contrapose! hst
    simp_all +decide [Complex.ext_iff]
    exact
      ⟨⟨by nlinarith only [hst.1], by nlinarith only [hst.1]⟩,
        ⟨by nlinarith only [hst.2], by nlinarith only [hst.2]⟩⟩
  rcases hpositive with hp | hp <;>
    nlinarith [mul_pos hp hxi_pos, mul_pos hp hy_pos,
      mul_lt_mul_of_pos_left (show epsilon - a < beta by linarith) hxi_pos,
      mul_lt_mul_of_pos_left (show mu - a < beta by linarith) hy_pos]

/-- Exact codimension-one interlacing consequence: if the compression of
`K-aI` to `q^perp` has floor `beta`, every eigenvalue distinct from a bottom
eigenvalue `epsilon ≤ a` is at least `a+beta`. -/
theorem hermitian_unit_trialLine_floor_separates_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a beta epsilon : ℝ)
    (xi : ι → ℂ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (hbeta : 0 < beta)
    (hfloor : complexTrialComplementFloor K q (a : ℂ) beta)
    (hxi : H2aPenalty.GEig K 1 epsilon xi)
    (hepsilon : epsilon ≤ a) :
    ∀ mu y, H2aPenalty.GEig K 1 mu y → mu ≠ epsilon → a + beta ≤ mu := by
  intro mu y hy hmu
  have hxy : star xi ⬝ᵥ y = 0 := by
    have h := H2aPenalty.geig_Gorth_of_ne hK
      (Matrix.isHermitian_one : (1 : Matrix ι ι ℂ).IsHermitian)
      hxi hy (Ne.symm hmu)
    simpa using h
  have hyx : star y ⬝ᵥ xi = 0 := by
    have h := H2aPenalty.geig_Gorth_of_ne hK
      (Matrix.isHermitian_one : (1 : Matrix ι ι ℂ).IsHermitian)
      hy hxi hmu
    simpa using h
  exact hermitian_unit_trialLine_floor_separates_orthogonal_eigenvectors
    K q a beta epsilon xi hbeta hfloor hxi hepsilon mu y hy hxy hyx

/-- Full finite-dimensional receiver selected by the Goal 058 architecture.

From a positive floor on the complement of the unit trial line, it constructs
a unit bottom eigenvector, proves a Rayleigh gap on its orthogonal complement,
and bounds the trial line's projective defect by the squared residual divided
by `beta^2`.  The floor itself remains an input: this theorem supplies no
literal CCM arithmetic, cofinal schedule, or asymptotic estimate. -/
theorem hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Matrix ι ι ℂ) (q r : ι → ℂ) (a beta : ℝ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (ha : (a : ℂ) = star q ⬝ᵥ (K *ᵥ q))
    (hr : r = K *ᵥ q - (a : ℂ) • q)
    (hfloor : complexTrialComplementFloor K q (a : ℂ) beta) :
    ∃ (epsilon : ℝ) (xi0 : ι → ℂ),
      complexHermitianGroundGapAtLeast K epsilon beta xi0 ∧
      1 - Complex.normSq (star xi0 ⬝ᵥ q) ≤
        (star r ⬝ᵥ r).re / beta ^ 2 := by
  obtain ⟨epsilon, xi0, hxi_unit, hxi_eig, hbottom⟩ :=
    hermitian_exists_unit_minimum_eigenpair K hK
  have hxi_ne : xi0 ≠ 0 := by
    intro hzero
    rw [hzero] at hxi_unit
    norm_num at hxi_unit
  have hxi : H2aPenalty.GEig K 1 epsilon xi0 := by
    refine ⟨hxi_ne, ?_⟩
    simpa using hxi_eig
  have hq_norm : (star q ⬝ᵥ q).re = 1 := by
    rw [hq]
    norm_num
  have hq_energy : (star q ⬝ᵥ (K *ᵥ q)).re = a := by
    rw [← ha]
    norm_num
  have hepsilon : epsilon ≤ a := by
    have h := hbottom q
    rw [hq_norm, hq_energy] at h
    simpa using h
  have hstrong :=
    hermitian_unit_trialLine_complementFloor_gives_orthogonalRayleigh
      K q a beta epsilon xi0 hK hq hfloor.1 hfloor hxi hepsilon hbottom
  have hgap : ∀ x : ι → ℂ,
      star xi0 ⬝ᵥ x = 0 →
      (epsilon + beta) * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (K *ᵥ x)).re := by
    intro x hx
    have hnorm : 0 ≤ (star x ⬝ᵥ x).re := by
      simpa [Complex.normSq, dotProduct] using
        (show 0 ≤ ∑ i, Complex.normSq (x i) from
          Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i))
    calc
      (epsilon + beta) * (star x ⬝ᵥ x).re ≤
          (a + beta) * (star x ⬝ᵥ x).re :=
        mul_le_mul_of_nonneg_right (by linarith) hnorm
      _ ≤ (star x ⬝ᵥ (K *ᵥ x)).re := hstrong x hx
  have htracking :=
    hermitian_unit_eigen_projective_defect_le_residual_sq_div_beta_sq_of_orthogonal_floor
      K xi0 q r epsilon a beta hK hxi_unit hxi_eig hq hr hfloor.1 hstrong
  exact
    ⟨epsilon, xi0,
      ⟨hxi_unit, hxi_eig, hbottom, hgap⟩,
      htracking⟩

/-- Literal finite CCM specialization of the full receiver.  It consumes an
already supplied literal complement floor and introduces no new source
assumption beyond that named input. -/
theorem sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (beta : ℝ)
    (hfloor : sourceCCMComplexTrialComplementFloor S i beta) :
    ∃ (epsilon : ℝ) (xi0 : CCMModeFinite i.N → ℂ),
      complexHermitianGroundGapAtLeast
          (D0Pstar.sourceCCMFiniteMatrix i) epsilon beta xi0 ∧
        1 - Complex.normSq
            (star xi0 ⬝ᵥ D0Pstar.sourceCCMComplexRow S i) ≤
          (star (D0Pstar.sourceCCMFiniteResidual S i) ⬝ᵥ
              D0Pstar.sourceCCMFiniteResidual S i).re / beta ^ 2 := by
  let K : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ :=
    D0Pstar.sourceCCMFiniteMatrix i
  let q : CCMModeFinite i.N → ℂ :=
    D0Pstar.sourceCCMComplexRow S i
  let a : ℝ := D0Pstar.sourceCCMFiniteRayleigh S i
  let r : CCMModeFinite i.N → ℂ :=
    D0Pstar.sourceCCMFiniteResidual S i
  have hK : K.IsHermitian := by
    simpa [K] using D0Pstar.sourceCCMFiniteMatrix_isHermitian i
  have hq : star q ⬝ᵥ q = 1 := by
    simpa [q] using D0Pstar.sourceCCMComplexRow_unit S i
  have ha : (a : ℂ) = star q ⬝ᵥ (K *ᵥ q) := by
    simpa [a, q, K] using D0Pstar.sourceCCMFiniteRayleigh_coe S i
  have hr : r = K *ᵥ q - (a : ℂ) • q := by
    rfl
  have hf : complexTrialComplementFloor K q (a : ℂ) beta := by
    simpa [K, q, a, sourceCCMComplexTrialComplementFloor] using hfloor
  simpa [K, q, r] using
    hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking
      K q r a beta hK hq ha hr hf

#print axioms complexHermitianGroundGapAtLeast
#print axioms hermitian_unit_trialLine_floor_separates_eigenvalues
#print axioms hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking
#print axioms sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor

end Q3.RouteB
