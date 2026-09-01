import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementSpectral
import Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
import Q3.Proofs.RouteB.CenteredXiZeroNonzero
import Q3.Proofs.RouteB.CompactEvaluationRateTransfer

set_option linter.mathlibStandardSet false

open Complex Filter Topology Matrix
open scoped Topology BigOperators ComplexOrder

noncomputable section
namespace Q3.RouteB

open CanonicalRHRoute

/-!
# Literal CCM cofinal residual/floor envelope and transform tail

This file instantiates the cofinal ground-to-trial tracking architecture on the
literal selected D0/CCM source objects.  In particular:

* the finite operator is `D0Pstar.sourceCCMFiniteMatrix`;
* the projected source trial is `D0Pstar.sourceCCMComplexRow`;
* the residual is `D0Pstar.sourceCCMFiniteResidual`;
* the positive number `beta` is tied to that same operator and trial by
  `sourceCCMComplexTrialComplementFloor`;
* the analytic transform is the source-ordered Proposition-59 transform;
* the comparison family is the production `selectedFamily` on the existing
  `parent (extract k)` schedule;
* the final tail is the literal difference from `selectedMuntzApproximation`.

No arbitrary error family, arbitrary decomposition identity, independently
chosen schedule, or free spectral gap is present.  The theorem is still
conditional: it does not construct the complement floor, prove the compact
kernel-rate budget, or prove the literal selected-family/Müntz tail decay.
-/

/-- Source-ordered coefficient transport from the CCM carrier `-N, ..., N` to
its literal Proposition-59 integer labels.  Unlike the Lagrange-polynomial
transport, this definition does not reverse the mode label. -/
noncomputable def sourceOrderedCCMCoefficient
    (N : ℕ) (q : CCMModeFinite N → ℂ) (n : ℤ) : ℂ :=
  if hn : n ∈ Finset.Icc (-(N : ℤ)) N then
    q ((ccmModeFiniteEquivIcc N).symm ⟨n, hn⟩)
  else 0

@[simp] theorem sourceOrderedCCMCoefficient_mode
    (N : ℕ) (q : CCMModeFinite N → ℂ) (j : CCMModeFinite N) :
    sourceOrderedCCMCoefficient N q (ccmModeFinite N j) = q j := by
  have hj : ccmModeFinite N j ∈ Finset.Icc (-(N : ℤ)) N :=
    Finset.mem_Icc.mpr (ccmModeFinite_range N j)
  rw [sourceOrderedCCMCoefficient, dif_pos hj]
  let e := ccmModeFiniteEquivIcc N
  have hsub :
      (⟨ccmModeFinite N j, hj⟩ :
        {n : ℤ // n ∈ Finset.Icc (-(N : ℤ)) N}) = e j := by
    apply Subtype.ext
    rfl
  change q (e.symm _) = q j
  rw [hsub, e.symm_apply_apply]

/-- The exact source-oriented raw Proposition-59 transform.  The argument
reflection `-z` is the production `rawFplus` convention. -/
noncomputable def sourceOrderedCCMRawTransform
    (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) (z : ℂ) : ℂ :=
  proposition59RawTransform L (Finset.Icc (-(N : ℤ)) N)
    (sourceOrderedCCMCoefficient N q) (-z)

/-- The source-ordered finite Proposition-59 transform is entire. -/
theorem differentiable_sourceOrderedCCMRawTransform
    (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) :
    Differentiable ℂ (sourceOrderedCCMRawTransform L N q) := by
  unfold sourceOrderedCCMRawTransform
  exact
    (differentiable_proposition59RawTransform L
      (Finset.Icc (-(N : ℤ)) N) (sourceOrderedCCMCoefficient N q)).comp
      differentiable_neg

/-- Exact Euclidean size of the source-ordered Proposition-59 kernel row. -/
noncomputable def sourceOrderedCCMKernelL2
    (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  ‖((Real.sqrt L : ℂ)⁻¹)‖ *
    Real.sqrt
      (∑ j : CCMModeFinite N,
        Complex.normSq
          (proposition59PoleKernel L (ccmModeFinite N j) (-z)))

/-- The exact source-kernel envelope is nonnegative. -/
theorem sourceOrderedCCMKernelL2_nonneg
    (L : ℝ) (N : ℕ) (z : ℂ) :
    0 ≤ sourceOrderedCCMKernelL2 L N z := by
  exact mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Exact finite mode-sum expansion in source order. -/
theorem sourceOrderedCCMRawTransform_eq_mode_sum
    (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) (z : ℂ) :
    sourceOrderedCCMRawTransform L N q z =
      ((Real.sqrt L : ℂ)⁻¹) *
        ∑ j, q j *
          proposition59PoleKernel L (ccmModeFinite N j) (-z) := by
  classical
  unfold sourceOrderedCCMRawTransform proposition59RawTransform
  congr 1
  let e := ccmModeFiniteEquivIcc N
  calc
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        sourceOrderedCCMCoefficient N q n *
          proposition59PoleKernel L n (-z)) =
        ∑ n : {n : ℤ // n ∈ Finset.Icc (-(N : ℤ)) N},
          sourceOrderedCCMCoefficient N q n.1 *
            proposition59PoleKernel L n.1 (-z) := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (Finset.Icc (-(N : ℤ)) N)
          (fun n => sourceOrderedCCMCoefficient N q n *
            proposition59PoleKernel L n (-z))).symm
    _ = ∑ j : CCMModeFinite N,
          sourceOrderedCCMCoefficient N q (e j).1 *
            proposition59PoleKernel L (e j).1 (-z) := by
      simpa using (e.sum_comp
        (fun n => sourceOrderedCCMCoefficient N q n.1 *
          proposition59PoleKernel L n.1 (-z))).symm
    _ = ∑ j, q j *
          proposition59PoleKernel L (ccmModeFinite N j) (-z) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [e, ccmModeFiniteEquivIcc]

private theorem sourceOrderedCCM_mode_sum_cauchy_schwarz
    (L : ℝ) (N : ℕ) (w : CCMModeFinite N → ℂ) (z : ℂ) :
    ‖∑ j, w j * proposition59PoleKernel L (ccmModeFinite N j) (-z)‖ ≤
      Real.sqrt (∑ j, Complex.normSq (w j)) *
        Real.sqrt
          (∑ j,
            Complex.normSq
              (proposition59PoleKernel L (ccmModeFinite N j) (-z))) := by
  classical
  calc
    ‖∑ j, w j * proposition59PoleKernel L (ccmModeFinite N j) (-z)‖ ≤
        ∑ j, ‖w j * proposition59PoleKernel L (ccmModeFinite N j) (-z)‖ :=
      norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖proposition59PoleKernel L (ccmModeFinite N j) (-z)‖ := by
      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    _ ≤ Real.sqrt (∑ j, ‖w j‖ ^ 2) *
          Real.sqrt
            (∑ j,
              ‖proposition59PoleKernel L (ccmModeFinite N j) (-z)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ j, Complex.normSq (w j)) *
          Real.sqrt
            (∑ j,
              Complex.normSq
                (proposition59PoleKernel L (ccmModeFinite N j) (-z))) := by
      simp [Complex.normSq_eq_norm_sq]

private theorem euclidean_inner_toLp_eq_star_dotProduct
    {ι : Type*} [Fintype ι]
    (u v : ι → ℂ) :
    inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = star u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

private theorem euclidean_norm_sq_toLp_eq_star_dotProduct_re
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ) :
    ‖WithLp.toLp 2 u‖ ^ 2 = (star u ⬝ᵥ u).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),
    euclidean_inner_toLp_eq_star_dotProduct]
  rfl

/-- Exact squared-distance identity for two unit complex coefficient rows. -/
private theorem complex_unit_projection_error_eq_sum_normSq
    {ι : Type*} [Fintype ι]
    (xi q : ι → ℂ)
    (hxi : star xi ⬝ᵥ xi = 1)
    (hq : star q ⬝ᵥ q = 1) :
    1 - Complex.normSq (star xi ⬝ᵥ q) =
      ∑ j,
        Complex.normSq
          (q j - (star xi ⬝ᵥ q) * xi j) := by
  let c : ℂ := star xi ⬝ᵥ q
  let x : ι → ℂ := q - c • xi
  let x₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  have hxi_x : star xi ⬝ᵥ x = 0 := by
    simp [x, c, dotProduct_sub, dotProduct_smul, hxi]
  have hq_decomp : c • xi + x = q := by
    simp [x]
  have hcxi_orth_x :
      inner ℂ (WithLp.toLp 2 (c • xi)) (WithLp.toLp 2 x) = 0 := by
    rw [euclidean_inner_toLp_eq_star_dotProduct]
    simp [hxi_x]
  have hq_pythagoras :
      ‖WithLp.toLp 2 q‖ ^ 2 =
        ‖WithLp.toLp 2 (c • xi)‖ ^ 2 + ‖x₂‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (WithLp.toLp 2 (c • xi)) (WithLp.toLp 2 x) hcxi_orth_x
    have hq_decomp₂ :
        WithLp.toLp 2 q =
          WithLp.toLp 2 (c • xi) + WithLp.toLp 2 x := by
      ext j
      exact congrFun hq_decomp.symm j
    rw [← hq_decomp₂] at h
    simpa [x₂, pow_two] using h
  have hq_norm_sq : ‖WithLp.toLp 2 q‖ ^ 2 = 1 := by
    rw [euclidean_norm_sq_toLp_eq_star_dotProduct_re]
    simpa using congrArg Complex.re hq
  have hxi_norm_sq : ‖WithLp.toLp 2 xi‖ ^ 2 = 1 := by
    rw [euclidean_norm_sq_toLp_eq_star_dotProduct_re]
    simpa using congrArg Complex.re hxi
  have hcxi_norm_sq :
      ‖WithLp.toLp 2 (c • xi)‖ ^ 2 = Complex.normSq c := by
    change ‖c • (WithLp.toLp 2 xi)‖ ^ 2 = Complex.normSq c
    rw [norm_smul, mul_pow, hxi_norm_sq, mul_one, Complex.sq_norm]
  have hdefect : 1 - Complex.normSq c = ‖x₂‖ ^ 2 := by
    rw [hq_norm_sq, hcxi_norm_sq] at hq_pythagoras
    linarith
  calc
    1 - Complex.normSq (star xi ⬝ᵥ q) = ‖x₂‖ ^ 2 := by
      simpa [c] using hdefect
    _ = (star x ⬝ᵥ x).re := by
      simpa [x₂] using euclidean_norm_sq_toLp_eq_star_dotProduct_re x
    _ = ∑ j, Complex.normSq (x j) := by
      have hxsum :
          star x ⬝ᵥ x =
            ((∑ j, Complex.normSq (x j) : ℝ) : ℂ) := by
        unfold dotProduct
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro j _
        simpa [Complex.normSq_eq_conj_mul_self]
      rw [hxsum]
      simp
    _ = ∑ j,
          Complex.normSq
            (q j - (star xi ⬝ᵥ q) * xi j) := by
      simp [x, c]

/-- The source-oriented P59 transform converts exact projective coefficient
error into a pointwise analytic error with no realification and no surrogate
row. -/
theorem sourceOrderedCCMRawTransform_sub_projection_le
    (L : ℝ) (N : ℕ)
    (xi q : CCMModeFinite N → ℂ)
    (hxi : star xi ⬝ᵥ xi = 1)
    (hq : star q ⬝ᵥ q = 1)
    (z : ℂ) :
    ‖sourceOrderedCCMRawTransform L N q z -
        (star xi ⬝ᵥ q) * sourceOrderedCCMRawTransform L N xi z‖ ≤
      sourceOrderedCCMKernelL2 L N z *
        Real.sqrt (1 - Complex.normSq (star xi ⬝ᵥ q)) := by
  classical
  let c : ℂ := star xi ⬝ᵥ q
  let w : CCMModeFinite N → ℂ := fun j => q j - c * xi j
  have herr :
      1 - Complex.normSq c = ∑ j, Complex.normSq (w j) := by
    simpa [c, w] using complex_unit_projection_error_eq_sum_normSq xi q hxi hq
  have hsplit :
      sourceOrderedCCMRawTransform L N q z -
          c * sourceOrderedCCMRawTransform L N xi z =
        ((Real.sqrt L : ℂ)⁻¹) *
          ∑ j, w j * proposition59PoleKernel L (ccmModeFinite N j) (-z) := by
    rw [sourceOrderedCCMRawTransform_eq_mode_sum,
      sourceOrderedCCMRawTransform_eq_mode_sum]
    have hsum :
        (∑ j, w j * proposition59PoleKernel L (ccmModeFinite N j) (-z)) =
          (∑ j, q j * proposition59PoleKernel L (ccmModeFinite N j) (-z)) -
            c * ∑ j, xi j *
              proposition59PoleKernel L (ccmModeFinite N j) (-z) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [w, sub_mul, mul_assoc]
    rw [hsum]
    ring
  rw [hsplit, norm_mul, herr]
  have hcs := sourceOrderedCCM_mode_sum_cauchy_schwarz L N w z
  have hnonneg : (0 : ℝ) ≤ ‖((Real.sqrt L : ℂ)⁻¹)‖ := norm_nonneg _
  calc
    ‖((Real.sqrt L : ℂ)⁻¹)‖ *
        ‖∑ j, w j * proposition59PoleKernel L (ccmModeFinite N j) (-z)‖ ≤
        ‖((Real.sqrt L : ℂ)⁻¹)‖ *
          (Real.sqrt (∑ j, Complex.normSq (w j)) *
            Real.sqrt
              (∑ j,
                Complex.normSq
                  (proposition59PoleKernel L (ccmModeFinite N j) (-z)))) := by
      exact mul_le_mul_of_nonneg_left hcs hnonneg
    _ = sourceOrderedCCMKernelL2 L N z *
          Real.sqrt (∑ j, Complex.normSq (w j)) := by
      rw [sourceOrderedCCMKernelL2]
      ring

/-- On the literal source row, the source-ordered transform is exactly the raw
production transform; no coordinate, carrier, or normalization crosswalk is
left implicit. -/
theorem sourceOrderedCCMRawTransform_sourceRow_eq_rawFplus
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) (z : ℂ) :
    sourceOrderedCCMRawTransform
        (D0Pstar.logLength i) i.N (D0Pstar.sourceCCMComplexRow S i) z =
      D0Pstar.rawFplus S.canonical.kTrial i z := by
  classical
  unfold sourceOrderedCCMRawTransform D0Pstar.rawFplus
  unfold proposition59RawTransform
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnicc : n ∈ Finset.Icc (-(i.N : ℤ)) i.N := by
    simpa [D0Pstar.modeSet] using hn
  rw [sourceOrderedCCMCoefficient, dif_pos hnicc]
  unfold D0Pstar.sourceCCMComplexRow
  have hmode :
      ccmModeFinite i.N
          ((ccmModeFiniteEquivIcc i.N).symm
            (⟨n, hnicc⟩ :
              {a : ℤ // a ∈ Finset.Icc (-(i.N : ℤ)) i.N})) = n := by
    have h := congrArg Subtype.val
      ((ccmModeFiniteEquivIcc i.N).apply_symm_apply
        (⟨n, hnicc⟩ :
          {a : ℤ // a ∈ Finset.Icc (-(i.N : ℤ)) i.N}))
    change ccmModeFinite i.N
        ((ccmModeFiniteEquivIcc i.N).symm
          (⟨n, hnicc⟩ :
            {a : ℤ // a ∈ Finset.Icc (-(i.N : ℤ)) i.N})) = n at h
    exact h
  rw [hmode]

/-- Exact production-family crosswalk at the selected D0/CCM index. -/
theorem selectedFamily_eq_centered_sourceOrderedCCMRawTransform
    (S : D0Pstar.ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    CanonicalRHRoute.selectedFamily
        (D0Pstar.canonicalApproximation S.canonical) k z =
      D0Pstar.selectedCenteringFactor S k *
        sourceOrderedCCMRawTransform
          (D0Pstar.logLength (D0Pstar.selectedPairIndex S k))
          (D0Pstar.selectedPairIndex S k).N
          (D0Pstar.sourceCCMComplexRow S (D0Pstar.selectedPairIndex S k)) z := by
  calc
    CanonicalRHRoute.selectedFamily
        (D0Pstar.canonicalApproximation S.canonical) k z =
      D0Pstar.selectedCenteringFactor S k *
        D0Pstar.selectedRawTransformCoordinate S k (-z) := by
          simpa using
            D0Pstar.selectedFamily_neg_eq_centeredRawCoordinate S k (-z)
    _ = D0Pstar.selectedCenteringFactor S k *
        D0Pstar.rawFplus S.canonical.kTrial
          (D0Pstar.selectedPairIndex S k) z := by
          simp [D0Pstar.selectedRawTransformCoordinate]
    _ = D0Pstar.selectedCenteringFactor S k *
        sourceOrderedCCMRawTransform
          (D0Pstar.logLength (D0Pstar.selectedPairIndex S k))
          (D0Pstar.selectedPairIndex S k).N
          (D0Pstar.sourceCCMComplexRow S (D0Pstar.selectedPairIndex S k)) z := by
          rw [sourceOrderedCCMRawTransform_sourceRow_eq_rawFplus]

/-- The chosen literal finite CCM minimum eigenvalue supplied by the exact
trial-complement floor. -/
noncomputable def selectedCCMGroundEigenvalue
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ) : ℝ :=
  Classical.choose
    (sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor
      S (D0Pstar.selectedPairIndex S k) (beta k) (hfloor k))

/-- The chosen literal unit ground vector supplied by the same floor. -/
noncomputable def selectedCCMGroundVector
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ) :
    CCMModeFinite (D0Pstar.selectedPairIndex S k).N → ℂ :=
  Classical.choose
    (Classical.choose_spec
      (sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor
        S (D0Pstar.selectedPairIndex S k) (beta k) (hfloor k)))

/-- The chosen ground vector retains both the literal ground-gap package and
the exact residual-over-floor projective estimate. -/
theorem selectedCCMGroundVector_spec
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ) :
    complexHermitianGroundGapAtLeast
        (D0Pstar.sourceCCMFiniteMatrix (D0Pstar.selectedPairIndex S k))
        (selectedCCMGroundEigenvalue S beta hfloor k)
        (beta k)
        (selectedCCMGroundVector S beta hfloor k) ∧
      1 - Complex.normSq
          (star (selectedCCMGroundVector S beta hfloor k) ⬝ᵥ
            D0Pstar.sourceCCMComplexRow S (D0Pstar.selectedPairIndex S k)) ≤
        (star (D0Pstar.sourceCCMFiniteResidual S
                (D0Pstar.selectedPairIndex S k)) ⬝ᵥ
              D0Pstar.sourceCCMFiniteResidual S
                (D0Pstar.selectedPairIndex S k)).re /
          beta k ^ 2 := by
  exact Classical.choose_spec
    (Classical.choose_spec
      (sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor
        S (D0Pstar.selectedPairIndex S k) (beta k) (hfloor k)))

/-- Exact projective coefficient of the literal source row on the chosen ground
line. -/
noncomputable def selectedCCMGroundOverlap
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ) : ℂ :=
  star (selectedCCMGroundVector S beta hfloor k) ⬝ᵥ
    D0Pstar.sourceCCMComplexRow S (D0Pstar.selectedPairIndex S k)

/-- Literal residual energy divided by the squared literal complement floor. -/
noncomputable def selectedCCMResidualFloorRatio
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (k : ℕ) : ℝ :=
  (star (D0Pstar.sourceCCMFiniteResidual S
          (D0Pstar.selectedPairIndex S k)) ⬝ᵥ
        D0Pstar.sourceCCMFiniteResidual S
          (D0Pstar.selectedPairIndex S k)).re /
    beta k ^ 2

/-- The exact nonzero scalar multiplying the selected finite ground transform. -/
noncomputable def selectedCCMGroundScale
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ) : ℂ :=
  D0Pstar.selectedCenteringFactor S k *
    selectedCCMGroundOverlap S beta hfloor k

/-- The exact selected finite-ground Proposition-59 transform. -/
noncomputable def selectedCCMGroundTransform
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ) (z : ℂ) : ℂ :=
  selectedCCMGroundScale S beta hfloor k *
    sourceOrderedCCMRawTransform
      (D0Pstar.logLength (D0Pstar.selectedPairIndex S k))
      (D0Pstar.selectedPairIndex S k).N
      (selectedCCMGroundVector S beta hfloor k) z

private theorem selectedCenteringFactor_ne_zero
    (S : D0Pstar.ProlateCanonicalSourceData) (k : ℕ) :
    D0Pstar.selectedCenteringFactor S k ≠ 0 := by
  unfold D0Pstar.selectedCenteringFactor
  exact div_ne_zero centeredXi_zero_ne_zero (by
    simpa [D0Pstar.selectedPairIndex, D0Pstar.selectedCentralIndex] using
      D0Pstar.rawFplus_zero_ne S.canonical.kTrial
        (D0Pstar.selectedCentralIndex S k))

/-- A strict residual/floor ratio below one forces the exact projective ground
coefficient to be nonzero. -/
theorem selectedCCMGroundOverlap_ne_zero_of_ratio_lt_one
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ)
    (hratio : selectedCCMResidualFloorRatio S beta k < 1) :
    selectedCCMGroundOverlap S beta hfloor k ≠ 0 := by
  have htracking := (selectedCCMGroundVector_spec S beta hfloor k).2
  have hpos :
      0 < Complex.normSq (selectedCCMGroundOverlap S beta hfloor k) := by
    unfold selectedCCMResidualFloorRatio selectedCCMGroundOverlap at *
    linarith
  exact Complex.normSq_pos.mp hpos

/-- The post-centering finite-ground scaling is genuinely nonzero when the
literal residual/floor ratio is strictly below one. -/
theorem selectedCCMGroundScale_ne_zero_of_ratio_lt_one
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ)
    (hratio : selectedCCMResidualFloorRatio S beta k < 1) :
    selectedCCMGroundScale S beta hfloor k ≠ 0 :=
  mul_ne_zero (selectedCenteringFactor_ne_zero S k)
    (selectedCCMGroundOverlap_ne_zero_of_ratio_lt_one
      S beta hfloor k hratio)

/-- Exact source-facing pointwise transform estimate.  Every object in the
right-hand side is computed from the same selected CCM cell and the same
literal complement floor. -/
theorem selectedCCMGroundTransform_sub_selectedFamily_le
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (k : ℕ) (z : ℂ) :
    ‖selectedCCMGroundTransform S beta hfloor k z -
        CanonicalRHRoute.selectedFamily
          (D0Pstar.canonicalApproximation S.canonical) k z‖ ≤
      ‖D0Pstar.selectedCenteringFactor S k‖ *
        sourceOrderedCCMKernelL2
          (D0Pstar.logLength (D0Pstar.selectedPairIndex S k))
          (D0Pstar.selectedPairIndex S k).N z *
        Real.sqrt (selectedCCMResidualFloorRatio S beta k) := by
  let i := D0Pstar.selectedPairIndex S k
  let xi := selectedCCMGroundVector S beta hfloor k
  let q := D0Pstar.sourceCCMComplexRow S i
  let c : ℂ := star xi ⬝ᵥ q
  have hxi : star xi ⬝ᵥ xi = 1 :=
    (selectedCCMGroundVector_spec S beta hfloor k).1.1
  have hq : star q ⬝ᵥ q = 1 := by
    simpa [q, i] using D0Pstar.sourceCCMComplexRow_unit S i
  have hraw := sourceOrderedCCMRawTransform_sub_projection_le
    (D0Pstar.logLength i) i.N xi q hxi hq z
  have hdefect := (selectedCCMGroundVector_spec S beta hfloor k).2
  have hsqrt :
      Real.sqrt (1 - Complex.normSq c) ≤
        Real.sqrt (selectedCCMResidualFloorRatio S beta k) := by
    apply Real.sqrt_le_sqrt
    simpa [c, q, xi, i, selectedCCMResidualFloorRatio] using hdefect
  have hraw' :
      ‖c * sourceOrderedCCMRawTransform (D0Pstar.logLength i) i.N xi z -
          sourceOrderedCCMRawTransform (D0Pstar.logLength i) i.N q z‖ ≤
        sourceOrderedCCMKernelL2 (D0Pstar.logLength i) i.N z *
          Real.sqrt (selectedCCMResidualFloorRatio S beta k) := by
    rw [norm_sub_rev]
    exact hraw.trans
      (mul_le_mul_of_nonneg_left hsqrt
        (sourceOrderedCCMKernelL2_nonneg _ _ _))
  rw [selectedCCMGroundTransform, selectedCCMGroundScale,
    selectedCCMGroundOverlap]
  rw [selectedFamily_eq_centered_sourceOrderedCCMRawTransform]
  simp only [mul_assoc]
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left hraw' (norm_nonneg _)

/-- Literal CCM cofinal composition.  The same source-locked operator, trial,
residual, floor, transform, selected schedule and Müntz target occur throughout.
The conclusion also exports eventual nondegeneracy of the actual finite-ground
normalization; nondegeneracy is not a dead premise. -/
theorem literalCCMCofinalResidualFloorEnvelopeAndTransformTail
    (S : D0Pstar.ProlateCanonicalSourceData)
    (beta : ℕ → ℝ)
    (hfloor : ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (beta k))
    (U : Set ℂ) (hU : IsOpen U)
    (hratioStrict :
      ∀ᶠ k in atTop, selectedCCMResidualFloorRatio S beta k < 1)
    (hcompactBudget :
      ∀ K ⊆ U, IsCompact K →
        ∃ C : ℕ → ℝ,
          Tendsto
              (fun k => C k *
                Real.sqrt (selectedCCMResidualFloorRatio S beta k))
              atTop (𝓝 0) ∧
            ∀ᶠ k in atTop,
              ∀ z ∈ K,
                ‖D0Pstar.selectedCenteringFactor S k‖ *
                    sourceOrderedCCMKernelL2
                      (D0Pstar.logLength (D0Pstar.selectedPairIndex S k))
                      (D0Pstar.selectedPairIndex S k).N z ≤
                  C k)
    (htail :
      TendstoLocallyUniformlyOn
        (fun k z =>
          CanonicalRHRoute.selectedFamily
              (D0Pstar.canonicalApproximation S.canonical) k z -
            D0Pstar.selectedMuntzApproximation S k z)
        (fun _ => 0) atTop U) :
    TendstoLocallyUniformlyOn
      (fun k z =>
        selectedCCMGroundTransform S beta hfloor k z -
          D0Pstar.selectedMuntzApproximation S k z)
      (fun _ => 0) atTop U ∧
    ∀ᶠ k in atTop, selectedCCMGroundScale S beta hfloor k ≠ 0 := by
  constructor
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at htail ⊢
    intro K hKU hK
    obtain ⟨C, hrate, hCbound⟩ := hcompactBudget K hKU hK
    have htracking :
        TendstoUniformlyOn
          (fun k z =>
            selectedCCMGroundTransform S beta hfloor k z -
              CanonicalRHRoute.selectedFamily
                (D0Pstar.canonicalApproximation S.canonical) k z)
          (fun _ => 0) atTop K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro epsilon hepsilon
      have hsmall :
          ∀ᶠ k in atTop,
            C k * Real.sqrt (selectedCCMResidualFloorRatio S beta k) <
              epsilon :=
        (tendsto_order.1 hrate).2 epsilon hepsilon
      filter_upwards [hsmall, hCbound] with k hk hCk
      intro z hz
      have hpoint :=
        selectedCCMGroundTransform_sub_selectedFamily_le
          S beta hfloor k z
      have hscale :
          ‖D0Pstar.selectedCenteringFactor S k‖ *
                sourceOrderedCCMKernelL2
                  (D0Pstar.logLength (D0Pstar.selectedPairIndex S k))
                  (D0Pstar.selectedPairIndex S k).N z *
              Real.sqrt (selectedCCMResidualFloorRatio S beta k) ≤
            C k * Real.sqrt (selectedCCMResidualFloorRatio S beta k) :=
        mul_le_mul_of_nonneg_right (hCk z hz) (Real.sqrt_nonneg _)
      simpa [dist_eq_norm, norm_sub_rev] using (hpoint.trans hscale).trans_lt hk
    have hsum := htracking.add (htail K hKU hK)
    have hsum0 :
        TendstoUniformlyOn
          ((fun k z =>
              selectedCCMGroundTransform S beta hfloor k z -
                CanonicalRHRoute.selectedFamily
                  (D0Pstar.canonicalApproximation S.canonical) k z) +
            fun k z =>
              CanonicalRHRoute.selectedFamily
                  (D0Pstar.canonicalApproximation S.canonical) k z -
                D0Pstar.selectedMuntzApproximation S k z)
          (fun _ => 0) atTop K := by
      exact hsum.congr_right (by
        intro _ _
        simp)
    refine hsum0.congr
      (Filter.Eventually.of_forall fun k z _ => ?_)
    simp only [Pi.add_apply]
    abel
  · filter_upwards [hratioStrict] with k hk
    exact selectedCCMGroundScale_ne_zero_of_ratio_lt_one
      S beta hfloor k hk

/-! ### Mandatory strictness plant -/

def goal058NormalizerCollapseXi : Fin 2 → ℂ := ![1, 0]
def goal058NormalizerCollapseQ : Fin 2 → ℂ := ![0, 1]

theorem goal058NormalizerCollapseXi_unit :
    star goal058NormalizerCollapseXi ⬝ᵥ goal058NormalizerCollapseXi = 1 := by
  simp [goal058NormalizerCollapseXi, dotProduct, Fin.sum_univ_succ]

theorem goal058NormalizerCollapseQ_unit :
    star goal058NormalizerCollapseQ ⬝ᵥ goal058NormalizerCollapseQ = 1 := by
  simp [goal058NormalizerCollapseQ, dotProduct, Fin.sum_univ_succ]

/-- At projective defect exactly one the overlap can vanish.  Therefore the
strict ratio hypothesis `< 1` in the cofinal theorem is load-bearing. -/
theorem goal058NormalizerCollapse_overlap_zero_and_defect_one :
    star goal058NormalizerCollapseXi ⬝ᵥ goal058NormalizerCollapseQ = 0 ∧
      1 - Complex.normSq
          (star goal058NormalizerCollapseXi ⬝ᵥ goal058NormalizerCollapseQ) = 1 := by
  simp [goal058NormalizerCollapseXi, goal058NormalizerCollapseQ,
    dotProduct, Fin.sum_univ_succ]

#print axioms sourceOrderedCCMRawTransform_sourceRow_eq_rawFplus
#print axioms differentiable_sourceOrderedCCMRawTransform
#print axioms selectedCCMGroundTransform_sub_selectedFamily_le
#print axioms literalCCMCofinalResidualFloorEnvelopeAndTransformTail
#print axioms goal058NormalizerCollapse_overlap_zero_and_defect_one

end Q3.RouteB
