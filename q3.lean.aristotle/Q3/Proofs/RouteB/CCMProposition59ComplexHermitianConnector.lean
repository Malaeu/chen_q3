import Q3.Proofs.RouteB.CCMProposition59SourceTrialFeshbachPreflight

set_option linter.mathlibStandardSet false

/-!
# Goal 058 complex Hermitian Proposition-59 connector

The literal CCM source coefficient row is complex and unit; the Proposition-59
transform consumes a real row.  This file removes that object mismatch without
any realification, parity, gap, tracking, or spectral hypothesis: it uses the
exact Hermitian rank-one projection onto the literal complex source line.

For a real row `xi` the scalar `sourceCCMGroundProjectionScalar S i xi` is the
exact Hermitian projection coefficient of `xi` onto the literal complex source
row, and `sourceCCMGroundProjectionErrorSq S i xi` is the exact squared
coefficient-space distance from `xi` to that complex line.  The main theorem
bounds the pointwise difference between the real Proposition-59 transform of
`xi` and the projection-scaled complex source transform by the exact P59 kernel
`L²`-norm times the square root of that projective error.

Nothing here asserts that the projective error is small or that it decays.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- Hermitian rank-one matrix of the complex trial line spanned by `q`. -/
noncomputable def complexTrialLineProjection
    {ι : Type*} (q : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec q (star q)

/-- Exact Hermitian projection coefficient of the real row `xi` onto the
literal complex CCM source line. -/
noncomputable def sourceCCMGroundProjectionScalar
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) : ℂ :=
  star (D0Pstar.sourceCCMComplexRow S i) ⬝ᵥ
    (fun j => (xi j : ℂ))

/-- Exact squared coefficient-space distance from `xi` to the complex source
line. -/
noncomputable def sourceCCMGroundProjectionErrorSq
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) : ℝ :=
  xi ⬝ᵥ xi -
    Complex.normSq (sourceCCMGroundProjectionScalar S i xi)

/-- Exact `L²` size of the finite Proposition-59 pole kernel family, in the
locked coordinate `source mode n → P59 pole -n`. -/
noncomputable def proposition59CCMKernelL2
    (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  ‖((Real.sqrt L : ℂ)⁻¹)‖ *
    Real.sqrt
      (∑ j : CCMModeFinite N,
        Complex.normSq
          (proposition59PoleKernel L (-ccmModeFinite N j) z))

theorem complexTrialLineProjection_isHermitian
    {ι : Type*} (q : ι → ℂ) :
    (complexTrialLineProjection q).IsHermitian := by
  show (complexTrialLineProjection q)ᴴ = complexTrialLineProjection q
  ext i j
  simp [complexTrialLineProjection, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, mul_comm]

theorem complexTrialLineProjection_sq_of_unit
    {ι : Type*} [Fintype ι]
    (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineProjection q * complexTrialLineProjection q =
      complexTrialLineProjection q := by
  rw [complexTrialLineProjection, Matrix.vecMulVec_mul_vecMulVec, hq, one_smul]

/-- Generic Hermitian projective error identity for an arbitrary unit complex
row.  This is a private helper: the public interface always hard-codes the
literal source row. -/
private theorem complexRow_projection_error_identity
    {ι : Type*} [Fintype ι]
    (row : ι → ℂ) (xi : ι → ℝ)
    (hrow : star row ⬝ᵥ row = 1) :
    xi ⬝ᵥ xi -
        Complex.normSq (star row ⬝ᵥ (fun j => (xi j : ℂ))) =
      ∑ j,
        Complex.normSq
          ((xi j : ℂ) -
            (star row ⬝ᵥ (fun j => (xi j : ℂ))) * row j) := by
  classical
  set c : ℂ := star row ⬝ᵥ (fun j => (xi j : ℂ)) with hc
  have hcdef : c = ∑ j, (starRingEnd ℂ) (row j) * (xi j : ℂ) := by
    simp [hc, dotProduct]
  have hrow' : ∑ j, (starRingEnd ℂ) (row j) * row j = 1 := by
    simpa [dotProduct] using hrow
  have hconj : (starRingEnd ℂ) c = ∑ j, row j * (xi j : ℂ) := by
    rw [hcdef, map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp [mul_comm]
  have hxi : ((xi ⬝ᵥ xi : ℝ) : ℂ) = ∑ j, (xi j : ℂ) * (xi j : ℂ) := by
    simp [dotProduct]
  have hterm : ∀ j : ι,
      ((Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ) =
        (xi j : ℂ) * (xi j : ℂ) -
          (starRingEnd ℂ) c * ((xi j : ℂ) * (starRingEnd ℂ) (row j)) -
          c * (row j * (xi j : ℂ)) +
          (c * (starRingEnd ℂ) c) *
            ((starRingEnd ℂ) (row j) * row j) := by
    intro j
    rw [← Complex.mul_conj]
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    ring
  have hcast :
      ((∑ j, Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ) =
        ((xi ⬝ᵥ xi : ℝ) : ℂ) - ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ j, ((Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ)) =
          ∑ j,
            ((xi j : ℂ) * (xi j : ℂ) -
              (starRingEnd ℂ) c * ((xi j : ℂ) * (starRingEnd ℂ) (row j)) -
              c * (row j * (xi j : ℂ)) +
              (c * (starRingEnd ℂ) c) *
                ((starRingEnd ℂ) (row j) * row j)) :=
        Finset.sum_congr rfl fun j _ => hterm j
      _ = (∑ j, (xi j : ℂ) * (xi j : ℂ)) -
            (starRingEnd ℂ) c *
              (∑ j, (xi j : ℂ) * (starRingEnd ℂ) (row j)) -
            c * (∑ j, row j * (xi j : ℂ)) +
            (c * (starRingEnd ℂ) c) *
              (∑ j, (starRingEnd ℂ) (row j) * row j) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
      _ = ((xi ⬝ᵥ xi : ℝ) : ℂ) - ((Complex.normSq c : ℝ) : ℂ) := by
        have hswap : (∑ j, (xi j : ℂ) * (starRingEnd ℂ) (row j)) = c := by
          rw [hcdef]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [hswap, ← hconj, hrow', hxi, ← Complex.mul_conj]
        ring
  exact_mod_cast hcast.symm

/-- The exact projective error of `xi` against the literal complex source line
is the total squared coefficient residual after removing the Hermitian
projection.  No realification or parity input is used. -/
theorem sourceCCMGroundProjectionErrorSq_eq_sum_normSq
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) :
    sourceCCMGroundProjectionErrorSq S i xi =
      ∑ j,
        Complex.normSq
          ((xi j : ℂ) -
            sourceCCMGroundProjectionScalar S i xi *
              D0Pstar.sourceCCMComplexRow S i j) := by
  exact complexRow_projection_error_identity
    (D0Pstar.sourceCCMComplexRow S i) xi
    (D0Pstar.sourceCCMComplexRow_unit S i)

/-- Finite Cauchy-Schwarz for the exact source-locked P59 mode sum. -/
private theorem proposition59CCM_mode_sum_cauchy_schwarz
    (L : ℝ) (N : ℕ) (w : CCMModeFinite N → ℂ) (z : ℂ) :
    ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ ≤
      Real.sqrt (∑ j, Complex.normSq (w j)) *
        Real.sqrt
          (∑ j,
            Complex.normSq
              (proposition59PoleKernel L (-ccmModeFinite N j) z)) := by
  classical
  calc
    ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ ≤
        ∑ j, ‖w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ :=
      norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖proposition59PoleKernel L (-ccmModeFinite N j) z‖ := by
      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    _ ≤ Real.sqrt (∑ j, ‖w j‖ ^ 2) *
          Real.sqrt
            (∑ j,
              ‖proposition59PoleKernel L (-ccmModeFinite N j) z‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ j, Complex.normSq (w j)) *
          Real.sqrt
            (∑ j,
              Complex.normSq
                (proposition59PoleKernel L (-ccmModeFinite N j) z)) := by
      simp [Complex.normSq_eq_norm_sq]

/-- Exact finite Hermitian connector.  The projective error is nonnegative, and
the pointwise difference between the real Proposition-59 transform of `xi` and
the projection-scaled complex source transform is bounded by the exact P59
kernel `L²`-norm times the square root of that error.

The positivity binder `hL` is part of the locked theorem head; the bound is in
fact uniform in `L`, so the proof does not consume it. -/
theorem proposition59CCMTransform_sub_sourceProjection_le
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (L : ℝ) (hL : 0 < L)
    (xi : CCMModeFinite i.N → ℝ) :
    0 ≤ sourceCCMGroundProjectionErrorSq S i xi ∧
    ∀ z : ℂ,
      ‖proposition59CCMTransform L i.N xi z -
          sourceCCMGroundProjectionScalar S i xi *
            proposition59CCMComplexTransform L i.N
              (D0Pstar.sourceCCMComplexRow S i) z‖
        ≤ proposition59CCMKernelL2 L i.N z *
            Real.sqrt (sourceCCMGroundProjectionErrorSq S i xi) := by
  classical
  set c : ℂ := sourceCCMGroundProjectionScalar S i xi with hc
  set row : CCMModeFinite i.N → ℂ := D0Pstar.sourceCCMComplexRow S i with hrowdef
  set w : CCMModeFinite i.N → ℂ := fun j => (xi j : ℂ) - c * row j with hw
  have herr :
      sourceCCMGroundProjectionErrorSq S i xi = ∑ j, Complex.normSq (w j) :=
    sourceCCMGroundProjectionErrorSq_eq_sum_normSq S i xi
  have hnonneg : 0 ≤ sourceCCMGroundProjectionErrorSq S i xi := by
    rw [herr]
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  refine ⟨hnonneg, fun z => ?_⟩
  have hsplit :
      proposition59CCMTransform L i.N xi z -
          c * proposition59CCMComplexTransform L i.N row z =
        ((Real.sqrt L : ℂ)⁻¹) *
          ∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z := by
    rw [proposition59CCMTransform_eq_mode_sum,
      proposition59CCMComplexTransform_eq_mode_sum]
    have hsum :
        (∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z) =
          (∑ j, (xi j : ℂ) *
              proposition59PoleKernel L (-ccmModeFinite i.N j) z) -
            c * ∑ j, row j *
              proposition59PoleKernel L (-ccmModeFinite i.N j) z := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [hw, sub_mul, mul_assoc]
    rw [hsum]
    ring
  rw [hsplit, norm_mul, herr]
  have hcs := proposition59CCM_mode_sum_cauchy_schwarz L i.N w z
  have hnormnn : (0 : ℝ) ≤ ‖((Real.sqrt L : ℂ)⁻¹)‖ := norm_nonneg _
  calc
    ‖((Real.sqrt L : ℂ)⁻¹)‖ *
        ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z‖ ≤
        ‖((Real.sqrt L : ℂ)⁻¹)‖ *
          (Real.sqrt (∑ j, Complex.normSq (w j)) *
            Real.sqrt
              (∑ j,
                Complex.normSq
                  (proposition59PoleKernel L
                    (-ccmModeFinite i.N j) z))) := by
      exact mul_le_mul_of_nonneg_left hcs hnormnn
    _ = proposition59CCMKernelL2 L i.N z *
          Real.sqrt (∑ j, Complex.normSq (w j)) := by
      rw [proposition59CCMKernelL2]
      ring

/-! ### Mandatory falsifier plants -/

/-- P2 plant: a two-coordinate complex row with entries `1` and `Complex.I`. -/
def goal058ConnectorPhasePlantRow : Fin 2 → ℂ := ![1, Complex.I]

/-- P2: no common unit phase turns the plant row into a real row, so the
Hermitian connector may not presuppose one. -/
theorem goal058ConnectorPhasePlant_no_common_real_phase :
    ¬ ∃ (phase : ℂ) (q : Fin 2 → ℝ),
        Complex.normSq phase = 1 ∧
          ∀ j, phase * goal058ConnectorPhasePlantRow j = (q j : ℂ) := by
  rintro ⟨phase, q, hunit, hreal⟩
  have h0 := hreal 0
  have h1 := hreal 1
  simp [goal058ConnectorPhasePlantRow] at h0 h1
  have hre : phase.re = 0 := by
    have := congrArg Complex.im h1
    simpa [Complex.ext_iff, Complex.mul_im, Complex.mul_re] using this
  have him : phase.im = 0 := by
    have := congrArg Complex.im h0
    simpa using this
  have : phase = 0 := by
    apply Complex.ext <;> simp [hre, him]
  rw [this] at hunit
  simp at hunit

/-- P5 plant: a unit complex row orthogonal to the tested real row. -/
def goal058ConnectorZeroOverlapRow : Fin 2 → ℂ := ![1, 0]

/-- P5 plant: the tested real row. -/
def goal058ConnectorZeroOverlapXi : Fin 2 → ℝ := ![0, 1]

theorem goal058ConnectorZeroOverlapRow_unit :
    star goal058ConnectorZeroOverlapRow ⬝ᵥ goal058ConnectorZeroOverlapRow
      = 1 := by
  simp [goal058ConnectorZeroOverlapRow, dotProduct, Fin.sum_univ_succ]

/-- P5: the Hermitian projection scalar vanishes on the orthogonal plant, and
the projective error is the full mass of the tested row.  No division by the
overlap occurs anywhere. -/
theorem goal058ConnectorZeroOverlapPlant_projection_zero :
    (star goal058ConnectorZeroOverlapRow ⬝ᵥ
        (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 0 ∧
      goal058ConnectorZeroOverlapXi ⬝ᵥ goal058ConnectorZeroOverlapXi -
          Complex.normSq
            (star goal058ConnectorZeroOverlapRow ⬝ᵥ
              (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 1 := by
  constructor <;>
    simp [goal058ConnectorZeroOverlapRow, goal058ConnectorZeroOverlapXi,
      dotProduct, Fin.sum_univ_succ]

/-- P6 plant: a one-coordinate purely imaginary source row. -/
def goal058ConnectorOrientationPlantRow : Fin 1 → ℂ := ![Complex.I]

/-- P6 plant: the tested one-coordinate real row. -/
def goal058ConnectorOrientationPlantXi : Fin 1 → ℝ := ![1]

theorem goal058ConnectorOrientationPlantRow_unit :
    star goal058ConnectorOrientationPlantRow ⬝ᵥ
        goal058ConnectorOrientationPlantRow = 1 := by
  simp [goal058ConnectorOrientationPlantRow, dotProduct]

/-- P6: with the Hermitian (conjugate-left) orientation the projection scalar
is `-I` and the coefficient error is exactly zero; a conjugation or orientation
reversal would break this. -/
theorem goal058ConnectorOrientationPlant_error_zero :
    (star goal058ConnectorOrientationPlantRow ⬝ᵥ
        (fun j => (goal058ConnectorOrientationPlantXi j : ℂ))) = -Complex.I ∧
      goal058ConnectorOrientationPlantXi ⬝ᵥ
            goal058ConnectorOrientationPlantXi -
          Complex.normSq
            (star goal058ConnectorOrientationPlantRow ⬝ᵥ
              (fun j =>
                (goal058ConnectorOrientationPlantXi j : ℂ))) = 0 ∧
      ∀ j,
        (goal058ConnectorOrientationPlantXi j : ℂ) -
            (star goal058ConnectorOrientationPlantRow ⬝ᵥ
              (fun k =>
                (goal058ConnectorOrientationPlantXi k : ℂ))) *
              goal058ConnectorOrientationPlantRow j = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [goal058ConnectorOrientationPlantRow,
      goal058ConnectorOrientationPlantXi, dotProduct]
  · simp [goal058ConnectorOrientationPlantRow,
      goal058ConnectorOrientationPlantXi, dotProduct]
  · intro j
    fin_cases j
    simp [goal058ConnectorOrientationPlantRow,
      goal058ConnectorOrientationPlantXi, dotProduct]

/-- P3: the exact commutator-tautology falsifiers of the preflight are retained
here as checks only.  Neither the main connector nor any lemma it uses depends
on them. -/
theorem goal058ConnectorCommutatorPlant_checks_retained :
    lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0 ∧
      ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ :=
  ⟨goal058Plant_lagCommutatorObservable_zero, goal058PlantQ_not_eigenvector⟩

#print axioms complexTrialLineProjection_isHermitian
#print axioms complexTrialLineProjection_sq_of_unit
#print axioms sourceCCMGroundProjectionErrorSq_eq_sum_normSq
#print axioms proposition59CCMTransform_sub_sourceProjection_le
#print axioms goal058ConnectorPhasePlant_no_common_real_phase
#print axioms goal058ConnectorZeroOverlapRow_unit
#print axioms goal058ConnectorZeroOverlapPlant_projection_zero
#print axioms goal058ConnectorOrientationPlantRow_unit
#print axioms goal058ConnectorOrientationPlant_error_zero
#print axioms goal058ConnectorCommutatorPlant_checks_retained

end Q3.RouteB
