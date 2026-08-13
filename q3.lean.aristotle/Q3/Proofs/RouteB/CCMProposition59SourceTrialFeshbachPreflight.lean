import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual
import Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge
import Q3.Proofs.RouteB.CCMFiniteWeilParity
import Q3.Proofs.RouteB.CCMFiniteWeilSourceCommutator

set_option linter.mathlibStandardSet false

/-!
# Goal 058 full-source trial-line / Schur preflight

This file deliberately separates the algebra that is already available from
the missing source theorem.  The exact D0Pstar source row is complex.  The
Proposition-59 ground transform is real.  A unit phase realification is
therefore recorded as an explicit proposition rather than synthesized by
taking real parts or by choosing a numerical phase.

The results below prove the exact consequences of such a realification, the
phase-adjusted P59 transform identity, the full trial-line four-block identity,
and a kernel-checked non-eigenvector commutator plant.  They do not prove that
the literal source row has the required phase realification, and they make
no positivity, gap, cofinal, route, or RH claim.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- Exact unit-phase realification, with no numerical phase choice and no
replacement of the complex row by its real part. -/
def phaseRealifies
    {ι : Type*}
    (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ) : Prop :=
  Complex.normSq phase = 1 ∧
    ∀ j, phase * row j = (q j : ℂ)

/-- The precise missing source-to-real carrier proposition for the literal
D0Pstar coefficient row. -/
def sourceCCMPhaseRealification
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (phase : ℂ)
    (q : CCMModeFinite i.N → ℝ) : Prop :=
  phaseRealifies phase (D0Pstar.sourceCCMComplexRow S i) q

/-- The exact existential source statement required before the complex trial
can be used as the real-even Proposition-59 row. -/
def sourceCCMHasRealEvenPhase
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) : Prop :=
  ∃ (phase : ℂ) (q : CCMModeFinite i.N → ℝ),
    sourceCCMPhaseRealification S i phase q ∧
      ∀ j, q (ccmNegFinite i.N j) = q j

/-- Taking real parts with phase one is not a construction: it requires the
original complex row to be exactly real coordinatewise. -/
theorem phaseOne_realPart_requires_exact_reality
    {ι : Type*} (row : ι → ℂ)
    (h : phaseRealifies 1 row (fun j => (row j).re)) :
    ∀ j, row j = (row j).re := by
  intro j
  simpa using h.2 j

/-- A unit phase realification preserves the exact Euclidean unit norm of a
complex row. -/
theorem dotProduct_self_eq_one_of_phaseRealifies
    {ι : Type*} [Fintype ι]
    (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ)
    (hrow : star row ⬝ᵥ row = 1)
    (hphase : phaseRealifies phase row q) :
    q ⬝ᵥ q = 1 := by
  rcases hphase with ⟨hunit, hreal⟩
  have hphaseNorm : star phase * phase = 1 := by
    have hunitC : ((Complex.normSq phase : ℝ) : ℂ) = 1 := by
      exact_mod_cast hunit
    rw [Complex.normSq_eq_conj_mul_self] at hunitC
    exact hunitC
  have hcomplex :
      star (fun j => phase * row j) ⬝ᵥ (fun j => phase * row j) = 1 := by
    have hterm (j : ι) :
        star (phase * row j) * (phase * row j) =
          (star phase * phase) * (star (row j) * row j) := by
      rw [StarMul.star_mul]
      ring
    calc
      star (fun j => phase * row j) ⬝ᵥ (fun j => phase * row j) =
          (star phase * phase) * (star row ⬝ᵥ row) := by
        classical
        simp only [dotProduct, Pi.star_apply, hterm]
        rw [Finset.mul_sum]
      _ = 1 := by
        rw [hrow, mul_one, hphaseNorm]
  have hcast : ((q ⬝ᵥ q : ℝ) : ℂ) = 1 := by
    calc
      ((q ⬝ᵥ q : ℝ) : ℂ) =
          star (fun j => (q j : ℂ)) ⬝ᵥ (fun j => (q j : ℂ)) := by
        classical
        simp [dotProduct]
      _ = star (fun j => phase * row j) ⬝ᵥ
          (fun j => phase * row j) := by
        congr 1
        · funext j
          simp only [Pi.star_apply]
          rw [hreal j]
        · funext j
          exact (hreal j).symm
      _ = 1 := hcomplex
  exact_mod_cast hcast

/-- The literal source row therefore yields a real unit row whenever the
missing phase-realification proposition is supplied. -/
theorem sourceCCMRealRow_unit_of_phaseRealification
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (phase : ℂ)
    (q : CCMModeFinite i.N → ℝ)
    (hphase : sourceCCMPhaseRealification S i phase q) :
    q ⬝ᵥ q = 1 := by
  exact dotProduct_self_eq_one_of_phaseRealifies
    phase (D0Pstar.sourceCCMComplexRow S i) q
    (D0Pstar.sourceCCMComplexRow_unit S i) hphase

/-- Exact reflection-evenness of a realified row would force exact
reflection-evenness of the original complex source row.  This is the
necessary source theorem that the current D0Pstar contract does not export. -/
theorem sourceCCMComplexRow_even_of_phaseRealification_even
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (phase : ℂ)
    (q : CCMModeFinite i.N → ℝ)
    (hphase : sourceCCMPhaseRealification S i phase q)
    (hqEven : ∀ j, q (ccmNegFinite i.N j) = q j) :
    ∀ j,
      D0Pstar.sourceCCMComplexRow S i (ccmNegFinite i.N j) =
        D0Pstar.sourceCCMComplexRow S i j := by
  rcases hphase with ⟨hunit, hreal⟩
  have hphase0 : phase ≠ 0 := by
    intro hzero
    subst phase
    simp at hunit
  intro j
  apply mul_left_cancel₀ hphase0
  rw [hreal, hqEven, hreal]

/-- Complex coefficient transport to the exact P59 pole order. -/
def proposition59CCMComplexCoefficient
    (N : ℕ) (q : CCMModeFinite N → ℂ) (k : ℤ) : ℂ :=
  if hk : k ∈ Finset.Icc (-(N : ℤ)) N then
    q ((ccmModeFiniteEquivIcc N).symm
      ⟨-k, neg_mem_Icc_of_mem_Icc hk⟩)
  else 0

@[simp] theorem proposition59CCMComplexCoefficient_neg_mode
    (N : ℕ) (q : CCMModeFinite N → ℂ) (i : CCMModeFinite N) :
    proposition59CCMComplexCoefficient N q (-ccmModeFinite N i) = q i := by
  have hi : -ccmModeFinite N i ∈ Finset.Icc (-(N : ℤ)) N :=
    neg_mem_Icc_of_mem_Icc
      (Finset.mem_Icc.mpr (ccmModeFinite_range N i))
  rw [proposition59CCMComplexCoefficient, dif_pos hi]
  congr 1
  let e := ccmModeFiniteEquivIcc N
  have hsub :
      (⟨-(-ccmModeFinite N i),
        neg_mem_Icc_of_mem_Icc hi⟩ :
          {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N}) = e i := by
    apply Subtype.ext
    simp [e, ccmModeFiniteEquivIcc]
  change e.symm _ = i
  rw [hsub, e.symm_apply_apply]

/-- The exact finite P59 transform of a complex CCM row. -/
def proposition59CCMComplexTransform
    (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) : ℂ → ℂ :=
  proposition59RawTransform L (Finset.Icc (-(N : ℤ)) N)
    (proposition59CCMComplexCoefficient N q)

theorem proposition59CCMComplexTransform_eq_mode_sum
    (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) (z : ℂ) :
    proposition59CCMComplexTransform L N q z =
      ((Real.sqrt L : ℂ)⁻¹) *
        ∑ i, q i * proposition59PoleKernel L (-ccmModeFinite N i) z := by
  classical
  unfold proposition59CCMComplexTransform proposition59RawTransform
  congr 1
  let e := ccmPoleModeEquivIcc N
  calc
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        proposition59CCMComplexCoefficient N q k *
          proposition59PoleKernel L k z) =
        ∑ k : {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N},
          proposition59CCMComplexCoefficient N q k.1 *
            proposition59PoleKernel L k.1 z := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (Finset.Icc (-(N : ℤ)) N)
          (fun k => proposition59CCMComplexCoefficient N q k *
            proposition59PoleKernel L k z)).symm
    _ = ∑ i : CCMModeFinite N,
          proposition59CCMComplexCoefficient N q (e i).1 *
            proposition59PoleKernel L (e i).1 z := by
      simpa using (e.sum_comp
        (fun k => proposition59CCMComplexCoefficient N q k.1 *
          proposition59PoleKernel L k.1 z)).symm
    _ = ∑ i, q i *
          proposition59PoleKernel L (-ccmModeFinite N i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [e, ccmPoleModeEquivIcc]

/-- The real P59 transform is exactly the unit-phase-adjusted transform of the
same complex source row.  This theorem is conditional only on the exact
realification equality; it does not manufacture that equality. -/
theorem proposition59CCMTransform_eq_phase_mul_complexTransform
    (L : ℝ) (N : ℕ)
    (phase : ℂ) (row : CCMModeFinite N → ℂ)
    (q : CCMModeFinite N → ℝ)
    (hreal : ∀ i, phase * row i = (q i : ℂ))
    (z : ℂ) :
    proposition59CCMTransform L N q z =
      phase * proposition59CCMComplexTransform L N row z := by
  rw [proposition59CCMTransform_eq_mode_sum,
    proposition59CCMComplexTransform_eq_mode_sum]
  simp_rw [← hreal, mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- Source-specialized exact P59 connector. -/
theorem sourceCCMProposition59Transform_eq_phase_mul_complexTransform
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (L : ℝ) (phase : ℂ) (q : CCMModeFinite i.N → ℝ)
    (hphase : sourceCCMPhaseRealification S i phase q)
    (z : ℂ) :
    proposition59CCMTransform L i.N q z =
      phase * proposition59CCMComplexTransform L i.N
        (D0Pstar.sourceCCMComplexRow S i) z := by
  exact proposition59CCMTransform_eq_phase_mul_complexTransform
    L i.N phase (D0Pstar.sourceCCMComplexRow S i) q hphase.2 z

/-- Rank-one trial-line matrix.  It is an orthogonal projection when `q` is
real and `q dot q = 1`. -/
def trialLineProjection
    {ι : Type*} (q : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.vecMulVec q q

/-- Algebraic complement of the trial line. -/
def trialLineComplement
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) : Matrix ι ι ℝ :=
  1 - trialLineProjection q

/-- Exact trial Rayleigh scalar. -/
def trialRayleigh
    {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ :=
  q ⬝ᵥ (K *ᵥ q)

/-- Exact coupling of the trial line into its algebraic complement. -/
def trialCoupling
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (q : ι → ℝ) : ι → ℝ :=
  trialLineComplement q *ᵥ (K *ᵥ q)

/-- Matrix of the exact CCM reflection permutation. -/
def ccmReflectionMatrix (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  fun i j => if j = ccmNegFinite N i then 1 else 0

/-- Exact even-sector projection for the CCM reflection. -/
def ccmEvenProjection (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  (2 : ℝ)⁻¹ • (1 + ccmReflectionMatrix N)

/-- Exact odd-sector projection for the CCM reflection. -/
def ccmOddProjection (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  (2 : ℝ)⁻¹ • (1 - ccmReflectionMatrix N)

/-- The even part of the complement-to-complement block. -/
def evenComplementBlock
    (N : ℕ)
    (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ)
    (q : CCMModeFinite N → ℝ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  ccmEvenProjection N * trialLineComplement q * K *
    trialLineComplement q * ccmEvenProjection N

/-- Exact odd-sector compression of the same matrix. -/
def oddSectorBlock
    (N : ℕ)
    (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  ccmOddProjection N * K * ccmOddProjection N

/-- Exact squared mass of the odd part of a trial row. -/
def oddTrialMass
    (N : ℕ) (q : CCMModeFinite N → ℝ) : ℝ :=
  let qOdd := ccmOddProjection N *ᵥ q
  qOdd ⬝ᵥ qOdd

theorem trialLineProjection_sq
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq : q ⬝ᵥ q = 1) :
    trialLineProjection q * trialLineProjection q =
      trialLineProjection q := by
  rw [trialLineProjection, Matrix.vecMulVec_mul_vecMulVec, hq]
  simp

/-- Exact four-block decomposition relative to the trial line and its
complement.  No spectral inequality is hidden in this identity. -/
theorem full_trialLine_four_block_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (q : ι → ℝ) :
    K =
      trialLineProjection q * K * trialLineProjection q +
      trialLineProjection q * K * trialLineComplement q +
      trialLineComplement q * K * trialLineProjection q +
      trialLineComplement q * K * trialLineComplement q := by
  unfold trialLineComplement
  noncomm_ring

/-- Literal CCM specialization of the exact four-block identity. -/
theorem ccmWeilMatFinite_full_trialLine_four_block_identity
    (mProject N : ℕ) (q : CCMModeFinite N → ℝ) :
    ccmWeilMatFinite mProject N =
      trialLineProjection q * ccmWeilMatFinite mProject N *
          trialLineProjection q +
      trialLineProjection q * ccmWeilMatFinite mProject N *
          trialLineComplement q +
      trialLineComplement q * ccmWeilMatFinite mProject N *
          trialLineProjection q +
      trialLineComplement q * ccmWeilMatFinite mProject N *
          trialLineComplement q := by
  exact full_trialLine_four_block_identity (ccmWeilMatFinite mProject N) q

/-- Scalar commutator observable tested by the exact plant below. -/
def lagCommutatorObservable
    {ι : Type*} [Fintype ι]
    (D K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ :=
  q ⬝ᵥ ((D * K - K * D) *ᵥ q)

/-- For symmetric real matrices the scalar expectation of a commutator is
identically zero, independently of whether the tested row is an eigenvector. -/
theorem lagCommutatorObservable_zero_of_isSymm
    {ι : Type*} [Fintype ι]
    (D K : Matrix ι ι ℝ) (q : ι → ℝ)
    (hD : D.IsSymm) (hK : K.IsSymm) :
    lagCommutatorObservable D K q = 0 := by
  have hDK :
      q ⬝ᵥ (D *ᵥ (K *ᵥ q)) = (D *ᵥ q) ⬝ᵥ (K *ᵥ q) := by
    calc
      q ⬝ᵥ (D *ᵥ (K *ᵥ q)) = (q ᵥ* D) ⬝ᵥ (K *ᵥ q) :=
        dotProduct_mulVec q D (K *ᵥ q)
      _ = (D.transpose *ᵥ q) ⬝ᵥ (K *ᵥ q) := by
        rw [Matrix.mulVec_transpose]
      _ = (D *ᵥ q) ⬝ᵥ (K *ᵥ q) := by rw [hD.eq]
  have hKD :
      q ⬝ᵥ (K *ᵥ (D *ᵥ q)) = (K *ᵥ q) ⬝ᵥ (D *ᵥ q) := by
    calc
      q ⬝ᵥ (K *ᵥ (D *ᵥ q)) = (q ᵥ* K) ⬝ᵥ (D *ᵥ q) :=
        dotProduct_mulVec q K (D *ᵥ q)
      _ = (K.transpose *ᵥ q) ⬝ᵥ (D *ᵥ q) := by
        rw [Matrix.mulVec_transpose]
      _ = (K *ᵥ q) ⬝ᵥ (D *ᵥ q) := by rw [hK.eq]
  rw [lagCommutatorObservable, Matrix.sub_mulVec, dotProduct_sub,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDK, hKD,
    dotProduct_comm, sub_self]

/-- Literal CCM specialization: the proposed scalar commutator expectation is
tautologically zero for every row, so it cannot be a new source observable. -/
theorem ccmLagCommutatorObservable_zero
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (q : CCMModeFinite N → ℝ) :
    lagCommutatorObservable
      (ccmModeDiagFinite N) (ccmWeilMatFinite mProject N) q = 0 := by
  apply lagCommutatorObservable_zero_of_isSymm
  · exact Matrix.isSymm_diagonal _
  · exact ccmWeilMatFinite_transpose_eq mProject N hm hN

/-- Three-valued classification required by the Goal-058 preflight. -/
inductive Goal058CommutatorClassification where
  | nonTautologicalSourceObservable
  | lagSourceTautologicalZero
  | commutatorEqualsUncontrolledEigenResidual
  deriving DecidableEq

/-- Typed stop returned by this preflight: the current source contract does
not provide `sourceCCMHasRealEvenPhase`. -/
inductive Goal058SourceTrialPreflightStop where
  | sourceComplexRealGroundCrosswalkMismatch
  deriving DecidableEq

def goal058SourceTrialPreflightStop : Goal058SourceTrialPreflightStop :=
  .sourceComplexRealGroundCrosswalkMismatch

theorem goal058SourceTrialPreflightStop_eq :
    goal058SourceTrialPreflightStop =
      Goal058SourceTrialPreflightStop.sourceComplexRealGroundCrosswalkMismatch :=
  rfl

abbrev Goal058PlantCarrier := CCMModeFinite 1

def goal058PlantD : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ :=
  !![-1, 0, 0;
      0, 0, 0;
      0, 0, 1]

/-- Exact symmetric, centrosymmetric, source-commutator-shaped plant matrix. -/
def goal058PlantK : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ :=
  !![0, 1, 1;
     1, 2, 1;
     1, 1, 0]

def goal058PlantEta : Goal058PlantCarrier → ℝ := ![1, 1, 1]
def goal058PlantBeta : Goal058PlantCarrier → ℝ := ![-1, 0, 1]
def goal058PlantQ : Goal058PlantCarrier → ℝ := ![1, 1, 1]

theorem goal058Plant_commutator :
    goal058PlantD * goal058PlantK - goal058PlantK * goal058PlantD =
      Matrix.vecMulVec goal058PlantBeta goal058PlantEta -
        Matrix.vecMulVec goal058PlantEta goal058PlantBeta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [goal058PlantD, goal058PlantK, goal058PlantBeta,
      goal058PlantEta, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Fin.sum_univ_succ]

theorem goal058PlantQ_reflection_even :
    ∀ i, goal058PlantQ (ccmNegFinite 1 i) = goal058PlantQ i := by
  intro i
  fin_cases i <;> norm_num [goal058PlantQ, ccmNegFinite]

theorem goal058PlantQ_not_eigenvector :
    ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ := by
  rintro ⟨mu, hmu⟩
  have h0 := congrFun hmu (0 : Goal058PlantCarrier)
  have h1 := congrFun hmu (1 : Goal058PlantCarrier)
  norm_num [goal058PlantK, goal058PlantQ, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at h0 h1
  linarith

theorem goal058Plant_lagCommutatorObservable_zero :
    lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0 := by
  norm_num [lagCommutatorObservable, goal058PlantD, goal058PlantK,
    goal058PlantQ, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_succ]

def goal058PlantClassification : Goal058CommutatorClassification :=
  .lagSourceTautologicalZero

theorem goal058PlantClassification_eq :
    goal058PlantClassification =
      Goal058CommutatorClassification.lagSourceTautologicalZero :=
  rfl

#print axioms dotProduct_self_eq_one_of_phaseRealifies
#print axioms phaseOne_realPart_requires_exact_reality
#print axioms sourceCCMRealRow_unit_of_phaseRealification
#print axioms sourceCCMComplexRow_even_of_phaseRealification_even
#print axioms proposition59CCMComplexTransform_eq_mode_sum
#print axioms proposition59CCMTransform_eq_phase_mul_complexTransform
#print axioms sourceCCMProposition59Transform_eq_phase_mul_complexTransform
#print axioms trialLineProjection_sq
#print axioms full_trialLine_four_block_identity
#print axioms ccmWeilMatFinite_full_trialLine_four_block_identity
#print axioms lagCommutatorObservable_zero_of_isSymm
#print axioms ccmLagCommutatorObservable_zero
#print axioms goal058Plant_commutator
#print axioms goal058PlantQ_reflection_even
#print axioms goal058PlantQ_not_eigenvector
#print axioms goal058Plant_lagCommutatorObservable_zero
#print axioms goal058PlantClassification_eq
#print axioms goal058SourceTrialPreflightStop_eq

end Q3.RouteB
