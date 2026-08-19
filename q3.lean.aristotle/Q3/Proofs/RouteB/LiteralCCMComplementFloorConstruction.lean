import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementFloor
import Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock

set_option linter.mathlibStandardSet false

open Complex Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace Q3.RouteB

/-!
# Literal CCM complement-floor construction by fixed-shift transport

The existing Gram checker proves a floor once a certificate at the literal
Rayleigh shift is supplied.  This file isolates a different source-facing
construction: a positive floor at one fixed real shift survives transport to
the literal source Rayleigh shift, with exactly one unit of floor lost per unit
of shift error.

The theorem is exact and finite-dimensional.  It does not construct the
fixed-shift floor or prove a Rayleigh-proximity rate.  Those remain visible
analytic suppliers on the production selected schedule.
-/

private theorem complexTrialLineComplement_sq_of_unit_fixedShift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineComplement q * complexTrialLineComplement q =
      complexTrialLineComplement q := by
  have hP := complexTrialLineProjection_sq_of_unit q hq
  rw [complexTrialLineComplement]
  simp [Matrix.sub_mul, Matrix.mul_sub, hP]

private theorem complexTrialComplementBlock_fixedShift_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ)
    (aStar a : ℝ)
    (hq : star q ⬝ᵥ q = 1) :
    let Q := complexTrialLineComplement q
    Q * (K - (a : ℂ) • (1 : Matrix ι ι ℂ)) * Q =
      Q * (K - (aStar : ℂ) • (1 : Matrix ι ι ℂ)) * Q +
        ((aStar - a : ℝ) : ℂ) • Q := by
  intro Q
  have hQsq : Q * Q = Q := by
    simpa [Q] using complexTrialLineComplement_sq_of_unit_fixedShift q hq
  have hexp (c : ℝ) :
      Q * (K - (c : ℂ) • (1 : Matrix ι ι ℂ)) * Q =
        Q * K * Q - (c : ℂ) • Q := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.sub_mul, Matrix.smul_mul, hQsq]
  rw [hexp a, hexp aStar]
  ext j k
  simp <;> ring

/-- A floor at a fixed real shift transports to another real shift.  The
available floor changes by the exact scalar `aStar - a`; the stated `beta` may
be any positive lower bound below that transported value. -/
theorem complexTrialComplementFloor_of_fixedShiftFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ)
    (aStar a betaStar beta : ℝ)
    (hq : star q ⬝ᵥ q = 1)
    (hfixed : complexTrialComplementFloor K q (aStar : ℂ) betaStar)
    (hbeta : 0 < beta)
    (hshift : beta ≤ betaStar + aStar - a) :
    complexTrialComplementFloor K q (a : ℂ) beta := by
  let Q := complexTrialLineComplement q
  let BStar := Q * (K - (aStar : ℂ) • (1 : Matrix ι ι ℂ)) * Q
  let B := Q * (K - (a : ℂ) • (1 : Matrix ι ι ℂ)) * Q
  have hblock : B = BStar + ((aStar - a : ℝ) : ℂ) • Q := by
    simpa [BStar, B, Q] using
      complexTrialComplementBlock_fixedShift_identity K q aStar a hq
  change 0 < beta ∧
    ∀ x : ι → ℂ,
      beta * ((star (Q *ᵥ x)) ⬝ᵥ (Q *ᵥ x)).re ≤
        ((star (Q *ᵥ x)) ⬝ᵥ (B *ᵥ x)).re
  refine ⟨hbeta, ?_⟩
  intro x
  have hfixedX := hfixed.2 x
  change betaStar * ((star (Q *ᵥ x)) ⬝ᵥ (Q *ᵥ x)).re ≤
    ((star (Q *ᵥ x)) ⬝ᵥ (BStar *ᵥ x)).re at hfixedX
  have henergy :
      ((star (Q *ᵥ x)) ⬝ᵥ (B *ᵥ x)).re =
        ((star (Q *ᵥ x)) ⬝ᵥ (BStar *ᵥ x)).re +
          (aStar - a) *
            ((star (Q *ᵥ x)) ⬝ᵥ (Q *ᵥ x)).re := by
    rw [hblock, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul]
    simp [smul_eq_mul, Complex.mul_re]
  have hnorm :
      0 ≤ ((star (Q *ᵥ x)) ⬝ᵥ (Q *ᵥ x)).re := by
    simpa [Complex.normSq, dotProduct] using
      (show 0 ≤ ∑ j, Complex.normSq ((Q *ᵥ x) j) from
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg ((Q *ᵥ x) j))
  rw [henergy]
  nlinarith

/-- Literal source specialization of fixed-shift transport. -/
theorem sourceCCMComplexTrialComplementFloor_of_fixedShiftFloor
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (aStar betaStar beta : ℝ)
    (hfixed :
      complexTrialComplementFloor
        (D0Pstar.sourceCCMFiniteMatrix i)
        (D0Pstar.sourceCCMComplexRow S i)
        (aStar : ℂ) betaStar)
    (hbeta : 0 < beta)
    (hshift :
      beta ≤ betaStar + aStar - D0Pstar.sourceCCMFiniteRayleigh S i) :
    sourceCCMComplexTrialComplementFloor S i beta := by
  simpa [sourceCCMComplexTrialComplementFloor] using
    complexTrialComplementFloor_of_fixedShiftFloor
      (D0Pstar.sourceCCMFiniteMatrix i)
      (D0Pstar.sourceCCMComplexRow S i)
      aStar (D0Pstar.sourceCCMFiniteRayleigh S i)
      betaStar beta
      (D0Pstar.sourceCCMComplexRow_unit S i)
      hfixed hbeta hshift

/-- Production-schedule constructor.  A uniform fixed-shift floor `betaStar`
and a half-floor Rayleigh proximity estimate produce the literal Rayleigh-shift
floor `betaStar / 2` at every selected cell. -/
theorem literalCCMComplementFloorConstruction
    (S : D0Pstar.ProlateCanonicalSourceData)
    (aStar betaStar : ℝ)
    (hbetaStar : 0 < betaStar)
    (hfixed : ∀ k,
      complexTrialComplementFloor
        (D0Pstar.sourceCCMFiniteMatrix (D0Pstar.selectedPairIndex S k))
        (D0Pstar.sourceCCMComplexRow S (D0Pstar.selectedPairIndex S k))
        (aStar : ℂ) betaStar)
    (hrayleigh : ∀ k,
      |D0Pstar.sourceCCMFiniteRayleigh S (D0Pstar.selectedPairIndex S k) -
          aStar| ≤ betaStar / 2) :
    ∀ k,
      sourceCCMComplexTrialComplementFloor S
        (D0Pstar.selectedPairIndex S k) (betaStar / 2) := by
  intro k
  have hupper :
      D0Pstar.sourceCCMFiniteRayleigh S (D0Pstar.selectedPairIndex S k) -
          aStar ≤ betaStar / 2 :=
    (le_abs_self _).trans (hrayleigh k)
  apply sourceCCMComplexTrialComplementFloor_of_fixedShiftFloor
    S (D0Pstar.selectedPairIndex S k) aStar betaStar (betaStar / 2)
    (hfixed k)
  · linarith
  · linarith

/-! ### Mandatory shift-mutation plant -/

/-- A literal two-dimensional matrix whose trial-line complement has floor one
at shift zero but loses that floor completely when the shift is moved to one. -/
def goal058FixedShiftMutationK : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 1]

def goal058FixedShiftMutationQ : Fin 2 → ℂ := ![1, 0]
def goal058FixedShiftMutationY : Fin 2 → ℂ := ![0, 1]

theorem goal058FixedShiftMutationQ_unit :
    star goal058FixedShiftMutationQ ⬝ᵥ goal058FixedShiftMutationQ = 1 := by
  norm_num [goal058FixedShiftMutationQ, dotProduct, Fin.sum_univ_succ]

theorem goal058FixedShiftMutationQComplement_fixes_Y :
    complexTrialLineComplement goal058FixedShiftMutationQ *ᵥ
        goal058FixedShiftMutationY = goal058FixedShiftMutationY := by
  funext i
  fin_cases i <;>
    norm_num [complexTrialLineComplement, complexTrialLineProjection,
      goal058FixedShiftMutationQ, goal058FixedShiftMutationY,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec,
      Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_succ,
      Matrix.one_apply, Fin.succ_zero_eq_one]

theorem goal058FixedShiftMutation_shiftedBlock_kills_Y :
    let Q := complexTrialLineComplement goal058FixedShiftMutationQ
    (Q *
        (goal058FixedShiftMutationK -
          (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Q) *ᵥ
      goal058FixedShiftMutationY = 0 := by
  dsimp only
  funext i
  fin_cases i <;>
    norm_num [complexTrialLineComplement, complexTrialLineProjection,
      goal058FixedShiftMutationK, goal058FixedShiftMutationQ,
      goal058FixedShiftMutationY, Matrix.mul_apply, Matrix.mulVec,
      Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_succ]

theorem goal058FixedShiftMutationY_normSq_re :
    (star goal058FixedShiftMutationY ⬝ᵥ goal058FixedShiftMutationY).re = 1 := by
  norm_num [goal058FixedShiftMutationY, dotProduct, Fin.sum_univ_succ]

/-- The shift discrepancy is load-bearing: at the mutated shift one, no
positive complement floor survives. -/
theorem goal058FixedShiftMutation_no_positive_floor
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ complexTrialComplementFloor
      goal058FixedShiftMutationK goal058FixedShiftMutationQ 1 beta := by
  intro hfloor
  have h := hfloor.2 goal058FixedShiftMutationY
  let Q := complexTrialLineComplement goal058FixedShiftMutationQ
  have hQY : Q *ᵥ goal058FixedShiftMutationY =
      goal058FixedShiftMutationY :=
    goal058FixedShiftMutationQComplement_fixes_Y
  have hBY :
      (Q *
          (goal058FixedShiftMutationK -
            (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Q) *ᵥ
        goal058FixedShiftMutationY = 0 :=
    goal058FixedShiftMutation_shiftedBlock_kills_Y
  change beta *
      ((star (Q *ᵥ goal058FixedShiftMutationY)) ⬝ᵥ
        (Q *ᵥ goal058FixedShiftMutationY)).re ≤
    ((star (Q *ᵥ goal058FixedShiftMutationY)) ⬝ᵥ
      ((Q *
          (goal058FixedShiftMutationK -
            (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Q) *ᵥ
        goal058FixedShiftMutationY)).re at h
  rw [hQY, hBY, dotProduct_zero, Complex.zero_re,
    goal058FixedShiftMutationY_normSq_re] at h
  linarith

#print axioms complexTrialComplementFloor_of_fixedShiftFloor
#print axioms sourceCCMComplexTrialComplementFloor_of_fixedShiftFloor
#print axioms literalCCMComplementFloorConstruction
#print axioms goal058FixedShiftMutation_no_positive_floor

end Q3.RouteB
