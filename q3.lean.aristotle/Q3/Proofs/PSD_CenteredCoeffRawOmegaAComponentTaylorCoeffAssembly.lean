import Q3.Proofs.PSD_CenteredCoeffRawOmegaAHRawLanding

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Step33A.1-A component Taylor coefficient assembly support.

This file only closes the exact algebraic subtraction layer in the active
`RawTaylorCoeffCert` residual convention.  It does not claim that a
proof-grade component product polynomial has been assembled from
`omega`, `omegaPrime`, `shapeSq`, and `shapeSqDeriv`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral
namespace RawOmegaATaylorModelCertificate

def primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree : Nat := 45

/-- Degree-45 zero extension of the active degree-15 derivative model. -/
def primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded
    (i : Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1)) :
    Rat :=
  if h : i.1 < 16 then
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff ⟨i.1, h⟩
  else
    0

/-- Residual coefficients obtained by subtracting the active degree-15
derivative model from a rational degree-45 raw-derivative model. -/
def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf
    (assembledRawDerivCoeff :
      Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1) ->
        Rat)
    (i : Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1)) :
    Rat :=
  assembledRawDerivCoeff i -
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded i

theorem rawOmegaATaylorPolynomial_sub_coeff
    (degree : Nat) (center : Rat)
    (lhs rhs : Fin (degree + 1) -> Rat) (eta : Real) :
    rawOmegaATaylorPolynomial
        degree center (fun i => lhs i - rhs i) eta =
      rawOmegaATaylorPolynomial degree center lhs eta -
        rawOmegaATaylorPolynomial degree center rhs eta := by
  unfold rawOmegaATaylorPolynomial
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  norm_num
  ring

/-- Cauchy coefficients for the product of two rational Taylor polynomials in
the same centered variable.

The definition is deliberately pair-indexed instead of range/antidiagonal
indexed.  This keeps the proof below independent of a later choice of concrete
component degrees and avoids hiding zero-extension conventions. -/
def rawOmegaTaylorCauchyCoeff
    (leftDegree rightDegree : Nat)
    (leftCoeff : Fin (leftDegree + 1) -> Rat)
    (rightCoeff : Fin (rightDegree + 1) -> Rat) :
    Fin (leftDegree + rightDegree + 1) -> Rat :=
  fun n =>
    ∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
      if i.1 + j.1 = n.1 then leftCoeff i * rightCoeff j else 0

theorem rawOmegaATaylorPolynomial_mul_coeff
    (leftDegree rightDegree : Nat) (center : Rat)
    (leftCoeff : Fin (leftDegree + 1) -> Rat)
    (rightCoeff : Fin (rightDegree + 1) -> Rat) (eta : Real) :
    rawOmegaATaylorPolynomial leftDegree center leftCoeff eta *
        rawOmegaATaylorPolynomial rightDegree center rightCoeff eta =
      rawOmegaATaylorPolynomial (leftDegree + rightDegree) center
        (rawOmegaTaylorCauchyCoeff leftDegree rightDegree leftCoeff rightCoeff)
        eta := by
  let x : Real := eta - (center : Real)
  unfold rawOmegaATaylorPolynomial rawOmegaTaylorCauchyCoeff
  change
    (∑ i : Fin (leftDegree + 1), (leftCoeff i : Real) * x ^ i.1) *
        (∑ j : Fin (rightDegree + 1), (rightCoeff j : Real) * x ^ j.1) =
      ∑ n : Fin (leftDegree + rightDegree + 1),
        ((∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
          if i.1 + j.1 = n.1 then leftCoeff i * rightCoeff j else 0 :
            Rat) : Real) *
          x ^ n.1
  have hsingle
      (i : Fin (leftDegree + 1)) (j : Fin (rightDegree + 1)) :
      (∑ n : Fin (leftDegree + rightDegree + 1),
          if i.1 + j.1 = n.1 then
            (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
          else
            (0 : Real)) =
        ((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ (i.1 + j.1) := by
    let n0 : Fin (leftDegree + rightDegree + 1) :=
      ⟨i.1 + j.1, by omega⟩
    calc
      (∑ n : Fin (leftDegree + rightDegree + 1),
          if i.1 + j.1 = n.1 then
            (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
          else
            (0 : Real))
          =
        (if i.1 + j.1 = n0.1 then
          (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n0.1)
        else
          (0 : Real)) := by
          refine
            Finset.sum_eq_single (s := Finset.univ)
              (f := fun n : Fin (leftDegree + rightDegree + 1) =>
                if i.1 + j.1 = n.1 then
                  (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
                else
                  (0 : Real))
              n0 ?_ ?_
          · intro n _hn hne
            have hval : i.1 + j.1 ≠ n.1 := by
              intro h
              exact hne (Fin.ext h.symm)
            simp [hval]
          · intro hn0
            exact False.elim (hn0 (Finset.mem_univ n0))
      _ = ((leftCoeff i * rightCoeff j : Rat) : Real) *
          x ^ (i.1 + j.1) := by
          simp [n0]
  calc
    (∑ i : Fin (leftDegree + 1), (leftCoeff i : Real) * x ^ i.1) *
        (∑ j : Fin (rightDegree + 1), (rightCoeff j : Real) * x ^ j.1)
        =
      ∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
        ((leftCoeff i : Real) * x ^ i.1) *
          ((rightCoeff j : Real) * x ^ j.1) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Finset.mul_sum]
    _ =
      ∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
        ((leftCoeff i * rightCoeff j : Rat) : Real) *
          x ^ (i.1 + j.1) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [pow_add]
        norm_num
        ring
    _ =
      ∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
        ∑ n : Fin (leftDegree + rightDegree + 1),
          if i.1 + j.1 = n.1 then
            (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
          else
            (0 : Real) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact (hsingle i j).symm
    _ =
      ∑ n : Fin (leftDegree + rightDegree + 1),
        ∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
          if i.1 + j.1 = n.1 then
            (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
          else
            (0 : Real) := by
        calc
          (∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
              ∑ n : Fin (leftDegree + rightDegree + 1),
                if i.1 + j.1 = n.1 then
                  (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
                else
                  (0 : Real))
              =
            ∑ i : Fin (leftDegree + 1), ∑ n : Fin (leftDegree + rightDegree + 1),
              ∑ j : Fin (rightDegree + 1),
                if i.1 + j.1 = n.1 then
                  (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
                else
                  (0 : Real) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [Finset.sum_comm]
          _ =
            ∑ n : Fin (leftDegree + rightDegree + 1), ∑ i : Fin (leftDegree + 1),
              ∑ j : Fin (rightDegree + 1),
                if i.1 + j.1 = n.1 then
                  (((leftCoeff i * rightCoeff j : Rat) : Real) * x ^ n.1)
                else
                  (0 : Real) := by
              rw [Finset.sum_comm]
    _ =
      ∑ n : Fin (leftDegree + rightDegree + 1),
        ((∑ i : Fin (leftDegree + 1), ∑ j : Fin (rightDegree + 1),
          if i.1 + j.1 = n.1 then leftCoeff i * rightCoeff j else 0 :
            Rat) : Real) *
          x ^ n.1 := by
        refine Finset.sum_congr rfl ?_
        intro n _hn
        rw [Rat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Rat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        by_cases h : i.1 + j.1 = n.1
        · simp [h]
        · simp [h]

/-!
Object-level component coefficient stream.

The scale below is the rational midpoint of the local interval used in the
active landing file.  It is intentionally named `NominalScaleCoeff`: these
definitions give a checked rational object bridge, not a proof that this
rational is equal to `((3 : Real) / 10) / Real.pi`.
-/

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff : Fin 16 -> Rat :=
  Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedCoeff

def primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower : Rat :=
  (-85314634821843642073465861701640867472353398314119326820557162830783014314359848985502357 : Rat) /
    16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper : Rat :=
  (-426573174109218210367240990627486922998187245419326080653670377242934688213891611916507071 : Rat) /
    80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff : Rat :=
  (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower +
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper) /
    2

def primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs : Rat :=
  (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper -
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower) /
    2

theorem primaryFiniteRow0Parent0Split100Sub0_nominalOmegaAnchor_abs_error_of_active_interval
    {omegaCenter : Real}
    (hLower :
      (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower :
        Real) <= omegaCenter)
    (hUpper :
      omegaCenter <=
        (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper :
          Real)) :
    |omegaCenter -
        (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff :
          Real)| <=
      (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs :
        Real) := by
  rw [abs_le]
  constructor
  · norm_num [primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper] at hLower hUpper ⊢
    linarith
  · norm_num [primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
      primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper] at hLower hUpper ⊢
    linarith

def primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff : Fin 17 -> Rat :=
  Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.integratedCoeff
    Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff

def primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff : Fin 17 -> Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff : Fin 16 -> Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated

def primaryFiniteRow0Parent0Split100Sub0TightScaleLower : Rat :=
  (95492965855137201461330258023 : Rat) /
    1000000000000000000000000000000

def primaryFiniteRow0Parent0Split100Sub0TightScaleUpper : Rat :=
  (95492965855137201461330258024 : Rat) /
    1000000000000000000000000000000

def primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Rat :=
  primaryFiniteRow0Parent0Split100Sub0TightScaleUpper

def primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Rat :=
  (190985931710274402922660516047 : Rat) /
    2000000000000000000000000000000

def primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Rat :=
  (1 : Rat) /
    2000000000000000000000000000000

theorem primaryFiniteRow0Parent0Split100Sub0_nominalScale_mem_tightInterval :
    (primaryFiniteRow0Parent0Split100Sub0TightScaleLower : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) ∧
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0TightScaleUpper : Real) := by
  constructor <;>
    norm_num [primaryFiniteRow0Parent0Split100Sub0TightScaleLower,
      primaryFiniteRow0Parent0Split100Sub0TightScaleUpper,
      primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff]

theorem primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_bound :
    |(primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)| <=
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real) := by
  rw [abs_of_nonneg]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff,
      primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound,
      primaryFiniteRow0Parent0Split100Sub0TightScaleUpper]
  · norm_num [primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff]

theorem primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_error_of_active_interval
    {scale : Real}
    (hLower :
      (primaryFiniteRow0Parent0Split100Sub0TightScaleLower : Real) <= scale)
    (hUpper :
      scale <=
        (primaryFiniteRow0Parent0Split100Sub0TightScaleUpper : Real)) :
    |scale - (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)| <=
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) := by
  rw [abs_le]
  constructor
  · norm_num [primaryFiniteRow0Parent0Split100Sub0TightScaleLower,
      primaryFiniteRow0Parent0Split100Sub0TightScaleUpper,
      primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff,
      primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs] at hLower hUpper ⊢
    linarith
  · norm_num [primaryFiniteRow0Parent0Split100Sub0TightScaleLower,
      primaryFiniteRow0Parent0Split100Sub0TightScaleUpper,
      primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff,
      primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs] at hLower hUpper ⊢
    linarith

theorem primaryFiniteRow0Parent0Split100Sub0_nominal_source_interval_bridge
    {scale omegaCenter : Real}
    (hScaleLower :
      (primaryFiniteRow0Parent0Split100Sub0TightScaleLower : Real) <= scale)
    (hScaleUpper :
      scale <=
        (primaryFiniteRow0Parent0Split100Sub0TightScaleUpper : Real))
    (hOmegaLower :
      (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower :
        Real) <= omegaCenter)
    (hOmegaUpper :
      omegaCenter <=
        (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper :
          Real)) :
    |scale - (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)| <=
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs : Real) ∧
      |omegaCenter -
          (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff :
            Real)| <=
        (primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs :
          Real) :=
  ⟨primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_error_of_active_interval
      hScaleLower hScaleUpper,
    primaryFiniteRow0Parent0Split100Sub0_nominalOmegaAnchor_abs_error_of_active_interval
      hOmegaLower hOmegaUpper⟩

theorem primaryFiniteRow0Parent0Split100Sub0_product_error_budget_bridge
    {scale nominalScale omegaPrimeShape omegaPrimeShapeNominal
      omegaShapeDeriv omegaShapeDerivNominal scaleErr omegaPrimeShapeErr
      omegaShapeDerivErr omegaPrimeShapeAbs omegaShapeDerivAbs nominalScaleAbs
      budget : Real}
    (hScale : |scale - nominalScale| <= scaleErr)
    (hOmegaPrimeShape :
      |omegaPrimeShape - omegaPrimeShapeNominal| <= omegaPrimeShapeErr)
    (hOmegaShapeDeriv :
      |omegaShapeDeriv - omegaShapeDerivNominal| <= omegaShapeDerivErr)
    (hOmegaPrimeShapeAbs : |omegaPrimeShape| <= omegaPrimeShapeAbs)
    (hOmegaShapeDerivAbs : |omegaShapeDeriv| <= omegaShapeDerivAbs)
    (hNominalScaleAbs : |nominalScale| <= nominalScaleAbs)
    (hScaleErrNonneg : 0 <= scaleErr)
    (hBudget :
      scaleErr * (omegaPrimeShapeAbs + omegaShapeDerivAbs) +
          nominalScaleAbs * (omegaPrimeShapeErr + omegaShapeDerivErr) <=
        budget) :
    |scale * (omegaPrimeShape + omegaShapeDeriv) -
        nominalScale * (omegaPrimeShapeNominal + omegaShapeDerivNominal)| <=
      budget := by
  have hProductAbs :
      |omegaPrimeShape + omegaShapeDeriv| <=
        omegaPrimeShapeAbs + omegaShapeDerivAbs :=
    (abs_add_le omegaPrimeShape omegaShapeDeriv).trans
      (add_le_add hOmegaPrimeShapeAbs hOmegaShapeDerivAbs)
  have hProductErr :
      |(omegaPrimeShape - omegaPrimeShapeNominal) +
          (omegaShapeDeriv - omegaShapeDerivNominal)| <=
        omegaPrimeShapeErr + omegaShapeDerivErr :=
    (abs_add_le (omegaPrimeShape - omegaPrimeShapeNominal)
      (omegaShapeDeriv - omegaShapeDerivNominal)).trans
      (add_le_add hOmegaPrimeShape hOmegaShapeDeriv)
  have hTermScale :
      |scale - nominalScale| * |omegaPrimeShape + omegaShapeDeriv| <=
        scaleErr * (omegaPrimeShapeAbs + omegaShapeDerivAbs) :=
    mul_le_mul hScale hProductAbs (abs_nonneg _) hScaleErrNonneg
  have hNominalScaleAbsNonneg : 0 <= nominalScaleAbs :=
    (abs_nonneg nominalScale).trans hNominalScaleAbs
  have hTermProduct :
      |nominalScale| *
          |(omegaPrimeShape - omegaPrimeShapeNominal) +
            (omegaShapeDeriv - omegaShapeDerivNominal)| <=
        nominalScaleAbs * (omegaPrimeShapeErr + omegaShapeDerivErr) :=
    mul_le_mul hNominalScaleAbs hProductErr (abs_nonneg _)
      hNominalScaleAbsNonneg
  have hDecomp :
      scale * (omegaPrimeShape + omegaShapeDeriv) -
          nominalScale * (omegaPrimeShapeNominal + omegaShapeDerivNominal) =
        (scale - nominalScale) * (omegaPrimeShape + omegaShapeDeriv) +
          nominalScale *
            ((omegaPrimeShape - omegaPrimeShapeNominal) +
              (omegaShapeDeriv - omegaShapeDerivNominal)) := by
    ring
  calc
    |scale * (omegaPrimeShape + omegaShapeDeriv) -
        nominalScale * (omegaPrimeShapeNominal + omegaShapeDerivNominal)|
        =
      |(scale - nominalScale) * (omegaPrimeShape + omegaShapeDeriv) +
        nominalScale *
          ((omegaPrimeShape - omegaPrimeShapeNominal) +
            (omegaShapeDeriv - omegaShapeDerivNominal))| := by
        rw [hDecomp]
    _ <=
      |(scale - nominalScale) * (omegaPrimeShape + omegaShapeDeriv)| +
        |nominalScale *
          ((omegaPrimeShape - omegaPrimeShapeNominal) +
            (omegaShapeDeriv - omegaShapeDerivNominal))| :=
        abs_add_le _ _
    _ =
      |scale - nominalScale| * |omegaPrimeShape + omegaShapeDeriv| +
        |nominalScale| *
          |(omegaPrimeShape - omegaPrimeShapeNominal) +
            (omegaShapeDeriv - omegaShapeDerivNominal)| := by
        rw [abs_mul, abs_mul]
    _ <=
      scaleErr * (omegaPrimeShapeAbs + omegaShapeDerivAbs) +
        nominalScaleAbs * (omegaPrimeShapeErr + omegaShapeDerivErr) :=
        add_le_add hTermScale hTermProduct
    _ <= budget := hBudget

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeSqProductCoeff :
    Fin 32 -> Rat :=
  rawOmegaTaylorCauchyCoeff 15 16
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff

def primaryFiniteRow0Parent0Split100Sub0OmegaShapeSqDerivProductCoeff :
    Fin 32 -> Rat :=
  rawOmegaTaylorCauchyCoeff 16 15
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff

def primaryFiniteRow0Parent0Split100Sub0ProductCoeffPadded
    (coeff : Fin 32 -> Rat)
    (i : Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1)) :
    Rat :=
  if h : i.1 < 32 then coeff ⟨i.1, h⟩ else 0

def primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff
    (i : Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1)) :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff *
    (primaryFiniteRow0Parent0Split100Sub0ProductCoeffPadded
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeSqProductCoeff i +
      primaryFiniteRow0Parent0Split100Sub0ProductCoeffPadded
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeSqDerivProductCoeff i)

def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
    (i : Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1)) :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff i

theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrime_shapeSq_product_crosswalk
    (eta : Real) :
    rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff eta *
        rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta =
      rawOmegaATaylorPolynomial 31 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeSqProductCoeff eta := by
  simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeShapeSqProductCoeff] using
    rawOmegaATaylorPolynomial_mul_coeff 15 16 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta

theorem primaryFiniteRow0Parent0Split100Sub0_omega_shapeSqDeriv_product_crosswalk
    (eta : Real) :
    rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff eta *
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta =
      rawOmegaATaylorPolynomial 31 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaShapeSqDerivProductCoeff eta := by
  simpa [primaryFiniteRow0Parent0Split100Sub0OmegaShapeSqDerivProductCoeff] using
    rawOmegaATaylorPolynomial_mul_coeff 16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta

theorem primaryFiniteRow0Parent0Split100Sub0_padded_residualDerivmodel_poly_eq
    (eta : Real) :
    rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded eta =
      rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta := by
  let term : Nat -> Real := fun k =>
    ((if h : k < 16 then
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff ⟨k, h⟩
      else
        0 : Rat) : Real) *
      (eta - (((1 : Rat) / 20 : Rat) : Real)) ^ k
  have h45 :
      rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded eta =
        ∑ k ∈ Finset.range 46, term k := by
    unfold rawOmegaATaylorPolynomial
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded
    change (∑ i : Fin 46, term i.1) = ∑ k ∈ Finset.range 46, term k
    exact Fin.sum_univ_eq_sum_range term 46
  have h15 :
      rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta =
        ∑ k ∈ Finset.range 16, term k := by
    unfold rawOmegaATaylorPolynomial
    change
      (∑ i : Fin 16,
        ((primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff i : Rat) :
            Real) *
          (eta - (((1 : Rat) / 20 : Rat) : Real)) ^ i.1) =
        ∑ k ∈ Finset.range 16, term k
    rw [← Fin.sum_univ_eq_sum_range term 16]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    unfold term
    simp [i.2]
  have hsubset : Finset.range 16 ⊆ Finset.range 46 := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have htail :
      ∀ k ∈ Finset.range 46, k ∉ Finset.range 16 -> term k = 0 := by
    intro k _hk46 hknot16
    have hkge : ¬ k < 16 := by
      simpa only [Finset.mem_range] using hknot16
    unfold term
    simp [hkge]
  calc
    rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded eta
        = ∑ k ∈ Finset.range 46, term k := h45
    _ = ∑ k ∈ Finset.range 16, term k := (Finset.sum_subset hsubset htail).symm
    _ = rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta := h15.symm

/-- Algebraic coefficient-subtraction crosswalk for the active degree-45
component residual model.

This theorem is conditional in the intended sense: it works for any rational
degree-45 `assembledRawDerivCoeff`.  A separate upstream proof must still build
that coefficient vector from proof-grade component Taylor data.

This is intentionally a same-degree bridge.  The bridge from the active
degree-15 derivative model to `ResidualDerivmodelCoeffPadded` is a separate
zero-extension gate, not hidden inside this theorem. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled
    (assembledRawDerivCoeff :
      Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1) ->
        Rat)
    (eta : Real) :
    rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20) assembledRawDerivCoeff eta -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded eta =
      rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf
          assembledRawDerivCoeff) eta := by
  rw [← rawOmegaATaylorPolynomial_sub_coeff
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    ((1 : Rat) / 20) assembledRawDerivCoeff
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded eta]
  rfl

/-- Algebraic active-model crosswalk after the degree-15 residual model is
zero-extended into the degree-45 component convention.

This is still conditional on a proof-grade rational `assembledRawDerivCoeff`.
It does not assert that the raw closed form with the `1 / Real.pi` scale has
already been assembled into rational coefficients. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk_of_assembled
    (assembledRawDerivCoeff :
      Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1) ->
        Rat)
    (eta : Real) :
    rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20) assembledRawDerivCoeff eta -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta =
      rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf
          assembledRawDerivCoeff) eta := by
  rw [← primaryFiniteRow0Parent0Split100Sub0_padded_residualDerivmodel_poly_eq eta]
  exact
    primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled
      assembledRawDerivCoeff eta

theorem primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk
    (eta : Real) :
    rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta =
      rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta := by
  simpa [primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff] using
    primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk_of_assembled
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta

end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
