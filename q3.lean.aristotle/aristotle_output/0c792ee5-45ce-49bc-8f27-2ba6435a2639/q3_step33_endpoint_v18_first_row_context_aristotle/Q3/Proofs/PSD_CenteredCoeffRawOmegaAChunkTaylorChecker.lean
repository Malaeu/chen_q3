import Q3.Proofs.A3_Floor_Monotonicity
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkIntegralBoundsImport

set_option linter.mathlibStandardSet false
set_option autoImplicit false

/-!
Raw-Omega chunk Taylor/model certificate checker.

This file is the proof-producing backend layer between numerical certificate
search and the existing raw-Omega direct chunk-integral receiver.  A generator
may use external numerics to discover rational Taylor/model data, but Lean only
accepts a chunk once the model validity fields below prove actual analytic
enclosure and integral side conditions.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral

open MeasureTheory
open CenteredCoeffPayloadImport
open scoped BigOperators

/-- Evaluate a rational Taylor polynomial around a rational center. -/
def rawOmegaATaylorPolynomial
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    (eta : Real) : Real :=
  ∑ i : Fin (degree + 1),
    (coeff i : Real) * (eta - (center : Real)) ^ i.1

/-- Closed-form integral contribution of `(eta - center)^n` on `[L,U]`. -/
def rawOmegaTaylorPowerIntegral
    (center : Rat) (n : Nat) (L U : Real) : Real :=
  ((U - (center : Real)) ^ (n + 1) -
      (L - (center : Real)) ^ (n + 1)) / ((n + 1 : Nat) : Real)

/-- Closed-form integral of a raw-Omega Taylor polynomial on `[L,U]`. -/
def rawOmegaTaylorPolynomialIntegral
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    (L U : Real) : Real :=
  ∑ i : Fin (degree + 1),
    (coeff i : Real) * rawOmegaTaylorPowerIntegral center i.1 L U

/-- Generator-facing Taylor/model certificate data for one raw-Omega chunk.

The polynomial and remainder are rational data.  The accompanying `Valid`
predicate below is deliberately proof-bearing: until a stronger rational
side-condition checker is added, a payload must prove that this model really
encloses the raw-Omega integrand on the chunk and that the model integrals sit
inside the requested bounds. -/
structure RawOmegaATaylorModelCertificate
    (k : Nat) (ell x L U lower upper : Real) where
  center : Rat
  radius : Rat
  degree : Nat
  coeff : Fin (degree + 1) -> Rat
  remainder : Rat

namespace RawOmegaATaylorModelCertificate

def polynomial
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial cert.degree cert.center cert.coeff eta

def lowerModel
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) : Real :=
  cert.polynomial eta - (cert.remainder : Real)

def upperModel
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) : Real :=
  cert.polynomial eta + (cert.remainder : Real)

def polynomialIntegral
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    Real :=
  rawOmegaTaylorPolynomialIntegral cert.degree cert.center cert.coeff L U

def lowerModelIntegral
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    Real :=
  cert.polynomialIntegral - (U - L) * (cert.remainder : Real)

def upperModelIntegral
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    Real :=
  cert.polynomialIntegral + (U - L) * (cert.remainder : Real)

theorem rawOmegaATaylorPolynomial_continuous
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat) :
    Continuous (rawOmegaATaylorPolynomial degree center coeff) := by
  unfold rawOmegaATaylorPolynomial
  fun_prop

theorem rawOmegaATaylorPolynomial_differentiableAt
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    (eta : Real) :
    DifferentiableAt Real (rawOmegaATaylorPolynomial degree center coeff) eta := by
  unfold rawOmegaATaylorPolynomial
  fun_prop

theorem continuous_polynomial
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    Continuous cert.polynomial := by
  simpa [polynomial] using
    rawOmegaATaylorPolynomial_continuous cert.degree cert.center cert.coeff

theorem differentiableAt_polynomial
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) :
    DifferentiableAt Real cert.polynomial eta := by
  simpa [polynomial] using
    rawOmegaATaylorPolynomial_differentiableAt
      cert.degree cert.center cert.coeff eta

theorem polynomial_center
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    cert.polynomial (cert.center : Real) = (cert.coeff 0 : Real) := by
  unfold polynomial rawOmegaATaylorPolynomial
  rw [Fin.sum_univ_succ]
  simp

theorem continuous_lowerModel
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    Continuous cert.lowerModel := by
  simpa [lowerModel] using cert.continuous_polynomial.sub continuous_const

theorem continuous_upperModel
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    Continuous cert.upperModel := by
  simpa [upperModel] using cert.continuous_polynomial.add continuous_const

theorem integrableOn_lowerModel_Ioc
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    IntegrableOn cert.lowerModel (Set.Ioc L U) := by
  exact
    ((cert.continuous_lowerModel.integrableOn_Icc (a := L) (b := U)).mono_set
      Set.Ioc_subset_Icc_self)

theorem integrableOn_upperModel_Ioc
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    IntegrableOn cert.upperModel (Set.Ioc L U) := by
  exact
    ((cert.continuous_upperModel.integrableOn_Icc (a := L) (b := U)).mono_set
      Set.Ioc_subset_Icc_self)

theorem intervalIntegral_shifted_pow
    (center : Rat) (n : Nat) (L U : Real) :
    (∫ eta in L..U, (eta - (center : Real)) ^ n) =
      rawOmegaTaylorPowerIntegral center n L U := by
  calc
    (∫ eta in L..U, (eta - (center : Real)) ^ n) =
        ∫ eta in (L - (center : Real))..(U - (center : Real)), eta ^ n := by
          simpa using
            (intervalIntegral.integral_comp_sub_right
              (f := fun eta : Real => eta ^ n)
              (a := L) (b := U) ((center : Real)))
    _ = rawOmegaTaylorPowerIntegral center n L U := by
          simp [rawOmegaTaylorPowerIntegral, integral_pow]

theorem intervalIntegral_rawOmegaATaylorPolynomial
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    (L U : Real) :
    (∫ eta in L..U, rawOmegaATaylorPolynomial degree center coeff eta) =
      rawOmegaTaylorPolynomialIntegral degree center coeff L U := by
  unfold rawOmegaATaylorPolynomial rawOmegaTaylorPolynomialIntegral
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral_shifted_pow]
  · intro i hi
    have hcont : Continuous
        (fun eta : Real =>
          (coeff i : Real) * (eta - (center : Real)) ^ i.1) := by
      fun_prop
    exact hcont.intervalIntegrable L U

theorem setIntegral_Ioc_rawOmegaATaylorPolynomial_of_le
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    {L U : Real} (hLU : L <= U) :
    (∫ eta in Set.Ioc L U, rawOmegaATaylorPolynomial degree center coeff eta) =
      rawOmegaTaylorPolynomialIntegral degree center coeff L U := by
  rw [← intervalIntegral.integral_of_le hLU]
  exact intervalIntegral_rawOmegaATaylorPolynomial degree center coeff L U

theorem setIntegral_Ioc_polynomial_of_le
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLU : L <= U) :
    (∫ eta in Set.Ioc L U, cert.polynomial eta) =
      cert.polynomialIntegral := by
  simpa [polynomial, polynomialIntegral] using
    setIntegral_Ioc_rawOmegaATaylorPolynomial_of_le
      cert.degree cert.center cert.coeff hLU

theorem setIntegral_Ioc_lowerModel_of_le
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLU : L <= U) :
    (∫ eta in Set.Ioc L U, cert.lowerModel eta) =
      cert.lowerModelIntegral := by
  rw [← intervalIntegral.integral_of_le hLU]
  have hpoly : IntervalIntegrable cert.polynomial volume L U :=
    cert.continuous_polynomial.intervalIntegrable L U
  have hconst : IntervalIntegrable (fun _ : Real => (cert.remainder : Real))
      volume L U :=
    continuous_const.intervalIntegrable L U
  calc
    (∫ eta in L..U, cert.lowerModel eta) =
        (∫ eta in L..U, cert.polynomial eta) -
          ∫ eta in L..U, (cert.remainder : Real) := by
          simpa [lowerModel] using
            (intervalIntegral.integral_sub hpoly hconst)
    _ = cert.lowerModelIntegral := by
          rw [show (∫ eta in L..U, cert.polynomial eta) =
              cert.polynomialIntegral by
                simpa [polynomial, polynomialIntegral] using
                  intervalIntegral_rawOmegaATaylorPolynomial
                    cert.degree cert.center cert.coeff L U]
          rw [intervalIntegral.integral_const]
          simp [lowerModelIntegral, smul_eq_mul]

theorem setIntegral_Ioc_upperModel_of_le
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLU : L <= U) :
    (∫ eta in Set.Ioc L U, cert.upperModel eta) =
      cert.upperModelIntegral := by
  rw [← intervalIntegral.integral_of_le hLU]
  have hpoly : IntervalIntegrable cert.polynomial volume L U :=
    cert.continuous_polynomial.intervalIntegrable L U
  have hconst : IntervalIntegrable (fun _ : Real => (cert.remainder : Real))
      volume L U :=
    continuous_const.intervalIntegrable L U
  calc
    (∫ eta in L..U, cert.upperModel eta) =
        (∫ eta in L..U, cert.polynomial eta) +
          ∫ eta in L..U, (cert.remainder : Real) := by
          simpa [upperModel] using
            (intervalIntegral.integral_add hpoly hconst)
    _ = cert.upperModelIntegral := by
          rw [show (∫ eta in L..U, cert.polynomial eta) =
              cert.polynomialIntegral by
                simpa [polynomial, polynomialIntegral] using
                  intervalIntegral_rawOmegaATaylorPolynomial
                    cert.degree cert.center cert.coeff L U]
          rw [intervalIntegral.integral_const]
          simp [upperModelIntegral, smul_eq_mul]

/-- Validity contract for one Taylor/model chunk certificate.

The shape is intentionally semantic at this stage: the next generator layer can
refine these fields into purely rational checks, but the current theorem below
does not trust numerical integration output directly. -/
structure Valid
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    Prop where
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hChunkInRadius :
    ∀ eta ∈ Set.Ioc L U,
      |eta - (cert.center : Real)| <= (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hLowerInt : IntegrableOn cert.lowerModel (Set.Ioc L U)
  hUpperInt : IntegrableOn cert.upperModel (Set.Ioc L U)
  hLowerModel :
    ∀ eta ∈ Set.Ioc L U,
      cert.lowerModel eta <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x eta
  hUpperModel :
    ∀ eta ∈ Set.Ioc L U,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x eta <=
        cert.upperModel eta
  hIntegralLower : lower <= ∫ eta in Set.Ioc L U, cert.lowerModel eta
  hIntegralUpper : (∫ eta in Set.Ioc L U, cert.upperModel eta) <= upper

theorem chunkInRadius_of_endpoint_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real)) :
    ∀ eta ∈ Set.Ioc L U,
      |eta - (cert.center : Real)| <= (cert.radius : Real) := by
  intro eta heta
  have hlow : -(cert.radius : Real) <= eta - (cert.center : Real) := by
    nlinarith [hLeft, le_of_lt heta.1]
  have hhigh : eta - (cert.center : Real) <= (cert.radius : Real) := by
    nlinarith [heta.2, hRight]
  exact abs_le.mpr ⟨hlow, hhigh⟩

theorem abs_rawOmegaATaylorPolynomial_le_sum_abs_coeff_mul_radius
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    {eta radius : Real}
    (hEta : |eta - (center : Real)| <= radius) :
    |rawOmegaATaylorPolynomial degree center coeff eta| <=
      ∑ i : Fin (degree + 1),
        |(coeff i : Real)| * radius ^ i.1 := by
  unfold rawOmegaATaylorPolynomial
  calc
    |∑ i : Fin (degree + 1),
        (coeff i : Real) * (eta - (center : Real)) ^ i.1| <=
        ∑ i : Fin (degree + 1),
          |(coeff i : Real) * (eta - (center : Real)) ^ i.1| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i : Fin (degree + 1),
        |(coeff i : Real)| * radius ^ i.1 := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [abs_mul, abs_pow]
          exact
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg _) hEta i.1) (abs_nonneg _)

theorem rawOmegaATaylorPolynomial_bounds_of_sum_abs_coeff_mul_radius
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    {eta radius polyAbs : Real}
    (hEta : |eta - (center : Real)| <= radius)
    (hSum :
      (∑ i : Fin (degree + 1),
        |(coeff i : Real)| * radius ^ i.1) <= polyAbs) :
    -polyAbs <= rawOmegaATaylorPolynomial degree center coeff eta ∧
      rawOmegaATaylorPolynomial degree center coeff eta <= polyAbs := by
  exact
    abs_le.mp
      (le_trans
        (abs_rawOmegaATaylorPolynomial_le_sum_abs_coeff_mul_radius
          degree center coeff hEta)
        hSum)

theorem polynomial_bounds_of_sum_abs_coeff_mul_radius
    {k : Nat} {ell x L U lower upper eta polyAbs : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hEta : |eta - (cert.center : Real)| <= (cert.radius : Real))
    (hSum :
      (∑ i : Fin (cert.degree + 1),
        |(cert.coeff i : Real)| * (cert.radius : Real) ^ i.1) <=
          polyAbs) :
    -polyAbs <= cert.polynomial eta ∧ cert.polynomial eta <= polyAbs := by
  simpa [polynomial] using
    rawOmegaATaylorPolynomial_bounds_of_sum_abs_coeff_mul_radius
      cert.degree cert.center cert.coeff hEta hSum

theorem polynomial_value_bounds_of_sum_abs_coeff_mul_radius
    {k : Nat} {ell x L U lower upper polyLower polyUpper polyAbs : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hSum :
      (∑ i : Fin (cert.degree + 1),
        |(cert.coeff i : Real)| * (cert.radius : Real) ^ i.1) <=
          polyAbs)
    (hPolyLower : polyLower <= -polyAbs)
    (hPolyUpper : polyAbs <= polyUpper) :
    (∀ eta ∈ Set.Ioc L U, polyLower <= cert.polynomial eta) ∧
      (∀ eta ∈ Set.Ioc L U, cert.polynomial eta <= polyUpper) := by
  constructor
  · intro eta heta
    have hEta := cert.chunkInRadius_of_endpoint_bounds hLeft hRight eta heta
    have hPoly :=
      cert.polynomial_bounds_of_sum_abs_coeff_mul_radius hEta hSum
    exact le_trans hPolyLower hPoly.1
  · intro eta heta
    have hEta := cert.chunkInRadius_of_endpoint_bounds hLeft hRight eta heta
    have hPoly :=
      cert.polynomial_bounds_of_sum_abs_coeff_mul_radius hEta hSum
    exact le_trans hPoly.2 hPolyUpper

theorem Valid.of_model_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hProfileInt :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (hLowerModel :
      ∀ eta ∈ Set.Ioc L U,
        cert.lowerModel eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta)
    (hUpperModel :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta <=
          cert.upperModel eta)
    (hIntegralLower : lower <= ∫ eta in Set.Ioc L U, cert.lowerModel eta)
    (hIntegralUpper : (∫ eta in Set.Ioc L U, cert.upperModel eta) <= upper) :
    cert.Valid := by
  exact
    { hRadiusNonneg := hRadiusNonneg
      hRemainderNonneg := hRemainderNonneg
      hChunkInRadius := cert.chunkInRadius_of_endpoint_bounds hLeft hRight
      hProfileInt := hProfileInt
      hLowerInt := cert.integrableOn_lowerModel_Ioc
      hUpperInt := cert.integrableOn_upperModel_Ioc
      hLowerModel := hLowerModel
      hUpperModel := hUpperModel
      hIntegralLower := hIntegralLower
      hIntegralUpper := hIntegralUpper }

theorem Valid.of_model_integral_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hProfileInt :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (hLowerModel :
      ∀ eta ∈ Set.Ioc L U,
        cert.lowerModel eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta)
    (hUpperModel :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta <=
          cert.upperModel eta)
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_model_bounds cert hRadiusNonneg hRemainderNonneg hLeft hRight
      hProfileInt hLowerModel hUpperModel
      (by simpa [setIntegral_Ioc_lowerModel_of_le cert hLU] using hIntegralLower)
      (by simpa [setIntegral_Ioc_upperModel_of_le cert hLU] using hIntegralUpper)

theorem lower_upper_model_bounds_of_abs_error
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hAbs :
      ∀ eta ∈ Set.Ioc L U,
        abs
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) <= (cert.remainder : Real)) :
    (∀ eta ∈ Set.Ioc L U,
        cert.lowerModel eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta) ∧
      (∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta <=
          cert.upperModel eta) := by
  constructor
  · intro eta heta
    have hlow := (abs_le.mp (hAbs eta heta)).1
    dsimp [lowerModel]
    nlinarith
  · intro eta heta
    have hhigh := (abs_le.mp (hAbs eta heta)).2
    dsimp [upperModel]
    nlinarith

theorem abs_error_of_diff_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hDiffLower :
      ∀ eta ∈ Set.Ioc L U,
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta <=
          (cert.remainder : Real)) :
    ∀ eta ∈ Set.Ioc L U,
      abs
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta -
          cert.polynomial eta) <= (cert.remainder : Real) := by
  intro eta heta
  exact abs_le.mpr ⟨hDiffLower eta heta, hDiffUpper eta heta⟩

/-- Residual between the raw-Omega integrand and the generated Taylor
polynomial.  Keeping this as a named expression gives generators a smaller
target than repeatedly expanding the full analytic integrand. -/
def residual
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) : Real :=
  Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
      k ell x eta -
    cert.polynomial eta

theorem residual_differentiableAt
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) :
    DifferentiableAt Real cert.residual eta := by
  unfold residual
  exact
    (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand_differentiableAt
      k ell x eta).sub
        (cert.differentiableAt_polynomial eta)

theorem residual_deriv_eq
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) :
    deriv cert.residual eta =
      deriv
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x) eta -
        deriv cert.polynomial eta := by
  simpa [residual] using
    (deriv_sub
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand_differentiableAt
        k ell x eta)
      (cert.differentiableAt_polynomial eta))

theorem residual_differentiableOn_Icc
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta := by
  intro eta _heta
  exact cert.residual_differentiableAt eta

/-- Pointwise residual-anchor bound from raw-profile and Taylor-polynomial
value enclosures at the anchor.

This keeps the refined route honest: generated code still has to prove the
analytic raw value and polynomial value bounds at the concrete anchor, while
Lean only packages those bounds into the `hAnchorResidual` field required by
the residual-anchor finite-cover receivers. -/
theorem anchor_residual_abs_of_raw_poly_value_bounds_at
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor rawLower rawUpper polyLower polyUpper sampleRadius : Real}
    (hRawLower :
      rawLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor)
    (hRawUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor <=
        rawUpper)
    (hPolyLower : polyLower <= cert.polynomial anchor)
    (hPolyUpper : cert.polynomial anchor <= polyUpper)
    (hResidualLower : -sampleRadius <= rawLower - polyUpper)
    (hResidualUpper : rawUpper - polyLower <= sampleRadius) :
    |cert.residual anchor| <= sampleRadius := by
  have hLower : -sampleRadius <= cert.residual anchor := by
    unfold residual
    nlinarith
  have hUpper : cert.residual anchor <= sampleRadius := by
    unfold residual
    nlinarith
  exact abs_le.mpr ⟨hLower, hUpper⟩

/-- Sharp pointwise residual-anchor receiver at the Taylor center.

This is the preferred route-A landing surface for the current refined
subchunks: instead of proving a coarse product box for the raw integrand at the
anchor, generated code can prove the one exact analytic fact it needs,
namely that the raw value at the center is within `sampleRadius` of the
constant Taylor coefficient. -/
theorem anchor_residual_abs_of_raw_center_coeff_abs_bound
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor sampleRadius : Real}
    (hAnchor : anchor = (cert.center : Real))
    (hRawCoeffAbs :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius) :
    |cert.residual anchor| <= sampleRadius := by
  have hpoly : cert.polynomial anchor = (cert.coeff 0 : Real) := by
    rw [hAnchor, cert.polynomial_center]
  have hres :
      cert.residual anchor =
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor - (cert.coeff 0 : Real) := by
    unfold residual
    rw [hpoly]
  rw [hres]
  exact hRawCoeffAbs

/-- Prove the sharp raw-center-minus-coeff0 field from a pointwise raw value
enclosure and two rational comparisons against the Taylor constant
coefficient.

This is the generator-facing adapter for `hRawCenterCoeffAbs`: generated code
can emit a lower/upper enclosure for the raw Step22-Omega integrand at the
anchor, then close the absolute-value bound by comparing both endpoints to
`cert.coeff 0`. -/
theorem raw_center_coeff_abs_of_raw_value_bounds_at
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor rawLower rawUpper sampleRadius : Real}
    (hRawLower :
      rawLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor)
    (hRawUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor <=
        rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  have hLower :
      -sampleRadius <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor - (cert.coeff 0 : Real) := by
    nlinarith
  have hUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor - (cert.coeff 0 : Real) <=
        sampleRadius := by
    nlinarith
  exact abs_le.mpr ⟨hLower, hUpper⟩

/-- Turn a finite-grid residual envelope plus a local variation/Lipschitz
bound into the absolute residual bound required by `Valid`.

This is the generator-facing route after plain ball interval residual
subtraction proved too wide: the generator can prove small residuals at anchor
points and a separate analytic variation bound on each refined subchunk. -/
theorem abs_error_of_residual_anchor_envelope
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {sampleRadius slope mesh : Real}
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc L U,
        ∃ anchor ∈ Set.Ioc L U,
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
        |cert.residual eta - cert.residual anchor| <= slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)) :
    ∀ eta ∈ Set.Ioc L U,
      |cert.residual eta| <= (cert.remainder : Real) := by
  intro eta heta
  rcases hCover eta heta with ⟨anchor, hanchor, hdist, hsample⟩
  have hvar := hResidualVariation eta heta anchor hanchor
  have hvarMesh :
      |cert.residual eta - cert.residual anchor| <= slope * mesh := by
    exact le_trans hvar (mul_le_mul_of_nonneg_left hdist hSlopeNonneg)
  have htri :
      |cert.residual eta| <=
        |cert.residual eta - cert.residual anchor| +
          |cert.residual anchor| := by
    let a : Real := cert.residual eta - cert.residual anchor
    let b : Real := cert.residual anchor
    have hdecomp :
        cert.residual eta = a + b := by
      dsimp [a, b]
      ring
    calc
      |cert.residual eta| = |a + b| := by rw [hdecomp]
      _ <= |a| + |b| := abs_add_le a b
      _ =
          |cert.residual eta - cert.residual anchor| +
            |cert.residual anchor| := by
            rfl
  calc
    |cert.residual eta|
        <= |cert.residual eta - cert.residual anchor| +
          |cert.residual anchor| := htri
    _ <= slope * mesh + sampleRadius := add_le_add hvarMesh hsample
    _ = sampleRadius + slope * mesh := by ring
    _ <= (cert.remainder : Real) := hEnvelope

/-- Two-sided Taylor diff bounds from the residual anchor-envelope helper. -/
theorem diff_bounds_of_residual_anchor_envelope
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {sampleRadius slope mesh : Real}
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc L U,
        ∃ anchor ∈ Set.Ioc L U,
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
        |cert.residual eta - cert.residual anchor| <= slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)) :
    (∀ eta ∈ Set.Ioc L U,
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) ∧
      (∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta <=
          (cert.remainder : Real)) := by
  have hAbs :=
    cert.abs_error_of_residual_anchor_envelope hSlopeNonneg hCover
      hResidualVariation hEnvelope
  constructor
  · intro eta heta
    exact (abs_le.mp (by simpa [residual] using hAbs eta heta)).1
  · intro eta heta
    exact (abs_le.mp (by simpa [residual] using hAbs eta heta)).2

/-- Pointwise value enclosures for the raw-Omega integrand and the Taylor
polynomial on one chunk.  This is the next generator-facing layer before a
fully componentized raw-Omega checker: generated code may prove these bounds
from interval arithmetic, while Lean checks the arithmetic bridge to the
existing diff-bound constructor below. -/
structure ValueBounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (rawLower rawUpper polyLower polyUpper : Real) : Prop where
  hRawLower :
    ∀ eta ∈ Set.Ioc L U,
      rawLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x eta
  hRawUpper :
    ∀ eta ∈ Set.Ioc L U,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x eta <=
        rawUpper
  hPolyLower :
    ∀ eta ∈ Set.Ioc L U,
      polyLower <= cert.polynomial eta
  hPolyUpper :
    ∀ eta ∈ Set.Ioc L U,
      cert.polynomial eta <= polyUpper

/-- Component-wise enclosures for the raw-Omega integrand on one chunk.

The product fields deliberately keep the sign-sensitive interval arithmetic
outside this reusable lemma: generated code must still prove the two product
comparisons for its concrete rational component intervals. -/
structure RawIntegrandComponentBounds
    (k : Nat) (ell x L U omegaLower omegaUpper shapeSqLower shapeSqUpper
      cosLower cosUpper rawLower rawUpper : Real) : Prop where
  hOmegaLower :
    ∀ eta ∈ Set.Ioc L U,
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta
  hOmegaUpper :
    ∀ eta ∈ Set.Ioc L U,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
        omegaUpper
  hShapeSqLower :
    ∀ eta ∈ Set.Ioc L U,
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2
  hShapeSqUpper :
    ∀ eta ∈ Set.Ioc L U,
      (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
        shapeSqUpper
  hCosLower :
    ∀ eta ∈ Set.Ioc L U,
      cosLower <= Real.cos (eta * x)
  hCosUpper :
    ∀ eta ∈ Set.Ioc L U,
      Real.cos (eta * x) <= cosUpper
  hProductLower :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue
  hProductUpper :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper

theorem product_bounds_of_nonneg_boxes_and_abs_cos
    {scale omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
      cosAbs rawLower rawUpper : Real}
    (hScaleNonneg : 0 <= scale)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower : rawLower <= -(scale * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper : scale * omegaUpper * shapeSqUpper * cosAbs <= rawUpper) :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        rawLower <= scale * omega * shapeSq * cosValue ∧
          scale * omega * shapeSq * cosValue <= rawUpper := by
  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeLower
    hShapeUpper hCosLower hCosUpper
  have hOmegaNonneg : 0 <= omega :=
    le_trans hOmegaLowerNonneg hOmegaLower
  have hShapeNonneg : 0 <= shapeSq :=
    le_trans hShapeSqLowerNonneg hShapeLower
  have hOmegaUpperNonneg : 0 <= omegaUpper :=
    le_trans hOmegaNonneg hOmegaUpper
  have hShapeUpperNonneg : 0 <= shapeSqUpper :=
    le_trans hShapeNonneg hShapeUpper
  have hOmegaShape :
      omega * shapeSq <= omegaUpper * shapeSqUpper :=
    mul_le_mul hOmegaUpper hShapeUpper hShapeNonneg hOmegaUpperNonneg
  have hScaledOmegaShape :
      scale * (omega * shapeSq) <= scale * (omegaUpper * shapeSqUpper) :=
    mul_le_mul_of_nonneg_left hOmegaShape hScaleNonneg
  have hScaleOmegaShapeNonneg : 0 <= scale * omega * shapeSq := by
    exact mul_nonneg (mul_nonneg hScaleNonneg hOmegaNonneg) hShapeNonneg
  have hScaleUpperNonneg : 0 <= scale * omegaUpper * shapeSqUpper := by
    exact
      mul_nonneg (mul_nonneg hScaleNonneg hOmegaUpperNonneg)
        hShapeUpperNonneg
  have hScaleOmegaShapeUpper :
      scale * omega * shapeSq <= scale * omegaUpper * shapeSqUpper := by
    nlinarith [hScaledOmegaShape]
  have hCosAbs : |cosValue| <= cosAbs := by
    exact abs_le.mpr
      ⟨le_trans hCosLowerAbs hCosLower, le_trans hCosUpper hCosUpperAbs⟩
  have hAbsProduct :
      |scale * omega * shapeSq * cosValue| <=
        scale * omegaUpper * shapeSqUpper * cosAbs := by
    calc
      |scale * omega * shapeSq * cosValue|
          = |scale * omega * shapeSq| * |cosValue| := by
              rw [abs_mul]
      _ = (scale * omega * shapeSq) * |cosValue| := by
              rw [abs_of_nonneg hScaleOmegaShapeNonneg]
      _ ≤ (scale * omegaUpper * shapeSqUpper) * cosAbs := by
              exact
                mul_le_mul hScaleOmegaShapeUpper hCosAbs (abs_nonneg _)
                  hScaleUpperNonneg
  have hBox := abs_le.mp hAbsProduct
  constructor
  · exact le_trans hRawLower hBox.1
  · exact le_trans hBox.2 hRawUpper

theorem mul_right_interval_bounds_of_endpoint_bounds
    {a b x y lower upper : Real}
    (hax : a <= x) (hxb : x <= b)
    (hLowerA : lower <= a * y)
    (hLowerB : lower <= b * y)
    (hUpperA : a * y <= upper)
    (hUpperB : b * y <= upper) :
    lower <= x * y ∧ x * y <= upper := by
  have hab : a <= b := le_trans hax hxb
  by_cases hlt : a < b
  · have hden_pos : 0 < b - a := sub_pos.mpr hlt
    have hden_nonneg : 0 <= b - a := le_of_lt hden_pos
    have hden_ne : b - a ≠ 0 := ne_of_gt hden_pos
    let leftWeight : Real := (b - x) / (b - a)
    let rightWeight : Real := (x - a) / (b - a)
    have hLeftWeightNonneg : 0 <= leftWeight := by
      exact div_nonneg (sub_nonneg.mpr hxb) hden_nonneg
    have hRightWeightNonneg : 0 <= rightWeight := by
      exact div_nonneg (sub_nonneg.mpr hax) hden_nonneg
    have hWeights : leftWeight + rightWeight = 1 := by
      dsimp [leftWeight, rightWeight]
      field_simp [hden_ne]
      ring
    have hxmul :
        x * y = leftWeight * (a * y) + rightWeight * (b * y) := by
      dsimp [leftWeight, rightWeight]
      field_simp [hden_ne]
      ring
    have hLowerLeft :
        leftWeight * lower <= leftWeight * (a * y) :=
      mul_le_mul_of_nonneg_left hLowerA hLeftWeightNonneg
    have hLowerRight :
        rightWeight * lower <= rightWeight * (b * y) :=
      mul_le_mul_of_nonneg_left hLowerB hRightWeightNonneg
    have hLowerSum :=
      add_le_add hLowerLeft hLowerRight
    have hLowerWeights :
        leftWeight * lower + rightWeight * lower = lower := by
      calc
        leftWeight * lower + rightWeight * lower =
            (leftWeight + rightWeight) * lower := by ring
        _ = lower := by rw [hWeights]; ring
    have hUpperLeft :
        leftWeight * (a * y) <= leftWeight * upper :=
      mul_le_mul_of_nonneg_left hUpperA hLeftWeightNonneg
    have hUpperRight :
        rightWeight * (b * y) <= rightWeight * upper :=
      mul_le_mul_of_nonneg_left hUpperB hRightWeightNonneg
    have hUpperSum :=
      add_le_add hUpperLeft hUpperRight
    have hUpperWeights :
        leftWeight * upper + rightWeight * upper = upper := by
      calc
        leftWeight * upper + rightWeight * upper =
            (leftWeight + rightWeight) * upper := by ring
        _ = upper := by rw [hWeights]; ring
    constructor
    · rw [hxmul]
      rw [← hLowerWeights]
      exact hLowerSum
    · rw [hxmul]
      rw [← hUpperWeights]
      exact hUpperSum
  · have hba : b <= a := le_of_not_gt hlt
    have hEq : a = b := le_antisymm hab hba
    subst b
    have hxEq : x = a := le_antisymm hxb hax
    subst x
    exact ⟨hLowerA, hUpperA⟩

theorem mul_interval_bounds_of_four_corners
    {a b c d x y lower upper : Real}
    (hax : a <= x) (hxb : x <= b)
    (hcy : c <= y) (hyd : y <= d)
    (hLowerAC : lower <= a * c)
    (hLowerAD : lower <= a * d)
    (hLowerBC : lower <= b * c)
    (hLowerBD : lower <= b * d)
    (hUpperAC : a * c <= upper)
    (hUpperAD : a * d <= upper)
    (hUpperBC : b * c <= upper)
    (hUpperBD : b * d <= upper) :
    lower <= x * y ∧ x * y <= upper := by
  have hA :
      lower <= a * y ∧ a * y <= upper := by
    have h :=
      mul_right_interval_bounds_of_endpoint_bounds
        (a := c) (b := d) (x := y) (y := a)
        hcy hyd
        (by simpa [mul_comm] using hLowerAC)
        (by simpa [mul_comm] using hLowerAD)
        (by simpa [mul_comm] using hUpperAC)
        (by simpa [mul_comm] using hUpperAD)
    exact
      ⟨by simpa [mul_comm] using h.1,
        by simpa [mul_comm] using h.2⟩
  have hB :
      lower <= b * y ∧ b * y <= upper := by
    have h :=
      mul_right_interval_bounds_of_endpoint_bounds
        (a := c) (b := d) (x := y) (y := b)
        hcy hyd
        (by simpa [mul_comm] using hLowerBC)
        (by simpa [mul_comm] using hLowerBD)
        (by simpa [mul_comm] using hUpperBC)
        (by simpa [mul_comm] using hUpperBD)
    exact
      ⟨by simpa [mul_comm] using h.1,
        by simpa [mul_comm] using h.2⟩
  exact
    mul_right_interval_bounds_of_endpoint_bounds hax hxb
      hA.1 hB.1 hA.2 hB.2

theorem const_mul_mul_interval_bounds_of_four_corners
    {scale a b c d x y lower upper : Real}
    (hax : a <= x) (hxb : x <= b)
    (hcy : c <= y) (hyd : y <= d)
    (hLowerAC : lower <= scale * a * c)
    (hLowerAD : lower <= scale * a * d)
    (hLowerBC : lower <= scale * b * c)
    (hLowerBD : lower <= scale * b * d)
    (hUpperAC : scale * a * c <= upper)
    (hUpperAD : scale * a * d <= upper)
    (hUpperBC : scale * b * c <= upper)
    (hUpperBD : scale * b * d <= upper) :
    lower <= scale * x * y ∧ scale * x * y <= upper := by
  have hA :
      lower <= scale * a * y ∧ scale * a * y <= upper := by
    have h :=
      mul_right_interval_bounds_of_endpoint_bounds
        (a := c) (b := d) (x := y) (y := scale * a)
        hcy hyd
        (by
          calc
            lower <= scale * a * c := hLowerAC
            _ = c * (scale * a) := by ring)
        (by
          calc
            lower <= scale * a * d := hLowerAD
            _ = d * (scale * a) := by ring)
        (by
          calc
            c * (scale * a) = scale * a * c := by ring
            _ <= upper := hUpperAC)
        (by
          calc
            d * (scale * a) = scale * a * d := by ring
            _ <= upper := hUpperAD)
    exact
      ⟨by
        calc
          lower <= y * (scale * a) := h.1
          _ = scale * a * y := by ring,
        by
        calc
          scale * a * y = y * (scale * a) := by ring
          _ <= upper := h.2⟩
  have hB :
      lower <= scale * b * y ∧ scale * b * y <= upper := by
    have h :=
      mul_right_interval_bounds_of_endpoint_bounds
        (a := c) (b := d) (x := y) (y := scale * b)
        hcy hyd
        (by
          calc
            lower <= scale * b * c := hLowerBC
            _ = c * (scale * b) := by ring)
        (by
          calc
            lower <= scale * b * d := hLowerBD
            _ = d * (scale * b) := by ring)
        (by
          calc
            c * (scale * b) = scale * b * c := by ring
            _ <= upper := hUpperBC)
        (by
          calc
            d * (scale * b) = scale * b * d := by ring
            _ <= upper := hUpperBD)
    exact
      ⟨by
        calc
          lower <= y * (scale * b) := h.1
          _ = scale * b * y := by ring,
        by
        calc
          scale * b * y = y * (scale * b) := by ring
          _ <= upper := h.2⟩
  have h :=
    mul_right_interval_bounds_of_endpoint_bounds
      (a := a) (b := b) (x := x) (y := scale * y)
      hax hxb
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA.1)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hB.1)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA.2)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hB.2)
  exact
    ⟨by simpa [mul_comm, mul_left_comm, mul_assoc] using h.1,
      by simpa [mul_comm, mul_left_comm, mul_assoc] using h.2⟩

theorem scale_triple_product_interval_bounds_of_eight_corners
    {scale omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
      omega shapeSq cosValue rawLower rawUpper : Real}
    (hOmegaLower : omegaLower <= omega)
    (hOmegaUpper : omega <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSq)
    (hShapeSqUpper : shapeSq <= shapeSqUpper)
    (hCosLower : cosLower <= cosValue)
    (hCosUpper : cosValue <= cosUpper)
    (hLowerLLL : rawLower <= scale * omegaLower * shapeSqLower * cosLower)
    (hLowerLLU : rawLower <= scale * omegaLower * shapeSqLower * cosUpper)
    (hLowerLUL : rawLower <= scale * omegaLower * shapeSqUpper * cosLower)
    (hLowerLUU : rawLower <= scale * omegaLower * shapeSqUpper * cosUpper)
    (hLowerULL : rawLower <= scale * omegaUpper * shapeSqLower * cosLower)
    (hLowerULU : rawLower <= scale * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUL : rawLower <= scale * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUU : rawLower <= scale * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLL : scale * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLU : scale * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUL : scale * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUU : scale * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULL : scale * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperULU : scale * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUL : scale * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUU : scale * omegaUpper * shapeSqUpper * cosUpper <= rawUpper) :
    rawLower <= scale * omega * shapeSq * cosValue ∧
      scale * omega * shapeSq * cosValue <= rawUpper := by
  have hLowerOmega :
      rawLower <= scale * omegaLower * shapeSq * cosValue ∧
        scale * omegaLower * shapeSq * cosValue <= rawUpper :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := scale * omegaLower)
      hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerLLL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerLLU)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerLUL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerLUU)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperLLL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperLLU)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperLUL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperLUU)
  have hUpperOmega :
      rawLower <= scale * omegaUpper * shapeSq * cosValue ∧
        scale * omegaUpper * shapeSq * cosValue <= rawUpper :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := scale * omegaUpper)
      hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerULL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerULU)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerUUL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerUUU)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperULL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperULU)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperUUL)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperUUU)
  have h :=
    mul_right_interval_bounds_of_endpoint_bounds
      (a := omegaLower) (b := omegaUpper) (x := omega)
      (y := scale * shapeSq * cosValue)
      hOmegaLower hOmegaUpper
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerOmega.1)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperOmega.1)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerOmega.2)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperOmega.2)
  exact
    ⟨by simpa [mul_comm, mul_left_comm, mul_assoc] using h.1,
      by simpa [mul_comm, mul_left_comm, mul_assoc] using h.2⟩

theorem product_bounds_of_eight_corners
    {ell omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
      rawLower rawUpper : Real}
    (hLowerLLL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosLower)
    (hLowerLLU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper)
    (hLowerLUL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower)
    (hLowerLUU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper)
    (hLowerULL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower)
    (hLowerULU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLL : (ell / Real.pi) * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLU : (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUL : (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUU : (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULL : (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperULU : (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUL : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUU : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper <= rawUpper) :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue ∧
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper := by
  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower
    hShapeSqUpper hCosLower hCosUpper
  exact
    scale_triple_product_interval_bounds_of_eight_corners
      (scale := ell / Real.pi)
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hLowerLLL hLowerLLU hLowerLUL hLowerLUU hLowerULL hLowerULU
      hLowerUUL hLowerUUU hUpperLLL hUpperLLU hUpperLUL hUpperLUU
      hUpperULL hUpperULU hUpperUUL hUpperUUU

theorem scale_interval_triple_product_interval_bounds_of_sixteen_corners
    {scaleLower scaleUpper scale omegaLower omegaUpper shapeSqLower shapeSqUpper
      cosLower cosUpper omega shapeSq cosValue rawLower rawUpper : Real}
    (hScaleLower : scaleLower <= scale)
    (hScaleUpper : scale <= scaleUpper)
    (hOmegaLower : omegaLower <= omega)
    (hOmegaUpper : omega <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSq)
    (hShapeSqUpper : shapeSq <= shapeSqUpper)
    (hCosLower : cosLower <= cosValue)
    (hCosUpper : cosValue <= cosUpper)
    (hLowerLLLL :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosLower)
    (hLowerLLLU :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosUpper)
    (hLowerLLUL :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosLower)
    (hLowerLLUU :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosUpper)
    (hLowerLULL :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosLower)
    (hLowerLULU :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosUpper)
    (hLowerLUUL :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosLower)
    (hLowerLUUU :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosUpper)
    (hLowerULLL :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosLower)
    (hLowerULLU :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosUpper)
    (hLowerULUL :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosLower)
    (hLowerULUU :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosUpper)
    (hLowerUULL :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosLower)
    (hLowerUULU :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUUL :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUUU :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLLL :
      scaleLower * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLLU :
      scaleLower * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLLUL :
      scaleLower * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLLUU :
      scaleLower * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperLULL :
      scaleLower * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperLULU :
      scaleLower * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUUL :
      scaleLower * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUUU :
      scaleLower * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULLL :
      scaleUpper * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperULLU :
      scaleUpper * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperULUL :
      scaleUpper * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperULUU :
      scaleUpper * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperUULL :
      scaleUpper * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperUULU :
      scaleUpper * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUUL :
      scaleUpper * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUUU :
      scaleUpper * omegaUpper * shapeSqUpper * cosUpper <= rawUpper) :
    rawLower <= scale * omega * shapeSq * cosValue ∧
      scale * omega * shapeSq * cosValue <= rawUpper := by
  have hLowerScale :
      rawLower <= scaleLower * omega * shapeSq * cosValue ∧
        scaleLower * omega * shapeSq * cosValue <= rawUpper :=
    scale_triple_product_interval_bounds_of_eight_corners
      (scale := scaleLower)
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hLowerLLLL hLowerLLLU hLowerLLUL hLowerLLUU hLowerLULL hLowerLULU
      hLowerLUUL hLowerLUUU hUpperLLLL hUpperLLLU hUpperLLUL hUpperLLUU
      hUpperLULL hUpperLULU hUpperLUUL hUpperLUUU
  have hUpperScale :
      rawLower <= scaleUpper * omega * shapeSq * cosValue ∧
        scaleUpper * omega * shapeSq * cosValue <= rawUpper :=
    scale_triple_product_interval_bounds_of_eight_corners
      (scale := scaleUpper)
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hLowerULLL hLowerULLU hLowerULUL hLowerULUU hLowerUULL hLowerUULU
      hLowerUUUL hLowerUUUU hUpperULLL hUpperULLU hUpperULUL hUpperULUU
      hUpperUULL hUpperUULU hUpperUUUL hUpperUUUU
  have h :=
    mul_right_interval_bounds_of_endpoint_bounds
      (a := scaleLower) (b := scaleUpper) (x := scale)
      (y := omega * shapeSq * cosValue)
      hScaleLower hScaleUpper
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerScale.1)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperScale.1)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hLowerScale.2)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hUpperScale.2)
  exact
    ⟨by simpa [mul_comm, mul_left_comm, mul_assoc] using h.1,
      by simpa [mul_comm, mul_left_comm, mul_assoc] using h.2⟩

theorem product_bounds_of_scale_interval_and_sixteen_corners
    {scaleLower scaleUpper ell omegaLower omegaUpper shapeSqLower shapeSqUpper
      cosLower cosUpper rawLower rawUpper : Real}
    (hScaleLower : scaleLower <= ell / Real.pi)
    (hScaleUpper : ell / Real.pi <= scaleUpper)
    (hLowerLLLL :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosLower)
    (hLowerLLLU :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosUpper)
    (hLowerLLUL :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosLower)
    (hLowerLLUU :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosUpper)
    (hLowerLULL :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosLower)
    (hLowerLULU :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosUpper)
    (hLowerLUUL :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosLower)
    (hLowerLUUU :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosUpper)
    (hLowerULLL :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosLower)
    (hLowerULLU :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosUpper)
    (hLowerULUL :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosLower)
    (hLowerULUU :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosUpper)
    (hLowerUULL :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosLower)
    (hLowerUULU :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUUL :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUUU :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLLL :
      scaleLower * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLLU :
      scaleLower * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLLUL :
      scaleLower * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLLUU :
      scaleLower * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperLULL :
      scaleLower * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperLULU :
      scaleLower * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUUL :
      scaleLower * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUUU :
      scaleLower * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULLL :
      scaleUpper * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperULLU :
      scaleUpper * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperULUL :
      scaleUpper * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperULUU :
      scaleUpper * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperUULL :
      scaleUpper * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperUULU :
      scaleUpper * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUUL :
      scaleUpper * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUUU :
      scaleUpper * omegaUpper * shapeSqUpper * cosUpper <= rawUpper) :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue ∧
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper := by
  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower
    hShapeSqUpper hCosLower hCosUpper
  exact
    scale_interval_triple_product_interval_bounds_of_sixteen_corners
      (scale := ell / Real.pi)
      hScaleLower hScaleUpper hOmegaLower hOmegaUpper hShapeSqLower
      hShapeSqUpper hCosLower hCosUpper hLowerLLLL hLowerLLLU hLowerLLUL
      hLowerLLUU hLowerLULL hLowerLULU hLowerLUUL hLowerLUUU hLowerULLL
      hLowerULLU hLowerULUL hLowerULUU hLowerUULL hLowerUULU hLowerUUUL
      hLowerUUUU hUpperLLLL hUpperLLLU hUpperLLUL hUpperLLUU hUpperLULL
      hUpperLULU hUpperLUUL hUpperLUUU hUpperULLL hUpperULLU hUpperULUL
      hUpperULUU hUpperUULL hUpperUULU hUpperUUUL hUpperUUUU

/-- Direct symmetric product box for the active raw-Omega component payload.
This avoids a generated 16-corner proof when the available component boxes have
the simple form `scale ∈ [0,scaleUpper]`, `omega ∈ [-M,M]`,
`shapeSq ∈ [0,S]`, and `cos ∈ [-1,1]`. -/
theorem product_bounds_of_scale_abs_box
    {scale scaleUpper omegaMajorant shapeSqUpper omega shapeSq cosValue : Real}
    (hScaleNonneg : 0 <= scale)
    (hScaleUpper : scale <= scaleUpper)
    (hScaleUpperNonneg : 0 <= scaleUpper)
    (hOmegaMajorantNonneg : 0 <= omegaMajorant)
    (hShapeSqUpperNonneg : 0 <= shapeSqUpper)
    (hOmegaLower : -omegaMajorant <= omega)
    (hOmegaUpper : omega <= omegaMajorant)
    (hShapeSqLower : 0 <= shapeSq)
    (hShapeSqUpper : shapeSq <= shapeSqUpper)
    (hCosLower : -1 <= cosValue)
    (hCosUpper : cosValue <= 1) :
    -(scaleUpper * omegaMajorant * shapeSqUpper) <=
        scale * omega * shapeSq * cosValue ∧
      scale * omega * shapeSq * cosValue <=
        scaleUpper * omegaMajorant * shapeSqUpper := by
  have hScaleAbs : |scale| <= scaleUpper := by
    simpa [abs_of_nonneg hScaleNonneg] using hScaleUpper
  have hOmegaAbs : |omega| <= omegaMajorant :=
    abs_le.mpr ⟨hOmegaLower, hOmegaUpper⟩
  have hShapeAbs : |shapeSq| <= shapeSqUpper := by
    simpa [abs_of_nonneg hShapeSqLower] using hShapeSqUpper
  have hCosAbs : |cosValue| <= (1 : Real) :=
    abs_le.mpr ⟨hCosLower, hCosUpper⟩
  have hprod_abs :
      |scale * omega * shapeSq * cosValue| <=
        scaleUpper * omegaMajorant * shapeSqUpper := by
    calc
      |scale * omega * shapeSq * cosValue| =
          |scale| * |omega| * |shapeSq| * |cosValue| := by
          simp [abs_mul, mul_assoc]
      _ <= scaleUpper * omegaMajorant * shapeSqUpper * (1 : Real) := by
          gcongr
      _ = scaleUpper * omegaMajorant * shapeSqUpper := by
          ring
  exact abs_le.mp hprod_abs

theorem RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds
    {k : Nat} {ell x L U omegaLower omegaUpper shapeSqLower shapeSqUpper
      cosLower cosUpper cosAbs rawLower rawUpper : Real}
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc L U,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc L U,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc L U,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc L U,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc L U,
        Real.cos (eta * x) <= cosUpper)
    (hScaleNonneg : 0 <= ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower : rawLower <= -((ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs <= rawUpper) :
    RawIntegrandComponentBounds k ell x L U omegaLower omegaUpper
      shapeSqLower shapeSqUpper cosLower cosUpper rawLower rawUpper := by
  refine
    { hOmegaLower := hOmegaLower
      hOmegaUpper := hOmegaUpper
      hShapeSqLower := hShapeSqLower
      hShapeSqUpper := hShapeSqUpper
      hCosLower := hCosLower
      hCosUpper := hCosUpper
      hProductLower := ?_
      hProductUpper := ?_ }
  · intro omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeLower'
      hShapeUpper' hCosLower' hCosUpper'
    exact
      (product_bounds_of_nonneg_boxes_and_abs_cos
        hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
        hCosUpperAbs hRawLower hRawUpper
        omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeLower'
        hShapeUpper' hCosLower' hCosUpper').1
  · intro omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeLower'
      hShapeUpper' hCosLower' hCosUpper'
    exact
      (product_bounds_of_nonneg_boxes_and_abs_cos
        hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
        hCosUpperAbs hRawLower hRawUpper
        omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeLower'
        hShapeUpper' hCosLower' hCosUpper').2

theorem RawIntegrandComponentBounds.of_product_bounds
    {k : Nat} {ell x L U omegaLower omegaUpper shapeSqLower shapeSqUpper
      cosLower cosUpper rawLower rawUpper : Real}
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc L U,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc L U,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc L U,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc L U,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc L U,
        Real.cos (eta * x) <= cosUpper)
    (hProductLower :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue)
    (hProductUpper :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper) :
    RawIntegrandComponentBounds k ell x L U omegaLower omegaUpper
      shapeSqLower shapeSqUpper cosLower cosUpper rawLower rawUpper :=
  { hOmegaLower := hOmegaLower
    hOmegaUpper := hOmegaUpper
    hShapeSqLower := hShapeSqLower
    hShapeSqUpper := hShapeSqUpper
    hCosLower := hCosLower
    hCosUpper := hCosUpper
    hProductLower := hProductLower
    hProductUpper := hProductUpper }

theorem rawOmegaAIntegrand_value_bounds_of_component_bounds
    {k : Nat} {ell x L U omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper : Real}
    (h :
      RawIntegrandComponentBounds k ell x L U omegaLower omegaUpper
        shapeSqLower shapeSqUpper cosLower cosUpper rawLower rawUpper) :
    (∀ eta ∈ Set.Ioc L U,
        rawLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta) ∧
      (∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta <= rawUpper) := by
  constructor
  · intro eta heta
    have hprod :=
      h.hProductLower
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
        ((centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
        (Real.cos (eta * x))
        (h.hOmegaLower eta heta) (h.hOmegaUpper eta heta)
        (h.hShapeSqLower eta heta) (h.hShapeSqUpper eta heta)
        (h.hCosLower eta heta) (h.hCosUpper eta heta)
    simpa
      [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand]
      using hprod
  · intro eta heta
    have hprod :=
      h.hProductUpper
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
        ((centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
        (Real.cos (eta * x))
        (h.hOmegaLower eta heta) (h.hOmegaUpper eta heta)
        (h.hShapeSqLower eta heta) (h.hShapeSqUpper eta heta)
        (h.hCosLower eta heta) (h.hCosUpper eta heta)
    simpa
      [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand]
      using hprod

/-- Pointwise raw-Omega integrand bounds from component bounds at one anchor.

This is the anchor-only analogue of
`rawOmegaAIntegrand_value_bounds_of_component_bounds`.  It is the route-B
landing surface for `hAnchorResidual`: generated code can prove Omega,
transform-square, cosine, and product bounds only at the chosen anchor instead
of producing an interval proof over the whole subchunk. -/
theorem rawOmegaAIntegrand_value_bounds_at_of_component_bounds
    {k : Nat} {ell x anchor omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper : Real}
    (hOmegaLower :
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaUpper)
    (hShapeSqLower :
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hCosLower : cosLower <= Real.cos (anchor * x))
    (hCosUpper : Real.cos (anchor * x) <= cosUpper)
    (hProductLower :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue)
    (hProductUpper :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper) :
    rawLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor <= rawUpper := by
  constructor
  · have hprod :=
      hProductLower
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
        ((centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
        (Real.cos (anchor * x))
        hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
    simpa
      [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand]
      using hprod
  · have hprod :=
      hProductUpper
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
        ((centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
        (Real.cos (anchor * x))
        hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
    simpa
      [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand]
      using hprod

/-- Pointwise raw-Omega integrand bounds at an anchor from interval component
bounds on the parent subchunk.

This is a thin generator bridge: existing payload seeds already know how to
prove Omega, transform-square, and cosine boxes on `(L,U]`, while the current
sharp anchor receiver only needs those facts at the Taylor center.  The only
extra local fact is `anchor ∈ (L,U]`. -/
theorem rawOmegaAIntegrand_value_bounds_at_of_interval_component_bounds
    {k : Nat} {ell x L U anchor omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper : Real}
    (hAnchorIn : anchor ∈ Set.Ioc L U)
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc L U,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc L U,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc L U,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc L U,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc L U,
        Real.cos (eta * x) <= cosUpper)
    (hProductLower :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue)
    (hProductUpper :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper) :
    rawLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor <= rawUpper := by
  exact
    rawOmegaAIntegrand_value_bounds_at_of_component_bounds
      (k := k) (ell := ell) (x := x) (anchor := anchor)
      (omegaLower := omegaLower) (omegaUpper := omegaUpper)
      (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
      (cosLower := cosLower) (cosUpper := cosUpper)
      (rawLower := rawLower) (rawUpper := rawUpper)
      (hOmegaLower anchor hAnchorIn) (hOmegaUpper anchor hAnchorIn)
      (hShapeSqLower anchor hAnchorIn) (hShapeSqUpper anchor hAnchorIn)
      (hCosLower anchor hAnchorIn) (hCosUpper anchor hAnchorIn)
      hProductLower hProductUpper

/-- Sharp raw-center-minus-coeff0 bound from pointwise raw component bounds.

This composes the anchor raw-value component receiver with
`raw_center_coeff_abs_of_raw_value_bounds_at`, so generated code can prove
Omega, transform-square, cosine, product, and coeff0 comparison facts without
constructing the raw-value interval proof manually. -/
theorem raw_center_coeff_abs_of_raw_component_bounds_at
    {k : Nat} {ell x L U lower upper omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hOmegaLower :
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaUpper)
    (hShapeSqLower :
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hCosLower : cosLower <= Real.cos (anchor * x))
    (hCosUpper : Real.cos (anchor * x) <= cosUpper)
    (hProductLower :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue)
    (hProductUpper :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  have hRaw :=
    rawOmegaAIntegrand_value_bounds_at_of_component_bounds
      (k := k) (ell := ell) (x := x) (anchor := anchor)
      (omegaLower := omegaLower) (omegaUpper := omegaUpper)
      (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
      (cosLower := cosLower) (cosUpper := cosUpper)
      (rawLower := rawLower) (rawUpper := rawUpper)
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hProductLower hProductUpper
  exact
    cert.raw_center_coeff_abs_of_raw_value_bounds_at
      hRaw.1 hRaw.2 hCoeffLower hCoeffUpper

/-- Sharp raw-center-minus-coeff0 bound from interval raw component bounds.

This is the interval-component version of
`raw_center_coeff_abs_of_raw_component_bounds_at`: generated code can reuse
the existing `(L,U]` Omega/shape/cos proof snippets and only provide the
already-seeded anchor-membership fact to land at the sharp center receiver. -/
theorem raw_center_coeff_abs_of_interval_raw_component_bounds_at
    {k : Nat} {ell x L U lower upper omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hAnchorIn : anchor ∈ Set.Ioc L U)
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc L U,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc L U,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc L U,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc L U,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc L U,
        Real.cos (eta * x) <= cosUpper)
    (hProductLower :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue)
    (hProductUpper :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  exact
    cert.raw_center_coeff_abs_of_raw_component_bounds_at
      (hOmegaLower anchor hAnchorIn) (hOmegaUpper anchor hAnchorIn)
      (hShapeSqLower anchor hAnchorIn) (hShapeSqUpper anchor hAnchorIn)
      (hCosLower anchor hAnchorIn) (hCosUpper anchor hAnchorIn)
      hProductLower hProductUpper hCoeffLower hCoeffUpper

/-- Generator-facing corner-check receiver for `hRawCenterCoeffAbs`.

The component boxes are analytic inputs, while the 16 product corner
comparisons and two coeff0 comparisons are rational arithmetic inputs.  Lean
turns them into the sharp raw-center-minus-coeff0 field through the generic
component receiver. -/
theorem raw_center_coeff_abs_of_raw_component_corner_bounds_at
    {k : Nat} {ell x L U lower upper omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hOmegaLower :
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaUpper)
    (hShapeSqLower :
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hCosLower : cosLower <= Real.cos (anchor * x))
    (hCosUpper : Real.cos (anchor * x) <= cosUpper)
    (hLowerLLL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosLower)
    (hLowerLLU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper)
    (hLowerLUL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower)
    (hLowerLUU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper)
    (hLowerULL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower)
    (hLowerULU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLL : (ell / Real.pi) * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLU : (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUL : (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUU : (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULL : (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperULU : (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUL : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUU : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  exact
    cert.raw_center_coeff_abs_of_raw_component_bounds_at
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      (fun omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper' =>
        (product_bounds_of_eight_corners
          (ell := ell) (omegaLower := omegaLower) (omegaUpper := omegaUpper)
          (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
          (cosLower := cosLower) (cosUpper := cosUpper)
          (rawLower := rawLower) (rawUpper := rawUpper)
          hLowerLLL hLowerLLU hLowerLUL hLowerLUU hLowerULL hLowerULU
          hLowerUUL hLowerUUU hUpperLLL hUpperLLU hUpperLUL hUpperLUU
          hUpperULL hUpperULU hUpperUUL hUpperUUU
          omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper').1)
      (fun omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper' =>
        (product_bounds_of_eight_corners
          (ell := ell) (omegaLower := omegaLower) (omegaUpper := omegaUpper)
          (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
          (cosLower := cosLower) (cosUpper := cosUpper)
          (rawLower := rawLower) (rawUpper := rawUpper)
          hLowerLLL hLowerLLU hLowerLUL hLowerLUU hLowerULL hLowerULU
          hLowerUUL hLowerUUU hUpperLLL hUpperLLU hUpperLUL hUpperLUU
          hUpperULL hUpperULU hUpperUUL hUpperUUU
          omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper').2)
      hCoeffLower hCoeffUpper

/-- Generator-facing corner-check receiver from interval component boxes.

This combines the old interval component proof snippets with the current
corner arithmetic receiver.  It is the practical route for generated
`hRawCenterCoeffAbs`: component proofs stay interval-level, while the sharp
anchor result follows by `hAnchorIn`. -/
theorem raw_center_coeff_abs_of_interval_raw_component_corner_bounds_at
    {k : Nat} {ell x L U lower upper omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hAnchorIn : anchor ∈ Set.Ioc L U)
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc L U,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc L U,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc L U,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc L U,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc L U,
        Real.cos (eta * x) <= cosUpper)
    (hLowerLLL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosLower)
    (hLowerLLU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper)
    (hLowerLUL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower)
    (hLowerLUU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper)
    (hLowerULL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower)
    (hLowerULU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLL : (ell / Real.pi) * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLU : (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUL : (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUU : (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULL : (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperULU : (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUL : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUU : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  exact
    cert.raw_center_coeff_abs_of_raw_component_corner_bounds_at
      (hOmegaLower anchor hAnchorIn) (hOmegaUpper anchor hAnchorIn)
      (hShapeSqLower anchor hAnchorIn) (hShapeSqUpper anchor hAnchorIn)
      (hCosLower anchor hAnchorIn) (hCosUpper anchor hAnchorIn)
      hLowerLLL hLowerLLU hLowerLUL hLowerLUU hLowerULL hLowerULU
      hLowerUUL hLowerUUU hUpperLLL hUpperLLU hUpperLUL hUpperLUU
      hUpperULL hUpperULU hUpperUUL hUpperUUU hCoeffLower hCoeffUpper

/-- Generator-facing corner-check receiver from local interval component boxes.

This is the anchor-local version of
`raw_center_coeff_abs_of_interval_raw_component_corner_bounds_at`.  The Taylor
certificate still lives on its window `(L,U]`, but the component enclosures may
be proved on a smaller auxiliary interval `(a,b]` that only has to contain the
anchor.  This keeps the sharp `hRawCenterCoeffAbs` route from inheriting the
full refined-subchunk width when the generated proof only needs the center
value. -/
theorem raw_center_coeff_abs_of_local_interval_raw_component_corner_bounds_at
    {k : Nat} {ell x L U lower upper a b omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc a b,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc a b,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc a b,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc a b,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc a b,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc a b,
        Real.cos (eta * x) <= cosUpper)
    (hLowerLLL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosLower)
    (hLowerLLU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper)
    (hLowerLUL : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower)
    (hLowerLUU : rawLower <= (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper)
    (hLowerULL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower)
    (hLowerULU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUL : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUU : rawLower <= (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLL : (ell / Real.pi) * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLU : (ell / Real.pi) * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUL : (ell / Real.pi) * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUU : (ell / Real.pi) * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULL : (ell / Real.pi) * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperULU : (ell / Real.pi) * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUL : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUU : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  exact
    cert.raw_center_coeff_abs_of_raw_component_corner_bounds_at
      (hOmegaLower anchor hAnchorIn) (hOmegaUpper anchor hAnchorIn)
      (hShapeSqLower anchor hAnchorIn) (hShapeSqUpper anchor hAnchorIn)
      (hCosLower anchor hAnchorIn) (hCosUpper anchor hAnchorIn)
      hLowerLLL hLowerLLU hLowerLUL hLowerLUU hLowerULL hLowerULU
      hLowerUUL hLowerUUU hUpperLLL hUpperLLU hUpperLUL hUpperLUU
      hUpperULL hUpperULU hUpperUUL hUpperUUU hCoeffLower hCoeffUpper

/-- Generator-facing local component receiver with a rational scale interval.

This is the active sharp arithmetic shape for tiny `hRawCenterCoeffAbs`
payloads: component boxes may live on an auxiliary `(a,b]` around the anchor,
and generated product checks use a rational enclosure
`scaleLower <= ell / Real.pi <= scaleUpper` instead of arithmetic directly
against the transcendental term `(ell / Real.pi)`. -/
theorem raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at
    {k : Nat} {ell x L U lower upper a b scaleLower scaleUpper
      omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
      rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc a b,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc a b,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc a b,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc a b,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc a b,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc a b,
        Real.cos (eta * x) <= cosUpper)
    (hScaleLower : scaleLower <= ell / Real.pi)
    (hScaleUpper : ell / Real.pi <= scaleUpper)
    (hLowerLLLL :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosLower)
    (hLowerLLLU :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosUpper)
    (hLowerLLUL :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosLower)
    (hLowerLLUU :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosUpper)
    (hLowerLULL :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosLower)
    (hLowerLULU :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosUpper)
    (hLowerLUUL :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosLower)
    (hLowerLUUU :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosUpper)
    (hLowerULLL :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosLower)
    (hLowerULLU :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosUpper)
    (hLowerULUL :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosLower)
    (hLowerULUU :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosUpper)
    (hLowerUULL :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosLower)
    (hLowerUULU :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUUL :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUUU :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLLL :
      scaleLower * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLLU :
      scaleLower * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLLUL :
      scaleLower * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLLUU :
      scaleLower * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperLULL :
      scaleLower * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperLULU :
      scaleLower * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUUL :
      scaleLower * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUUU :
      scaleLower * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULLL :
      scaleUpper * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperULLU :
      scaleUpper * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperULUL :
      scaleUpper * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperULUU :
      scaleUpper * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperUULL :
      scaleUpper * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperUULU :
      scaleUpper * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUUL :
      scaleUpper * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUUU :
      scaleUpper * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  exact
    cert.raw_center_coeff_abs_of_raw_component_bounds_at
      (hOmegaLower anchor hAnchorIn) (hOmegaUpper anchor hAnchorIn)
      (hShapeSqLower anchor hAnchorIn) (hShapeSqUpper anchor hAnchorIn)
      (hCosLower anchor hAnchorIn) (hCosUpper anchor hAnchorIn)
      (fun omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper' =>
        (product_bounds_of_scale_interval_and_sixteen_corners
          (scaleLower := scaleLower) (scaleUpper := scaleUpper) (ell := ell)
          (omegaLower := omegaLower) (omegaUpper := omegaUpper)
          (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
          (cosLower := cosLower) (cosUpper := cosUpper)
          (rawLower := rawLower) (rawUpper := rawUpper)
          hScaleLower hScaleUpper
          hLowerLLLL hLowerLLLU hLowerLLUL hLowerLLUU hLowerLULL
          hLowerLULU hLowerLUUL hLowerLUUU hLowerULLL hLowerULLU
          hLowerULUL hLowerULUU hLowerUULL hLowerUULU hLowerUUUL
          hLowerUUUU hUpperLLLL hUpperLLLU hUpperLLUL hUpperLLUU
          hUpperLULL hUpperLULU hUpperLUUL hUpperLUUU hUpperULLL
          hUpperULLU hUpperULUL hUpperULUU hUpperUULL hUpperUULU
          hUpperUUUL hUpperUUUU
          omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper').1)
      (fun omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper' =>
        (product_bounds_of_scale_interval_and_sixteen_corners
          (scaleLower := scaleLower) (scaleUpper := scaleUpper) (ell := ell)
          (omegaLower := omegaLower) (omegaUpper := omegaUpper)
          (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
          (cosLower := cosLower) (cosUpper := cosUpper)
          (rawLower := rawLower) (rawUpper := rawUpper)
          hScaleLower hScaleUpper
          hLowerLLLL hLowerLLLU hLowerLLUL hLowerLLUU hLowerLULL
          hLowerLULU hLowerLUUL hLowerLUUU hLowerULLL hLowerULLU
          hLowerULUL hLowerULUU hLowerUULL hLowerUULU hLowerUUUL
          hLowerUUUU hUpperLLLL hUpperLLLU hUpperLLUL hUpperLLUU
          hUpperLULL hUpperLULU hUpperLUUL hUpperLUUU hUpperULLL
          hUpperULLU hUpperULUL hUpperULUU hUpperUULL hUpperUULU
          hUpperUUUL hUpperUUUU
          omega shapeSq cosValue hOmegaLower' hOmegaUpper' hShapeSqLower'
          hShapeSqUpper' hCosLower' hCosUpper').2)
      hCoeffLower hCoeffUpper

/-- Zero-distance variant of the local scale-interval receiver.

For the current selected `row = 0` refined subchunks, the cosine component is
identically `1`, so generated payloads only need the rational comparisons
`cosLower <= 1` and `1 <= cosUpper` instead of interval cosine proofs. -/
theorem raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at_zero_distance
    {k : Nat} {ell L U lower upper a b scaleLower scaleUpper
      omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
      rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell 0 L U lower upper)
    {anchor : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc a b,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc a b,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc a b,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc a b,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLowerOne : cosLower <= 1)
    (hCosUpperOne : (1 : Real) <= cosUpper)
    (hScaleLower : scaleLower <= ell / Real.pi)
    (hScaleUpper : ell / Real.pi <= scaleUpper)
    (hLowerLLLL :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosLower)
    (hLowerLLLU :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosUpper)
    (hLowerLLUL :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosLower)
    (hLowerLLUU :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosUpper)
    (hLowerLULL :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosLower)
    (hLowerLULU :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosUpper)
    (hLowerLUUL :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosLower)
    (hLowerLUUU :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosUpper)
    (hLowerULLL :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosLower)
    (hLowerULLU :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosUpper)
    (hLowerULUL :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosLower)
    (hLowerULUU :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosUpper)
    (hLowerUULL :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosLower)
    (hLowerUULU :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUUL :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUUU :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLLL :
      scaleLower * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLLU :
      scaleLower * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLLUL :
      scaleLower * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLLUU :
      scaleLower * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperLULL :
      scaleLower * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperLULU :
      scaleLower * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUUL :
      scaleLower * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUUU :
      scaleLower * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULLL :
      scaleUpper * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperULLU :
      scaleUpper * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperULUL :
      scaleUpper * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperULUU :
      scaleUpper * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperUULL :
      scaleUpper * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperUULU :
      scaleUpper * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUUL :
      scaleUpper * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUUU :
      scaleUpper * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell 0 anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  refine
    cert.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at
      hAnchorIn hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper ?_ ?_
      hScaleLower hScaleUpper
      hLowerLLLL hLowerLLLU hLowerLLUL hLowerLLUU hLowerLULL hLowerLULU
      hLowerLUUL hLowerLUUU hLowerULLL hLowerULLU hLowerULUL hLowerULUU
      hLowerUULL hLowerUULU hLowerUUUL hLowerUUUU
      hUpperLLLL hUpperLLLU hUpperLLUL hUpperLLUU hUpperLULL hUpperLULU
      hUpperLUUL hUpperLUUU hUpperULLL hUpperULLU hUpperULUL hUpperULUU
      hUpperUULL hUpperUULU hUpperUUUL hUpperUUUU hCoeffLower hCoeffUpper
  · intro eta heta
    simpa using hCosLowerOne
  · intro eta heta
    simpa using hCosUpperOne

/-- Compact local component certificate for the raw Step22 positive-axis Omega
source on one auxiliary interval `(a,b]`.

This is a generator-facing package: one payload object carries the four
analytic component interval facts used by the sharp local `hRawCenterCoeffAbs`
receiver. -/
structure LocalRawOmegaComponentIntervalCert
    (k : Nat) (ell a b omegaLower omegaUpper shapeSqLower shapeSqUpper : Real) :
    Prop where
  hOmegaLower :
    ∀ eta ∈ Set.Ioc a b,
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta
  hOmegaUpper :
    ∀ eta ∈ Set.Ioc a b,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
        omegaUpper
  hShapeSqLower :
    ∀ eta ∈ Set.Ioc a b,
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2
  hShapeSqUpper :
    ∀ eta ∈ Set.Ioc a b,
      (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
        shapeSqUpper

/-- Convert an anchor-local deviation bound plus an anchor value enclosure into
a center-radius enclosure on the whole local interval. -/
theorem abs_sub_center_le_of_anchor_deviation_and_center_error
    {f : Real -> Real} {a b anchor center localRadius centerError radius : Real}
    (hDev :
      ∀ eta ∈ Set.Ioc a b,
        |f eta - f anchor| <= localRadius)
    (hCenter : |f anchor - center| <= centerError)
    (hContain : localRadius + centerError <= radius) :
    ∀ eta ∈ Set.Ioc a b, |f eta - center| <= radius := by
  intro eta heta
  have hsplit : f eta - center = (f eta - f anchor) + (f anchor - center) := by
    ring
  rw [hsplit]
  exact
    le_trans (abs_add_le _ _)
      (le_trans (add_le_add (hDev eta heta) hCenter) hContain)

/-- Build a local component interval certificate from two center-radius
enclosures.

This is the proof-producing surface for tight local component payloads: generated
code can prove an absolute ball bound for the Omega weight and for the
B-spline-shape square, while Lean handles the conversion to lower/upper interval
facts. -/
theorem LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds
    {k : Nat} {ell a b omegaLower omegaUpper shapeSqLower shapeSqUpper
      omegaCenter omegaRadius shapeSqCenter shapeSqRadius : Real}
    (hOmegaAbs :
      ∀ eta ∈ Set.Ioc a b,
        |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta -
          omegaCenter| <= omegaRadius)
    (hShapeSqAbs :
      ∀ eta ∈ Set.Ioc a b,
        |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 -
          shapeSqCenter| <= shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  refine
    { hOmegaLower := ?_
      hOmegaUpper := ?_
      hShapeSqLower := ?_
      hShapeSqUpper := ?_ }
  · intro eta heta
    have hbox := abs_le.mp (hOmegaAbs eta heta)
    linarith
  · intro eta heta
    have hbox := abs_le.mp (hOmegaAbs eta heta)
    linarith
  · intro eta heta
    have hbox := abs_le.mp (hShapeSqAbs eta heta)
    linarith
  · intro eta heta
    have hbox := abs_le.mp (hShapeSqAbs eta heta)
    linarith

/-- Endpoint arithmetic for bounding distance to an anchor on an auxiliary
interval `(a,b]`. -/
theorem abs_sub_anchor_le_of_mem_Ioc_endpoint_radius
    {a b anchor etaRadius : Real}
    (hLeft : anchor - a <= etaRadius)
    (hRight : b - anchor <= etaRadius) :
    ∀ eta ∈ Set.Ioc a b, |eta - anchor| <= etaRadius := by
  intro eta heta
  rw [abs_le]
  constructor
  · have ha : a <= eta := le_of_lt heta.1
    linarith
  · linarith [heta.2]

/-- Turn a local Lipschitz-style bound and an interval radius into an anchor
deviation bound. -/
theorem abs_sub_anchor_le_of_local_lipschitz_radius
    {f : Real -> Real} {a b anchor slope etaRadius localRadius : Real}
    (hLip :
      ∀ eta ∈ Set.Ioc a b,
        |f eta - f anchor| <= slope * |eta - anchor|)
    (hEtaRadius :
      ∀ eta ∈ Set.Ioc a b, |eta - anchor| <= etaRadius)
    (hSlopeNonneg : 0 <= slope)
    (hContain : slope * etaRadius <= localRadius) :
    ∀ eta ∈ Set.Ioc a b, |f eta - f anchor| <= localRadius := by
  intro eta heta
  have hScaled :
      slope * |eta - anchor| <= slope * etaRadius :=
    mul_le_mul_of_nonneg_left (hEtaRadius eta heta) hSlopeNonneg
  exact le_trans (hLip eta heta) (le_trans hScaled hContain)

/-- Derivative bound on the closed auxiliary interval gives the local
Lipschitz-style bound used by component certificates. -/
theorem abs_sub_anchor_le_of_deriv_bound_on_Icc
    {f : Real -> Real} {a b anchor slope : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hDifferentiable :
      ∀ eta ∈ Set.Icc a b, DifferentiableAt Real f eta)
    (hDerivBound :
      ∀ eta ∈ Set.Icc a b, ‖deriv f eta‖ <= slope) :
    ∀ eta ∈ Set.Ioc a b,
      |f eta - f anchor| <= slope * |eta - anchor| := by
  intro eta heta
  have hconvex : Convex Real (Set.Icc a b) := by
    simpa using (convex_Icc a b)
  have hetaIcc : eta ∈ Set.Icc a b := ⟨le_of_lt heta.1, heta.2⟩
  have hanchorIcc : anchor ∈ Set.Icc a b :=
    ⟨le_of_lt hAnchorIn.1, hAnchorIn.2⟩
  simpa [Real.norm_eq_abs, abs_sub_comm] using
    (Convex.norm_image_sub_le_of_norm_deriv_le
      (f := f) (s := Set.Icc a b) (x := eta) (y := anchor)
      hDifferentiable hDerivBound hconvex hetaIcc hanchorIcc)

/-- Build a local component interval certificate from anchor-deviation bounds.

This is the next proof-producing surface below `of_anchor_abs_bounds`: a
generator may prove analytic variation around an exact anchor value and a
separate rational enclosure for that anchor value; Lean recenters the result
before converting it to lower/upper component interval facts. -/
theorem LocalRawOmegaComponentIntervalCert.of_anchor_deviation_bounds
    {k : Nat} {ell a b anchor omegaLower omegaUpper shapeSqLower shapeSqUpper
      omegaCenter omegaRadius omegaLocalRadius omegaCenterError
      shapeSqCenter shapeSqRadius shapeSqLocalRadius shapeSqCenterError :
      Real}
    (hOmegaDev :
      ∀ eta ∈ Set.Ioc a b,
        |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta -
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            anchor| <= omegaLocalRadius)
    (hOmegaCenter :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor -
        omegaCenter| <= omegaCenterError)
    (hOmegaContain : omegaLocalRadius + omegaCenterError <= omegaRadius)
    (hShapeSqDev :
      ∀ eta ∈ Set.Ioc a b,
        |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 -
          (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2| <=
          shapeSqLocalRadius)
    (hShapeSqCenter :
      |(centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 -
        shapeSqCenter| <= shapeSqCenterError)
    (hShapeSqContain :
      shapeSqLocalRadius + shapeSqCenterError <= shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  refine
    LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds
      ?_ ?_ hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper
  · exact
      abs_sub_center_le_of_anchor_deviation_and_center_error
        hOmegaDev hOmegaCenter hOmegaContain
  · exact
      abs_sub_center_le_of_anchor_deviation_and_center_error
        hShapeSqDev hShapeSqCenter hShapeSqContain

/-- Build a local component interval certificate from local Lipschitz bounds.

This is the structured proof-producing surface below
`of_anchor_deviation_bounds`: generated payloads may prove slope bounds for the
Omega weight and B-spline-shape square, while Lean combines them with endpoint
radius arithmetic and anchor-value enclosures. -/
theorem LocalRawOmegaComponentIntervalCert.of_anchor_lipschitz_bounds
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper
      shapeSqLower shapeSqUpper omegaCenter omegaRadius omegaSlope
      omegaLocalRadius omegaCenterError shapeSqCenter shapeSqRadius
      shapeSqSlope shapeSqLocalRadius shapeSqCenterError : Real}
    (hEtaLeft : anchor - a <= etaRadius)
    (hEtaRight : b - anchor <= etaRadius)
    (hOmegaLip :
      ∀ eta ∈ Set.Ioc a b,
        |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta -
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            anchor| <= omegaSlope * |eta - anchor|)
    (hOmegaSlopeNonneg : 0 <= omegaSlope)
    (hOmegaLocalContain : omegaSlope * etaRadius <= omegaLocalRadius)
    (hOmegaCenter :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor -
        omegaCenter| <= omegaCenterError)
    (hOmegaContain : omegaLocalRadius + omegaCenterError <= omegaRadius)
    (hShapeSqLip :
      ∀ eta ∈ Set.Ioc a b,
        |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 -
          (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2| <=
          shapeSqSlope * |eta - anchor|)
    (hShapeSqSlopeNonneg : 0 <= shapeSqSlope)
    (hShapeSqLocalContain : shapeSqSlope * etaRadius <= shapeSqLocalRadius)
    (hShapeSqCenter :
      |(centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 -
        shapeSqCenter| <= shapeSqCenterError)
    (hShapeSqContain :
      shapeSqLocalRadius + shapeSqCenterError <= shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  have hEtaRadius :
      ∀ eta ∈ Set.Ioc a b, |eta - anchor| <= etaRadius :=
    abs_sub_anchor_le_of_mem_Ioc_endpoint_radius hEtaLeft hEtaRight
  refine
    LocalRawOmegaComponentIntervalCert.of_anchor_deviation_bounds
      ?_ hOmegaCenter hOmegaContain ?_ hShapeSqCenter hShapeSqContain
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper
  · exact
      abs_sub_anchor_le_of_local_lipschitz_radius
        hOmegaLip hEtaRadius hOmegaSlopeNonneg hOmegaLocalContain
  · exact
      abs_sub_anchor_le_of_local_lipschitz_radius
        hShapeSqLip hEtaRadius hShapeSqSlopeNonneg hShapeSqLocalContain

/-- Build a local component interval certificate from derivative bounds on the
closed auxiliary interval.

This is the preferred proof-producing surface below `of_anchor_lipschitz_bounds`
when generated data can enclose the derivatives of the Omega weight and
B-spline-shape square on `Set.Icc a b`. -/
theorem LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper
      shapeSqLower shapeSqUpper omegaCenter omegaRadius omegaSlope
      omegaLocalRadius omegaCenterError shapeSqCenter shapeSqRadius
      shapeSqSlope shapeSqLocalRadius shapeSqCenterError : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hEtaLeft : anchor - a <= etaRadius)
    (hEtaRight : b - anchor <= etaRadius)
    (hOmegaDifferentiable :
      ∀ eta ∈ Set.Icc a b,
        DifferentiableAt Real
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta)
    (hOmegaDerivBound :
      ∀ eta ∈ Set.Icc a b,
        ‖deriv
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            eta‖ <= omegaSlope)
    (hOmegaSlopeNonneg : 0 <= omegaSlope)
    (hOmegaLocalContain : omegaSlope * etaRadius <= omegaLocalRadius)
    (hOmegaCenter :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor -
        omegaCenter| <= omegaCenterError)
    (hOmegaContain : omegaLocalRadius + omegaCenterError <= omegaRadius)
    (hShapeSqDifferentiable :
      ∀ eta ∈ Set.Icc a b,
        DifferentiableAt Real
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2) eta)
    (hShapeSqDerivBound :
      ∀ eta ∈ Set.Icc a b,
        ‖deriv
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
            eta‖ <= shapeSqSlope)
    (hShapeSqSlopeNonneg : 0 <= shapeSqSlope)
    (hShapeSqLocalContain : shapeSqSlope * etaRadius <= shapeSqLocalRadius)
    (hShapeSqCenter :
      |(centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 -
        shapeSqCenter| <= shapeSqCenterError)
    (hShapeSqContain :
      shapeSqLocalRadius + shapeSqCenterError <= shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  refine
    LocalRawOmegaComponentIntervalCert.of_anchor_lipschitz_bounds
      hEtaLeft hEtaRight ?_ hOmegaSlopeNonneg hOmegaLocalContain
      hOmegaCenter hOmegaContain ?_ hShapeSqSlopeNonneg hShapeSqLocalContain
      hShapeSqCenter hShapeSqContain hOmegaLower hOmegaUpper hShapeSqLower
      hShapeSqUpper
  · exact
      abs_sub_anchor_le_of_deriv_bound_on_Icc
        hAnchorIn hOmegaDifferentiable hOmegaDerivBound
  · exact
      abs_sub_anchor_le_of_deriv_bound_on_Icc
        hAnchorIn hShapeSqDifferentiable hShapeSqDerivBound

/-- Build a local component interval certificate from derivative bounds, using
the backend differentiability lemmas for the Omega weight and B-spline-shape
square automatically. -/
theorem LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds_auto_differentiability
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper
      shapeSqLower shapeSqUpper omegaCenter omegaRadius omegaSlope
      omegaLocalRadius omegaCenterError shapeSqCenter shapeSqRadius
      shapeSqSlope shapeSqLocalRadius shapeSqCenterError : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hEtaLeft : anchor - a <= etaRadius)
    (hEtaRight : b - anchor <= etaRadius)
    (hOmegaDerivBound :
      ∀ eta ∈ Set.Icc a b,
        ‖deriv
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            eta‖ <= omegaSlope)
    (hOmegaSlopeNonneg : 0 <= omegaSlope)
    (hOmegaLocalContain : omegaSlope * etaRadius <= omegaLocalRadius)
    (hOmegaCenter :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor -
        omegaCenter| <= omegaCenterError)
    (hOmegaContain : omegaLocalRadius + omegaCenterError <= omegaRadius)
    (hShapeSqDerivBound :
      ∀ eta ∈ Set.Icc a b,
        ‖deriv
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
            eta‖ <= shapeSqSlope)
    (hShapeSqSlopeNonneg : 0 <= shapeSqSlope)
    (hShapeSqLocalContain : shapeSqSlope * etaRadius <= shapeSqLocalRadius)
    (hShapeSqCenter :
      |(centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 -
        shapeSqCenter| <= shapeSqCenterError)
    (hShapeSqContain :
      shapeSqLocalRadius + shapeSqCenterError <= shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  refine
    LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds
      hAnchorIn hEtaLeft hEtaRight ?_ hOmegaDerivBound hOmegaSlopeNonneg
      hOmegaLocalContain hOmegaCenter hOmegaContain ?_ hShapeSqDerivBound
      hShapeSqSlopeNonneg hShapeSqLocalContain hShapeSqCenter
      hShapeSqContain hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper
  · intro eta _heta
    exact
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt
        eta
  · intro eta _heta
    exact
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformRealClosedForm_differentiableAt
        k ell eta).pow 2

/-- Derivative of the local shape-square component.

Endpoint payloads can use this to reduce
`deriv (fun t => E(t)^2)` enclosures to enclosures for the closed-form
component `E` and its derivative. -/
theorem deriv_centeredBSplineImagTransformRealClosedForm_sq
    (k : Nat) (ell eta : Real) :
    deriv
        (fun t : Real =>
          (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
        eta =
      2 * centeredBSplineImagTransformRealClosedForm k ell eta *
        deriv
          (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
          eta := by
  have hf :
      DifferentiableAt Real
        (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
        eta :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformRealClosedForm_differentiableAt
      k ell eta
  simpa [pow_one, mul_assoc] using (deriv_fun_pow hf 2)

/-- Closed-form derivative target for the B-spline shape component `E`.

This deliberately keeps the derivative of `realSinc` as the checked analytic
derivative operator.  Generated endpoint payloads can now target this named
closed form, while Lean supplies the chain-rule bridge from the original
`deriv (fun t => centeredBSplineImagTransformRealClosedForm k ell t)`. -/
def centeredBSplineImagTransformRealClosedFormDerivClosedForm
    (k : Nat) (ell eta : Real) : Real :=
  (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
    ((k + 1 : Real) *
      (realSinc (ell * eta / (2 * bsplineScale k))) ^ k *
        (deriv realSinc (ell * eta / (2 * bsplineScale k)) *
          (ell / (2 * bsplineScale k))))

/-- Derivative identity for the B-spline shape component `E`.

This is the shared proof-safe bridge for generated shape endpoint facts:
interval rows may prove bounds for
`centeredBSplineImagTransformRealClosedFormDerivClosedForm`, and Lean rewrites
the actual derivative of `E` to that target here. -/
theorem centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm
    (k : Nat) (ell eta : Real) :
    deriv
        (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
        eta =
      centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta := by
  unfold centeredBSplineImagTransformRealClosedForm
  unfold centeredBSplineImagTransformRealClosedFormDerivClosedForm
  have hlin :
      deriv (fun t : Real => ell * t / (2 * bsplineScale k)) eta =
        ell / (2 * bsplineScale k) := by
    have hfun :
        (fun t : Real => ell * t / (2 * bsplineScale k)) =
          fun t : Real => (ell / (2 * bsplineScale k)) * t := by
      funext t
      ring_nf
    rw [hfun]
    rw [deriv_const_mul]
    · simp
    · exact differentiableAt_id
  have hcomp :
      deriv
          (fun t : Real => realSinc (ell * t / (2 * bsplineScale k)))
          eta =
        deriv realSinc (ell * eta / (2 * bsplineScale k)) *
          (ell / (2 * bsplineScale k)) := by
    have harg :
        DifferentiableAt Real
          (fun t : Real => ell * t / (2 * bsplineScale k)) eta := by
      fun_prop
    have hraw :=
      deriv_comp
        eta
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.realSinc_differentiableAt
          (ell * eta / (2 * bsplineScale k)))
        harg
    simpa [Function.comp_def, hlin] using hraw
  have hpow :
      deriv
          (fun t : Real =>
            (realSinc (ell * t / (2 * bsplineScale k))) ^ (k + 1))
          eta =
        ((k + 1 : Real) *
          (realSinc (ell * eta / (2 * bsplineScale k))) ^ k *
            deriv
              (fun t : Real =>
                realSinc (ell * t / (2 * bsplineScale k)))
              eta) := by
    have hsinc :
        DifferentiableAt Real
          (fun t : Real => realSinc (ell * t / (2 * bsplineScale k)))
          eta := by
      fun_prop
    have hraw := deriv_fun_pow hsinc (k + 1)
    simpa [Nat.cast_add, Nat.cast_one] using hraw
  calc
    deriv
        (fun t : Real =>
          (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
            (realSinc (ell * t / (2 * bsplineScale k))) ^ (k + 1))
        eta =
        (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
          deriv
            (fun t : Real =>
              (realSinc (ell * t / (2 * bsplineScale k))) ^ (k + 1))
            eta := by
          rw [deriv_const_mul]
          fun_prop
    _ =
        (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
          ((k + 1 : Real) *
            (realSinc (ell * eta / (2 * bsplineScale k))) ^ k *
              deriv
                (fun t : Real =>
                  realSinc (ell * t / (2 * bsplineScale k)))
                eta) := by
          rw [hpow]
    _ =
        (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
          ((k + 1 : Real) *
            (realSinc (ell * eta / (2 * bsplineScale k))) ^ k *
              (deriv realSinc (ell * eta / (2 * bsplineScale k)) *
                (ell / (2 * bsplineScale k)))) := by
          rw [hcomp]
    _ =
        (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
          ((k + 1 : Real) *
            (realSinc (ell * eta / (2 * bsplineScale k))) ^ k *
              (deriv realSinc (ell * eta / (2 * bsplineScale k)) *
                (ell / (2 * bsplineScale k)))) := by
          rfl

/-- Uniform `Icc` wrapper for the B-spline shape closed-form derivative
identity. -/
theorem centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm_on_Icc
    {k : Nat} {ell a b : Real} :
    ∀ eta ∈ Set.Icc a b,
      deriv
          (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
          eta =
        centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta := by
  intro eta _
  exact centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm k ell eta

/-- Shape-square derivative interval bounds from endpoint intervals for the
closed-form component and its derivative.

This is the Lean-side receiver for generated endpoint payloads: the generator
only has to enclose `E`, enclose `E'`, and check the four product corners for
`2 * E * E'`. -/
theorem shapeSqDeriv_interval_bounds_of_closedForm_value_deriv_intervals
    {k : Nat} {ell eta shapeLower shapeUpper derivLower derivUpper
      shapeSqDerivLower shapeSqDerivUpper : Real}
    (hValueLower :
      shapeLower <= centeredBSplineImagTransformRealClosedForm k ell eta)
    (hValueUpper :
      centeredBSplineImagTransformRealClosedForm k ell eta <= shapeUpper)
    (hDerivLower :
      derivLower <=
        deriv (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t) eta)
    (hDerivUpper :
      deriv (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t) eta <=
        derivUpper)
    (hLowerLL : shapeSqDerivLower <= 2 * shapeLower * derivLower)
    (hLowerLU : shapeSqDerivLower <= 2 * shapeLower * derivUpper)
    (hLowerUL : shapeSqDerivLower <= 2 * shapeUpper * derivLower)
    (hLowerUU : shapeSqDerivLower <= 2 * shapeUpper * derivUpper)
    (hUpperLL : 2 * shapeLower * derivLower <= shapeSqDerivUpper)
    (hUpperLU : 2 * shapeLower * derivUpper <= shapeSqDerivUpper)
    (hUpperUL : 2 * shapeUpper * derivLower <= shapeSqDerivUpper)
    (hUpperUU : 2 * shapeUpper * derivUpper <= shapeSqDerivUpper) :
    shapeSqDerivLower <=
        deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta ∧
      deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta <= shapeSqDerivUpper := by
  have hprod :
      shapeSqDerivLower <=
          2 * centeredBSplineImagTransformRealClosedForm k ell eta *
            deriv
              (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
              eta ∧
        2 * centeredBSplineImagTransformRealClosedForm k ell eta *
            deriv
              (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
              eta <= shapeSqDerivUpper :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := (2 : Real))
      hValueLower hValueUpper hDerivLower hDerivUpper
      hLowerLL hLowerLU hLowerUL hLowerUU
      hUpperLL hUpperLU hUpperUL hUpperUU
  constructor
  · calc
      shapeSqDerivLower <=
          2 * centeredBSplineImagTransformRealClosedForm k ell eta *
            deriv
              (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
              eta := hprod.1
      _ =
          deriv
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
            eta := by
        exact (deriv_centeredBSplineImagTransformRealClosedForm_sq k ell eta).symm
  · calc
      deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta =
          2 * centeredBSplineImagTransformRealClosedForm k ell eta *
            deriv
              (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
          eta := deriv_centeredBSplineImagTransformRealClosedForm_sq k ell eta
      _ <= shapeSqDerivUpper := hprod.2

/-- Uniform `Icc` version of
`shapeSqDeriv_interval_bounds_of_closedForm_value_deriv_intervals`. -/
theorem shapeSqDeriv_interval_bounds_on_Icc_of_closedForm_value_deriv_intervals
    {k : Nat} {ell a b shapeLower shapeUpper derivLower derivUpper
      shapeSqDerivLower shapeSqDerivUpper : Real}
    (hValueLower :
      ∀ eta ∈ Set.Icc a b,
        shapeLower <= centeredBSplineImagTransformRealClosedForm k ell eta)
    (hValueUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedForm k ell eta <= shapeUpper)
    (hDerivLower :
      ∀ eta ∈ Set.Icc a b,
        derivLower <=
          deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta)
    (hDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta <= derivUpper)
    (hLowerLL : shapeSqDerivLower <= 2 * shapeLower * derivLower)
    (hLowerLU : shapeSqDerivLower <= 2 * shapeLower * derivUpper)
    (hLowerUL : shapeSqDerivLower <= 2 * shapeUpper * derivLower)
    (hLowerUU : shapeSqDerivLower <= 2 * shapeUpper * derivUpper)
    (hUpperLL : 2 * shapeLower * derivLower <= shapeSqDerivUpper)
    (hUpperLU : 2 * shapeLower * derivUpper <= shapeSqDerivUpper)
    (hUpperUL : 2 * shapeUpper * derivLower <= shapeSqDerivUpper)
    (hUpperUU : 2 * shapeUpper * derivUpper <= shapeSqDerivUpper) :
    (∀ eta ∈ Set.Icc a b,
      shapeSqDerivLower <=
        deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta) ∧
      (∀ eta ∈ Set.Icc a b,
        deriv
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
            eta <= shapeSqDerivUpper) := by
  constructor
  · intro eta heta
    exact
      (shapeSqDeriv_interval_bounds_of_closedForm_value_deriv_intervals
        (hValueLower eta heta) (hValueUpper eta heta)
        (hDerivLower eta heta) (hDerivUpper eta heta)
        hLowerLL hLowerLU hLowerUL hLowerUU
        hUpperLL hUpperLU hUpperUL hUpperUU).1
  · intro eta heta
    exact
      (shapeSqDeriv_interval_bounds_of_closedForm_value_deriv_intervals
        (hValueLower eta heta) (hValueUpper eta heta)
        (hDerivLower eta heta) (hDerivUpper eta heta)
        hLowerLL hLowerLU hLowerUL hLowerUU
        hUpperLL hUpperLU hUpperUL hUpperUU).2

/-- Canonical absolute-value bound extracted from a two-sided interval. -/
def intervalAutoAbsBound (lower upper : Real) : Real :=
  max 0 (max (-lower) upper)

theorem intervalAutoAbsBound_nonneg (lower upper : Real) :
    0 <= intervalAutoAbsBound lower upper := by
  unfold intervalAutoAbsBound
  exact le_max_left 0 (max (-lower) upper)

theorem norm_le_intervalAutoAbsBound_of_interval_bounds
    {y lower upper : Real}
    (hLower : lower <= y)
    (hUpper : y <= upper) :
    ‖y‖ <= intervalAutoAbsBound lower upper := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hNegLower : -lower <= intervalAutoAbsBound lower upper := by
      unfold intervalAutoAbsBound
      exact le_trans (le_max_left (-lower) upper)
        (le_max_right 0 (max (-lower) upper))
    linarith
  · have hUpperBound : upper <= intervalAutoAbsBound lower upper := by
      unfold intervalAutoAbsBound
      exact le_trans (le_max_right (-lower) upper)
        (le_max_right 0 (max (-lower) upper))
    linarith

/-- Canonical center-error bound extracted from a two-sided value interval. -/
def intervalAutoCenterError (lower upper center : Real) : Real :=
  max 0 (max (center - lower) (upper - center))

theorem intervalAutoCenterError_nonneg (lower upper center : Real) :
    0 <= intervalAutoCenterError lower upper center := by
  unfold intervalAutoCenterError
  exact le_max_left 0 (max (center - lower) (upper - center))

theorem abs_sub_center_le_intervalAutoCenterError_of_interval_bounds
    {y lower upper center : Real}
    (hLower : lower <= y)
    (hUpper : y <= upper) :
    |y - center| <= intervalAutoCenterError lower upper center := by
  rw [abs_le]
  constructor
  · have hLeft :
        center - lower <= intervalAutoCenterError lower upper center := by
      unfold intervalAutoCenterError
      exact le_trans (le_max_left (center - lower) (upper - center))
        (le_max_right 0 (max (center - lower) (upper - center)))
    linarith
  · have hRight :
        upper - center <= intervalAutoCenterError lower upper center := by
      unfold intervalAutoCenterError
      exact le_trans (le_max_right (center - lower) (upper - center))
        (le_max_right 0 (max (center - lower) (upper - center)))
    linarith

/-- Closed form for the derivative of the raw Step22 Omega weight.

The factor is written as `-(Im trigamma * 1/2)` because this is the normal
form produced by the real-part chain rule in Lean. -/
def step22OmegaArchWeightDerivClosedForm (eta : Real) : Real :=
  -((trigamma
      ((1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex)))).im *
    (1 / 2 : Real))

/-- Convert a two-sided enclosure for the imaginary part of the trigamma
series into a two-sided enclosure for the raw Step22 Omega derivative
closed form.

This is the derivative-side companion to the Stieltjes anchor bridge.  Future
generated rows can prove finite-sum/tail bounds for the series, then use this
checked bridge before constructing `Step22OmegaClosedFormEndpointBoundsCert`. -/
theorem step22OmegaArchWeightDerivClosedForm_bounds_from_trigamma_im_series
    (eta imLower imUpper derivLower derivUpper : Real)
    (hImLower :
      imLower <=
        ∑' n : Nat,
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
    (hImUpper :
      (∑' n : Nat,
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
        <= imUpper)
    (hDerivLower : derivLower <= -(imUpper * (1 / 2 : Real)))
    (hDerivUpper : -(imLower * (1 / 2 : Real)) <= derivUpper) :
    derivLower <= step22OmegaArchWeightDerivClosedForm eta ∧
      step22OmegaArchWeightDerivClosedForm eta <= derivUpper := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  have hz : 0 < z.re := by
    norm_num [z]
  have hseries :
      (trigamma z).im =
        ∑' n : Nat, (1 / (z + n) ^ 2).im :=
    _root_.im_trigamma_eq_tsum_im hz
  have hImLower' : imLower <= (trigamma z).im := by
    rw [hseries]
    simpa [z] using hImLower
  have hImUpper' : (trigamma z).im <= imUpper := by
    rw [hseries]
    simpa [z] using hImUpper
  constructor
  · change derivLower <= -((trigamma z).im * (1 / 2 : Real))
    linarith
  · change -((trigamma z).im * (1 / 2 : Real)) <= derivUpper
    linarith

/-- Bound a convergent real series from a rational finite prefix and an
absolute tail radius.

This is the generic arithmetic landing surface for future generated
finite-sum/tail endpoint rows. -/
theorem tsum_bounds_of_sum_range_tail_abs
    {f : Nat -> Real} (N : Nat) (lower upper tailRadius : Real)
    (hf : Summable f)
    (hLower : lower <= (Finset.range N).sum f)
    (hUpper : (Finset.range N).sum f <= upper)
    (hTail : |∑' n : Nat, f (n + N)| <= tailRadius) :
    lower - tailRadius <= ∑' n : Nat, f n ∧
      (∑' n : Nat, f n) <= upper + tailRadius := by
  have hsplit :
      (Finset.range N).sum f + (∑' n : Nat, f (n + N)) =
        ∑' n : Nat, f n := by
    simpa using (hf.sum_add_tsum_nat_add N)
  have hTailLower : -tailRadius <= ∑' n : Nat, f (n + N) :=
    (abs_le.mp hTail).1
  have hTailUpper : (∑' n : Nat, f (n + N)) <= tailRadius :=
    (abs_le.mp hTail).2
  constructor
  · rw [← hsplit]
    linarith
  · rw [← hsplit]
    linarith

/-- Bound an absolute tail by a summable nonnegative majorant.  Generated
endpoint rows can use this to turn pointwise tail estimates into the tail
radius consumed by `tsum_bounds_of_sum_range_tail_abs`. -/
theorem abs_tsum_tail_le_of_abs_le_tsum_bound
    {f g : Nat -> Real} (N : Nat) (tailRadius : Real)
    (hfTail : Summable (fun n : Nat => f (n + N)))
    (hg : Summable g)
    (hterm : ∀ n : Nat, |f (n + N)| <= g n)
    (hsum : (∑' n : Nat, g n) <= tailRadius) :
    |∑' n : Nat, f (n + N)| <= tailRadius := by
  have hnorm :
      ‖∑' n : Nat, f (n + N)‖ <=
        ∑' n : Nat, ‖f (n + N)‖ := by
    exact norm_tsum_le_tsum_norm hfTail.norm
  have habs_sum :
      (∑' n : Nat, |f (n + N)|) <= ∑' n : Nat, g n := by
    exact Summable.tsum_le_tsum hterm hfTail.abs hg
  rw [Real.norm_eq_abs] at hnorm
  have hnorm' :
      |∑' n : Nat, f (n + N)| <=
        ∑' n : Nat, |f (n + N)| := by
    simpa [Real.norm_eq_abs] using hnorm
  exact le_trans hnorm' (le_trans habs_sum hsum)

/-- Bound a finite prefix by termwise lower and upper bounds.  This is the
finite-sum companion to the tail-majorant bridge. -/
theorem sum_range_bounds_of_term_bounds
    {f lower upper : Nat -> Real} (N : Nat)
    (hLower : ∀ n : Nat, n < N -> lower n <= f n)
    (hUpper : ∀ n : Nat, n < N -> f n <= upper n) :
    (Finset.range N).sum lower <= (Finset.range N).sum f ∧
      (Finset.range N).sum f <= (Finset.range N).sum upper := by
  constructor
  · exact Finset.sum_le_sum (by
      intro n hn
      exact hLower n (Finset.mem_range.mp hn))
  · exact Finset.sum_le_sum (by
      intro n hn
      exact hUpper n (Finset.mem_range.mp hn))

/-- Real closed form for one term in the trigamma-imaginary series used by
the raw Step22 Omega derivative. -/
def trigammaImSeriesTermClosedForm (eta : Real) (n : Nat) : Real :=
  -((2 * ((n : Real) + (1 / 4 : Real)) * (eta / 2)) /
    ((((n : Real) + (1 / 4 : Real)) ^ 2 + (eta / 2) ^ 2) ^ 2))

/-- Convert the complex trigamma-imaginary term into the real rational
closed form that endpoint generators can bound by ordinary interval
arithmetic. -/
theorem trigamma_im_series_term_eq_closed_form (eta : Real) (n : Nat) :
    (1 /
        (((1 / 4 : Complex) +
              Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im =
      trigammaImSeriesTermClosedForm eta n := by
  let x : Real := (n : Real) + (1 / 4 : Real)
  let y : Real := eta / 2
  have hxpos : 0 < x := by
    dsimp [x]
    have hn : 0 <= (n : Real) := by exact_mod_cast Nat.zero_le n
    linarith
  have hxy :
      (((1 / 4 : Complex) +
            Complex.I * (((eta / 2 : Real) : Complex))) + n) =
        (x : Complex) + Complex.I * (y : Complex) := by
    exact Complex.ext_iff.2 (by
      constructor <;> simp [x, y, add_comm, add_left_comm])
  rw [hxy]
  have hden : (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by
    have hx2pos : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hy2nonneg : 0 <= y ^ 2 := sq_nonneg y
    have hsumpos : 0 < x ^ 2 + y ^ 2 := by linarith
    exact pow_ne_zero 2 (ne_of_gt hsumpos)
  simp only [trigammaImSeriesTermClosedForm, x, y]
  rw [Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, zero_mul]
  have hnorm :
      Complex.normSq (((x : Complex) + Complex.I * (y : Complex)) ^ 2) =
        (x ^ 2 + y ^ 2) ^ 2 := by
    have hbase :
        Complex.normSq ((x : Complex) + Complex.I * (y : Complex)) =
          x ^ 2 + y ^ 2 := by
      have hcomm :
          ((x : Complex) + Complex.I * (y : Complex)) =
            (x : Complex) + (y : Complex) * Complex.I := by
        ring
      rw [hcomm, Complex.normSq_add_mul_I]
    rw [pow_two, Complex.normSq_mul, hbase]
    ring
  rw [hnorm]
  have him :
      (((x : Complex) + Complex.I * (y : Complex)) ^ 2).im = 2 * x * y := by
    norm_num [pow_two]
    ring
  rw [him]
  field_simp [hden]
  ring

/-- A coarse cubic majorant for the closed-form trigamma-imaginary term on the
positive eta axis.

This is intentionally simple: endpoint generators may use it for tail rows,
then prove the resulting rational `tsum` comparison separately. -/
theorem abs_trigammaImSeriesTermClosedForm_le_etaUpper_cubic
    {eta etaUpper : Real} (n : Nat)
    (hEtaNonneg : 0 <= eta) (hEtaUpper : eta <= etaUpper) :
    |trigammaImSeriesTermClosedForm eta n| <=
      etaUpper / (((n : Real) + (1 / 4 : Real)) ^ 3) := by
  let x : Real := (n : Real) + (1 / 4 : Real)
  let y : Real := eta / 2
  have hxpos : 0 < x := by
    dsimp [x]
    have hn : 0 <= (n : Real) := by exact_mod_cast Nat.zero_le n
    linarith
  have hynonneg : 0 <= y := by
    dsimp [y]
    linarith
  have hUpperNonneg : 0 <= etaUpper := by
    linarith
  have hdenpos : 0 < (x ^ 2 + y ^ 2) ^ 2 := by
    have hx2pos : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hy2nonneg : 0 <= y ^ 2 := sq_nonneg y
    have hsumpos : 0 < x ^ 2 + y ^ 2 := by linarith
    exact sq_pos_of_pos hsumpos
  have hx3pos : 0 < x ^ 3 := pow_pos hxpos 3
  have hx4pos : 0 < x ^ 4 := pow_pos hxpos 4
  have hden_ge_x4 : x ^ 4 <= (x ^ 2 + y ^ 2) ^ 2 := by
    nlinarith [sq_nonneg y, sq_nonneg (y ^ 2), mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  have hnum_nonneg : 0 <= 2 * x * y := by nlinarith
  have hdiv_den :
      (2 * x * y) / ((x ^ 2 + y ^ 2) ^ 2) <= (2 * x * y) / (x ^ 4) := by
    exact div_le_div_of_nonneg_left hnum_nonneg hx4pos hden_ge_x4
  have hdiv_upper : (2 * x * y) / (x ^ 4) <= etaUpper / (x ^ 3) := by
    have hnum_eq : 2 * x * y = x * eta := by
      dsimp [y]
      ring
    rw [hnum_eq]
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hx3ne : x ^ 3 ≠ 0 := ne_of_gt hx3pos
    calc
      (x * eta) / (x ^ 4) = eta / (x ^ 3) := by
        field_simp [hxne, hx3ne]
      _ <= etaUpper / (x ^ 3) := by
        exact div_le_div_of_nonneg_right hEtaUpper (le_of_lt hx3pos)
  have hclosed :
      |trigammaImSeriesTermClosedForm eta n| =
        (2 * x * y) / ((x ^ 2 + y ^ 2) ^ 2) := by
    simp only [trigammaImSeriesTermClosedForm, x, y]
    rw [abs_neg, abs_div]
    have hnum_abs : |2 * x * y| = 2 * x * y := abs_of_nonneg hnum_nonneg
    have hden_abs : |((x ^ 2 + y ^ 2) ^ 2)| = (x ^ 2 + y ^ 2) ^ 2 :=
      abs_of_nonneg (le_of_lt hdenpos)
    rw [hnum_abs, hden_abs]
  rw [hclosed]
  exact le_trans hdiv_den hdiv_upper

/-- The quarter-shifted cubic comparison series used by the Omega tail
majorant is summable uniformly in the finite cutoff `N`. -/
theorem summable_one_div_nat_add_quarter_cubic (N : Nat) :
    Summable (fun n : Nat =>
      1 / ((((n + N : Nat) : Real) + (1 / 4 : Real)) ^ 3)) := by
  have hbase : Summable (fun n : Nat => 1 / (((n + 1 : Nat) : Real) ^ 3)) := by
    have hpow : Summable (fun n : Nat => 1 / ((n : Real) ^ 3)) := by
      exact Real.summable_one_div_nat_pow.2 (by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : Nat => 1 / ((n : Real) ^ 3)) 1).2 hpow)
  refine Summable.of_nonneg_of_le ?hNonneg ?hLe (Summable.mul_left (64 : Real) hbase)
  · intro n
    exact div_nonneg zero_le_one (pow_nonneg (by
      have hn : 0 <= ((n + N : Nat) : Real) := by
        exact_mod_cast Nat.zero_le (n + N)
      norm_num
      linarith) 3)
  · intro n
    let x : Real := (((n + N : Nat) : Real) + (1 / 4 : Real))
    let y : Real := (((n + 1 : Nat) : Real) / 4)
    have hypos : 0 < y := by
      dsimp [y]
      have hn1 : (0 : Real) < ((n + 1 : Nat) : Real) := by
        exact_mod_cast Nat.succ_pos n
      positivity
    have hylex : y <= x := by
      dsimp [x, y]
      have hN : 0 <= (N : Real) := by
        exact_mod_cast Nat.zero_le N
      have hn : 0 <= (n : Real) := by
        exact_mod_cast Nat.zero_le n
      norm_num [Nat.cast_add]
      nlinarith
    have hpow : y ^ 3 <= x ^ 3 := pow_le_pow_left₀ (le_of_lt hypos) hylex 3
    have hy3pos : 0 < y ^ 3 := pow_pos hypos 3
    calc
      1 / x ^ 3 <= 1 / y ^ 3 := one_div_le_one_div_of_le hy3pos hpow
      _ = 64 * (1 / (((n + 1 : Nat) : Real) ^ 3)) := by
        dsimp [y]
        have hn1 : ((n + 1 : Nat) : Real) ≠ 0 := by
          exact_mod_cast (Nat.succ_ne_zero n)
        field_simp [hn1]
        ring

/-- The concrete cubic tail majorant selected for generated Omega endpoint
rows is summable. -/
theorem summable_trigammaImSeriesTermClosedForm_cubic_majorant
    (etaUpper : Real) (N : Nat) :
    Summable (fun n : Nat =>
      etaUpper / ((((n + N : Nat) : Real) + (1 / 4 : Real)) ^ 3)) := by
  have h := summable_one_div_nat_add_quarter_cubic N
  simpa [div_eq_mul_inv] using Summable.mul_left etaUpper h

/-- Specialized finite-prefix plus tail-radius bound for the imaginary part of
the trigamma series appearing in the Step22 Omega derivative. -/
theorem trigamma_im_series_bounds_of_sum_range_tail_abs
    (eta : Real) (N : Nat) (lower upper tailRadius : Real)
    (hLower :
      lower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im))
    (hUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
        <= upper)
    (hTail :
      |∑' n : Nat,
        (1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((eta / 2 : Real) : Complex))) + (n + N)) ^ 2).im| <=
        tailRadius) :
    lower - tailRadius <=
        ∑' n : Nat,
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im ∧
      (∑' n : Nat,
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im) <=
        upper + tailRadius := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  let f : Nat -> Real := fun n : Nat => (1 / (z + n) ^ 2).im
  have hz : 0 < z.re := by
    norm_num [z]
  have hfComplex : Summable (fun n : Nat => 1 / (z + n) ^ 2) :=
    _root_.summable_trigamma_series hz
  have hf : Summable f := by
    exact Complex.imCLM.summable hfComplex
  have hBounds :=
    tsum_bounds_of_sum_range_tail_abs (f := f) N lower upper tailRadius hf
      (by simpa [f, z] using hLower) (by simpa [f, z] using hUpper)
      (by simpa [f, z, add_assoc] using hTail)
  simpa [f, z] using hBounds

/-- Specialized tail-majorant bridge for the imaginary part of the trigamma
series appearing in the Step22 Omega derivative. -/
theorem trigamma_im_series_tail_abs_le_of_majorant
    (eta : Real) (N : Nat) (g : Nat -> Real) (tailRadius : Real)
    (hg : Summable g)
    (hterm :
      ∀ n : Nat,
        |(1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((eta / 2 : Real) : Complex))) + (n + N)) ^ 2).im| <=
          g n)
    (hsum : (∑' n : Nat, g n) <= tailRadius) :
    |∑' n : Nat,
      (1 /
          (((1 / 4 : Complex) +
                Complex.I * (((eta / 2 : Real) : Complex))) + (n + N)) ^ 2).im| <=
      tailRadius := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  let f : Nat -> Real := fun n : Nat => (1 / (z + n) ^ 2).im
  have hz : 0 < z.re := by
    norm_num [z]
  have hfComplex : Summable (fun n : Nat => 1 / (z + n) ^ 2) :=
    _root_.summable_trigamma_series hz
  have hf : Summable f := by
    exact Complex.imCLM.summable hfComplex
  have hinj : Function.Injective (fun n : Nat => n + N) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hfTail : Summable (fun n : Nat => f (n + N)) := by
    have htail : Summable (f ∘ fun n : Nat => n + N) :=
      hf.comp_injective hinj
    simpa [Function.comp_def] using htail
  have htailBound :=
    abs_tsum_tail_le_of_abs_le_tsum_bound (f := f) (g := g) N tailRadius
      hfTail hg (by intro n; simpa [f, z, add_assoc] using hterm n)
      hsum
  simpa [f, z, add_assoc] using htailBound

/-- Specialized finite-prefix interval bound from termwise bounds for the
imaginary part of the trigamma series. -/
theorem trigamma_im_series_prefix_bounds_of_term_bounds
    (eta : Real) (N : Nat) (termLower termUpper : Nat -> Real)
    (hLower :
      ∀ n : Nat, n < N ->
        termLower n <=
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
    (hUpper :
      ∀ n : Nat, n < N ->
        (1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im <=
          termUpper n) :
    (Finset.range N).sum termLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im) ∧
      (Finset.range N).sum (fun n : Nat =>
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im) <=
        (Finset.range N).sum termUpper := by
  exact
    sum_range_bounds_of_term_bounds N
      (fun n hn => hLower n hn)
      (fun n hn => hUpper n hn)

/-- Real-valued term for the Step22 Omega anchor series
`Re digamma(1/4 + i eta/2) - log pi`.

This is the direct-anchor route for tight Omega endpoint rows.  It avoids the
coarse Stieltjes `N = 1` envelope, which is numerically false for the active
refined endpoint rows. -/
def step22OmegaArchWeightReSeriesTerm (eta : Real) (n : Nat) : Real :=
  (1 / (((n : Real) + 1))) -
    (((n : Real) + (1 / 4 : Real)) /
      ((((n : Real) + (1 / 4 : Real)) ^ 2) + (eta / 2) ^ 2))

/-- Rewrite the complex real-part digamma-series term into the rational
real-valued form consumed by generated endpoint anchor bounds. -/
theorem step22OmegaArchWeightReSeriesTerm_eq_complex_re
    (eta : Real) (n : Nat) :
    ((1 / ((n : Complex) + 1) -
        1 /
          (((1 / 4 : Complex) +
              Complex.I * (((eta / 2 : Real) : Complex))) + n)).re) =
      step22OmegaArchWeightReSeriesTerm eta n := by
  let x : Real := (n : Real) + (1 / 4 : Real)
  let y : Real := eta / 2
  unfold step22OmegaArchWeightReSeriesTerm
  rw [Complex.sub_re]
  have hleft : (1 / ((n : Complex) + 1)).re = 1 / ((n : Real) + 1) := by
    rw [Complex.div_re]
    norm_num [Complex.add_re, Complex.add_im, Complex.normSq, pow_two]
  rw [hleft]
  have hright :
      (1 /
          (((1 / 4 : Complex) +
              Complex.I * (((eta / 2 : Real) : Complex))) + n)).re =
        x / (x ^ 2 + y ^ 2) := by
    have harg :
        (((1 / 4 : Complex) +
            Complex.I * (((eta / 2 : Real) : Complex))) + n) =
          (x : Complex) + Complex.I * (y : Complex) := by
      simp [x, y, add_comm, add_left_comm]
    rw [harg]
    rw [Complex.div_re]
    norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.normSq, pow_two]
  rw [hright]

/-- Summability of the real Step22 Omega anchor series. -/
theorem summable_step22OmegaArchWeightReSeriesTerm (eta : Real) :
    Summable (step22OmegaArchWeightReSeriesTerm eta) := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  have hzNonzero : ∀ n : Nat, z + n ≠ 0 := by
    intro n hzero
    have hre := congrArg Complex.re hzero
    have hn : 0 <= (n : Real) := by
      exact_mod_cast Nat.zero_le n
    norm_num [z, Complex.add_re, Complex.mul_re] at hre
    linarith
  have hComplex := Q3.digamma_series_summable z hzNonzero
  have hRe :
      Summable
        (fun n : Nat => (1 / ((n : Complex) + 1) - 1 / (z + n)).re) := by
    exact Complex.reCLM.summable hComplex
  exact hRe.congr (by
    intro n
    simpa [z] using step22OmegaArchWeightReSeriesTerm_eq_complex_re eta n)

/-- Direct real-series expansion for `step22OmegaArchWeight`.

This is the checked semantic source for future generated
`hAnchorLower`/`hAnchorUpper` rows in
`Step22OmegaClosedFormEndpointBoundsCert.of_direct_anchor_...`. -/
theorem step22OmegaArchWeight_eq_re_series (eta : Real) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta =
      -Real.eulerMascheroniConstant - Real.log Real.pi +
        ∑' n : Nat, step22OmegaArchWeightReSeriesTerm eta n := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  have hzpos : 0 < z.re := by
    norm_num [z]
  have hzNonzero : ∀ n : Nat, z + n ≠ 0 := by
    intro n hzero
    have hre := congrArg Complex.re hzero
    have hn : 0 <= (n : Real) := by
      exact_mod_cast Nat.zero_le n
    norm_num [z, Complex.add_re, Complex.mul_re] at hre
    linarith
  have hdig :=
    Q3.re_digamma_eq_sum_of_tendsto z hzNonzero
      (Q3.digammaSeq_tendsto_Q3_digamma z hzpos)
  have hterms :
      (∑' n : Nat, (1 / ((n : Complex) + 1) - 1 / (z + n)).re) =
        ∑' n : Nat, step22OmegaArchWeightReSeriesTerm eta n := by
    apply tsum_congr
    intro n
    simpa [z] using step22OmegaArchWeightReSeriesTerm_eq_complex_re eta n
  calc
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta =
        (Q3.digamma z).re - Real.log Real.pi := by
          simp [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight, z]
    _ = (-Real.eulerMascheroniConstant +
          ∑' n : Nat, (1 / ((n : Complex) + 1) - 1 / (z + n)).re) -
          Real.log Real.pi := by
          rw [hdig]
    _ = -Real.eulerMascheroniConstant - Real.log Real.pi +
          ∑' n : Nat, step22OmegaArchWeightReSeriesTerm eta n := by
          rw [hterms]
          ring

/-- Convert generated constant bounds, finite-prefix bounds, and an absolute
tail bound for the direct real series into Omega anchor bounds. -/
theorem step22OmegaArchWeight_bounds_from_re_series_prefix_tail_abs
    (eta lower upper constLower constUpper prefixLower prefixUpper tailRadius :
      Real)
    (N : Nat)
    (hConstLower :
      constLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= constUpper)
    (hPrefixLower :
      prefixLower <=
        (Finset.range N).sum (step22OmegaArchWeightReSeriesTerm eta))
    (hPrefixUpper :
      (Finset.range N).sum (step22OmegaArchWeightReSeriesTerm eta) <=
        prefixUpper)
    (hTail :
      |∑' n : Nat, step22OmegaArchWeightReSeriesTerm eta (n + N)| <=
        tailRadius)
    (hLower : lower <= constLower + prefixLower - tailRadius)
    (hUpper : constUpper + prefixUpper + tailRadius <= upper) :
    lower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
        upper := by
  have hsum :=
    tsum_bounds_of_sum_range_tail_abs
      (f := step22OmegaArchWeightReSeriesTerm eta) N prefixLower prefixUpper
      tailRadius (summable_step22OmegaArchWeightReSeriesTerm eta)
      hPrefixLower hPrefixUpper hTail
  have hseries := step22OmegaArchWeight_eq_re_series eta
  constructor
  · rw [hseries]
    calc
      lower <= constLower + prefixLower - tailRadius := hLower
      _ <= (-Real.eulerMascheroniConstant - Real.log Real.pi) +
          prefixLower - tailRadius := by
        linarith
      _ <= (-Real.eulerMascheroniConstant - Real.log Real.pi) +
            (∑' n : Nat, step22OmegaArchWeightReSeriesTerm eta n) := by
        linarith [hsum.1]
  · rw [hseries]
    calc
      (-Real.eulerMascheroniConstant - Real.log Real.pi) +
          (∑' n : Nat, step22OmegaArchWeightReSeriesTerm eta n) <=
          constUpper + prefixUpper + tailRadius := by
        linarith [hsum.2]
      _ <= upper := hUpper

/-- Real-part chain rule for the Step22 Omega digamma profile. -/
theorem deriv_re_q3_digamma_half (eta : Real) :
    deriv
        (fun t : Real =>
          (Q3.digamma
            ((1 / 4 : Complex) + Complex.I * (((t / 2 : Real) : Complex)))).re)
        eta =
      -((deriv (fun z : Complex => Q3.digamma z)
          ((1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex)))).im *
        (1 / 2 : Real)) := by
  let z0 : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  have hzPos : 0 < z0.re := by
    dsimp [z0]
    norm_num [Complex.add_re, Complex.mul_re]
  have hDiff :
      DifferentiableAt Complex (fun z : Complex => Q3.digamma z) z0 := by
    exact
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.digamma_differentiableAt_of_re_pos
        hzPos
  have hChain :
      HasDerivAt
        (fun t : Real =>
          Q3.digamma
            ((1 / 4 : Complex) + Complex.I * (((t / 2 : Real) : Complex))))
        (deriv (fun z : Complex => Q3.digamma z) z0 * (Complex.I / 2))
        eta := by
    have hz :
        HasDerivAt
          (fun t : Real =>
            (1 / 4 : Complex) + Complex.I * (((t / 2 : Real) : Complex)))
          (Complex.I / 2) eta := by
      convert
        HasDerivAt.add (hasDerivAt_const _ _)
          (HasDerivAt.mul (hasDerivAt_const _ _)
            ((hasDerivAt_id eta).div_const (2 : Real) |>.ofReal_comp))
        using 1
      · norm_num [div_eq_mul_inv]
    simpa [z0] using HasDerivAt.comp eta hDiff.hasDerivAt hz
  have hReal :
      HasDerivAt
        (fun t : Real =>
          (Q3.digamma
            ((1 / 4 : Complex) + Complex.I * (((t / 2 : Real) : Complex)))).re)
        ((deriv (fun z : Complex => Q3.digamma z) z0 *
            (Complex.I / 2)).re)
        eta := by
    simpa [Function.comp_def] using
      ((Complex.reCLM : Complex →L[Real] Real).hasFDerivAt.comp_hasDerivAt
        eta hChain)
  have hValue :
      (deriv (fun z : Complex => Q3.digamma z) z0 * (Complex.I / 2)).re =
        -((deriv (fun z : Complex => Q3.digamma z) z0).im *
          (1 / 2 : Real)) := by
    norm_num [div_eq_mul_inv, Complex.mul_re, Complex.mul_im]
  simpa [z0, hValue] using hReal.deriv

/-- The Step22 Omega derivative is the trigamma closed form. -/
theorem step22OmegaArchWeight_deriv_eq_closedForm (eta : Real) :
    deriv
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta =
      step22OmegaArchWeightDerivClosedForm eta := by
  unfold
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
    step22OmegaArchWeightDerivClosedForm
  rw [deriv_sub_const]
  rw [deriv_re_q3_digamma_half eta]
  have hzPos :
      0 <
        (((1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))).re) := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hTrigamma :
      deriv (fun z : Complex => Q3.digamma z)
          ((1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))) =
        trigamma
          ((1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))) := by
    simpa [Q3.digamma, digamma] using deriv_digamma_eq_trigamma hzPos
  rw [hTrigamma]

/-- Interval wrapper for generated Omega derivative closed-form bounds. -/
theorem step22OmegaArchWeight_deriv_eq_closedForm_on_Icc
    {a b : Real} :
    ∀ eta ∈ Set.Icc a b,
      deriv
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta =
        step22OmegaArchWeightDerivClosedForm eta := by
  intro eta _
  exact step22OmegaArchWeight_deriv_eq_closedForm eta

/-- Proof-bearing endpoint package for the raw Step22 Omega weight.

Generated endpoint rows should target this compact surface: it carries the two
uniform derivative interval facts on `Set.Icc a b` and the two anchor value
facts for `step22OmegaArchWeight`. -/
structure Step22OmegaEndpointIntervalCert
    (a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper : Real) : Prop where
  hDerivLower :
    ∀ eta ∈ Set.Icc a b,
      omegaDerivLower <=
        deriv
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta
  hDerivUpper :
    ∀ eta ∈ Set.Icc a b,
      deriv
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta <= omegaDerivUpper
  hAnchorLower :
    omegaAnchorLower <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
        anchor
  hAnchorUpper :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
        anchor <= omegaAnchorUpper

/-- Build the Omega endpoint cert from a closed-form derivative identity and
closed-form interval bounds.

This is the generic A-first receiver requested by the route review: prove the
derivative closed form once, generate rational lower/upper bounds for that
closed form per row, and then feed the compact
`Step22OmegaEndpointIntervalCert` surface. -/
theorem step22OmegaArchWeight_endpointValueDerivIntervalCert_of_closedForm_bounds
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper : Real}
    {omegaDerivClosedForm : Real → Real}
    (hDerivEq :
      ∀ eta ∈ Set.Icc a b,
        deriv
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta =
            omegaDerivClosedForm eta)
    (hDerivLower :
      ∀ eta ∈ Set.Icc a b,
        omegaDerivLower <= omegaDerivClosedForm eta)
    (hDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        omegaDerivClosedForm eta <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <= omegaAnchorUpper) :
    Step22OmegaEndpointIntervalCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  refine ⟨?_, ?_, hAnchorLower, hAnchorUpper⟩
  · intro eta heta
    rw [hDerivEq eta heta]
    exact hDerivLower eta heta
  · intro eta heta
    rw [hDerivEq eta heta]
    exact hDerivUpper eta heta

/-- Proof-bearing closed-form endpoint package for the raw Step22 Omega weight.

Generated endpoint rows should now materialize this structure first: the
derivative facts are stated against the checked closed form, while the anchor
facts remain statements about the actual Step22 Omega weight. -/
structure Step22OmegaClosedFormEndpointBoundsCert
    (a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper : Real) : Prop where
  hDerivLower :
    ∀ eta ∈ Set.Icc a b,
      omegaDerivLower <= step22OmegaArchWeightDerivClosedForm eta
  hDerivUpper :
    ∀ eta ∈ Set.Icc a b,
      step22OmegaArchWeightDerivClosedForm eta <= omegaDerivUpper
  hAnchorLower :
    omegaAnchorLower <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
        anchor
  hAnchorUpper :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
        anchor <= omegaAnchorUpper

/-- Build the raw Step22 Omega endpoint package using the checked Stieltjes
anchor bridge.

This keeps the generated endpoint package proof-safe without asking each row
to prove a direct digamma value enclosure at the anchor.  Generated rows still
need derivative enclosures and rational checks for the Stieltjes main/error
anchor enclosure. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_anchor_bounds
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper : Real}
    (hDerivLower :
      ∀ eta ∈ Set.Icc a b,
        omegaDerivLower <= step22OmegaArchWeightDerivClosedForm eta)
    (hDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        step22OmegaArchWeightDerivClosedForm eta <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor -
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor +
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  have hAnchor :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_anchor_bounds_from_stieltjes
      anchor omegaAnchorLower omegaAnchorUpper hAnchorLower hAnchorUpper
  exact
    { hDerivLower := hDerivLower
      hDerivUpper := hDerivUpper
      hAnchorLower := hAnchor.1
      hAnchorUpper := hAnchor.2 }

/-- Build the raw Step22 Omega endpoint package directly from Stieltjes anchor
enclosures and uniform two-sided bounds for the trigamma imaginary series.

Generated endpoint rows can now prove finite-sum/tail bounds for the series,
then use this checked constructor to obtain the Omega endpoint package. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_series_bounds
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imLower imUpper : Real}
    (hImLower :
      ∀ eta ∈ Set.Icc a b,
        imLower <=
          ∑' n : Nat,
            (1 /
                (((1 / 4 : Complex) +
                      Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
    (hImUpper :
      ∀ eta ∈ Set.Icc a b,
        (∑' n : Nat,
            (1 /
                (((1 / 4 : Complex) +
                      Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
          <= imUpper)
    (hDerivLower : omegaDerivLower <= -(imUpper * (1 / 2 : Real)))
    (hDerivUpper : -(imLower * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor -
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor +
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  refine
    Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_anchor_bounds
      ?_ ?_ hAnchorLower hAnchorUpper
  · intro eta heta
    exact
      (step22OmegaArchWeightDerivClosedForm_bounds_from_trigamma_im_series
        eta imLower imUpper omegaDerivLower omegaDerivUpper
        (hImLower eta heta) (hImUpper eta heta) hDerivLower hDerivUpper).1
  · intro eta heta
    exact
      (step22OmegaArchWeightDerivClosedForm_bounds_from_trigamma_im_series
        eta imLower imUpper omegaDerivLower omegaDerivUpper
        (hImLower eta heta) (hImUpper eta heta) hDerivLower hDerivUpper).2

/-- Build the raw Step22 Omega endpoint package from finite-prefix trigamma
intervals and a summable tail majorant.

This is the generator-facing Omega landing surface for
`rawOmegaEndpointClosedFormBounds_generated`: generated rows can supply
rational bounds for the finite prefix, a pointwise absolute majorant for the
tail, and a rational bound for the majorant sum. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_series_prefix_tail_majorant
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imPrefixLower imPrefixUpper tailRadius : Real}
    (N : Nat) (g : Nat -> Real)
    (hg : Summable g)
    (hPrefixLower :
      ∀ eta ∈ Set.Icc a b,
        imPrefixLower <=
          (Finset.range N).sum (fun n : Nat =>
            (1 /
                (((1 / 4 : Complex) +
                      Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im))
    (hPrefixUpper :
      ∀ eta ∈ Set.Icc a b,
        (Finset.range N).sum (fun n : Nat =>
            (1 /
                (((1 / 4 : Complex) +
                      Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
          <= imPrefixUpper)
    (hTailTerm :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat,
        |(1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((eta / 2 : Real) : Complex))) + (n + N)) ^ 2).im| <=
          g n)
    (hTailSum : (∑' n : Nat, g n) <= tailRadius)
    (hDerivLower :
      omegaDerivLower <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor -
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor +
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  refine
    Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_series_bounds
      (imLower := imPrefixLower - tailRadius)
      (imUpper := imPrefixUpper + tailRadius)
      ?_ ?_ hDerivLower hDerivUpper hAnchorLower hAnchorUpper
  · intro eta heta
    exact
      (trigamma_im_series_bounds_of_sum_range_tail_abs eta N imPrefixLower
        imPrefixUpper tailRadius (hPrefixLower eta heta)
        (hPrefixUpper eta heta)
        (trigamma_im_series_tail_abs_le_of_majorant eta N g tailRadius hg
          (hTailTerm eta heta) hTailSum)).1
  · intro eta heta
    exact
      (trigamma_im_series_bounds_of_sum_range_tail_abs eta N imPrefixLower
        imPrefixUpper tailRadius (hPrefixLower eta heta)
        (hPrefixUpper eta heta)
        (trigamma_im_series_tail_abs_le_of_majorant eta N g tailRadius hg
          (hTailTerm eta heta) hTailSum)).2

/-- Build the raw Step22 Omega endpoint package from termwise finite-prefix
bounds plus a summable tail majorant.

This is the most generator-friendly Omega endpoint surface: a row generator can
emit rational interval bounds for each finite-prefix term, rational comparisons
from the term sums to the selected prefix interval, and the existing tail
majorant data. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_series_term_prefix_tail_majorant
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imPrefixLower imPrefixUpper tailRadius : Real}
    (N : Nat) (termLower termUpper g : Nat -> Real)
    (hg : Summable g)
    (hTermLower :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        termLower n <=
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im)
    (hTermUpper :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        (1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im <=
          termUpper n)
    (hPrefixLower : imPrefixLower <= (Finset.range N).sum termLower)
    (hPrefixUpper : (Finset.range N).sum termUpper <= imPrefixUpper)
    (hTailTerm :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat,
        |(1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((eta / 2 : Real) : Complex))) + (n + N)) ^ 2).im| <=
          g n)
    (hTailSum : (∑' n : Nat, g n) <= tailRadius)
    (hDerivLower :
      omegaDerivLower <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor -
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor +
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  refine
    Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_series_prefix_tail_majorant
      N g hg ?_ ?_ hTailTerm hTailSum hDerivLower hDerivUpper
      hAnchorLower hAnchorUpper
  · intro eta heta
    exact le_trans hPrefixLower
      (trigamma_im_series_prefix_bounds_of_term_bounds eta N termLower
        termUpper
        (fun n hn => hTermLower eta heta n hn)
        (fun n hn => hTermUpper eta heta n hn)).1
  · intro eta heta
    exact le_trans
      (trigamma_im_series_prefix_bounds_of_term_bounds eta N termLower
        termUpper
        (fun n hn => hTermLower eta heta n hn)
        (fun n hn => hTermUpper eta heta n hn)).2
      hPrefixUpper

/-- Build the raw Step22 Omega endpoint package from real closed-form
termwise bounds plus a summable tail majorant.

This is the intended generated-row landing surface after expanding each
trigamma-imaginary term with `trigammaImSeriesTermClosedForm`: all row-specific
term and tail estimates become ordinary real rational-function interval
checks. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_closed_form_term_prefix_tail_majorant
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imPrefixLower imPrefixUpper tailRadius : Real}
    (N : Nat) (termLower termUpper g : Nat -> Real)
    (hg : Summable g)
    (hTermLower :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        termLower n <= trigammaImSeriesTermClosedForm eta n)
    (hTermUpper :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        trigammaImSeriesTermClosedForm eta n <= termUpper n)
    (hPrefixLower : imPrefixLower <= (Finset.range N).sum termLower)
    (hPrefixUpper : (Finset.range N).sum termUpper <= imPrefixUpper)
    (hTailTerm :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat,
        |trigammaImSeriesTermClosedForm eta (n + N)| <= g n)
    (hTailSum : (∑' n : Nat, g n) <= tailRadius)
    (hDerivLower :
      omegaDerivLower <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor -
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor +
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  refine
    Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_series_term_prefix_tail_majorant
      N termLower termUpper g hg ?_ ?_ hPrefixLower hPrefixUpper ?_
      hTailSum hDerivLower hDerivUpper hAnchorLower hAnchorUpper
  · intro eta heta n hn
    rw [trigamma_im_series_term_eq_closed_form]
    exact hTermLower eta heta n hn
  · intro eta heta n hn
    rw [trigamma_im_series_term_eq_closed_form]
    exact hTermUpper eta heta n hn
  · intro eta heta n
    have hraw :
        |(1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((eta / 2 : Real) : Complex))) + (n + N)) ^ 2).im| <=
          g n := by
      have hcast :
          ((n + N : Nat) : Complex) = (n : Complex) + (N : Complex) := by
        exact_mod_cast Nat.cast_add n N
      rw [← hcast]
      rw [trigamma_im_series_term_eq_closed_form]
      exact hTailTerm eta heta n
    simpa [Nat.cast_add] using hraw

/-- Build the raw Step22 Omega endpoint package from real closed-form
termwise bounds and the canonical cubic tail majorant.

Generated endpoint rows only need to supply a uniform positive-axis `etaUpper`
and the rational `tsum` comparison for that cubic majorant; Lean supplies the
majorant function, its summability, and the pointwise tail-term proof. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_closed_form_term_prefix_cubic_tail
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imPrefixLower imPrefixUpper tailRadius etaUpper : Real}
    (N : Nat) (termLower termUpper : Nat -> Real)
    (hEtaNonneg : ∀ eta ∈ Set.Icc a b, 0 <= eta)
    (hEtaUpper : ∀ eta ∈ Set.Icc a b, eta <= etaUpper)
    (hTermLower :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        termLower n <= trigammaImSeriesTermClosedForm eta n)
    (hTermUpper :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        trigammaImSeriesTermClosedForm eta n <= termUpper n)
    (hPrefixLower : imPrefixLower <= (Finset.range N).sum termLower)
    (hPrefixUpper : (Finset.range N).sum termUpper <= imPrefixUpper)
    (hTailSum :
      (∑' n : Nat,
        etaUpper / ((((n + N : Nat) : Real) + (1 / 4 : Real)) ^ 3)) <= tailRadius)
    (hDerivLower :
      omegaDerivLower <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor -
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor +
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  refine
    Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_closed_form_term_prefix_tail_majorant
      N termLower termUpper
      (fun n : Nat =>
        etaUpper / ((((n + N : Nat) : Real) + (1 / 4 : Real)) ^ 3))
      (summable_trigammaImSeriesTermClosedForm_cubic_majorant etaUpper N)
      hTermLower hTermUpper hPrefixLower hPrefixUpper ?_ hTailSum
      hDerivLower hDerivUpper hAnchorLower hAnchorUpper
  intro eta heta n
  simpa using
    (abs_trigammaImSeriesTermClosedForm_le_etaUpper_cubic
      (eta := eta) (etaUpper := etaUpper) (n + N)
      (hEtaNonneg eta heta) (hEtaUpper eta heta))

/-- Variant of the cubic-tail endpoint constructor where the positive-axis
facts are generated as endpoint inequalities. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imPrefixLower imPrefixUpper tailRadius etaUpper : Real}
    (N : Nat) (termLower termUpper : Nat -> Real)
    (hANonneg : 0 <= a)
    (hBUpper : b <= etaUpper)
    (hTermLower :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        termLower n <= trigammaImSeriesTermClosedForm eta n)
    (hTermUpper :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        trigammaImSeriesTermClosedForm eta n <= termUpper n)
    (hPrefixLower : imPrefixLower <= (Finset.range N).sum termLower)
    (hPrefixUpper : (Finset.range N).sum termUpper <= imPrefixUpper)
    (hTailSum :
      (∑' n : Nat,
        etaUpper / ((((n + N : Nat) : Real) + (1 / 4 : Real)) ^ 3)) <= tailRadius)
    (hDerivLower :
      omegaDerivLower <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor -
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesMain
          anchor +
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightStieltjesErr
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  refine
    Step22OmegaClosedFormEndpointBoundsCert.of_stieltjes_trigamma_im_closed_form_term_prefix_cubic_tail
      N termLower termUpper ?_ ?_ hTermLower hTermUpper hPrefixLower hPrefixUpper
      hTailSum hDerivLower hDerivUpper hAnchorLower hAnchorUpper
  · intro eta heta
    exact le_trans hANonneg heta.1
  · intro eta heta
    exact le_trans heta.2 hBUpper

/-- Build the raw Step22 Omega endpoint package from real closed-form
termwise bounds and the canonical cubic tail majorant, while taking the
anchor bounds directly against `step22OmegaArchWeight`.

This is the corrected generator-facing surface for small-eta endpoint rows:
the Stieltjes main-plus-or-minus-error anchor enclosure is too coarse for the
tight direct anchor intervals used by the refined subchunk route, but the
derivative side still uses the checked trigamma prefix/cubic-tail machinery. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_direct_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imPrefixLower imPrefixUpper tailRadius etaUpper : Real}
    (N : Nat) (termLower termUpper : Nat -> Real)
    (hANonneg : 0 <= a)
    (hBUpper : b <= etaUpper)
    (hTermLower :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        termLower n <= trigammaImSeriesTermClosedForm eta n)
    (hTermUpper :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < N ->
        trigammaImSeriesTermClosedForm eta n <= termUpper n)
    (hPrefixLower : imPrefixLower <= (Finset.range N).sum termLower)
    (hPrefixUpper : (Finset.range N).sum termUpper <= imPrefixUpper)
    (hTailSum :
      (∑' n : Nat,
        etaUpper / ((((n + N : Nat) : Real) + (1 / 4 : Real)) ^ 3)) <= tailRadius)
    (hDerivLower :
      omegaDerivLower <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <= omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  have hImBounds :
      ∀ eta ∈ Set.Icc a b,
        imPrefixLower - tailRadius <=
            ∑' n : Nat,
              (1 /
                  (((1 / 4 : Complex) +
                        Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im ∧
          (∑' n : Nat,
              (1 /
                  (((1 / 4 : Complex) +
                        Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im) <=
            imPrefixUpper + tailRadius := by
    intro eta heta
    have hEtaNonneg : 0 <= eta := le_trans hANonneg heta.1
    have hEtaUpper : eta <= etaUpper := le_trans heta.2 hBUpper
    have hPrefixBounds :=
      trigamma_im_series_prefix_bounds_of_term_bounds eta N termLower
        termUpper
        (fun n hn => by
          rw [trigamma_im_series_term_eq_closed_form]
          exact hTermLower eta heta n hn)
        (fun n hn => by
          rw [trigamma_im_series_term_eq_closed_form]
          exact hTermUpper eta heta n hn)
    have hTail :
        |∑' n : Nat,
          (1 /
              (((1 / 4 : Complex) +
                    Complex.I * (((eta / 2 : Real) : Complex))) + (n + N)) ^ 2).im| <=
          tailRadius := by
      refine
        trigamma_im_series_tail_abs_le_of_majorant eta N
          (fun n : Nat =>
            etaUpper / ((((n + N : Nat) : Real) + (1 / 4 : Real)) ^ 3))
          tailRadius
          (summable_trigammaImSeriesTermClosedForm_cubic_majorant etaUpper N)
          ?_ hTailSum
      intro n
      have hcast :
          ((n + N : Nat) : Complex) = (n : Complex) + (N : Complex) := by
        exact_mod_cast Nat.cast_add n N
      rw [← hcast]
      rw [trigamma_im_series_term_eq_closed_form]
      exact
        abs_trigammaImSeriesTermClosedForm_le_etaUpper_cubic
          (eta := eta) (etaUpper := etaUpper) (n + N) hEtaNonneg hEtaUpper
    exact
      trigamma_im_series_bounds_of_sum_range_tail_abs eta N
        imPrefixLower imPrefixUpper tailRadius
        (le_trans hPrefixLower hPrefixBounds.1)
        (le_trans hPrefixBounds.2 hPrefixUpper)
        hTail
  refine
    { hDerivLower := ?_
      hDerivUpper := ?_
      hAnchorLower := hAnchorLower
      hAnchorUpper := hAnchorUpper }
  · intro eta heta
    exact
      (step22OmegaArchWeightDerivClosedForm_bounds_from_trigamma_im_series
        eta (imPrefixLower - tailRadius) (imPrefixUpper + tailRadius)
        omegaDerivLower omegaDerivUpper
        (hImBounds eta heta).1 (hImBounds eta heta).2
        hDerivLower hDerivUpper).1
  · intro eta heta
    exact
      (step22OmegaArchWeightDerivClosedForm_bounds_from_trigamma_im_series
        eta (imPrefixLower - tailRadius) (imPrefixUpper + tailRadius)
        omegaDerivLower omegaDerivUpper
        (hImBounds eta heta).1 (hImBounds eta heta).2
        hDerivLower hDerivUpper).2

/-- Build the raw Step22 Omega endpoint package from the checked direct
Omega-anchor real series and the trigamma finite-prefix/cubic-tail derivative
route.

This is the compact generator-facing endpoint receiver for the active
refined-subchunk route: generated rows may keep separate prefix lengths for the
derivative trigamma series and the direct anchor re-series, while Lean performs
the common composition into `Step22OmegaClosedFormEndpointBoundsCert`. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.of_re_series_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper imPrefixLower imPrefixUpper tailRadius etaUpper
      anchorConstLower anchorConstUpper anchorPrefixLower anchorPrefixUpper
      anchorTailRadius : Real}
    (derivN anchorN : Nat) (termLower termUpper : Nat -> Real)
    (hANonneg : 0 <= a)
    (hBUpper : b <= etaUpper)
    (hTermLower :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < derivN ->
        termLower n <= trigammaImSeriesTermClosedForm eta n)
    (hTermUpper :
      ∀ eta ∈ Set.Icc a b, ∀ n : Nat, n < derivN ->
        trigammaImSeriesTermClosedForm eta n <= termUpper n)
    (hPrefixLower : imPrefixLower <= (Finset.range derivN).sum termLower)
    (hPrefixUpper : (Finset.range derivN).sum termUpper <= imPrefixUpper)
    (hTailSum :
      (∑' n : Nat,
        etaUpper / ((((n + derivN : Nat) : Real) + (1 / 4 : Real)) ^ 3)) <=
          tailRadius)
    (hDerivLower :
      omegaDerivLower <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <= omegaDerivUpper)
    (hAnchorConstLower :
      anchorConstLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hAnchorConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= anchorConstUpper)
    (hAnchorPrefixLower :
      anchorPrefixLower <=
        (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm anchor))
    (hAnchorPrefixUpper :
      (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm anchor) <=
        anchorPrefixUpper)
    (hAnchorTailAbs :
      |∑' n : Nat, step22OmegaArchWeightReSeriesTerm anchor (n + anchorN)| <=
        anchorTailRadius)
    (hAnchorLowerFromReSeries :
      omegaAnchorLower <=
        anchorConstLower + anchorPrefixLower - anchorTailRadius)
    (hAnchorUpperFromReSeries :
      anchorConstUpper + anchorPrefixUpper + anchorTailRadius <=
        omegaAnchorUpper) :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper := by
  have hAnchor :=
    step22OmegaArchWeight_bounds_from_re_series_prefix_tail_abs
      anchor omegaAnchorLower omegaAnchorUpper anchorConstLower
      anchorConstUpper anchorPrefixLower anchorPrefixUpper anchorTailRadius
      anchorN hAnchorConstLower hAnchorConstUpper hAnchorPrefixLower
      hAnchorPrefixUpper hAnchorTailAbs hAnchorLowerFromReSeries
      hAnchorUpperFromReSeries
  exact
    Step22OmegaClosedFormEndpointBoundsCert.of_direct_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
      derivN termLower termUpper hANonneg hBUpper hTermLower hTermUpper
      hPrefixLower hPrefixUpper hTailSum hDerivLower hDerivUpper
      hAnchor.1 hAnchor.2

/-- Convert the closed-form endpoint package into the existing raw Step22 Omega
endpoint interval cert.  This is the proof-safe target for
`rawOmegaEndpointClosedFormBounds_generated`: row payloads may instantiate the
closed-form structure, and Lean supplies the derivative identity bridge here. -/
theorem Step22OmegaClosedFormEndpointBoundsCert.toStep22OmegaEndpointIntervalCert
    {a b anchor omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper : Real}
    (cert :
      Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
        omegaDerivUpper omegaAnchorLower omegaAnchorUpper) :
    Step22OmegaEndpointIntervalCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper :=
  step22OmegaArchWeight_endpointValueDerivIntervalCert_of_closedForm_bounds
    (omegaDerivClosedForm := step22OmegaArchWeightDerivClosedForm)
    step22OmegaArchWeight_deriv_eq_closedForm_on_Icc
    cert.hDerivLower cert.hDerivUpper cert.hAnchorLower cert.hAnchorUpper

/-- Build a local component interval certificate from derivative and anchor
value interval enclosures, using Lean-computed slope/error radii.

This is the next generated-payload surface below
`of_anchor_deriv_bounds_auto_differentiability`: generated code may prove
ordinary two-sided intervals for the derivatives on `Set.Icc a b` and for the
two anchor values.  Lean converts those intervals into nonnegative derivative
slopes and center-error bounds, then feeds the checked derivative receiver. -/
theorem LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_auto_differentiability
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper
      shapeSqLower shapeSqUpper omegaCenter omegaRadius shapeSqCenter
      shapeSqRadius omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper shapeSqDerivLower shapeSqDerivUpper shapeSqAnchorLower
      shapeSqAnchorUpper : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hEtaLeft : anchor - a <= etaRadius)
    (hEtaRight : b - anchor <= etaRadius)
    (hOmegaDerivLower :
      ∀ eta ∈ Set.Icc a b,
        omegaDerivLower <=
          deriv
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            eta)
    (hOmegaDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            eta <= omegaDerivUpper)
    (hOmegaAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <= omegaAnchorUpper)
    (hOmegaContain :
      intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
          intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
            omegaCenter <=
        omegaRadius)
    (hShapeSqDerivLower :
      ∀ eta ∈ Set.Icc a b,
        shapeSqDerivLower <=
          deriv
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
            eta)
    (hShapeSqDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            (fun t : Real =>
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
            eta <= shapeSqDerivUpper)
    (hShapeSqAnchorLower :
      shapeSqAnchorLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqAnchorUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqAnchorUpper)
    (hShapeSqContain :
      intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
          intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
            shapeSqCenter <=
        shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  refine
    LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds_auto_differentiability
      hAnchorIn hEtaLeft hEtaRight ?_ ?_ (le_rfl) ?_ hOmegaContain ?_
      ?_ (le_rfl) ?_ hShapeSqContain hOmegaLower hOmegaUpper
      hShapeSqLower hShapeSqUpper
  · intro eta heta
    exact
      norm_le_intervalAutoAbsBound_of_interval_bounds
        (hOmegaDerivLower eta heta) (hOmegaDerivUpper eta heta)
  · exact intervalAutoAbsBound_nonneg omegaDerivLower omegaDerivUpper
  · exact
      abs_sub_center_le_intervalAutoCenterError_of_interval_bounds
        hOmegaAnchorLower hOmegaAnchorUpper
  · intro eta heta
    exact
      norm_le_intervalAutoAbsBound_of_interval_bounds
        (hShapeSqDerivLower eta heta) (hShapeSqDerivUpper eta heta)
  · exact intervalAutoAbsBound_nonneg shapeSqDerivLower shapeSqDerivUpper
  · exact
      abs_sub_center_le_intervalAutoCenterError_of_interval_bounds
        hShapeSqAnchorLower hShapeSqAnchorUpper

/-- Variant of the endpoint-interval receiver that reduces the shape-square
derivative facts to endpoint intervals for the closed-form component `E` and
its derivative `E'`.

This keeps generated payloads away from the opaque `deriv (fun t => E t ^ 2)`
expression: they may instead prove ordinary `E`/`E'` interval enclosures and
four rational corner comparisons for `2 * E * E'`. -/
theorem LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_shapeSq_closedForm_auto_differentiability
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper
      shapeSqLower shapeSqUpper omegaCenter omegaRadius shapeSqCenter
      shapeSqRadius omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper shapeValueLower shapeValueUpper shapeDerivLower
      shapeDerivUpper shapeSqDerivLower shapeSqDerivUpper shapeSqAnchorLower
      shapeSqAnchorUpper : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hEtaLeft : anchor - a <= etaRadius)
    (hEtaRight : b - anchor <= etaRadius)
    (hOmegaDerivLower :
      ∀ eta ∈ Set.Icc a b,
        omegaDerivLower <=
          deriv
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            eta)
    (hOmegaDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
            eta <= omegaDerivUpper)
    (hOmegaAnchorLower :
      omegaAnchorLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <= omegaAnchorUpper)
    (hOmegaContain :
      intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
          intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
            omegaCenter <=
        omegaRadius)
    (hShapeValueLower :
      ∀ eta ∈ Set.Icc a b,
        shapeValueLower <=
          centeredBSplineImagTransformRealClosedForm k ell eta)
    (hShapeValueUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedForm k ell eta <=
          shapeValueUpper)
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc a b,
        shapeDerivLower <=
          deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta <= shapeDerivUpper)
    (hShapeSqDerivLowerLL :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivLower)
    (hShapeSqDerivLowerLU :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivUpper)
    (hShapeSqDerivLowerUL :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivLower)
    (hShapeSqDerivLowerUU :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivUpper)
    (hShapeSqDerivUpperLL :
      2 * shapeValueLower * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperLU :
      2 * shapeValueLower * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUL :
      2 * shapeValueUpper * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUU :
      2 * shapeValueUpper * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqAnchorLower :
      shapeSqAnchorLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqAnchorUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqAnchorUpper)
    (hShapeSqContain :
      intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
          intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
            shapeSqCenter <=
        shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  have hShapeSqDeriv :=
    shapeSqDeriv_interval_bounds_on_Icc_of_closedForm_value_deriv_intervals
      hShapeValueLower hShapeValueUpper hShapeDerivLower hShapeDerivUpper
      hShapeSqDerivLowerLL hShapeSqDerivLowerLU hShapeSqDerivLowerUL
      hShapeSqDerivLowerUU hShapeSqDerivUpperLL hShapeSqDerivUpperLU
      hShapeSqDerivUpperUL hShapeSqDerivUpperUU
  exact
    LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_auto_differentiability
      hAnchorIn hEtaLeft hEtaRight hOmegaDerivLower hOmegaDerivUpper
      hOmegaAnchorLower hOmegaAnchorUpper hOmegaContain hShapeSqDeriv.1
      hShapeSqDeriv.2 hShapeSqAnchorLower hShapeSqAnchorUpper
      hShapeSqContain hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper

/-- Same v5 local component receiver, but with the Omega endpoint facts packed
as a single proof-bearing `Step22OmegaEndpointIntervalCert`. -/
theorem LocalRawOmegaComponentIntervalCert.of_omega_endpoint_cert_shapeSq_closedForm_auto_differentiability
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper
      shapeSqLower shapeSqUpper omegaCenter omegaRadius shapeSqCenter
      shapeSqRadius omegaDerivLower omegaDerivUpper omegaAnchorLower
      omegaAnchorUpper shapeValueLower shapeValueUpper shapeDerivLower
      shapeDerivUpper shapeSqDerivLower shapeSqDerivUpper shapeSqAnchorLower
      shapeSqAnchorUpper : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hEtaLeft : anchor - a <= etaRadius)
    (hEtaRight : b - anchor <= etaRadius)
    (hOmega :
      Step22OmegaEndpointIntervalCert a b anchor omegaDerivLower
        omegaDerivUpper omegaAnchorLower omegaAnchorUpper)
    (hOmegaContain :
      intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
          intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
            omegaCenter <=
        omegaRadius)
    (hShapeValueLower :
      ∀ eta ∈ Set.Icc a b,
        shapeValueLower <=
          centeredBSplineImagTransformRealClosedForm k ell eta)
    (hShapeValueUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedForm k ell eta <=
          shapeValueUpper)
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc a b,
        shapeDerivLower <=
          deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta <= shapeDerivUpper)
    (hShapeSqDerivLowerLL :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivLower)
    (hShapeSqDerivLowerLU :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivUpper)
    (hShapeSqDerivLowerUL :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivLower)
    (hShapeSqDerivLowerUU :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivUpper)
    (hShapeSqDerivUpperLL :
      2 * shapeValueLower * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperLU :
      2 * shapeValueLower * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUL :
      2 * shapeValueUpper * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUU :
      2 * shapeValueUpper * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqAnchorLower :
      shapeSqAnchorLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqAnchorUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqAnchorUpper)
    (hShapeSqContain :
      intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
          intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
            shapeSqCenter <=
        shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  exact
    LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_shapeSq_closedForm_auto_differentiability
      hAnchorIn hEtaLeft hEtaRight hOmega.hDerivLower hOmega.hDerivUpper
      hOmega.hAnchorLower hOmega.hAnchorUpper hOmegaContain
      hShapeValueLower hShapeValueUpper hShapeDerivLower hShapeDerivUpper
      hShapeSqDerivLowerLL hShapeSqDerivLowerLU hShapeSqDerivLowerUL
      hShapeSqDerivLowerUU hShapeSqDerivUpperLL hShapeSqDerivUpperLU
      hShapeSqDerivUpperUL hShapeSqDerivUpperUU hShapeSqAnchorLower
      hShapeSqAnchorUpper hShapeSqContain hOmegaLower hOmegaUpper
      hShapeSqLower hShapeSqUpper

/-- Generated payload target for one local component endpoint interval cert in
the closed-form route.

Compared to `LocalRawOmegaComponentEndpointIntervalCert`, the Omega side is
packed as a `Step22OmegaClosedFormEndpointBoundsCert`, and the shape-square
derivative side is expressed through interval enclosures for the closed-form
component `E` and its derivative `E'`.  Generated rows still have to prove the
analytic endpoint facts and the rational corner/containment comparisons; this
structure only gives those facts a proof-safe landing surface. -/
structure LocalRawOmegaComponentClosedFormEndpointIntervalCert
    (k : Nat) (ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius : Real) where
  omegaDerivLower : Real
  omegaDerivUpper : Real
  omegaAnchorLower : Real
  omegaAnchorUpper : Real
  shapeValueLower : Real
  shapeValueUpper : Real
  shapeDerivLower : Real
  shapeDerivUpper : Real
  shapeSqDerivLower : Real
  shapeSqDerivUpper : Real
  shapeSqAnchorLower : Real
  shapeSqAnchorUpper : Real
  hAnchorIn : anchor ∈ Set.Ioc a b
  hEtaLeft : anchor - a <= etaRadius
  hEtaRight : b - anchor <= etaRadius
  hOmega :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper
  hOmegaContain :
    intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
        intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
          omegaCenter <=
      omegaRadius
  hShapeValueLower :
    ∀ eta ∈ Set.Icc a b,
      shapeValueLower <=
        centeredBSplineImagTransformRealClosedForm k ell eta
  hShapeValueUpper :
    ∀ eta ∈ Set.Icc a b,
      centeredBSplineImagTransformRealClosedForm k ell eta <=
        shapeValueUpper
  hShapeDerivLower :
    ∀ eta ∈ Set.Icc a b,
      shapeDerivLower <=
        deriv
          (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
          eta
  hShapeDerivUpper :
    ∀ eta ∈ Set.Icc a b,
      deriv
          (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
          eta <= shapeDerivUpper
  hShapeSqDerivLowerLL :
    shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivLower
  hShapeSqDerivLowerLU :
    shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivUpper
  hShapeSqDerivLowerUL :
    shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivLower
  hShapeSqDerivLowerUU :
    shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivUpper
  hShapeSqDerivUpperLL :
    2 * shapeValueLower * shapeDerivLower <= shapeSqDerivUpper
  hShapeSqDerivUpperLU :
    2 * shapeValueLower * shapeDerivUpper <= shapeSqDerivUpper
  hShapeSqDerivUpperUL :
    2 * shapeValueUpper * shapeDerivLower <= shapeSqDerivUpper
  hShapeSqDerivUpperUU :
    2 * shapeValueUpper * shapeDerivUpper <= shapeSqDerivUpper
  hShapeSqAnchorLower :
    shapeSqAnchorLower <=
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2
  hShapeSqAnchorUpper :
    (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
      shapeSqAnchorUpper
  hShapeSqContain :
    intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
        intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
          shapeSqCenter <=
      shapeSqRadius
  hOmegaLower : omegaLower <= omegaCenter - omegaRadius
  hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper
  hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius
  hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper

theorem LocalRawOmegaComponentClosedFormEndpointIntervalCert.toComponentIntervalCert
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius : Real}
    (cert :
      LocalRawOmegaComponentClosedFormEndpointIntervalCert k ell a b anchor
        etaRadius omegaLower omegaUpper shapeSqLower shapeSqUpper omegaCenter
        omegaRadius shapeSqCenter shapeSqRadius) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  exact
    LocalRawOmegaComponentIntervalCert.of_omega_endpoint_cert_shapeSq_closedForm_auto_differentiability
      cert.hAnchorIn cert.hEtaLeft cert.hEtaRight
      cert.hOmega.toStep22OmegaEndpointIntervalCert cert.hOmegaContain
      cert.hShapeValueLower cert.hShapeValueUpper cert.hShapeDerivLower
      cert.hShapeDerivUpper cert.hShapeSqDerivLowerLL
      cert.hShapeSqDerivLowerLU cert.hShapeSqDerivLowerUL
      cert.hShapeSqDerivLowerUU cert.hShapeSqDerivUpperLL
      cert.hShapeSqDerivUpperLU cert.hShapeSqDerivUpperUL
      cert.hShapeSqDerivUpperUU cert.hShapeSqAnchorLower
      cert.hShapeSqAnchorUpper cert.hShapeSqContain cert.hOmegaLower
      cert.hOmegaUpper cert.hShapeSqLower cert.hShapeSqUpper

/-- Generated payload target for the direct shape-square endpoint route.

The Omega side is packed through the proof-bearing closed-form endpoint
certificate, while the shape-square side keeps the direct derivative and anchor
facts for `(centeredBSplineImagTransformRealClosedForm k ell eta)^2`.  This is
the v12 receiver shape: it avoids the rejected `E`/`E'` corner-lift route, but
still lets Lean reuse the checked Omega derivative identity. -/
structure LocalRawOmegaComponentDirectEndpointIntervalCert
    (k : Nat) (ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius : Real) where
  omegaDerivLower : Real
  omegaDerivUpper : Real
  omegaAnchorLower : Real
  omegaAnchorUpper : Real
  shapeSqDerivLower : Real
  shapeSqDerivUpper : Real
  shapeSqAnchorLower : Real
  shapeSqAnchorUpper : Real
  hAnchorIn : anchor ∈ Set.Ioc a b
  hEtaLeft : anchor - a <= etaRadius
  hEtaRight : b - anchor <= etaRadius
  hOmega :
    Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
      omegaDerivUpper omegaAnchorLower omegaAnchorUpper
  hOmegaContain :
    intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
        intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
          omegaCenter <=
      omegaRadius
  hShapeSqDerivLower :
    ∀ eta ∈ Set.Icc a b,
      shapeSqDerivLower <=
        deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta
  hShapeSqDerivUpper :
    ∀ eta ∈ Set.Icc a b,
      deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta <= shapeSqDerivUpper
  hShapeSqAnchorLower :
    shapeSqAnchorLower <=
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2
  hShapeSqAnchorUpper :
    (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
      shapeSqAnchorUpper
  hShapeSqContain :
    intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
        intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
          shapeSqCenter <=
      shapeSqRadius
  hOmegaLower : omegaLower <= omegaCenter - omegaRadius
  hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper
  hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius
  hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper

theorem LocalRawOmegaComponentDirectEndpointIntervalCert.toComponentIntervalCert
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius : Real}
    (cert :
      LocalRawOmegaComponentDirectEndpointIntervalCert k ell a b anchor
        etaRadius omegaLower omegaUpper shapeSqLower shapeSqUpper omegaCenter
        omegaRadius shapeSqCenter shapeSqRadius) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  have hOmega := cert.hOmega.toStep22OmegaEndpointIntervalCert
  exact
    LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_auto_differentiability
      cert.hAnchorIn cert.hEtaLeft cert.hEtaRight hOmega.hDerivLower
      hOmega.hDerivUpper hOmega.hAnchorLower hOmega.hAnchorUpper
      cert.hOmegaContain cert.hShapeSqDerivLower cert.hShapeSqDerivUpper
      cert.hShapeSqAnchorLower cert.hShapeSqAnchorUpper
      cert.hShapeSqContain cert.hOmegaLower cert.hOmegaUpper
      cert.hShapeSqLower cert.hShapeSqUpper

/-- Proof-bearing endpoint package for the direct shape-square side.

Generated endpoint rows should instantiate this separately from the Omega
closed-form package.  The row constructor below then combines both packages
with the purely rational containment comparisons. -/
structure ShapeSqEndpointBoundsCert
    (k : Nat) (ell a b anchor shapeSqDerivLower shapeSqDerivUpper
      shapeSqAnchorLower shapeSqAnchorUpper : Real) : Prop where
  hDerivLower :
    ∀ eta ∈ Set.Icc a b,
      shapeSqDerivLower <=
        deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta
  hDerivUpper :
    ∀ eta ∈ Set.Icc a b,
      deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta <= shapeSqDerivUpper
  hAnchorLower :
    shapeSqAnchorLower <=
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2
  hAnchorUpper :
    (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
      shapeSqAnchorUpper

/-- Build the shape-square endpoint package from closed-form `E` and `E'`
intervals plus the product-corner comparisons for `2 * E * E'`.

This is the proof-safe shape target for generated rows: the generator proves
ordinary endpoint enclosures for `centeredBSplineImagTransformRealClosedForm`
and its derivative, while Lean supplies the derivative-of-square bridge. -/
theorem ShapeSqEndpointBoundsCert.of_closedForm_value_deriv_intervals
    {k : Nat} {ell a b anchor shapeValueLower shapeValueUpper
      shapeDerivLower shapeDerivUpper shapeSqDerivLower shapeSqDerivUpper
      shapeSqAnchorLower shapeSqAnchorUpper : Real}
    (hShapeValueLower :
      ∀ eta ∈ Set.Icc a b,
        shapeValueLower <=
          centeredBSplineImagTransformRealClosedForm k ell eta)
    (hShapeValueUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedForm k ell eta <=
          shapeValueUpper)
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc a b,
        shapeDerivLower <=
          deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta <= shapeDerivUpper)
    (hShapeSqDerivLowerLL :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivLower)
    (hShapeSqDerivLowerLU :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivUpper)
    (hShapeSqDerivLowerUL :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivLower)
    (hShapeSqDerivLowerUU :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivUpper)
    (hShapeSqDerivUpperLL :
      2 * shapeValueLower * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperLU :
      2 * shapeValueLower * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUL :
      2 * shapeValueUpper * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUU :
      2 * shapeValueUpper * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqAnchorLower :
      shapeSqAnchorLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqAnchorUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqAnchorUpper) :
    ShapeSqEndpointBoundsCert k ell a b anchor shapeSqDerivLower
      shapeSqDerivUpper shapeSqAnchorLower shapeSqAnchorUpper := by
  have hShapeSqDeriv :=
    shapeSqDeriv_interval_bounds_on_Icc_of_closedForm_value_deriv_intervals
      hShapeValueLower hShapeValueUpper hShapeDerivLower hShapeDerivUpper
      hShapeSqDerivLowerLL hShapeSqDerivLowerLU hShapeSqDerivLowerUL
      hShapeSqDerivLowerUU hShapeSqDerivUpperLL hShapeSqDerivUpperLU
      hShapeSqDerivUpperUL hShapeSqDerivUpperUU
  exact
    { hDerivLower := hShapeSqDeriv.1
      hDerivUpper := hShapeSqDeriv.2
      hAnchorLower := hShapeSqAnchorLower
      hAnchorUpper := hShapeSqAnchorUpper }

/-- Build the shape-square endpoint package from closed-form `E` intervals and
checked closed-form `E'` intervals.

This is the v17 generated-row target: endpoint payloads may prove derivative
bounds for `centeredBSplineImagTransformRealClosedFormDerivClosedForm`, while
Lean rewrites those bounds to the actual derivative of `E` before applying the
existing shape-square receiver. -/
theorem ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals
    {k : Nat} {ell a b anchor shapeValueLower shapeValueUpper
      shapeDerivLower shapeDerivUpper shapeSqDerivLower shapeSqDerivUpper
      shapeSqAnchorLower shapeSqAnchorUpper : Real}
    (hShapeValueLower :
      ∀ eta ∈ Set.Icc a b,
        shapeValueLower <=
          centeredBSplineImagTransformRealClosedForm k ell eta)
    (hShapeValueUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedForm k ell eta <=
          shapeValueUpper)
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc a b,
        shapeDerivLower <=
          centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta <=
          shapeDerivUpper)
    (hShapeSqDerivLowerLL :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivLower)
    (hShapeSqDerivLowerLU :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivUpper)
    (hShapeSqDerivLowerUL :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivLower)
    (hShapeSqDerivLowerUU :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivUpper)
    (hShapeSqDerivUpperLL :
      2 * shapeValueLower * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperLU :
      2 * shapeValueLower * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUL :
      2 * shapeValueUpper * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUU :
      2 * shapeValueUpper * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqAnchorLower :
      shapeSqAnchorLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqAnchorUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqAnchorUpper) :
    ShapeSqEndpointBoundsCert k ell a b anchor shapeSqDerivLower
      shapeSqDerivUpper shapeSqAnchorLower shapeSqAnchorUpper := by
  have hDerivLower :
      ∀ eta ∈ Set.Icc a b,
        shapeDerivLower <=
          deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta := by
    intro eta heta
    rw [centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm]
    exact hShapeDerivLower eta heta
  have hDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        deriv
            (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t)
            eta <= shapeDerivUpper := by
    intro eta heta
    rw [centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm]
    exact hShapeDerivUpper eta heta
  exact
    ShapeSqEndpointBoundsCert.of_closedForm_value_deriv_intervals
      hShapeValueLower hShapeValueUpper hDerivLower hDerivUpper
      hShapeSqDerivLowerLL hShapeSqDerivLowerLU hShapeSqDerivLowerUL
      hShapeSqDerivLowerUU hShapeSqDerivUpperLL hShapeSqDerivUpperLU
      hShapeSqDerivUpperUL hShapeSqDerivUpperUU hShapeSqAnchorLower
      hShapeSqAnchorUpper

/-- Build the shape-square endpoint package from closed-form `E` intervals,
checked closed-form `E'` intervals, and rational corner comparisons for both
`2 * E * E'` and the anchor square `E(anchor)^2`.

This removes the need for generated rows to prove separate analytic endpoint
facts for the shape-square anchor value: once `anchor ∈ [a,b]`, the existing
`E` interval at the anchor plus four square corners gives the anchor square
enclosure. -/
theorem ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals_anchorValueCorners
    {k : Nat} {ell a b anchor shapeValueLower shapeValueUpper
      shapeDerivLower shapeDerivUpper shapeSqDerivLower shapeSqDerivUpper
      shapeSqAnchorLower shapeSqAnchorUpper : Real}
    (hAnchorIn : anchor ∈ Set.Icc a b)
    (hShapeValueLower :
      ∀ eta ∈ Set.Icc a b,
        shapeValueLower <=
          centeredBSplineImagTransformRealClosedForm k ell eta)
    (hShapeValueUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedForm k ell eta <=
          shapeValueUpper)
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc a b,
        shapeDerivLower <=
          centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc a b,
        centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta <=
          shapeDerivUpper)
    (hShapeSqDerivLowerLL :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivLower)
    (hShapeSqDerivLowerLU :
      shapeSqDerivLower <= 2 * shapeValueLower * shapeDerivUpper)
    (hShapeSqDerivLowerUL :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivLower)
    (hShapeSqDerivLowerUU :
      shapeSqDerivLower <= 2 * shapeValueUpper * shapeDerivUpper)
    (hShapeSqDerivUpperLL :
      2 * shapeValueLower * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperLU :
      2 * shapeValueLower * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUL :
      2 * shapeValueUpper * shapeDerivLower <= shapeSqDerivUpper)
    (hShapeSqDerivUpperUU :
      2 * shapeValueUpper * shapeDerivUpper <= shapeSqDerivUpper)
    (hShapeSqAnchorLowerLL :
      shapeSqAnchorLower <= shapeValueLower * shapeValueLower)
    (hShapeSqAnchorLowerLU :
      shapeSqAnchorLower <= shapeValueLower * shapeValueUpper)
    (hShapeSqAnchorLowerUL :
      shapeSqAnchorLower <= shapeValueUpper * shapeValueLower)
    (hShapeSqAnchorLowerUU :
      shapeSqAnchorLower <= shapeValueUpper * shapeValueUpper)
    (hShapeSqAnchorUpperLL :
      shapeValueLower * shapeValueLower <= shapeSqAnchorUpper)
    (hShapeSqAnchorUpperLU :
      shapeValueLower * shapeValueUpper <= shapeSqAnchorUpper)
    (hShapeSqAnchorUpperUL :
      shapeValueUpper * shapeValueLower <= shapeSqAnchorUpper)
    (hShapeSqAnchorUpperUU :
      shapeValueUpper * shapeValueUpper <= shapeSqAnchorUpper) :
    ShapeSqEndpointBoundsCert k ell a b anchor shapeSqDerivLower
      shapeSqDerivUpper shapeSqAnchorLower shapeSqAnchorUpper := by
  have hAnchorValueLower :
      shapeValueLower <=
        centeredBSplineImagTransformRealClosedForm k ell anchor :=
    hShapeValueLower anchor hAnchorIn
  have hAnchorValueUpper :
      centeredBSplineImagTransformRealClosedForm k ell anchor <=
        shapeValueUpper :=
    hShapeValueUpper anchor hAnchorIn
  have hAnchorSq :=
    mul_interval_bounds_of_four_corners
      hAnchorValueLower hAnchorValueUpper hAnchorValueLower hAnchorValueUpper
      hShapeSqAnchorLowerLL hShapeSqAnchorLowerLU hShapeSqAnchorLowerUL
      hShapeSqAnchorLowerUU hShapeSqAnchorUpperLL hShapeSqAnchorUpperLU
      hShapeSqAnchorUpperUL hShapeSqAnchorUpperUU
  exact
    ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals
      hShapeValueLower hShapeValueUpper hShapeDerivLower hShapeDerivUpper
      hShapeSqDerivLowerLL hShapeSqDerivLowerLU hShapeSqDerivLowerUL
      hShapeSqDerivLowerUU hShapeSqDerivUpperLL hShapeSqDerivUpperLU
      hShapeSqDerivUpperUL hShapeSqDerivUpperUU
      (by simpa [pow_two] using hAnchorSq.1)
      (by simpa [pow_two] using hAnchorSq.2)

/-- Build the direct endpoint row cert from independent Omega and shape-square
endpoint packages.

This is the next stable generated theorem surface: after proving
`rawOmegaEndpointClosedFormBounds_generated` and
`rawShapeSqEndpointBounds_generated`, the remaining row constructor is just
the endpoint-radius arithmetic. -/
def LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius
      omegaDerivLower omegaDerivUpper omegaAnchorLower omegaAnchorUpper
      shapeSqDerivLower shapeSqDerivUpper shapeSqAnchorLower
      shapeSqAnchorUpper : Real}
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hEtaLeft : anchor - a <= etaRadius)
    (hEtaRight : b - anchor <= etaRadius)
    (hOmega :
      Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
        omegaDerivUpper omegaAnchorLower omegaAnchorUpper)
    (hShape :
      ShapeSqEndpointBoundsCert k ell a b anchor shapeSqDerivLower
        shapeSqDerivUpper shapeSqAnchorLower shapeSqAnchorUpper)
    (hOmegaContain :
      intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
          intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
            omegaCenter <=
        omegaRadius)
    (hShapeSqContain :
      intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
          intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
            shapeSqCenter <=
        shapeSqRadius)
    (hOmegaLower : omegaLower <= omegaCenter - omegaRadius)
    (hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper)
    (hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius)
    (hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper) :
    LocalRawOmegaComponentDirectEndpointIntervalCert k ell a b anchor
      etaRadius omegaLower omegaUpper shapeSqLower shapeSqUpper omegaCenter
      omegaRadius shapeSqCenter shapeSqRadius :=
  { omegaDerivLower := omegaDerivLower
    omegaDerivUpper := omegaDerivUpper
    omegaAnchorLower := omegaAnchorLower
    omegaAnchorUpper := omegaAnchorUpper
    shapeSqDerivLower := shapeSqDerivLower
    shapeSqDerivUpper := shapeSqDerivUpper
    shapeSqAnchorLower := shapeSqAnchorLower
    shapeSqAnchorUpper := shapeSqAnchorUpper
    hAnchorIn := hAnchorIn
    hEtaLeft := hEtaLeft
    hEtaRight := hEtaRight
    hOmega := hOmega
    hOmegaContain := hOmegaContain
    hShapeSqDerivLower := hShape.hDerivLower
    hShapeSqDerivUpper := hShape.hDerivUpper
    hShapeSqAnchorLower := hShape.hAnchorLower
    hShapeSqAnchorUpper := hShape.hAnchorUpper
    hShapeSqContain := hShapeSqContain
    hOmegaLower := hOmegaLower
    hOmegaUpper := hOmegaUpper
    hShapeSqLower := hShapeSqLower
    hShapeSqUpper := hShapeSqUpper }

/-- Purely rational row data for the direct Omega/shape endpoint constructor.

The analytic endpoint packages are supplied separately; this structure keeps
the generator-facing arithmetic comparisons stable and proof-safe. -/
structure LocalRawOmegaComponentDirectEndpointRationalCert
    (a b anchor etaRadius omegaCenter omegaRadius shapeSqCenter shapeSqRadius
      omegaDerivLower omegaDerivUpper omegaAnchorLower omegaAnchorUpper
      shapeSqDerivLower shapeSqDerivUpper shapeSqAnchorLower shapeSqAnchorUpper
      omegaLower omegaUpper shapeSqLower shapeSqUpper : Real) : Prop where
  hAnchorIn : anchor ∈ Set.Ioc a b
  hEtaLeft : anchor - a <= etaRadius
  hEtaRight : b - anchor <= etaRadius
  hOmegaContain :
    intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
        intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
          omegaCenter <=
      omegaRadius
  hShapeSqContain :
    intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
        intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
          shapeSqCenter <=
      shapeSqRadius
  hOmegaLower : omegaLower <= omegaCenter - omegaRadius
  hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper
  hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius
  hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper

/-- Build the direct endpoint row certificate from two analytic endpoint
packages plus the purely rational row cert. -/
def LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds_rational
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius
      omegaDerivLower omegaDerivUpper omegaAnchorLower omegaAnchorUpper
      shapeSqDerivLower shapeSqDerivUpper shapeSqAnchorLower
      shapeSqAnchorUpper : Real}
    (hOmega :
      Step22OmegaClosedFormEndpointBoundsCert a b anchor omegaDerivLower
        omegaDerivUpper omegaAnchorLower omegaAnchorUpper)
    (hShape :
      ShapeSqEndpointBoundsCert k ell a b anchor shapeSqDerivLower
        shapeSqDerivUpper shapeSqAnchorLower shapeSqAnchorUpper)
    (hRat :
      LocalRawOmegaComponentDirectEndpointRationalCert a b anchor etaRadius
        omegaCenter omegaRadius shapeSqCenter shapeSqRadius omegaDerivLower
        omegaDerivUpper omegaAnchorLower omegaAnchorUpper shapeSqDerivLower
        shapeSqDerivUpper shapeSqAnchorLower shapeSqAnchorUpper omegaLower
        omegaUpper shapeSqLower shapeSqUpper) :
    LocalRawOmegaComponentDirectEndpointIntervalCert k ell a b anchor
      etaRadius omegaLower omegaUpper shapeSqLower shapeSqUpper omegaCenter
      omegaRadius shapeSqCenter shapeSqRadius :=
  LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds
    hRat.hAnchorIn hRat.hEtaLeft hRat.hEtaRight hOmega hShape
    hRat.hOmegaContain hRat.hShapeSqContain hRat.hOmegaLower
    hRat.hOmegaUpper hRat.hShapeSqLower hRat.hShapeSqUpper

/-- Generated payload target for one local component endpoint interval cert.

This packages the eight analytic endpoint facts plus the rational containment
checks into one row-level object.  The endpoint facts remain real hypotheses;
the structure only gives the generator a stable Lean landing surface. -/
structure LocalRawOmegaComponentEndpointIntervalCert
    (k : Nat) (ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius : Real) where
  omegaDerivLower : Real
  omegaDerivUpper : Real
  omegaAnchorLower : Real
  omegaAnchorUpper : Real
  shapeSqDerivLower : Real
  shapeSqDerivUpper : Real
  shapeSqAnchorLower : Real
  shapeSqAnchorUpper : Real
  hAnchorIn : anchor ∈ Set.Ioc a b
  hEtaLeft : anchor - a <= etaRadius
  hEtaRight : b - anchor <= etaRadius
  hOmegaDerivLower :
    ∀ eta ∈ Set.Icc a b,
      omegaDerivLower <=
        deriv
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta
  hOmegaDerivUpper :
    ∀ eta ∈ Set.Icc a b,
      deriv
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta <= omegaDerivUpper
  hOmegaAnchorLower :
    omegaAnchorLower <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
        anchor
  hOmegaAnchorUpper :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
        anchor <= omegaAnchorUpper
  hOmegaContain :
    intervalAutoAbsBound omegaDerivLower omegaDerivUpper * etaRadius +
        intervalAutoCenterError omegaAnchorLower omegaAnchorUpper
          omegaCenter <=
      omegaRadius
  hShapeSqDerivLower :
    ∀ eta ∈ Set.Icc a b,
      shapeSqDerivLower <=
        deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta
  hShapeSqDerivUpper :
    ∀ eta ∈ Set.Icc a b,
      deriv
          (fun t : Real =>
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
          eta <= shapeSqDerivUpper
  hShapeSqAnchorLower :
    shapeSqAnchorLower <=
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2
  hShapeSqAnchorUpper :
    (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
      shapeSqAnchorUpper
  hShapeSqContain :
    intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * etaRadius +
        intervalAutoCenterError shapeSqAnchorLower shapeSqAnchorUpper
          shapeSqCenter <=
      shapeSqRadius
  hOmegaLower : omegaLower <= omegaCenter - omegaRadius
  hOmegaUpper : omegaCenter + omegaRadius <= omegaUpper
  hShapeSqLower : shapeSqLower <= shapeSqCenter - shapeSqRadius
  hShapeSqUpper : shapeSqCenter + shapeSqRadius <= shapeSqUpper

theorem LocalRawOmegaComponentEndpointIntervalCert.toComponentIntervalCert
    {k : Nat} {ell a b anchor etaRadius omegaLower omegaUpper shapeSqLower
      shapeSqUpper omegaCenter omegaRadius shapeSqCenter shapeSqRadius : Real}
    (cert :
      LocalRawOmegaComponentEndpointIntervalCert k ell a b anchor etaRadius
        omegaLower omegaUpper shapeSqLower shapeSqUpper omegaCenter omegaRadius
        shapeSqCenter shapeSqRadius) :
    LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
      shapeSqLower shapeSqUpper := by
  exact
    LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_auto_differentiability
      cert.hAnchorIn cert.hEtaLeft cert.hEtaRight cert.hOmegaDerivLower
      cert.hOmegaDerivUpper cert.hOmegaAnchorLower cert.hOmegaAnchorUpper
      cert.hOmegaContain cert.hShapeSqDerivLower cert.hShapeSqDerivUpper
      cert.hShapeSqAnchorLower cert.hShapeSqAnchorUpper cert.hShapeSqContain
      cert.hOmegaLower cert.hOmegaUpper cert.hShapeSqLower cert.hShapeSqUpper

/-- Zero-distance local receiver fed by a compact component certificate.

For the active `row = 0` refined subchunk lane, this is the preferred emitter
surface: generated arithmetic still proves the scale, corner, and coefficient
comparisons directly, while the analytic component obligation is a single
local cert per row. -/
theorem raw_center_coeff_abs_of_local_component_cert_scale_interval_corner_bounds_at_zero_distance
    {k : Nat} {ell L U lower upper a b scaleLower scaleUpper
      omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
      rawLower rawUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell 0 L U lower upper)
    {anchor : Real}
    (component :
      LocalRawOmegaComponentIntervalCert k ell a b omegaLower omegaUpper
        shapeSqLower shapeSqUpper)
    (hAnchorIn : anchor ∈ Set.Ioc a b)
    (hCosLowerOne : cosLower <= 1)
    (hCosUpperOne : (1 : Real) <= cosUpper)
    (hScaleLower : scaleLower <= ell / Real.pi)
    (hScaleUpper : ell / Real.pi <= scaleUpper)
    (hLowerLLLL :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosLower)
    (hLowerLLLU :
      rawLower <= scaleLower * omegaLower * shapeSqLower * cosUpper)
    (hLowerLLUL :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosLower)
    (hLowerLLUU :
      rawLower <= scaleLower * omegaLower * shapeSqUpper * cosUpper)
    (hLowerLULL :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosLower)
    (hLowerLULU :
      rawLower <= scaleLower * omegaUpper * shapeSqLower * cosUpper)
    (hLowerLUUL :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosLower)
    (hLowerLUUU :
      rawLower <= scaleLower * omegaUpper * shapeSqUpper * cosUpper)
    (hLowerULLL :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosLower)
    (hLowerULLU :
      rawLower <= scaleUpper * omegaLower * shapeSqLower * cosUpper)
    (hLowerULUL :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosLower)
    (hLowerULUU :
      rawLower <= scaleUpper * omegaLower * shapeSqUpper * cosUpper)
    (hLowerUULL :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosLower)
    (hLowerUULU :
      rawLower <= scaleUpper * omegaUpper * shapeSqLower * cosUpper)
    (hLowerUUUL :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosLower)
    (hLowerUUUU :
      rawLower <= scaleUpper * omegaUpper * shapeSqUpper * cosUpper)
    (hUpperLLLL :
      scaleLower * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperLLLU :
      scaleLower * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLLUL :
      scaleLower * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLLUU :
      scaleLower * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperLULL :
      scaleLower * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperLULU :
      scaleLower * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperLUUL :
      scaleLower * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperLUUU :
      scaleLower * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperULLL :
      scaleUpper * omegaLower * shapeSqLower * cosLower <= rawUpper)
    (hUpperULLU :
      scaleUpper * omegaLower * shapeSqLower * cosUpper <= rawUpper)
    (hUpperULUL :
      scaleUpper * omegaLower * shapeSqUpper * cosLower <= rawUpper)
    (hUpperULUU :
      scaleUpper * omegaLower * shapeSqUpper * cosUpper <= rawUpper)
    (hUpperUULL :
      scaleUpper * omegaUpper * shapeSqLower * cosLower <= rawUpper)
    (hUpperUULU :
      scaleUpper * omegaUpper * shapeSqLower * cosUpper <= rawUpper)
    (hUpperUUUL :
      scaleUpper * omegaUpper * shapeSqUpper * cosLower <= rawUpper)
    (hUpperUUUU :
      scaleUpper * omegaUpper * shapeSqUpper * cosUpper <= rawUpper)
    (hCoeffLower : -sampleRadius <= rawLower - (cert.coeff 0 : Real))
    (hCoeffUpper : rawUpper - (cert.coeff 0 : Real) <= sampleRadius) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell 0 anchor - (cert.coeff 0 : Real)| <= sampleRadius := by
  exact
    cert.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at_zero_distance
      hAnchorIn component.hOmegaLower component.hOmegaUpper
      component.hShapeSqLower component.hShapeSqUpper hCosLowerOne
      hCosUpperOne hScaleLower hScaleUpper hLowerLLLL hLowerLLLU
      hLowerLLUL hLowerLLUU hLowerLULL hLowerLULU hLowerLUUL hLowerLUUU
      hLowerULLL hLowerULLU hLowerULUL hLowerULUU hLowerUULL hLowerUULU
      hLowerUUUL hLowerUUUU hUpperLLLL hUpperLLLU hUpperLLUL hUpperLLUU
      hUpperLULL hUpperLULU hUpperLUUL hUpperLUUU hUpperULLL hUpperULLU
      hUpperULUL hUpperULUU hUpperUULL hUpperUULU hUpperUUUL hUpperUUUU
      hCoeffLower hCoeffUpper

/-- Pointwise raw-Omega integrand bounds from nonnegative component boxes and
an absolute cosine enclosure at one anchor.

This is the anchor-only analogue of
`RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds`.  It avoids
asking generated code for a general product-corner function when the active
route-B field only needs the raw integrand at the Taylor center. -/
theorem rawOmegaAIntegrand_value_bounds_at_of_nonneg_abs_cos_component_bounds
    {k : Nat} {ell x anchor omegaLower omegaUpper shapeSqLower shapeSqUpper
      cosLower cosUpper cosAbs rawLower rawUpper : Real}
    (hOmegaLower :
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaUpper)
    (hShapeSqLower :
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hCosLower : cosLower <= Real.cos (anchor * x))
    (hCosUpper : Real.cos (anchor * x) <= cosUpper)
    (hScaleNonneg : 0 <= ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower :
      rawLower <= -((ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper :
      (ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs <= rawUpper) :
    rawLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor <= rawUpper := by
  have hprod :=
    product_bounds_of_nonneg_boxes_and_abs_cos
      (scale := ell / Real.pi)
      (omegaLower := omegaLower) (omegaUpper := omegaUpper)
      (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
      (cosLower := cosLower) (cosUpper := cosUpper) (cosAbs := cosAbs)
      (rawLower := rawLower) (rawUpper := rawUpper)
      hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
      hCosUpperAbs hRawLower hRawUpper
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
        anchor)
      ((centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
      (Real.cos (anchor * x))
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
  simpa
    [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand]
    using hprod

/-- Pointwise raw-Omega integrand bounds from a signed Omega majorant.

This is the route-B anchor-safe replacement for the nonnegative-Omega abs-cos
receiver on finite chunks.  It only requires
`Omega(anchor) ∈ [-omegaMajorant, omegaMajorant]`, the structural
`shapeSq >= 0`, and the universal cosine box `[-1, 1]`. -/
theorem rawOmegaAIntegrand_value_bounds_at_of_scale_abs_box_bounds
    {k : Nat} {ell x anchor scaleUpper omegaMajorant shapeSqUpper
      rawLower rawUpper : Real}
    (hScaleNonneg : 0 <= ell / Real.pi)
    (hScaleUpper : ell / Real.pi <= scaleUpper)
    (hScaleUpperNonneg : 0 <= scaleUpper)
    (hOmegaMajorantNonneg : 0 <= omegaMajorant)
    (hShapeSqUpperNonneg : 0 <= shapeSqUpper)
    (hOmegaLower :
      -omegaMajorant <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaMajorant)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hRawLower :
      rawLower <= -(scaleUpper * omegaMajorant * shapeSqUpper))
    (hRawUpper :
      scaleUpper * omegaMajorant * shapeSqUpper <= rawUpper) :
    rawLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x anchor <= rawUpper := by
  have hprod :=
    product_bounds_of_scale_abs_box
      (scale := ell / Real.pi)
      (scaleUpper := scaleUpper)
      (omegaMajorant := omegaMajorant)
      (shapeSqUpper := shapeSqUpper)
      (omega :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
      (shapeSq := (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
      (cosValue := Real.cos (anchor * x))
      hScaleNonneg hScaleUpper hScaleUpperNonneg hOmegaMajorantNonneg
      hShapeSqUpperNonneg hOmegaLower hOmegaUpper (sq_nonneg _)
      hShapeSqUpper (Real.neg_one_le_cos (anchor * x))
      (Real.cos_le_one (anchor * x))
  constructor
  · have h :
        rawLower <=
          (ell / Real.pi) *
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
              anchor *
            (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 *
            Real.cos (anchor * x) :=
      le_trans hRawLower hprod.1
    simpa
      [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand]
      using h
  · have h :
        (ell / Real.pi) *
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
              anchor *
            (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 *
            Real.cos (anchor * x) <=
          rawUpper :=
      le_trans hprod.2 hRawUpper
    simpa
      [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand]
      using h

/-- Route-B pointwise residual-anchor receiver from raw component bounds and
the Taylor-center polynomial normalization.

For the current pilot the anchor is the Taylor center.  This theorem lets the
generated payload prove component bounds for the raw-Omega integrand at that
single point, prove rational comparisons around `coeff 0`, and let Lean package
the resulting `hAnchorResidual` fact. -/
theorem anchor_residual_abs_of_raw_component_bounds_at_center
    {k : Nat} {ell x L U lower upper omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper rawLower rawUpper polyLower polyUpper
      sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hAnchor : anchor = (cert.center : Real))
    (hOmegaLower :
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaUpper)
    (hShapeSqLower :
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hCosLower : cosLower <= Real.cos (anchor * x))
    (hCosUpper : Real.cos (anchor * x) <= cosUpper)
    (hProductLower :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue)
    (hProductUpper :
      ∀ omega shapeSq cosValue,
        omegaLower <= omega -> omega <= omegaUpper ->
        shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
        cosLower <= cosValue -> cosValue <= cosUpper ->
          (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper)
    (hCoeffLower : polyLower <= (cert.coeff 0 : Real))
    (hCoeffUpper : (cert.coeff 0 : Real) <= polyUpper)
    (hResidualLower : -sampleRadius <= rawLower - polyUpper)
    (hResidualUpper : rawUpper - polyLower <= sampleRadius) :
    |cert.residual anchor| <= sampleRadius := by
  have hRaw :=
    rawOmegaAIntegrand_value_bounds_at_of_component_bounds
      (k := k) (ell := ell) (x := x) (anchor := anchor)
      (omegaLower := omegaLower) (omegaUpper := omegaUpper)
      (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
      (cosLower := cosLower) (cosUpper := cosUpper)
      (rawLower := rawLower) (rawUpper := rawUpper)
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hProductLower hProductUpper
  have hPolyLower : polyLower <= cert.polynomial anchor := by
    rw [hAnchor, cert.polynomial_center]
    exact hCoeffLower
  have hPolyUpper : cert.polynomial anchor <= polyUpper := by
    rw [hAnchor, cert.polynomial_center]
    exact hCoeffUpper
  exact
    cert.anchor_residual_abs_of_raw_poly_value_bounds_at
      hRaw.1 hRaw.2 hPolyLower hPolyUpper hResidualLower hResidualUpper

/-- Route-B residual-anchor receiver from nonnegative raw component boxes and
an absolute cosine enclosure at the Taylor center.

Compared to `anchor_residual_abs_of_raw_component_bounds_at_center`, this
receiver replaces generated product-corner obligations by two scalar
comparisons against `(ell / pi) * omegaUpper * shapeSqUpper * cosAbs`. -/
theorem anchor_residual_abs_of_nonneg_abs_cos_component_bounds_at_center
    {k : Nat} {ell x L U lower upper omegaLower omegaUpper shapeSqLower
      shapeSqUpper cosLower cosUpper cosAbs rawLower rawUpper polyLower
      polyUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hAnchor : anchor = (cert.center : Real))
    (hOmegaLower :
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaUpper)
    (hShapeSqLower :
      shapeSqLower <=
        (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hCosLower : cosLower <= Real.cos (anchor * x))
    (hCosUpper : Real.cos (anchor * x) <= cosUpper)
    (hScaleNonneg : 0 <= ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower :
      rawLower <= -((ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper :
      (ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs <= rawUpper)
    (hCoeffLower : polyLower <= (cert.coeff 0 : Real))
    (hCoeffUpper : (cert.coeff 0 : Real) <= polyUpper)
    (hResidualLower : -sampleRadius <= rawLower - polyUpper)
    (hResidualUpper : rawUpper - polyLower <= sampleRadius) :
    |cert.residual anchor| <= sampleRadius := by
  have hRaw :=
    rawOmegaAIntegrand_value_bounds_at_of_nonneg_abs_cos_component_bounds
      (k := k) (ell := ell) (x := x) (anchor := anchor)
      (omegaLower := omegaLower) (omegaUpper := omegaUpper)
      (shapeSqLower := shapeSqLower) (shapeSqUpper := shapeSqUpper)
      (cosLower := cosLower) (cosUpper := cosUpper) (cosAbs := cosAbs)
      (rawLower := rawLower) (rawUpper := rawUpper)
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
      hCosUpperAbs hRawLower hRawUpper
  have hPolyLower : polyLower <= cert.polynomial anchor := by
    rw [hAnchor, cert.polynomial_center]
    exact hCoeffLower
  have hPolyUpper : cert.polynomial anchor <= polyUpper := by
    rw [hAnchor, cert.polynomial_center]
    exact hCoeffUpper
  exact
    cert.anchor_residual_abs_of_raw_poly_value_bounds_at
      hRaw.1 hRaw.2 hPolyLower hPolyUpper hResidualLower hResidualUpper

/-- Route-B residual-anchor receiver from a signed Omega majorant.

This is the active finite-chunk route.  Unlike
`anchor_residual_abs_of_nonneg_abs_cos_component_bounds_at_center`, it does not
assume `0 <= omegaLower`; the first raw-Omega finite chunk crosses the negative
Omega region. -/
theorem anchor_residual_abs_of_scale_abs_box_component_bounds_at_center
    {k : Nat} {ell x L U lower upper scaleUpper omegaMajorant shapeSqUpper
      rawLower rawUpper polyLower polyUpper sampleRadius : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {anchor : Real}
    (hAnchor : anchor = (cert.center : Real))
    (hScaleNonneg : 0 <= ell / Real.pi)
    (hScaleUpper : ell / Real.pi <= scaleUpper)
    (hScaleUpperNonneg : 0 <= scaleUpper)
    (hOmegaMajorantNonneg : 0 <= omegaMajorant)
    (hShapeSqUpperNonneg : 0 <= shapeSqUpper)
    (hOmegaLower :
      -omegaMajorant <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor)
    (hOmegaUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          anchor <=
        omegaMajorant)
    (hShapeSqUpper :
      (centeredBSplineImagTransformRealClosedForm k ell anchor) ^ 2 <=
        shapeSqUpper)
    (hRawLower :
      rawLower <= -(scaleUpper * omegaMajorant * shapeSqUpper))
    (hRawUpper :
      scaleUpper * omegaMajorant * shapeSqUpper <= rawUpper)
    (hCoeffLower : polyLower <= (cert.coeff 0 : Real))
    (hCoeffUpper : (cert.coeff 0 : Real) <= polyUpper)
    (hResidualLower : -sampleRadius <= rawLower - polyUpper)
    (hResidualUpper : rawUpper - polyLower <= sampleRadius) :
    |cert.residual anchor| <= sampleRadius := by
  have hRaw :=
    rawOmegaAIntegrand_value_bounds_at_of_scale_abs_box_bounds
      (k := k) (ell := ell) (x := x) (anchor := anchor)
      (scaleUpper := scaleUpper) (omegaMajorant := omegaMajorant)
      (shapeSqUpper := shapeSqUpper) (rawLower := rawLower)
      (rawUpper := rawUpper)
      hScaleNonneg hScaleUpper hScaleUpperNonneg hOmegaMajorantNonneg
      hShapeSqUpperNonneg hOmegaLower hOmegaUpper hShapeSqUpper
      hRawLower hRawUpper
  have hPolyLower : polyLower <= cert.polynomial anchor := by
    rw [hAnchor, cert.polynomial_center]
    exact hCoeffLower
  have hPolyUpper : cert.polynomial anchor <= polyUpper := by
    rw [hAnchor, cert.polynomial_center]
    exact hCoeffUpper
  exact
    cert.anchor_residual_abs_of_raw_poly_value_bounds_at
      hRaw.1 hRaw.2 hPolyLower hPolyUpper hResidualLower hResidualUpper

/-- Per-term enclosures for the Taylor polynomial on one chunk.  This lets a
generated payload prove interval bounds for each monomial term and let Lean
sum them into the polynomial value enclosure. -/
structure PolynomialTermBounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (termLower termUpper : Fin (cert.degree + 1) -> Real) : Prop where
  hTermLower :
    ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Ioc L U,
      termLower i <=
        (cert.coeff i : Real) * (eta - (cert.center : Real)) ^ i.1
  hTermUpper :
    ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Ioc L U,
      (cert.coeff i : Real) * (eta - (cert.center : Real)) ^ i.1 <=
        termUpper i

theorem polynomial_value_bounds_of_term_bounds
    {k : Nat} {ell x L U lower upper polyLower polyUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ i : Fin (cert.degree + 1), termLower i)
    (hPolyUpper : (∑ i : Fin (cert.degree + 1), termUpper i) <= polyUpper) :
    (∀ eta ∈ Set.Ioc L U, polyLower <= cert.polynomial eta) ∧
      (∀ eta ∈ Set.Ioc L U, cert.polynomial eta <= polyUpper) := by
  constructor
  · intro eta heta
    have hsum :
        (∑ i : Fin (cert.degree + 1), termLower i) <= cert.polynomial eta := by
      unfold polynomial rawOmegaATaylorPolynomial
      exact Finset.sum_le_sum (by
        intro i hi
        exact hTerms.hTermLower i eta heta)
    exact le_trans hPolyLower hsum
  · intro eta heta
    have hsum :
        cert.polynomial eta <=
          ∑ i : Fin (cert.degree + 1), termUpper i := by
      unfold polynomial rawOmegaATaylorPolynomial
      exact Finset.sum_le_sum (by
        intro i hi
        exact hTerms.hTermUpper i eta heta)
    exact le_trans hsum hPolyUpper

/-- Derivative of the generated Taylor polynomial as a finite sum of the
derivatives of its monomial terms.

This keeps the derivative-cell route local: generated code may bound each
term derivative on a cell, and Lean supplies the sum identity. -/
theorem polynomial_deriv_eq_term_deriv_sum
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (eta : Real) :
    deriv cert.polynomial eta =
      ∑ i : Fin (cert.degree + 1),
        deriv
          (fun t : Real =>
            (cert.coeff i : Real) * (t - (cert.center : Real)) ^ i.1)
          eta := by
  change
    deriv
        (fun eta : Real =>
          Finset.sum (Finset.univ : Finset (Fin (cert.degree + 1))) fun i =>
            (cert.coeff i : Real) * (eta - (cert.center : Real)) ^ i.1)
        eta =
      Finset.sum (Finset.univ : Finset (Fin (cert.degree + 1))) fun i =>
        deriv
          (fun t : Real =>
            (cert.coeff i : Real) * (t - (cert.center : Real)) ^ i.1)
          eta
  rw [deriv_fun_sum]
  intro i hi
  fun_prop

/-- Derivative of one generated Taylor monomial. -/
theorem polynomial_term_deriv_eq
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (i : Fin (cert.degree + 1)) (eta : Real) :
    deriv
        (fun t : Real =>
          (cert.coeff i : Real) * (t - (cert.center : Real)) ^ i.1)
        eta =
      (cert.coeff i : Real) *
        ((i.1 : Real) * (eta - (cert.center : Real)) ^ (i.1 - 1)) := by
  calc
    deriv
        (fun t : Real =>
          (cert.coeff i : Real) * (t - (cert.center : Real)) ^ i.1)
        eta =
        (cert.coeff i : Real) *
          deriv (fun t : Real => (t - (cert.center : Real)) ^ i.1) eta := by
          rw [deriv_const_mul]
          fun_prop
    _ =
        (cert.coeff i : Real) *
          ((i.1 : Real) * (eta - (cert.center : Real)) ^ (i.1 - 1) *
            deriv (fun t : Real => t - (cert.center : Real)) eta) := by
          rw [deriv_fun_pow]
          fun_prop
    _ =
        (cert.coeff i : Real) *
          ((i.1 : Real) * (eta - (cert.center : Real)) ^ (i.1 - 1)) := by
          simp

/-- Per-term derivative enclosures for the Taylor polynomial on one derivative
cell. -/
structure PolynomialDerivativeTermBoundsOnCell
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (cellL cellU : Real)
    (termDerivLower termDerivUpper : Fin (cert.degree + 1) -> Real) : Prop where
  hTermDerivLower :
    ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
      termDerivLower i <=
        deriv
          (fun t : Real =>
            (cert.coeff i : Real) * (t - (cert.center : Real)) ^ i.1)
          eta
  hTermDerivUpper :
    ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
      deriv
          (fun t : Real =>
            (cert.coeff i : Real) * (t - (cert.center : Real)) ^ i.1)
          eta <=
        termDerivUpper i

theorem polynomial_derivative_term_bounds_on_cell_of_expr_bounds
    {k : Nat} {ell x L U lower upper cellL cellU : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {termDerivLower termDerivUpper : Fin (cert.degree + 1) -> Real}
    (hTermDerivLowerExpr :
      ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
        termDerivLower i <=
          (cert.coeff i : Real) *
            ((i.1 : Real) *
              (eta - (cert.center : Real)) ^ (i.1 - 1)))
    (hTermDerivUpperExpr :
      ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
        (cert.coeff i : Real) *
            ((i.1 : Real) *
              (eta - (cert.center : Real)) ^ (i.1 - 1)) <=
          termDerivUpper i) :
    cert.PolynomialDerivativeTermBoundsOnCell cellL cellU
      termDerivLower termDerivUpper where
  hTermDerivLower := by
    intro i eta heta
    rw [cert.polynomial_term_deriv_eq i eta]
    exact hTermDerivLowerExpr i eta heta
  hTermDerivUpper := by
    intro i eta heta
    rw [cert.polynomial_term_deriv_eq i eta]
    exact hTermDerivUpperExpr i eta heta

theorem polynomial_deriv_bounds_on_cell_of_term_deriv_bounds
    {k : Nat} {ell x L U lower upper cellL cellU polyDerivLower
      polyDerivUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {termDerivLower termDerivUpper : Fin (cert.degree + 1) -> Real}
    (hTerms :
      cert.PolynomialDerivativeTermBoundsOnCell cellL cellU
        termDerivLower termDerivUpper)
    (hPolyDerivLower :
      polyDerivLower <= ∑ i : Fin (cert.degree + 1), termDerivLower i)
    (hPolyDerivUpper :
      (∑ i : Fin (cert.degree + 1), termDerivUpper i) <= polyDerivUpper) :
    (∀ eta ∈ Set.Icc cellL cellU,
        polyDerivLower <= deriv cert.polynomial eta) ∧
      (∀ eta ∈ Set.Icc cellL cellU,
        deriv cert.polynomial eta <= polyDerivUpper) := by
  constructor
  · intro eta heta
    rw [cert.polynomial_deriv_eq_term_deriv_sum eta]
    have hsum :
        (∑ i : Fin (cert.degree + 1), termDerivLower i) <=
          ∑ i : Fin (cert.degree + 1),
            deriv
              (fun t : Real =>
                (cert.coeff i : Real) *
                  (t - (cert.center : Real)) ^ i.1)
              eta := by
      exact Finset.sum_le_sum (by
        intro i hi
        exact hTerms.hTermDerivLower i eta heta)
    exact le_trans hPolyDerivLower hsum
  · intro eta heta
    rw [cert.polynomial_deriv_eq_term_deriv_sum eta]
    have hsum :
        (∑ i : Fin (cert.degree + 1),
            deriv
              (fun t : Real =>
                (cert.coeff i : Real) *
                  (t - (cert.center : Real)) ^ i.1)
              eta) <=
          ∑ i : Fin (cert.degree + 1), termDerivUpper i := by
      exact Finset.sum_le_sum (by
        intro i hi
        exact hTerms.hTermDerivUpper i eta heta)
    exact le_trans hsum hPolyDerivUpper

theorem ValueBounds.of_raw_and_polynomial_term_bounds
    {k : Nat} {ell x L U lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRawLower :
      ∀ eta ∈ Set.Ioc L U,
        rawLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta)
    (hRawUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta <=
          rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ i : Fin (cert.degree + 1), termLower i)
    (hPolyUpper : (∑ i : Fin (cert.degree + 1), termUpper i) <= polyUpper) :
    cert.ValueBounds rawLower rawUpper polyLower polyUpper := by
  have hPoly :=
    cert.polynomial_value_bounds_of_term_bounds hTerms hPolyLower hPolyUpper
  exact
    { hRawLower := hRawLower
      hRawUpper := hRawUpper
      hPolyLower := hPoly.1
      hPolyUpper := hPoly.2 }

theorem ValueBounds.of_raw_component_and_polynomial_term_bounds
    {k : Nat} {ell x L U lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRaw :
      RawIntegrandComponentBounds k ell x L U omegaLower omegaUpper
        shapeSqLower shapeSqUpper cosLower cosUpper rawLower rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ i : Fin (cert.degree + 1), termLower i)
    (hPolyUpper : (∑ i : Fin (cert.degree + 1), termUpper i) <= polyUpper) :
    cert.ValueBounds rawLower rawUpper polyLower polyUpper := by
  have hRawBounds := rawOmegaAIntegrand_value_bounds_of_component_bounds hRaw
  exact
    ValueBounds.of_raw_and_polynomial_term_bounds cert hRawBounds.1
      hRawBounds.2 hTerms hPolyLower hPolyUpper

theorem ValueBounds.of_raw_and_polynomial_value_bounds
    {k : Nat} {ell x L U lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hRawLower :
      ∀ eta ∈ Set.Ioc L U,
        rawLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta)
    (hRawUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x eta <=
          rawUpper)
    (hPolyLower :
      ∀ eta ∈ Set.Ioc L U, polyLower <= cert.polynomial eta)
    (hPolyUpper :
      ∀ eta ∈ Set.Ioc L U, cert.polynomial eta <= polyUpper) :
    cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
  { hRawLower := hRawLower
    hRawUpper := hRawUpper
    hPolyLower := hPolyLower
    hPolyUpper := hPolyUpper }

theorem ValueBounds.of_raw_component_and_polynomial_value_bounds
    {k : Nat} {ell x L U lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hRaw :
      RawIntegrandComponentBounds k ell x L U omegaLower omegaUpper
        shapeSqLower shapeSqUpper cosLower cosUpper rawLower rawUpper)
    (hPolyLower :
      ∀ eta ∈ Set.Ioc L U, polyLower <= cert.polynomial eta)
    (hPolyUpper :
      ∀ eta ∈ Set.Ioc L U, cert.polynomial eta <= polyUpper) :
    cert.ValueBounds rawLower rawUpper polyLower polyUpper := by
  have hRawBounds := rawOmegaAIntegrand_value_bounds_of_component_bounds hRaw
  exact
    ValueBounds.of_raw_and_polynomial_value_bounds cert hRawBounds.1
      hRawBounds.2 hPolyLower hPolyUpper

structure ComponentTermBounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  rawLower : Real
  rawUpper : Real
  polyLower : Real
  polyUpper : Real
  omegaLower : Real
  omegaUpper : Real
  shapeSqLower : Real
  shapeSqUpper : Real
  cosLower : Real
  cosUpper : Real
  termLower : Fin (cert.degree + 1) -> Real
  termUpper : Fin (cert.degree + 1) -> Real
  hOmegaLower :
    ∀ eta ∈ Set.Ioc L U,
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta
  hOmegaUpper :
    ∀ eta ∈ Set.Ioc L U,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
        omegaUpper
  hShapeSqLower :
    ∀ eta ∈ Set.Ioc L U,
      shapeSqLower <= (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2
  hShapeSqUpper :
    ∀ eta ∈ Set.Ioc L U,
      (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
        shapeSqUpper
  hCosLower :
    ∀ eta ∈ Set.Ioc L U,
      cosLower <= Real.cos (eta * x)
  hCosUpper :
    ∀ eta ∈ Set.Ioc L U,
      Real.cos (eta * x) <= cosUpper
  hProductLower :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue
  hProductUpper :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper
  hTerms : cert.PolynomialTermBounds termLower termUpper
  hPolyLower : polyLower <= ∑ i : Fin (cert.degree + 1), termLower i
  hPolyUpper : (∑ i : Fin (cert.degree + 1), termUpper i) <= polyUpper

theorem ComponentTermBounds.toRawComponentBounds
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ComponentTermBounds cert) :
    RawIntegrandComponentBounds k ell x L U data.omegaLower data.omegaUpper
      data.shapeSqLower data.shapeSqUpper data.cosLower data.cosUpper
      data.rawLower data.rawUpper :=
  RawIntegrandComponentBounds.of_product_bounds data.hOmegaLower
    data.hOmegaUpper data.hShapeSqLower data.hShapeSqUpper data.hCosLower
    data.hCosUpper data.hProductLower data.hProductUpper

theorem ComponentTermBounds.toValueBounds
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ComponentTermBounds cert) :
    cert.ValueBounds data.rawLower data.rawUpper data.polyLower data.polyUpper := by
  exact
    ValueBounds.of_raw_component_and_polynomial_term_bounds cert
      data.toRawComponentBounds data.hTerms data.hPolyLower data.hPolyUpper

structure ComponentValueBounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  rawLower : Real
  rawUpper : Real
  polyLower : Real
  polyUpper : Real
  omegaLower : Real
  omegaUpper : Real
  shapeSqLower : Real
  shapeSqUpper : Real
  cosLower : Real
  cosUpper : Real
  hOmegaLower :
    ∀ eta ∈ Set.Ioc L U,
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta
  hOmegaUpper :
    ∀ eta ∈ Set.Ioc L U,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
        omegaUpper
  hShapeSqLower :
    ∀ eta ∈ Set.Ioc L U,
      shapeSqLower <= (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2
  hShapeSqUpper :
    ∀ eta ∈ Set.Ioc L U,
      (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
        shapeSqUpper
  hCosLower :
    ∀ eta ∈ Set.Ioc L U,
      cosLower <= Real.cos (eta * x)
  hCosUpper :
    ∀ eta ∈ Set.Ioc L U,
      Real.cos (eta * x) <= cosUpper
  hProductLower :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        rawLower <= (ell / Real.pi) * omega * shapeSq * cosValue
  hProductUpper :
    ∀ omega shapeSq cosValue,
      omegaLower <= omega -> omega <= omegaUpper ->
      shapeSqLower <= shapeSq -> shapeSq <= shapeSqUpper ->
      cosLower <= cosValue -> cosValue <= cosUpper ->
        (ell / Real.pi) * omega * shapeSq * cosValue <= rawUpper
  hPolyLower :
    ∀ eta ∈ Set.Ioc L U, polyLower <= cert.polynomial eta
  hPolyUpper :
    ∀ eta ∈ Set.Ioc L U, cert.polynomial eta <= polyUpper

theorem ComponentValueBounds.toRawComponentBounds
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ComponentValueBounds cert) :
    RawIntegrandComponentBounds k ell x L U data.omegaLower data.omegaUpper
      data.shapeSqLower data.shapeSqUpper data.cosLower data.cosUpper
      data.rawLower data.rawUpper :=
  RawIntegrandComponentBounds.of_product_bounds data.hOmegaLower
    data.hOmegaUpper data.hShapeSqLower data.hShapeSqUpper data.hCosLower
    data.hCosUpper data.hProductLower data.hProductUpper

theorem ComponentValueBounds.toValueBounds
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ComponentValueBounds cert) :
    cert.ValueBounds data.rawLower data.rawUpper data.polyLower data.polyUpper :=
  ValueBounds.of_raw_component_and_polynomial_value_bounds cert
    data.toRawComponentBounds data.hPolyLower data.hPolyUpper

theorem ValueBounds.of_raw_component_abs_cos_and_polynomial_term_bounds
    {k : Nat} {ell x L U lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper cosAbs : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc L U,
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc L U,
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc L U,
        (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc L U,
        cosLower <= Real.cos (eta * x))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc L U,
        Real.cos (eta * x) <= cosUpper)
    (hScaleNonneg : 0 <= ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower : rawLower <= -((ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper : (ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs <= rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ i : Fin (cert.degree + 1), termLower i)
    (hPolyUpper : (∑ i : Fin (cert.degree + 1), termUpper i) <= polyUpper) :
    cert.ValueBounds rawLower rawUpper polyLower polyUpper := by
  have hRaw :
      RawIntegrandComponentBounds k ell x L U omegaLower omegaUpper
        shapeSqLower shapeSqUpper cosLower cosUpper rawLower rawUpper :=
    RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
      hCosUpperAbs hRawLower hRawUpper
  exact
    ValueBounds.of_raw_component_and_polynomial_term_bounds cert hRaw hTerms
      hPolyLower hPolyUpper

structure AbsCosComponentTermBounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  rawLower : Real
  rawUpper : Real
  polyLower : Real
  polyUpper : Real
  omegaLower : Real
  omegaUpper : Real
  shapeSqLower : Real
  shapeSqUpper : Real
  cosLower : Real
  cosUpper : Real
  cosAbs : Real
  termLower : Fin (cert.degree + 1) -> Real
  termUpper : Fin (cert.degree + 1) -> Real
  hOmegaLower :
    ∀ eta ∈ Set.Ioc L U,
      omegaLower <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta
  hOmegaUpper :
    ∀ eta ∈ Set.Ioc L U,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
        omegaUpper
  hShapeSqLower :
    ∀ eta ∈ Set.Ioc L U,
      shapeSqLower <= (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2
  hShapeSqUpper :
    ∀ eta ∈ Set.Ioc L U,
      (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
        shapeSqUpper
  hCosLower :
    ∀ eta ∈ Set.Ioc L U,
      cosLower <= Real.cos (eta * x)
  hCosUpper :
    ∀ eta ∈ Set.Ioc L U,
      Real.cos (eta * x) <= cosUpper
  hScaleNonneg : 0 <= ell / Real.pi
  hOmegaLowerNonneg : 0 <= omegaLower
  hShapeSqLowerNonneg : 0 <= shapeSqLower
  hCosLowerAbs : -cosAbs <= cosLower
  hCosUpperAbs : cosUpper <= cosAbs
  hRawLower :
    rawLower <= -((ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs)
  hRawUpper :
    (ell / Real.pi) * omegaUpper * shapeSqUpper * cosAbs <= rawUpper
  hTerms : cert.PolynomialTermBounds termLower termUpper
  hPolyLower : polyLower <= ∑ i : Fin (cert.degree + 1), termLower i
  hPolyUpper : (∑ i : Fin (cert.degree + 1), termUpper i) <= polyUpper

theorem AbsCosComponentTermBounds.toValueBounds
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : AbsCosComponentTermBounds cert) :
    cert.ValueBounds data.rawLower data.rawUpper data.polyLower data.polyUpper := by
  exact
    ValueBounds.of_raw_component_abs_cos_and_polynomial_term_bounds
      cert data.hOmegaLower data.hOmegaUpper data.hShapeSqLower
      data.hShapeSqUpper data.hCosLower data.hCosUpper data.hScaleNonneg
      data.hOmegaLowerNonneg data.hShapeSqLowerNonneg data.hCosLowerAbs
      data.hCosUpperAbs data.hRawLower data.hRawUpper data.hTerms
      data.hPolyLower data.hPolyUpper

structure AbsCosChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  bounds : AbsCosComponentTermBounds cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hDiffLower :
    -(cert.remainder : Real) <= bounds.rawLower - bounds.polyUpper
  hDiffUpper :
    bounds.rawUpper - bounds.polyLower <= (cert.remainder : Real)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

structure ComponentChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  bounds : ComponentTermBounds cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hDiffLower :
    -(cert.remainder : Real) <= bounds.rawLower - bounds.polyUpper
  hDiffUpper :
    bounds.rawUpper - bounds.polyLower <= (cert.remainder : Real)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

structure ComponentValueChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  bounds : ComponentValueBounds cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hDiffLower :
    -(cert.remainder : Real) <= bounds.rawLower - bounds.polyUpper
  hDiffUpper :
    bounds.rawUpper - bounds.polyLower <= (cert.remainder : Real)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Residual-anchor data for one Taylor/model chunk.  The generated payload
uses this when it proves the residual only at finitely many anchors plus a
separate local variation bound. -/
structure ResidualAnchorEnvelopeData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  hSlopeNonneg : 0 <= slope
  hCover :
    ∀ eta ∈ Set.Ioc L U,
      ∃ anchor ∈ Set.Ioc L U,
        |eta - anchor| <= mesh ∧
          |cert.residual anchor| <= sampleRadius
  hResidualVariation :
    ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
      |cert.residual eta - cert.residual anchor| <=
        slope * |eta - anchor|
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

/-- Finite-cover residual-anchor data for one Taylor/model chunk.

This is a generator-oriented refinement of `ResidualAnchorEnvelopeData`: instead
of emitting the existential `hCover` directly, generated code can give a finite
list of anchor cells, prove the cells cover `(L,U]`, prove each point in a cell
is within `mesh` of its anchor, and prove the residual bound at each anchor.
-/
structure ResidualAnchorFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchorCount : Nat
  anchor : Fin anchorCount -> Real
  cellLeft : Fin anchorCount -> Real
  cellRight : Fin anchorCount -> Real
  hSlopeNonneg : 0 <= slope
  hCoverCells :
    ∀ eta ∈ Set.Ioc L U,
      ∃ i : Fin anchorCount, eta ∈ Set.Icc (cellLeft i) (cellRight i)
  hAnchorIn : ∀ i : Fin anchorCount, anchor i ∈ Set.Ioc L U
  hWithinMesh :
    ∀ i : Fin anchorCount, ∀ eta ∈ Set.Icc (cellLeft i) (cellRight i),
      |eta - anchor i| <= mesh
  hAnchorResidual :
    ∀ i : Fin anchorCount, |cert.residual (anchor i)| <= sampleRadius
  hResidualVariation :
    ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
      |cert.residual eta - cert.residual anchor| <=
        slope * |eta - anchor|
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

structure ResidualAnchorChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorEnvelopeData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Collapse finite anchor-cell cover data to the existing residual-anchor
envelope receiver. -/
def ResidualAnchorFiniteCoverData.toResidualAnchorEnvelopeData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorFiniteCoverData cert) :
    ResidualAnchorEnvelopeData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    hSlopeNonneg := data.hSlopeNonneg
    hCover := by
      intro eta heta
      rcases data.hCoverCells eta heta with ⟨i, hi⟩
      exact
        ⟨data.anchor i, data.hAnchorIn i, data.hWithinMesh i eta hi,
          data.hAnchorResidual i⟩
    hResidualVariation := data.hResidualVariation
    hEnvelope := data.hEnvelope }

/-- Collapse finite-cover chunk proof data to the existing residual-anchor
chunk proof packet. -/
def ResidualAnchorFiniteCoverChunkProofData.toResidualAnchorChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorFiniteCoverChunkProofData cert) :
    ResidualAnchorChunkProofData cert :=
  { envelope := data.envelope.toResidualAnchorEnvelopeData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Single-anchor residual-cover data for one Taylor/model chunk.

This is the smallest generator-facing refinement of the residual-anchor route:
the generated payload supplies one anchor inside the chunk, proves the whole
chunk lies within `mesh` of that anchor, and then reuses the finite-cover
receiver with a one-cell cover. -/
structure ResidualAnchorSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  hSlopeNonneg : 0 <= slope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualVariation :
    ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
      |cert.residual eta - cert.residual anchor| <=
        slope * |eta - anchor|
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorSingleCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Expand one-anchor cover data into the finite-cover receiver. -/
def ResidualAnchorSingleCoverData.toResidualAnchorFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorSingleCoverData cert) :
    ResidualAnchorFiniteCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchorCount := 1
    anchor := fun _ => data.anchor
    cellLeft := fun _ => L
    cellRight := fun _ => U
    hSlopeNonneg := data.hSlopeNonneg
    hCoverCells := by
      intro eta heta
      refine ⟨⟨0, by decide⟩, ?_⟩
      exact ⟨le_of_lt heta.1, heta.2⟩
    hAnchorIn := by
      intro _
      exact data.hAnchorIn
    hWithinMesh := by
      intro _ eta heta
      have hLeftEta : data.anchor - data.mesh <= eta := by
        exact le_trans data.hLeftMesh heta.1
      have hRightEta : eta <= data.anchor + data.mesh := by
        exact le_trans heta.2 data.hRightMesh
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    hAnchorResidual := by
      intro _
      exact data.hAnchorResidual
    hResidualVariation := data.hResidualVariation
    hEnvelope := data.hEnvelope }

/-- Expand one-anchor chunk proof data into the finite-cover receiver. -/
def ResidualAnchorSingleCoverChunkProofData.toResidualAnchorFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorSingleCoverChunkProofData cert) :
    ResidualAnchorFiniteCoverChunkProofData cert :=
  { envelope := data.envelope.toResidualAnchorFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Residual variation from a derivative bound on the closed chunk.  This is
the next proof-producing bridge for the refined generator: instead of emitting
the two-point Lipschitz statement directly, a payload may prove a derivative
bound for the residual on `[L,U]`. -/
theorem residual_variation_of_deriv_bound
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {slope : Real}
    (hDifferentiable :
      ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta)
    (hDerivBound :
      ∀ eta ∈ Set.Icc L U, ‖deriv cert.residual eta‖ <= slope) :
    ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
      |cert.residual eta - cert.residual anchor| <=
        slope * |eta - anchor| := by
  intro eta heta anchor hanchor
  have hconvex : Convex Real (Set.Icc L U) := by
    simpa using (convex_Icc L U)
  have hetaIcc : eta ∈ Set.Icc L U := ⟨le_of_lt heta.1, heta.2⟩
  have hanchorIcc : anchor ∈ Set.Icc L U :=
    ⟨le_of_lt hanchor.1, hanchor.2⟩
  simpa [Real.norm_eq_abs, abs_sub_comm] using
    (Convex.norm_image_sub_le_of_norm_deriv_le
      (f := cert.residual) (s := Set.Icc L U)
      (x := eta) (y := anchor)
      hDifferentiable hDerivBound hconvex hetaIcc hanchorIcc)

/-- Single-anchor residual data where the local variation is supplied by a
derivative bound.  This is the intended pilot surface after the direct interval
residual route failed from dependency overestimation. -/
structure ResidualAnchorDerivativeSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  hSlopeNonneg : 0 <= slope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hResidualDerivBound :
    ∀ eta ∈ Set.Icc L U, ‖deriv cert.residual eta‖ <= slope
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorDerivativeSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeSingleCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Derivative single-cover data where the derivative norm bound is proved by a
finite cover of the closed chunk.

This is the direct residual-jet landing surface after broad raw/poly and
second-derivative interval bounds proved too wide: generated code may prove
small derivative-residual bounds on local cells, while Lean only packages the
finite cover into the global derivative bound required by
`ResidualAnchorDerivativeSingleCoverData`. -/
structure ResidualAnchorDerivativeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  derivCellCount : Nat
  derivCellLeft : Fin derivCellCount -> Real
  derivCellRight : Fin derivCellCount -> Real
  hSlopeNonneg : 0 <= slope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCells :
    ∀ eta ∈ Set.Icc L U,
      ∃ i : Fin derivCellCount,
        eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i)
  hResidualDerivBoundOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        ‖deriv cert.residual eta‖ <= slope
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorDerivativeFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Derivative finite-cover data where each derivative cell is supplied as a
two-sided residual-derivative interval.

This facade keeps the active finite-cover route, but gives generated code a
more arithmetic landing surface than a direct norm inequality on every cell:
prove lower/upper bounds for `deriv residual`, prove the two endpoints are
inside `[-slope, slope]`, and Lean packages the absolute-value bound. -/
structure ResidualAnchorDerivativeIntervalFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  derivCellCount : Nat
  derivCellLeft : Fin derivCellCount -> Real
  derivCellRight : Fin derivCellCount -> Real
  derivLower : Fin derivCellCount -> Real
  derivUpper : Fin derivCellCount -> Real
  hSlopeNonneg : 0 <= slope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCells :
    ∀ eta ∈ Set.Icc L U,
      ∃ i : Fin derivCellCount,
        eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i)
  hResidualDerivLowerOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        derivLower i <= deriv cert.residual eta
  hResidualDerivUpperOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        deriv cert.residual eta <= derivUpper i
  hDerivLowerAbs : ∀ i : Fin derivCellCount, -slope <= derivLower i
  hDerivUpperAbs : ∀ i : Fin derivCellCount, derivUpper i <= slope
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeIntervalFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Canonical nonnegative slope extracted from finite derivative intervals.

For each derivative cell it dominates both interval endpoints in absolute
value; summing those nonnegative cell envelopes gives a single global slope
for the existing finite-cover receiver. -/
def derivativeIntervalAutoSlope {N : Nat}
    (derivLower derivUpper : Fin N -> Real) : Real :=
  ∑ i : Fin N, max 0 (max (-(derivLower i)) (derivUpper i))

theorem derivativeIntervalAutoSlope_nonneg {N : Nat}
    (derivLower derivUpper : Fin N -> Real) :
    0 <= derivativeIntervalAutoSlope derivLower derivUpper := by
  unfold derivativeIntervalAutoSlope
  exact Finset.sum_nonneg (by
    intro i _hi
    exact le_max_left 0 (max (-(derivLower i)) (derivUpper i)))

theorem neg_derivativeIntervalAutoSlope_le_derivLower {N : Nat}
    (derivLower derivUpper : Fin N -> Real) (i : Fin N) :
    -derivativeIntervalAutoSlope derivLower derivUpper <= derivLower i := by
  let term : Fin N -> Real :=
    fun j => max 0 (max (-(derivLower j)) (derivUpper j))
  have hterm_nonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin N)), 0 <= term j := by
    intro j _hj
    exact le_max_left 0 (max (-(derivLower j)) (derivUpper j))
  have hsingle : term i <= ∑ j : Fin N, term j := by
    exact Finset.single_le_sum hterm_nonneg (by simp)
  have hneg : -derivLower i <= term i := by
    exact
      le_trans (le_max_left (-(derivLower i)) (derivUpper i))
        (le_max_right 0 (max (-(derivLower i)) (derivUpper i)))
  have hslope :
      -derivLower i <= derivativeIntervalAutoSlope derivLower derivUpper := by
    simpa [derivativeIntervalAutoSlope, term] using le_trans hneg hsingle
  linarith

theorem derivUpper_le_derivativeIntervalAutoSlope {N : Nat}
    (derivLower derivUpper : Fin N -> Real) (i : Fin N) :
    derivUpper i <= derivativeIntervalAutoSlope derivLower derivUpper := by
  let term : Fin N -> Real :=
    fun j => max 0 (max (-(derivLower j)) (derivUpper j))
  have hterm_nonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin N)), 0 <= term j := by
    intro j _hj
    exact le_max_left 0 (max (-(derivLower j)) (derivUpper j))
  have hsingle : term i <= ∑ j : Fin N, term j := by
    exact Finset.single_le_sum hterm_nonneg (by simp)
  have hupper : derivUpper i <= term i := by
    exact
      le_trans (le_max_right (-(derivLower i)) (derivUpper i))
        (le_max_right 0 (max (-(derivLower i)) (derivUpper i)))
  simpa [derivativeIntervalAutoSlope, term] using le_trans hupper hsingle

/-- Interval finite-cover data with the global derivative slope computed by
Lean from the supplied derivative-cell interval endpoints.  This removes the
generated `slope`, `hSlopeNonneg`, `hDerivLowerAbs`, and `hDerivUpperAbs`
fields from the active refined-subchunk proof surface. -/
structure ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  mesh : Real
  anchor : Real
  derivCellCount : Nat
  derivCellLeft : Fin derivCellCount -> Real
  derivCellRight : Fin derivCellCount -> Real
  derivLower : Fin derivCellCount -> Real
  derivUpper : Fin derivCellCount -> Real
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCells :
    ∀ eta ∈ Set.Icc L U,
      ∃ i : Fin derivCellCount,
        eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i)
  hResidualDerivLowerOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        derivLower i <= deriv cert.residual eta
  hResidualDerivUpperOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        deriv cert.residual eta <= derivUpper i
  hEnvelope :
    sampleRadius + derivativeIntervalAutoSlope derivLower derivUpper * mesh <=
      (cert.remainder : Real)

structure ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Auto-slope finite-cover data with the anchor residual and envelope merged
into one direct comparison.

This removes the generated `sampleRadius` datum and the separate
`hAnchorResidual` proof.  Lean recovers the old receiver by taking
`sampleRadius = |cert.residual anchor|`. -/
structure ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  mesh : Real
  anchor : Real
  derivCellCount : Nat
  derivCellLeft : Fin derivCellCount -> Real
  derivCellRight : Fin derivCellCount -> Real
  derivLower : Fin derivCellCount -> Real
  derivUpper : Fin derivCellCount -> Real
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCells :
    ∀ eta ∈ Set.Icc L U,
      ∃ i : Fin derivCellCount,
        eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i)
  hResidualDerivLowerOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        derivLower i <= deriv cert.residual eta
  hResidualDerivUpperOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        deriv cert.residual eta <= derivUpper i
  hEnvelope :
    |cert.residual anchor| +
        derivativeIntervalAutoSlope derivLower derivUpper * mesh <=
      (cert.remainder : Real)

structure ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope :
    ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverData
      cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Canonical nonnegative slope extracted from per-cell derivative norm
bounds.  Each cell slope is first clipped below by `0`, then all cell
envelopes are summed into the global slope required by the existing receiver. -/
def derivativeCellAutoSlope {N : Nat} (derivSlope : Fin N -> Real) : Real :=
  ∑ i : Fin N, max 0 (derivSlope i)

theorem derivativeCellAutoSlope_nonneg {N : Nat}
    (derivSlope : Fin N -> Real) :
    0 <= derivativeCellAutoSlope derivSlope := by
  unfold derivativeCellAutoSlope
  exact Finset.sum_nonneg (by
    intro i _hi
    exact le_max_left 0 (derivSlope i))

theorem derivSlope_le_derivativeCellAutoSlope {N : Nat}
    (derivSlope : Fin N -> Real) (i : Fin N) :
    derivSlope i <= derivativeCellAutoSlope derivSlope := by
  let term : Fin N -> Real := fun j => max 0 (derivSlope j)
  have hterm_nonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin N)), 0 <= term j := by
    intro j _hj
    exact le_max_left 0 (derivSlope j)
  have hsingle : term i <= ∑ j : Fin N, term j := by
    exact Finset.single_le_sum hterm_nonneg (by simp)
  have hle : derivSlope i <= term i := by
    exact le_max_right 0 (derivSlope i)
  simpa [derivativeCellAutoSlope, term] using le_trans hle hsingle

theorem derivativeCellAutoSlope_singleton (derivSlope : Fin 1 -> Real) :
    derivativeCellAutoSlope derivSlope =
      max 0 (derivSlope ⟨0, by decide⟩) := by
  simp [derivativeCellAutoSlope]

/-- Direct envelope receiver for the current one-cell route.

For `derivCellCount = 1`, generated code may prove the envelope inequality
against the scalar `max 0 (derivSlope 0)` instead of unfolding the finite sum
inside `derivativeCellAutoSlope`. -/
theorem direct_envelope_of_single_cell_residual_bound
    {k : Nat} {ell x L U lower upper sampleRadius mesh anchor : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {derivSlope : Fin 1 -> Real}
    (hResidual : |cert.residual anchor| <= sampleRadius)
    (hEnvelope :
      sampleRadius + max 0 (derivSlope ⟨0, by decide⟩) * mesh <=
        (cert.remainder : Real)) :
    |cert.residual anchor| + derivativeCellAutoSlope derivSlope * mesh <=
      (cert.remainder : Real) := by
  rw [derivativeCellAutoSlope_singleton derivSlope]
  have hsum :
      |cert.residual anchor| +
          max 0 (derivSlope ⟨0, by decide⟩) * mesh <=
        sampleRadius + max 0 (derivSlope ⟨0, by decide⟩) * mesh := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_right hResidual
        (max 0 (derivSlope ⟨0, by decide⟩) * mesh))
  exact le_trans hsum hEnvelope

/-- Direct-envelope finite-cover data where each derivative cell supplies a
single norm bound instead of lower/upper derivative interval endpoints. -/
structure ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  mesh : Real
  anchor : Real
  derivCellCount : Nat
  derivCellLeft : Fin derivCellCount -> Real
  derivCellRight : Fin derivCellCount -> Real
  derivSlope : Fin derivCellCount -> Real
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCells :
    ∀ eta ∈ Set.Icc L U,
      ∃ i : Fin derivCellCount,
        eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i)
  hResidualDerivBoundOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        ‖deriv cert.residual eta‖ <= derivSlope i
  hEnvelope :
    |cert.residual anchor| + derivativeCellAutoSlope derivSlope * mesh <=
      (cert.remainder : Real)

structure ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Derivative finite-cover data where each derivative-cell interval is proved
from a local derivative anchor and a second-derivative/Lipschitz envelope.

This is a proof-producing surface for the pilot residual-jet emitter: instead
of asking generated code to prove `derivLower <= deriv residual <= derivUpper`
directly on a cell, it can prove an interval for `deriv residual` at one local
anchor and a second-derivative bound on the same cell. -/
structure ResidualAnchorDerivativeJetIntervalFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  derivCellCount : Nat
  derivCellLeft : Fin derivCellCount -> Real
  derivCellRight : Fin derivCellCount -> Real
  derivLower : Fin derivCellCount -> Real
  derivUpper : Fin derivCellCount -> Real
  derivAnchor : Fin derivCellCount -> Real
  derivAnchorLower : Fin derivCellCount -> Real
  derivAnchorUpper : Fin derivCellCount -> Real
  derivMesh : Fin derivCellCount -> Real
  derivSlope : Fin derivCellCount -> Real
  hSlopeNonneg : 0 <= slope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCells :
    ∀ eta ∈ Set.Icc L U,
      ∃ i : Fin derivCellCount,
        eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i)
  hDerivSlopeNonneg : ∀ i : Fin derivCellCount, 0 <= derivSlope i
  hDerivAnchorIn :
    ∀ i : Fin derivCellCount,
      derivAnchor i ∈ Set.Icc (derivCellLeft i) (derivCellRight i)
  hDerivLeftMesh :
    ∀ i : Fin derivCellCount,
      derivAnchor i - derivMesh i <= derivCellLeft i
  hDerivRightMesh :
    ∀ i : Fin derivCellCount,
      derivCellRight i <= derivAnchor i + derivMesh i
  hDerivAnchorLower :
    ∀ i : Fin derivCellCount,
      derivAnchorLower i <= deriv cert.residual (derivAnchor i)
  hDerivAnchorUpper :
    ∀ i : Fin derivCellCount,
      deriv cert.residual (derivAnchor i) <= derivAnchorUpper i
  hResidualDerivDifferentiableOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        DifferentiableAt Real (fun t => deriv cert.residual t) eta
  hResidualSecondDerivBoundOnCell :
    ∀ i : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft i) (derivCellRight i),
        ‖deriv (fun t => deriv cert.residual t) eta‖ <= derivSlope i
  hDerivLowerFromAnchor :
    ∀ i : Fin derivCellCount,
      derivLower i <= derivAnchorLower i - derivSlope i * derivMesh i
  hDerivUpperFromAnchor :
    ∀ i : Fin derivCellCount,
      derivAnchorUpper i + derivSlope i * derivMesh i <= derivUpper i
  hDerivLowerAbs : ∀ i : Fin derivCellCount, -slope <= derivLower i
  hDerivUpperAbs : ∀ i : Fin derivCellCount, derivUpper i <= slope
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeJetIntervalFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Convert two-sided residual-derivative interval bounds into the norm bound
required by the derivative single-cover receiver.  This is the next
generator-facing surface after plain interval derivative enclosures proved too
wide: a sharper Cauchy/Taylor emitter can prove lower/upper derivative bounds
and leave Lean to perform the absolute-value packaging. -/
theorem residual_deriv_bound_of_interval_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {slope derivLower derivUpper : Real}
    (hDerivLower :
      ∀ eta ∈ Set.Icc L U, derivLower <= deriv cert.residual eta)
    (hDerivUpper :
      ∀ eta ∈ Set.Icc L U, deriv cert.residual eta <= derivUpper)
    (hDerivLowerAbs : -slope <= derivLower)
    (hDerivUpperAbs : derivUpper <= slope) :
    ∀ eta ∈ Set.Icc L U, ‖deriv cert.residual eta‖ <= slope := by
  intro eta heta
  have hLower : -slope <= deriv cert.residual eta :=
    le_trans hDerivLowerAbs (hDerivLower eta heta)
  have hUpper : deriv cert.residual eta <= slope :=
    le_trans (hDerivUpper eta heta) hDerivUpperAbs
  simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hLower, hUpper⟩)

/-- Bound the residual derivative from one derivative anchor and a second
derivative/Lipschitz envelope on the closed chunk.

This is the cancellation-preserving receiver for the refined generator: instead
of separately bounding raw and polynomial derivatives, a payload can prove that
`deriv residual` is tiny at one anchor and has controlled variation across the
subchunk. -/
theorem residual_deriv_bound_of_deriv_anchor_envelope
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {slope mesh anchor derivSampleRadius derivSlope : Real}
    (hDerivSlopeNonneg : 0 <= derivSlope)
    (hAnchorIn : anchor ∈ Set.Ioc L U)
    (hLeftMesh : anchor - mesh <= L)
    (hRightMesh : U <= anchor + mesh)
    (hAnchorDerivResidual :
      |deriv cert.residual anchor| <= derivSampleRadius)
    (hResidualDerivDifferentiable :
      ∀ eta ∈ Set.Icc L U,
        DifferentiableAt Real (fun t => deriv cert.residual t) eta)
    (hResidualSecondDerivBound :
      ∀ eta ∈ Set.Icc L U,
        ‖deriv (fun t => deriv cert.residual t) eta‖ <= derivSlope)
    (hDerivEnvelope : derivSampleRadius + derivSlope * mesh <= slope) :
    ∀ eta ∈ Set.Icc L U, ‖deriv cert.residual eta‖ <= slope := by
  intro eta heta
  have hconvex : Convex Real (Set.Icc L U) := by
    simpa using (convex_Icc L U)
  have hanchorIcc : anchor ∈ Set.Icc L U :=
    ⟨le_of_lt hAnchorIn.1, hAnchorIn.2⟩
  have hvar :
      |deriv cert.residual eta - deriv cert.residual anchor| <=
        derivSlope * |eta - anchor| := by
    simpa [Real.norm_eq_abs, abs_sub_comm] using
      (Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun t => deriv cert.residual t) (s := Set.Icc L U)
        (x := eta) (y := anchor)
        hResidualDerivDifferentiable hResidualSecondDerivBound hconvex
        heta hanchorIcc)
  have hWithinMesh : |eta - anchor| <= mesh := by
    have hLeftEta : anchor - mesh <= eta := le_trans hLeftMesh heta.1
    have hRightEta : eta <= anchor + mesh := le_trans heta.2 hRightMesh
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hvarMesh :
      |deriv cert.residual eta - deriv cert.residual anchor| <=
        derivSlope * mesh := by
    exact le_trans hvar (mul_le_mul_of_nonneg_left hWithinMesh hDerivSlopeNonneg)
  have htri :
      |deriv cert.residual eta| <=
        |deriv cert.residual eta - deriv cert.residual anchor| +
          |deriv cert.residual anchor| := by
    let a : Real := deriv cert.residual eta - deriv cert.residual anchor
    let b : Real := deriv cert.residual anchor
    have hdecomp : deriv cert.residual eta = a + b := by
      dsimp [a, b]
      ring
    calc
      |deriv cert.residual eta| = |a + b| := by rw [hdecomp]
      _ <= |a| + |b| := abs_add_le a b
      _ =
          |deriv cert.residual eta - deriv cert.residual anchor| +
            |deriv cert.residual anchor| := by
            rfl
  have habs :
      |deriv cert.residual eta| <= slope := by
    calc
      |deriv cert.residual eta|
          <= |deriv cert.residual eta - deriv cert.residual anchor| +
            |deriv cert.residual anchor| := htri
      _ <= derivSlope * mesh + derivSampleRadius :=
            add_le_add hvarMesh hAnchorDerivResidual
      _ = derivSampleRadius + derivSlope * mesh := by ring
      _ <= slope := hDerivEnvelope
  simpa [Real.norm_eq_abs] using habs

/-- Produce two-sided residual-derivative bounds on one derivative cell from a
local derivative anchor and a second-derivative/Lipschitz envelope.

This is the local residual-jet bridge behind the refined pilot emitter.  The
payload only has to prove the anchor interval and the second-derivative bound;
the lower/upper bounds over the whole cell are then pure triangle inequality
and interval arithmetic. -/
theorem residual_deriv_interval_bounds_of_cell_anchor_envelope
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {cellL cellU anchor mesh derivAnchorLower derivAnchorUpper
      derivSlope derivLower derivUpper : Real}
    (hDerivSlopeNonneg : 0 <= derivSlope)
    (hAnchorIn : anchor ∈ Set.Icc cellL cellU)
    (hLeftMesh : anchor - mesh <= cellL)
    (hRightMesh : cellU <= anchor + mesh)
    (hAnchorLower :
      derivAnchorLower <= deriv cert.residual anchor)
    (hAnchorUpper :
      deriv cert.residual anchor <= derivAnchorUpper)
    (hResidualDerivDifferentiable :
      ∀ eta ∈ Set.Icc cellL cellU,
        DifferentiableAt Real (fun t => deriv cert.residual t) eta)
    (hResidualSecondDerivBound :
      ∀ eta ∈ Set.Icc cellL cellU,
        ‖deriv (fun t => deriv cert.residual t) eta‖ <= derivSlope)
    (hDerivLowerFromAnchor :
      derivLower <= derivAnchorLower - derivSlope * mesh)
    (hDerivUpperFromAnchor :
      derivAnchorUpper + derivSlope * mesh <= derivUpper) :
    (∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta) ∧
      (∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper) := by
  constructor
  · intro eta heta
    have hconvex : Convex Real (Set.Icc cellL cellU) := by
      simpa using (convex_Icc cellL cellU)
    have hvar :
        |deriv cert.residual eta - deriv cert.residual anchor| <=
          derivSlope * |eta - anchor| := by
      simpa [Real.norm_eq_abs, abs_sub_comm] using
        (Convex.norm_image_sub_le_of_norm_deriv_le
          (f := fun t => deriv cert.residual t) (s := Set.Icc cellL cellU)
          (x := eta) (y := anchor)
          hResidualDerivDifferentiable hResidualSecondDerivBound hconvex
          heta hAnchorIn)
    have hWithinMesh : |eta - anchor| <= mesh := by
      have hLeftEta : anchor - mesh <= eta := le_trans hLeftMesh heta.1
      have hRightEta : eta <= anchor + mesh := le_trans heta.2 hRightMesh
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hvarMesh :
        |deriv cert.residual eta - deriv cert.residual anchor| <=
          derivSlope * mesh := by
      exact le_trans hvar
        (mul_le_mul_of_nonneg_left hWithinMesh hDerivSlopeNonneg)
    have hdiffLower :
        -(derivSlope * mesh) <=
          deriv cert.residual eta - deriv cert.residual anchor :=
      (abs_le.mp hvarMesh).1
    linarith
  · intro eta heta
    have hconvex : Convex Real (Set.Icc cellL cellU) := by
      simpa using (convex_Icc cellL cellU)
    have hvar :
        |deriv cert.residual eta - deriv cert.residual anchor| <=
          derivSlope * |eta - anchor| := by
      simpa [Real.norm_eq_abs, abs_sub_comm] using
        (Convex.norm_image_sub_le_of_norm_deriv_le
          (f := fun t => deriv cert.residual t) (s := Set.Icc cellL cellU)
          (x := eta) (y := anchor)
          hResidualDerivDifferentiable hResidualSecondDerivBound hconvex
          heta hAnchorIn)
    have hWithinMesh : |eta - anchor| <= mesh := by
      have hLeftEta : anchor - mesh <= eta := le_trans hLeftMesh heta.1
      have hRightEta : eta <= anchor + mesh := le_trans heta.2 hRightMesh
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hvarMesh :
        |deriv cert.residual eta - deriv cert.residual anchor| <=
          derivSlope * mesh := by
      exact le_trans hvar
        (mul_le_mul_of_nonneg_left hWithinMesh hDerivSlopeNonneg)
    have hdiffUpper :
        deriv cert.residual eta - deriv cert.residual anchor <=
          derivSlope * mesh :=
      (abs_le.mp hvarMesh).2
    linarith

/-- Build two-sided residual-derivative bounds from separate raw-profile and
polynomial-derivative bounds.

This is a proof-producing bridge for generators that can enclose the analytic
raw derivative and the Taylor polynomial derivative separately, then prove the
residual derivative identity on the chunk. -/
theorem residual_deriv_interval_bounds_of_raw_poly_deriv_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {rawDerivLower rawDerivUpper polyDerivLower polyDerivUpper
      derivLower derivUpper : Real}
    (hRawDerivLower :
      ∀ eta ∈ Set.Icc L U,
        rawDerivLower <=
          deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta)
    (hRawDerivUpper :
      ∀ eta ∈ Set.Icc L U,
        deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta <= rawDerivUpper)
    (hPolyDerivLower :
      ∀ eta ∈ Set.Icc L U, polyDerivLower <= deriv cert.polynomial eta)
    (hPolyDerivUpper :
      ∀ eta ∈ Set.Icc L U, deriv cert.polynomial eta <= polyDerivUpper)
    (hResidualDerivEq :
      ∀ eta ∈ Set.Icc L U,
        deriv cert.residual eta =
          deriv
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                k ell x) eta -
            deriv cert.polynomial eta)
    (hDerivLowerFromRawPoly :
      derivLower <= rawDerivLower - polyDerivUpper)
    (hDerivUpperFromRawPoly :
      rawDerivUpper - polyDerivLower <= derivUpper) :
    (∀ eta ∈ Set.Icc L U, derivLower <= deriv cert.residual eta) ∧
      (∀ eta ∈ Set.Icc L U, deriv cert.residual eta <= derivUpper) := by
  constructor
  · intro eta heta
    have hraw := hRawDerivLower eta heta
    have hpoly := hPolyDerivUpper eta heta
    rw [hResidualDerivEq eta heta]
    linarith
  · intro eta heta
    have hraw := hRawDerivUpper eta heta
    have hpoly := hPolyDerivLower eta heta
    rw [hResidualDerivEq eta heta]
    linarith

/-- Cell-local version of
`residual_deriv_interval_bounds_of_raw_poly_deriv_bounds`.

The direct route-B overlay needs exactly this surface for
`hResidualDerivLowerOnCell` and `hResidualDerivUpperOnCell`: generated code can
prove raw-profile and polynomial-derivative enclosures on a derivative cell,
while Lean supplies the residual-derivative identity from definitions. -/
theorem residual_deriv_interval_bounds_on_cell_of_raw_poly_deriv_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {cellL cellU rawDerivLower rawDerivUpper polyDerivLower polyDerivUpper
      derivLower derivUpper : Real}
    (hRawDerivLower :
      ∀ eta ∈ Set.Icc cellL cellU,
        rawDerivLower <=
          deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta)
    (hRawDerivUpper :
      ∀ eta ∈ Set.Icc cellL cellU,
        deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta <= rawDerivUpper)
    (hPolyDerivLower :
      ∀ eta ∈ Set.Icc cellL cellU,
        polyDerivLower <= deriv cert.polynomial eta)
    (hPolyDerivUpper :
      ∀ eta ∈ Set.Icc cellL cellU,
        deriv cert.polynomial eta <= polyDerivUpper)
    (hDerivLowerFromRawPoly :
      derivLower <= rawDerivLower - polyDerivUpper)
    (hDerivUpperFromRawPoly :
      rawDerivUpper - polyDerivLower <= derivUpper) :
    (∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta) ∧
      (∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper) := by
  constructor
  · intro eta heta
    have hraw := hRawDerivLower eta heta
    have hpoly := hPolyDerivUpper eta heta
    rw [cert.residual_deriv_eq eta]
    linarith
  · intro eta heta
    have hraw := hRawDerivUpper eta heta
    have hpoly := hPolyDerivLower eta heta
    rw [cert.residual_deriv_eq eta]
    linarith

/-- Composite derivative-cell receiver for route-B.

Generated code proves raw derivative bounds and term-wise Taylor-polynomial
derivative bounds on the same cell.  Lean sums the polynomial derivative terms,
supplies the residual derivative identity, and packages the two-sided residual
derivative interval. -/
theorem residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {cellL cellU rawDerivLower rawDerivUpper polyDerivLower polyDerivUpper
      derivLower derivUpper : Real}
    {termDerivLower termDerivUpper : Fin (cert.degree + 1) -> Real}
    (hRawDerivLower :
      ∀ eta ∈ Set.Icc cellL cellU,
        rawDerivLower <=
          deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta)
    (hRawDerivUpper :
      ∀ eta ∈ Set.Icc cellL cellU,
        deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta <= rawDerivUpper)
    (hPolyTerms :
      cert.PolynomialDerivativeTermBoundsOnCell cellL cellU
        termDerivLower termDerivUpper)
    (hPolyDerivLower :
      polyDerivLower <= ∑ i : Fin (cert.degree + 1), termDerivLower i)
    (hPolyDerivUpper :
      (∑ i : Fin (cert.degree + 1), termDerivUpper i) <= polyDerivUpper)
    (hDerivLowerFromRawPoly :
      derivLower <= rawDerivLower - polyDerivUpper)
    (hDerivUpperFromRawPoly :
      rawDerivUpper - polyDerivLower <= derivUpper) :
    (∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta) ∧
      (∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper) := by
  have hPoly :=
    cert.polynomial_deriv_bounds_on_cell_of_term_deriv_bounds hPolyTerms
      hPolyDerivLower hPolyDerivUpper
  exact
    cert.residual_deriv_interval_bounds_on_cell_of_raw_poly_deriv_bounds
      hRawDerivLower hRawDerivUpper hPoly.1 hPoly.2
      hDerivLowerFromRawPoly hDerivUpperFromRawPoly

/-- Composite derivative-cell receiver where the polynomial side is given as
arithmetic bounds for the explicit monomial derivative formula. -/
theorem residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {cellL cellU rawDerivLower rawDerivUpper polyDerivLower polyDerivUpper
      derivLower derivUpper : Real}
    {termDerivLower termDerivUpper : Fin (cert.degree + 1) -> Real}
    (hRawDerivLower :
      ∀ eta ∈ Set.Icc cellL cellU,
        rawDerivLower <=
          deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta)
    (hRawDerivUpper :
      ∀ eta ∈ Set.Icc cellL cellU,
        deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta <= rawDerivUpper)
    (hTermDerivLowerExpr :
      ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
        termDerivLower i <=
          (cert.coeff i : Real) *
            ((i.1 : Real) *
              (eta - (cert.center : Real)) ^ (i.1 - 1)))
    (hTermDerivUpperExpr :
      ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
        (cert.coeff i : Real) *
            ((i.1 : Real) *
              (eta - (cert.center : Real)) ^ (i.1 - 1)) <=
          termDerivUpper i)
    (hPolyDerivLower :
      polyDerivLower <= ∑ i : Fin (cert.degree + 1), termDerivLower i)
    (hPolyDerivUpper :
      (∑ i : Fin (cert.degree + 1), termDerivUpper i) <= polyDerivUpper)
    (hDerivLowerFromRawPoly :
      derivLower <= rawDerivLower - polyDerivUpper)
    (hDerivUpperFromRawPoly :
      rawDerivUpper - polyDerivLower <= derivUpper) :
    (∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta) ∧
      (∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper) := by
  have hPolyTerms :=
    cert.polynomial_derivative_term_bounds_on_cell_of_expr_bounds
      hTermDerivLowerExpr hTermDerivUpperExpr
  exact
    cert.residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_bounds
      hRawDerivLower hRawDerivUpper hPolyTerms hPolyDerivLower
      hPolyDerivUpper hDerivLowerFromRawPoly hDerivUpperFromRawPoly

/-- Cell-indexed composite derivative receiver for route-B.

This is the scalable version of
`residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds`:
generated code supplies raw derivative bounds, explicit monomial derivative
expression bounds, polynomial sum comparisons, and raw-minus-polynomial
comparisons for every derivative cell.  Lean packages the two structure fields
`hResidualDerivLowerOnCell` and `hResidualDerivUpperOnCell` at once. -/
theorem residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {derivCellCount : Nat}
    {derivCellLeft derivCellRight rawDerivLower rawDerivUpper
      polyDerivLower polyDerivUpper derivLower derivUpper :
        Fin derivCellCount -> Real}
    {termDerivLower termDerivUpper :
        Fin derivCellCount -> Fin (cert.degree + 1) -> Real}
    (hRawDerivLower :
      ∀ c : Fin derivCellCount,
        ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
          rawDerivLower c <=
            deriv
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                k ell x) eta)
    (hRawDerivUpper :
      ∀ c : Fin derivCellCount,
        ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
          deriv
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                k ell x) eta <= rawDerivUpper c)
    (hTermDerivLowerExpr :
      ∀ c : Fin derivCellCount,
        ∀ i : Fin (cert.degree + 1),
          ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
            termDerivLower c i <=
              (cert.coeff i : Real) *
                ((i.1 : Real) *
                  (eta - (cert.center : Real)) ^ (i.1 - 1)))
    (hTermDerivUpperExpr :
      ∀ c : Fin derivCellCount,
        ∀ i : Fin (cert.degree + 1),
          ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
            (cert.coeff i : Real) *
                ((i.1 : Real) *
                  (eta - (cert.center : Real)) ^ (i.1 - 1)) <=
              termDerivUpper c i)
    (hPolyDerivLower :
      ∀ c : Fin derivCellCount,
        polyDerivLower c <=
          ∑ i : Fin (cert.degree + 1), termDerivLower c i)
    (hPolyDerivUpper :
      ∀ c : Fin derivCellCount,
        (∑ i : Fin (cert.degree + 1), termDerivUpper c i) <=
          polyDerivUpper c)
    (hDerivLowerFromRawPoly :
      ∀ c : Fin derivCellCount,
        derivLower c <= rawDerivLower c - polyDerivUpper c)
    (hDerivUpperFromRawPoly :
      ∀ c : Fin derivCellCount,
        rawDerivUpper c - polyDerivLower c <= derivUpper c) :
    (∀ c : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
        derivLower c <= deriv cert.residual eta) ∧
      (∀ c : Fin derivCellCount,
        ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
          deriv cert.residual eta <= derivUpper c) := by
  constructor
  · intro c eta heta
    have hcell :=
      cert.residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds
        (cellL := derivCellLeft c) (cellU := derivCellRight c)
        (rawDerivLower := rawDerivLower c)
        (rawDerivUpper := rawDerivUpper c)
        (polyDerivLower := polyDerivLower c)
        (polyDerivUpper := polyDerivUpper c)
        (derivLower := derivLower c) (derivUpper := derivUpper c)
        (termDerivLower := termDerivLower c)
        (termDerivUpper := termDerivUpper c)
        (hRawDerivLower c) (hRawDerivUpper c)
        (hTermDerivLowerExpr c) (hTermDerivUpperExpr c)
        (hPolyDerivLower c) (hPolyDerivUpper c)
        (hDerivLowerFromRawPoly c) (hDerivUpperFromRawPoly c)
    exact hcell.1 eta heta
  · intro c eta heta
    have hcell :=
      cert.residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds
        (cellL := derivCellLeft c) (cellU := derivCellRight c)
        (rawDerivLower := rawDerivLower c)
        (rawDerivUpper := rawDerivUpper c)
        (polyDerivLower := polyDerivLower c)
        (polyDerivUpper := polyDerivUpper c)
        (derivLower := derivLower c) (derivUpper := derivUpper c)
        (termDerivLower := termDerivLower c)
        (termDerivUpper := termDerivUpper c)
        (hRawDerivLower c) (hRawDerivUpper c)
        (hTermDerivLowerExpr c) (hTermDerivUpperExpr c)
        (hPolyDerivLower c) (hPolyDerivUpper c)
        (hDerivLowerFromRawPoly c) (hDerivUpperFromRawPoly c)
    exact hcell.2 eta heta

/-- Package cell-indexed two-sided residual-derivative intervals into the
cell-indexed derivative norm bound required by the direct-envelope cell-slope
receiver. -/
theorem residual_deriv_bound_on_cells_of_interval_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {derivCellCount : Nat}
    {derivCellLeft derivCellRight derivLower derivUpper derivSlope :
      Fin derivCellCount -> Real}
    (hDerivLower :
      ∀ c : Fin derivCellCount,
        ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
          derivLower c <= deriv cert.residual eta)
    (hDerivUpper :
      ∀ c : Fin derivCellCount,
        ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
          deriv cert.residual eta <= derivUpper c)
    (hDerivLowerAbs :
      ∀ c : Fin derivCellCount, -derivSlope c <= derivLower c)
    (hDerivUpperAbs :
      ∀ c : Fin derivCellCount, derivUpper c <= derivSlope c) :
    ∀ c : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
        ‖deriv cert.residual eta‖ <= derivSlope c := by
  intro c eta heta
  have hLower : -derivSlope c <= deriv cert.residual eta :=
    le_trans (hDerivLowerAbs c) (hDerivLower c eta heta)
  have hUpper : deriv cert.residual eta <= derivSlope c :=
    le_trans (hDerivUpper c eta heta) (hDerivUpperAbs c)
  simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hLower, hUpper⟩)

/-- Single-cell interval receiver for the cancellation-preserving direct
residual-derivative route.

The current refined-subchunk route already has one derivative cell per
subchunk.  Generated proof data can therefore provide sharp lower/upper bounds
for `deriv cert.residual` directly on that cell, plus the two scalar
comparisons putting those endpoints inside `[-derivSlope, derivSlope]`.  Lean
then performs only the absolute-value packaging. -/
theorem residual_deriv_bound_on_single_cell_of_interval_bounds
    {k : Nat} {ell x L U lower upper cellL cellU
      derivLower derivUpper derivSlope : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hDerivLower :
      ∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta)
    (hDerivUpper :
      ∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper)
    (hDerivLowerAbs : -derivSlope <= derivLower)
    (hDerivUpperAbs : derivUpper <= derivSlope) :
    ∀ eta ∈ Set.Icc cellL cellU,
      ‖deriv cert.residual eta‖ <= derivSlope := by
  intro eta heta
  have hLower : -derivSlope <= deriv cert.residual eta :=
    le_trans hDerivLowerAbs (hDerivLower eta heta)
  have hUpper : deriv cert.residual eta <= derivSlope :=
    le_trans (hDerivUpper eta heta) hDerivUpperAbs
  simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hLower, hUpper⟩)

/-- Scalar one-cell finite-cover data for the current refined route.

The active direct subchunks all have one derivative cell.  This proof-data
facade lets generated code provide direct residual-derivative interval bounds
as scalar fields, while Lean expands them to the existing cell-slope
finite-cover receiver. -/
structure ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  mesh : Real
  anchor : Real
  cellL : Real
  cellU : Real
  derivLower : Real
  derivUpper : Real
  derivSlope : Real
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCell :
    ∀ eta ∈ Set.Icc L U, eta ∈ Set.Icc cellL cellU
  hResidualDerivLowerOnCell :
    ∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta
  hResidualDerivUpperOnCell :
    ∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper
  hDerivLowerAbs : -derivSlope <= derivLower
  hDerivUpperAbs : derivUpper <= derivSlope
  hEnvelope :
    |cert.residual anchor| + max 0 derivSlope * mesh <=
      (cert.remainder : Real)

/-- Expand scalar one-cell interval data to the existing cell-slope
direct-envelope finite-cover receiver. -/
def ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeFiniteCoverData.toResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeFiniteCoverData
        cert) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData cert :=
  { mesh := data.mesh
    anchor := data.anchor
    derivCellCount := 1
    derivCellLeft := fun _ => data.cellL
    derivCellRight := fun _ => data.cellU
    derivSlope := fun _ => data.derivSlope
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCells := by
      intro eta heta
      exact ⟨⟨0, by decide⟩, data.hDerivCoverCell eta heta⟩
    hResidualDerivBoundOnCell := by
      intro _i eta heta
      exact
        cert.residual_deriv_bound_on_single_cell_of_interval_bounds
          data.hResidualDerivLowerOnCell data.hResidualDerivUpperOnCell
          data.hDerivLowerAbs data.hDerivUpperAbs eta heta
    hEnvelope := by
      simpa [derivativeCellAutoSlope_singleton] using data.hEnvelope }

/-- Scalar one-cell finite-cover data whose envelope is proved through a
separate anchor residual radius.

This is the proof-producing shape exposed by the current worklist: generated
code proves `|cert.residual anchor| <= sampleRadius` and a rational envelope
comparison against `sampleRadius`.  Lean combines the two into the direct
envelope inequality required by the existing cell-slope receiver. -/
structure ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  mesh : Real
  anchor : Real
  cellL : Real
  cellU : Real
  derivLower : Real
  derivUpper : Real
  derivSlope : Real
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCell :
    ∀ eta ∈ Set.Icc L U, eta ∈ Set.Icc cellL cellU
  hResidualDerivLowerOnCell :
    ∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta
  hResidualDerivUpperOnCell :
    ∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper
  hDerivLowerAbs : -derivSlope <= derivLower
  hDerivUpperAbs : derivUpper <= derivSlope
  hEnvelope :
    sampleRadius + max 0 derivSlope * mesh <= (cert.remainder : Real)

/-- Collapse sample-envelope one-cell data to the direct-envelope one-cell
receiver by applying the anchor residual bound. -/
def ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData.toResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData
        cert) :
    ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeFiniteCoverData
      cert :=
  { mesh := data.mesh
    anchor := data.anchor
    cellL := data.cellL
    cellU := data.cellU
    derivLower := data.derivLower
    derivUpper := data.derivUpper
    derivSlope := data.derivSlope
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCell := data.hDerivCoverCell
    hResidualDerivLowerOnCell := data.hResidualDerivLowerOnCell
    hResidualDerivUpperOnCell := data.hResidualDerivUpperOnCell
    hDerivLowerAbs := data.hDerivLowerAbs
    hDerivUpperAbs := data.hDerivUpperAbs
    hEnvelope := by
      have hsum :
          |cert.residual data.anchor| +
              max 0 data.derivSlope * data.mesh <=
            data.sampleRadius + max 0 data.derivSlope * data.mesh := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right data.hAnchorResidual
            (max 0 data.derivSlope * data.mesh)
      exact le_trans hsum data.hEnvelope }

/-- Scalar one-cell data where the anchor residual proof is generated in the
sharp raw-center-minus-coeff0 form.

This is the current preferred payload shape: generated code proves one local
analytic bound for the raw profile value at the Taylor center, and Lean turns
it into the sampled-envelope `hAnchorResidual` field. -/
structure ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  mesh : Real
  anchor : Real
  cellL : Real
  cellU : Real
  derivLower : Real
  derivUpper : Real
  derivSlope : Real
  hAnchorCenter : anchor = (cert.center : Real)
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hRawCenterCoeffAbs :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x anchor - (cert.coeff 0 : Real)| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hDerivCoverCell :
    ∀ eta ∈ Set.Icc L U, eta ∈ Set.Icc cellL cellU
  hResidualDerivLowerOnCell :
    ∀ eta ∈ Set.Icc cellL cellU, derivLower <= deriv cert.residual eta
  hResidualDerivUpperOnCell :
    ∀ eta ∈ Set.Icc cellL cellU, deriv cert.residual eta <= derivUpper
  hDerivLowerAbs : -derivSlope <= derivLower
  hDerivUpperAbs : derivUpper <= derivSlope
  hEnvelope :
    sampleRadius + max 0 derivSlope * mesh <= (cert.remainder : Real)

/-- Convert sharp raw-center-minus-coeff0 one-cell data to the sampled-envelope
receiver. -/
def ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData.toResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData
        cert) :
    ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData
      cert :=
  { sampleRadius := data.sampleRadius
    mesh := data.mesh
    anchor := data.anchor
    cellL := data.cellL
    cellU := data.cellU
    derivLower := data.derivLower
    derivUpper := data.derivUpper
    derivSlope := data.derivSlope
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual :=
      cert.anchor_residual_abs_of_raw_center_coeff_abs_bound
        data.hAnchorCenter data.hRawCenterCoeffAbs
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCell := data.hDerivCoverCell
    hResidualDerivLowerOnCell := data.hResidualDerivLowerOnCell
    hResidualDerivUpperOnCell := data.hResidualDerivUpperOnCell
    hDerivLowerAbs := data.hDerivLowerAbs
    hDerivUpperAbs := data.hDerivUpperAbs
    hEnvelope := data.hEnvelope }

/-- Composite cell-indexed derivative norm receiver where the raw side is an
analytic derivative enclosure and the polynomial side is supplied as explicit
monomial derivative expression bounds. -/
theorem residual_deriv_bound_on_cells_of_raw_deriv_and_poly_term_expr_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {derivCellCount : Nat}
    {derivCellLeft derivCellRight rawDerivLower rawDerivUpper
      polyDerivLower polyDerivUpper derivLower derivUpper derivSlope :
        Fin derivCellCount -> Real}
    {termDerivLower termDerivUpper :
        Fin derivCellCount -> Fin (cert.degree + 1) -> Real}
    (hRawDerivLower :
      ∀ c : Fin derivCellCount,
        ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
          rawDerivLower c <=
            deriv
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                k ell x) eta)
    (hRawDerivUpper :
      ∀ c : Fin derivCellCount,
        ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
          deriv
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                k ell x) eta <= rawDerivUpper c)
    (hTermDerivLowerExpr :
      ∀ c : Fin derivCellCount,
        ∀ i : Fin (cert.degree + 1),
          ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
            termDerivLower c i <=
              (cert.coeff i : Real) *
                ((i.1 : Real) *
                  (eta - (cert.center : Real)) ^ (i.1 - 1)))
    (hTermDerivUpperExpr :
      ∀ c : Fin derivCellCount,
        ∀ i : Fin (cert.degree + 1),
          ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
            (cert.coeff i : Real) *
                ((i.1 : Real) *
                  (eta - (cert.center : Real)) ^ (i.1 - 1)) <=
              termDerivUpper c i)
    (hPolyDerivLower :
      ∀ c : Fin derivCellCount,
        polyDerivLower c <=
          ∑ i : Fin (cert.degree + 1), termDerivLower c i)
    (hPolyDerivUpper :
      ∀ c : Fin derivCellCount,
        (∑ i : Fin (cert.degree + 1), termDerivUpper c i) <=
          polyDerivUpper c)
    (hDerivLowerFromRawPoly :
      ∀ c : Fin derivCellCount,
        derivLower c <= rawDerivLower c - polyDerivUpper c)
    (hDerivUpperFromRawPoly :
      ∀ c : Fin derivCellCount,
        rawDerivUpper c - polyDerivLower c <= derivUpper c)
    (hDerivLowerAbs :
      ∀ c : Fin derivCellCount, -derivSlope c <= derivLower c)
    (hDerivUpperAbs :
      ∀ c : Fin derivCellCount, derivUpper c <= derivSlope c) :
    ∀ c : Fin derivCellCount,
      ∀ eta ∈ Set.Icc (derivCellLeft c) (derivCellRight c),
        ‖deriv cert.residual eta‖ <= derivSlope c := by
  have hIntervals :=
    cert.residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds
      (derivCellLeft := derivCellLeft) (derivCellRight := derivCellRight)
      (rawDerivLower := rawDerivLower) (rawDerivUpper := rawDerivUpper)
      (polyDerivLower := polyDerivLower) (polyDerivUpper := polyDerivUpper)
      (derivLower := derivLower) (derivUpper := derivUpper)
      (termDerivLower := termDerivLower) (termDerivUpper := termDerivUpper)
      hRawDerivLower hRawDerivUpper hTermDerivLowerExpr
      hTermDerivUpperExpr hPolyDerivLower hPolyDerivUpper
      hDerivLowerFromRawPoly hDerivUpperFromRawPoly
  exact
    cert.residual_deriv_bound_on_cells_of_interval_bounds hIntervals.1
      hIntervals.2 hDerivLowerAbs hDerivUpperAbs

/-- Single-cell composite derivative norm receiver for route-B.

The current direct refined subchunk overlays use exactly one derivative cell
per refined subchunk.  This scalar receiver keeps generated payloads from
building a synthetic `Fin 1` layer while reusing the checked raw/poly
derivative interval receiver. -/
theorem residual_deriv_bound_on_single_cell_of_raw_deriv_and_poly_term_expr_bounds
    {k : Nat} {ell x L U lower upper cellL cellU rawDerivLower rawDerivUpper
      polyDerivLower polyDerivUpper derivLower derivUpper derivSlope : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {termDerivLower termDerivUpper : Fin (cert.degree + 1) -> Real}
    (hRawDerivLower :
      ∀ eta ∈ Set.Icc cellL cellU,
        rawDerivLower <=
          deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta)
    (hRawDerivUpper :
      ∀ eta ∈ Set.Icc cellL cellU,
        deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta <= rawDerivUpper)
    (hTermDerivLowerExpr :
      ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
        termDerivLower i <=
          (cert.coeff i : Real) *
            ((i.1 : Real) *
              (eta - (cert.center : Real)) ^ (i.1 - 1)))
    (hTermDerivUpperExpr :
      ∀ i : Fin (cert.degree + 1), ∀ eta ∈ Set.Icc cellL cellU,
        (cert.coeff i : Real) *
            ((i.1 : Real) *
              (eta - (cert.center : Real)) ^ (i.1 - 1)) <=
          termDerivUpper i)
    (hPolyDerivLower :
      polyDerivLower <= ∑ i : Fin (cert.degree + 1), termDerivLower i)
    (hPolyDerivUpper :
      (∑ i : Fin (cert.degree + 1), termDerivUpper i) <=
        polyDerivUpper)
    (hDerivLowerFromRawPoly :
      derivLower <= rawDerivLower - polyDerivUpper)
    (hDerivUpperFromRawPoly :
      rawDerivUpper - polyDerivLower <= derivUpper)
    (hDerivLowerAbs : -derivSlope <= derivLower)
    (hDerivUpperAbs : derivUpper <= derivSlope) :
    ∀ eta ∈ Set.Icc cellL cellU,
      ‖deriv cert.residual eta‖ <= derivSlope := by
  have hIntervals :=
    cert.residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds
      (cellL := cellL) (cellU := cellU)
      (rawDerivLower := rawDerivLower) (rawDerivUpper := rawDerivUpper)
      (polyDerivLower := polyDerivLower) (polyDerivUpper := polyDerivUpper)
      (derivLower := derivLower) (derivUpper := derivUpper)
      (termDerivLower := termDerivLower) (termDerivUpper := termDerivUpper)
      hRawDerivLower hRawDerivUpper hTermDerivLowerExpr
      hTermDerivUpperExpr hPolyDerivLower hPolyDerivUpper
      hDerivLowerFromRawPoly hDerivUpperFromRawPoly
  intro eta heta
  have hLower : -derivSlope <= deriv cert.residual eta :=
    le_trans hDerivLowerAbs (hIntervals.1 eta heta)
  have hUpper : deriv cert.residual eta <= derivSlope :=
    le_trans (hIntervals.2 eta heta) hDerivUpperAbs
  simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hLower, hUpper⟩)

/-- Derivative single-cover data where the universal derivative norm bound is
itself built from a two-sided derivative interval.  The proof-producing
generator can target this shape with sharp analytic derivative enclosures. -/
structure ResidualAnchorDerivativeIntervalSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  derivLower : Real
  derivUpper : Real
  hSlopeNonneg : 0 <= slope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hResidualDerivLower :
    ∀ eta ∈ Set.Icc L U, derivLower <= deriv cert.residual eta
  hResidualDerivUpper :
    ∀ eta ∈ Set.Icc L U, deriv cert.residual eta <= derivUpper
  hDerivLowerAbs : -slope <= derivLower
  hDerivUpperAbs : derivUpper <= slope
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorDerivativeIntervalSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeIntervalSingleCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Derivative single-cover data where the derivative norm bound is built from
one anchor value for `deriv residual` plus a second-derivative/Lipschitz bound.
This is the active cancellation-preserving target after raw/poly subtraction
proved too wide. -/
structure ResidualAnchorDerivativeSecondDerivativeSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  derivSampleRadius : Real
  derivSlope : Real
  hSlopeNonneg : 0 <= slope
  hDerivSlopeNonneg : 0 <= derivSlope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hAnchorDerivResidual :
    |deriv cert.residual anchor| <= derivSampleRadius
  hResidualDerivDifferentiable :
    ∀ eta ∈ Set.Icc L U,
      DifferentiableAt Real (fun t => deriv cert.residual t) eta
  hResidualSecondDerivBound :
    ∀ eta ∈ Set.Icc L U,
      ‖deriv (fun t => deriv cert.residual t) eta‖ <= derivSlope
  hDerivEnvelope : derivSampleRadius + derivSlope * mesh <= slope
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorDerivativeSecondDerivativeSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeSecondDerivativeSingleCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Derivative interval single-cover data where the two-sided residual
derivative interval is produced from raw-profile and polynomial derivative
intervals plus the residual derivative identity. -/
structure ResidualAnchorDerivativeRawPolyIntervalSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  sampleRadius : Real
  slope : Real
  mesh : Real
  anchor : Real
  derivLower : Real
  derivUpper : Real
  rawDerivLower : Real
  rawDerivUpper : Real
  polyDerivLower : Real
  polyDerivUpper : Real
  hSlopeNonneg : 0 <= slope
  hAnchorIn : anchor ∈ Set.Ioc L U
  hLeftMesh : anchor - mesh <= L
  hRightMesh : U <= anchor + mesh
  hAnchorResidual : |cert.residual anchor| <= sampleRadius
  hResidualDifferentiable :
    ∀ eta ∈ Set.Icc L U, DifferentiableAt Real cert.residual eta
  hRawDerivLower :
    ∀ eta ∈ Set.Icc L U,
      rawDerivLower <=
        deriv
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x) eta
  hRawDerivUpper :
    ∀ eta ∈ Set.Icc L U,
      deriv
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            k ell x) eta <= rawDerivUpper
  hPolyDerivLower :
    ∀ eta ∈ Set.Icc L U, polyDerivLower <= deriv cert.polynomial eta
  hPolyDerivUpper :
    ∀ eta ∈ Set.Icc L U, deriv cert.polynomial eta <= polyDerivUpper
  hResidualDerivEq :
    ∀ eta ∈ Set.Icc L U,
      deriv cert.residual eta =
        deriv
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x) eta -
          deriv cert.polynomial eta
  hDerivLowerFromRawPoly :
    derivLower <= rawDerivLower - polyDerivUpper
  hDerivUpperFromRawPoly :
    rawDerivUpper - polyDerivLower <= derivUpper
  hDerivLowerAbs : -slope <= derivLower
  hDerivUpperAbs : derivUpper <= slope
  hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real)

structure ResidualAnchorDerivativeRawPolyIntervalSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeRawPolyIntervalSingleCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  hIntegralLower : lower <= cert.lowerModelIntegral
  hIntegralUpper : cert.upperModelIntegral <= upper

/-- Collapse derivative-bound single-anchor data to the single-cover receiver. -/
def ResidualAnchorDerivativeSingleCoverData.toResidualAnchorSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeSingleCoverData cert) :
    ResidualAnchorSingleCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchor := data.anchor
    hSlopeNonneg := data.hSlopeNonneg
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualVariation :=
      cert.residual_variation_of_deriv_bound data.hResidualDifferentiable
        data.hResidualDerivBound
    hEnvelope := data.hEnvelope }

/-- Collapse derivative-bound single-anchor chunk data to the single-cover
receiver. -/
def ResidualAnchorDerivativeSingleCoverChunkProofData.toResidualAnchorSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeSingleCoverChunkProofData cert) :
    ResidualAnchorSingleCoverChunkProofData cert :=
  { envelope := data.envelope.toResidualAnchorSingleCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Collapse finite-cover derivative-bound data to the derivative single-cover
receiver. -/
def ResidualAnchorDerivativeFiniteCoverData.toResidualAnchorDerivativeSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeFiniteCoverData cert) :
    ResidualAnchorDerivativeSingleCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchor := data.anchor
    hSlopeNonneg := data.hSlopeNonneg
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualDifferentiable := data.hResidualDifferentiable
    hResidualDerivBound := by
      intro eta heta
      rcases data.hDerivCoverCells eta heta with ⟨i, hi⟩
      exact data.hResidualDerivBoundOnCell i eta hi
    hEnvelope := data.hEnvelope }

/-- Collapse finite-cover derivative-bound chunk proof data to the derivative
single-cover receiver. -/
def ResidualAnchorDerivativeFiniteCoverChunkProofData.toResidualAnchorDerivativeSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeFiniteCoverChunkProofData cert) :
    ResidualAnchorDerivativeSingleCoverChunkProofData cert :=
  { envelope := data.envelope.toResidualAnchorDerivativeSingleCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Collapse interval finite-cover derivative-bound data to the finite-cover
derivative receiver. -/
def ResidualAnchorDerivativeIntervalFiniteCoverData.toResidualAnchorDerivativeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeIntervalFiniteCoverData cert) :
    ResidualAnchorDerivativeFiniteCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchor := data.anchor
    derivCellCount := data.derivCellCount
    derivCellLeft := data.derivCellLeft
    derivCellRight := data.derivCellRight
    hSlopeNonneg := data.hSlopeNonneg
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCells := data.hDerivCoverCells
    hResidualDerivBoundOnCell := by
      intro i eta heta
      have hLower : -data.slope <= deriv cert.residual eta :=
        le_trans (data.hDerivLowerAbs i)
          (data.hResidualDerivLowerOnCell i eta heta)
      have hUpper : deriv cert.residual eta <= data.slope :=
        le_trans (data.hResidualDerivUpperOnCell i eta heta)
          (data.hDerivUpperAbs i)
      simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hLower, hUpper⟩)
    hEnvelope := data.hEnvelope }

/-- Collapse interval finite-cover chunk proof data to the finite-cover
derivative receiver. -/
def ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData.toResidualAnchorDerivativeFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData cert) :
    ResidualAnchorDerivativeFiniteCoverChunkProofData cert :=
  { envelope := data.envelope.toResidualAnchorDerivativeFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Expand auto-slope interval finite-cover data to the existing interval
finite-cover receiver. -/
def ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData.toResidualAnchorDerivativeIntervalFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData cert) :
    ResidualAnchorDerivativeIntervalFiniteCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope :=
      derivativeIntervalAutoSlope data.derivLower data.derivUpper
    mesh := data.mesh
    anchor := data.anchor
    derivCellCount := data.derivCellCount
    derivCellLeft := data.derivCellLeft
    derivCellRight := data.derivCellRight
    derivLower := data.derivLower
    derivUpper := data.derivUpper
    hSlopeNonneg :=
      derivativeIntervalAutoSlope_nonneg data.derivLower data.derivUpper
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCells := data.hDerivCoverCells
    hResidualDerivLowerOnCell := data.hResidualDerivLowerOnCell
    hResidualDerivUpperOnCell := data.hResidualDerivUpperOnCell
    hDerivLowerAbs :=
      neg_derivativeIntervalAutoSlope_le_derivLower
        data.derivLower data.derivUpper
    hDerivUpperAbs :=
      derivUpper_le_derivativeIntervalAutoSlope
        data.derivLower data.derivUpper
    hEnvelope := data.hEnvelope }

/-- Expand auto-slope interval finite-cover chunk data to the existing chunk
proof receiver. -/
def ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverChunkProofData.toResidualAnchorDerivativeIntervalFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverChunkProofData
        cert) :
    ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeIntervalFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Expand direct-envelope auto-slope finite-cover data to the auto-slope
receiver by taking the sample radius to be the actual anchor residual. -/
def ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverData.toResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverData
        cert) :
    ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData cert :=
  { sampleRadius := |cert.residual data.anchor|
    mesh := data.mesh
    anchor := data.anchor
    derivCellCount := data.derivCellCount
    derivCellLeft := data.derivCellLeft
    derivCellRight := data.derivCellRight
    derivLower := data.derivLower
    derivUpper := data.derivUpper
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := le_rfl
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCells := data.hDerivCoverCells
    hResidualDerivLowerOnCell := data.hResidualDerivLowerOnCell
    hResidualDerivUpperOnCell := data.hResidualDerivUpperOnCell
    hEnvelope := data.hEnvelope }

/-- Expand direct-envelope auto-slope chunk data to the existing interval
finite-cover chunk receiver. -/
def ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverChunkProofData.toResidualAnchorDerivativeIntervalFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverChunkProofData
        cert) :
    ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData cert :=
  { envelope :=
      ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData.toResidualAnchorDerivativeIntervalFiniteCoverData
        (data.envelope.toResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData)
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Expand cell-slope direct-envelope finite-cover data to the derivative
finite-cover receiver. -/
def ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData.toResidualAnchorDerivativeFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData cert) :
    ResidualAnchorDerivativeFiniteCoverData cert :=
  { sampleRadius := |cert.residual data.anchor|
    slope := derivativeCellAutoSlope data.derivSlope
    mesh := data.mesh
    anchor := data.anchor
    derivCellCount := data.derivCellCount
    derivCellLeft := data.derivCellLeft
    derivCellRight := data.derivCellRight
    hSlopeNonneg := derivativeCellAutoSlope_nonneg data.derivSlope
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := le_rfl
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCells := data.hDerivCoverCells
    hResidualDerivBoundOnCell := by
      intro i eta heta
      exact
        le_trans (data.hResidualDerivBoundOnCell i eta heta)
          (derivSlope_le_derivativeCellAutoSlope data.derivSlope i)
    hEnvelope := data.hEnvelope }

/-- Expand cell-slope direct-envelope chunk data to the derivative finite-cover
chunk receiver. -/
def ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverChunkProofData.toResidualAnchorDerivativeFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverChunkProofData
        cert) :
    ResidualAnchorDerivativeFiniteCoverChunkProofData cert :=
  { envelope := data.envelope.toResidualAnchorDerivativeFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Collapse residual-jet derivative-cell data to the interval finite-cover
receiver. -/
def ResidualAnchorDerivativeJetIntervalFiniteCoverData.toResidualAnchorDerivativeIntervalFiniteCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeJetIntervalFiniteCoverData cert) :
    ResidualAnchorDerivativeIntervalFiniteCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchor := data.anchor
    derivCellCount := data.derivCellCount
    derivCellLeft := data.derivCellLeft
    derivCellRight := data.derivCellRight
    derivLower := data.derivLower
    derivUpper := data.derivUpper
    hSlopeNonneg := data.hSlopeNonneg
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualDifferentiable := data.hResidualDifferentiable
    hDerivCoverCells := data.hDerivCoverCells
    hResidualDerivLowerOnCell := by
      intro i eta heta
      have hBounds :=
        cert.residual_deriv_interval_bounds_of_cell_anchor_envelope
          (data.hDerivSlopeNonneg i) (data.hDerivAnchorIn i)
          (data.hDerivLeftMesh i) (data.hDerivRightMesh i)
          (data.hDerivAnchorLower i) (data.hDerivAnchorUpper i)
          (data.hResidualDerivDifferentiableOnCell i)
          (data.hResidualSecondDerivBoundOnCell i)
          (data.hDerivLowerFromAnchor i) (data.hDerivUpperFromAnchor i)
      exact hBounds.1 eta heta
    hResidualDerivUpperOnCell := by
      intro i eta heta
      have hBounds :=
        cert.residual_deriv_interval_bounds_of_cell_anchor_envelope
          (data.hDerivSlopeNonneg i) (data.hDerivAnchorIn i)
          (data.hDerivLeftMesh i) (data.hDerivRightMesh i)
          (data.hDerivAnchorLower i) (data.hDerivAnchorUpper i)
          (data.hResidualDerivDifferentiableOnCell i)
          (data.hResidualSecondDerivBoundOnCell i)
          (data.hDerivLowerFromAnchor i) (data.hDerivUpperFromAnchor i)
      exact hBounds.2 eta heta
    hDerivLowerAbs := data.hDerivLowerAbs
    hDerivUpperAbs := data.hDerivUpperAbs
    hEnvelope := data.hEnvelope }

/-- Collapse residual-jet derivative-cell chunk data to the interval
finite-cover receiver. -/
def ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData.toResidualAnchorDerivativeIntervalFiniteCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData cert) :
    ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeIntervalFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Collapse interval-derivative single-anchor data to the derivative
single-cover receiver. -/
def ResidualAnchorDerivativeIntervalSingleCoverData.toResidualAnchorDerivativeSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeIntervalSingleCoverData cert) :
    ResidualAnchorDerivativeSingleCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchor := data.anchor
    hSlopeNonneg := data.hSlopeNonneg
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualDifferentiable := data.hResidualDifferentiable
    hResidualDerivBound :=
      cert.residual_deriv_bound_of_interval_bounds
        data.hResidualDerivLower data.hResidualDerivUpper
        data.hDerivLowerAbs data.hDerivUpperAbs
    hEnvelope := data.hEnvelope }

/-- Collapse interval-derivative chunk proof data to the derivative
single-cover receiver. -/
def ResidualAnchorDerivativeIntervalSingleCoverChunkProofData.toResidualAnchorDerivativeSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeIntervalSingleCoverChunkProofData cert) :
    ResidualAnchorDerivativeSingleCoverChunkProofData cert :=
  { envelope := data.envelope.toResidualAnchorDerivativeSingleCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Collapse second-derivative anchor data to the derivative single-cover
receiver. -/
def ResidualAnchorDerivativeSecondDerivativeSingleCoverData.toResidualAnchorDerivativeSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeSecondDerivativeSingleCoverData cert) :
    ResidualAnchorDerivativeSingleCoverData cert :=
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchor := data.anchor
    hSlopeNonneg := data.hSlopeNonneg
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualDifferentiable := data.hResidualDifferentiable
    hResidualDerivBound :=
      cert.residual_deriv_bound_of_deriv_anchor_envelope
        data.hDerivSlopeNonneg data.hAnchorIn data.hLeftMesh
        data.hRightMesh data.hAnchorDerivResidual
        data.hResidualDerivDifferentiable data.hResidualSecondDerivBound
        data.hDerivEnvelope
    hEnvelope := data.hEnvelope }

/-- Collapse second-derivative anchor chunk data to the derivative
single-cover receiver. -/
def ResidualAnchorDerivativeSecondDerivativeSingleCoverChunkProofData.toResidualAnchorDerivativeSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSecondDerivativeSingleCoverChunkProofData cert) :
    ResidualAnchorDerivativeSingleCoverChunkProofData cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeSingleCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

/-- Collapse raw/poly derivative interval data to the existing interval
derivative single-cover receiver. -/
def ResidualAnchorDerivativeRawPolyIntervalSingleCoverData.toResidualAnchorDerivativeIntervalSingleCoverData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeRawPolyIntervalSingleCoverData cert) :
    ResidualAnchorDerivativeIntervalSingleCoverData cert :=
  have hDeriv :=
    cert.residual_deriv_interval_bounds_of_raw_poly_deriv_bounds
      data.hRawDerivLower data.hRawDerivUpper
      data.hPolyDerivLower data.hPolyDerivUpper
      data.hResidualDerivEq data.hDerivLowerFromRawPoly
      data.hDerivUpperFromRawPoly
  { sampleRadius := data.sampleRadius
    slope := data.slope
    mesh := data.mesh
    anchor := data.anchor
    derivLower := data.derivLower
    derivUpper := data.derivUpper
    hSlopeNonneg := data.hSlopeNonneg
    hAnchorIn := data.hAnchorIn
    hLeftMesh := data.hLeftMesh
    hRightMesh := data.hRightMesh
    hAnchorResidual := data.hAnchorResidual
    hResidualDifferentiable := data.hResidualDifferentiable
    hResidualDerivLower := hDeriv.1
    hResidualDerivUpper := hDeriv.2
    hDerivLowerAbs := data.hDerivLowerAbs
    hDerivUpperAbs := data.hDerivUpperAbs
    hEnvelope := data.hEnvelope }

/-- Collapse raw/poly derivative interval chunk proof data to the existing
interval-derivative chunk receiver. -/
def ResidualAnchorDerivativeRawPolyIntervalSingleCoverChunkProofData.toResidualAnchorDerivativeIntervalSingleCoverChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeRawPolyIntervalSingleCoverChunkProofData cert) :
    ResidualAnchorDerivativeIntervalSingleCoverChunkProofData cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeIntervalSingleCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt
    hIntegralLower := data.hIntegralLower
    hIntegralUpper := data.hIntegralUpper }

theorem diff_bounds_of_value_bounds
    {k : Nat} {ell x L U lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real)) :
    (∀ eta ∈ Set.Ioc L U,
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) ∧
      (∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta <=
          (cert.remainder : Real)) := by
  constructor
  · intro eta heta
    have hRaw := hBounds.hRawLower eta heta
    have hPoly := hBounds.hPolyUpper eta heta
    nlinarith
  · intro eta heta
    have hRaw := hBounds.hRawUpper eta heta
    have hPoly := hBounds.hPolyLower eta heta
    nlinarith

theorem diff_bounds_of_residual_anchor_envelope_data
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (data : cert.ResidualAnchorEnvelopeData) :
    (∀ eta ∈ Set.Ioc L U,
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) ∧
      (∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta <=
          (cert.remainder : Real)) := by
  exact
    cert.diff_bounds_of_residual_anchor_envelope data.hSlopeNonneg
      data.hCover data.hResidualVariation data.hEnvelope

theorem Valid.of_abs_error_model_integral_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hProfileInt :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (hAbs :
      ∀ eta ∈ Set.Ioc L U,
        abs
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hModels := cert.lower_upper_model_bounds_of_abs_error hAbs
  exact
    Valid.of_model_integral_bounds cert hLU hRadiusNonneg hRemainderNonneg
      hLeft hRight hProfileInt hModels.1 hModels.2 hIntegralLower
      hIntegralUpper

theorem Valid.of_diff_bounds_model_integral_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hProfileInt :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (hDiffLower :
      ∀ eta ∈ Set.Ioc L U,
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta <=
          (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_abs_error_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight hProfileInt
      (cert.abs_error_of_diff_bounds hDiffLower hDiffUpper)
      hIntegralLower hIntegralUpper

/-- Validity from a finite residual-anchor envelope plus model integral
comparisons.  This is the intended landing surface for a derivative/Cauchy
Taylor-remainder generator: generated code supplies anchor residual checks,
local variation bounds, and the final scalar envelope comparison. -/
theorem Valid.of_residual_anchor_envelope_model_integral_bounds
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    {sampleRadius slope mesh : Real}
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hProfileInt :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc L U,
        ∃ anchor ∈ Set.Ioc L U,
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
        |cert.residual eta - cert.residual anchor| <= slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hAbsResidual :=
    cert.abs_error_of_residual_anchor_envelope hSlopeNonneg hCover
      hResidualVariation hEnvelope
  have hAbs :
      ∀ eta ∈ Set.Ioc L U,
        abs
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) <= (cert.remainder : Real) := by
    intro eta heta
    simpa [residual] using hAbsResidual eta heta
  exact
    Valid.of_abs_error_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight hProfileInt hAbs hIntegralLower
      hIntegralUpper

theorem Valid.of_value_bounds_model_integral_bounds
    {k : Nat} {ell x L U lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hProfileInt :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hDiff := cert.diff_bounds_of_value_bounds hBounds hDiffLower hDiffUpper
  exact
    Valid.of_diff_bounds_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight hProfileInt hDiff.1 hDiff.2
      hIntegralLower hIntegralUpper

theorem AbsCosChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : AbsCosChunkProofData cert) :
    cert.Valid := by
  exact
    Valid.of_value_bounds_model_integral_bounds cert data.hLU
      data.hRadiusNonneg data.hRemainderNonneg data.hLeft data.hRight
      data.hProfileInt data.bounds.toValueBounds data.hDiffLower
      data.hDiffUpper data.hIntegralLower data.hIntegralUpper

theorem ComponentChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ComponentChunkProofData cert) :
    cert.Valid := by
  exact
    Valid.of_value_bounds_model_integral_bounds cert data.hLU
      data.hRadiusNonneg data.hRemainderNonneg data.hLeft data.hRight
      data.hProfileInt data.bounds.toValueBounds data.hDiffLower
      data.hDiffUpper data.hIntegralLower data.hIntegralUpper

theorem ComponentValueChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ComponentValueChunkProofData cert) :
    cert.Valid := by
  exact
    Valid.of_value_bounds_model_integral_bounds cert data.hLU
      data.hRadiusNonneg data.hRemainderNonneg data.hLeft data.hRight
      data.hProfileInt data.bounds.toValueBounds data.hDiffLower
      data.hDiffUpper data.hIntegralLower data.hIntegralUpper

theorem ResidualAnchorChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorChunkProofData cert) :
    cert.Valid := by
  exact
    Valid.of_residual_anchor_envelope_model_integral_bounds cert data.hLU
      data.hRadiusNonneg data.hRemainderNonneg data.hLeft data.hRight
      data.hProfileInt data.envelope.hSlopeNonneg data.envelope.hCover
      data.envelope.hResidualVariation data.envelope.hEnvelope
      data.hIntegralLower data.hIntegralUpper

theorem ResidualAnchorFiniteCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorFiniteCoverChunkProofData cert) :
    cert.Valid := by
  exact data.toResidualAnchorChunkProofData.valid

theorem ResidualAnchorSingleCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorSingleCoverChunkProofData cert) :
    cert.Valid := by
  exact data.toResidualAnchorFiniteCoverChunkProofData.valid

theorem ResidualAnchorDerivativeSingleCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeSingleCoverChunkProofData cert) :
  cert.Valid := by
  exact data.toResidualAnchorSingleCoverChunkProofData.valid

theorem ResidualAnchorDerivativeFiniteCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeFiniteCoverChunkProofData cert) :
  cert.Valid := by
  exact data.toResidualAnchorDerivativeSingleCoverChunkProofData.valid

theorem ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeIntervalFiniteCoverChunkProofData cert) :
  cert.Valid := by
  exact data.toResidualAnchorDerivativeFiniteCoverChunkProofData.valid

/-- Exact-model-integral version of the active interval finite-cover chunk
proof data.

The ordinary chunk proof data asks a generator to emit two arithmetic
comparisons per refined subchunk:
`lower <= cert.lowerModelIntegral` and
`cert.upperModelIntegral <= upper`.  For the refined parent route those bounds
can instead be chosen definitionally as the model integrals themselves.  This
keeps the analytic residual/derivative obligations unchanged while moving the
subchunk integral comparisons out of the generated proof-data surface. -/
structure ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeIntervalFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)

/-- Exact-model-integral chunk data with the derivative slope computed from
the supplied derivative intervals. -/
structure ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)

/-- Exact-model-integral chunk data with auto-slope and a direct anchor
residual envelope. -/
structure ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope :
    ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)

/-- Exact-model-integral chunk data with direct anchor envelope and per-cell
derivative norm slopes. -/
structure ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope : ResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)

/-- Exact-model-integral chunk data specialized to the current one-cell
direct residual-derivative interval route. -/
structure ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope :
    ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)

/-- Exact-model-integral chunk data specialized to the current one-cell route,
with the envelope proved from a separate sampled residual radius. -/
structure ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope :
    ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)

/-- Exact-model-integral chunk data for the current sharp-anchor route.

The generated payload supplies the sharp raw-center-minus-coeff0 anchor bound
directly; Lean converts it to the sampled-envelope chunk receiver. -/
structure ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper) where
  envelope :
    ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData cert
  hLU : L <= U
  hRadiusNonneg : 0 <= (cert.radius : Real)
  hRemainderNonneg : 0 <= (cert.remainder : Real)
  hLeft : (cert.center : Real) - (cert.radius : Real) <= L
  hRight : U <= (cert.center : Real) + (cert.radius : Real)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)

/-- Expand auto-slope exact-integral chunk data to the already checked
exact-integral interval finite-cover receiver. -/
def ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralChunkProofData.toResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralChunkProofData
        cert) :
    ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData
      cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeIntervalFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt }

/-- Expand direct-envelope auto-slope exact-integral chunk data to the already
checked exact-integral interval finite-cover receiver. -/
def ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralChunkProofData.toResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralChunkProofData
        cert) :
    ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData
      cert :=
  { envelope :=
      ResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData.toResidualAnchorDerivativeIntervalFiniteCoverData
        (data.envelope.toResidualAnchorDerivativeIntervalAutoSlopeFiniteCoverData)
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt }

/-- Expand one-cell direct residual-derivative interval exact-integral data to
the existing cell-slope exact-integral receiver. -/
def ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData.toResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData
        cert) :
    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeCellSlopeDirectEnvelopeFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt }

/-- Collapse sampled-envelope exact-integral chunk data to the one-cell direct
envelope exact-integral receiver. -/
def ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData.toResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData
        cert) :
    ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData
      cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt }

/-- Collapse sharp-anchor exact-integral chunk data to the sampled-envelope
chunk receiver. -/
def ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData.toResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData
        cert) :
    ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData
      cert :=
  { envelope :=
      data.envelope.toResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData
    hLU := data.hLU
    hRadiusNonneg := data.hRadiusNonneg
    hRemainderNonneg := data.hRemainderNonneg
    hLeft := data.hLeft
    hRight := data.hRight
    hProfileInt := data.hProfileInt }

/-- Convert exact-model-integral chunk data directly to a raw-Omega window
certificate with subchunk bounds equal to the model integrals. -/
theorem ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData.windowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData
        cert) :
    WindowPartBoundsCert k ell x L U
      cert.lowerModelIntegral cert.upperModelIntegral := by
  let finiteEnv :=
    data.envelope.toResidualAnchorDerivativeFiniteCoverData
  let singleDerivEnv :=
    finiteEnv.toResidualAnchorDerivativeSingleCoverData
  let singleEnv :=
    singleDerivEnv.toResidualAnchorSingleCoverData
  let coverEnv :=
    singleEnv.toResidualAnchorFiniteCoverData
  let env : ResidualAnchorEnvelopeData cert :=
    coverEnv.toResidualAnchorEnvelopeData
  have hAbsResidual :=
    cert.abs_error_of_residual_anchor_envelope env.hSlopeNonneg env.hCover
      env.hResidualVariation env.hEnvelope
  have hAbs :
      ∀ eta ∈ Set.Ioc L U,
        abs
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) <= (cert.remainder : Real) := by
    intro eta heta
    simpa [residual] using hAbsResidual eta heta
  have hModels := cert.lower_upper_model_bounds_of_abs_error hAbs
  have hbounds :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart_bounds_of_comparison_integrals
      k ell x L U cert.lowerModelIntegral cert.upperModelIntegral
      cert.lowerModel cert.upperModel data.hProfileInt
      cert.integrableOn_lowerModel_Ioc cert.integrableOn_upperModel_Ioc
      hModels.1 hModels.2
      (by
        simp [setIntegral_Ioc_lowerModel_of_le cert data.hLU])
      (by
        simp [setIntegral_Ioc_upperModel_of_le cert data.hLU])
  exact
    { hWindowLower := by
        simpa [windowPart] using hbounds.1
      hWindowUpper := by
        simpa [windowPart] using hbounds.2 }

/-- Convert auto-slope exact-integral chunk data directly to a raw-Omega
window certificate. -/
theorem ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralChunkProofData.windowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralChunkProofData
        cert) :
    WindowPartBoundsCert k ell x L U
      cert.lowerModelIntegral cert.upperModelIntegral :=
  ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData.windowPartBoundsCert
    (data.toResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData)

/-- Convert direct-envelope auto-slope exact-integral chunk data directly to a
raw-Omega window certificate. -/
theorem ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralChunkProofData
        cert) :
    WindowPartBoundsCert k ell x L U
      cert.lowerModelIntegral cert.upperModelIntegral :=
  ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData.windowPartBoundsCert
    (data.toResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData)

/-- Convert cell-slope direct-envelope exact-integral chunk data directly to a
raw-Omega window certificate. -/
theorem ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
        cert) :
    WindowPartBoundsCert k ell x L U
      cert.lowerModelIntegral cert.upperModelIntegral := by
  let finiteEnv :=
    data.envelope.toResidualAnchorDerivativeFiniteCoverData
  let singleDerivEnv :=
    finiteEnv.toResidualAnchorDerivativeSingleCoverData
  let singleEnv :=
    singleDerivEnv.toResidualAnchorSingleCoverData
  let coverEnv :=
    singleEnv.toResidualAnchorFiniteCoverData
  let env : ResidualAnchorEnvelopeData cert :=
    coverEnv.toResidualAnchorEnvelopeData
  have hAbsResidual :=
    cert.abs_error_of_residual_anchor_envelope env.hSlopeNonneg env.hCover
      env.hResidualVariation env.hEnvelope
  have hAbs :
      ∀ eta ∈ Set.Ioc L U,
        abs
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x eta -
            cert.polynomial eta) <= (cert.remainder : Real) := by
    intro eta heta
    simpa [residual] using hAbsResidual eta heta
  have hModels := cert.lower_upper_model_bounds_of_abs_error hAbs
  have hbounds :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart_bounds_of_comparison_integrals
      k ell x L U cert.lowerModelIntegral cert.upperModelIntegral
      cert.lowerModel cert.upperModel data.hProfileInt
      cert.integrableOn_lowerModel_Ioc cert.integrableOn_upperModel_Ioc
      hModels.1 hModels.2
      (by
        simp [setIntegral_Ioc_lowerModel_of_le cert data.hLU])
      (by
        simp [setIntegral_Ioc_upperModel_of_le cert data.hLU])
  exact
    { hWindowLower := by
        simpa [windowPart] using hbounds.1
      hWindowUpper := by
        simpa [windowPart] using hbounds.2 }

/-- Convert one-cell direct residual-derivative interval exact-integral chunk
data directly to a raw-Omega window certificate. -/
theorem ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData
        cert) :
    WindowPartBoundsCert k ell x L U
      cert.lowerModelIntegral cert.upperModelIntegral :=
  ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    (data.toResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData)

/-- Convert one-cell sampled-envelope exact-integral chunk data directly to a
raw-Omega window certificate. -/
theorem ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData
        cert) :
    WindowPartBoundsCert k ell x L U
      cert.lowerModelIntegral cert.upperModelIntegral :=
  ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    (data.toResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData)

/-- Convert sharp-anchor one-cell exact-integral chunk data directly to a
raw-Omega window certificate. -/
theorem ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData
        cert) :
    WindowPartBoundsCert k ell x L U
      cert.lowerModelIntegral cert.upperModelIntegral :=
  ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData.windowPartBoundsCert
    (data.toResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData)

theorem ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData cert) :
  cert.Valid := by
  exact data.toResidualAnchorDerivativeIntervalFiniteCoverChunkProofData.valid

theorem ResidualAnchorDerivativeSecondDerivativeSingleCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeSecondDerivativeSingleCoverChunkProofData cert) :
    cert.Valid := by
  exact data.toResidualAnchorDerivativeSingleCoverChunkProofData.valid

theorem ResidualAnchorDerivativeIntervalSingleCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data : ResidualAnchorDerivativeIntervalSingleCoverChunkProofData cert) :
    cert.Valid := by
  exact data.toResidualAnchorDerivativeSingleCoverChunkProofData.valid

theorem ResidualAnchorDerivativeRawPolyIntervalSingleCoverChunkProofData.valid
    {k : Nat} {ell x L U lower upper : Real}
    {cert : RawOmegaATaylorModelCertificate k ell x L U lower upper}
    (data :
      ResidualAnchorDerivativeRawPolyIntervalSingleCoverChunkProofData cert) :
    cert.Valid := by
  exact data.toResidualAnchorDerivativeIntervalSingleCoverChunkProofData.valid

theorem primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left
    (n : CoeffIndex23) (L U : Real) (hL : 0 <= L) :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        11 primaryK11Ell ((n.1 : Real) / 4))
      (Set.Ioc L U) := by
  exact
    (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi
      n).mono_set (by
        intro eta heta
        exact lt_of_le_of_lt hL heta.1)

theorem controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left
    (n : CoeffIndex23) (L U : Real) (hL : 0 <= L) :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        9 controlK9Ell ((n.1 : Real) / 4))
      (Set.Ioc L U) := by
  exact
    (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi
      n).mono_set (by
        intro eta heta
        exact lt_of_le_of_lt hL heta.1)

theorem Valid.primaryK11_of_model_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hLowerModel :
      ∀ eta ∈ Set.Ioc L U,
        cert.lowerModel eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hUpperModel :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          cert.upperModel eta)
    (hIntegralLower : lower <= ∫ eta in Set.Ioc L U, cert.lowerModel eta)
    (hIntegralUpper : (∫ eta in Set.Ioc L U, cert.upperModel eta) <= upper) :
    cert.Valid := by
  exact
    Valid.of_model_bounds cert hRadiusNonneg hRemainderNonneg hLeft hRight
      (primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hLowerModel hUpperModel hIntegralLower hIntegralUpper

theorem Valid.primaryK11_of_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hLowerModel :
      ∀ eta ∈ Set.Ioc L U,
        cert.lowerModel eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hUpperModel :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          cert.upperModel eta)
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_model_integral_bounds cert hLU hRadiusNonneg hRemainderNonneg
      hLeft hRight
      (primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hLowerModel hUpperModel hIntegralLower hIntegralUpper

theorem Valid.primaryK11_of_abs_error_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hAbs :
      ∀ eta ∈ Set.Ioc L U,
        abs
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              11 primaryK11Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta) <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_abs_error_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight
      (primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hAbs hIntegralLower hIntegralUpper

theorem Valid.primaryK11_of_diff_bounds_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hDiffLower :
      ∀ eta ∈ Set.Ioc L U,
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              11 primaryK11Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              11 primaryK11Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta <=
          (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_diff_bounds_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight
      (primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_of_residual_anchor_envelope_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4) L U lower upper)
    {sampleRadius slope mesh : Real}
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc L U,
        ∃ anchor ∈ Set.Ioc L U,
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
        |cert.residual eta - cert.residual anchor| <=
          slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_residual_anchor_envelope_model_integral_bounds cert hLU
      hRadiusNonneg hRemainderNonneg hLeft hRight
      (primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hSlopeNonneg hCover hResidualVariation hEnvelope hIntegralLower
      hIntegralUpper

theorem Valid.primaryK11_of_value_bounds_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_value_bounds_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight
      (primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hBounds hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_of_model_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hLowerModel :
      ∀ eta ∈ Set.Ioc L U,
        cert.lowerModel eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hUpperModel :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          cert.upperModel eta)
    (hIntegralLower : lower <= ∫ eta in Set.Ioc L U, cert.lowerModel eta)
    (hIntegralUpper : (∫ eta in Set.Ioc L U, cert.upperModel eta) <= upper) :
    cert.Valid := by
  exact
    Valid.of_model_bounds cert hRadiusNonneg hRemainderNonneg hLeft hRight
      (controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hLowerModel hUpperModel hIntegralLower hIntegralUpper

theorem Valid.controlK9_of_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hLowerModel :
      ∀ eta ∈ Set.Ioc L U,
        cert.lowerModel eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hUpperModel :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          cert.upperModel eta)
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_model_integral_bounds cert hLU hRadiusNonneg hRemainderNonneg
      hLeft hRight
      (controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hLowerModel hUpperModel hIntegralLower hIntegralUpper

theorem Valid.controlK9_of_abs_error_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hAbs :
      ∀ eta ∈ Set.Ioc L U,
        abs
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              9 controlK9Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta) <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_abs_error_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight
      (controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hAbs hIntegralLower hIntegralUpper

theorem Valid.controlK9_of_diff_bounds_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hDiffLower :
      ∀ eta ∈ Set.Ioc L U,
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              9 controlK9Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc L U,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              9 controlK9Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta <=
          (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_diff_bounds_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight
      (controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_of_residual_anchor_envelope_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4) L U lower upper)
    {sampleRadius slope mesh : Real}
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc L U,
        ∃ anchor ∈ Set.Ioc L U,
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc L U, ∀ anchor ∈ Set.Ioc L U,
        |cert.residual eta - cert.residual anchor| <=
          slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_residual_anchor_envelope_model_integral_bounds cert hLU
      hRadiusNonneg hRemainderNonneg hLeft hRight
      (controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hSlopeNonneg hCover hResidualVariation hEnvelope hIntegralLower
      hIntegralUpper

theorem Valid.controlK9_of_value_bounds_model_integral_bounds
    (n : CoeffIndex23) {L U lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4) L U lower upper)
    (hL : 0 <= L)
    (hLU : L <= U)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft : (cert.center : Real) - (cert.radius : Real) <= L)
    (hRight : U <= (cert.center : Real) + (cert.radius : Real))
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.of_value_bounds_model_integral_bounds cert hLU hRadiusNonneg
      hRemainderNonneg hLeft hRight
      (controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left n L U hL)
      hBounds hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem rawOmegaAFiniteChunk_left_nonneg (i : Nat) :
    0 <= ((0 : Real) + (10 : Real) * (i : Real)) := by
  have hi : (0 : Real) <= (i : Real) := by
    exact_mod_cast Nat.zero_le i
  nlinarith

theorem rawOmegaAFiniteChunk_left_le_right (i : Nat) :
    ((0 : Real) + (10 : Real) * (i : Real)) <=
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) := by
  have hi : (i : Real) <= ((i + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ i
  nlinarith

theorem rawOmegaATailChunk_left_nonneg (i : Nat) :
    0 <= rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real) := by
  have hcut : 0 <= rawOmegaAFiniteTailCutoff := by
    norm_num [rawOmegaAFiniteTailCutoff]
  have hi : (0 : Real) <= (i : Real) := by
    exact_mod_cast Nat.zero_le i
  nlinarith

theorem rawOmegaATailChunk_left_le_right (i : Nat) :
    rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real) <=
      rawOmegaAFiniteTailCutoff + (10 : Real) *
        ((i + 1 : Nat) : Real) := by
  have hi : (i : Real) <= ((i + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ i
  nlinarith

theorem Valid.primaryK11_finiteChunk_of_value_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_of_value_bounds_model_integral_bounds n cert
      (rawOmegaAFiniteChunk_left_nonneg i)
      (rawOmegaAFiniteChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_tailChunk_of_value_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_of_value_bounds_model_integral_bounds n cert
      (rawOmegaATailChunk_left_nonneg i)
      (rawOmegaATailChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_finiteChunk_of_value_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_of_value_bounds_model_integral_bounds n cert
      (rawOmegaAFiniteChunk_left_nonneg i)
      (rawOmegaAFiniteChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_tailChunk_of_value_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hBounds : cert.ValueBounds rawLower rawUpper polyLower polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_of_value_bounds_model_integral_bounds n cert
      (rawOmegaATailChunk_left_nonneg i)
      (rawOmegaATailChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRawLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        rawLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hRawUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_and_polynomial_term_bounds cert hRawLower hRawUpper
      hTerms hPolyLower hPolyUpper
  exact
    Valid.primaryK11_finiteChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRawLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        rawLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hRawUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_and_polynomial_term_bounds cert hRawLower hRawUpper
      hTerms hPolyLower hPolyUpper
  exact
    Valid.primaryK11_tailChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRawLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        rawLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hRawUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_and_polynomial_term_bounds cert hRawLower hRawUpper
      hTerms hPolyLower hPolyUpper
  exact
    Valid.controlK9_finiteChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRawLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        rawLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hRawUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_and_polynomial_term_bounds cert hRawLower hRawUpper
      hTerms hPolyLower hPolyUpper
  exact
    Valid.controlK9_tailChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_finiteChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRaw :
      RawIntegrandComponentBounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_component_and_polynomial_term_bounds cert hRaw
      hTerms hPolyLower hPolyUpper
  exact
    Valid.primaryK11_finiteChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_tailChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRaw :
      RawIntegrandComponentBounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_component_and_polynomial_term_bounds cert hRaw
      hTerms hPolyLower hPolyUpper
  exact
    Valid.primaryK11_tailChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_finiteChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRaw :
      RawIntegrandComponentBounds
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_component_and_polynomial_term_bounds cert hRaw
      hTerms hPolyLower hPolyUpper
  exact
    Valid.controlK9_finiteChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_tailChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hRaw :
      RawIntegrandComponentBounds
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hBounds :
      cert.ValueBounds rawLower rawUpper polyLower polyUpper :=
    ValueBounds.of_raw_component_and_polynomial_term_bounds cert hRaw
      hTerms hPolyLower hPolyUpper
  exact
    Valid.controlK9_tailChunk_of_value_bounds_model_integral_bounds n i
      cert hRadiusNonneg hRemainderNonneg hLeft hRight hBounds hDiffLower
      hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper cosAbs : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm
            11 primaryK11Ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        (centeredBSplineImagTransformRealClosedForm
            11 primaryK11Ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        cosLower <= Real.cos (eta * ((n.1 : Real) / 4)))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Real.cos (eta * ((n.1 : Real) / 4)) <= cosUpper)
    (hScaleNonneg : 0 <= primaryK11Ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower :
      rawLower <= -(primaryK11Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper :
      primaryK11Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs <= rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hRaw :
      RawIntegrandComponentBounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper :=
    RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
      hCosUpperAbs hRawLower hRawUpper
  exact
    Valid.primaryK11_finiteChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight hRaw hTerms
      hPolyLower hPolyUpper hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper cosAbs : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm
            11 primaryK11Ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        (centeredBSplineImagTransformRealClosedForm
            11 primaryK11Ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        cosLower <= Real.cos (eta * ((n.1 : Real) / 4)))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Real.cos (eta * ((n.1 : Real) / 4)) <= cosUpper)
    (hScaleNonneg : 0 <= primaryK11Ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower :
      rawLower <= -(primaryK11Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper :
      primaryK11Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs <= rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hRaw :
      RawIntegrandComponentBounds
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper :=
    RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
      hCosUpperAbs hRawLower hRawUpper
  exact
    Valid.primaryK11_tailChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight hRaw hTerms
      hPolyLower hPolyUpper hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper cosAbs : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm
            9 controlK9Ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        (centeredBSplineImagTransformRealClosedForm
            9 controlK9Ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        cosLower <= Real.cos (eta * ((n.1 : Real) / 4)))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Real.cos (eta * ((n.1 : Real) / 4)) <= cosUpper)
    (hScaleNonneg : 0 <= controlK9Ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower :
      rawLower <= -(controlK9Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper :
      controlK9Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs <= rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hRaw :
      RawIntegrandComponentBounds
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper :=
    RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
      hCosUpperAbs hRawLower hRawUpper
  exact
    Valid.controlK9_finiteChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight hRaw hTerms
      hPolyLower hPolyUpper hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.controlK9_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper rawLower rawUpper polyLower
      polyUpper omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower
      cosUpper cosAbs : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {termLower termUpper : Fin (cert.degree + 1) -> Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hOmegaLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        omegaLower <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta)
    (hOmegaUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
          omegaUpper)
    (hShapeSqLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        shapeSqLower <=
          (centeredBSplineImagTransformRealClosedForm
            9 controlK9Ell eta) ^ 2)
    (hShapeSqUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        (centeredBSplineImagTransformRealClosedForm
            9 controlK9Ell eta) ^ 2 <=
          shapeSqUpper)
    (hCosLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        cosLower <= Real.cos (eta * ((n.1 : Real) / 4)))
    (hCosUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Real.cos (eta * ((n.1 : Real) / 4)) <= cosUpper)
    (hScaleNonneg : 0 <= controlK9Ell / Real.pi)
    (hOmegaLowerNonneg : 0 <= omegaLower)
    (hShapeSqLowerNonneg : 0 <= shapeSqLower)
    (hCosLowerAbs : -cosAbs <= cosLower)
    (hCosUpperAbs : cosUpper <= cosAbs)
    (hRawLower :
      rawLower <= -(controlK9Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs))
    (hRawUpper :
      controlK9Ell / Real.pi * omegaUpper * shapeSqUpper * cosAbs <= rawUpper)
    (hTerms : cert.PolynomialTermBounds termLower termUpper)
    (hPolyLower : polyLower <= ∑ j : Fin (cert.degree + 1), termLower j)
    (hPolyUpper : (∑ j : Fin (cert.degree + 1), termUpper j) <= polyUpper)
    (hDiffLower : -(cert.remainder : Real) <= rawLower - polyUpper)
    (hDiffUpper : rawUpper - polyLower <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  have hRaw :
      RawIntegrandComponentBounds
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        omegaLower omegaUpper shapeSqLower shapeSqUpper cosLower cosUpper
        rawLower rawUpper :=
    RawIntegrandComponentBounds.of_nonneg_abs_cos_product_bounds
      hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper hCosLower hCosUpper
      hScaleNonneg hOmegaLowerNonneg hShapeSqLowerNonneg hCosLowerAbs
      hCosUpperAbs hRawLower hRawUpper
  exact
    Valid.controlK9_tailChunk_of_raw_component_and_polynomial_term_bounds_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight hRaw hTerms
      hPolyLower hPolyUpper hDiffLower hDiffUpper hIntegralLower hIntegralUpper

theorem Valid.primaryK11_finiteChunk_of_diff_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hDiffLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              11 primaryK11Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              11 primaryK11Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta <=
          (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_of_diff_bounds_model_integral_bounds n cert
      (rawOmegaAFiniteChunk_left_nonneg i)
      (rawOmegaAFiniteChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hDiffLower hDiffUpper
      hIntegralLower hIntegralUpper

theorem Valid.primaryK11_finiteChunk_of_residual_anchor_envelope_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {sampleRadius slope mesh : Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        ∃ anchor ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        ∀ anchor ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
          |cert.residual eta - cert.residual anchor| <=
            slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_of_residual_anchor_envelope_model_integral_bounds n cert
      (rawOmegaAFiniteChunk_left_nonneg i)
      (rawOmegaAFiniteChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hSlopeNonneg hCover
      hResidualVariation hEnvelope hIntegralLower hIntegralUpper

theorem Valid.primaryK11_finiteChunk_of_residual_anchor_envelope_data_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    (data : cert.ResidualAnchorEnvelopeData)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_finiteChunk_of_residual_anchor_envelope_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight
      data.hSlopeNonneg data.hCover data.hResidualVariation data.hEnvelope
      hIntegralLower hIntegralUpper

theorem Valid.primaryK11_tailChunk_of_residual_anchor_envelope_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {sampleRadius slope mesh : Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        ∃ anchor ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        ∀ anchor ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
          |cert.residual eta - cert.residual anchor| <=
            slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_of_residual_anchor_envelope_model_integral_bounds n cert
      (rawOmegaATailChunk_left_nonneg i)
      (rawOmegaATailChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hSlopeNonneg hCover
      hResidualVariation hEnvelope hIntegralLower hIntegralUpper

theorem Valid.primaryK11_tailChunk_of_residual_anchor_envelope_data_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    (data : cert.ResidualAnchorEnvelopeData)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_tailChunk_of_residual_anchor_envelope_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight
      data.hSlopeNonneg data.hCover data.hResidualVariation data.hEnvelope
      hIntegralLower hIntegralUpper

theorem Valid.controlK9_finiteChunk_of_residual_anchor_envelope_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    {sampleRadius slope mesh : Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        ∃ anchor ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        ∀ anchor ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
          |cert.residual eta - cert.residual anchor| <=
            slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_of_residual_anchor_envelope_model_integral_bounds n cert
      (rawOmegaAFiniteChunk_left_nonneg i)
      (rawOmegaAFiniteChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hSlopeNonneg hCover
      hResidualVariation hEnvelope hIntegralLower hIntegralUpper

theorem Valid.controlK9_finiteChunk_of_residual_anchor_envelope_data_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    (data : cert.ResidualAnchorEnvelopeData)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_finiteChunk_of_residual_anchor_envelope_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight
      data.hSlopeNonneg data.hCover data.hResidualVariation data.hEnvelope
      hIntegralLower hIntegralUpper

theorem Valid.controlK9_tailChunk_of_residual_anchor_envelope_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    {sampleRadius slope mesh : Real}
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hSlopeNonneg : 0 <= slope)
    (hCover :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        ∃ anchor ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
          |eta - anchor| <= mesh ∧
            |cert.residual anchor| <= sampleRadius)
    (hResidualVariation :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        ∀ anchor ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
          |cert.residual eta - cert.residual anchor| <=
            slope * |eta - anchor|)
    (hEnvelope : sampleRadius + slope * mesh <= (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_of_residual_anchor_envelope_model_integral_bounds n cert
      (rawOmegaATailChunk_left_nonneg i)
      (rawOmegaATailChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hSlopeNonneg hCover
      hResidualVariation hEnvelope hIntegralLower hIntegralUpper

theorem Valid.controlK9_tailChunk_of_residual_anchor_envelope_data_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    (data : cert.ResidualAnchorEnvelopeData)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_tailChunk_of_residual_anchor_envelope_model_integral_bounds
      n i cert hRadiusNonneg hRemainderNonneg hLeft hRight
      data.hSlopeNonneg data.hCover data.hResidualVariation data.hEnvelope
      hIntegralLower hIntegralUpper

theorem Valid.primaryK11_tailChunk_of_diff_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        11 primaryK11Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hDiffLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              11 primaryK11Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              11 primaryK11Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta <=
          (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.primaryK11_of_diff_bounds_model_integral_bounds n cert
      (rawOmegaATailChunk_left_nonneg i)
      (rawOmegaATailChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hDiffLower hDiffUpper
      hIntegralLower hIntegralUpper

theorem Valid.controlK9_finiteChunk_of_diff_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        ((0 : Real) + (10 : Real) * (i : Real))
        ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        ((0 : Real) + (10 : Real) * (i : Real)))
    (hRight :
      ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)) <=
        (cert.center : Real) + (cert.radius : Real))
    (hDiffLower :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              9 controlK9Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc
          ((0 : Real) + (10 : Real) * (i : Real))
          ((0 : Real) + (10 : Real) * ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              9 controlK9Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta <=
          (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_of_diff_bounds_model_integral_bounds n cert
      (rawOmegaAFiniteChunk_left_nonneg i)
      (rawOmegaAFiniteChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hDiffLower hDiffUpper
      hIntegralLower hIntegralUpper

theorem Valid.controlK9_tailChunk_of_diff_bounds_model_integral_bounds
    (n : CoeffIndex23) (i : Nat) {lower upper : Real}
    (cert :
      RawOmegaATaylorModelCertificate
        9 controlK9Ell ((n.1 : Real) / 4)
        (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
        (rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real))
        lower upper)
    (hRadiusNonneg : 0 <= (cert.radius : Real))
    (hRemainderNonneg : 0 <= (cert.remainder : Real))
    (hLeft :
      (cert.center : Real) - (cert.radius : Real) <=
        rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
    (hRight :
      rawOmegaAFiniteTailCutoff + (10 : Real) *
          ((i + 1 : Nat) : Real) <=
        (cert.center : Real) + (cert.radius : Real))
    (hDiffLower :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        -(cert.remainder : Real) <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              9 controlK9Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta)
    (hDiffUpper :
      ∀ eta ∈ Set.Ioc
          (rawOmegaAFiniteTailCutoff + (10 : Real) * (i : Real))
          (rawOmegaAFiniteTailCutoff + (10 : Real) *
            ((i + 1 : Nat) : Real)),
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              9 controlK9Ell ((n.1 : Real) / 4) eta -
            cert.polynomial eta <=
          (cert.remainder : Real))
    (hIntegralLower : lower <= cert.lowerModelIntegral)
    (hIntegralUpper : cert.upperModelIntegral <= upper) :
    cert.Valid := by
  exact
    Valid.controlK9_of_diff_bounds_model_integral_bounds n cert
      (rawOmegaATailChunk_left_nonneg i)
      (rawOmegaATailChunk_left_le_right i)
      hRadiusNonneg hRemainderNonneg hLeft hRight hDiffLower hDiffUpper
      hIntegralLower hIntegralUpper

end RawOmegaATaylorModelCertificate

/-- The primary raw-Omega scale factor used by the abs-cos component checker is
nonnegative.  Generated payloads use this as a shared proof term. -/
theorem primaryK11Ell_div_pi_nonneg : 0 <= primaryK11Ell / Real.pi := by
  have hEll : 0 <= primaryK11Ell := by
    norm_num [primaryK11Ell, primaryK11EllRat]
  exact div_nonneg hEll (le_of_lt Real.pi_pos)

theorem primaryK11Ell_div_pi_scaleLower :
    (9 : Real) / 100 <= primaryK11Ell / Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hmul : ((9 : Real) / 100) * Real.pi <= primaryK11Ell := by
    norm_num [primaryK11Ell, primaryK11EllRat]
    nlinarith [Real.pi_lt_d2]
  rwa [le_div_iff₀ hpi_pos]

theorem primaryK11Ell_div_pi_scaleUpper :
    primaryK11Ell / Real.pi <= (1 : Real) / 10 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hmul : primaryK11Ell <= ((1 : Real) / 10) * Real.pi := by
    norm_num [primaryK11Ell, primaryK11EllRat]
    nlinarith [Real.pi_gt_three]
  rwa [div_le_iff₀ hpi_pos]

/-- The control raw-Omega scale factor used by the abs-cos component checker is
nonnegative.  Generated payloads use this as a shared proof term. -/
theorem controlK9Ell_div_pi_nonneg : 0 <= controlK9Ell / Real.pi := by
  have hEll : 0 <= controlK9Ell := by
    norm_num [controlK9Ell, controlK9EllRat]
  exact div_nonneg hEll (le_of_lt Real.pi_pos)

theorem controlK9Ell_div_pi_scaleLower :
    (9 : Real) / 100 <= controlK9Ell / Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hmul : ((9 : Real) / 100) * Real.pi <= controlK9Ell := by
    norm_num [controlK9Ell, controlK9EllRat]
    nlinarith [Real.pi_lt_d2]
  rwa [le_div_iff₀ hpi_pos]

theorem controlK9Ell_div_pi_scaleUpper :
    controlK9Ell / Real.pi <= (1 : Real) / 10 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hmul : controlK9Ell <= ((1 : Real) / 10) * Real.pi := by
    norm_num [controlK9Ell, controlK9EllRat]
    nlinarith [Real.pi_gt_three]
  rwa [div_le_iff₀ hpi_pos]

theorem q3_pi_gt_d29 :
    (3.14159265358979323846264338327 : Real) < Real.pi := by
  pi_lower_bound [
    565685424949238019520675489683879231427868750150779229270671895196293 / 400000000000000000000000000000000000000000000000000000000000000000000,
    18477590650225735122563663787935765736448332517272849722301954625610701 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    19615705608064608982523644722684780739478674617866721900058321770906131 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    4975923633360984431224184765547399607877374343649285309168064828924451 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    19975909124103447854295432095182013888864072294092235886856341473712199 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    9996988186962042201157656496661721968500610812577296246441237879263817 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    799939761471315632737317192957106579480485175041774264195266938401187 / 400000000000000000000000000000000000000000000000000000000000000000000,
    9999811752826011426569904377285677161739172509443350919401576950808211 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 94123808476569768397485997602008940247327556246917785260265123533 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 23530965961801419485796569479619034641542204699215522749410897763 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 735342794452099429455653085807209340251626745996520510020255857 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 367671410744276342596463060715258994221555386154676339272143279 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 367671414123833061691941805709898478975144392932493724218908023 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 287243292944314254178774615690069106050659198498077948332589 / 31250000000000000000000000000000000000000000000000000000000000000000,
    2 - 5744865862186633461027229457997312919028589382910854308325769 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 5744865863011720555627164478218210841634294945785805840708701 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1436216465804498082322990194790393337809683960939172175497479 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 89763529113586879261079463101804062518620995726102035878121 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 44881764556894158270026755584853985346859088190066364921653 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 897635291138386758597970796920622471581907978024230887261 / 400000000000000000000000000000000000000000000000000000000000000000000,
    2 - 701277571201963013201038869954976249924465300681164840053 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 280511028480795041085052967157827413064540590595271123821 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 350638785600996875045265402493621029695807737565391319519 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 43829848200124705433437837610446650442316199664862170797 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 5478731025015591180829094148144871030262499867522544263 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 5478731025015591931241435259854836526874483760299979189 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 342420689063474507427782533611396296803939124614706343 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 21401293066467156897442546317438350028710481224572161 / 625000000000000000000000000000000000000000000000000000000000000000000,
    2 - 8560517226586862777297632323647948237747586087474571 / 1000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2675161633308394619336808054005031343504529624886843 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1337580816654197309847316271110646611701177851129019 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1337580816654197309892044332137679346691397480620213 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 334395204163549327475806586848609382609784837151687 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 20899700260221832967281591425134798068376351572527 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 20899700260221832967292511361908975982192562796333 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 522492506505545824182381033652563011516165407887 / 1000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 65311563313193228022799762006721583063312905437 / 500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 163278908282983070057000738016898461798152407021 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 81639454141491535028500535633461043916559971439 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 4081972707074576751425028864485699858546545671 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 5102465883843220939281286731486077217782728057 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1275616470960805234820321723551453829108153637 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 63780823548040261741016086686071873013688577 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 79726029435050327176270108516495835504073501 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 4982876839690645448516881784763895878957137 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 622859604961330681064610223173077802368159 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 155714901240332670266152555798118876685697 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 155714901240332670266152555799331233209111 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 38928725310083167566538138949908580584991 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 9732181327520791891634534737481880913917 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 4866090663760395945817267368741532427917 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 304130666485024746613579210546355026291 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 304130666485024746613579210546357338677 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 76032666621256186653394802636589479193 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 19008166655314046663348700659147378831 / 10000000000000000000000000000000000000000000000000000000000000000000000
  ]

theorem q3_pi_lt_d29 :
    Real.pi < (3.14159265358979323846264338328 : Real) := by
  pi_upper_bound [
    3535533905932737622004221810524245196424179688442370182941699344976831 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    18477590650225735122563663787935765736448332517272849722301954625610699 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    19615705608064608982523644722684780739478674617866721900058321770906129 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    19903694533443937724896739062189598431509497374597141236672259315697803 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    9987954562051723927147716047591006944432036147046117943428170736856099 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    19993976373924084402315312993323443937001221625154592492882475758527633 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    9999247018391445409216464911963832243506064688022178302440836730014837 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 376494347977146860191245428645676521654981113298161196846098383579 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 18824761695313953679497199520401788049465511249383557052053024707 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 4706193192360283897159313895923806928308440939843104549882179553 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2941371177808397717822612343228837361006506983986082040081023429 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 735342821488552685192926121430517988443110772309352678544286559 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 45958926765479132711492725713737309871893049116561715527363503 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 91917853742180561337207877020822113936210943519384943466428481 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 22979463448746533844108917831989251676114357531643417233303077 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2872432931505860277813582239109105420817147472892902920354351 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1436216465804498082322990194790393337809683960939172175497481 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 71810823290869503408863570481443250014896796580881628702497 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 89763529113788316540053511169707970693718176380132729843307 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 11220441139229834482474634961507780894773849725302886090763 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 224408822784628164224332438385592399975828896217972748817 / 400000000000000000000000000000000000000000000000000000000000000000000,
    2 - 701277571201987602712632417894568532661351476488177809553 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2191492410006230469032908765585131435598798359783695747 / 62500000000000000000000000000000000000000000000000000000000000000000,
    2 - 17531939280049882173375135044178660176926479865944868319 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 21914924100062364723316376592579484121049999470090177053 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 547873102501559193124143525985483652687448376029997919 / 1000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1369682756253898029711130134445585187215756498458825373 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 342420689063474510359080741079013600459367699593154577 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 85605172265868627772976323236479482377475860874745711 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 10700646533233578477347232216020125374018118499547373 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2675161633308394619694632542221293223402355702258039 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 668790408327098654946022166068839673345698740310107 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 41799400520443665934475823356076172826223104643961 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 8359880104088733186912636570053919227350540629011 / 1000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 4179940052044366593458502272381795196438512559267 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 653115633131932280227976292065703764395206759859 / 1250000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1306231266263864560455995240134431661266258108741 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 326557816565966140114001476033796923596304814043 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 81639454141491535028500535633461043916559971441 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 5102465883843220939281286080607124823183182089 / 2500000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2551232941921610469640643365743038608891364029 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 637808235480402617410160861775726914554076819 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 159452058870100654352540216715179682534221443 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 39863014717525163588135054258247917752036751 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 398630147175251635881350542781111670316571 / 200000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2491438419845322724258440892692311209472637 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1245719209922661362129220446384951013485577 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 311429802480665340532305111598662466418223 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 77857450620166335133076277899817161169983 / 10000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 3892872531008316756653813894992752365567 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 2433045331880197972908633684370766213959 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 243304533188019797290863368437084021033 / 2000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 152065333242512373306789605273178669339 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 38016333310628093326697401318294739597 / 5000000000000000000000000000000000000000000000000000000000000000000000,
    2 - 1188010415957127916459293791196711177 / 625000000000000000000000000000000000000000000000000000000000000000000
  ]

theorem rawOmegaEll_div_pi_tightScaleLower :
    (0.095492965855137201461330258023 : Real) <= (3 : Real) / 10 / Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hscale_nonneg :
      0 <= (0.095492965855137201461330258023 : Real) := by
    norm_num
  have hmul_pi :
      (0.095492965855137201461330258023 : Real) * Real.pi <=
        (0.095492965855137201461330258023 : Real) *
          (3.14159265358979323846264338328 : Real) :=
    mul_le_mul_of_nonneg_left (le_of_lt q3_pi_lt_d29) hscale_nonneg
  have hmul_bound :
      (0.095492965855137201461330258023 : Real) *
          (3.14159265358979323846264338328 : Real) <=
        (3 : Real) / 10 := by
    norm_num
  have hmul :
      (0.095492965855137201461330258023 : Real) * Real.pi <=
        (3 : Real) / 10 :=
    le_trans hmul_pi hmul_bound
  rwa [le_div_iff₀ hpi_pos]

theorem rawOmegaEll_div_pi_tightScaleUpper :
    (3 : Real) / 10 / Real.pi <=
      (0.095492965855137201461330258024 : Real) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hscale_nonneg :
      0 <= (0.095492965855137201461330258024 : Real) := by
    norm_num
  have hmul_pi :
      (0.095492965855137201461330258024 : Real) *
          (3.14159265358979323846264338327 : Real) <=
        (0.095492965855137201461330258024 : Real) * Real.pi :=
    mul_le_mul_of_nonneg_left (le_of_lt q3_pi_gt_d29) hscale_nonneg
  have hmul_bound :
      (3 : Real) / 10 <=
        (0.095492965855137201461330258024 : Real) *
          (3.14159265358979323846264338327 : Real) := by
    norm_num
  have hmul :
      (3 : Real) / 10 <=
        (0.095492965855137201461330258024 : Real) * Real.pi :=
    le_trans hmul_bound hmul_pi
  rwa [div_le_iff₀ hpi_pos]

theorem primaryK11Ell_div_pi_tightScaleLower :
    (0.095492965855137201461330258023 : Real) <=
      primaryK11Ell / Real.pi := by
  rw [show primaryK11Ell = (3 : Real) / 10 by
    norm_num [primaryK11Ell, primaryK11EllRat]]
  exact rawOmegaEll_div_pi_tightScaleLower

theorem primaryK11Ell_div_pi_tightScaleUpper :
    primaryK11Ell / Real.pi <=
      (0.095492965855137201461330258024 : Real) := by
  rw [show primaryK11Ell = (3 : Real) / 10 by
    norm_num [primaryK11Ell, primaryK11EllRat]]
  exact rawOmegaEll_div_pi_tightScaleUpper

theorem controlK9Ell_div_pi_tightScaleLower :
    (0.095492965855137201461330258023 : Real) <=
      controlK9Ell / Real.pi := by
  rw [show controlK9Ell = (3 : Real) / 10 by
    norm_num [controlK9Ell, controlK9EllRat]]
  exact rawOmegaEll_div_pi_tightScaleLower

theorem controlK9Ell_div_pi_tightScaleUpper :
    controlK9Ell / Real.pi <=
      (0.095492965855137201461330258024 : Real) := by
  rw [show controlK9Ell = (3 : Real) / 10 by
    norm_num [controlK9Ell, controlK9EllRat]]
  exact rawOmegaEll_div_pi_tightScaleUpper

/-- Coarse compact-window Omega envelope for the first finite chunk `(0,10]`.
The bound is deliberately wide: it is a proof-data seed that removes the
last unseeded Omega component cells before sharper product/Taylor data are
generated. -/
theorem step22OmegaArchWeight_abs_le_twoHundred_on_Ioc_zero_ten
    {eta : Real} (heta : eta ∈ Set.Ioc (0 : Real) (10 : Real)) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| <=
      (200 : Real) := by
  let xi : Real := eta / (2 * Real.pi)
  let z : Complex :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.aStarTailArg xi
  have htwoPi_pos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have heta_pos : 0 < eta := by simpa using heta.1
  have heta_le_ten : eta <= (10 : Real) := by simpa using heta.2
  have hxi_nonneg : 0 <= xi := by
    rw [show xi = eta / (2 * Real.pi) by rfl]
    exact div_nonneg (le_of_lt heta_pos) (le_of_lt htwoPi_pos)
  have hz_re : z.re = (1 / 4 : Real) := by
    simp [z, Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.aStarTailArg]
  have hnorm_ge_quarter : (1 / 4 : Real) <= ‖z‖ := by
    have hre_le : |z.re| <= ‖z‖ := by
      simpa using (RCLike.abs_re_le_norm z)
    simpa [hz_re] using hre_le
  have hnorm_pos : 0 < ‖z‖ := by
    nlinarith
  have hnorm_sq_ge : (1 / 16 : Real) <= ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - (1 / 4 : Real))]
  have hnorm_le_six : ‖z‖ <= (6 : Real) := by
    have htri :
        ‖(1 / 4 : Complex) +
            Complex.I * (Real.pi : Complex) * (xi : Complex)‖ <=
          ‖(1 / 4 : Complex)‖ +
            ‖Complex.I * (Real.pi : Complex) * (xi : Complex)‖ :=
      norm_add_le _ _
    have hnorm_i :
        ‖Complex.I * (Real.pi : Complex) * (xi : Complex)‖ =
          Real.pi * xi := by
      calc
        ‖Complex.I * (Real.pi : Complex) * (xi : Complex)‖ =
            ‖Complex.I‖ * ‖(Real.pi : Complex)‖ *
              ‖(xi : Complex)‖ := by
              simp [mul_assoc]
        _ = Real.pi * xi := by
              simp [abs_of_pos Real.pi_pos, abs_of_nonneg hxi_nonneg]
    have hpi_xi : Real.pi * xi = eta / 2 := by
      rw [show xi = eta / (2 * Real.pi) by rfl]
      field_simp [Real.pi_ne_zero]
    have hnorm_quarter : ‖(1 / 4 : Complex)‖ = (1 / 4 : Real) := by
      norm_num
    calc
      ‖z‖ =
          ‖(1 / 4 : Complex) +
            Complex.I * (Real.pi : Complex) * (xi : Complex)‖ := by
            simp [z, Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.aStarTailArg,
              mul_assoc]
      _ <= ‖(1 / 4 : Complex)‖ +
          ‖Complex.I * (Real.pi : Complex) * (xi : Complex)‖ := htri
      _ = (1 / 4 : Real) + eta / 2 := by
            rw [hnorm_quarter, hnorm_i, hpi_xi]
      _ <= (6 : Real) := by
            nlinarith
  have hden2_pos : 0 < 2 * ‖z‖ ^ 2 := by positivity
  have hden2_ge : (1 / 8 : Real) <= 2 * ‖z‖ ^ 2 := by
    nlinarith
  have hterm2_abs :
      |z.re / (2 * ‖z‖ ^ 2)| =
        (1 / 4 : Real) / (2 * ‖z‖ ^ 2) := by
    rw [abs_div, abs_of_pos hden2_pos, hz_re]
    norm_num
  have hterm2 : |z.re / (2 * ‖z‖ ^ 2)| <= (2 : Real) := by
    rw [hterm2_abs]
    have h := div_le_div_of_nonneg_left
      (show (0 : Real) <= 1 / 4 by norm_num)
      (show (0 : Real) < 1 / 8 by norm_num) hden2_ge
    have hcalc : (1 / 4 : Real) / (1 / 8 : Real) = 2 := by
      norm_num
    exact h.trans_eq hcalc
  have hden3_pos : 0 < 4 * ‖z‖ ^ 2 := by positivity
  have hden3_ge : (1 / 4 : Real) <= 4 * ‖z‖ ^ 2 := by
    nlinarith
  have hterm3 : 1 / (4 * ‖z‖ ^ 2) <= (4 : Real) := by
    have h := one_div_le_one_div_of_le
      (show (0 : Real) < 1 / 4 by norm_num) hden3_ge
    have hcalc : (1 : Real) / (1 / 4 : Real) = 4 := by
      norm_num
    exact h.trans_eq hcalc
  have hfour_le_exp_two : (4 : Real) <= Real.exp (2 : Real) := by
    have h := Real.exp_one_gt_d9
    have hexp2 :
        Real.exp (2 : Real) = Real.exp (1 : Real) * Real.exp (1 : Real) := by
      rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [h, hexp2]
  have hlog_pi_le_two : Real.log Real.pi <= (2 : Real) := by
    have hpi_le_exp_two : Real.pi <= Real.exp (2 : Real) := by
      exact le_trans (le_of_lt Real.pi_lt_four) hfour_le_exp_two
    exact (Real.log_le_iff_le_exp Real.pi_pos).2 hpi_le_exp_two
  have hlog_pi_nonneg : 0 <= Real.log Real.pi := by
    exact Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlog_norm_ge_neg_two : -(2 : Real) <= Real.log ‖z‖ := by
    have hexp_neg_two_le_norm : Real.exp (-(2 : Real)) <= ‖z‖ := by
      have hexp_neg_two_le_quarter :
          Real.exp (-(2 : Real)) <= (1 / 4 : Real) := by
        have hone_div := one_div_le_one_div_of_le
          (show (0 : Real) < 4 by norm_num) hfour_le_exp_two
        have hneg :
            Real.exp (-(2 : Real)) = (Real.exp (2 : Real))⁻¹ := by
          rw [Real.exp_neg]
        rw [hneg]
        simpa [one_div] using hone_div
      exact le_trans hexp_neg_two_le_quarter hnorm_ge_quarter
    exact (Real.le_log_iff_exp_le hnorm_pos).2 hexp_neg_two_le_norm
  have hlog_norm_le_six : Real.log ‖z‖ <= (6 : Real) := by
    exact (Real.log_le_self hnorm_pos.le).trans hnorm_le_six
  have hlog_abs :
      |Real.log Real.pi - Real.log ‖z‖| <= (8 : Real) := by
    apply abs_sub_le_iff.2
    constructor <;> linarith
  have hinside_nonneg :
      0 <= |Real.log Real.pi - Real.log ‖z‖| +
        |z.re / (2 * ‖z‖ ^ 2)| + 1 / (4 * ‖z‖ ^ 2) := by
    positivity
  have hinside_le :
      |Real.log Real.pi - Real.log ‖z‖| +
          |z.re / (2 * ‖z‖ ^ 2)| + 1 / (4 * ‖z‖ ^ 2) <=
        (14 : Real) := by
    nlinarith
  have henv :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.aStarStieltjesLogEnvelope
          xi <=
        (98 : Real) := by
    have htwo_pi_le_seven : 2 * Real.pi <= (7 : Real) := by
      nlinarith [Real.pi_lt_d2]
    calc
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.aStarStieltjesLogEnvelope
          xi =
          2 * Real.pi *
            (|Real.log Real.pi - Real.log ‖z‖| +
              |z.re / (2 * ‖z‖ ^ 2)| + 1 / (4 * ‖z‖ ^ 2)) := by
            simp [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.aStarStieltjesLogEnvelope,
              z]
      _ <= 7 *
          (|Real.log Real.pi - Real.log ‖z‖| +
            |z.re / (2 * ‖z‖ ^ 2)| + 1 / (4 * ‖z‖ ^ 2)) := by
            exact mul_le_mul_of_nonneg_right htwo_pi_le_seven hinside_nonneg
      _ <= 7 * (14 : Real) := by
            exact mul_le_mul_of_nonneg_left hinside_le (by norm_num)
      _ = (98 : Real) := by
            norm_num
  have hA : |Q3.a_star xi| <= (98 : Real) :=
    le_trans
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.a_star_abs_le_stieltjesLogEnvelope xi)
      henv
  have hinv_le_one : |(2 * Real.pi)⁻¹| <= 1 := by
    rw [abs_of_pos (inv_pos.mpr htwoPi_pos)]
    calc
      (2 * Real.pi)⁻¹ = (1 : Real) / (2 * Real.pi) := by
        ring
      _ <= (1 : Real) / 1 := by
        exact one_div_le_one_div_of_le zero_lt_one
          (by nlinarith [Real.pi_gt_three])
      _ = 1 := by
        norm_num
  calc
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| =
        |(2 * Real.pi)⁻¹| * |Q3.a_star xi| := by
          rw [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_eq_neg_inv_twoPi_aStar eta]
          simp [xi, abs_mul, abs_neg]
    _ <= 1 * (98 : Real) := by
          exact mul_le_mul hinv_le_one hA (abs_nonneg _) (by norm_num)
    _ <= (200 : Real) := by
          norm_num

theorem step22OmegaArchWeight_neg_twoHundred_le_on_Ioc_zero_ten
    {eta : Real} (heta : eta ∈ Set.Ioc (0 : Real) (10 : Real)) :
    -(200 : Real) <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta := by
  exact (abs_le.mp
    (step22OmegaArchWeight_abs_le_twoHundred_on_Ioc_zero_ten heta)).1

theorem step22OmegaArchWeight_le_twoHundred_on_Ioc_zero_ten
    {eta : Real} (heta : eta ∈ Set.Ioc (0 : Real) (10 : Real)) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
      (200 : Real) := by
  exact (abs_le.mp
    (step22OmegaArchWeight_abs_le_twoHundred_on_Ioc_zero_ten heta)).2

/-- A reusable Step33 chunk-scale Omega envelope after the first finite
window chunk.  The proof is the same Stieltjes/log envelope used by the
tail backend, with the threshold lowered to `10`; this is enough for every
`(10 * i, 10 * (i+1)]` chunk with `i > 0`. -/
theorem step22OmegaArchWeight_abs_le_ten_logOmega_after_ten :
    ∀ eta ∈ Set.Ioi (10 : Real),
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| <=
        10 * Real.log (3 * eta) := by
  intro eta heta
  let xi : Real := eta / (2 * Real.pi)
  have htwoPi_pos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have heta_gt : (10 : Real) < eta := by
    simpa [Set.mem_Ioi] using heta
  have heta_pos : 0 < eta := by linarith
  have hxi_gt_one : (1 : Real) < xi := by
    rw [show xi = eta / (2 * Real.pi) by rfl]
    rw [lt_div_iff₀ htwoPi_pos]
    nlinarith [heta_gt, Real.pi_lt_d2]
  have hxi_pos : 0 < xi := lt_trans zero_lt_one hxi_gt_one
  have hxi_le_eta : xi <= eta := by
    rw [show xi = eta / (2 * Real.pi) by rfl]
    rw [div_le_iff₀ htwoPi_pos]
    nlinarith [heta_pos, Real.pi_gt_three]
  have hA :
      |Q3.a_star xi| <= 10 * Real.log (3 * xi) := by
    exact le_trans
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.a_star_abs_le_stieltjesLogEnvelope xi)
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.aStarStieltjesLogEnvelope_le_ten_log_after_one
        hxi_gt_one)
  have hlog_mono : Real.log (3 * xi) <= Real.log (3 * eta) := by
    have hthree_xi_pos : 0 < 3 * xi := by positivity
    have hthree_le : 3 * xi <= 3 * eta := by nlinarith
    exact Real.log_le_log hthree_xi_pos hthree_le
  have hinv_le_one : |(2 * Real.pi)⁻¹| <= 1 := by
    rw [abs_of_pos (inv_pos.mpr htwoPi_pos)]
    calc
      (2 * Real.pi)⁻¹ = (1 : Real) / (2 * Real.pi) := by
        ring
      _ <= (1 : Real) / 1 := by
        exact one_div_le_one_div_of_le zero_lt_one
          (by nlinarith [Real.pi_gt_three])
      _ = 1 := by norm_num
  calc
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| =
        |(2 * Real.pi)⁻¹| * |Q3.a_star xi| := by
          rw [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_eq_neg_inv_twoPi_aStar eta]
          simp [xi, abs_mul, abs_neg]
    _ <= 1 * (10 * Real.log (3 * xi)) := by
          exact mul_le_mul hinv_le_one hA (abs_nonneg _) (by norm_num)
    _ = 10 * Real.log (3 * xi) := by ring
    _ <= 10 * Real.log (3 * eta) := by
          exact mul_le_mul_of_nonneg_left hlog_mono (by norm_num)

theorem step22OmegaArchWeight_abs_le_ten_logOmega_right_on_Ioc
    {L U eta : Real} (hL : (10 : Real) <= L)
    (heta : eta ∈ Set.Ioc L U) :
    |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| <=
      10 * Real.log (3 * U) := by
  have heta_gt_ten : (10 : Real) < eta :=
    lt_of_le_of_lt hL heta.1
  have hAbs :=
    step22OmegaArchWeight_abs_le_ten_logOmega_after_ten eta
      (by simpa [Set.mem_Ioi] using heta_gt_ten)
  have hlog_mono : Real.log (3 * eta) <= Real.log (3 * U) := by
    have heta_pos : 0 < eta := by linarith
    have hthree_eta_pos : 0 < 3 * eta := by positivity
    have hthree_le : 3 * eta <= 3 * U := by nlinarith [heta.2]
    exact Real.log_le_log hthree_eta_pos hthree_le
  exact le_trans hAbs (mul_le_mul_of_nonneg_left hlog_mono (by norm_num))

theorem step22OmegaArchWeight_neg_ten_logOmega_right_le_on_Ioc
    {L U eta : Real} (hL : (10 : Real) <= L)
    (heta : eta ∈ Set.Ioc L U) :
    -(10 * Real.log (3 * U)) <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta := by
  exact (abs_le.mp
    (step22OmegaArchWeight_abs_le_ten_logOmega_right_on_Ioc hL heta)).1

theorem step22OmegaArchWeight_le_ten_logOmega_right_on_Ioc
    {L U eta : Real} (hL : (10 : Real) <= L)
    (heta : eta ∈ Set.Ioc L U) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta <=
      10 * Real.log (3 * U) := by
  exact (abs_le.mp
    (step22OmegaArchWeight_abs_le_ten_logOmega_right_on_Ioc hL heta)).2

/-- Coarse global upper bound for the square of the centered B-spline
imaginary-axis transform.  The generator uses this as the shared `shapeSqUpper`
candidate before any sharper per-chunk shape enclosure is available. -/
def centeredBSplineImagTransformSqGlobalMajorant (k : Nat) : Real :=
  |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2

theorem centeredBSplineImagTransformSqGlobalMajorant_nonneg (k : Nat) :
    0 <= centeredBSplineImagTransformSqGlobalMajorant k := by
  unfold centeredBSplineImagTransformSqGlobalMajorant
  exact sq_nonneg _

theorem centeredBSplineImagTransformRealClosedForm_sq_nonneg
    (k : Nat) (ell eta : Real) :
    0 <= (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 := by
  exact sq_nonneg _

theorem centeredBSplineImagTransformRealClosedForm_sq_le_globalMajorant
    (k : Nat) (ell eta : Real) :
    (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 <=
      centeredBSplineImagTransformSqGlobalMajorant k := by
  let D : Real := (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹
  let s : Real := realSinc (ell * eta / (2 * bsplineScale k))
  have hs_abs : |s| <= (1 : Real) := realSinc_abs_le_one _
  have hs_pow_abs : |s ^ (k + 1)| <= (1 : Real) := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg s) hs_abs
  have hE_abs :
      |centeredBSplineImagTransformRealClosedForm k ell eta| <= |D| := by
    unfold centeredBSplineImagTransformRealClosedForm
    change |D * s ^ (k + 1)| <= |D|
    calc
      |D * s ^ (k + 1)| = |D| * |s ^ (k + 1)| := by
          rw [abs_mul]
      _ <= |D| * 1 := by
          exact mul_le_mul_of_nonneg_left hs_pow_abs (abs_nonneg D)
      _ = |D| := by ring
  have hsq :
      |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 <= |D| ^ 2 := by
    exact pow_le_pow_left₀ (abs_nonneg _) hE_abs 2
  calc
    (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 =
        |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 := by
          rw [sq_abs]
    _ <= |D| ^ 2 := hsq
    _ = centeredBSplineImagTransformSqGlobalMajorant k := by
          simp [centeredBSplineImagTransformSqGlobalMajorant, D]

/-- Universal lower bound for the raw-Omega cosine factor.  Generated Taylor
payloads use this coarse envelope until sharper per-chunk cosine bounds are
available. -/
theorem cos_neg_one_le_mul (eta x : Real) :
    (-1 : Real) <= Real.cos (eta * x) := by
  exact Real.neg_one_le_cos (eta * x)

/-- Universal upper bound for the raw-Omega cosine factor.  Generated Taylor
payloads use this coarse envelope until sharper per-chunk cosine bounds are
available. -/
theorem cos_mul_le_one (eta x : Real) :
    Real.cos (eta * x) <= (1 : Real) := by
  exact Real.cos_le_one (eta * x)

/-- Convert one valid raw-Omega Taylor/model certificate into the existing
chunk window-bound certificate. -/
theorem rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
    (k : Nat) (ell x L U lower upper : Real)
    (cert : RawOmegaATaylorModelCertificate k ell x L U lower upper)
    (hcert : cert.Valid) :
    WindowPartBoundsCert k ell x L U lower upper := by
  have hbounds :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailWindowPart_bounds_of_comparison_integrals
      k ell x L U lower upper cert.lowerModel cert.upperModel
      hcert.hProfileInt hcert.hLowerInt hcert.hUpperInt
      hcert.hLowerModel hcert.hUpperModel hcert.hIntegralLower
      hcert.hIntegralUpper
  exact
    { hWindowLower := by
        simpa [windowPart] using hbounds.1
      hWindowUpper := by
        simpa [windowPart] using hbounds.2 }

/-- A parent raw-Omega window certified by adjacent refined subchunk window
certificates.  This is the non-uniform version of the refined-subchunk
receiver: generators can provide arbitrary rational breakpoints `pts 0, ...,
pts n`, as long as they are adjacent and cover the parent interval. -/
structure RefinedWindowPartBoundsCert
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  subLower : Nat -> Real
  subUpper : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  subCert : ∀ i : Nat, i < n ->
    WindowPartBoundsCert
      k ell x (pts i) (pts (i + 1)) (subLower i) (subUpper i)
  lower_le_sum : lower <= ∑ i ∈ Finset.range n, subLower i
  sum_le_upper : (∑ i ∈ Finset.range n, subUpper i) <= upper

/-- Build the refined parent certificate in the exact-sum case.  This is the
shape consumed by `RefinedPayloadFin`: the parent lower/upper values are the
two sums of refined subchunk bounds, so the parent fold comparisons are
reflexive. -/
def RefinedWindowPartBoundsCert.of_refinedSubchunkSums
    (k : Nat) (ell x L U : Real)
    (pts subLower subUpper : Nat -> Real) (N : Nat)
    (first_eq : pts 0 = L) (last_eq : pts N = U)
    (mono : ∀ i : Nat, i < N -> pts i <= pts (i + 1))
    (hProfileInt :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (subCert : ∀ i : Nat, i < N ->
      WindowPartBoundsCert
        k ell x (pts i) (pts (i + 1)) (subLower i) (subUpper i)) :
    RefinedWindowPartBoundsCert k ell x L U
      (∑ i ∈ Finset.range N, subLower i)
      (∑ i ∈ Finset.range N, subUpper i) :=
  { n := N
    pts := pts
    subLower := subLower
    subUpper := subUpper
    first_eq := first_eq
    last_eq := last_eq
    mono := mono
    hProfileInt := hProfileInt
    subCert := subCert
    lower_le_sum := le_rfl
    sum_le_upper := le_rfl }

/-- The first point is below the `N`-th point when adjacent breakpoints are
monotone up to `N`. -/
theorem pts_zero_le_of_mono_range
    (pts : Nat -> Real) :
    ∀ N : Nat, (∀ i : Nat, i < N -> pts i <= pts (i + 1)) ->
      pts 0 <= pts N
  | 0, _ => le_rfl
  | N + 1, hmono =>
      le_trans
        (pts_zero_le_of_mono_range pts N
          (fun i hi => hmono i (Nat.lt_trans hi (Nat.lt_succ_self N))))
        (hmono N (Nat.lt_succ_self N))

/-- Fold non-uniform adjacent raw-Omega subchunk certificates into one window
certificate over the first and last breakpoints. -/
theorem windowPartBoundsCert_of_refinedSubchunks_range
    (k : Nat) (ell x : Real)
    (pts subLower subUpper : Nat -> Real) (N : Nat)
    (mono : ∀ i : Nat, i < N -> pts i <= pts (i + 1))
    (hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc (pts 0) (pts N)))
    (subCert : ∀ i : Nat, i < N ->
      WindowPartBoundsCert
        k ell x (pts i) (pts (i + 1)) (subLower i) (subUpper i)) :
    WindowPartBoundsCert k ell x (pts 0) (pts N)
      (∑ i ∈ Finset.range N, subLower i)
      (∑ i ∈ Finset.range N, subUpper i) := by
  induction N with
  | zero =>
      simpa using windowPartBoundsCert_empty k ell x (pts 0)
  | succ N ih =>
      have hRight : pts N <= pts (N + 1) := by
        exact mono N (Nat.lt_succ_self N)
      have hprefixHint :
          IntegrableOn
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
              k ell x)
            (Set.Ioc (pts 0) (pts N)) := by
        exact hint.mono_set (by
          intro y hy
          exact ⟨hy.1, le_trans hy.2 hRight⟩)
      have hprefix :
          WindowPartBoundsCert k ell x (pts 0) (pts N)
            (∑ i ∈ Finset.range N, subLower i)
            (∑ i ∈ Finset.range N, subUpper i) := by
        exact ih
          (fun i hi => mono i (Nat.lt_trans hi (Nat.lt_succ_self N)))
          hprefixHint
          (fun i hi => subCert i (Nat.lt_trans hi (Nat.lt_succ_self N)))
      have hlast :
          WindowPartBoundsCert
            k ell x (pts N) (pts (N + 1))
            (subLower N) (subUpper N) := by
        exact subCert N (Nat.lt_succ_self N)
      have hLeft : pts 0 <= pts N := by
        exact pts_zero_le_of_mono_range pts N
          (fun i hi => mono i (Nat.lt_trans hi (Nat.lt_succ_self N)))
      exact
        windowPartBoundsCert_glue_adjacent
          k ell x (pts 0) (pts (N + 1)) (pts N)
          (∑ i ∈ Finset.range (N + 1), subLower i)
          (∑ i ∈ Finset.range (N + 1), subUpper i)
          (∑ i ∈ Finset.range N, subLower i)
          (∑ i ∈ Finset.range N, subUpper i)
          (subLower N) (subUpper N)
          hint hLeft hRight hprefix hlast
          (by rw [Finset.sum_range_succ])
          (by rw [Finset.sum_range_succ])

/-- Fold non-uniform adjacent refined subchunks and rewrite the endpoints to a
named parent interval.  This is the exact-sum parent route: a generator can set
the parent lower/upper bounds to these two sums and avoid separate parent
fold-slack comparisons. -/
theorem WindowPartBoundsCert.of_refinedSubchunkSums
    (k : Nat) (ell x L U : Real)
    (pts subLower subUpper : Nat -> Real) (N : Nat)
    (first_eq : pts 0 = L) (last_eq : pts N = U)
    (mono : ∀ i : Nat, i < N -> pts i <= pts (i + 1))
    (hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L U))
    (subCert : ∀ i : Nat, i < N ->
      WindowPartBoundsCert
        k ell x (pts i) (pts (i + 1)) (subLower i) (subUpper i)) :
    WindowPartBoundsCert k ell x L U
      (∑ i ∈ Finset.range N, subLower i)
      (∑ i ∈ Finset.range N, subUpper i) := by
  have hint' :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc (pts 0) (pts N)) := by
    simpa [first_eq, last_eq] using hint
  have folded :=
    windowPartBoundsCert_of_refinedSubchunks_range
      k ell x pts subLower subUpper N mono hint' subCert
  simpa [first_eq, last_eq] using folded

/-- Fold a refined parent certificate into one raw-Omega window certificate. -/
theorem WindowPartBoundsCert.of_refinedSubchunks
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RefinedWindowPartBoundsCert k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper := by
  have hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc (cert.pts 0) (cert.pts cert.n)) := by
    simpa [cert.first_eq, cert.last_eq] using cert.hProfileInt
  have folded :=
    windowPartBoundsCert_of_refinedSubchunks_range
      k ell x cert.pts cert.subLower cert.subUpper cert.n cert.mono
      hint cert.subCert
  have bounded :
      WindowPartBoundsCert k ell x (cert.pts 0) (cert.pts cert.n)
        lower upper :=
    { hWindowLower := le_trans cert.lower_le_sum folded.hWindowLower
      hWindowUpper := le_trans folded.hWindowUpper cert.sum_le_upper }
  simpa [cert.first_eq, cert.last_eq] using bounded

/-- Alias for generators that produce refined Taylor/model subchunks before
folding them into the parent window certificate. -/
theorem WindowPartBoundsCert.of_refinedTaylorSubchunks
    {k : Nat} {ell x L U lower upper : Real}
    (cert : RefinedWindowPartBoundsCert k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks cert

/-- Generator-facing refined parent data whose subchunk certificates are proved
by residual-anchor envelopes.  This connects the derivative/residual-anchor
route to the Louise route-A parent-refined payload shape: the generator supplies
one residual-anchor proof packet per refined subchunk, and Lean folds those
subchunks into a parent `RefinedWindowPartBoundsCert`. -/
structure ResidualAnchorRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  subLower : Nat -> Real
  subUpper : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) (subLower i) (subUpper i)
  proofData : ∀ i : Nat, ∀ hi : i < n,
    RawOmegaATaylorModelCertificate.ResidualAnchorChunkProofData
      (cert i hi)
  lower_le_sum : lower <= ∑ i ∈ Finset.range n, subLower i
  sum_le_upper : (∑ i ∈ Finset.range n, subUpper i) <= upper

/-- Convert residual-anchor refined subchunk proof data into the parent
refined-window certificate consumed by `RefinedPayloadFin`. -/
def ResidualAnchorRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorRefinedWindowProofData k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := proofData.subLower
    subUpper := proofData.subUpper
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
          k ell x (proofData.pts i) (proofData.pts (i + 1))
          (proofData.subLower i) (proofData.subUpper i)
          (proofData.cert i hi)
          (RawOmegaATaylorModelCertificate.ResidualAnchorChunkProofData.valid
            (proofData.proofData i hi))
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Refined parent data whose subchunk bounds are exact Taylor/model integrals.

This is the compressed generator-facing variant of
`ResidualAnchorRefinedWindowProofData` for the active interval finite-cover
route.  The generator still proves the residual-anchor and residual-derivative
facts on every refined subchunk, but it no longer emits separate
`hIntegralLower`/`hIntegralUpper` comparisons for every subchunk: the subchunk
lower and upper bounds are definitionally `cert.lowerModelIntegral` and
`cert.upperModelIntegral`.  Only the parent/row sum comparisons remain. -/
structure ResidualAnchorDerivativeIntervalExactIntegralRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat,
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) 0 0
  proofData : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeIntervalFiniteCoverExactIntegralChunkProofData
      (cert i)
  lower_le_sum :
    lower <= ∑ i ∈ Finset.range n, (cert i).lowerModelIntegral
  sum_le_upper :
    (∑ i ∈ Finset.range n, (cert i).upperModelIntegral) <= upper

/-- Convert exact-integral refined parent data to the existing refined-window
certificate. -/
def ResidualAnchorDerivativeIntervalExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeIntervalExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := fun i => (proofData.cert i).lowerModelIntegral
    subUpper := fun i => (proofData.cert i).upperModelIntegral
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        (proofData.proofData i hi).windowPartBoundsCert
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Refined parent data whose subchunk bounds are exact Taylor/model integrals
and whose per-subchunk derivative slope is computed from derivative-cell
interval endpoints. -/
structure ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat,
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) 0 0
  proofData : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralChunkProofData
      (cert i)
  lower_le_sum :
    lower <= ∑ i ∈ Finset.range n, (cert i).lowerModelIntegral
  sum_le_upper :
    (∑ i ∈ Finset.range n, (cert i).upperModelIntegral) <= upper

/-- Convert auto-slope exact-integral refined parent data to the existing
refined-window certificate. -/
def ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := fun i => (proofData.cert i).lowerModelIntegral
    subUpper := fun i => (proofData.cert i).upperModelIntegral
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        (proofData.proofData i hi).windowPartBoundsCert
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Refined parent data whose subchunk bounds are exact Taylor/model integrals,
whose derivative slope is computed from derivative-cell endpoints, and whose
anchor residual is folded directly into the envelope comparison. -/
structure ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat,
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) 0 0
  proofData : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralChunkProofData
      (cert i)
  lower_le_sum :
    lower <= ∑ i ∈ Finset.range n, (cert i).lowerModelIntegral
  sum_le_upper :
    (∑ i ∈ Finset.range n, (cert i).upperModelIntegral) <= upper

/-- Convert direct-envelope auto-slope exact-integral refined parent data to
the existing refined-window certificate. -/
def ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := fun i => (proofData.cert i).lowerModelIntegral
    subUpper := fun i => (proofData.cert i).upperModelIntegral
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        (proofData.proofData i hi).windowPartBoundsCert
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Refined parent data whose subchunk bounds are exact Taylor/model integrals,
whose derivative control is supplied by per-cell norm slopes, and whose anchor
residual is folded directly into the envelope comparison. -/
structure ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat,
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) 0 0
  proofData : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData
      (cert i)
  lower_le_sum :
    lower <= ∑ i ∈ Finset.range n, (cert i).lowerModelIntegral
  sum_le_upper :
    (∑ i ∈ Finset.range n, (cert i).upperModelIntegral) <= upper

/-- Convert cell-slope direct-envelope exact-integral refined parent data to
the existing refined-window certificate. -/
def ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := fun i => (proofData.cert i).lowerModelIntegral
    subUpper := fun i => (proofData.cert i).upperModelIntegral
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        (proofData.proofData i hi).windowPartBoundsCert
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Refined parent data specialized to the current one-cell direct
residual-derivative interval route.

This is a generator-facing facade for route A: subchunks use scalar
one-cell residual-derivative interval proof data, then Lean expands each
subchunk to the existing cell-slope exact-integral certificate and folds the
refined subchunks into the parent window bound. -/
structure ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat,
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) 0 0
  proofData : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralChunkProofData
      (cert i)
  lower_le_sum :
    lower <= ∑ i ∈ Finset.range n, (cert i).lowerModelIntegral
  sum_le_upper :
    (∑ i ∈ Finset.range n, (cert i).upperModelIntegral) <= upper

/-- Refined parent data specialized to the current one-cell sampled-envelope
route.

This is the proof-producing route-A facade: each subchunk supplies a sampled
anchor residual bound, a scalar envelope comparison, and direct
residual-derivative interval data; Lean folds those into the existing
parent-window certificate. -/
structure ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat,
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) 0 0
  proofData : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralChunkProofData
      (cert i)
  lower_le_sum :
    lower <= ∑ i ∈ Finset.range n, (cert i).lowerModelIntegral
  sum_le_upper :
    (∑ i ∈ Finset.range n, (cert i).upperModelIntegral) <= upper

/-- Refined parent data for the current sharp-anchor one-cell route.

Each subchunk supplies the raw-center-minus-coeff0 anchor bound directly, then
Lean lowers it through the sampled-envelope route-A fold. -/
structure ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData
    (k : Nat) (ell x L U lower upper : Real) where
  n : Nat
  pts : Nat -> Real
  first_eq : pts 0 = L
  last_eq : pts n = U
  mono : ∀ i : Nat, i < n -> pts i <= pts (i + 1)
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L U)
  cert : ∀ i : Nat,
    RawOmegaATaylorModelCertificate
      k ell x (pts i) (pts (i + 1)) 0 0
  proofData : ∀ i : Nat, i < n ->
    RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData
      (cert i)
  lower_le_sum :
    lower <= ∑ i ∈ Finset.range n, (cert i).lowerModelIntegral
  sum_le_upper :
    (∑ i ∈ Finset.range n, (cert i).upperModelIntegral) <= upper

/-- Convert one-cell direct residual-derivative interval refined parent data
to the existing refined-window certificate. -/
def ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := fun i => (proofData.cert i).lowerModelIntegral
    subUpper := fun i => (proofData.cert i).upperModelIntegral
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        (proofData.proofData i hi).windowPartBoundsCert
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Convert one-cell sampled-envelope refined parent data to the existing
refined-window certificate. -/
def ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := fun i => (proofData.cert i).lowerModelIntegral
    subUpper := fun i => (proofData.cert i).upperModelIntegral
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        (proofData.proofData i hi).windowPartBoundsCert
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Convert sharp-anchor one-cell refined parent data to the existing
refined-window certificate. -/
def ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    RefinedWindowPartBoundsCert k ell x L U lower upper :=
  { n := proofData.n
    pts := proofData.pts
    subLower := fun i => (proofData.cert i).lowerModelIntegral
    subUpper := fun i => (proofData.cert i).upperModelIntegral
    first_eq := proofData.first_eq
    last_eq := proofData.last_eq
    mono := proofData.mono
    hProfileInt := proofData.hProfileInt
    subCert := by
      intro i hi
      exact
        (proofData.proofData i hi).windowPartBoundsCert
    lower_le_sum := proofData.lower_le_sum
    sum_le_upper := proofData.sum_le_upper }

/-- Fold residual-anchor refined parent data all the way to the existing parent
window certificate.  This is a generator-facing alias for the route-A fold. -/
theorem ResidualAnchorRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData : ResidualAnchorRefinedWindowProofData k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold exact-integral interval refined parent data all the way to the
existing parent window certificate. -/
theorem ResidualAnchorDerivativeIntervalExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeIntervalExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold auto-slope exact-integral refined parent data all the way to the
existing parent window certificate. -/
theorem ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeIntervalAutoSlopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold direct-envelope auto-slope exact-integral refined parent data all the
way to the existing parent window certificate. -/
theorem ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeIntervalAutoSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold cell-slope direct-envelope exact-integral refined parent data all the
way to the existing parent window certificate.  This is the current route-A
landing surface for the 26-parent payload. -/
theorem ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold one-cell direct residual-derivative interval refined parent data all
the way to the existing parent window certificate. -/
theorem ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeSingleCellIntervalDirectEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold one-cell sampled-envelope refined parent data all the way to the
existing parent window certificate. -/
theorem ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold sharp-anchor one-cell sampled-envelope refined parent data all the
way to the existing parent window certificate. -/
theorem ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L U lower upper : Real}
    (proofData :
      ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData
        k ell x L U lower upper) :
    WindowPartBoundsCert k ell x L U lower upper :=
  WindowPartBoundsCert.of_refinedSubchunks
    proofData.toRefinedWindowPartBoundsCert

/-- Fold a uniform refined grid of valid raw-Omega Taylor/model certificates
into one parent window certificate.  This is the Lean landing surface for the
diagnostic route where a coarse 10-wide parent chunk is internally split into
smaller Taylor subchunks. -/
theorem rawOmegaAWindowPartBoundsCert_of_taylorModelSubchunkCertificates
    (k : Nat) (ell x L step : Real)
    (chunkLower chunkUpper : Nat -> Real) (N : Nat)
    (hstep : 0 <= step)
    (hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L (L + step * (N : Real))))
    (cert : ∀ i : Nat, i < N ->
      RawOmegaATaylorModelCertificate
        k ell x (L + step * (i : Real))
          (L + step * ((i + 1 : Nat) : Real))
        (chunkLower i) (chunkUpper i))
    (valid : ∀ i : Nat, ∀ hi : i < N, (cert i hi).Valid) :
    WindowPartBoundsCert k ell x L (L + step * (N : Real))
      (∑ i ∈ Finset.range N, chunkLower i)
      (∑ i ∈ Finset.range N, chunkUpper i) := by
  exact
    windowPartBoundsCert_of_chunked_range
      k ell x L step chunkLower chunkUpper N hstep hint
      (fun i hi =>
        rawOmegaAWindowPartBoundsCert_of_taylorModelCertificate
          k ell x (L + step * (i : Real))
            (L + step * ((i + 1 : Nat) : Real))
          (chunkLower i) (chunkUpper i)
          (cert i hi) (valid i hi))

/-- Fold refined Taylor/model subchunk certificates, then compare their sums
against a parent chunk interval.  A generator can use this to keep the outer
`Fin 26` parent payload while proving each parent interval from a refined
subchunk grid. -/
theorem rawOmegaAWindowPartBoundsCert_of_taylorModelSubchunkCertificates_bounds
    (k : Nat) (ell x L step : Real)
    (chunkLower chunkUpper : Nat -> Real) (N : Nat)
    (lower upper : Real)
    (hstep : 0 <= step)
    (hint :
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          k ell x)
        (Set.Ioc L (L + step * (N : Real))))
    (cert : ∀ i : Nat, i < N ->
      RawOmegaATaylorModelCertificate
        k ell x (L + step * (i : Real))
          (L + step * ((i + 1 : Nat) : Real))
        (chunkLower i) (chunkUpper i))
    (valid : ∀ i : Nat, ∀ hi : i < N, (cert i hi).Valid)
    (hWindowLower : lower <= ∑ i ∈ Finset.range N, chunkLower i)
    (hWindowUpper : (∑ i ∈ Finset.range N, chunkUpper i) <= upper) :
    WindowPartBoundsCert k ell x L (L + step * (N : Real)) lower upper := by
  have folded :=
    rawOmegaAWindowPartBoundsCert_of_taylorModelSubchunkCertificates
      k ell x L step chunkLower chunkUpper N hstep hint cert valid
  exact
    { hWindowLower := le_trans hWindowLower folded.hWindowLower
      hWindowUpper := le_trans folded.hWindowUpper hWindowUpper }

/-- Generator-facing packet for proving one parent raw-Omega window from a
uniform refined Taylor/model grid.  The outer payload can keep its parent chunk
shape while this structure stores the subchunk certificates and the parent
sum comparisons. -/
structure RefinedSubchunkWindowProofData
    (k : Nat) (ell x L step : Real)
    (chunkLower chunkUpper : Nat -> Real) (N : Nat)
    (lower upper : Real) where
  hstep : 0 <= step
  hProfileInt :
    IntegrableOn
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
        k ell x)
      (Set.Ioc L (L + step * (N : Real)))
  cert : ∀ i : Nat, i < N ->
    RawOmegaATaylorModelCertificate
      k ell x (L + step * (i : Real))
        (L + step * ((i + 1 : Nat) : Real))
      (chunkLower i) (chunkUpper i)
  valid : ∀ i : Nat, ∀ hi : i < N, (cert i hi).Valid
  hWindowLower : lower <= ∑ i ∈ Finset.range N, chunkLower i
  hWindowUpper : (∑ i ∈ Finset.range N, chunkUpper i) <= upper

/-- Consume generator-facing refined-subchunk proof data into the existing
parent `WindowPartBoundsCert`. -/
theorem RefinedSubchunkWindowProofData.toWindowPartBoundsCert
    {k : Nat} {ell x L step : Real}
    {chunkLower chunkUpper : Nat -> Real} {N : Nat}
    {lower upper : Real}
    (data :
      RefinedSubchunkWindowProofData
        k ell x L step chunkLower chunkUpper N lower upper) :
    WindowPartBoundsCert k ell x L (L + step * (N : Real)) lower upper := by
  exact
    rawOmegaAWindowPartBoundsCert_of_taylorModelSubchunkCertificates_bounds
      k ell x L step chunkLower chunkUpper N lower upper data.hstep
      data.hProfileInt data.cert data.valid data.hWindowLower
      data.hWindowUpper

/-- Consume refined-subchunk proof data when the parent endpoint is written in
a different but equal form.  Payload adapters use this to match fixed parent
chunks such as `(10*i, 10*(i+1)]` while refined data is indexed by
`L + step * N`. -/
theorem RefinedSubchunkWindowProofData.toWindowPartBoundsCert_of_endpoint
    {k : Nat} {ell x L step U : Real}
    {chunkLower chunkUpper : Nat -> Real} {N : Nat}
    {lower upper : Real}
    (data :
      RefinedSubchunkWindowProofData
        k ell x L step chunkLower chunkUpper N lower upper)
    (hU : L + step * (N : Real) = U) :
    WindowPartBoundsCert k ell x L U lower upper := by
  simpa [hU] using data.toWindowPartBoundsCert

end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
