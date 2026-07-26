import Q3.Proofs.RouteB.D0KTrialStage3

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# The centered critical-moment contract

This file materializes the exact post-Galerkin `L¹` estimate requested by
`004_centered_critical_moment.goal.md`.  The full-weight
`L²(exp |t|)` projection branch is explicitly not part of the target.

The source expansion is

`q_(m,N)(t) = L_m⁻¹/² ∑_{n=-N}^N (-1)^n c_n exp(2π i n t / L_m)`.

The missing analytic input is the uniform weighted estimate encoded below by
`CenteredTrialCriticalMomentRatio`.
-/

/-- The exact centered D0 density after the Galerkin projection and
`TrialNonzero` normalization.  Translation by `L_m / 2` contributes the
factor `(-1)^n`.

Source locks:
`D0KTrialStage1.lean` (`L_m`, `modeSet`, `V_n_m`, `P_m_N`);
`D0KTrialStage3.lean` (`sTrial_m_N`, `kTrial_m_N`, `c_n`);
`PROSHKA_VERDICT_S1_ANCHOR_2026-07-27.md`, section 1.
-/
def centeredTrialDensity
    (D : CoefficientFamily) (i : PairIndex) (t : ℝ) : ℂ :=
  (Real.sqrt (L_m i) : ℂ)⁻¹ *
    ∑ n ∈ modeSet i,
      ((-1 : ℂ) ^ n) * D.kTrial i n *
        Complex.exp
          (((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L_m i : ℂ)) *
            (t : ℂ))

/-- The centered weighted `L¹` moment on the exact D0 window. -/
def centeredCriticalMoment
    (D : CoefficientFamily) (i : PairIndex) (σ : ℝ) : ℝ :=
  ∫ t in Set.Icc (-(L_m i) / 2) (L_m i / 2),
    ‖centeredTrialDensity D i t‖ * Real.exp (σ * |t|)

/-- The denominator is exactly the zero Fourier coefficient multiplied by
`sqrt (log m)`.  Unit normalization of the full projected vector gives no
positive lower bound for this one coefficient. -/
theorem rawFplus_zero_eq_sqrt_mul_c0
    (D : CoefficientFamily) (i : PairIndex) :
    rawFplus D i 0 =
      (Real.sqrt (L_m i) : ℂ) * D.kTrial i 0 := by
  rw [← rawFplus_eq_D0_integral]
  have h0 : (0 : ℤ) ∈ modeSet i := by
    simp [modeSet]
  simpa [finiteFplusCenteredIntegral] using
    Fplus_zero_eq_sqrt_mul_c0
      (L_m i) (modeSet i) (D.kTrial i) (logLength_pos i) h0

/-- The direct leakage quantity requested by the guard.  Its dependencies are
exactly `(m,N,σ)` through `i` and `σ`; no full-weight `L²` projection norm is
introduced. -/
def centeredMomentLeakage
    (D : CoefficientFamily) (i : CentralIndex D) (σ : ℝ) : ℝ :=
  centeredCriticalMoment D i.1 σ / ‖rawFplus D i.1 0‖

theorem centeredCriticalMoment_eq_leakage_mul_denominator
    (D : CoefficientFamily) (i : CentralIndex D) (σ : ℝ) :
    centeredCriticalMoment D i.1 σ =
      centeredMomentLeakage D i σ * ‖rawFplus D i.1 0‖ := by
  have hden : ‖rawFplus D i.1 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (rawFplus_zero_ne D i)
  simp [centeredMomentLeakage, hden]

/-- `CENTERED_TRIAL_CRITICAL_MOMENT_RATIO`.

This is the weakest repaired S1 input isolated by the Round-2026-07-27
verdict.  The cofinal path is fixed once; the constant may depend on `σ`, but
not on `k`, `m_k`, or `N_k`.
-/
def CenteredTrialCriticalMomentRatio
    (D : CoefficientFamily) (p : ℕ → CentralIndex D) : Prop :=
  PairCofinal p ∧
    ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 →
      ∃ Cσ : ℝ, 0 ≤ Cσ ∧
        ∀ k : ℕ,
          centeredCriticalMoment D (p k).1 σ ≤
            Cσ * ‖rawFplus D (p k).1 0‖

/-! ## Planted failures -/

/-- Two coordinates model an interior cell and an endpoint cell.  This is the
orthogonal projection onto the constant mode for the unweighted Euclidean
inner product. -/
def endpointDirichletProjection (v : ℝ × ℝ) : ℝ × ℝ :=
  ((v.1 + v.2) / 2, (v.1 + v.2) / 2)

def unweightedSquare (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 + v.2 ^ 2

/-- The factor `9` is a finite planted surrogate for the endpoint exponential
weight. -/
def endpointWeightedSquare (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 + 9 * v.2 ^ 2

/-- The endpoint-Dirichlet plant retires the forbidden full-weight `L²`
projection route: the same projection contracts the ordinary square norm but
strictly expands the endpoint-weighted square norm.  This plant is a kill
certificate, not a proposed route to the guarded `L¹` target. -/
theorem endpointDirichletWeightedProjectionPlant :
    unweightedSquare (endpointDirichletProjection (1, 0)) ≤
        unweightedSquare (1, 0) ∧
      endpointWeightedSquare (1, 0) <
        endpointWeightedSquare (endpointDirichletProjection (1, 0)) := by
  norm_num [endpointDirichletProjection, unweightedSquare, endpointWeightedSquare]

/-- The normalized constant-mode transform.  The branch at zero is the
removable value.  This is the exact constant-mode plant
`sin(zL/2)/(zL/2)` from the verdict. -/
def constantModeNormalizedTransform (L : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin (z * (L : ℂ) / 2) / (z * (L : ℂ) / 2)

@[simp] theorem constantModeNormalizedTransform_zero (L : ℝ) :
    constantModeNormalizedTransform L 0 = 1 := by
  simp [constantModeNormalizedTransform]

theorem constantModeNormalizedTransform_off_zero
    (L : ℝ) (z : ℂ) (hz : z ≠ 0) :
    constantModeNormalizedTransform L z =
      Complex.sin (z * (L : ℂ) / 2) / (z * (L : ℂ) / 2) := by
  simp [constantModeNormalizedTransform, hz]

end Q3.RouteB.D0Pstar
