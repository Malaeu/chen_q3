import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof contract for the Step33A.1-A sub0 `realSinc` derivative majorant.

This file is intentionally payload-small.  It records the exact rational
majorant shape selected for the next certificate generator, and it does not
claim the remaining summation/reindex bridge from `changeOriginSeries.sum` to
the live absolute majorant row.

Current first missing bridge:
`STEP33_A1_SUB0_REALSINC_CHANGEORIGINSERIES_TSUM_LIVE_REINDEX_GAP`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- All-index scalar coefficient for the project `realSinc` power series.
Odd coefficients are zero; the even coefficient `2*m` is
`(-1)^m / (2*m+1)!`. -/
def step33RealSincCoeff (n : Nat) : Real :=
  if n % 2 = 0 then
    ((-1 : Real) ^ (n / 2)) / (Nat.factorial (n + 1) : Real)
  else
    0

/-- The `FormalMultilinearSeries` surface for the all-index `realSinc`
coefficients.  This is a scaffold for the remaining rows `1, ..., 17`
crosswalk; it does not by itself prove the derivative majorant. -/
noncomputable def step33RealSincFormalSeries :
    FormalMultilinearSeries Real Real Real :=
  FormalMultilinearSeries.ofScalars Real step33RealSincCoeff

/-- Coefficients of the scaffolded formal series are the all-index sinc
coefficients. -/
theorem step33RealSincFormalSeries_coeff (n : Nat) :
    step33RealSincFormalSeries.coeff n = step33RealSincCoeff n := by
  simp [step33RealSincFormalSeries, FormalMultilinearSeries.coeff_ofScalars]

/-- All-index scalar coefficient for the sine power series.  Even
coefficients vanish; the odd coefficient `2*m+1` is
`(-1)^m / (2*m+1)!`. -/
def step33SinCoeff (n : Nat) : Real :=
  if n % 2 = 1 then
    ((-1 : Real) ^ (n / 2)) / (Nat.factorial n : Real)
  else
    0

/-- The `FormalMultilinearSeries` surface for the all-index sine
coefficients.  Its `fslope` is the named `realSinc` scaffold. -/
noncomputable def step33SinFormalSeries :
    FormalMultilinearSeries Real Real Real :=
  FormalMultilinearSeries.ofScalars Real step33SinCoeff

/-- Even coefficients of the all-index sine series vanish. -/
theorem step33SinCoeff_two_mul (m : Nat) :
    step33SinCoeff (2 * m) = 0 := by
  unfold step33SinCoeff
  have hmod : (2 * m) % 2 ≠ 1 := by
    rw [Nat.mul_mod_right]
    norm_num
  rw [if_neg hmod]

/-- Odd coefficients of the all-index sine series. -/
theorem step33SinCoeff_two_mul_add_one (m : Nat) :
    step33SinCoeff (2 * m + 1) =
      ((-1 : Real) ^ m) / (Nat.factorial (2 * m + 1) : Real) := by
  unfold step33SinCoeff
  have hmod : (2 * m + 1) % 2 = 1 := by
    rw [show 2 * m + 1 = 1 + 2 * m by omega]
    rw [Nat.add_mul_mod_self_left]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [if_pos hmod, hdiv]

/-- The sine coefficients are the normalized iterated derivatives at zero. -/
theorem step33SinCoeff_eq_iteratedDeriv_sin_div_factorial (n : Nat) :
    step33SinCoeff n =
      iteratedDeriv n Real.sin (0 : Real) / (Nat.factorial n : Real) := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨m, hm⟩
    subst n
    have hcoeff : step33SinCoeff (m + m) = 0 := by
      simpa [two_mul] using step33SinCoeff_two_mul m
    rw [hcoeff]
    have hderiv : iteratedDeriv (m + m) Real.sin (0 : Real) = 0 := by
      simpa [two_mul] using
        congrFun (Real.iteratedDeriv_even_sin m) (0 : Real)
    rw [hderiv]
    simp
  · rcases hOdd with ⟨m, hm⟩
    subst n
    rw [step33SinCoeff_two_mul_add_one]
    have hderiv :
        iteratedDeriv (2 * m + 1) Real.sin (0 : Real) =
          (-1 : Real) ^ m := by
      simp
    rw [hderiv]

/-- Coefficients of the scaffolded sine formal series are the normalized
iterated derivatives at zero. -/
theorem step33SinFormalSeries_coeff_eq_iteratedDeriv_sin_div_factorial
    (n : Nat) :
    step33SinFormalSeries.coeff n =
      iteratedDeriv n Real.sin (0 : Real) / (Nat.factorial n : Real) := by
  rw [step33SinFormalSeries, FormalMultilinearSeries.coeff_ofScalars,
    step33SinCoeff_eq_iteratedDeriv_sin_div_factorial]

/-- The named sine formal series is a local power series for `Real.sin` at
zero. -/
theorem step33SinFormalSeries_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Real.sin step33SinFormalSeries (0 : Real) := by
  have hAnalytic : AnalyticAt Real Real.sin (0 : Real) := Real.analyticAt_sin
  have hraw : HasFPowerSeriesAt Real.sin
      (FormalMultilinearSeries.ofScalars Real
        (fun n : Nat =>
          iteratedDeriv n Real.sin (0 : Real) / (Nat.factorial n : Real)))
      (0 : Real) :=
    hAnalytic.hasFPowerSeriesAt
  convert hraw using 1
  ext n
  change step33SinFormalSeries.coeff n =
    (FormalMultilinearSeries.ofScalars Real
      (fun n : Nat =>
        iteratedDeriv n Real.sin (0 : Real) / (Nat.factorial n : Real))).coeff n
  rw [step33SinFormalSeries_coeff_eq_iteratedDeriv_sin_div_factorial]
  simp [FormalMultilinearSeries.coeff_ofScalars]

/-- Even coefficients of the all-index `realSinc` series. -/
theorem step33RealSincCoeff_two_mul (m : Nat) :
    step33RealSincCoeff (2 * m) =
      ((-1 : Real) ^ m) / (Nat.factorial (2 * m + 1) : Real) := by
  unfold step33RealSincCoeff
  rw [if_pos (Nat.mul_mod_right 2 m)]
  simp [Nat.mul_div_right m (by norm_num : 0 < 2)]

/-- Odd coefficients of the all-index `realSinc` series vanish. -/
theorem step33RealSincCoeff_two_mul_add_one (m : Nat) :
    step33RealSincCoeff (2 * m + 1) = 0 := by
  unfold step33RealSincCoeff
  rw [if_neg]
  rw [show (2 * m + 1) % 2 = 1 by
    rw [show 2 * m + 1 = 1 + 2 * m by omega]
    rw [Nat.add_mul_mod_self_left]]
  norm_num

/-- The all-index `realSinc` coefficient is bounded by the exponential
coefficient.  This is deliberately crude; it is only used to expose an
infinite convergence radius for the formal-series scaffold. -/
theorem step33RealSincCoeff_norm_le_inv_factorial (n : Nat) :
    ‖step33RealSincCoeff n‖ <= ((Nat.factorial n : Real))⁻¹ := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨m, hm⟩
    subst n
    rw [show m + m = 2 * m by omega]
    rw [step33RealSincCoeff_two_mul]
    have hfac_pos :
        0 < (Nat.factorial (2 * m) : Real) := by
      positivity
    have hfac_succ_pos :
        0 < (Nat.factorial (2 * m + 1) : Real) := by
      positivity
    have hfac_le :
        (Nat.factorial (2 * m) : Real) <=
          (Nat.factorial (2 * m + 1) : Real) := by
      exact_mod_cast Nat.factorial_le (by omega : 2 * m <= 2 * m + 1)
    calc
      ‖((-1 : Real) ^ m / (Nat.factorial (2 * m + 1) : Real))‖
          = ((Nat.factorial (2 * m + 1) : Real))⁻¹ := by
            rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one,
              one_pow, abs_of_pos hfac_succ_pos]
            simp [div_eq_mul_inv]
      _ <= ((Nat.factorial (2 * m) : Real))⁻¹ := by
            exact (inv_le_inv₀ hfac_succ_pos hfac_pos).2 hfac_le
  · rcases hOdd with ⟨m, hm⟩
    subst n
    rw [step33RealSincCoeff_two_mul_add_one]
    simp

/-- The named all-index `realSinc` formal-series scaffold has infinite
radius.  This is the radius half of the on-ball bridge needed before applying
`changeOrigin` at `u <= 1 / 400`. -/
theorem step33RealSincFormalSeries_radius_eq_top :
    step33RealSincFormalSeries.radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ ?_
  intro r
  refine Summable.of_nonneg_of_le
    (f := fun n : Nat => (r : Real) ^ n / (Nat.factorial n : Real))
    (g := fun n : Nat =>
      ‖step33RealSincFormalSeries n‖ * (r : Real) ^ n)
    ?hNonneg ?hLe (Real.summable_pow_div_factorial (r : Real))
  · intro n
    positivity
  · intro n
    have hcoeff := step33RealSincCoeff_norm_le_inv_factorial n
    have hpow_nonneg : 0 <= (r : Real) ^ n := by
      positivity
    calc
      ‖step33RealSincFormalSeries n‖ * (r : Real) ^ n
          = ‖step33RealSincCoeff n‖ * (r : Real) ^ n := by
            rw [step33RealSincFormalSeries,
              FormalMultilinearSeries.ofScalars_norm]
      _ <= ((Nat.factorial n : Real))⁻¹ * (r : Real) ^ n := by
            exact mul_le_mul_of_nonneg_right hcoeff hpow_nonneg
      _ = (r : Real) ^ n / (Nat.factorial n : Real) := by
            rw [div_eq_mul_inv, mul_comm]

/-- All-index scalar summation bridge for the named `realSinc`
coefficients.  This is the missing even/odd reindex layer between the existing
even `realSinc` series and the all-index formal-series scaffold. -/
theorem step33RealSincCoeff_hasSum_allIndex (x : Real) :
    HasSum (fun n : Nat => step33RealSincCoeff n * x ^ n) (realSinc x) := by
  have heven :
      HasSum
        (fun m : Nat => step33RealSincCoeff (2 * m) * x ^ (2 * m))
        (realSinc x) := by
    refine HasSum.congr_fun (realSinc_hasSum_even_powerSeries x) ?_
    intro m
    rw [step33RealSincCoeff_two_mul]
    rw [div_mul_eq_mul_div]
  have hodd :
      HasSum
        (fun m : Nat => step33RealSincCoeff (2 * m + 1) *
          x ^ (2 * m + 1))
        0 := by
    simpa [step33RealSincCoeff_two_mul_add_one] using
      (hasSum_zero : HasSum (fun _m : Nat => (0 : Real)) (0 : Real))
  have hall :=
    HasSum.even_add_odd
      (f := fun n : Nat => step33RealSincCoeff n * x ^ n) heven hodd
  simpa using hall

/-- All-index formal-series summation bridge for the named `realSinc`
scaffold.  This packages the scalar all-index bridge in the
`FormalMultilinearSeries` convention required by `HasFPowerSeriesOnBall`. -/
theorem step33RealSincFormalSeries_hasSum_apply (x : Real) :
    HasSum
      (fun n : Nat => step33RealSincFormalSeries n (fun _ : Fin n => x))
      (realSinc x) := by
  refine HasSum.congr_fun (step33RealSincCoeff_hasSum_allIndex x) ?_
  intro n
  rw [step33RealSincFormalSeries,
    FormalMultilinearSeries.ofScalars_apply_eq]
  simp [smul_eq_mul]

/-- Unit-ball power-series surface for the named all-index `realSinc`
scaffold.  This closes the explicit on-ball prerequisite for the subsequent
`changeOrigin`/`iteratedDeriv` majorant bridge on `0 <= u <= 1 / 400`. -/
theorem step33RealSincFormalSeries_hasFPowerSeriesOnBall_one :
    HasFPowerSeriesOnBall realSinc step33RealSincFormalSeries
      (0 : Real) (1 : ENNReal) := by
  refine ⟨?r_le, ?r_pos, ?hasSum⟩
  · rw [step33RealSincFormalSeries_radius_eq_top]
    exact le_top
  · norm_num
  · intro y _hy
    simpa using step33RealSincFormalSeries_hasSum_apply y

/-- Points in the tiny sub0 interval lie inside the unit convergence ball used
by the checked `realSinc` formal-series source. -/
theorem step33Sub0RealSinc_mem_unit_ball_of_mem_Icc
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400)) :
    (‖u‖₊ : ENNReal) < (1 : ENNReal) := by
  have hnorm_le : ‖u‖₊ <= ((1 : Real) / 400).toNNReal := by
    rw [Real.nnnorm_of_nonneg hu.1]
    rw [Real.toNNReal_of_nonneg (by norm_num : 0 <= (1 : Real) / 400)]
    exact_mod_cast hu.2
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hnorm_le) (by norm_num)

/-- `changeOrigin`/`factorial_smul` bridge from the checked all-index
`realSinc` power series to the ordinary one-dimensional iterated derivative.
This is the analytic equality needed before turning the live signed
`changeOriginSeries` terms into absolute row majorants. -/
theorem step33RealSinc_iteratedDeriv_eq_factorial_changeOriginSeries_sum
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400)) (k : Nat) :
    iteratedDeriv k realSinc u =
      (Nat.factorial k : Real) *
        (((step33RealSincFormalSeries.changeOriginSeries k).sum u)
          (fun _ : Fin k => (1 : Real))) := by
  have hunit := step33Sub0RealSinc_mem_unit_ball_of_mem_Icc hu
  have hshift :=
    step33RealSincFormalSeries_hasFPowerSeriesOnBall_one.changeOrigin
      (y := u) hunit
  have hfact := hshift.factorial_smul (1 : Real) k
  rw [zero_add] at hfact
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [← hfact]
  simp [FormalMultilinearSeries.changeOrigin, nsmul_eq_mul]

/-- The `fslope` of the all-index sine series is the all-index project
`realSinc` series. -/
theorem step33SinFormalSeries_fslope_eq_realSincFormalSeries :
    step33SinFormalSeries.fslope = step33RealSincFormalSeries := by
  ext n
  change step33SinFormalSeries.fslope.coeff n =
    step33RealSincFormalSeries.coeff n
  rw [FormalMultilinearSeries.coeff_fslope]
  rw [step33SinFormalSeries, FormalMultilinearSeries.coeff_ofScalars]
  rw [step33RealSincFormalSeries_coeff]
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨m, hm⟩
    subst n
    have hsin :
        step33SinCoeff (m + m + 1) =
          ((-1 : Real) ^ m) / (Nat.factorial (m + m + 1) : Real) := by
      simpa [two_mul] using step33SinCoeff_two_mul_add_one m
    have hsinc :
        step33RealSincCoeff (m + m) =
          ((-1 : Real) ^ m) / (Nat.factorial (m + m + 1) : Real) := by
      simpa [two_mul] using step33RealSincCoeff_two_mul m
    rw [hsin, hsinc]
  · rcases hOdd with ⟨m, hm⟩
    subst n
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
    rw [step33SinCoeff_two_mul]
    rw [step33RealSincCoeff_two_mul_add_one]

/-- The named all-index `realSinc` scaffold is a local power series for
`realSinc` at zero.  This is the analytic source needed before converting the
checked `changeOriginSeries` live-index algebra into rows `1, ..., 17`. -/
theorem step33RealSincFormalSeries_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt realSinc step33RealSincFormalSeries (0 : Real) := by
  have hsinc :=
    realSinc_hasFPowerSeriesAt_zero_of_sin
      step33SinFormalSeries_hasFPowerSeriesAt_zero
  simpa [step33SinFormalSeries_fslope_eq_realSincFormalSeries] using hsinc

/-- Diagonal even terms of the scaffolded formal series match the usual
even sinc power-series terms. -/
theorem step33RealSincFormalSeries_apply_two_mul (m : Nat) (x : Real) :
    step33RealSincFormalSeries (2 * m) (fun _ : Fin (2 * m) => x) =
      (((-1 : Real) ^ m) / (Nat.factorial (2 * m + 1) : Real)) *
        x ^ (2 * m) := by
  rw [step33RealSincFormalSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [step33RealSincCoeff_two_mul]
  simp [smul_eq_mul]

/-- Diagonal odd terms of the scaffolded formal series vanish. -/
theorem step33RealSincFormalSeries_apply_two_mul_add_one (m : Nat) (x : Real) :
    step33RealSincFormalSeries (2 * m + 1)
        (fun _ : Fin (2 * m + 1) => x) = 0 := by
  rw [step33RealSincFormalSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [step33RealSincCoeff_two_mul_add_one]
  simp

/-- Number of `n`-element subsets of `Fin (1+n)`.  This is the cardinality
factor appearing in the first derivative series of a scalar formal series. -/
theorem step33_card_subsets_fin_one_add_card_eq (n : Nat) :
    Fintype.card {s : Finset (Fin (1 + n)) // s.card = n} = n + 1 := by
  rw [Fintype.card_subtype]
  change (Finset.univ.filter
      (fun x : Finset (Fin (1 + n)) => x.card = n)).card = n + 1
  have hfin : Finset.univ.filter
      (fun x : Finset (Fin (1 + n)) => x.card = n) =
        Finset.powersetCard n (Finset.univ : Finset (Fin (1 + n))) := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [hfin, Finset.card_powersetCard]
  simp [Nat.add_comm, Nat.choose_succ_self_right]

/-- Each change-origin term in the first derivative series of a scalar formal
series contributes the same monomial when evaluated at scalar direction `1`. -/
theorem step33_ofScalars_changeOriginSeriesTerm_one_apply_one
    (c : Nat -> Real) (n : Nat) (u : Real)
    (s : {s : Finset (Fin (1 + n)) // Finset.card s = n}) :
    (((FormalMultilinearSeries.ofScalars Real c).changeOriginSeriesTerm 1 n
        s.1 s.2) (fun _ : Fin n => u)) (fun _ : Fin 1 => (1 : Real)) =
      c (1 + n) * u ^ n := by
  rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  simp only [FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul,
    List.prod_ofFn]
  rw [Finset.prod_piecewise]
  simp [Finset.prod_const, s.2]

/-- First derivative series term for a scalar formal series, evaluated at
scalar direction `1`.  This is the local bridge missing from Mathlib for the
`realSinc` row-`1` and iterated-row crosswalk. -/
theorem step33_ofScalars_derivSeries_apply_one
    (c : Nat -> Real) (n : Nat) (u : Real) :
    (FormalMultilinearSeries.ofScalars Real c).derivSeries n
        (fun _ : Fin n => u) (1 : Real) =
      ((n + 1 : Nat) : Real) * c (1 + n) * u ^ n := by
  rw [FormalMultilinearSeries.derivSeries]
  change ((continuousMultilinearCurryFin1 Real Real Real)
      ((((FormalMultilinearSeries.ofScalars Real c).changeOriginSeries 1) n)
        (fun _ : Fin n => u))) (1 : Real) =
    ((n + 1 : Nat) : Real) * c (1 + n) * u ^ n
  rw [continuousMultilinearCurryFin1_apply]
  rw [FormalMultilinearSeries.changeOriginSeries]
  simp only [ContinuousMultilinearMap.sum_apply]
  calc
    (∑ x : {s : Finset (Fin (1 + n)) // Finset.card s = n},
      (((FormalMultilinearSeries.ofScalars Real c).changeOriginSeriesTerm
          1 n x.1 x.2) (fun _ : Fin n => u)) (Fin.snoc 0 1))
        = ∑ _x : {s : Finset (Fin (1 + n)) // Finset.card s = n},
            c (1 + n) * u ^ n := by
          apply Finset.sum_congr rfl
          intro x hx
          simpa using
            step33_ofScalars_changeOriginSeriesTerm_one_apply_one c n u x
    _ = ((Fintype.card {s : Finset (Fin (1 + n)) // s.card = n} : Nat) :
          Real) * (c (1 + n) * u ^ n) := by
          simp [nsmul_eq_mul]
    _ = ((n + 1 : Nat) : Real) * c (1 + n) * u ^ n := by
          rw [step33_card_subsets_fin_one_add_card_eq n]
          ring

/-- Specialized first derivative-series term for the named `realSinc` formal
series scaffold. -/
theorem step33RealSincFormalSeries_derivSeries_apply_one
    (n : Nat) (u : Real) :
    step33RealSincFormalSeries.derivSeries n
        (fun _ : Fin n => u) (1 : Real) =
      ((n + 1 : Nat) : Real) * step33RealSincCoeff (n + 1) * u ^ n := by
  simpa [step33RealSincFormalSeries, Nat.add_comm] using
    step33_ofScalars_derivSeries_apply_one step33RealSincCoeff n u

/-- Number of `e`-element subsets of `Fin (k+e)`.  This is the scalar
binomial coefficient in the general `changeOriginSeries` term. -/
theorem step33_card_subsets_fin_add_card_eq (k e : Nat) :
    Fintype.card {s : Finset (Fin (k + e)) // s.card = e} =
      Nat.choose (k + e) e := by
  rw [Fintype.card_subtype]
  change (Finset.univ.filter
      (fun x : Finset (Fin (k + e)) => x.card = e)).card =
    Nat.choose (k + e) e
  have hfin : Finset.univ.filter
      (fun x : Finset (Fin (k + e)) => x.card = e) =
        Finset.powersetCard e (Finset.univ : Finset (Fin (k + e))) := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [hfin, Finset.card_powersetCard]
  simp

/-- Each scalar `changeOriginSeriesTerm` contributes the same monomial when the
old variables are evaluated at `1` and the new variables at scalar `u`. -/
theorem step33_ofScalars_changeOriginSeriesTerm_apply_ones
    (c : Nat -> Real) (k e : Nat) (u : Real)
    (s : {s : Finset (Fin (k + e)) // Finset.card s = e}) :
    (((FormalMultilinearSeries.ofScalars Real c).changeOriginSeriesTerm k e
        s.1 s.2) (fun _ : Fin e => u)) (fun _ : Fin k => (1 : Real)) =
      c (k + e) * u ^ e := by
  rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  simp only [FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul,
    List.prod_ofFn]
  rw [Finset.prod_piecewise]
  simp [Finset.prod_const, s.2]

/-- Scalar `changeOriginSeries` evaluated on constant scalar directions.  This
is the binomial bridge needed before the `realSinc` parity reindex. -/
theorem step33_ofScalars_changeOriginSeries_apply_ones
    (c : Nat -> Real) (k e : Nat) (u : Real) :
    (((FormalMultilinearSeries.ofScalars Real c).changeOriginSeries k e)
        (fun _ : Fin e => u)) (fun _ : Fin k => (1 : Real)) =
      ((Nat.choose (k + e) e : Nat) : Real) * c (k + e) * u ^ e := by
  rw [FormalMultilinearSeries.changeOriginSeries]
  simp only [ContinuousMultilinearMap.sum_apply]
  calc
    (∑ x : {s : Finset (Fin (k + e)) // Finset.card s = e},
      (((FormalMultilinearSeries.ofScalars Real c).changeOriginSeriesTerm
          k e x.1 x.2) (fun _ : Fin e => u)) (fun _ : Fin k => (1 : Real)))
        = ∑ _x : {s : Finset (Fin (k + e)) // Finset.card s = e},
            c (k + e) * u ^ e := by
          apply Finset.sum_congr rfl
          intro x hx
          simpa using
            step33_ofScalars_changeOriginSeriesTerm_apply_ones c k e u x
    _ = ((Fintype.card {s : Finset (Fin (k + e)) // s.card = e} : Nat) :
          Real) * (c (k + e) * u ^ e) := by
          simp [nsmul_eq_mul]
    _ = ((Nat.choose (k + e) e : Nat) : Real) * c (k + e) * u ^ e := by
          rw [step33_card_subsets_fin_add_card_eq k e]
          ring

/-- Specialized scalar `changeOriginSeries` bridge for the named all-index
`realSinc` formal-series scaffold. -/
theorem step33RealSincFormalSeries_changeOriginSeries_apply_ones
    (k e : Nat) (u : Real) :
    ((step33RealSincFormalSeries.changeOriginSeries k e)
        (fun _ : Fin e => u)) (fun _ : Fin k => (1 : Real)) =
      ((Nat.choose (k + e) e : Nat) : Real) *
        step33RealSincCoeff (k + e) * u ^ e := by
  simpa [step33RealSincFormalSeries] using
    step33_ofScalars_changeOriginSeries_apply_ones step33RealSincCoeff k e u

/-- Even total indices in the scalar `changeOriginSeries` bridge expose the
usual nonzero sinc coefficient. -/
theorem step33RealSincFormalSeries_changeOriginSeries_apply_ones_even_index
    {k n : Nat} (hk : k <= 2 * n) (u : Real) :
    ((step33RealSincFormalSeries.changeOriginSeries k (2 * n - k))
        (fun _ : Fin (2 * n - k) => u)) (fun _ : Fin k => (1 : Real)) =
      ((Nat.choose (2 * n) (2 * n - k) : Nat) : Real) *
        (((-1 : Real) ^ n) / (Nat.factorial (2 * n + 1) : Real)) *
        u ^ (2 * n - k) := by
  rw [step33RealSincFormalSeries_changeOriginSeries_apply_ones]
  have hsum : k + (2 * n - k) = 2 * n := Nat.add_sub_of_le hk
  rw [hsum, step33RealSincCoeff_two_mul]

/-- Odd total indices in the scalar `changeOriginSeries` bridge vanish for the
all-index `realSinc` formal-series scaffold. -/
theorem step33RealSincFormalSeries_changeOriginSeries_apply_ones_odd_index
    {k n : Nat} (hk : k <= 2 * n + 1) (u : Real) :
    ((step33RealSincFormalSeries.changeOriginSeries k (2 * n + 1 - k))
        (fun _ : Fin (2 * n + 1 - k) => u))
        (fun _ : Fin k => (1 : Real)) = 0 := by
  rw [step33RealSincFormalSeries_changeOriginSeries_apply_ones]
  have hsum : k + (2 * n + 1 - k) = 2 * n + 1 := Nat.add_sub_of_le hk
  rw [hsum, step33RealSincCoeff_two_mul_add_one]
  ring

/-- Binomial/factorial normalization for the even `realSinc` derivative
coefficient.  This is the scalar arithmetic bridge from the
`changeOriginSeries` binomial factor to the denominator used by the rational
majorant checker. -/
theorem step33RealSinc_even_choose_factorial_div_eq_majorant_coeff
    {k n : Nat} (hk : k <= 2 * n) :
    ((Nat.factorial k : Real) *
        ((Nat.choose (2 * n) (2 * n - k) : Nat) : Real)) /
        (Nat.factorial (2 * n + 1) : Real) =
      1 / (((2 * n + 1 : Nat) : Real) *
        (Nat.factorial (2 * n - k) : Real)) := by
  have hchoose :
      ((Nat.choose (2 * n) (2 * n - k) : Nat) : Real) =
        (Nat.factorial (2 * n) : Real) /
          ((Nat.factorial (2 * n - k) : Real) *
            (Nat.factorial k : Real)) := by
    have hle : 2 * n - k <= 2 * n := Nat.sub_le _ _
    have hsub : 2 * n - (2 * n - k) = k := by omega
    simpa [hsub] using
      (Nat.cast_choose (K := Real) (a := 2 * n - k) (b := 2 * n) hle)
  have hfact_succ :
      (Nat.factorial (2 * n + 1) : Real) =
        ((2 * n + 1 : Nat) : Real) * (Nat.factorial (2 * n) : Real) := by
    rw [show 2 * n + 1 = (2 * n).succ by omega]
    simp [Nat.factorial_succ]
  have hkfac : (Nat.factorial k : Real) ≠ 0 := by positivity
  have hefac : (Nat.factorial (2 * n - k) : Real) ≠ 0 := by positivity
  have htfac : (Nat.factorial (2 * n) : Real) ≠ 0 := by positivity
  have hlin : ((2 * n + 1 : Nat) : Real) ≠ 0 := by positivity
  rw [hchoose, hfact_succ]
  field_simp [hkfac, hefac, htfac, hlin]

/-- Signed version of the even binomial/factorial normalization. -/
theorem step33RealSinc_even_choose_factorial_coeff_eq_majorant_coeff
    {k n : Nat} (hk : k <= 2 * n) :
    (Nat.factorial k : Real) *
        ((Nat.choose (2 * n) (2 * n - k) : Nat) : Real) *
        (((-1 : Real) ^ n) / (Nat.factorial (2 * n + 1) : Real)) =
      ((-1 : Real) ^ n) /
        (((2 * n + 1 : Nat) : Real) *
          (Nat.factorial (2 * n - k) : Real)) := by
  have hbase :=
    step33RealSinc_even_choose_factorial_div_eq_majorant_coeff
      (k := k) (n := n) hk
  calc
    (Nat.factorial k : Real) *
        ((Nat.choose (2 * n) (2 * n - k) : Nat) : Real) *
        (((-1 : Real) ^ n) / (Nat.factorial (2 * n + 1) : Real))
        = ((-1 : Real) ^ n) *
            (((Nat.factorial k : Real) *
              ((Nat.choose (2 * n) (2 * n - k) : Nat) : Real)) /
              (Nat.factorial (2 * n + 1) : Real)) := by
          ring
    _ = ((-1 : Real) ^ n) /
        (((2 * n + 1 : Nat) : Real) *
          (Nat.factorial (2 * n - k) : Real)) := by
          rw [hbase]
          ring

/-- Starting series index for the absolute majorant of the `k`-th derivative
of `realSinc`.  This is `ceil(k / 2)`, written in integer form. -/
def step33Sub0RealSincDerivMajorantStart (k : Nat) : Nat :=
  (k + 1) / 2

/-- Actual power-series index used by the `m`-th live term of row `k`. -/
def step33Sub0RealSincDerivMajorantIndex (k m : Nat) : Nat :=
  step33Sub0RealSincDerivMajorantStart k + m

/-- Derivative exponent `2*n-k` for the `m`-th live term of row `k`. -/
def step33Sub0RealSincDerivMajorantExponent (k m : Nat) : Nat :=
  2 * step33Sub0RealSincDerivMajorantIndex k m - k

/-- Positive integer denominator `(2*n+1) * (2*n-k)!` for the live term. -/
def step33Sub0RealSincDerivMajorantDenominator (k m : Nat) : Nat :=
  (2 * step33Sub0RealSincDerivMajorantIndex k m + 1) *
    (step33Sub0RealSincDerivMajorantExponent k m).factorial

/-- Rational absolute majorant term for the `m`-th live term in the `k`-th
`realSinc` derivative bound on `0 <= u <= 1 / 400`.

For `n = ceil(k / 2) + m` and `e = 2*n - k`, the intended analytic term is
`(1/400)^e / ((2*n+1) * e!)`.  The derivative crosswalk proving this really
majorizes `‖iteratedDeriv k realSinc u‖` is deliberately not asserted here. -/
def step33Sub0RealSincDerivMajorantTerm (k m : Nat) : Rat :=
  (((1 : Rat) / 400) ^ step33Sub0RealSincDerivMajorantExponent k m) /
    (step33Sub0RealSincDerivMajorantDenominator k m : Rat)

/-- Direct real-valued view of `step33Sub0RealSincDerivMajorantTerm`. -/
def step33Sub0RealSincDerivMajorantTermReal (k m : Nat) : Real :=
  (((1 : Real) / 400) ^ step33Sub0RealSincDerivMajorantExponent k m) /
    (step33Sub0RealSincDerivMajorantDenominator k m : Real)

/-- The rational term and its direct real formula agree after coercion. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_eq (k m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm k m : Real) =
      step33Sub0RealSincDerivMajorantTermReal k m := by
  unfold step33Sub0RealSincDerivMajorantTerm
    step33Sub0RealSincDerivMajorantTermReal
  norm_num

/-- The chosen start index is large enough for the `k`-th derivative row. -/
theorem step33Sub0RealSincDerivMajorantStart_spec (k : Nat) :
    k <= 2 * step33Sub0RealSincDerivMajorantStart k := by
  unfold step33Sub0RealSincDerivMajorantStart
  omega

/-- The live majorant index is large enough for row `k`. -/
theorem step33Sub0RealSincDerivMajorantIndex_spec (k m : Nat) :
    k <= 2 * step33Sub0RealSincDerivMajorantIndex k m := by
  unfold step33Sub0RealSincDerivMajorantIndex
  have hs := step33Sub0RealSincDerivMajorantStart_spec k
  omega

/-- The live exponent is exactly the leftover even-index degree after taking
`k` derivatives. -/
theorem step33Sub0RealSincDerivMajorantIndex_add_exponent (k m : Nat) :
    k + step33Sub0RealSincDerivMajorantExponent k m =
      2 * step33Sub0RealSincDerivMajorantIndex k m := by
  unfold step33Sub0RealSincDerivMajorantExponent
  exact Nat.add_sub_of_le (step33Sub0RealSincDerivMajorantIndex_spec k m)

/-- The live exponent plus the derivative order recovers the even total
degree.  This is the commuted form of the live-index arithmetic used by later
reindexing lemmas. -/
theorem step33Sub0RealSincDerivMajorantExponent_add_k (k m : Nat) :
    step33Sub0RealSincDerivMajorantExponent k m + k =
      2 * step33Sub0RealSincDerivMajorantIndex k m := by
  rw [Nat.add_comm]
  exact step33Sub0RealSincDerivMajorantIndex_add_exponent k m

/-- If an even total degree `2*n` survives the `k`-th derivative, then `n` is
past the live majorant start index. -/
theorem step33Sub0RealSincDerivMajorantStart_le_of_k_le_two_mul
    {k n : Nat} (hkn : k <= 2 * n) :
    step33Sub0RealSincDerivMajorantStart k <= n := by
  unfold step33Sub0RealSincDerivMajorantStart
  omega

/-- Reindex an arbitrary surviving even total degree back to the live majorant
index. -/
theorem step33Sub0RealSincDerivMajorantIndex_sub_start
    {k n : Nat} (hkn : k <= 2 * n) :
    step33Sub0RealSincDerivMajorantIndex k
        (n - step33Sub0RealSincDerivMajorantStart k) = n := by
  unfold step33Sub0RealSincDerivMajorantIndex
  exact Nat.add_sub_of_le
    (step33Sub0RealSincDerivMajorantStart_le_of_k_le_two_mul hkn)

/-- Reindex an arbitrary surviving even exponent into the live majorant
exponent convention. -/
theorem step33Sub0RealSincDerivMajorantExponent_sub_start
    {k n : Nat} (hkn : k <= 2 * n) :
    step33Sub0RealSincDerivMajorantExponent k
        (n - step33Sub0RealSincDerivMajorantStart k) = 2 * n - k := by
  unfold step33Sub0RealSincDerivMajorantExponent
  rw [step33Sub0RealSincDerivMajorantIndex_sub_start hkn]

/-- The `realSinc` scalar `changeOriginSeries` bridge specialized to the live
indices used by the rational majorant checker. -/
theorem step33RealSincFormalSeries_changeOriginSeries_apply_ones_live_index
    (k m : Nat) (u : Real) :
    ((step33RealSincFormalSeries.changeOriginSeries k
        (step33Sub0RealSincDerivMajorantExponent k m))
        (fun _ : Fin (step33Sub0RealSincDerivMajorantExponent k m) => u))
        (fun _ : Fin k => (1 : Real)) =
      ((Nat.choose (2 * step33Sub0RealSincDerivMajorantIndex k m)
          (step33Sub0RealSincDerivMajorantExponent k m) : Nat) : Real) *
        (((-1 : Real) ^ step33Sub0RealSincDerivMajorantIndex k m) /
          (Nat.factorial
            (2 * step33Sub0RealSincDerivMajorantIndex k m + 1) : Real)) *
        u ^ step33Sub0RealSincDerivMajorantExponent k m := by
  simpa [step33Sub0RealSincDerivMajorantExponent] using
    step33RealSincFormalSeries_changeOriginSeries_apply_ones_even_index
      (k := k) (n := step33Sub0RealSincDerivMajorantIndex k m)
      (step33Sub0RealSincDerivMajorantIndex_spec k m) u

/-- Live-index scalar bridge with the `k!` normalization expected by the
`iteratedFDeriv`/power-series crosswalk.  This is the exact signed coefficient
shape underlying the rational absolute majorant term. -/
theorem step33RealSincFormalSeries_factorial_mul_changeOriginSeries_apply_ones_live_index
    (k m : Nat) (u : Real) :
    (Nat.factorial k : Real) *
      (((step33RealSincFormalSeries.changeOriginSeries k
          (step33Sub0RealSincDerivMajorantExponent k m))
          (fun _ : Fin (step33Sub0RealSincDerivMajorantExponent k m) => u))
          (fun _ : Fin k => (1 : Real))) =
      (((-1 : Real) ^ step33Sub0RealSincDerivMajorantIndex k m) /
          (((2 * step33Sub0RealSincDerivMajorantIndex k m + 1 : Nat) : Real) *
            (Nat.factorial
              (step33Sub0RealSincDerivMajorantExponent k m) : Real))) *
        u ^ step33Sub0RealSincDerivMajorantExponent k m := by
  rw [step33RealSincFormalSeries_changeOriginSeries_apply_ones_live_index]
  have hnorm :=
    step33RealSinc_even_choose_factorial_coeff_eq_majorant_coeff
      (k := k) (n := step33Sub0RealSincDerivMajorantIndex k m)
      (step33Sub0RealSincDerivMajorantIndex_spec k m)
  calc
    (Nat.factorial k : Real) *
      (((Nat.choose (2 * step33Sub0RealSincDerivMajorantIndex k m)
          (step33Sub0RealSincDerivMajorantExponent k m) : Nat) : Real) *
        (((-1 : Real) ^ step33Sub0RealSincDerivMajorantIndex k m) /
          (Nat.factorial
            (2 * step33Sub0RealSincDerivMajorantIndex k m + 1) : Real)) *
        u ^ step33Sub0RealSincDerivMajorantExponent k m)
        =
      ((Nat.factorial k : Real) *
        ((Nat.choose (2 * step33Sub0RealSincDerivMajorantIndex k m)
          (step33Sub0RealSincDerivMajorantExponent k m) : Nat) : Real) *
        (((-1 : Real) ^ step33Sub0RealSincDerivMajorantIndex k m) /
          (Nat.factorial
            (2 * step33Sub0RealSincDerivMajorantIndex k m + 1) : Real))) *
        u ^ step33Sub0RealSincDerivMajorantExponent k m := by
          ring
    _ =
      (((-1 : Real) ^ step33Sub0RealSincDerivMajorantIndex k m) /
          (((2 * step33Sub0RealSincDerivMajorantIndex k m + 1 : Nat) : Real) *
            (Nat.factorial
              (step33Sub0RealSincDerivMajorantExponent k m) : Real))) *
        u ^ step33Sub0RealSincDerivMajorantExponent k m := by
          rw [show step33Sub0RealSincDerivMajorantExponent k m =
              2 * step33Sub0RealSincDerivMajorantIndex k m - k by rfl]
          rw [hnorm]

/-- Odd total degrees vanish even after multiplying by the derivative
normalization. -/
theorem step33RealSincFormalSeries_factorial_mul_changeOriginSeries_apply_ones_odd_index
    {k n : Nat} (hk : k <= 2 * n + 1) (u : Real) :
    (Nat.factorial k : Real) *
      (((step33RealSincFormalSeries.changeOriginSeries k (2 * n + 1 - k))
          (fun _ : Fin (2 * n + 1 - k) => u))
          (fun _ : Fin k => (1 : Real))) = 0 := by
  rw [step33RealSincFormalSeries_changeOriginSeries_apply_ones_odd_index hk u]
  ring

/-- Each live signed `changeOriginSeries` term is covered by the rational
absolute majorant term on the tiny sub0 interval.  This is the termwise
estimate needed after the analytic `iteratedDeriv = k! * changeOriginSeries`
bridge. -/
theorem step33RealSinc_factorial_changeOriginSeries_live_norm_le_majorant
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400))
    (k m : Nat) :
    ‖(Nat.factorial k : Real) *
      (((step33RealSincFormalSeries.changeOriginSeries k
          (step33Sub0RealSincDerivMajorantExponent k m))
          (fun _ : Fin (step33Sub0RealSincDerivMajorantExponent k m) => u))
          (fun _ : Fin k => (1 : Real)))‖ <=
      (step33Sub0RealSincDerivMajorantTerm k m : Real) := by
  rw [step33RealSincFormalSeries_factorial_mul_changeOriginSeries_apply_ones_live_index]
  rw [step33Sub0RealSincDerivMajorantTerm_real_eq]
  unfold step33Sub0RealSincDerivMajorantTermReal
    step33Sub0RealSincDerivMajorantDenominator
  let n := step33Sub0RealSincDerivMajorantIndex k m
  let e := step33Sub0RealSincDerivMajorantExponent k m
  have hu_abs : |u| <= (1 : Real) / 400 := by
    rw [abs_of_nonneg hu.1]
    exact hu.2
  have hpow : |u| ^ e <= ((1 : Real) / 400) ^ e :=
    pow_le_pow_left₀ (abs_nonneg u) hu_abs e
  have hden_pos :
      0 < (((2 * n + 1 : Nat) : Real) * (Nat.factorial e : Real)) := by
    positivity
  have hden_nonneg :
      0 <= ((((2 * n + 1 : Nat) : Real) *
        (Nat.factorial e : Real)))⁻¹ := by
    positivity
  calc
    ‖(((-1 : Real) ^ n) /
          (((2 * n + 1 : Nat) : Real) * (Nat.factorial e : Real))) *
        u ^ e‖
        = |u| ^ e /
            (((2 * n + 1 : Nat) : Real) * (Nat.factorial e : Real)) := by
          rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
            abs_neg, abs_one, one_pow, abs_of_pos hden_pos]
          simp [div_eq_mul_inv, mul_comm]
    _ <= ((1 : Real) / 400) ^ e /
          (((2 * n + 1 : Nat) : Real) * (Nat.factorial e : Real)) := by
          exact mul_le_mul_of_nonneg_right hpow hden_nonneg
    _ = ((1 : Real) / 400) ^ e /
          (((2 * n + 1) * e.factorial : Nat) : Real) := by
          norm_num [Nat.cast_mul]

/-- Consecutive live terms increase the derivative exponent by exactly two. -/
theorem step33Sub0RealSincDerivMajorantExponent_succ (k m : Nat) :
    step33Sub0RealSincDerivMajorantExponent k (m + 1) =
      step33Sub0RealSincDerivMajorantExponent k m + 2 := by
  unfold step33Sub0RealSincDerivMajorantExponent
    step33Sub0RealSincDerivMajorantIndex
  have h0 : k <= 2 * (step33Sub0RealSincDerivMajorantStart k + m) := by
    have hs := step33Sub0RealSincDerivMajorantStart_spec k
    omega
  rw [show 2 * (step33Sub0RealSincDerivMajorantStart k + (m + 1)) =
      2 * (step33Sub0RealSincDerivMajorantStart k + m) + 2 by omega]
  rw [Nat.sub_add_comm h0]

/-- The live-term denominator is strictly positive. -/
theorem step33Sub0RealSincDerivMajorantDenominator_pos (k m : Nat) :
    0 < step33Sub0RealSincDerivMajorantDenominator k m := by
  unfold step33Sub0RealSincDerivMajorantDenominator
  exact Nat.mul_pos (by omega) (Nat.factorial_pos _)

/-- The live-term denominator is monotone along the tail. -/
theorem step33Sub0RealSincDerivMajorantDenominator_le_succ (k m : Nat) :
    step33Sub0RealSincDerivMajorantDenominator k m <=
      step33Sub0RealSincDerivMajorantDenominator k (m + 1) := by
  unfold step33Sub0RealSincDerivMajorantDenominator
    step33Sub0RealSincDerivMajorantIndex
  apply Nat.mul_le_mul
  · omega
  · rw [step33Sub0RealSincDerivMajorantExponent_succ]
    exact Nat.factorial_le (by omega)

/-- Consecutive real majorant terms shrink by at least the geometric ratio
`(1/400)^2`. -/
theorem step33Sub0RealSincDerivMajorantTermReal_succ_le_ratio (k m : Nat) :
    step33Sub0RealSincDerivMajorantTermReal k (m + 1) <=
      (((1 : Real) / 400) ^ 2) *
        step33Sub0RealSincDerivMajorantTermReal k m := by
  unfold step33Sub0RealSincDerivMajorantTermReal
  rw [step33Sub0RealSincDerivMajorantExponent_succ]
  rw [pow_add]
  have hnum :
      0 <= (((1 : Real) / 400) ^
          step33Sub0RealSincDerivMajorantExponent k m) *
        (((1 : Real) / 400) ^ 2) := by
    positivity
  have hdenpos :
      0 < (step33Sub0RealSincDerivMajorantDenominator k m : Real) := by
    exact_mod_cast step33Sub0RealSincDerivMajorantDenominator_pos k m
  have hdenle :
      (step33Sub0RealSincDerivMajorantDenominator k m : Real) <=
        (step33Sub0RealSincDerivMajorantDenominator k (m + 1) : Real) := by
    exact_mod_cast step33Sub0RealSincDerivMajorantDenominator_le_succ k m
  have hdiv := div_le_div_of_nonneg_left hnum hdenpos hdenle
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Consecutive rational majorant terms shrink by at least the geometric ratio
`(1/400)^2` after coercion to `Real`. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_succ_le_ratio (k m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm k (m + 1) : Real) <=
      (((1 : Real) / 400) ^ 2) *
        (step33Sub0RealSincDerivMajorantTerm k m : Real) := by
  rw [step33Sub0RealSincDerivMajorantTerm_real_eq,
    step33Sub0RealSincDerivMajorantTerm_real_eq]
  exact step33Sub0RealSincDerivMajorantTermReal_succ_le_ratio k m

/-- The rational majorant terms are nonnegative. -/
theorem step33Sub0RealSincDerivMajorantTerm_nonneg (k m : Nat) :
    0 <= step33Sub0RealSincDerivMajorantTerm k m := by
  unfold step33Sub0RealSincDerivMajorantTerm
  positivity

/-- Real-cast form of `step33Sub0RealSincDerivMajorantTerm_nonneg`. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_nonneg (k m : Nat) :
    0 <= (step33Sub0RealSincDerivMajorantTerm k m : Real) := by
  exact_mod_cast step33Sub0RealSincDerivMajorantTerm_nonneg k m

/-- A shifted live-term tail is bounded termwise by the geometric envelope
with ratio `(1/400)^2`. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_shift_le_geometric
    (k N m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) <=
      (step33Sub0RealSincDerivMajorantTerm k N : Real) *
        (((1 : Real) / 400) ^ 2) ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hratio :
          (step33Sub0RealSincDerivMajorantTerm k (N + (m + 1)) : Real) <=
            (((1 : Real) / 400) ^ 2) *
              (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) := by
        simpa [Nat.add_assoc] using
          step33Sub0RealSincDerivMajorantTerm_real_succ_le_ratio k (N + m)
      have hstep :
          (((1 : Real) / 400) ^ 2) *
              (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) <=
            (((1 : Real) / 400) ^ 2) *
              ((step33Sub0RealSincDerivMajorantTerm k N : Real) *
                (((1 : Real) / 400) ^ 2) ^ m) := by
        exact mul_le_mul_of_nonneg_left ih (by positivity)
      calc
        (step33Sub0RealSincDerivMajorantTerm k (N + (m + 1)) : Real)
            <= (((1 : Real) / 400) ^ 2) *
                (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) := hratio
        _ <= (((1 : Real) / 400) ^ 2) *
              ((step33Sub0RealSincDerivMajorantTerm k N : Real) *
                (((1 : Real) / 400) ^ 2) ^ m) := hstep
        _ = (step33Sub0RealSincDerivMajorantTerm k N : Real) *
              (((1 : Real) / 400) ^ 2) ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- Shifted live-term tails are summable. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_shift_summable
    (k N : Nat) :
    Summable (fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real)) := by
  refine Summable.of_nonneg_of_le
    (f := fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k N : Real) *
        (((1 : Real) / 400) ^ 2) ^ m)
    (g := fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real))
    ?hNonneg ?hLe ?hGeom
  · intro m
    exact step33Sub0RealSincDerivMajorantTerm_real_nonneg k (N + m)
  · intro m
    exact step33Sub0RealSincDerivMajorantTerm_real_shift_le_geometric k N m
  · exact Summable.mul_left (step33Sub0RealSincDerivMajorantTerm k N : Real)
      (summable_geometric_of_lt_one (by positivity) (by norm_num))

/-- Geometric `tsum` bound for the shifted majorant tail. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_tsum_tail_le
    (k N : Nat) :
    (∑' m : Nat,
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real)) <=
      (step33Sub0RealSincDerivMajorantTerm k N : Real) /
        (1 - (((1 : Real) / 400) ^ 2)) := by
  have hShift :=
    step33Sub0RealSincDerivMajorantTerm_real_shift_summable k N
  have hGeom : Summable (fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k N : Real) *
        (((1 : Real) / 400) ^ 2) ^ m) := by
    exact Summable.mul_left (step33Sub0RealSincDerivMajorantTerm k N : Real)
      (summable_geometric_of_lt_one (by positivity) (by norm_num))
  have hsum :
      (∑' m : Nat,
        (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real)) <=
        ∑' m : Nat,
          (step33Sub0RealSincDerivMajorantTerm k N : Real) *
            (((1 : Real) / 400) ^ 2) ^ m := by
    exact Summable.tsum_le_tsum
      (step33Sub0RealSincDerivMajorantTerm_real_shift_le_geometric k N)
      hShift hGeom
  calc
    (∑' m : Nat,
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real))
        <= ∑' m : Nat,
          (step33Sub0RealSincDerivMajorantTerm k N : Real) *
            (((1 : Real) / 400) ^ 2) ^ m := hsum
    _ = (step33Sub0RealSincDerivMajorantTerm k N : Real) *
          (1 - (((1 : Real) / 400) ^ 2))⁻¹ := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by positivity) (by norm_num)]
    _ = (step33Sub0RealSincDerivMajorantTerm k N : Real) /
          (1 - (((1 : Real) / 400) ^ 2)) := by
      simp [div_eq_mul_inv]

/-- Closed form of the row-`0` majorant term. -/
theorem step33Sub0RealSincDerivMajorantTerm_zero_eq (m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm 0 m : Real) =
      (((1 : Real) / 400) ^ (2 * m)) /
        (Nat.factorial (2 * m + 1) : Real) := by
  rw [step33Sub0RealSincDerivMajorantTerm_real_eq]
  unfold step33Sub0RealSincDerivMajorantTermReal
    step33Sub0RealSincDerivMajorantExponent
    step33Sub0RealSincDerivMajorantDenominator
    step33Sub0RealSincDerivMajorantIndex
    step33Sub0RealSincDerivMajorantStart
  norm_num
  rw [show step33Sub0RealSincDerivMajorantExponent 0 m = 2 * m by
    unfold step33Sub0RealSincDerivMajorantExponent
      step33Sub0RealSincDerivMajorantIndex
      step33Sub0RealSincDerivMajorantStart
    norm_num]
  rw [show (2 * m + 1).factorial = (2 * m + 1) * (2 * m).factorial by
    simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using (Nat.factorial_succ (2 * m))]
  norm_num

/-- The absolute row-`0` sinc series term is bounded by the row-`0` majorant
on `0 <= u <= 1/400`. -/
theorem step33Sub0RealSinc_seriesTerm_norm_le_majorant_zero
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400))
    (m : Nat) :
    ‖((-1 : Real) ^ m * u ^ (2 * m) /
        (Nat.factorial (2 * m + 1) : Real))‖ <=
      (step33Sub0RealSincDerivMajorantTerm 0 m : Real) := by
  rw [step33Sub0RealSincDerivMajorantTerm_zero_eq]
  have hu_abs : |u| <= (1 : Real) / 400 := by
    rw [abs_of_nonneg hu.1]
    exact hu.2
  have hpow :
      |u| ^ (2 * m) <= ((1 : Real) / 400) ^ (2 * m) :=
    pow_le_pow_left₀ (abs_nonneg u) hu_abs (2 * m)
  have hden_nonneg :
      0 <= ((Nat.factorial (2 * m + 1) : Real))⁻¹ := by
    positivity
  calc
    ‖((-1 : Real) ^ m * u ^ (2 * m) /
        (Nat.factorial (2 * m + 1) : Real))‖
        = |u| ^ (2 * m) /
            (Nat.factorial (2 * m + 1) : Real) := by
          have hfact_pos :
              0 < (Nat.factorial (2 * m + 1) : Real) := by
            positivity
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
          simp [abs_of_pos hfact_pos, div_eq_mul_inv]
    _ <= ((1 : Real) / 400) ^ (2 * m) /
          (Nat.factorial (2 * m + 1) : Real) := by
          exact mul_le_mul_of_nonneg_right hpow hden_nonneg

/-- Row-`0` analytic crosswalk from the sinc series to the exact majorant
`tsum`.  This closes only the zeroth derivative row. -/
theorem realSinc_norm_le_tsum_majorant_zero
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400)) :
    ‖realSinc u‖ <=
      ∑' m : Nat, (step33Sub0RealSincDerivMajorantTerm 0 m : Real) := by
  let f : Nat -> Real := fun m : Nat =>
    ((-1 : Real) ^ m * u ^ (2 * m)) /
      (Nat.factorial (2 * m + 1) : Real)
  let g : Nat -> Real := fun m : Nat =>
    (step33Sub0RealSincDerivMajorantTerm 0 m : Real)
  have hg : Summable g := by
    simpa [g] using
      step33Sub0RealSincDerivMajorantTerm_real_shift_summable 0 0
  have hfg : ∀ m : Nat, ‖f m‖ <= g m := by
    intro m
    simpa [f, g] using
      step33Sub0RealSinc_seriesTerm_norm_le_majorant_zero hu m
  have hf : Summable (fun m : Nat => ‖f m‖) := by
    refine Summable.of_nonneg_of_le (f := g) (g := fun m : Nat => ‖f m‖)
      ?hNonneg ?hLe hg
    · intro m
      exact norm_nonneg _
    · exact hfg
  have hsum_norm :
      ‖∑' m : Nat, f m‖ <= ∑' m : Nat, ‖f m‖ :=
    norm_tsum_le_tsum_norm hf
  have hsum_le :
      (∑' m : Nat, ‖f m‖) <= ∑' m : Nat, g m :=
    Summable.tsum_le_tsum hfg hf hg
  have hseries : HasSum f (realSinc u) := by
    simpa [f] using realSinc_hasSum_even_powerSeries u
  rw [← hseries.tsum_eq]
  exact le_trans hsum_norm hsum_le

/-- Zeroth-derivative version of the row-`0` analytic crosswalk. -/
theorem realSinc_iteratedDeriv_zero_norm_le_tsum_majorant
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400)) :
    ‖iteratedDeriv 0 realSinc u‖ <=
      ∑' m : Nat, (step33Sub0RealSincDerivMajorantTerm 0 m : Real) := by
  simpa [iteratedDeriv] using realSinc_norm_le_tsum_majorant_zero hu

/-- Finite rational certificate surface for the `realSinc` derivative rows
`k = 0, ..., 17`.

`baseAbs` is the proof-grade row bound intended for
`‖iteratedDeriv k realSinc u‖` on `Set.Icc 0 (1/400)`.  The `Valid` predicate
checks only the rational arithmetic budget: finite prefix plus a geometric
tail allowance. -/
structure Step33Sub0RealSincDerivativeMajorantCert where
  prefixN : Fin 18 -> Nat
  tailAbs : Fin 18 -> Rat
  baseAbs : Fin 18 -> Rat

namespace Step33Sub0RealSincDerivativeMajorantCert

/-- Rational checker obligations for a candidate `realSinc` derivative
majorant certificate.

The geometric ratio `((1/400)^2)` is the intended uniform ratio for consecutive
live terms in the positive absolute series.  The proof that the actual analytic
terms are covered by this rational checker is the current crosswalk gap. -/
structure Valid (data : Step33Sub0RealSincDerivativeMajorantCert) : Prop where
  tailBudget :
    ∀ k : Fin 18,
      step33Sub0RealSincDerivMajorantTerm k.1 (data.prefixN k) /
          (1 - ((1 : Rat) / 400) ^ 2) <=
        data.tailAbs k
  totalBudget :
    ∀ k : Fin 18,
      (∑ m ∈ Finset.range (data.prefixN k),
          step33Sub0RealSincDerivMajorantTerm k.1 m) +
          data.tailAbs k <=
        data.baseAbs k

/-- Explicit marker for the live obstruction.  A proof of this proposition,
together with `Valid`, would feed the existing scaled-sinc receiver in
`PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver.lean`. -/
def ProvidesAnalyticMajorant
    (data : Step33Sub0RealSincDerivativeMajorantCert) : Prop :=
  ∀ u ∈ Set.Icc (0 : Real) ((1 : Real) / 400),
    ∀ k : Fin 18,
      ‖iteratedDeriv k.1 realSinc u‖ <= (data.baseAbs k : Real)

end Step33Sub0RealSincDerivativeMajorantCert

end Step33
end PSDpd
end Q3
