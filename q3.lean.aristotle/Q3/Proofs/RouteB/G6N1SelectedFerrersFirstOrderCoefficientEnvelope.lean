import Q3.Proofs.RouteB.G6N1SelectedFerrersFixedKShiftedRootEnergy
import Q3.Proofs.RouteB.G6N1SelectedFerrersQuantitativeShiftedRootEnergy
import Q3.Proofs.RouteB.D0PstarPhysicalFourierEnergyControl

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 800000

open Complex Filter MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# First-order physical coefficient envelope on the W3 Abel-limit vector

Ratified route (verdict aea49e0f): the generic projection-tail receiver
consumes an envelope `‖c_n‖^2 ≤ C^2 * L_m / n^2`.  This node proves the
exact coefficient crosswalk `inner(V_n, x) = L^{-1/2} * 𝓕(zeroExt x)(n/L)`
for every `H_m` vector, and instantiates it on the W3 selected Abel-limit
vector via the committed W4 quantitative Fourier decay.  The remaining
distance from `selectedFerrersAbelLimitHm` to the production `gTrial_m`
(midpoint correction and family crosswalk) is NOT claimed here.
-/

/-- Local reconstruction of the upstream private additive-mode membership. -/
private theorem w5c_additiveMode_memLp (i : PairIndex) (n : ℤ) :
    MemLp
      (fun x : ℝ =>
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * (x / L_m i)))
      2 (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  letI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  apply MemLp.of_bound
    ((Continuous.aestronglyMeasurable (by fun_prop)))
    ((Real.sqrt (L_m i))⁻¹)
  filter_upwards [] with x
  rw [norm_mul]
  have h1 : ‖((Real.sqrt (L_m i))⁻¹ : ℂ)‖ = (Real.sqrt (L_m i))⁻¹ := by
    have hcast : ((Real.sqrt (L_m i))⁻¹ : ℂ) =
        (((Real.sqrt (L_m i))⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * n * (x / L_m i))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * n * (x / L_m i)).re = 0 := by
      have hcast :
          (2 * Real.pi * Complex.I * n * (x / L_m i) : ℂ) =
            Complex.I * ((2 * Real.pi * n * (x / L_m i) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast]
      simp [Complex.mul_re]
    rw [hre]
    exact Real.exp_zero
  rw [h1, h2, mul_one]

/-- The additive-window mode class (local reconstruction). -/
private def w5c_additiveModeLp (i : PairIndex) (n : ℤ) :
    MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
  (w5c_additiveMode_memLp i n).toLp _

/-- The additive window unitary sends the additive mode class to the
literal production mode (local reconstruction of the upstream private). -/
private theorem w5c_logWindowL2Equiv_additiveModeLp
    (i : PairIndex) (n : ℤ) :
    logWindowL2Equiv i (w5c_additiveModeLp i n) = V_n_m i n := by
  apply MeasureTheory.Lp.ext
  have hcoe := coeFn_logWindowL2Equiv i (w5c_additiveModeLp i n)
  have hmode := MemLp.coeFn_toLp (w5c_additiveMode_memLp i n)
  have hVcoe :
      ((V_n_m i n : H_m i) : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    exact MemLp.coeFn_toLp _
  have hcomp := hmode.comp_tendsto
    (sourceLogWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcoe, hVcoe, hcomp] with u hu hV hcm
  rw [hu, hV]
  simpa using hcm

private theorem w5c_symm_V_n_m (i : PairIndex) (n : ℤ) :
    (logWindowL2Equiv i).symm (V_n_m i n) = w5c_additiveModeLp i n := by
  rw [← w5c_logWindowL2Equiv_additiveModeLp i n]
  exact (logWindowL2Equiv i).symm_apply_apply _

/-- Fourier integral is blind to a.e. modification (local reconstruction). -/
private theorem w5c_fourier_congr_ae
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) (t : ℝ) :
    𝓕 f t = 𝓕 g t := by
  rw [Real.fourier_eq', Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/--
**The exact first-order coefficient crosswalk.**  For every vector of the
literal carrier, the physical Fourier coefficient against `V_n_m` is the
ordinary whole-line Fourier integral of its additive log-window zero
extension at the lattice frequency `n / L_m`, scaled by `(√L_m)⁻¹`.
-/
theorem physicalFourierCoefficient_eq_fourier_sourceLogWindowZeroExtension
    (i : PairIndex) (x : H_m i) (n : ℤ) :
    physicalFourierCoefficient i x n =
      ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        𝓕 (sourceLogWindowZeroExtension i x) ((n : ℝ) / L_m i) := by
  have hL : 0 < L_m i := logLength_pos i
  set y := (logWindowL2Equiv i).symm x with hy
  have hxy : logWindowL2Equiv i y = x :=
    (logWindowL2Equiv i).apply_symm_apply x
  have hinner :
      physicalFourierCoefficient i x n =
        inner ℂ (w5c_additiveModeLp i n) y := by
    rw [physicalFourierCoefficient, ← hxy,
      ← w5c_logWindowL2Equiv_additiveModeLp i n,
      LinearIsometryEquiv.inner_map_map]
  rw [hinner, MeasureTheory.L2.inner_def]
  have hmode :
      (w5c_additiveModeLp i n : ℝ → ℂ)
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))]
      (fun x : ℝ =>
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * (x / L_m i))) :=
    MemLp.coeFn_toLp (w5c_additiveMode_memLp i n)
  have hpoint :
      (fun z : ℝ =>
          (inner ℂ ((w5c_additiveModeLp i n : ℝ → ℂ) z) ((y : ℝ → ℂ) z) : ℂ))
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))]
      (fun z : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            (Complex.exp (-(2 * Real.pi * Complex.I * n * (z / L_m i))) *
              (y : ℝ → ℂ) z)) := by
    filter_upwards [hmode] with z hz
    rw [RCLike.inner_apply, hz]
    rw [map_mul, ← Complex.exp_conj]
    have hconj1 :
        (starRingEnd ℂ) ((Real.sqrt (L_m i))⁻¹ : ℂ) =
          ((Real.sqrt (L_m i))⁻¹ : ℂ) := by
      have hcast : ((Real.sqrt (L_m i))⁻¹ : ℂ) =
          (((Real.sqrt (L_m i))⁻¹ : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.conj_ofReal]
    have hconj2 :
        (starRingEnd ℂ) (2 * Real.pi * Complex.I * n * (z / L_m i)) =
          -(2 * Real.pi * Complex.I * n * (z / L_m i)) := by
      have hcast :
          (2 * Real.pi * Complex.I * n * (z / L_m i) : ℂ) =
            Complex.I * ((2 * Real.pi * n * (z / L_m i) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj1, hconj2]
    ring
  rw [integral_congr_ae hpoint, integral_const_mul]
  congr 1
  have hindicator :
      ∫ z in Set.Icc (0 : ℝ) (L_m i),
          Complex.exp (-(2 * Real.pi * Complex.I * n * (z / L_m i))) *
            (y : ℝ → ℂ) z ∂volume =
        ∫ z : ℝ,
          Set.indicator (Set.Icc (0 : ℝ) (L_m i))
            (fun w : ℝ =>
              Complex.exp (-(2 * Real.pi * Complex.I * n * (w / L_m i))) *
                (y : ℝ → ℂ) w) z ∂volume := by
    rw [integral_indicator measurableSet_Icc]
  rw [hindicator]
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with z
  have harg :
      ((↑(-2 * Real.pi * (inner ℝ z ((n : ℝ) / L_m i) : ℝ)) : ℂ) *
          Complex.I) =
        -(2 * Real.pi * Complex.I * (n : ℂ) * ((z : ℂ) / ((L_m i : ℝ) : ℂ))) := by
    have hip : (inner ℝ z ((n : ℝ) / L_m i) : ℝ) = ((n : ℝ) / L_m i) * z := by
      simp [RCLike.inner_apply]
    rw [hip]
    push_cast
    ring
  by_cases hmem : z ∈ Set.Icc (0 : ℝ) (L_m i)
  · rw [Set.indicator_of_mem hmem, smul_eq_mul]
    unfold sourceLogWindowZeroExtension
    rw [Set.indicator_of_mem hmem, ← hy, harg]
  · rw [Set.indicator_of_notMem hmem]
    unfold sourceLogWindowZeroExtension
    rw [Set.indicator_of_notMem hmem, smul_zero]

/--
**W4-fed first-order envelope on the W3 Abel-limit vector.**  For every
selected `k` and every nonzero integer mode, the physical coefficient of
`selectedFerrersAbelLimitHm` obeys the exact receiver envelope with
constant `selectedFerrersAbelFourierDecayBudget k`.
-/
theorem selectedFerrersAbelLimitHm_physicalCoefficient_sq_le
    (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖physicalFourierCoefficient (selectedFerrersPreAnchorIndex k)
        (selectedFerrersAbelLimitHm k) n‖ ^ 2 ≤
      selectedFerrersAbelFourierDecayBudget k ^ 2 *
        L_m (selectedFerrersPreAnchorIndex k) / (n : ℝ) ^ 2 := by
  set i := selectedFerrersPreAnchorIndex k with hi
  have hL : 0 < L_m i := logLength_pos i
  have hB := selectedFerrersAbelFourierDecayBudget_nonneg k
  set B := selectedFerrersAbelFourierDecayBudget k with hBdef
  have hnabs : (0 : ℝ) < |(n : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hn
  have hident :=
    physicalFourierCoefficient_eq_fourier_sourceLogWindowZeroExtension
      i (selectedFerrersAbelLimitHm k) n
  have hswap :
      𝓕 (sourceLogWindowZeroExtension i (selectedFerrersAbelLimitHm k))
          ((n : ℝ) / L_m i) =
        𝓕 (selectedFerrersAbelLogZeroExtension k) ((n : ℝ) / L_m i) :=
    w5c_fourier_congr_ae
      (sourceLogWindowZeroExtension_selectedFerrersAbelLimitHm_ae k) _
  have hdecay :=
    selectedFerrersAbelLogZeroExtension_fourier_decay_quantitative
      k ((n : ℝ) / L_m i)
  have hnorm :
      ‖physicalFourierCoefficient i (selectedFerrersAbelLimitHm k) n‖ ≤
        (Real.sqrt (L_m i))⁻¹ * (B / (1 + |(n : ℝ) / L_m i|)) := by
    rw [hident, hswap, norm_mul]
    have hcoef : ‖((Real.sqrt (L_m i))⁻¹ : ℂ)‖ = (Real.sqrt (L_m i))⁻¹ := by
      have hcast : ((Real.sqrt (L_m i))⁻¹ : ℂ) =
          (((Real.sqrt (L_m i))⁻¹ : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      positivity
    rw [hcoef]
    have hsqrtpos : (0 : ℝ) < (Real.sqrt (L_m i))⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hdecay hsqrtpos.le
  have htail : (Real.sqrt (L_m i))⁻¹ * (B / (1 + |(n : ℝ) / L_m i|)) ≤
      B * Real.sqrt (L_m i) / |(n : ℝ)| := by
    have habs : |(n : ℝ) / L_m i| = |(n : ℝ)| / L_m i := by
      rw [abs_div, abs_of_pos hL]
    have hstep : 1 + |(n : ℝ) / L_m i| ≥ |(n : ℝ)| / L_m i := by
      rw [habs]
      linarith
    have hfracpos : (0 : ℝ) < |(n : ℝ)| / L_m i := by positivity
    have hinv : (1 + |(n : ℝ) / L_m i|)⁻¹ ≤ L_m i / |(n : ℝ)| := by
      rw [ge_iff_le] at hstep
      have := inv_anti₀ hfracpos hstep
      rwa [inv_div] at this
    calc
      (Real.sqrt (L_m i))⁻¹ * (B / (1 + |(n : ℝ) / L_m i|))
          = (Real.sqrt (L_m i))⁻¹ * B * (1 + |(n : ℝ) / L_m i|)⁻¹ := by
            rw [div_eq_mul_inv]
            ring
      _ ≤ (Real.sqrt (L_m i))⁻¹ * B * (L_m i / |(n : ℝ)|) := by
            apply mul_le_mul_of_nonneg_left hinv
            positivity
      _ = B * (L_m i / Real.sqrt (L_m i)) / |(n : ℝ)| := by
            ring
      _ = B * Real.sqrt (L_m i) / |(n : ℝ)| := by
            rw [Real.div_sqrt]
  have hfinal :
      ‖physicalFourierCoefficient i (selectedFerrersAbelLimitHm k) n‖ ≤
        B * Real.sqrt (L_m i) / |(n : ℝ)| := hnorm.trans htail
  have hnn : (0 : ℝ) ≤ ‖physicalFourierCoefficient i
      (selectedFerrersAbelLimitHm k) n‖ := norm_nonneg _
  calc
    ‖physicalFourierCoefficient i (selectedFerrersAbelLimitHm k) n‖ ^ 2
        ≤ (B * Real.sqrt (L_m i) / |(n : ℝ)|) ^ 2 := by
          apply sq_le_sq' _ hfinal
          have : (0 : ℝ) ≤ B * Real.sqrt (L_m i) / |(n : ℝ)| := by positivity
          linarith
    _ = B ^ 2 * L_m i / (n : ℝ) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hL.le, sq_abs]

#print axioms physicalFourierCoefficient_eq_fourier_sourceLogWindowZeroExtension
#print axioms selectedFerrersAbelLimitHm_physicalCoefficient_sq_le

end Q3.RouteB.D0Pstar
