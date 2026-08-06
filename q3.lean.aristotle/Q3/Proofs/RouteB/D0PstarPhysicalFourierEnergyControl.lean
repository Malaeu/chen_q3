import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
import Q3.Proofs.RouteB.D0PstarGalerkinResidualDecay
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Ring.Lemmas

set_option linter.mathlibStandardSet false

open Complex Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Physical Fourier-energy control of the selected Galerkin residual

This module converts the abstract weighted Hilbert-basis tail estimate into
the literal physical-frequency scale of the logarithmic window.  It then
provides the conditional selected-path receiver from two independent
suppliers: bounded physical energy and cofinal physical bandwidth.
-/

/-- Physical angular frequency of the literal log-window Fourier mode. -/
def physicalFourierFrequency
    (i : PairIndex) (n : ℤ) : ℝ :=
  (2 * Real.pi * (n : ℝ)) / L_m i

/-- Order-one physical Fourier weight. -/
def physicalFourierWeight
    (i : PairIndex) (n : ℤ) : ℝ :=
  |physicalFourierFrequency i n| ^ 2

/-- Literal Phase-4D coefficient orientation: basis vector in the first slot. -/
def physicalFourierCoefficient
    (i : PairIndex) (f : H_m i) (n : ℤ) : ℂ :=
  inner ℂ (V_n_m i n) f

/-- Physical order-one coefficient energy of a vector in the literal carrier. -/
noncomputable def physicalFourierEnergy
    (i : PairIndex) (f : H_m i) : ℝ :=
  ∑' n : ℤ,
    physicalFourierWeight i n *
      ‖physicalFourierCoefficient i f n‖ ^ 2

/-- First omitted physical angular frequency. -/
def physicalFourierBandwidth
    (i : PairIndex) : ℝ :=
  (2 * Real.pi * ((i.N + 1 : ℕ) : ℝ)) / L_m i

/--
Physical energy of the literal full source object, on the existing
`parent ∘ extract` path.
-/
noncomputable def selectedPhysicalFourierEnergy
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  physicalFourierEnergy i (gTrial_m i h hLp)

/--
Independent selected-energy contract: each physical coefficient row is
summable, and the resulting energies are eventually bounded.
-/
def SelectedPhysicalFourierEnergyControl
    (S : ProlateCanonicalSourceData) : Prop :=
  (∀ k : ℕ,
    let i := selectedPairIndex S k
    let h := selectedProlateTrial S k
    let hLp := S.source.eStar_memLp i
    Summable
      (fun n : ℤ =>
        physicalFourierWeight i n *
          ‖physicalFourierCoefficient
              i (gTrial_m i h hLp) n‖ ^ 2)) ∧
  IsBoundedUnder (· ≤ ·) atTop
    (norm ∘ selectedPhysicalFourierEnergy S)

/-- The first omitted physical frequency tends to infinity on the frozen path. -/
def SelectedPhysicalBandwidthCofinal
    (S : ProlateCanonicalSourceData) : Prop :=
  Tendsto
    (fun k : ℕ =>
      physicalFourierBandwidth (selectedPairIndex S k))
    atTop
    atTop

private theorem physicalFourierBandwidth_pos
    (i : PairIndex) :
    0 < physicalFourierBandwidth i := by
  have hL : 0 < L_m i := logLength_pos i
  simp only [physicalFourierBandwidth]
  positivity

private theorem physicalFourierBandwidth_inv_sq_eq
    (i : PairIndex) :
    ((physicalFourierBandwidth i)⁻¹) ^ 2 =
      (L_m i /
        (2 * Real.pi * ((i.N + 1 : ℕ) : ℝ))) ^ 2 := by
  have hL : 0 < L_m i := logLength_pos i
  simp only [physicalFourierBandwidth]
  field_simp [hL.ne', Real.pi_ne_zero]

private theorem one_le_bandwidth_inv_sq_mul_physicalWeight_of_not_mem_modeSet
    (i : PairIndex) (n : ℤ)
    (hn : n ∉ modeSet i) :
    1 ≤
      ((physicalFourierBandwidth i)⁻¹) ^ 2 *
        physicalFourierWeight i n := by
  have hL : 0 < L_m i := logLength_pos i
  have hnmem : ¬ (-(i.N : ℤ) ≤ n ∧ n ≤ (i.N : ℤ)) := by
    simpa [modeSet, Finset.mem_Icc] using hn
  have houtside : n ≤ -(i.N : ℤ) - 1 ∨ (i.N : ℤ) + 1 ≤ n := by
    omega
  have hint : (i.N : ℤ) + 1 ≤ |n| := by
    rcases houtside with hleft | hright
    · rw [abs_of_nonpos (by omega)]
      omega
    · rw [abs_of_nonneg (by omega)]
      exact hright
  have hreal : ((i.N + 1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast hint
  have hden : 0 < ((i.N + 1 : ℕ) : ℝ) := by positivity
  have hratio : 1 ≤ |(n : ℝ)| / ((i.N + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hden]
    simpa using hreal
  have hsq : 1 ≤ (|(n : ℝ)| / ((i.N + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (|(n : ℝ)| / ((i.N + 1 : ℕ) : ℝ) - 1)]
  calc
    1 ≤ (|(n : ℝ)| / ((i.N + 1 : ℕ) : ℝ)) ^ 2 := hsq
    _ = ((physicalFourierBandwidth i)⁻¹) ^ 2 *
          physicalFourierWeight i n := by
      simp only [physicalFourierBandwidth, physicalFourierWeight,
        physicalFourierFrequency]
      rw [abs_div, abs_mul, abs_mul]
      simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos, abs_of_pos hL]
      field_simp [hL.ne', Real.pi_ne_zero]

/--
The exact finite Galerkin residual is controlled by the physical order-one
coefficient energy at the sharp first-omitted-mode scale.
-/
theorem norm_sub_coe_P_m_N_sq_le_bandwidth_inv_sq_mul_physicalFourierEnergy
    (i : PairIndex) (f : H_m i)
    (hsum :
      Summable
        (fun n : ℤ =>
          physicalFourierWeight i n *
            ‖physicalFourierCoefficient i f n‖ ^ 2)) :
    ‖f - (P_m_N i f : H_m i)‖ ^ 2 ≤
      ((physicalFourierBandwidth i)⁻¹) ^ 2 *
        physicalFourierEnergy i f := by
  have hsum' : Summable (fun n : ℤ =>
      physicalFourierWeight i n *
        ‖inner ℂ (V_n_m_hilbertBasis i n) f‖ ^ 2) := by
    simpa [physicalFourierCoefficient, V_n_m_hilbertBasis_apply] using hsum
  rw [coe_P_m_N_apply_eq_sum_inner_V_n_m_smul]
  simpa [physicalFourierCoefficient, V_n_m_hilbertBasis_apply,
    physicalFourierEnergy] using
    norm_sub_basisPartialSum_sq_le_weightedEnergy
      (V_n_m_hilbertBasis i)
      (modeSet i)
      f
      (((physicalFourierBandwidth i)⁻¹) ^ 2)
      (physicalFourierWeight i)
      (sq_nonneg _)
      (fun n => sq_nonneg _)
      (one_le_bandwidth_inv_sq_mul_physicalWeight_of_not_mem_modeSet i)
      hsum'

set_option maxHeartbeats 800000

/--
Bounded selected physical energies and diverging physical bandwidth imply
the already-defined literal selected projection-tail decay.
-/
theorem selectedProjectionTailDecay_of_physicalFourierEnergyControl
    (S : ProlateCanonicalSourceData)
    (hEnergy : SelectedPhysicalFourierEnergyControl S)
    (hBandwidth : SelectedPhysicalBandwidthCofinal S) :
    SelectedProjectionTailDecay S := by
  have hfactor : Tendsto
      (fun k =>
        ((physicalFourierBandwidth (selectedPairIndex S k))⁻¹) ^ 2)
      atTop (𝓝 0) := by
    have hinv : Tendsto
        (fun k =>
          (physicalFourierBandwidth (selectedPairIndex S k))⁻¹)
        atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hBandwidth
    have hinvSq := hinv.pow 2
    norm_num at hinvSq
    simpa only [inv_pow] using hinvSq
  have hproduct : Tendsto
      (fun k =>
        ((physicalFourierBandwidth (selectedPairIndex S k))⁻¹) ^ 2 *
          selectedPhysicalFourierEnergy S k)
      atTop (𝓝 0) := by
    have hmul := Filter.isBoundedUnder_le_mul_tendsto_zero hEnergy.2 hfactor
    simpa only [Function.comp_def, mul_comm] using hmul
  have hresidualSq (k : ℕ) :
      selectedUnnormalizedGalerkinResidualNorm S k ^ 2 ≤
        ((physicalFourierBandwidth (selectedPairIndex S k))⁻¹) ^ 2 *
          selectedPhysicalFourierEnergy S k := by
    let i := selectedPairIndex S k
    let h := selectedProlateTrial S k
    let hLp := S.source.eStar_memLp i
    have hsum : Summable (fun n : ℤ =>
        physicalFourierWeight i n *
          ‖physicalFourierCoefficient i (gTrial_m i h hLp) n‖ ^ 2) := by
      simpa [i, h, hLp] using hEnergy.1 k
    have htail :=
      norm_sub_coe_P_m_N_sq_le_bandwidth_inv_sq_mul_physicalFourierEnergy
        i (gTrial_m i h hLp) hsum
    simpa [selectedUnnormalizedGalerkinResidualNorm,
      selectedPhysicalFourierEnergy, i, h, hLp, gTrial_m_N,
      norm_sub_rev] using htail
  have hsq : Tendsto
      (fun k => selectedUnnormalizedGalerkinResidualNorm S k ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero'
      (Eventually.of_forall fun k => sq_nonneg _)
      (Eventually.of_forall hresidualSq)
      hproduct
  have hsqrt := hsq.sqrt
  simpa [SelectedProjectionTailDecay, selectedUnnormalizedGalerkinResidualNorm,
    Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt

#print axioms norm_sub_coe_P_m_N_sq_le_bandwidth_inv_sq_mul_physicalFourierEnergy
#print axioms selectedProjectionTailDecay_of_physicalFourierEnergyControl

end Q3.RouteB.D0Pstar
