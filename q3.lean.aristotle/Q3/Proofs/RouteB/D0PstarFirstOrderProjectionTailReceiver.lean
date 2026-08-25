import Q3.Proofs.RouteB.D0PstarPhysicalFourierEnergyControl
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option linter.mathlibStandardSet false

open Complex Filter Finset
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# First-order coefficient receiver for the selected projection tail

Ratified by `PROSHKA_VERDICT_GOAL058_W5_FIRST_ORDER_PROJECTION_TAIL_SUPPLIER`
(2026-08-25).  The quadratic physical-energy supplier is generically false on
the literal jump family (R2 preflight, commit f084dc27), so this module
supplies the SAME consumer `SelectedProjectionTailDecay` from a first-order
coefficient envelope `‖c_n‖^2 ≤ C^2 * L_m / n^2` plus the existing cofinal
bandwidth contract.  `SelectedPhysicalFourierEnergyControl` is untouched and
retained as an alternative sufficient supplier only.
-/

/-- Base integer p-series with the Galerkin sector removed. -/
private def w5rTailWeight (i : PairIndex) (n : ℤ) : ℝ :=
  if n ∈ modeSet i then 0 else ((n : ℝ) ^ 2)⁻¹

private theorem w5r_nat_base_summable :
    Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  simpa [one_div] using (summable_one_div_nat_pow (p := 2)).mpr (by norm_num)

private theorem w5r_int_base_summable :
    Summable (fun n : ℤ => ((n : ℝ) ^ 2)⁻¹) := by
  simpa [one_div] using (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)

private theorem w5rTailWeight_nonneg (i : PairIndex) (n : ℤ) :
    0 ≤ w5rTailWeight i n := by
  unfold w5rTailWeight
  split <;> positivity

private theorem w5rTailWeight_le_base (i : PairIndex) (n : ℤ) :
    w5rTailWeight i n ≤ ((n : ℝ) ^ 2)⁻¹ := by
  unfold w5rTailWeight
  split
  · positivity
  · exact le_rfl

private theorem w5rTailWeight_summable (i : PairIndex) :
    Summable (w5rTailWeight i) :=
  Summable.of_nonneg_of_le (w5rTailWeight_nonneg i)
    (w5rTailWeight_le_base i) w5r_int_base_summable

/-- The one-sided natural tail with the sector removed. -/
private def w5rNatTail (N : ℕ) (n : ℕ) : ℝ :=
  if n ≤ N then 0 else ((n : ℝ) ^ 2)⁻¹

private theorem w5rNatTail_nonneg (N n : ℕ) : 0 ≤ w5rNatTail N n := by
  unfold w5rNatTail
  split <;> positivity

private theorem w5rNatTail_summable (N : ℕ) :
    Summable (w5rNatTail N) := by
  refine Summable.of_nonneg_of_le (w5rNatTail_nonneg N)
    (fun n => ?_) w5r_nat_base_summable
  unfold w5rNatTail
  split
  · positivity
  · exact le_rfl

/-- The classical telescoping tail bound, `tsum` form. -/
private theorem w5rNatTail_tsum_le (N : ℕ) :
    ∑' n : ℕ, w5rNatTail N n ≤ 2 / ((N : ℝ) + 1) := by
  refine (w5rNatTail_summable N).tsum_le_of_sum_le ?_
  intro s
  have hsub : s.filter (fun n => ¬ n ≤ N) ⊆ Finset.Ioo N (s.sup id + 1) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hnN⟩
    refine Finset.mem_Ioo.mpr ⟨by omega, ?_⟩
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hns
    omega
  calc
    ∑ n ∈ s, w5rNatTail N n
        = ∑ n ∈ s.filter (fun n => ¬ n ≤ N), ((n : ℝ) ^ 2)⁻¹ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          unfold w5rNatTail
          by_cases h : n ≤ N <;> simp [h]
    _ ≤ ∑ n ∈ Finset.Ioo N (s.sup id + 1), ((n : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => by positivity)
    _ ≤ 2 / ((N : ℝ) + 1) := by
          simpa using sum_Ioo_inv_sq_le (α := ℝ) N (s.sup id + 1)

private theorem w5rTailWeight_nat_eq (i : PairIndex) (n : ℕ) :
    w5rTailWeight i (n : ℤ) = w5rNatTail i.N n := by
  unfold w5rTailWeight w5rNatTail
  have hmem : ((n : ℤ) ∈ modeSet i) ↔ n ≤ i.N := by
    simp only [modeSet, Finset.mem_Icc]
    omega
  by_cases h : n ≤ i.N
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hx => h (hmem.mp hx)), if_neg h]
    norm_cast

private theorem w5rTailWeight_neg_eq (i : PairIndex) (n : ℕ) :
    w5rTailWeight i (-((n : ℤ) + 1)) = w5rNatTail i.N (n + 1) := by
  unfold w5rTailWeight w5rNatTail
  have hmem : ((-((n : ℤ) + 1)) ∈ modeSet i) ↔ n + 1 ≤ i.N := by
    simp only [modeSet, Finset.mem_Icc]
    omega
  by_cases h : n + 1 ≤ i.N
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hx => h (hmem.mp hx)), if_neg h]
    congr 1
    push_cast
    ring

/-- Two-sided integer tail bound at the sharp first-omitted-mode scale. -/
private theorem w5rTailWeight_tsum_le (i : PairIndex) :
    ∑' n : ℤ, w5rTailWeight i n ≤ 4 / ((i.N : ℝ) + 1) := by
  have hnat : Summable (fun n : ℕ => w5rTailWeight i (n : ℤ)) := by
    refine (w5rNatTail_summable i.N).congr ?_
    intro n
    exact (w5rTailWeight_nat_eq i n).symm
  have hshift : Summable (fun n : ℕ => w5rNatTail i.N (n + 1)) :=
    (summable_nat_add_iff 1).mpr (w5rNatTail_summable i.N)
  have hneg : Summable (fun n : ℕ => w5rTailWeight i (-((n : ℤ) + 1))) := by
    refine hshift.congr ?_
    intro n
    exact (w5rTailWeight_neg_eq i n).symm
  have hsplit :
      ∑' n : ℤ, w5rTailWeight i n =
        (∑' n : ℕ, w5rTailWeight i (n : ℤ)) +
          ∑' n : ℕ, w5rTailWeight i (-((n : ℤ) + 1)) := by
    simpa using tsum_of_nat_of_neg_add_one hnat hneg
  have hnat_le : (∑' n : ℕ, w5rTailWeight i (n : ℤ)) ≤ 2 / ((i.N : ℝ) + 1) := by
    calc
      (∑' n : ℕ, w5rTailWeight i (n : ℤ))
          = ∑' n : ℕ, w5rNatTail i.N n :=
            tsum_congr (w5rTailWeight_nat_eq i)
      _ ≤ 2 / ((i.N : ℝ) + 1) := w5rNatTail_tsum_le i.N
  have hneg_le :
      (∑' n : ℕ, w5rTailWeight i (-((n : ℤ) + 1))) ≤ 2 / ((i.N : ℝ) + 1) := by
    have hshift_le :
        (∑' n : ℕ, w5rNatTail i.N (n + 1)) ≤ 2 / ((i.N : ℝ) + 1) := by
      have hzero : w5rNatTail i.N 0 = 0 := by
        unfold w5rNatTail
        simp
      have hz :=
        (w5rNatTail_summable i.N).tsum_eq_zero_add
      have : (∑' n : ℕ, w5rNatTail i.N (n + 1)) = ∑' n : ℕ, w5rNatTail i.N n := by
        rw [hz, hzero, zero_add]
      rw [this]
      exact w5rNatTail_tsum_le i.N
    calc
      (∑' n : ℕ, w5rTailWeight i (-((n : ℤ) + 1)))
          = ∑' n : ℕ, w5rNatTail i.N (n + 1) :=
            tsum_congr (w5rTailWeight_neg_eq i)
      _ ≤ 2 / ((i.N : ℝ) + 1) := hshift_le
  calc
    ∑' n : ℤ, w5rTailWeight i n
        = (∑' n : ℕ, w5rTailWeight i (n : ℤ)) +
            ∑' n : ℕ, w5rTailWeight i (-((n : ℤ) + 1)) := hsplit
    _ ≤ 2 / ((i.N : ℝ) + 1) + 2 / ((i.N : ℝ) + 1) :=
          add_le_add hnat_le hneg_le
    _ = 4 / ((i.N : ℝ) + 1) := by ring

/--
The ratified generic first-order receiver: a first-order coefficient envelope
on the omitted modes plus cofinal physical bandwidth imply the literal
selected projection-tail decay.  `SelectedPhysicalFourierEnergyControl` is
not required and its `n^2` weights are untouched.
-/
theorem selectedProjectionTailDecay_of_firstOrderCoefficientBudgetAndBandwidth
    (S : ProlateCanonicalSourceData)
    (hCoeff : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k : ℕ in atTop,
        ∀ n : ℤ, n ∉ modeSet (selectedPairIndex S k) →
          ‖physicalFourierCoefficient (selectedPairIndex S k)
              (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
                (S.source.eStar_memLp (selectedPairIndex S k))) n‖ ^ 2 ≤
            C ^ 2 * L_m (selectedPairIndex S k) / (n : ℝ) ^ 2)
    (hBandwidth : SelectedPhysicalBandwidthCofinal S) :
    SelectedProjectionTailDecay S := by
  obtain ⟨C, hC0, hEv⟩ := hCoeff
  have hres_sq : ∀ᶠ k : ℕ in atTop,
      selectedUnnormalizedGalerkinResidualNorm S k ^ 2 ≤
        8 * Real.pi * C ^ 2 *
          (physicalFourierBandwidth (selectedPairIndex S k))⁻¹ := by
    refine hEv.mono ?_
    intro k hk
    set i := selectedPairIndex S k with hi
    set f := gTrial_m i (selectedProlateTrial S k) (S.source.eStar_memLp i)
      with hf
    have hL : 0 < L_m i := logLength_pos i
    have hN1 : (0 : ℝ) < (i.N : ℝ) + 1 := by positivity
    have hparseval :
        selectedUnnormalizedGalerkinResidualNorm S k ^ 2 =
          ∑' n : ℤ,
            if n ∈ modeSet i then 0
            else ‖inner ℂ (V_n_m i n) f‖ ^ 2 := by
      have h0 := norm_sub_coe_P_m_N_sq_eq_tsum_complement i f
      simpa [selectedUnnormalizedGalerkinResidualNorm, gTrial_m_N,
        norm_sub_rev, hi, hf] using h0
    have hpoint : ∀ n : ℤ,
        (if n ∈ modeSet i then 0 else ‖inner ℂ (V_n_m i n) f‖ ^ 2) ≤
          C ^ 2 * L_m i * w5rTailWeight i n := by
      intro n
      unfold w5rTailWeight
      by_cases h : n ∈ modeSet i
      · simp [h]
      · have hcn := hk n h
        simp only [h, if_false]
        calc
          ‖inner ℂ (V_n_m i n) f‖ ^ 2 ≤
              C ^ 2 * L_m i / (n : ℝ) ^ 2 := by
                simpa [physicalFourierCoefficient, hi, hf] using hcn
          _ = C ^ 2 * L_m i * ((n : ℝ) ^ 2)⁻¹ := by
                rw [div_eq_mul_inv]
    have hmaj_summable :
        Summable (fun n : ℤ => C ^ 2 * L_m i * w5rTailWeight i n) :=
      (w5rTailWeight_summable i).mul_left _
    have hlhs_summable :
        Summable (fun n : ℤ =>
          if n ∈ modeSet i then (0 : ℝ)
          else ‖inner ℂ (V_n_m i n) f‖ ^ 2) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) hpoint hmaj_summable
      split <;> positivity
    have htail :
        selectedUnnormalizedGalerkinResidualNorm S k ^ 2 ≤
          C ^ 2 * L_m i * (4 / ((i.N : ℝ) + 1)) := by
      calc
        selectedUnnormalizedGalerkinResidualNorm S k ^ 2
            = ∑' n : ℤ,
                if n ∈ modeSet i then 0
                else ‖inner ℂ (V_n_m i n) f‖ ^ 2 := hparseval
        _ ≤ ∑' n : ℤ, C ^ 2 * L_m i * w5rTailWeight i n :=
              Summable.tsum_le_tsum hpoint hlhs_summable hmaj_summable
        _ = C ^ 2 * L_m i * ∑' n : ℤ, w5rTailWeight i n := tsum_mul_left
        _ ≤ C ^ 2 * L_m i * (4 / ((i.N : ℝ) + 1)) := by
              have hcl : 0 ≤ C ^ 2 * L_m i := by positivity
              exact mul_le_mul_of_nonneg_left (w5rTailWeight_tsum_le i) hcl
    have hconvert :
        C ^ 2 * L_m i * (4 / ((i.N : ℝ) + 1)) =
          8 * Real.pi * C ^ 2 * (physicalFourierBandwidth i)⁻¹ := by
      simp only [physicalFourierBandwidth]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    calc
      selectedUnnormalizedGalerkinResidualNorm S k ^ 2 ≤
          C ^ 2 * L_m i * (4 / ((i.N : ℝ) + 1)) := htail
      _ = 8 * Real.pi * C ^ 2 * (physicalFourierBandwidth i)⁻¹ := hconvert
  have hmaj_zero : Tendsto
      (fun k : ℕ =>
        8 * Real.pi * C ^ 2 *
          (physicalFourierBandwidth (selectedPairIndex S k))⁻¹)
      atTop (𝓝 0) := by
    have hinv : Tendsto
        (fun k : ℕ =>
          (physicalFourierBandwidth (selectedPairIndex S k))⁻¹)
        atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hBandwidth
    have := hinv.const_mul (8 * Real.pi * C ^ 2)
    simpa using this
  have hsq : Tendsto
      (fun k : ℕ => selectedUnnormalizedGalerkinResidualNorm S k ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero'
      (Eventually.of_forall fun k => sq_nonneg _) hres_sq hmaj_zero
  have hsqrt := hsq.sqrt
  simpa [SelectedProjectionTailDecay, selectedUnnormalizedGalerkinResidualNorm,
    Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt

#print axioms selectedProjectionTailDecay_of_firstOrderCoefficientBudgetAndBandwidth

end Q3.RouteB.D0Pstar
