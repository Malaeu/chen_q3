import Q3.Proofs.RouteB.G6N1SelectedFerrersW5RateAssembly
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000

open Complex Filter Finset MeasureTheory
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Goal 058 — N2 pre-anchor source-scaled Mellin projection-tail rate

Verdict `REQ-2026-08-26-J`: the N2 consumer is the source-scale-weighted
UNNORMALIZED projection residual on the literal pre-anchor Ferrers family.
The finite trial normalizer cancels exactly; no scale upper bound, no
inverse-scale bound, no family crosswalk and no subsequence enter.

Route:
1. exact scalar homogeneity `sourceScale • gTrial = selectedFerrersEStarHm`;
2. the same scalar commutes through the literal Galerkin projection, so the
   scaled projection residual IS the projection residual of
   `selectedFerrersEStarHm`;
3. public first-order coefficient envelope for `selectedFerrersEStarHm`,
   the public Abel-budget rate export and the F72.6 center rate give the
   eventual coefficient constant `A_k = AF·(k+2)^{1/4}·√(log(k+2)+2) + Cp/(4π)`;
4. Parseval plus the two-sided `1/n²` omitted-mode tail give
   `‖P_kE_k−E_k‖² ≤ 4·A_k²·L_k/(k+3)`;
5. the moving-window kernel envelope `√L_k·λ_k^σ` is paid: the squared
   weighted budget is `O((log(k+2)+2)³·(k+2)^{σ−1/2})`, which vanishes for
   every fixed `0 ≤ σ < 1/2`.

No compact-rate premise; strictly substrip (`σ = 1/2` is not claimed).
-/

/-! ## Step 1: exact scalar homogeneity through the projection -/

private theorem n2r_eStar_scale (k : ℕ) (u : ℝ) :
    E_star (selectedFerrersLemma73SourcePacket k) u =
      selectedFerrersLemma73SourceScale k *
        E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u := by
  unfold E_star selectedFerrersLemma73SourcePacket
  rw [tsum_mul_left]
  ring

private theorem n2r_packet_memLp (k : ℕ) :
    MemLp (E_star (selectedFerrersLemma73SourcePacket k)) 2
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  have hbase := (selectedFerrersPreAnchorPair_eStar_memLp k).const_mul
    (selectedFerrersLemma73SourceScale k)
  exact (memLp_congr_ae
    (Filter.Eventually.of_forall fun u => n2r_eStar_scale k u)).mpr hbase

private theorem n2r_EStarHm_eq_toLp (k : ℕ) :
    selectedFerrersEStarHm k =
      (n2r_packet_memLp k).toLp
        (E_star (selectedFerrersLemma73SourcePacket k)) := rfl

private theorem n2r_scale_smul_gTrial (k : ℕ) :
    selectedFerrersLemma73SourceScale k •
      gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) =
      selectedFerrersEStarHm k := by
  rw [n2r_EStarHm_eq_toLp k]
  apply MeasureTheory.Lp.ext
  have h1 : (gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))]
      E_star (prolateCombination (selectedFerrersPreAnchorPair k)) :=
    MemLp.coeFn_toLp _
  have h2 : ((n2r_packet_memLp k).toLp
      (E_star (selectedFerrersLemma73SourcePacket k)) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))]
      E_star (selectedFerrersLemma73SourcePacket k) :=
    MemLp.coeFn_toLp _
  have hsmul := MeasureTheory.Lp.coeFn_smul
    (selectedFerrersLemma73SourceScale k)
    (gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k))
  filter_upwards [h1, h2, hsmul] with u hu1 hu2 hu3
  rw [hu3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hu1, hu2, n2r_eStar_scale k u]

/-- **The exact scaled-residual crosswalk.**  The source scale moves through
the literal Galerkin projection by linearity; the scaled projection residual
is the projection residual of the pure `E⋆` vector.  No norms are taken. -/
private theorem n2r_scaled_residual_eq (k : ℕ) :
    selectedFerrersLemma73SourceScale k •
      ((gTrial_m_N (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) : H_m (selectedFerrersPreAnchorIndex k)) -
        gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k)) =
      ((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
        selectedFerrersEStarHm k := by
  rw [smul_sub]
  congr 1
  · have h1 : gTrial_m_N (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) =
        P_m_N (selectedFerrersPreAnchorIndex k)
          (gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k)) := rfl
    rw [h1, ← Submodule.coe_smul, ← map_smul, n2r_scale_smul_gTrial k]
  · exact n2r_scale_smul_gTrial k

/-! ## Step 2: the two-sided omitted-mode tail weights -/

private def n2rTailWeight (i : PairIndex) (n : ℤ) : ℝ :=
  if n ∈ modeSet i then 0 else ((n : ℝ) ^ 2)⁻¹

private theorem n2r_nat_base_summable :
    Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  simpa [one_div] using (summable_one_div_nat_pow (p := 2)).mpr (by norm_num)

private theorem n2r_int_base_summable :
    Summable (fun n : ℤ => ((n : ℝ) ^ 2)⁻¹) := by
  simpa [one_div] using (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)

private theorem n2rTailWeight_nonneg (i : PairIndex) (n : ℤ) :
    0 ≤ n2rTailWeight i n := by
  unfold n2rTailWeight
  split <;> positivity

private theorem n2rTailWeight_le_base (i : PairIndex) (n : ℤ) :
    n2rTailWeight i n ≤ ((n : ℝ) ^ 2)⁻¹ := by
  unfold n2rTailWeight
  split
  · positivity
  · exact le_rfl

private theorem n2rTailWeight_summable (i : PairIndex) :
    Summable (n2rTailWeight i) :=
  Summable.of_nonneg_of_le (n2rTailWeight_nonneg i)
    (n2rTailWeight_le_base i) n2r_int_base_summable

private def n2rNatTail (N : ℕ) (n : ℕ) : ℝ :=
  if n ≤ N then 0 else ((n : ℝ) ^ 2)⁻¹

private theorem n2rNatTail_nonneg (N n : ℕ) : 0 ≤ n2rNatTail N n := by
  unfold n2rNatTail
  split <;> positivity

private theorem n2rNatTail_summable (N : ℕ) :
    Summable (n2rNatTail N) := by
  refine Summable.of_nonneg_of_le (n2rNatTail_nonneg N)
    (fun n => ?_) n2r_nat_base_summable
  unfold n2rNatTail
  split
  · positivity
  · exact le_rfl

private theorem n2rNatTail_tsum_le (N : ℕ) :
    ∑' n : ℕ, n2rNatTail N n ≤ 2 / ((N : ℝ) + 1) := by
  refine (n2rNatTail_summable N).tsum_le_of_sum_le ?_
  intro s
  have hsub : s.filter (fun n => ¬ n ≤ N) ⊆ Finset.Ioo N (s.sup id + 1) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hnN⟩
    refine Finset.mem_Ioo.mpr ⟨by omega, ?_⟩
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hns
    omega
  calc
    ∑ n ∈ s, n2rNatTail N n
        = ∑ n ∈ s.filter (fun n => ¬ n ≤ N), ((n : ℝ) ^ 2)⁻¹ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          unfold n2rNatTail
          by_cases h : n ≤ N <;> simp [h]
    _ ≤ ∑ n ∈ Finset.Ioo N (s.sup id + 1), ((n : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => by positivity)
    _ ≤ 2 / ((N : ℝ) + 1) := by
          simpa using sum_Ioo_inv_sq_le (α := ℝ) N (s.sup id + 1)

private theorem n2rTailWeight_nat_eq (i : PairIndex) (n : ℕ) :
    n2rTailWeight i (n : ℤ) = n2rNatTail i.N n := by
  unfold n2rTailWeight n2rNatTail
  have hmem : ((n : ℤ) ∈ modeSet i) ↔ n ≤ i.N := by
    simp only [modeSet, Finset.mem_Icc]
    omega
  by_cases h : n ≤ i.N
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hx => h (hmem.mp hx)), if_neg h]
    norm_cast

private theorem n2rTailWeight_neg_eq (i : PairIndex) (n : ℕ) :
    n2rTailWeight i (-((n : ℤ) + 1)) = n2rNatTail i.N (n + 1) := by
  unfold n2rTailWeight n2rNatTail
  have hmem : ((-((n : ℤ) + 1)) ∈ modeSet i) ↔ n + 1 ≤ i.N := by
    simp only [modeSet, Finset.mem_Icc]
    omega
  by_cases h : n + 1 ≤ i.N
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hx => h (hmem.mp hx)), if_neg h]
    congr 1
    push_cast
    ring

private theorem n2rTailWeight_tsum_le (i : PairIndex) :
    ∑' n : ℤ, n2rTailWeight i n ≤ 4 / ((i.N : ℝ) + 1) := by
  have hnat : Summable (fun n : ℕ => n2rTailWeight i (n : ℤ)) := by
    refine (n2rNatTail_summable i.N).congr ?_
    intro n
    exact (n2rTailWeight_nat_eq i n).symm
  have hshift : Summable (fun n : ℕ => n2rNatTail i.N (n + 1)) :=
    (summable_nat_add_iff 1).mpr (n2rNatTail_summable i.N)
  have hneg : Summable (fun n : ℕ => n2rTailWeight i (-((n : ℤ) + 1))) := by
    refine hshift.congr ?_
    intro n
    exact (n2rTailWeight_neg_eq i n).symm
  have hsplit :
      ∑' n : ℤ, n2rTailWeight i n =
        (∑' n : ℕ, n2rTailWeight i (n : ℤ)) +
          ∑' n : ℕ, n2rTailWeight i (-((n : ℤ) + 1)) := by
    simpa using tsum_of_nat_of_neg_add_one hnat hneg
  have hnat_le : (∑' n : ℕ, n2rTailWeight i (n : ℤ)) ≤ 2 / ((i.N : ℝ) + 1) := by
    calc
      (∑' n : ℕ, n2rTailWeight i (n : ℤ))
          = ∑' n : ℕ, n2rNatTail i.N n :=
            tsum_congr (n2rTailWeight_nat_eq i)
      _ ≤ 2 / ((i.N : ℝ) + 1) := n2rNatTail_tsum_le i.N
  have hneg_le :
      (∑' n : ℕ, n2rTailWeight i (-((n : ℤ) + 1))) ≤ 2 / ((i.N : ℝ) + 1) := by
    have hshift_le :
        (∑' n : ℕ, n2rNatTail i.N (n + 1)) ≤ 2 / ((i.N : ℝ) + 1) := by
      have hzero : n2rNatTail i.N 0 = 0 := by
        unfold n2rNatTail
        simp
      have hz :=
        (n2rNatTail_summable i.N).tsum_eq_zero_add
      have heq : (∑' n : ℕ, n2rNatTail i.N (n + 1)) =
          ∑' n : ℕ, n2rNatTail i.N n := by
        rw [hz, hzero, zero_add]
      rw [heq]
      exact n2rNatTail_tsum_le i.N
    calc
      (∑' n : ℕ, n2rTailWeight i (-((n : ℤ) + 1)))
          = ∑' n : ℕ, n2rNatTail i.N (n + 1) :=
            tsum_congr (n2rTailWeight_neg_eq i)
      _ ≤ 2 / ((i.N : ℝ) + 1) := hshift_le
  calc
    ∑' n : ℤ, n2rTailWeight i n
        = (∑' n : ℕ, n2rTailWeight i (n : ℤ)) +
            ∑' n : ℕ, n2rTailWeight i (-((n : ℤ) + 1)) := hsplit
    _ ≤ 2 / ((i.N : ℝ) + 1) + 2 / ((i.N : ℝ) + 1) :=
          add_le_add hnat_le hneg_le
    _ = 4 / ((i.N : ℝ) + 1) := by ring

/-! ## Step 3: eventual coefficient constant for the pure `E⋆` vector -/

private def n2rConst (AF Cp : ℝ) (k : ℕ) : ℝ :=
  AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
    Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) + Cp / (4 * Real.pi)

private theorem n2rConst_nonneg {AF Cp : ℝ} (hAF : 0 ≤ AF) (hCp : 0 ≤ Cp)
    (k : ℕ) : 0 ≤ n2rConst AF Cp k := by
  unfold n2rConst
  have hpi := Real.pi_pos
  positivity

set_option maxHeartbeats 8000000 in
private theorem n2r_coeff_sq_ev
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    ∃ AF Cp : ℝ, 0 ≤ AF ∧ 0 ≤ Cp ∧ ∀ᶠ k in Filter.atTop,
      ∀ n : ℤ, n ∉ modeSet (selectedFerrersPreAnchorIndex k) →
        ‖physicalFourierCoefficient (selectedFerrersPreAnchorIndex k)
            (selectedFerrersEStarHm k) n‖ ^ 2 ≤
          (n2rConst AF Cp k) ^ 2 *
            L_m (selectedFerrersPreAnchorIndex k) / (n : ℝ) ^ 2 := by
  obtain ⟨AF, hAF0, hAFev⟩ :=
    selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates
      C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ
  obtain ⟨Cp, hCp0, hCpRate⟩ :=
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hcenter : ∀ᶠ k in Filter.atTop,
      ‖selectedFerrersLemma73SourcePacket k 0‖ ≤
        Cp / (selectedFerrersPaperLambda k) ^ 2 := by
    filter_upwards [hCpRate] with k hk
    have hlam : 0 ≤ selectedFerrersPaperLambda k := Real.sqrt_nonneg _
    have hmem : (0 : ℝ) ∈ Set.Icc (-(selectedFerrersPaperLambda k))
        (selectedFerrersPaperLambda k) := ⟨by linarith, hlam⟩
    have h := hk 0 hmem
    have hH0 : explicitCCMLimitH 0 = 0 := by
      rw [explicitCCMLimitH]
      norm_num
    rw [hH0, mul_zero, sub_zero] at h
    exact h
  refine ⟨AF, Cp, hAF0, hCp0, ?_⟩
  filter_upwards [hAFev, hcenter] with k hkB hkC
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h0
    apply hn
    rw [h0]
    simp only [modeSet, Finset.mem_Icc]
    constructor
    · omega
    · omega
  have hL : 0 < L_m (selectedFerrersPreAnchorIndex k) :=
    logLength_pos _
  have hlameq : selectedFerrersPaperLambda k =
      lambda_m (selectedFerrersPreAnchorIndex k) :=
    selectedFerrersPaperLambda_eq_lambda_m k
  have hlam1 : (1 : ℝ) ≤ selectedFerrersPaperLambda k := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (by omega : 1 ≤ k + 2)
  have hlam0 : (0 : ℝ) < selectedFerrersPaperLambda k := by linarith
  have hsqrt_le :
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) ≤
        (selectedFerrersPaperLambda k) ^ 2 := by
    rw [← hlameq]
    have h1 : Real.sqrt (selectedFerrersPaperLambda k) ≤
        Real.sqrt ((selectedFerrersPaperLambda k) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.sqrt_sq hlam0.le] at h1
    calc
      Real.sqrt (selectedFerrersPaperLambda k) ≤
          selectedFerrersPaperLambda k := h1
      _ ≤ (selectedFerrersPaperLambda k) ^ 2 := by nlinarith
  have hcenterProd :
      ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) ≤ Cp := by
    calc
      ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) ≤
        (Cp / (selectedFerrersPaperLambda k) ^ 2) *
          (selectedFerrersPaperLambda k) ^ 2 := by
          apply mul_le_mul hkC hsqrt_le (Real.sqrt_nonneg _)
          positivity
      _ = Cp := by
          field_simp
  have hcomb :
      selectedFerrersAbelFourierDecayBudget k +
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) /
            (4 * Real.pi) ≤
      n2rConst AF Cp k := by
    unfold n2rConst
    apply add_le_add hkB
    apply div_le_div_of_nonneg_right hcenterProd
    have := Real.pi_pos
    positivity
  have hbase0 :
      0 ≤ selectedFerrersAbelFourierDecayBudget k +
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) /
            (4 * Real.pi) := by
    have hb := selectedFerrersAbelFourierDecayBudget_nonneg k
    have := Real.pi_pos
    positivity
  have hsq := selectedFerrersEStarHm_physicalCoefficient_sq_le k n hn0
  have hCk2 :
      (selectedFerrersAbelFourierDecayBudget k +
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) /
            (4 * Real.pi)) ^ 2 ≤ (n2rConst AF Cp k) ^ 2 :=
    pow_le_pow_left₀ hbase0 hcomb 2
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn0
    positivity
  calc
    ‖physicalFourierCoefficient (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) n‖ ^ 2 ≤
        (selectedFerrersAbelFourierDecayBudget k +
          ‖selectedFerrersLemma73SourcePacket k 0‖ *
            Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) /
              (4 * Real.pi)) ^ 2 *
          L_m (selectedFerrersPreAnchorIndex k) / (n : ℝ) ^ 2 := hsq
    _ ≤ (n2rConst AF Cp k) ^ 2 *
          L_m (selectedFerrersPreAnchorIndex k) / (n : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ hn2.le
        exact mul_le_mul_of_nonneg_right hCk2 hL.le

/-! ## Step 4: the per-`k` Parseval tail bound -/

private theorem n2r_residual_sq_le (k : ℕ) (Ck : ℝ) (hCk : 0 ≤ Ck)
    (hcoeff : ∀ n : ℤ, n ∉ modeSet (selectedFerrersPreAnchorIndex k) →
      ‖physicalFourierCoefficient (selectedFerrersPreAnchorIndex k)
          (selectedFerrersEStarHm k) n‖ ^ 2 ≤
        Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) / (n : ℝ) ^ 2) :
    ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
      selectedFerrersEStarHm k‖ ^ 2 ≤
    Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) *
      (4 / (((selectedFerrersPreAnchorIndex k).N : ℝ) + 1)) := by
  have hL : 0 < L_m (selectedFerrersPreAnchorIndex k) := logLength_pos _
  have hparseval :
      ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
        selectedFerrersEStarHm k‖ ^ 2 =
        ∑' n : ℤ,
          if n ∈ modeSet (selectedFerrersPreAnchorIndex k) then 0
          else ‖inner ℂ (V_n_m (selectedFerrersPreAnchorIndex k) n)
            (selectedFerrersEStarHm k)‖ ^ 2 := by
    rw [norm_sub_rev]
    exact norm_sub_coe_P_m_N_sq_eq_tsum_complement
      (selectedFerrersPreAnchorIndex k) (selectedFerrersEStarHm k)
  have hpoint : ∀ n : ℤ,
      (if n ∈ modeSet (selectedFerrersPreAnchorIndex k) then (0 : ℝ)
        else ‖inner ℂ (V_n_m (selectedFerrersPreAnchorIndex k) n)
          (selectedFerrersEStarHm k)‖ ^ 2) ≤
        Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) *
          n2rTailWeight (selectedFerrersPreAnchorIndex k) n := by
    intro n
    unfold n2rTailWeight
    by_cases h : n ∈ modeSet (selectedFerrersPreAnchorIndex k)
    · simp [h]
    · have hcn := hcoeff n h
      simp only [h, if_false]
      calc
        ‖inner ℂ (V_n_m (selectedFerrersPreAnchorIndex k) n)
            (selectedFerrersEStarHm k)‖ ^ 2 ≤
            Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) / (n : ℝ) ^ 2 := by
              simpa [physicalFourierCoefficient] using hcn
        _ = Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) *
              ((n : ℝ) ^ 2)⁻¹ := by
              rw [div_eq_mul_inv]
  have hmaj_summable :
      Summable (fun n : ℤ =>
        Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) *
          n2rTailWeight (selectedFerrersPreAnchorIndex k) n) :=
    (n2rTailWeight_summable _).mul_left _
  have hlhs_summable :
      Summable (fun n : ℤ =>
        if n ∈ modeSet (selectedFerrersPreAnchorIndex k) then (0 : ℝ)
        else ‖inner ℂ (V_n_m (selectedFerrersPreAnchorIndex k) n)
          (selectedFerrersEStarHm k)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hpoint hmaj_summable
    split <;> positivity
  calc
    ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
      selectedFerrersEStarHm k‖ ^ 2
        = ∑' n : ℤ,
            if n ∈ modeSet (selectedFerrersPreAnchorIndex k) then 0
            else ‖inner ℂ (V_n_m (selectedFerrersPreAnchorIndex k) n)
              (selectedFerrersEStarHm k)‖ ^ 2 := hparseval
    _ ≤ ∑' n : ℤ, Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) *
          n2rTailWeight (selectedFerrersPreAnchorIndex k) n :=
          Summable.tsum_le_tsum hpoint hlhs_summable hmaj_summable
    _ = Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) *
          ∑' n : ℤ, n2rTailWeight (selectedFerrersPreAnchorIndex k) n :=
          tsum_mul_left
    _ ≤ Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) *
          (4 / (((selectedFerrersPreAnchorIndex k).N : ℝ) + 1)) := by
          have hcl : 0 ≤ Ck ^ 2 * L_m (selectedFerrersPreAnchorIndex k) := by
            positivity
          exact mul_le_mul_of_nonneg_left (n2rTailWeight_tsum_le _) hcl

/-! ## Step 5: the log-versus-power limit -/

private theorem n2r_log_cube_limit {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun x : ℝ => (Real.log x + 2) ^ (3 : ℕ) / x ^ ε)
      Filter.atTop (nhds 0) := by
  have hlog :=
    (isLittleO_log_rpow_rpow_atTop (((3 : ℕ)) : ℝ) hε).tendsto_div_nhds_zero
  have hcong : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (((3 : ℕ)) : ℝ) / x ^ ε =
        Real.log x ^ (3 : ℕ) / x ^ ε := by
    filter_upwards [] with x
    rw [Real.rpow_natCast]
  have h3 : Filter.Tendsto (fun x : ℝ => Real.log x ^ (3 : ℕ) / x ^ ε)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr' hcong hlog
  have h27 := h3.const_mul (27 : ℝ)
  rw [mul_zero] at h27
  apply squeeze_zero' ?_ ?_ h27
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hlx : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
        _ ≤ 3 := by norm_num
        _ ≤ x := hx
    have hpow : (Real.log x + 2) ^ (3 : ℕ) ≤ 27 * Real.log x ^ (3 : ℕ) := by
      have h1 : Real.log x + 2 ≤ 3 * Real.log x := by linarith
      calc (Real.log x + 2) ^ (3 : ℕ) ≤ (3 * Real.log x) ^ (3 : ℕ) :=
            pow_le_pow_left₀ (by linarith) h1 3
        _ = 27 * Real.log x ^ (3 : ℕ) := by ring
    have hxε : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx0 ε
    calc (Real.log x + 2) ^ (3 : ℕ) / x ^ ε ≤
          27 * Real.log x ^ (3 : ℕ) / x ^ ε :=
          div_le_div_of_nonneg_right hpow hxε.le
      _ = 27 * (Real.log x ^ (3 : ℕ) / x ^ ε) := by ring

private theorem n2r_nat_comp :
    Filter.Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
  have heq : (fun k : ℕ => ((k + 2 : ℕ) : ℝ)) =
      fun k : ℕ => ((k : ℕ) : ℝ) + 2 := by
    funext k
    push_cast
    ring
  rw [heq]
  exact Filter.tendsto_atTop_add_const_right _ 2
    tendsto_natCast_atTop_atTop

/-! ## Step 6: the public source-scaled tail-rate theorem -/

set_option maxHeartbeats 16000000 in
/-- **The N2 pre-anchor source-scaled Mellin projection-tail rate** (verdict
`REQ-2026-08-26-J`).  The moving-window kernel envelope `√L_k · λ_k^σ` times
the norm of the literal source-scaled projection residual vanishes for every
fixed `σ` with `0 ≤ σ < 1/2`, from exactly the frozen W5 inputs.  The finite
trial normalizer is cancelled exactly; no scale bound, family crosswalk,
subsequence or compact-rate premise enters. -/
theorem selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    Filter.Tendsto
      (fun k : ℕ =>
        Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) *
          lambda_m (selectedFerrersPreAnchorIndex k) ^ σ *
          ‖selectedFerrersLemma73SourceScale k •
            ((gTrial_m_N (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k) :
                H_m (selectedFerrersPreAnchorIndex k)) -
              gTrial_m (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k))‖)
      Filter.atTop (nhds 0) := by
  obtain ⟨AF, Cp, hAF0, hCp0, hcoeffEv⟩ :=
    n2r_coeff_sq_ev C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ
  have hε : (0 : ℝ) < 1 / 2 - σ := by linarith
  have hpi := Real.pi_pos
  have hD20 : (0 : ℝ) ≤ 8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2 := by
    positivity
  -- the eventual squared majorant
  have hsq_ev : ∀ᶠ k : ℕ in Filter.atTop,
      (Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) *
          lambda_m (selectedFerrersPreAnchorIndex k) ^ σ *
          ‖selectedFerrersLemma73SourceScale k •
            ((gTrial_m_N (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k) :
                H_m (selectedFerrersPreAnchorIndex k)) -
              gTrial_m (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k))‖) ^ 2 ≤
        (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
          ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) /
            ((k + 2 : ℕ) : ℝ) ^ (1 / 2 - σ)) := by
    filter_upwards [hcoeffEv] with k hk
    have hres2 := n2r_residual_sq_le k (n2rConst AF Cp k)
      (n2rConst_nonneg hAF0 hCp0 k) hk
    rw [n2r_scaled_residual_eq k]
    rw [show L_m (selectedFerrersPreAnchorIndex k) =
        Real.log ((k + 2 : ℕ) : ℝ) from rfl,
      show lambda_m (selectedFerrersPreAnchorIndex k) =
        Real.sqrt ((k + 2 : ℕ) : ℝ) from rfl]
    rw [show L_m (selectedFerrersPreAnchorIndex k) =
        Real.log ((k + 2 : ℕ) : ℝ) from rfl,
      show ((selectedFerrersPreAnchorIndex k).N : ℝ) =
        ((k + 2 : ℕ) : ℝ) from by norm_cast] at hres2
    have hx2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ k + 2)
    have hx0 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by linarith
    have hx1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by linarith
    have hlg0 : (0 : ℝ) ≤ Real.log ((k + 2 : ℕ) : ℝ) :=
      Real.log_nonneg hx1
    have hl2 : (0 : ℝ) ≤ Real.log ((k + 2 : ℕ) : ℝ) + 2 := by linarith
    have hl21 : (1 : ℝ) ≤ Real.log ((k + 2 : ℕ) : ℝ) + 2 := by linarith
    have hRnn : (0 : ℝ) ≤
        ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
          selectedFerrersEStarHm k‖ := norm_nonneg _
    have hxσ : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ σ :=
      Real.rpow_nonneg hx0.le σ
    -- expand the square
    have hexpand :
        (Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt ((k + 2 : ℕ) : ℝ) ^ σ *
          ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
            selectedFerrersEStarHm k‖) ^ 2 =
        Real.log ((k + 2 : ℕ) : ℝ) *
          ((Real.sqrt ((k + 2 : ℕ) : ℝ) ^ σ) ^ 2 *
            ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
              selectedFerrersEStarHm k‖ ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hlg0]
      ring
    have hlp : (Real.sqrt ((k + 2 : ℕ) : ℝ) ^ σ) ^ (2 : ℕ) =
        ((k + 2 : ℕ) : ℝ) ^ σ := by
      rw [← Real.rpow_natCast (Real.sqrt ((k + 2 : ℕ) : ℝ) ^ σ) 2,
        ← Real.rpow_mul (Real.sqrt_nonneg _),
        Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      congr 1
      push_cast
      ring
    rw [hexpand, hlp]
    -- chain to the explicit majorant
    have hstep1 :
        ((k + 2 : ℕ) : ℝ) ^ σ *
          ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
            selectedFerrersEStarHm k‖ ^ 2 ≤
        ((k + 2 : ℕ) : ℝ) ^ σ *
          ((n2rConst AF Cp k) ^ 2 * Real.log ((k + 2 : ℕ) : ℝ) *
            (4 / (((k + 2 : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hres2 hxσ
    have hstep2 :
        Real.log ((k + 2 : ℕ) : ℝ) *
          (((k + 2 : ℕ) : ℝ) ^ σ *
            ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
              selectedFerrersEStarHm k‖ ^ 2) ≤
        4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
          ((k + 2 : ℕ) : ℝ) ^ σ / (((k + 2 : ℕ) : ℝ) + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hstep1 hlg0
      calc Real.log ((k + 2 : ℕ) : ℝ) *
            (((k + 2 : ℕ) : ℝ) ^ σ *
              ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
                selectedFerrersEStarHm k‖ ^ 2) ≤
          Real.log ((k + 2 : ℕ) : ℝ) *
            (((k + 2 : ℕ) : ℝ) ^ σ *
              ((n2rConst AF Cp k) ^ 2 * Real.log ((k + 2 : ℕ) : ℝ) *
                (4 / (((k + 2 : ℕ) : ℝ) + 1)))) := h1
        _ = 4 * (n2rConst AF Cp k) ^ 2 *
              (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
              ((k + 2 : ℕ) : ℝ) ^ σ / (((k + 2 : ℕ) : ℝ) + 1) := by
            ring
    have hstep3 :
        4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
          ((k + 2 : ℕ) : ℝ) ^ σ / (((k + 2 : ℕ) : ℝ) + 1) ≤
        4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
          ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) := by
      have hnum : (0 : ℝ) ≤ 4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 * ((k + 2 : ℕ) : ℝ) ^ σ := by
        have := n2rConst_nonneg hAF0 hCp0 k
        positivity
      have hd1 := one_div_le_one_div_of_le hx0 (by linarith :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 1)
      calc 4 * (n2rConst AF Cp k) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
            ((k + 2 : ℕ) : ℝ) ^ σ / (((k + 2 : ℕ) : ℝ) + 1) =
          (4 * (n2rConst AF Cp k) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
            ((k + 2 : ℕ) : ℝ) ^ σ) * (1 / (((k + 2 : ℕ) : ℝ) + 1)) := by ring
        _ ≤ (4 * (n2rConst AF Cp k) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
            ((k + 2 : ℕ) : ℝ) ^ σ) * (1 / ((k + 2 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hd1 hnum
        _ = 4 * (n2rConst AF Cp k) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
            ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) := by ring
    -- split the coefficient constant
    have hCksq : (n2rConst AF Cp k) ^ 2 ≤
        2 * AF ^ 2 * (Real.sqrt ((k + 2 : ℕ) : ℝ) *
          (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
        2 * (Cp / (4 * Real.pi)) ^ 2 := by
      have hsq1 : (AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2))) ^ 2 =
          AF ^ 2 * (Real.sqrt ((k + 2 : ℕ) : ℝ) *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2)) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _),
          Real.sq_sqrt hl2]
      unfold n2rConst
      nlinarith [sq_nonneg (AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) - Cp / (4 * Real.pi)),
        hsq1]
    -- exact exponent identities
    have hpow1 : Real.sqrt ((k + 2 : ℕ) : ℝ) *
        ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) =
        ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) := by
      have h1 : ((k + 2 : ℕ) : ℝ) ^ ((1:ℝ)/2 + σ - 1) =
          ((k + 2 : ℕ) : ℝ) ^ ((1:ℝ)/2) * ((k + 2 : ℕ) : ℝ) ^ σ /
            ((k + 2 : ℕ) : ℝ) := by
        rw [Real.rpow_sub hx0, Real.rpow_add hx0, Real.rpow_one]
      rw [Real.sqrt_eq_rpow, ← h1]
      congr 1
      ring
    have hpow2 : ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) ≤
        ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) := by
      have h1 : ((k + 2 : ℕ) : ℝ) ^ (σ - 1) =
          ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) := by
        rw [Real.rpow_sub hx0, Real.rpow_one]
      rw [← h1]
      apply Real.rpow_le_rpow_of_exponent_le hx1
      linarith
    have hxeneg : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) :=
      Real.rpow_nonneg hx0.le _
    -- assemble the two pieces
    have hlgsq : (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 ≤
        (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 := by
      nlinarith
    have hfinal :
        4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
          ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) ≤
        (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
          ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) *
            ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ))) := by
      have hA : 4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
          ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) =
          (4 * (n2rConst AF Cp k) ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2) *
            (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) := by ring
      have hB : (0 : ℝ) ≤
          4 * (n2rConst AF Cp k) ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 := by
        have := n2rConst_nonneg hAF0 hCp0 k
        positivity
      -- piece bound: Ck² lg² (x^σ/x) ≤ (2AF²√x·l2 + 2P²)·l2²·x^{-ε} ... assembled below
      have hsx0 : (0 : ℝ) ≤ Real.sqrt ((k + 2 : ℕ) : ℝ) := Real.sqrt_nonneg _
      have h1 : 4 * (n2rConst AF Cp k) ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
            (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) ≤
          4 * (2 * AF ^ 2 * (Real.sqrt ((k + 2 : ℕ) : ℝ) *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
            2 * (Cp / (4 * Real.pi)) ^ 2) *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
            (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) := by
        have hquot0 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) := by
          positivity
        apply mul_le_mul_of_nonneg_right _ hquot0
        have h2 := mul_le_mul hCksq hlgsq (sq_nonneg _) (by positivity)
        nlinarith [h2, sq_nonneg (Real.log ((k + 2 : ℕ) : ℝ))]
      have hsplit :
          4 * (2 * AF ^ 2 * (Real.sqrt ((k + 2 : ℕ) : ℝ) *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
            2 * (Cp / (4 * Real.pi)) ^ 2) *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
            (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) =
          8 * AF ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
            (Real.sqrt ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) +
          8 * (Cp / (4 * Real.pi)) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
            (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) := by
        ring
      have hp1 : 8 * AF ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
            (Real.sqrt ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) =
          8 * AF ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
            ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) := by
        rw [hpow1]
      have hp2 : 8 * (Cp / (4 * Real.pi)) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
            (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) ≤
          8 * (Cp / (4 * Real.pi)) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
            ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) := by
        have hl23 : (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 ≤
            (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 := by
          exact pow_le_pow_right₀ hl21 (by omega : 2 ≤ 3)
        have hc0 : (0 : ℝ) ≤ 8 * (Cp / (4 * Real.pi)) ^ 2 := by positivity
        calc 8 * (Cp / (4 * Real.pi)) ^ 2 *
              (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
              (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) ≤
            8 * (Cp / (4 * Real.pi)) ^ 2 *
              (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
              ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) := by
              apply mul_le_mul_of_nonneg_left hpow2
              positivity
          _ ≤ 8 * (Cp / (4 * Real.pi)) ^ 2 *
              (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
              ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) := by
              apply mul_le_mul_of_nonneg_right _ hxeneg
              exact mul_le_mul_of_nonneg_left hl23 hc0
      calc 4 * (n2rConst AF Cp k) ^ 2 *
            (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
            ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) =
          (4 * (n2rConst AF Cp k) ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2) *
            (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) := hA
        _ ≤ 4 * (2 * AF ^ 2 * (Real.sqrt ((k + 2 : ℕ) : ℝ) *
              (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
              2 * (Cp / (4 * Real.pi)) ^ 2) *
              (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
              (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) := by
            exact h1
        _ = 8 * AF ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
              (Real.sqrt ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) +
            8 * (Cp / (4 * Real.pi)) ^ 2 *
              (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 2 *
              (((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ)) := hsplit
        _ ≤ 8 * AF ^ 2 * (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
              ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) +
            8 * (Cp / (4 * Real.pi)) ^ 2 *
              (Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ 3 *
              ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ)) := by
            rw [hp1]
            exact add_le_add le_rfl hp2
        _ = (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
              ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) *
                ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ))) := by
            ring
    have hdivform : (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
          ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) *
            ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ))) =
        (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
          ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) /
            ((k + 2 : ℕ) : ℝ) ^ (1 / 2 - σ)) := by
      rw [Real.rpow_neg hx0.le]
      ring
    calc Real.log ((k + 2 : ℕ) : ℝ) *
          (((k + 2 : ℕ) : ℝ) ^ σ *
            ‖((P_m_N (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) : E_m_N (selectedFerrersPreAnchorIndex k)) :
        H_m (selectedFerrersPreAnchorIndex k)) -
              selectedFerrersEStarHm k‖ ^ 2) ≤
        4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
          ((k + 2 : ℕ) : ℝ) ^ σ / (((k + 2 : ℕ) : ℝ) + 1) := hstep2
      _ ≤ 4 * (n2rConst AF Cp k) ^ 2 *
          (Real.log ((k + 2 : ℕ) : ℝ)) ^ 2 *
          ((k + 2 : ℕ) : ℝ) ^ σ / ((k + 2 : ℕ) : ℝ) := hstep3
      _ ≤ (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
            ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) *
              ((k + 2 : ℕ) : ℝ) ^ (-(1 / 2 - σ))) := hfinal
      _ = (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
            ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) /
              ((k + 2 : ℕ) : ℝ) ^ (1 / 2 - σ)) := hdivform
  -- majorant tends to zero
  have hmajz : Filter.Tendsto
      (fun k : ℕ => (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2) *
        ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (3 : ℕ) /
          ((k + 2 : ℕ) : ℝ) ^ (1 / 2 - σ)))
      Filter.atTop (nhds 0) := by
    have hcomp := (n2r_log_cube_limit hε).comp n2r_nat_comp
    have hlim := hcomp.const_mul
      (8 * AF ^ 2 + 8 * (Cp / (4 * Real.pi)) ^ 2)
    rw [mul_zero] at hlim
    simpa [Function.comp] using hlim
  -- squeeze the squares, then take square roots
  have hsq : Filter.Tendsto
      (fun k : ℕ =>
        (Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) *
          lambda_m (selectedFerrersPreAnchorIndex k) ^ σ *
          ‖selectedFerrersLemma73SourceScale k •
            ((gTrial_m_N (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k) :
                H_m (selectedFerrersPreAnchorIndex k)) -
              gTrial_m (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k))‖) ^ 2)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun k => sq_nonneg _)
      hsq_ev hmajz
  have hsqrt := hsq.sqrt
  rw [Real.sqrt_zero] at hsqrt
  refine Filter.Tendsto.congr (fun k => ?_) hsqrt
  have hnn : (0 : ℝ) ≤
      Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) *
        lambda_m (selectedFerrersPreAnchorIndex k) ^ σ *
        ‖selectedFerrersLemma73SourceScale k •
          ((gTrial_m_N (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k) :
              H_m (selectedFerrersPreAnchorIndex k)) -
            gTrial_m (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k))‖ := by
    have hlam0 : (0 : ℝ) ≤ lambda_m (selectedFerrersPreAnchorIndex k) := by
      rw [show lambda_m (selectedFerrersPreAnchorIndex k) =
        Real.sqrt ((k + 2 : ℕ) : ℝ) from rfl]
      exact Real.sqrt_nonneg _
    have h1 : (0 : ℝ) ≤
        lambda_m (selectedFerrersPreAnchorIndex k) ^ σ :=
      Real.rpow_nonneg hlam0 σ
    have h2 : (0 : ℝ) ≤
        Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) :=
      Real.sqrt_nonneg _
    positivity
  exact Real.sqrt_sq hnn

#print axioms selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate

end Q3.RouteB.D0Pstar
