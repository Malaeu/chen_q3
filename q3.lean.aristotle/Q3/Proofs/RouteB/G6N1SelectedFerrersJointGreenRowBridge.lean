import Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMSourceRow
import Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Selected Ferrers coefficient to its window Mellin coordinate

This module records the exact source normalization of a selected finite CCM
row coefficient at each carrier index.  It identifies the coefficient with
the normalized, signed Mellin sample of the same unprojected Ferrers packet;
Expanding that sample into a finite paired-window sum requires the separate
support and integrability hypotheses of `EStarWindowedMellinCrosswalk`.

No coefficient row is replaced by an arbitrary unit vector, and no Mellin
normalizer or sign is supplied as an extra hypothesis.
-/

private lemma selectedFerrers_inner_V_P_eq
    (i : PairIndex) (x : H_m i) {n : ℤ}
    (hn : n ∈ modeSet i) :
    inner ℂ (V_n_m i n) ((P_m_N i x : H_m i)) =
      inner ℂ (V_n_m i n) x := by
  classical
  rw [coe_P_m_N_apply_eq_sum_inner_V_n_m_smul, inner_sum]
  simp_rw [inner_smul_right,
    orthonormal_iff_ite.mp (V_n_m_orthonormal i), mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq (modeSet i) n
    (fun r => inner ℂ (V_n_m i r) x), if_pos hn]

private lemma selectedFerrers_c_n_eq_smul_inner
    (i : PairIndex) (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNz : TrialNonzero i h hLp) {n : ℤ}
    (hn : n ∈ modeSet i) :
    c_n i h hLp hNz n =
      ((sTrial_m_N i h hLp hNz : ℝ) : ℂ) *
        inner ℂ (V_n_m i n) (gTrial_m i h hLp) := by
  unfold c_n kTrial_m_N
  rw [Submodule.coe_smul, inner_smul_right]
  congr 1
  exact selectedFerrers_inner_V_P_eq i _ hn

private lemma selectedFerrers_phase_eq_zpow (n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * n) = (-1 : ℂ) ^ n := by
  have hbase : Complex.exp (-(Real.pi : ℂ) * Complex.I) = (-1 : ℂ) := by
    rw [show -(Real.pi : ℂ) * Complex.I = -((Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  have hn : -(Real.pi : ℂ) * Complex.I * n = n * (-(Real.pi : ℂ) * Complex.I) := by
    ring
  rw [hn, Complex.exp_int_mul, hbase]

private lemma selectedFerrers_lambda_log (i : PairIndex) :
    Real.log (lambda_m i) = L_m i / 2 := by
  rw [lambda_m, Real.log_sqrt]
  · rfl
  · positivity

private lemma selectedFerrers_window_mellin_sample
    (i : PairIndex) (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (n : ℤ) :
    inner ℂ (V_n_m i n) (gTrial_m i h hLp) =
      ((-1 : ℂ) ^ n) *
        ((Real.sqrt (L_m i) : ℝ)⁻¹ : ℂ) *
          preAnchorFullMellinCoordinate i h hLp
            (((2 * Real.pi * (n : ℝ)) / L_m i : ℝ) : ℂ) := by
  let ω : ℝ := (2 * Real.pi * (n : ℝ)) / L_m i
  let phase : ℂ := (-1 : ℂ) ^ n
  have hLpos : 0 < L_m i := logLength_pos i
  have hlam : 0 < lambda_m i := by
    unfold lambda_m
    apply Real.sqrt_pos.mpr
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hrep :
      (fun u : ℝ => (gTrial_m i h hLp : H_m i) u) =ᵐ[dStar.restrict (I_m i)]
        E_star h := by
    unfold gTrial_m
    exact MemLp.coeFn_toLp hLp
  have hmode :
      (fun u : ℝ => (V_n_m i n) u) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    exact MemLp.coeFn_toLp _
  have hkernel :
      (fun u : ℝ =>
        star
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) * E_star h u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        phase * ((Real.sqrt (L_m i) : ℝ)⁻¹ : ℂ) *
          (E_star h u * (u : ℂ) ^ (-Complex.I * (ω : ℂ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu_pos : 0 < u :=
      (inv_pos.mpr hlam).trans_le hu.1
    have hlogmul :
        Real.log (lambda_m i * u) = Real.log (lambda_m i) + Real.log u :=
      Real.log_mul hlam.ne' hu_pos.ne'
    have hloglambda := selectedFerrers_lambda_log i
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    change (starRingEnd ℂ)
        (((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * n *
              (Real.log (lambda_m i * u) / L_m i))) * E_star h u =
        phase * ((Real.sqrt (L_m i) : ℝ)⁻¹ : ℂ) *
          (E_star h u * (u : ℂ) ^ (-Complex.I * (ω : ℂ)))
    have hstarArg :
        (starRingEnd ℂ)
          (2 * Real.pi * Complex.I * n *
            (Real.log (lambda_m i * u) / L_m i)) =
          -(2 * Real.pi * Complex.I * n *
            (Real.log (lambda_m i * u) / L_m i)) := by
      have hcast :
          (2 * Real.pi * Complex.I * n *
            (Real.log (lambda_m i * u) / L_m i) : ℂ) =
          Complex.I *
            (((2 * Real.pi * (n : ℝ) *
              (Real.log (lambda_m i * u) / L_m i) : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [hcast, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [map_mul, map_inv₀, Complex.conj_ofReal,
      ← Complex.exp_conj, hstarArg]
    rw [hlogmul]
    rw [Complex.cpow_def_of_ne_zero hu_ne]
    have hexp :
        -(2 * Real.pi * Complex.I * n *
            (((Real.log (lambda_m i) + Real.log u : ℝ) : ℂ) /
              ((L_m i : ℝ) : ℂ))) =
          -(Real.pi : ℂ) * Complex.I * n +
            (-Complex.I * (ω : ℂ)) * (Real.log u : ℂ) := by
      dsimp [ω]
      push_cast
      rw [hloglambda]
      push_cast
      have hLne : ((L_m i : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hLpos.ne'
      field_simp [hLne]
      ring
    rw [hexp, Complex.exp_add, ← Complex.ofReal_log hu_pos.le]
    rw [show (-Complex.I * (ω : ℂ)) * (Real.log u : ℂ) =
        (Real.log u : ℂ) * (-Complex.I * (ω : ℂ)) by ring]
    rw [show Complex.exp (-(Real.pi : ℂ) * Complex.I * n) = phase by
      dsimp [phase]
      convert selectedFerrers_phase_eq_zpow n using 1]
    ring
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply]
  calc
    (∫ u : ℝ,
        (gTrial_m i h hLp : H_m i) u * star ((V_n_m i n) u)
          ∂(dStar.restrict (I_m i))) =
      ∫ u : ℝ,
        phase * ((Real.sqrt (L_m i) : ℝ)⁻¹ : ℂ) *
          (E_star h u * (u : ℂ) ^ (-Complex.I * (ω : ℂ)))
          ∂(dStar.restrict (I_m i)) := by
      apply integral_congr_ae
      filter_upwards [hrep, hmode, hkernel] with u hrep_u hmode_u hkernel_u
      rw [hmode_u, hrep_u]
      rw [mul_comm]
      exact hkernel_u
    _ = phase * ((Real.sqrt (L_m i) : ℝ)⁻¹ : ℂ) *
          preAnchorFullMellinCoordinate i h hLp ω := by
      rw [MeasureTheory.integral_const_mul]
      have hint :
          (∫ u : ℝ,
            E_star h u * (u : ℂ) ^ (-Complex.I * (ω : ℂ))
              ∂(dStar.restrict (I_m i))) =
          preAnchorFullMellinCoordinate i h hLp (ω : ℂ) := by
        unfold preAnchorFullMellinCoordinate
        apply integral_congr_ae
        filter_upwards [hrep] with u hu
        rw [hu]
      rw [hint]

/-- Exact phase and normalizer for the selected row, conditional on the existing
`CCMLemma73PreAnchorPort`. This is not yet a finite paired-window sum. -/
theorem selectedFerrersFiniteCCMRow_eq_normalizedMellinSample
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ)
    (j : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) :
    selectedFerrersFiniteCCMRow P k j =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) *
        ((-1 : ℂ) ^ ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N j) *
        ((Real.sqrt (L_m ((selectedFerrersCofinalSourceData P).index k)) : ℝ)⁻¹ : ℂ) *
        preAnchorGwinTransformCoordinate
          ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((((2 * Real.pi *
              (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j : ℝ)) /
              L_m ((selectedFerrersCofinalSourceData P).index k)) : ℝ) : ℂ) := by
  let D := selectedFerrersCofinalSourceData P
  let i := D.index k
  let h := prolateCombination (D.pair k)
  let hLp := D.eStar_memLp k
  let hNz := D.trialNonzero k
  let n := ccmModeFinite i.N j
  have hn : n ∈ modeSet i := by
    have h := ccmModeFinite_range i.N j
    unfold modeSet
    exact Finset.mem_Icc.mpr h
  rw [selectedFerrersFiniteCCMRow_apply]
  rw [selectedFerrers_c_n_eq_smul_inner i h hLp hNz hn]
  rw [selectedFerrers_window_mellin_sample]
  rw [preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate]
  simp only [D, i, h, n]
  ring

#print axioms selectedFerrersFiniteCCMRow_eq_normalizedMellinSample

end Q3.RouteB.D0Pstar

end
