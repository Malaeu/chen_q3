import Q3.Proofs.RouteB.D0PstarSourceWeilEvenTailExplicitCoercivity
import Q3.Proofs.RouteB.G6N1SelectedFerrersPreAnchorDataInhabitant

set_option linter.mathlibStandardSet false
set_option maxRecDepth 2048

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators Real

namespace Q3.RouteB.D0Pstar

/-!
# Fixed even-tail cutoff obstruction on the selected Ferrers schedule

The explicit source-Weil even-tail coercivity theorem begins after
`sourceWeilEvenTailCutoff i`.  The literal selected finite CCM carrier ends at
mode `i.N`.  This file proves that, on every selected Ferrers cell, the fixed
cutoff lies strictly beyond that finite carrier.

Consequently the explicit fixed-tail theorem cannot directly supply the
selected finite-tail floor.  This is a scoped obstruction to that supplier,
not a failure of the explicit coercivity theorem and not a claim about an
adaptive cutoff or direct finite-carrier argument.
-/

/-- The central W02 mode gives a linear lower bound for the ambient W02 form
norm. -/
theorem sourceW02AmbientContinuousSesquilinearForm_norm_lower
    (i : PairIndex) :
    2 * L_m i ≤ ‖sourceW02AmbientContinuousSesquilinearForm i‖ := by
  have hL : 0 < L_m i := logLength_pos i
  have hsinh : L_m i / 4 ≤ Real.sinh (L_m i / 4) :=
    Real.self_le_sinh_iff.mpr (by positivity)
  have hsinh0 : 0 ≤ Real.sinh (L_m i / 4) := by positivity
  have hsquares : (L_m i / 4) ^ 2 ≤ Real.sinh (L_m i / 4) ^ 2 := by
    nlinarith
  have hcenter :
      Q3.RouteB.ccmW02Entry (L_m i) 0 0 =
        32 * Real.sinh (L_m i / 4) ^ 2 / L_m i := by
    unfold Q3.RouteB.ccmW02Entry
    norm_num
    field_simp [hL.ne']
  have hcenterLower :
      2 * L_m i ≤ Q3.RouteB.ccmW02Entry (L_m i) 0 0 := by
    rw [hcenter, le_div_iff₀ hL]
    nlinarith
  have hvnorm : ‖V_n_m i 0‖ = 1 :=
    (V_n_m_orthonormal i).norm_eq_one 0
  have happ :
      ‖(Q3.RouteB.ccmW02Entry (L_m i) 0 0 : ℂ)‖ ≤
        ‖sourceW02AmbientContinuousSesquilinearForm i‖ := by
    calc
      ‖(Q3.RouteB.ccmW02Entry (L_m i) 0 0 : ℂ)‖ =
          ‖sourceW02AmbientContinuousSesquilinearForm i
            (V_n_m i 0) (V_n_m i 0)‖ := by
              rw [sourceW02AmbientContinuousSesquilinearForm_apply_mode]
              rw [sourceW02ModePairing_eq_ccmW02Entry]
      _ ≤ ‖sourceW02AmbientContinuousSesquilinearForm i (V_n_m i 0)‖ *
          ‖V_n_m i 0‖ :=
        (sourceW02AmbientContinuousSesquilinearForm i (V_n_m i 0)).le_opNorm _
      _ ≤ (‖sourceW02AmbientContinuousSesquilinearForm i‖ * ‖V_n_m i 0‖) *
          ‖V_n_m i 0‖ := by
        gcongr
        exact (sourceW02AmbientContinuousSesquilinearForm i).le_opNorm _
      _ = ‖sourceW02AmbientContinuousSesquilinearForm i‖ := by
        rw [hvnorm]
        ring
  have hcenterNonneg : 0 ≤ Q3.RouteB.ccmW02Entry (L_m i) 0 0 := by
    linarith
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hcenterNonneg] at happ
  exact hcenterLower.trans happ

/-- On every selected Ferrers cell, the fixed explicit even-tail cutoff lies
strictly beyond the last mode of the literal finite CCM carrier. -/
theorem selectedFerrersPreAnchorIndex_N_lt_sourceWeilEvenTailCutoff
    (k : ℕ) :
    (selectedFerrersPreAnchorIndex k).N <
      sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k) := by
  let i := selectedFerrersPreAnchorIndex k
  have hm2 : 2 ≤ i.m := i.hm
  have hmpos : 0 < (i.m : ℝ) := by positivity
  have hL : 0 < L_m i := logLength_pos i
  have hlog2le : Real.log 2 ≤ L_m i := by
    change Real.log 2 ≤ Real.log (i.m : ℝ)
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hmpos
    · exact_mod_cast hm2
  have hLhalf : (1 / 2 : ℝ) < L_m i := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    exact hlog2.trans_le hlog2le
  have hnorm :
      2 * L_m i ≤ ‖sourceW02AmbientContinuousSesquilinearForm i‖ :=
    sourceW02AmbientContinuousSesquilinearForm_norm_lower i
  have harg :
      2 * L_m i ≤
        sourceWeilOddTailHighTarget i + |Real.log Real.pi| + 6 := by
    unfold sourceWeilOddTailHighTarget
    nlinarith [norm_nonneg (sourcePrimeContinuousSesquilinearForm i),
      abs_nonneg (Real.log Real.pi)]
  have hband : (i.m : ℝ) ^ 2 ≤ sourceWeilOddTailBandRadius i := by
    calc
      (i.m : ℝ) ^ 2 = Real.exp (2 * L_m i) := by
        rw [show 2 * L_m i = L_m i + L_m i by ring, Real.exp_add]
        rw [show L_m i = Real.log (i.m : ℝ) by rfl,
          Real.exp_log hmpos]
        ring
      _ ≤ Real.exp
          (sourceWeilOddTailHighTarget i + |Real.log Real.pi| + 6) := by
        rw [Real.exp_le_exp]
        exact harg
      _ = sourceWeilOddTailBandRadius i := by
        rfl
  have hbranch :
      2 * L_m i * (sourceWeilOddTailBandRadius i + 1) ≤
        sourceWeilOddTailCutoffScale i := by
    unfold sourceWeilOddTailCutoffScale
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hscaleCutoff :
      sourceWeilOddTailCutoffScale i ≤
        (sourceWeilOddTailCutoff i : ℝ) := by
    have hceil :
        sourceWeilOddTailCutoffScale i ≤
          (Nat.ceil (sourceWeilOddTailCutoffScale i) : ℝ) :=
      Nat.le_ceil _
    unfold sourceWeilOddTailCutoff
    norm_num
    linarith
  have hmReal :
      (i.m : ℝ) <
        2 * L_m i * (sourceWeilOddTailBandRadius i + 1) := by
    have hmge : (2 : ℝ) ≤ i.m := by exact_mod_cast hm2
    have hband0 : 0 ≤ sourceWeilOddTailBandRadius i :=
      (sourceWeilOddTailBandRadius_pos i).le
    nlinarith
  have hmCutoff : i.m < sourceWeilOddTailCutoff i := by
    exact_mod_cast hmReal.trans_le (hbranch.trans hscaleCutoff)
  simpa [i, selectedFerrersPreAnchorIndex] using hmCutoff

/-- The carrier-domination premise required by the fixed-cutoff transfer is
false on every selected Ferrers cell. -/
theorem selectedFerrersPreAnchorIndex_not_cutoff_le_N (k : ℕ) :
    ¬ sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k) ≤
      (selectedFerrersPreAnchorIndex k).N :=
  Nat.not_le_of_lt
    (selectedFerrersPreAnchorIndex_N_lt_sourceWeilEvenTailCutoff k)

#print axioms sourceW02AmbientContinuousSesquilinearForm_norm_lower
#print axioms selectedFerrersPreAnchorIndex_N_lt_sourceWeilEvenTailCutoff
#print axioms selectedFerrersPreAnchorIndex_not_cutoff_le_N

end Q3.RouteB.D0Pstar
