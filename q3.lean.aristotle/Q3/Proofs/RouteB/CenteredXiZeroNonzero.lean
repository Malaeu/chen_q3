import Q3.Proofs.RouteB.ClassicalXiInterface
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed

open Complex Set Filter Topology
open scoped BigOperators Real ComplexOrder

noncomputable section

namespace Q3.RouteB

noncomputable def etaPairTerm (s : ℂ) (k : ℕ) : ℂ :=
  (((2 * k + 1 : ℕ) : ℂ) ^ (-s)) -
  (((2 * k + 2 : ℕ) : ℂ) ^ (-s))

noncomputable def etaPaired (s : ℂ) : ℂ :=
  ∑' k : ℕ, etaPairTerm s k

example (k : ℕ) :
    Differentiable ℂ (fun s : ℂ => etaPairTerm s k) := by
  unfold etaPairTerm
  fun_prop

theorem etaPairTerm_norm_le {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ‖etaPairTerm s k‖ ≤
      ‖s‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  let a : ℝ := 2 * k + 1
  let b : ℝ := 2 * k + 2
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  have hab : a ≤ b := by dsimp [a, b]; norm_num
  have ha : 0 < a := by dsimp [a]; positivity
  have hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (ha.trans_le hx.1))
      (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs))).differentiableAt
  have hbound : ∀ x ∈ Set.Icc a b,
      ‖deriv f x‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [show deriv f x = (-s) * (x : ℂ) ^ (-s - 1) by
      exact Complex.deriv_ofReal_cpow_const
        (ne_of_gt (ha.trans_le hx.1))
        (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs))]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1)]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)) (norm_nonneg s)
  have hmv := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  dsimp [f] at hmv
  have hba : |b - a| = 1 := by dsimp [a, b]; norm_num
  rw [hba, mul_one] at hmv
  rw [etaPairTerm, norm_sub_rev]
  convert hmv using 1 <;> norm_num [a, b] <;> push_cast

theorem etaPairTerm_summable_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    Summable (etaPairTerm s) := by
  let p : ℝ := -s.re - 1
  have hp : p < -1 := by dsimp [p]; linarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ p) :=
    Real.summable_nat_rpow.mpr hp
  have hshift : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hbase
  have hmaj : Summable (fun k : ℕ => ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ p) :=
    hshift.mul_left ‖s‖
  refine hmaj.of_norm_bounded (fun k => ?_)
  calc
    ‖etaPairTerm s k‖
        ≤ ‖s‖ * ((2 * k + 1 : ℕ) : ℝ) ^ p := by
          simpa only [p] using etaPairTerm_norm_le hs k
    _ ≤ ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ p := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity)
          (by
            have hk : k + 1 ≤ 2 * k + 1 := by omega
            exact_mod_cast hk)
          (by dsimp [p]; linarith)) (norm_nonneg s)

theorem etaPairTerm_norm_le_of_re_ge
    {σ R : ℝ} {s : ℂ} (hσ : 0 < σ) (hre : σ ≤ s.re)
    (hnorm : ‖s‖ ≤ R) (k : ℕ) :
    ‖etaPairTerm s k‖ ≤
      R * ((2 * k + 1 : ℕ) : ℝ) ^ (-σ - 1) := by
  have ha : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    norm_num
  calc
    ‖etaPairTerm s k‖
        ≤ ‖s‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
          etaPairTerm_norm_le (hσ.trans_le hre) k
    _ ≤ R * ((2 * k + 1 : ℕ) : ℝ) ^ (-σ - 1) := by
      apply mul_le_mul hnorm
      · exact Real.rpow_le_rpow_of_exponent_le ha (by linarith)
      · exact Real.rpow_nonneg (by positivity) _
      · exact (norm_nonneg s).trans hnorm

theorem summable_odd_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ p) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ p) :=
    Real.summable_nat_rpow.mpr hp
  have hshift : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hbase
  refine hshift.of_nonneg_of_le (fun _ => Real.rpow_nonneg (by positivity) _) (fun k => ?_)
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by
      have hk : k + 1 ≤ 2 * k + 1 := by omega
      exact_mod_cast hk)
    (by linarith)

theorem analyticOnNhd_etaPaired :
    AnalyticOnNhd ℂ etaPaired {s : ℂ | 0 < s.re} := by
  rw [analyticOnNhd_iff_differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)]
  intro s hs
  let σ : ℝ := s.re / 2
  let r : ℝ := s.re / 2
  let R : ℝ := ‖s‖ + r
  have hspos : 0 < s.re := hs
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hp : -σ - 1 < -1 := by linarith
  have hsum : Summable
      (fun k : ℕ => R * ((2 * k + 1 : ℕ) : ℝ) ^ (-σ - 1)) :=
    (summable_odd_rpow hp).mul_left R
  have hdiff : DifferentiableOn ℂ etaPaired (Metric.ball s r) := by
    unfold etaPaired
    apply differentiableOn_tsum_of_summable_norm hsum
    · intro k
      unfold etaPairTerm
      fun_prop
    · exact Metric.isOpen_ball
    · intro k w hw
      have hdist : ‖w - s‖ < r := by
        simpa only [dist_eq_norm] using Metric.mem_ball.mp hw
      have hreabs : |(w - s).re| ≤ ‖w - s‖ := abs_re_le_norm (w - s)
      have hreleft : -‖w - s‖ ≤ (w - s).re := (abs_le.mp hreabs).1
      simp only [sub_re] at hreleft
      have hre : σ ≤ w.re := by dsimp [σ, r] at *; linarith
      have hnorm : ‖w‖ ≤ R := by
        calc
          ‖w‖ = ‖(w - s) + s‖ := by congr 1 <;> abel
          _ ≤ ‖w - s‖ + ‖s‖ := norm_add_le _ _
          _ ≤ R := by dsimp [R]; linarith
      exact etaPairTerm_norm_le_of_re_ge hσ hre hnorm k
  exact ((hdiff s (Metric.mem_ball_self hr)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

private noncomputable def expHalfTerm (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (2 * π * I * (1 / 2 : ℝ) * n) / (n : ℂ) ^ s

private lemma half_unitAddCircle_ne_zero :
    ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  have hx : ∃ n : ℕ, n • (1 : ℝ) = (1 / 2 : ℝ) :=
    (AddCircle.coe_eq_zero_of_pos_iff (p := (1 : ℝ)) one_pos (by norm_num)).mp h
  obtain ⟨n, hn⟩ := hx
  simp only [nsmul_eq_mul, mul_one] at hn
  have hnltR : (n : ℝ) < 1 := by linarith
  have hnlt : n < 1 := by exact_mod_cast hnltR
  have hn0 : n = 0 := by omega
  norm_num [hn0] at hn

private lemma exp_two_pi_half_mul_nat (n : ℕ) :
    Complex.exp (2 * π * I * (1 / 2 : ℝ) * n) = (-1 : ℂ) ^ n := by
  rw [show 2 * π * I * (1 / 2 : ℝ) * n = (n : ℂ) * (π * I) by
    push_cast
    ring]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private lemma expHalfTerm_zero {s : ℂ} (hs : 0 < s.re) :
    expHalfTerm s 0 = 0 := by
  simp [expHalfTerm, Complex.zero_cpow (Complex.ne_zero_of_re_pos hs)]

private lemma expHalfTerm_odd (s : ℂ) (k : ℕ) :
    expHalfTerm s (2 * k + 1) =
      -(((2 * k + 1 : ℕ) : ℂ) ^ (-s)) := by
  rw [expHalfTerm, exp_two_pi_half_mul_nat]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  rw [cpow_neg]
  ring

private lemma expHalfTerm_even_pos (s : ℂ) (k : ℕ) :
    expHalfTerm s (2 * k + 2) =
      (((2 * k + 2 : ℕ) : ℂ) ^ (-s)) := by
  rw [expHalfTerm, exp_two_pi_half_mul_nat]
  have he : Even (2 * k + 2) := by
    convert even_two.mul_right (k + 1) using 1 <;> omega
  rw [Even.neg_one_pow he]
  rw [cpow_neg]
  simp

private lemma etaPairTerm_eq_neg_shift_pair (s : ℂ) (k : ℕ) :
    etaPairTerm s k =
      -(expHalfTerm s (2 * k + 1) + expHalfTerm s (2 * k + 2)) := by
  rw [expHalfTerm_odd, expHalfTerm_even_pos]
  unfold etaPairTerm
  ring

private theorem etaPaired_eq_neg_expZeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    etaPaired s = -HurwitzZeta.expZeta (1 / 2 : ℝ) s := by
  let f : ℕ → ℂ := expHalfTerm s
  let g : ℕ → ℂ := fun n => f (n + 1)
  have hf_has : HasSum f (HurwitzZeta.expZeta (1 / 2 : ℝ) s) := by
    simpa only [f, expHalfTerm] using
      (HurwitzZeta.hasSum_expZeta_of_one_lt_re (1 / 2 : ℝ) hs)
  have hf : Summable f := hf_has.summable
  have hg : Summable g := by
    simpa only [g] using (summable_nat_add_iff 1).mpr hf
  have hge : Summable (fun k : ℕ => g (2 * k)) := by
    simpa only [Function.comp_def, mul_comm] using
      hg.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have hgo : Summable (fun k : ℕ => g (2 * k + 1)) := by
    simpa only [Function.comp_def, mul_comm, add_comm] using
      hg.comp_injective
        ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have hsplit :
      (∑' k : ℕ, g (2 * k)) + (∑' k : ℕ, g (2 * k + 1)) = ∑' n : ℕ, g n :=
    tsum_even_add_odd hge hgo
  have hshift : (∑' n : ℕ, g n) = HurwitzZeta.expZeta (1 / 2 : ℝ) s := by
    have h := hf.sum_add_tsum_nat_add 1
    have hf0 : f 0 = 0 := by
      exact expHalfTerm_zero (zero_lt_one.trans hs)
    simp only [Finset.sum_range_one, hf0, zero_add, g] at h
    exact h.trans hf_has.tsum_eq
  calc
    etaPaired s = ∑' k : ℕ, -(g (2 * k) + g (2 * k + 1)) := by
      apply tsum_congr
      intro k
      unfold g f
      convert etaPairTerm_eq_neg_shift_pair s k using 1 <;> omega
    _ = -((∑' k : ℕ, g (2 * k)) + (∑' k : ℕ, g (2 * k + 1))) := by
      rw [← hge.tsum_add hgo, tsum_neg]
    _ = -(∑' n : ℕ, g n) := by rw [hsplit]
    _ = -HurwitzZeta.expZeta (1 / 2 : ℝ) s := by rw [hshift]

theorem etaPaired_eq_neg_expZeta
    {s : ℂ} (hs : 0 < s.re) :
    etaPaired s = -HurwitzZeta.expZeta (1 / 2 : ℝ) s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let V : Set ℂ := {z : ℂ | 1 < z.re}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hVopen : IsOpen V := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hexp_diff : Differentiable ℂ
      (fun z : ℂ => -HurwitzZeta.expZeta (1 / 2 : ℝ) z) := by
    exact (HurwitzZeta.differentiable_expZeta_of_ne_zero half_unitAddCircle_ne_zero).neg
  have hexp_an : AnalyticOnNhd ℂ
      (fun z : ℂ => -HurwitzZeta.expZeta (1 / 2 : ℝ) z) U := by
    rw [analyticOnNhd_iff_differentiableOn hUopen]
    exact hexp_diff.differentiableOn
  have htwoU : (2 : ℂ) ∈ U := by simp [U]
  have htwoV : (2 : ℂ) ∈ V := by simp [V]
  have hevent : etaPaired =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => -HurwitzZeta.expZeta (1 / 2 : ℝ) z) := by
    filter_upwards [hVopen.mem_nhds htwoV] with z hz
    exact etaPaired_eq_neg_expZeta_of_one_lt_re hz
  have hall : Set.EqOn etaPaired
      (fun z : ℂ => -HurwitzZeta.expZeta (1 / 2 : ℝ) z) U :=
    analyticOnNhd_etaPaired.eqOn_of_preconnected_of_eventuallyEq
      hexp_an (convex_halfSpace_re_gt 0).isPreconnected htwoU hevent
  exact hall hs

private lemma zmod_two_additive_char_decomposition :
    (fun k : ZMod 2 => ZMod.stdAddChar ((1 : ZMod 2) * k)) =
      (fun k : ZMod 2 => (1 : ℂ) - 2 * (1 : DirichletCharacter ℂ 2) k) := by
  funext k
  fin_cases k
  · change ZMod.stdAddChar (0 : ZMod 2) =
      (1 : ℂ) - 2 * (1 : DirichletCharacter ℂ 2) 0
    rw [(1 : DirichletCharacter ℂ 2).map_zero' (by norm_num)]
    simpa using (ZMod.stdAddChar (R := ℂ) (0 : ZMod 2)).map_zero
  · change ZMod.stdAddChar (1 : ZMod 2) =
      (1 : ℂ) - 2 * (1 : DirichletCharacter ℂ 2) 1
    rw [MulChar.one_apply (isUnit_one)]
    simp only [ZMod.stdAddChar_apply, ZMod.toCircle_apply, ZMod.val_one, Nat.cast_one,
      one_div]
    convert Complex.exp_pi_mul_I using 1 <;> ring

theorem expZeta_half_eq_factor_mul_riemannZeta
    {s : ℂ} (hs : s ≠ 1) :
    HurwitzZeta.expZeta (1 / 2 : ℝ) s =
      ((2 : ℂ) ^ (1 - s) - 1) * riemannZeta s := by
  have hadd := ZMod.LFunction_stdAddChar_eq_expZeta
    (N := 2) (1 : ZMod 2) s (Or.inl one_ne_zero)
  have hcircle : ZMod.toAddCircle (1 : ZMod 2) =
      ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [ZMod.toAddCircle_apply]
    norm_num [ZMod.val_one]
  have hadd' :
      ZMod.LFunction (fun k : ZMod 2 => ZMod.stdAddChar ((1 : ZMod 2) * k)) s =
        HurwitzZeta.expZeta (1 / 2 : ℝ) s := by
    simpa only [hcircle] using hadd
  have hzero := ZMod.LFunction_stdAddChar_eq_expZeta
    (N := 2) (0 : ZMod 2) s (Or.inr hs)
  have hconst : ZMod.LFunction (fun _ : ZMod 2 => (1 : ℂ)) s = riemannZeta s := by
    simpa [HurwitzZeta.expZeta_zero] using hzero
  have hlin :
      ZMod.LFunction (fun k : ZMod 2 => ZMod.stdAddChar ((1 : ZMod 2) * k)) s =
        ZMod.LFunction (fun _ : ZMod 2 => (1 : ℂ)) s -
          2 * DirichletCharacter.LFunctionTrivChar 2 s := by
    change
      ZMod.LFunction (fun k : ZMod 2 => ZMod.stdAddChar ((1 : ZMod 2) * k)) s =
        ZMod.LFunction (fun _ : ZMod 2 => (1 : ℂ)) s -
          2 * ZMod.LFunction (fun k : ZMod 2 => (1 : DirichletCharacter ℂ 2) k) s
    rw [zmod_two_additive_char_decomposition]
    unfold ZMod.LFunction
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
    ring_nf
    simp only [Finset.sum_mul, mul_assoc]
  have htriv := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
    (N := 2) hs
  rw [← hadd', hlin, hconst, htriv]
  norm_num [Nat.primeFactors]
  rw [show (1 - s : ℂ) = 1 + (-s) by ring,
    Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  ring

theorem etaPaired_half_ne_zero :
    etaPaired (1 / 2 : ℂ) ≠ 0 := by
  have hterm (k : ℕ) :
      etaPairTerm (1 / 2 : ℂ) k =
        (((((2 * k + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) -
          (((2 * k + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) : ℝ) : ℂ) := by
    unfold etaPairTerm
    have hexp : -(1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by norm_num
    have hodd : (((2 * k + 1 : ℕ) : ℂ)) =
        ((((2 * k + 1 : ℕ) : ℝ) : ℂ)) := by norm_cast
    have heven : (((2 * k + 2 : ℕ) : ℂ)) =
        ((((2 * k + 2 : ℕ) : ℝ) : ℂ)) := by norm_cast
    rw [hexp, hodd, heven]
    rw [← Complex.ofReal_cpow (by positivity :
      0 ≤ ((2 * k + 1 : ℕ) : ℝ)) (-1 / 2 : ℝ)]
    rw [← Complex.ofReal_cpow (by positivity :
      0 ≤ ((2 * k + 2 : ℕ) : ℝ)) (-1 / 2 : ℝ)]
    push_cast
    norm_num
  have hpos (k : ℕ) : 0 < etaPairTerm (1 / 2 : ℂ) k := by
    rw [hterm]
    exact_mod_cast sub_pos.mpr
      (Real.rpow_lt_rpow_of_neg (by positivity)
        (by norm_num) (by norm_num : (-1 / 2 : ℝ) < 0))
  have hsum : Summable (etaPairTerm (1 / 2 : ℂ)) :=
    etaPairTerm_summable_of_re_pos (by norm_num)
  exact ne_of_gt (hsum.tsum_pos (fun k => (hpos k).le) 0 (hpos 0))

theorem riemannZeta_half_ne_zero :
    riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  intro hzeta
  have hexp : HurwitzZeta.expZeta (1 / 2 : ℝ) (1 / 2 : ℂ) = 0 := by
    rw [expZeta_half_eq_factor_mul_riemannZeta (by norm_num), hzeta, mul_zero]
  have heta := etaPaired_eq_neg_expZeta (s := (1 / 2 : ℂ)) (by norm_num)
  rw [hexp, neg_zero] at heta
  exact etaPaired_half_ne_zero heta

theorem centeredXi_zero_ne_zero : centeredXi 0 ≠ 0 := by
  intro hxi
  have hriemannXi : riemannXi (1 / 2 : ℂ) = 0 := by
    simpa [centeredXi] using hxi
  have hzeta : riemannZeta (1 / 2 : ℂ) = 0 :=
    (riemannXi_eq_zero_iff_riemannZeta_eq_zero
      (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num)).mp hriemannXi
  exact riemannZeta_half_ne_zero hzeta

#print axioms etaPaired_eq_neg_expZeta
#print axioms expZeta_half_eq_factor_mul_riemannZeta
#print axioms etaPaired_half_ne_zero
#print axioms centeredXi_zero_ne_zero

end Q3.RouteB
