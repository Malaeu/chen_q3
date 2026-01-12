import Mathlib
import A3_FLOOR_v20_bounds_core
import A3_FLOOR_v19_monotonicity

open scoped BigOperators Real Classical
open Real Set
open Filter

noncomputable section

/-- Target floor constant. -/
def c_star : ℝ := 11 / 10

/-- Archimedean symbol kernel. -/
def g (B t ξ : ℝ) : ℝ := Q3.a ξ * w B t ξ

/-- Periodized symbol. -/
def P_A (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)

lemma a_antitone_on_Ioi : AntitoneOn Q3.a (Set.Ioi 0) := by
  intro x hx y hy hxy
  by_cases hxy' : x = y
  · simpa [hxy']
  · have hlt : x < y := lt_of_le_of_ne hxy hxy'
    exact (strictAntiOn_a hx hy hlt).le

lemma a_even (ξ : ℝ) : Q3.a (-ξ) = Q3.a ξ := by
  have h := Q3.a_star_even ξ
  have h' : (2 * Real.pi : ℝ) * Q3.a (-ξ) = (2 * Real.pi : ℝ) * Q3.a ξ := by
    simpa [Q3.a_star, mul_comm, mul_left_comm, mul_assoc] using h
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  exact mul_left_cancel₀ hpi h'

lemma w_even (B t ξ : ℝ) : w B t (-ξ) = w B t ξ := by
  simp [w, abs_neg, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma g_even (B t ξ : ℝ) : g B t (-ξ) = g B t ξ := by
  simp [g, a_even, w_even]

lemma a_zero_ge_a_half : Q3.a 0 ≥ Q3.a (1 / 2 : ℝ) := by
  have hcont : ContinuousWithinAt Q3.a (Set.Ici 0) 0 := by
    simpa using (continuousOn_a.continuousWithinAt (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)))
  have hseq :
      Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq'' :
      Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hseq
  have hseq' :
      Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhdsWithin (0 : ℝ) (Set.Ici 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f := fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) (s := Set.Ici 0) hseq'' ?_
    refine (Filter.Eventually.of_forall ?_)
    intro n
    have hpos : (0 : ℝ) ≤ (1 / ((n + 1 : ℕ) : ℝ)) := by
      have hpos' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      exact one_div_nonneg.mpr (le_of_lt hpos')
    simpa using hpos
  have hlim :
      Tendsto (fun n : ℕ => Q3.a (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhds (Q3.a 0)) :=
    hcont.tendsto.comp hseq'
  have hconst :
      Tendsto (fun n : ℕ => Q3.a (1 / 2 : ℝ)) atTop (nhds (Q3.a (1 / 2 : ℝ))) :=
    tendsto_const_nhds
  have hle :
      (fun n : ℕ => Q3.a (1 / 2 : ℝ)) ≤ᶠ[atTop]
        fun n : ℕ => Q3.a (1 / ((n + 1 : ℕ) : ℝ)) := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hxpos : (0 : ℝ) < (1 / ((n + 1 : ℕ) : ℝ)) := by
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      exact one_div_pos.mpr hpos
    have hx : (1 / ((n + 1 : ℕ) : ℝ)) ∈ Set.Ioi (0 : ℝ) := by
      simpa using hxpos
    have hy : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have hge : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hxy : (1 / ((n + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (2 : ℝ)) hge
      simpa [one_div] using h
    exact a_antitone_on_Ioi hx hy hxy
  have h := le_of_tendsto_of_tendsto hconst hlim hle
  exact h

lemma a_ge_a_half_on_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Q3.a θ ≥ Q3.a (1 / 2 : ℝ) := by
  by_cases hθ0 : θ = 0
  · simpa [hθ0] using a_zero_ge_a_half
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    have hθin : θ ∈ Set.Ioi (0 : ℝ) := hθpos
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have h := a_antitone_on_Ioi hθin hhalf hθ.2
    exact h

lemma w_lower_on_half {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    w B_min t_sym θ ≥ (9 / 20 : ℝ) := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθle : θ ≤ (1 / 2 : ℝ) := hθ.2
  have habs : |θ| = θ := abs_of_nonneg hθ0
  have hnonneg : 0 ≤ 1 - θ / B_min := by
    have : 0 ≤ 1 - θ / (3 : ℝ) := by nlinarith [hθle]
    simpa [B_min] using this
  have hfac1 : (5 / 6 : ℝ) ≤ 1 - θ / B_min := by
    have : (5 / 6 : ℝ) ≤ 1 - θ / (3 : ℝ) := by nlinarith [hθle]
    simpa [B_min] using this
  have hsq : θ^2 ≤ (1 / 2 : ℝ)^2 := by nlinarith [hθ0, hθle]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2 ≤
        -4 * Real.pi^2 * t_sym * θ^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) ≤
        (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
    exact mul_le_mul hfac1 hfac2 hpos hnonneg
  have hnonneg_abs : 0 ≤ 1 - |θ| / B_min := by
    simpa [habs] using hnonneg
  have hmax : max 0 (1 - |θ| / B_min) = 1 - |θ| / B_min := by
    exact max_eq_right hnonneg_abs
  have hrew :
      w B_min t_sym θ =
        (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
    unfold w
    calc
      max 0 (1 - |θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2)
          = (1 - |θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
              rw [hmax]
      _ = (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
            rw [habs]
  have hhalf :
      w B_min t_sym (1 / 2 : ℝ) =
        (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := by
    have hconst : (-3 * Real.pi^2 / 50 : ℝ) = -4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      w B_min t_sym (1 / 2 : ℝ) = (5 / 6 : ℝ) * Real.exp (-3 * Real.pi^2 / 50) := w_half_eq
      _ = (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := by
            rw [hconst]
  have hmain : w B_min t_sym (1 / 2 : ℝ) ≤ w B_min t_sym θ := by
    calc
      w B_min t_sym (1 / 2 : ℝ)
          = (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := hhalf
      _ ≤ (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := hmul
      _ = w B_min t_sym θ := hrew.symm
  exact le_trans w_half_bound hmain

lemma exp_neg_two_le_one_div_seven : Real.exp (-2 : ℝ) ≤ (1 / 7 : ℝ) := by
  have h_exp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    nlinarith
  have h_pow : (2.7 : ℝ)^2 ≤ (Real.exp 1)^2 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (2.7 : ℝ)) h_exp1 _
  have h_exp2 : (2.7 : ℝ)^2 ≤ Real.exp 2 := by
    have h := Real.exp_nat_mul 1 2
    simpa [pow_two] using (h_pow.trans_eq h.symm)
  have h_num : (7 : ℝ) ≤ (2.7 : ℝ)^2 := by norm_num
  have h_exp2_ge : (7 : ℝ) ≤ Real.exp 2 := by exact le_trans h_num h_exp2
  have hdiv : (1 / Real.exp 2 : ℝ) ≤ (1 / 7 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7) h_exp2_ge
  simpa [Real.exp_neg, one_div] using hdiv

lemma exp_neg_eight_le_one_div_2500 : Real.exp (-8 : ℝ) ≤ (1 / 2500 : ℝ) := by
  have h_exp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    nlinarith
  have h_pow : (2.7 : ℝ)^8 ≤ (Real.exp 1)^8 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (2.7 : ℝ)) h_exp1 _
  have h_exp8 : (2.7 : ℝ)^8 ≤ Real.exp 8 := by
    have h := Real.exp_nat_mul 1 8
    simpa using (h_pow.trans_eq h.symm)
  have h_num : (2500 : ℝ) ≤ (2.7 : ℝ)^8 := by norm_num
  have h_exp8_ge : (2500 : ℝ) ≤ Real.exp 8 := by exact le_trans h_num h_exp8
  have hdiv : (1 / Real.exp 8 : ℝ) ≤ (1 / 2500 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2500) h_exp8_ge
  simpa [Real.exp_neg, one_div] using hdiv

lemma exp_neg_five_le_one_div_100 : Real.exp (-5 : ℝ) ≤ (1 / 100 : ℝ) := by
  have h_exp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    nlinarith
  have h_pow : (2.7 : ℝ)^5 ≤ (Real.exp 1)^5 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (2.7 : ℝ)) h_exp1 _
  have h_exp5 : (2.7 : ℝ)^5 ≤ Real.exp 5 := by
    have h := Real.exp_nat_mul 1 5
    simpa using (h_pow.trans_eq h.symm)
  have h_num : (100 : ℝ) ≤ (2.7 : ℝ)^5 := by norm_num
  have h_exp5_ge : (100 : ℝ) ≤ Real.exp 5 := by exact le_trans h_num h_exp5
  have hdiv : (1 / Real.exp 5 : ℝ) ≤ (1 / 100 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) h_exp5_ge
  simpa [Real.exp_neg, one_div] using hdiv

lemma w_one_upper : w B_min t_sym 1 ≤ (2 / 21 : ℝ) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (25 / 3 : ℝ) ≤ Real.pi^2 := by nlinarith [hpi]
  have hle : -12 * Real.pi^2 / 50 ≤ (-2 : ℝ) := by
    nlinarith [hpi2]
  have h_exp : Real.exp (-12 * Real.pi^2 / 50) ≤ Real.exp (-2 : ℝ) := by
    exact Real.exp_le_exp.mpr hle
  have h_exp' : Real.exp (-12 * Real.pi^2 / 50) ≤ (1 / 7 : ℝ) :=
    h_exp.trans exp_neg_two_le_one_div_seven
  have hpos : 0 ≤ (2 / 3 : ℝ) := by norm_num
  calc
    w B_min t_sym 1
        = (2 / 3 : ℝ) * Real.exp (-12 * Real.pi^2 / 50) := w_one_eq
    _ ≤ (2 / 3 : ℝ) * (1 / 7 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp' hpos
    _ = (2 / 21 : ℝ) := by norm_num

lemma w_two_upper : w B_min t_sym 2 ≤ (1 / 7500 : ℝ) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (25 / 3 : ℝ) ≤ Real.pi^2 := by nlinarith [hpi]
  have hle : -48 * Real.pi^2 / 50 ≤ (-8 : ℝ) := by
    nlinarith [hpi2]
  have h_exp : Real.exp (-48 * Real.pi^2 / 50) ≤ Real.exp (-8 : ℝ) := by
    exact Real.exp_le_exp.mpr hle
  have h_exp' : Real.exp (-48 * Real.pi^2 / 50) ≤ (1 / 2500 : ℝ) :=
    h_exp.trans exp_neg_eight_le_one_div_2500
  have hpos : 0 ≤ (1 / 3 : ℝ) := by norm_num
  calc
    w B_min t_sym 2
        = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := w_two_eq
    _ ≤ (1 / 3 : ℝ) * (1 / 2500 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp' hpos
    _ = (1 / 7500 : ℝ) := by norm_num

lemma w_three_halves_eq :
    w B_min t_sym (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.exp (-27 * Real.pi^2 / 50) := by
  have habs : |(3 / 2 : ℝ)| = (3 / 2 : ℝ) := by norm_num
  have hnonneg : (0 : ℝ) ≤ 1 - (3 / 2 : ℝ) / 3 := by norm_num
  simp [w, B_min, t_sym, pow_two, habs, max_eq_right hnonneg, mul_comm, mul_left_comm, mul_assoc]
  ring_nf

lemma exp_bound_three_halves : Real.exp (-27 * Real.pi^2 / 50) ≤ (1 / 100 : ℝ) := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi2 : (3.1415 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [hpi]
  have h_bound : (5 : ℝ) ≤ (27 / 50 : ℝ) * Real.pi ^ 2 := by
    have h_num : (5 : ℝ) ≤ (27 / 50 : ℝ) * (3.1415 : ℝ) ^ 2 := by
      norm_num
    nlinarith [h_num, hpi2]
  have h_exp_le : Real.exp (-27 * Real.pi^2 / 50) ≤ Real.exp (-5 : ℝ) := by
    exact Real.exp_le_exp.mpr (by nlinarith [h_bound])
  exact h_exp_le.trans exp_neg_five_le_one_div_100

lemma w_three_halves_upper : w B_min t_sym (3 / 2 : ℝ) ≤ (1 / 200 : ℝ) := by
  have h_exp : Real.exp (-27 * Real.pi^2 / 50) ≤ (1 / 100 : ℝ) := exp_bound_three_halves
  have hpos : 0 ≤ (1 / 2 : ℝ) := by norm_num
  calc
    w B_min t_sym (3 / 2 : ℝ)
        = (1 / 2 : ℝ) * Real.exp (-27 * Real.pi^2 / 50) := w_three_halves_eq
    _ ≤ (1 / 2 : ℝ) * (1 / 100 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp hpos
    _ = (1 / 200 : ℝ) := by norm_num

lemma g0_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym θ ≥ (9 / 32 : ℝ) := by
  have ha : Q3.a θ ≥ (5 / 8 : ℝ) := by
    have h := a_ge_a_half_on_Icc hθ
    have hhalf : Q3.a (1 / 2 : ℝ) ≥ (5 / 8 : ℝ) := a_half_bound
    exact le_trans hhalf h
  have hw : w B_min t_sym θ ≥ (9 / 20 : ℝ) := w_lower_on_half hθ
  have ha_nonneg : 0 ≤ Q3.a θ := by nlinarith [ha]
  have hmul : (5 / 8 : ℝ) * (9 / 20 : ℝ) ≤ Q3.a θ * w B_min t_sym θ := by
    exact mul_le_mul ha hw (by norm_num) ha_nonneg
  have hconst : (5 / 8 : ℝ) * (9 / 20 : ℝ) = (9 / 32 : ℝ) := by norm_num
  simpa [g, hconst] using hmul

lemma g1_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (θ + 1) ≥ (-1 / 21 : ℝ) := by
  have hxI' : (0 : ℝ) < θ + 1 := by nlinarith [hθ.1]
  have hxI : θ + 1 ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (3 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : θ + 1 ≤ (3 / 2 : ℝ) := by nlinarith [hθ.2]
  have ha : Q3.a (θ + 1) ≥ (-1 / 2 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_three_half_bound h
  have hpos : 0 ≤ θ + 1 := by nlinarith [hθ.1]
  have habs : |θ + 1| = θ + 1 := abs_of_nonneg hpos
  have hnonneg : 0 ≤ 1 - (θ + 1) / B_min := by
    have : 0 ≤ 1 - (θ + 1) / (3 : ℝ) := by nlinarith [hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (θ + 1) / B_min ≤ (2 / 3 : ℝ) := by
    have : 1 - (θ + 1) / (3 : ℝ) ≤ (2 / 3 : ℝ) := by nlinarith [hθ.1]
    simpa [B_min] using this
  have hsq : (1 : ℝ)^2 ≤ (θ + 1)^2 := by nlinarith [hθ.1]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (θ + 1)^2 ≤
        -4 * Real.pi^2 * t_sym * (1 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) ≤
        (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (θ + 1) =
        (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |θ + 1| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |θ + 1| / B_min) = 1 - |θ + 1| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |θ + 1| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2)
          = (1 - |θ + 1| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
              rw [hmax]
      _ = (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
            rw [habs]
  have hrew1 :
      (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) =
        w B_min t_sym 1 := by
    have hconst : (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2 : ℝ) = -12 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2)
          = (2 / 3 : ℝ) * Real.exp (-12 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym 1 := by
            symm
            exact w_one_eq
  have hwle : w B_min t_sym (θ + 1) ≤ w B_min t_sym 1 := by
    calc
      w B_min t_sym (θ + 1)
          = (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
              simpa using hrew
      _ ≤ (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) := hmul
      _ = w B_min t_sym 1 := hrew1
  have hw : w B_min t_sym (θ + 1) ≤ (2 / 21 : ℝ) := le_trans hwle w_one_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (θ + 1) := by
    have h' : 0 ≤ max 0 (1 - |θ + 1| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 :
      Q3.a (θ + 1) * w B_min t_sym (θ + 1) ≥ (-1 / 2 : ℝ) * w B_min t_sym (θ + 1) := by
    exact mul_le_mul_of_nonneg_right ha hw_nonneg
  have hmul2 :
      (-1 / 2 : ℝ) * w B_min t_sym (θ + 1) ≥ (-1 / 2 : ℝ) * (2 / 21 : ℝ) := by
    have hneg : (-1 / 2 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hw hneg
  have hfinal :
      Q3.a (θ + 1) * w B_min t_sym (θ + 1) ≥ (-1 / 2 : ℝ) * (2 / 21 : ℝ) :=
    le_trans hmul2 hmul1
  have hconst : (-1 / 2 : ℝ) * (2 / 21 : ℝ) = (-1 / 21 : ℝ) := by norm_num
  simpa [g, hconst] using hfinal

lemma g2_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (θ + 2) ≥ (-7 / 50000 : ℝ) := by
  have hxI' : (0 : ℝ) < θ + 2 := by nlinarith [hθ.1]
  have hxI : θ + 2 ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (5 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : θ + 2 ≤ (5 / 2 : ℝ) := by nlinarith [hθ.2]
  have ha : Q3.a (θ + 2) ≥ (-21 / 20 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_five_half_bound h
  have hpos : 0 ≤ θ + 2 := by nlinarith [hθ.1]
  have habs : |θ + 2| = θ + 2 := abs_of_nonneg hpos
  have hnonneg : 0 ≤ 1 - (θ + 2) / B_min := by
    have : 0 ≤ 1 - (θ + 2) / (3 : ℝ) := by nlinarith [hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (θ + 2) / B_min ≤ (1 / 3 : ℝ) := by
    have : 1 - (θ + 2) / (3 : ℝ) ≤ (1 / 3 : ℝ) := by nlinarith [hθ.1]
    simpa [B_min] using this
  have hsq : (2 : ℝ)^2 ≤ (θ + 2)^2 := by nlinarith [hθ.1]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (θ + 2)^2 ≤
        -4 * Real.pi^2 * t_sym * (2 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) ≤
        (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (θ + 2) =
        (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |θ + 2| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |θ + 2| / B_min) = 1 - |θ + 2| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |θ + 2| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2)
          = (1 - |θ + 2| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
              rw [hmax]
      _ = (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
            rw [habs]
  have hrew1 :
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) =
        w B_min t_sym 2 := by
    have hconst : (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2 : ℝ) = -48 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2)
          = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym 2 := by
            symm
            exact w_two_eq
  have hwle : w B_min t_sym (θ + 2) ≤ w B_min t_sym 2 := by
    calc
      w B_min t_sym (θ + 2)
          = (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
              simpa using hrew
      _ ≤ (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := hmul
      _ = w B_min t_sym 2 := hrew1
  have hw : w B_min t_sym (θ + 2) ≤ (1 / 7500 : ℝ) := le_trans hwle w_two_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (θ + 2) := by
    have h' : 0 ≤ max 0 (1 - |θ + 2| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 :
      Q3.a (θ + 2) * w B_min t_sym (θ + 2) ≥ (-21 / 20 : ℝ) * w B_min t_sym (θ + 2) := by
    exact mul_le_mul_of_nonneg_right ha hw_nonneg
  have hmul2 :
      (-21 / 20 : ℝ) * (1 / 7500 : ℝ) ≤ (-21 / 20 : ℝ) * w B_min t_sym (θ + 2) := by
    have hneg : (-21 / 20 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hw hneg
  have hfinal : (-7 / 50000 : ℝ) ≤ Q3.a (θ + 2) * w B_min t_sym (θ + 2) := by
    have htmp :
        (-21 / 20 : ℝ) * (1 / 7500 : ℝ) ≤
          Q3.a (θ + 2) * w B_min t_sym (θ + 2) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_neg1_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (1 - θ) ≥ (-1 / 50 : ℝ) := by
  have hxI' : (0 : ℝ) < 1 - θ := by linarith [hθ.2]
  have hxI : 1 - θ ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : 1 - θ ≤ (1 : ℝ) := by linarith [hθ.1]
  have ha : Q3.a (1 - θ) ≥ (-1 / 50 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_one_bound h
  have hw_le : w B_min t_sym (1 - θ) ≤ (1 : ℝ) := by
    have hB : 0 < B_min := by norm_num [B_min]
    have hnonneg : 0 ≤ |1 - θ| / B_min := by
      have habs : 0 ≤ |1 - θ| := abs_nonneg _
      exact div_nonneg habs (le_of_lt hB)
    have hmax : max 0 (1 - |1 - θ| / B_min) ≤ (1 : ℝ) := by
      have : (1 - |1 - θ| / B_min) ≤ (1 : ℝ) := by nlinarith [hnonneg]
      exact max_le_iff.mpr ⟨by norm_num, this⟩
    have h_exp : Real.exp (-4 * Real.pi^2 * t_sym * (1 - θ)^2) ≤ (1 : ℝ) := by
      have hneg : (-4 * Real.pi^2 * t_sym * (1 - θ)^2 : ℝ) ≤ 0 := by
        have ht : 0 ≤ t_sym := by norm_num [t_sym]
        have hpi : 0 ≤ (Real.pi : ℝ)^2 := by nlinarith [Real.pi_pos]
        have hsq : 0 ≤ (1 - θ)^2 := by nlinarith
        have hpos : 0 ≤ 4 * Real.pi^2 * t_sym * (1 - θ)^2 := by
          have h4 : 0 ≤ (4 : ℝ) := by norm_num
          exact mul_nonneg (mul_nonneg (mul_nonneg h4 hpi) ht) hsq
        nlinarith
      simpa using (Real.exp_le_one_iff.mpr hneg)
    have h_exp_nonneg : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (1 - θ)^2) := by
      exact Real.exp_nonneg _
    calc
      w B_min t_sym (1 - θ)
          = max 0 (1 - |1 - θ| / B_min) *
              Real.exp (-4 * Real.pi^2 * t_sym * (1 - θ)^2) := by rfl
      _ ≤ 1 * 1 := by exact mul_le_mul hmax h_exp h_exp_nonneg (by norm_num)
      _ = (1 : ℝ) := by ring
  have hw_nonneg : 0 ≤ w B_min t_sym (1 - θ) := by
    have h' : 0 ≤ max 0 (1 - |1 - θ| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 :
      Q3.a (1 - θ) * w B_min t_sym (1 - θ) ≥ (-1 / 50 : ℝ) * w B_min t_sym (1 - θ) := by
    exact mul_le_mul_of_nonneg_right ha hw_nonneg
  have hmul2 :
      (-1 / 50 : ℝ) * (1 : ℝ) ≤ (-1 / 50 : ℝ) * w B_min t_sym (1 - θ) := by
    have hneg : (-1 / 50 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hw_le hneg
  have hfinal :
      (-1 / 50 : ℝ) ≤ Q3.a (1 - θ) * w B_min t_sym (1 - θ) := by
    have htmp : (-1 / 50 : ℝ) * (1 : ℝ) ≤ Q3.a (1 - θ) * w B_min t_sym (1 - θ) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_neg2_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (2 - θ) ≥ (-1 / 100 : ℝ) := by
  have hxI' : (0 : ℝ) < 2 - θ := by nlinarith [hθ.2]
  have hxI : 2 - θ ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : 2 - θ ≤ (2 : ℝ) := by nlinarith [hθ.1]
  have ha' : Q3.a (2 - θ) ≥ (-2 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_two_bound h
  have hxi_ge : (3 / 2 : ℝ) ≤ 2 - θ := by nlinarith [hθ.2]
  have habs : |2 - θ| = 2 - θ := abs_of_nonneg (by nlinarith [hθ.2])
  have hnonneg : 0 ≤ 1 - (2 - θ) / B_min := by
    have : 0 ≤ 1 - (2 - θ) / (3 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (2 - θ) / B_min ≤ (1 / 2 : ℝ) := by
    have : 1 - (2 - θ) / (3 : ℝ) ≤ (1 / 2 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hsq : (3 / 2 : ℝ)^2 ≤ (2 - θ)^2 := by nlinarith [hxi_ge]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (2 - θ)^2 ≤
        -4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) ≤
        (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (2 - θ) =
        (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |2 - θ| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |2 - θ| / B_min) = 1 - |2 - θ| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |2 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2)
          = (1 - |2 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
              rw [hmax]
      _ = (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
            rw [habs]
  have hrew1 :
      (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) =
        w B_min t_sym (3 / 2 : ℝ) := by
    have hconst : (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2 : ℝ) = -27 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2)
          = (1 / 2 : ℝ) * Real.exp (-27 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym (3 / 2 : ℝ) := by
            symm
            exact w_three_halves_eq
  have hwle : w B_min t_sym (2 - θ) ≤ w B_min t_sym (3 / 2 : ℝ) := by
    calc
      w B_min t_sym (2 - θ)
          = (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
              simpa using hrew
      _ ≤ (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) := hmul
      _ = w B_min t_sym (3 / 2 : ℝ) := hrew1
  have hwle' : w B_min t_sym (2 - θ) ≤ (1 / 200 : ℝ) :=
    le_trans hwle w_three_halves_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (2 - θ) := by
    have h' : 0 ≤ max 0 (1 - |2 - θ| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 : (-2 : ℝ) * w B_min t_sym (2 - θ) ≤ Q3.a (2 - θ) * w B_min t_sym (2 - θ) := by
    exact mul_le_mul_of_nonneg_right ha' hw_nonneg
  have hmul2 :
      (-2 : ℝ) * (1 / 200 : ℝ) ≤ (-2 : ℝ) * w B_min t_sym (2 - θ) := by
    have hneg : (-2 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hwle' hneg
  have hfinal : (-1 / 100 : ℝ) ≤ Q3.a (2 - θ) * w B_min t_sym (2 - θ) := by
    have htmp : (-2 : ℝ) * (1 / 200 : ℝ) ≤ Q3.a (2 - θ) * w B_min t_sym (2 - θ) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_neg3_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (3 - θ) ≥ (-1 / 2500 : ℝ) := by
  have hxI' : (0 : ℝ) < 3 - θ := by nlinarith [hθ.2]
  have hxI : 3 - θ ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (3 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : 3 - θ ≤ (3 : ℝ) := by nlinarith [hθ.1]
  have ha' : Q3.a (3 - θ) ≥ (-3 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_three_bound h
  have hxi_ge : (2 : ℝ) ≤ 3 - θ := by nlinarith [hθ.2]
  have habs : |3 - θ| = 3 - θ := abs_of_nonneg (by nlinarith [hθ.2])
  have hnonneg : 0 ≤ 1 - (3 - θ) / B_min := by
    have : 0 ≤ 1 - (3 - θ) / (3 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (3 - θ) / B_min ≤ (1 / 3 : ℝ) := by
    have : 1 - (3 - θ) / (3 : ℝ) ≤ (1 / 3 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hsq : (2 : ℝ)^2 ≤ (3 - θ)^2 := by nlinarith [hxi_ge]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (3 - θ)^2 ≤
        -4 * Real.pi^2 * t_sym * (2 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) ≤
        (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (3 - θ) =
        (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |3 - θ| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |3 - θ| / B_min) = 1 - |3 - θ| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |3 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2)
          = (1 - |3 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
              rw [hmax]
      _ = (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
            rw [habs]
  have hrew1 :
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) =
        w B_min t_sym 2 := by
    have hconst : (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2 : ℝ) = -48 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2)
          = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym 2 := by
            symm
            exact w_two_eq
  have hwle : w B_min t_sym (3 - θ) ≤ w B_min t_sym 2 := by
    calc
      w B_min t_sym (3 - θ)
          = (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
              simpa using hrew
      _ ≤ (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := hmul
      _ = w B_min t_sym 2 := hrew1
  have hwle' : w B_min t_sym (3 - θ) ≤ (1 / 7500 : ℝ) :=
    le_trans hwle w_two_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (3 - θ) := by
    have h' : 0 ≤ max 0 (1 - |3 - θ| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 : (-3 : ℝ) * w B_min t_sym (3 - θ) ≤ Q3.a (3 - θ) * w B_min t_sym (3 - θ) := by
    exact mul_le_mul_of_nonneg_right ha' hw_nonneg
  have hmul2 :
      (-3 : ℝ) * (1 / 7500 : ℝ) ≤ (-3 : ℝ) * w B_min t_sym (3 - θ) := by
    have hneg : (-3 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hwle' hneg
  have hfinal : (-1 / 2500 : ℝ) ≤ Q3.a (3 - θ) * w B_min t_sym (3 - θ) := by
    have htmp : (-3 : ℝ) * (1 / 7500 : ℝ) ≤ Q3.a (3 - θ) * w B_min t_sym (3 - θ) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_zero_of_large_index {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) {m : ℤ}
    (hm : m ≤ -4 ∨ 3 ≤ m) : g B_min t_sym (θ + m) = 0 := by
  have hm' : (B_min : ℝ) ≤ |θ + (m : ℝ)| := by
    cases hm with
    | inl hlow =>
        have hmle : (m : ℝ) ≤ -4 := by exact_mod_cast hlow
        have hsum : θ + (m : ℝ) ≤ (-7 / 2 : ℝ) := by nlinarith [hθ.2, hmle]
        have habs : |θ + (m : ℝ)| = -(θ + (m : ℝ)) := by
          exact abs_of_nonpos (by nlinarith [hsum])
        have hbound : (3 : ℝ) ≤ |θ + (m : ℝ)| := by
          nlinarith [habs, hsum]
        simpa [B_min] using hbound
    | inr hhigh =>
        have hmge : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhigh
        have hsum : (3 : ℝ) ≤ θ + (m : ℝ) := by nlinarith [hθ.1, hmge]
        have habs : |θ + (m : ℝ)| = θ + (m : ℝ) := by
          exact abs_of_nonneg (by nlinarith [hsum])
        have hbound : (3 : ℝ) ≤ |θ + (m : ℝ)| := by
          nlinarith [habs, hsum]
        simpa [B_min] using hbound
  have hlin : (1 - |θ + (m : ℝ)| / B_min) ≤ 0 := by
    have hm'' : (3 : ℝ) ≤ |θ + (m : ℝ)| := by
      simpa [B_min] using hm'
    have hlin' : (1 - |θ + (m : ℝ)| / (3 : ℝ)) ≤ 0 := by
      nlinarith [hm'']
    simpa [B_min] using hlin'
  have hmax : max 0 (1 - |θ + (m : ℝ)| / B_min) = 0 := by
    exact max_eq_left hlin
  calc
    g B_min t_sym (θ + m)
        = Q3.a (θ + m) *
            (max 0 (1 - |θ + (m : ℝ)| / B_min) *
              Real.exp (-4 * Real.pi^2 * t_sym * (θ + (m : ℝ))^2)) := by rfl
    _ = Q3.a (θ + m) * (0 * Real.exp (-4 * Real.pi^2 * t_sym * (θ + (m : ℝ))^2)) := by
          simp [hmax]
    _ = 0 := by ring

lemma sum_map_embedding {α β γ : Type*} [DecidableEq α] [AddCommMonoid γ]
    (s : Finset α) (e : α ↪ β) (f : β → γ) :
    (s.map e).sum f = s.sum (fun x => f (e x)) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha hs
    simp [ha, hs]

lemma P_A_eq_sum6 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    P_A B_min t_sym θ =
      2 * Real.pi *
        (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
          g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)) := by
  classical
  let f : ℤ → ℝ := fun m => g B_min t_sym (θ + m)
  have hzero : ∀ m, m ∉ Finset.Icc (-3 : ℤ) 2 → f m = 0 := by
    intro m hm
    have hm' : ¬((-3 : ℤ) ≤ m ∧ m ≤ 2) := by
      simpa [Finset.mem_Icc] using hm
    have hm'' := not_and_or.mp hm'
    cases hm'' with
    | inl h1 =>
        have hmle : m ≤ -4 := by linarith
        simpa [f, add_comm, add_left_comm, add_assoc] using
          g_zero_of_large_index hθ (Or.inl hmle)
    | inr h2 =>
        have hmge : 3 ≤ m := by linarith
        simpa [f, add_comm, add_left_comm, add_assoc] using
          g_zero_of_large_index hθ (Or.inr hmge)
  have htsum : (∑' m : ℤ, f m) = (Finset.Icc (-3 : ℤ) 2).sum f := by
    simpa using (tsum_eq_sum (f := f) (s := Finset.Icc (-3 : ℤ) 2) hzero)
  have hsum :
      (Finset.Icc (-3 : ℤ) 2).sum f =
        f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2 := by
    have hsum_map :
        (Finset.Icc (-3 : ℤ) 2).sum f =
          (Finset.range 6).sum (fun n => f (n + (-3 : ℤ))) := by
      -- unfold the Int interval as a mapped range
      simpa [Int.Icc_eq_finset_map, addLeftEmbedding, add_comm, add_left_comm, add_assoc] using
        (sum_map_embedding (s := Finset.range 6)
          (e := Nat.castEmbedding.trans (addLeftEmbedding (-3)))
          (f := f))
    have hsum_range :
        (Finset.range 6).sum (fun n => f (n + (-3 : ℤ))) =
          f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2 := by
      simp [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]
    exact hsum_map.trans hsum_range
  calc
    P_A B_min t_sym θ
        = 2 * Real.pi * ∑' m : ℤ, f m := by rfl
    _ = 2 * Real.pi * (f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2) := by
          simp [htsum, hsum]
    _ = 2 * Real.pi *
          (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
            g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)) := by
          simp [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma P_A_ge_c_star_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    P_A B_min t_sym θ ≥ c_star := by
  have hg0 : g B_min t_sym θ ≥ (9 / 32 : ℝ) := g0_lower hθ
  have hg1 : g B_min t_sym (θ + 1) ≥ (-1 / 21 : ℝ) := g1_lower hθ
  have hg2 : g B_min t_sym (θ + 2) ≥ (-7 / 50000 : ℝ) := g2_lower hθ
  have hgm1 : g B_min t_sym (1 - θ) ≥ (-1 / 50 : ℝ) := g_neg1_lower hθ
  have hgm2 : g B_min t_sym (2 - θ) ≥ (-1 / 100 : ℝ) := g_neg2_lower hθ
  have hgm3 : g B_min t_sym (3 - θ) ≥ (-1 / 2500 : ℝ) := g_neg3_lower hθ
  have hsum :
      g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
        g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)
          ≥ (1 / 5 : ℝ) := by
    have h1 : g B_min t_sym (θ - 1) = g B_min t_sym (1 - θ) := by
      have hneg : θ - 1 = -(1 - θ) := by ring
      calc
        g B_min t_sym (θ - 1) = g B_min t_sym (-(1 - θ)) := by
          rw [hneg]
        _ = g B_min t_sym (1 - θ) := by
          simpa using (g_even (B := B_min) (t := t_sym) (ξ := 1 - θ))
    have h2 : g B_min t_sym (θ - 2) = g B_min t_sym (2 - θ) := by
      have hneg : θ - 2 = -(2 - θ) := by ring
      calc
        g B_min t_sym (θ - 2) = g B_min t_sym (-(2 - θ)) := by
          rw [hneg]
        _ = g B_min t_sym (2 - θ) := by
          simpa using (g_even (B := B_min) (t := t_sym) (ξ := 2 - θ))
    have h3 : g B_min t_sym (θ - 3) = g B_min t_sym (3 - θ) := by
      have hneg : θ - 3 = -(3 - θ) := by ring
      calc
        g B_min t_sym (θ - 3) = g B_min t_sym (-(3 - θ)) := by
          rw [hneg]
        _ = g B_min t_sym (3 - θ) := by
          simpa using (g_even (B := B_min) (t := t_sym) (ξ := 3 - θ))
    nlinarith [hg0, hg1, hg2, hgm1, hgm2, hgm3, h1, h2, h3]
  have hmain := P_A_eq_sum6 hθ
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hpi_pos : 0 ≤ (1 / 5 : ℝ) := by norm_num
  have hconst : (6 : ℝ) * (1 / 5 : ℝ) ≥ c_star := by
    norm_num [c_star]
  have hfinal : 2 * Real.pi * (1 / 5 : ℝ) ≥ c_star := by
    have hmul : (6 : ℝ) * (1 / 5 : ℝ) ≤ 2 * Real.pi * (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hpi hpi_pos
    exact le_trans hconst hmul
  have hpospi : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
  calc
    P_A B_min t_sym θ
        = 2 * Real.pi *
            (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
              g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)) := hmain
    _ ≥ 2 * Real.pi * (1 / 5 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsum hpospi
    _ ≥ c_star := hfinal

-- Evenness of the periodized symbol (g is even, sum is reindexed).
lemma P_A_even (θ : ℝ) : P_A B_min t_sym (-θ) = P_A B_min t_sym θ := by
  have hsum_neg :
      ∑' m : ℤ, g B_min t_sym (-θ + m) =
        ∑' m : ℤ, g B_min t_sym (θ + (-m)) := by
    refine tsum_congr ?_
    intro m
    have hneg : -θ + (m : ℝ) = -(θ + (- (m : ℝ))) := by ring
    simpa [hneg] using (g_even (B := B_min) (t := t_sym) (ξ := θ + (- (m : ℝ))))
  have hsum :
      ∑' m : ℤ, g B_min t_sym (θ + (-m)) =
        ∑' m : ℤ, g B_min t_sym (θ + m) := by
    simpa using (Equiv.tsum_eq (Equiv.neg ℤ) (fun m : ℤ => g B_min t_sym (θ + m)))
  calc
    P_A B_min t_sym (-θ)
        = 2 * Real.pi * ∑' m : ℤ, g B_min t_sym (-θ + m) := by rfl
    _ = 2 * Real.pi * ∑' m : ℤ, g B_min t_sym (θ + m) := by
          simp [hsum_neg, hsum]
    _ = P_A B_min t_sym θ := by rfl

/-- Final A3 floor on [-1/2, 1/2]. -/
theorem P_A_ge_c_star {θ : ℝ} (hθ : θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    P_A B_min t_sym θ ≥ c_star := by
  by_cases hθpos : 0 ≤ θ
  · have hθ' : θ ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      exact ⟨hθpos, hθ.2⟩
    exact P_A_ge_c_star_nonneg hθ'
  · have hθ' : -θ ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      have h1 : 0 ≤ -θ := by nlinarith
      have h2 : -θ ≤ (1 / 2 : ℝ) := by nlinarith [hθ.1]
      exact ⟨h1, h2⟩
    have h := P_A_ge_c_star_nonneg hθ'
    simpa [P_A_even] using h
