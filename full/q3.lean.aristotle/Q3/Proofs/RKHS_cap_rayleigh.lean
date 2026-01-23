/-
RKHS cap for the Rayleigh quotient (compression form).
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Q3.Axioms
import Q3.Proofs.Rayleigh_utils
import Q3.Proofs.T_P_comp_utils
import Q3.Proofs.A3_bridge_rayleigh_first
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.C1_T_P_comp_dictEmbedding

set_option maxHeartbeats 0

open scoped BigOperators
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Q3.Proofs

private def normSq {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  ∑ i, (v i) ^ 2

private def quadForm {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

private def rayleighQ {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  quadForm A v / normSq v

private def rankOne {M : ℕ} (α : ℝ) (u : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => α * u i * u j

lemma inner_sq_le_normSq {M : ℕ} (u v : Fin M → ℝ) (hu : ∑ i, (u i) ^ 2 = 1) :
    (∑ i, u i * v i) ^ 2 ≤ ∑ i, (v i) ^ 2 := by
  have h_cauchy_schwarz :
      (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (f:=u) (g:=v))
  simpa [hu] using h_cauchy_schwarz

lemma quadForm_rankOne {M : ℕ} (α : ℝ) (u v : Fin M → ℝ) :
    quadForm (rankOne α u) v = α * (∑ i, u i * v i) ^ 2 := by
  simp +decide [Finset.mul_sum, pow_two, mul_comm, mul_left_comm, rankOne, quadForm]

lemma quadForm_sum {M : ℕ} {ι : Type*} [Fintype ι]
    (As : ι → Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
    quadForm (∑ n, As n) v = ∑ n, quadForm (As n) v := by
  unfold quadForm
  simp +decide only [mul_comm, Matrix.sum_apply, Finset.mul_sum]
  exact Eq.symm (by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _ =>
        Finset.sum_congr rfl (fun _ _ => by ring)))))

lemma rayleighQ_rankone_sum_le
    {M : ℕ} [NeZero M] {NodesK : Type} [Fintype NodesK] [DecidableEq NodesK]
    (coeff : NodesK → ℝ) (basis : NodesK → Fin M → ℝ)
    (v : Fin M → ℝ)
    (h_coeff_nonneg : ∀ n, 0 ≤ coeff n)
    (h_basis_norm : ∀ n, ∑ i : Fin M, (basis n i) ^ 2 = 1) :
    Q3.RayleighQuotient (fun i j => ∑ n : NodesK, coeff n * basis n i * basis n j) v
      ≤ ∑ n : NodesK, coeff n := by
  have hRayleigh :
      rayleighQ (fun i j => ∑ n : NodesK, coeff n * basis n i * basis n j) v
        ≤ ∑ n : NodesK, coeff n := by
    refine' div_le_of_le_mul₀ _ _ _
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · exact Finset.sum_nonneg (fun _ _ => h_coeff_nonneg _)
    · have h_quadForm_sum :
          quadForm (fun i j => ∑ n, coeff n * basis n i * basis n j) v
            = ∑ n, coeff n * (∑ i, basis n i * v i) ^ 2 := by
          unfold quadForm
          simp +decide only [mul_comm, mul_left_comm, Finset.mul_sum, pow_two]
          exact Eq.symm (by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun _ _ =>
              Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _ =>
                Finset.sum_congr rfl (fun _ _ => by ring)))))
      have h_inner_sq_le_normSq : ∀ n, (∑ i, basis n i * v i) ^ 2 ≤ normSq v := by
        intro n
        have h_inner_sq_le_normSq :
            (∑ i, basis n i * v i) ^ 2 ≤
              (∑ i, (basis n i) ^ 2) * (∑ i, (v i) ^ 2) := by
          simpa using
            (Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (f:=basis n) (g:=v))
        have hnorm := h_basis_norm n
        simpa [normSq, hnorm] using h_inner_sq_le_normSq
      simpa only [h_quadForm_sum, Finset.sum_mul] using
        Finset.sum_le_sum (fun n _ =>
          mul_le_mul_of_nonneg_left (h_inner_sq_le_normSq n) (h_coeff_nonneg n))
  simpa [rayleighQ, Q3.RayleighQuotient, quadForm, normSq] using hRayleigh

lemma fejer_heat_window_le_exp (B t ξ : ℝ) (hB : 0 < B) :
    Q3.fejer_heat_window B t ξ ≤ Real.exp (-4 * Real.pi ^ 2 * t * ξ ^ 2) := by
  unfold Q3.fejer_heat_window
  have hmax : max (0 : ℝ) (1 - |ξ| / B) ≤ 1 := by
    refine max_le_iff.mpr ?_
    constructor
    · norm_num
    · have : 0 ≤ |ξ| / B := by
        exact div_nonneg (abs_nonneg _) (le_of_lt hB)
      linarith
  have h := mul_le_mul_of_nonneg_right hmax
    (Real.exp_nonneg (-4 * Real.pi ^ 2 * t * ξ ^ 2))
  simpa [one_mul] using h

lemma w_Q_le_const (n : ℕ) (hn : n ≥ 2) :
    Q3.w_Q n ≤ 4 / Real.exp 1 := by
  have hlog : Real.log n / Real.sqrt n ≤ 2 / Real.exp 1 :=
    Q3.log_div_sqrt_le n hn
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hmul : 2 * ArithmeticFunction.vonMangoldt n ≤ 2 * Real.log (n : ℝ) := by
    nlinarith [hΛ]
  have hdiv :
      (2 * ArithmeticFunction.vonMangoldt n) / Real.sqrt n
        ≤ (2 * Real.log (n : ℝ)) / Real.sqrt n := by
    exact div_le_div_of_nonneg_right hmul (Real.sqrt_nonneg _)
  have hlog' :
      (2 * Real.log (n : ℝ)) / Real.sqrt n ≤ 4 / Real.exp 1 := by
    calc
      (2 * Real.log (n : ℝ)) / Real.sqrt n
          = 2 * (Real.log n / Real.sqrt n) := by ring
      _ ≤ 2 * (2 / Real.exp 1) := by
          exact mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)
      _ = 4 / Real.exp 1 := by ring
  have hw : Q3.w_Q n = (2 * ArithmeticFunction.vonMangoldt n) / Real.sqrt n := by
    unfold Q3.w_Q
    ring
  exact (le_trans (by simpa [hw] using hdiv) hlog')

lemma exp_log_sq_le_pow (n : ℕ) (hn : n ≥ 2) :
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2) ≤ (n : ℝ) ^ (-10 : ℝ) := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have ht : (10 : ℝ) ≤ t_rkhs_cap * Real.log 2 := by
    have ht' : (10 : ℝ) ≤ (40 : ℝ) * Real.log 2 := by
      nlinarith [hlog2]
    simpa [t_rkhs_cap] using ht'
  have hlog_ge : Real.log 2 ≤ Real.log n := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.log_le_log (by norm_num) h2
  have ht' : (10 : ℝ) ≤ t_rkhs_cap * Real.log n := by
    have hpos : 0 ≤ t_rkhs_cap := by norm_num [t_rkhs_cap]
    exact le_trans ht (mul_le_mul_of_nonneg_left hlog_ge hpos)
  have hlog_pos : 0 < Real.log n := by
    have h2 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hn)
    exact Real.log_pos h2
  have hmul : (10 : ℝ) * Real.log n ≤ t_rkhs_cap * (Real.log n) ^ 2 := by
    have := mul_le_mul_of_nonneg_right ht' (le_of_lt hlog_pos)
    simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using this
  have hneg : -t_rkhs_cap * (Real.log n) ^ 2 ≤ -10 * Real.log n := by
    nlinarith [hmul]
  have hexp : Real.exp (-t_rkhs_cap * (Real.log n) ^ 2) ≤ Real.exp (-10 * Real.log n) := by
    exact (Real.exp_le_exp).2 hneg
  have hpow : Real.exp (-10 * Real.log n) = (n : ℝ) ^ (-10 : ℝ) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 2) hn)
    -- rpow_def_of_pos gives: n^(-10) = exp (log n * (-10))
    have h := Real.rpow_def_of_pos hnpos (-10 : ℝ)
    -- rewrite to exp (-10 * log n)
    simpa [mul_comm] using h.symm
  calc
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2)
        ≤ Real.exp (-10 * Real.log n) := hexp
    _ = (n : ℝ) ^ (-10 : ℝ) := hpow

lemma exp_log_sq_le_inv_pow (n : ℕ) (hn : n ≥ 2) :
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2) ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
  have h := exp_log_sq_le_pow n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn)
  have hx : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hpow : (n : ℝ) ^ (-10 : ℝ) = 1 / (n : ℝ) ^ (10 : ℕ) := by
    calc
      (n : ℝ) ^ (-10 : ℝ) = ((n : ℝ) ^ (10 : ℝ))⁻¹ := by
        rw [Real.rpow_neg hx]
      _ = 1 / (n : ℝ) ^ (10 : ℕ) := by
        simp [Real.rpow_natCast, one_div]
  calc
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2)
        ≤ (n : ℝ) ^ (-10 : ℝ) := h
    _ = 1 / (n : ℝ) ^ (10 : ℕ) := hpow

private def pow_inv_shift (n : ℕ) : ℝ := 1 / (n + 2 : ℝ) ^ (10 : ℕ)

lemma pow_inv_shift_nonneg (n : ℕ) : 0 ≤ pow_inv_shift n := by
  have hpos : 0 ≤ (n + 2 : ℝ) ^ (10 : ℕ) := by positivity
  exact one_div_nonneg.mpr hpos

lemma pow_inv_shift_antitone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    pow_inv_shift n ≤ pow_inv_shift m := by
  have hmn' : (m + 2 : ℝ) ≤ n + 2 := by
    exact_mod_cast (Nat.add_le_add_right hmn 2)
  have hpow : (m + 2 : ℝ) ^ (10 : ℕ) ≤ (n + 2 : ℝ) ^ (10 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hmn' _
  have hpos : 0 < (m + 2 : ℝ) ^ (10 : ℕ) := by positivity
  have hpos' : 0 < (n + 2 : ℝ) ^ (10 : ℕ) := by positivity
  have hinv : 1 / (n + 2 : ℝ) ^ (10 : ℕ) ≤ 1 / (m + 2 : ℝ) ^ (10 : ℕ) := by
    exact one_div_le_one_div_of_le hpos hpow
  simpa [pow_inv_shift] using hinv

lemma summable_pow_inv_shift : Summable pow_inv_shift := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) := by
    exact (Real.summable_one_div_nat_pow (p:=10)).2 (by norm_num)
  have hsum_shift :
      Summable (fun n : ℕ => 1 / (n + 2 : ℝ) ^ (10 : ℕ)) := by
    simpa [one_div, add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff (f:=fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) 2).2 hsum
  refine hsum_shift.congr ?_
  intro n
  simp [pow_inv_shift]

lemma condensed_term_le_geom (k : ℕ) :
    (2 ^ k : ℝ) * pow_inv_shift (2 ^ k) ≤ (1 / (2 ^ 9 : ℝ)) ^ k := by
  have hkpos : 0 ≤ (2 ^ k : ℝ) := by positivity
  have hpow_le :
      pow_inv_shift (2 ^ k) ≤ 1 / (2 ^ k : ℝ) ^ (10 : ℕ) := by
    have hle : (2 ^ k : ℝ) ≤ 2 ^ k + 2 := by
      linarith
    have hpow : (2 ^ k : ℝ) ^ (10 : ℕ) ≤ (2 ^ k + 2 : ℝ) ^ (10 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity) hle _
    have hpos : 0 < (2 ^ k : ℝ) ^ (10 : ℕ) := by positivity
    have hinv : 1 / (2 ^ k + 2 : ℝ) ^ (10 : ℕ) ≤ 1 / (2 ^ k : ℝ) ^ (10 : ℕ) := by
      exact one_div_le_one_div_of_le hpos hpow
    simpa [pow_inv_shift] using hinv
  calc
    (2 ^ k : ℝ) * pow_inv_shift (2 ^ k)
        ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ) ^ (10 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hpow_le hkpos
    _ = 1 / (2 ^ k : ℝ) ^ (9 : ℕ) := by
          field_simp [pow_succ]
    _ = 1 / (2 ^ 9 : ℝ) ^ k := by
          have hpow : (2 ^ k : ℝ) ^ (9 : ℕ) = (2 ^ 9 : ℝ) ^ k := by
            calc
              (2 ^ k : ℝ) ^ (9 : ℕ) = (2 : ℝ) ^ (k * 9) := by
                simpa [pow_mul] using (pow_mul (2 : ℝ) k 9).symm
              _ = (2 : ℝ) ^ (9 * k) := by
                simp [mul_comm]
              _ = (2 ^ 9 : ℝ) ^ k := by
                simpa [pow_mul] using (pow_mul (2 : ℝ) 9 k)
          simpa [hpow]
    _ = (1 / (2 ^ 9 : ℝ)) ^ k := by
          simp [one_div_pow]

private def condensed_term (k : ℕ) : ℝ := (2 ^ k : ℝ) * pow_inv_shift (2 ^ k)

lemma condensed_term_nonneg (k : ℕ) : 0 ≤ condensed_term k := by
  have : 0 ≤ (2 ^ k : ℝ) := by positivity
  have : 0 ≤ pow_inv_shift (2 ^ k) := pow_inv_shift_nonneg _
  exact mul_nonneg (by positivity) this

lemma summable_geom : Summable (fun k : ℕ => (1 / (2 ^ 9 : ℝ)) ^ k) := by
  have h0 : 0 ≤ (1 / (2 ^ 9 : ℝ)) := by positivity
  have h1 : (1 / (2 ^ 9 : ℝ)) < 1 := by norm_num
  exact summable_geometric_of_lt_one h0 h1

lemma summable_condensed_term : Summable condensed_term := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_geom
  · intro k
    exact condensed_term_nonneg k
  · intro k
    simpa [condensed_term] using (condensed_term_le_geom k)

lemma tsum_geom_tail :
    (∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1)) = (1 / 511 : ℝ) := by
  set r : ℝ := (1 / (2 ^ 9 : ℝ))
  have h0 : 0 ≤ r := by
    simp [r]
  have h1 : r < 1 := by
    have h : (1 / (2 ^ 9 : ℝ)) < 1 := by
      norm_num
    simpa [r] using h
  have htsum : (∑' k : ℕ, r ^ k) = (1 - r)⁻¹ := by
    exact tsum_geometric_of_lt_one h0 h1
  calc
    (∑' k : ℕ, r ^ (k + 1))
        = r * (∑' k : ℕ, r ^ k) := by
            simp [pow_succ, mul_comm, mul_left_comm, mul_assoc, tsum_mul_left]
    _ = r * (1 - r)⁻¹ := by
            simpa [htsum]
    _ = (1 / 511 : ℝ) := by
            norm_num [r]

lemma tsum_condensed_term_le :
    ∑' k : ℕ, condensed_term k ≤ pow_inv_shift 1 + (1 / 511 : ℝ) := by
  have hsum_tail :
      Summable (fun k : ℕ => condensed_term (k + 1)) := by
    simpa [condensed_term] using (summable_nat_add_iff 1).2 summable_condensed_term
  have hgeom_tail :
      Summable (fun k : ℕ => (1 / (2 ^ 9 : ℝ)) ^ (k + 1)) := by
    simpa using (summable_nat_add_iff 1).2 summable_geom
  have htail_le :
      ∑' k : ℕ, condensed_term (k + 1) ≤
        ∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1) := by
    refine Summable.tsum_le_tsum ?_ hsum_tail hgeom_tail
    intro k
    simpa [condensed_term] using (condensed_term_le_geom (k + 1))
  have hsplit :
      ∑' k : ℕ, condensed_term k =
        condensed_term 0 + ∑' k : ℕ, condensed_term (k + 1) := by
    simpa [condensed_term] using (summable_condensed_term.sum_add_tsum_nat_add 1).symm
  calc
    ∑' k : ℕ, condensed_term k
        = condensed_term 0 + ∑' k : ℕ, condensed_term (k + 1) := hsplit
    _ ≤ condensed_term 0 + ∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1) := by
          exact add_le_add_left htail_le _
    _ = pow_inv_shift 1 + (1 / 511 : ℝ) := by
          have hgeom :
              (∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1)) = (1 / 511 : ℝ) :=
            tsum_geom_tail
          simpa [condensed_term] using congrArg (fun s => condensed_term 0 + s) hgeom

lemma tsum_pow_inv_shift_le :
    ∑' n : ℕ, pow_inv_shift n ≤
      pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ) := by
  have hsum_pow : Summable pow_inv_shift := by
    have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) := by
      exact (Real.summable_one_div_nat_pow (p:=10)).2 (by norm_num)
    have hsum_shift :
        Summable (fun n : ℕ => 1 / (n + 2 : ℝ) ^ (10 : ℕ)) := by
      simpa [one_div, add_comm, add_left_comm, add_assoc] using
        (summable_nat_add_iff (f:=fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) 2).2 hsum
    refine hsum_shift.congr ?_
    intro n
    simp [pow_inv_shift]
  have hbound :
      ∀ s : Finset ℕ, ∑ n ∈ s, pow_inv_shift n ≤
        pow_inv_shift 0 + ∑' k : ℕ, condensed_term k := by
    intro s
    classical
    by_cases hs : s.Nonempty
    · let N := s.max' hs
      have hsubset : s ⊆ Finset.range (2 ^ (N + 1)) := by
        intro n hn
        have hle : n ≤ N := by
          have hle' : n ≤ s.max' hs := Finset.le_max' s n hn
          simpa [N] using hle'
        have hlt : n < N + 1 := Nat.lt_succ_of_le hle
        have hpow : N + 1 ≤ 2 ^ (N + 1) := Nat.le_of_lt (Nat.lt_two_pow_self (n:=N + 1))
        exact Finset.mem_range.mpr (lt_of_lt_of_le hlt hpow)
      have hsum_le :
          (∑ n ∈ s, pow_inv_shift n) ≤
            ∑ n ∈ Finset.range (2 ^ (N + 1)), pow_inv_shift n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro n hn hnot
        exact pow_inv_shift_nonneg n
      have hcond :
          (∑ n ∈ Finset.range (2 ^ (N + 1)), pow_inv_shift n) ≤
            pow_inv_shift 0 + ∑ k ∈ Finset.range (N + 1), (2 ^ k : ℝ) • pow_inv_shift (2 ^ k) := by
        simpa using (Finset.le_sum_condensed (f:=pow_inv_shift)
          (hf:=by
            intro m n hm hmn
            exact pow_inv_shift_antitone (m:=m) (n:=n) hm hmn) (n:=N + 1))
      have hsum_condensed :
          (∑ k ∈ Finset.range (N + 1), (2 ^ k : ℝ) • pow_inv_shift (2 ^ k)) ≤
            ∑' k : ℕ, condensed_term k := by
        have hnonneg : ∀ k, 0 ≤ condensed_term k := by
          intro k
          exact condensed_term_nonneg k
        have hsum := (Summable.sum_le_tsum (s:=Finset.range (N + 1))
          (f:=condensed_term) (hs:=by
            intro k hk
            exact hnonneg k) (hf:=summable_condensed_term))
        simpa [condensed_term] using hsum
      exact le_trans hsum_le (le_trans hcond (by
        simpa [condensed_term] using add_le_add_left hsum_condensed (pow_inv_shift 0)))
    · have hnonneg : 0 ≤ pow_inv_shift 0 + ∑' k : ℕ, condensed_term k := by
        refine add_nonneg (pow_inv_shift_nonneg 0) ?_
        exact tsum_nonneg (fun _ => condensed_term_nonneg _)
      simp [Finset.not_nonempty_iff_eq_empty.mp hs, hnonneg]
  have htsum :
      ∑' n : ℕ, pow_inv_shift n ≤ pow_inv_shift 0 + ∑' k : ℕ, condensed_term k :=
    hsum_pow.tsum_le_of_sum_le hbound
  have hcond_le :
      ∑' k : ℕ, condensed_term k ≤ pow_inv_shift 1 + (1 / 511 : ℝ) :=
    tsum_condensed_term_le
  exact le_trans htsum (by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hcond_le (pow_inv_shift 0))

lemma exp_xi_log_eq (n : ℕ) :
    Real.exp (-(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)) =
      Real.exp (-(t_rkhs_cap * (Real.log n) ^ 2)) := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hpos :
      4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2
        = t_rkhs_cap * (Real.log n) ^ 2 := by
    unfold Q3.xi_n
    field_simp [pow_two, hpi]
    ring
  have hneg :
      -(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)
        = -(t_rkhs_cap * (Real.log n) ^ 2) := by
    nlinarith [hpos]
  simpa [hneg]

lemma exp_shift_le_exp_mul (K t xi tau : ℝ) (hxi : |xi| ≤ K) (ht : 0 ≤ t) :
    Real.exp (-4 * Real.pi ^ 2 * t * (xi - tau) ^ 2) ≤
      Real.exp (8 * Real.pi ^ 2 * t * K ^ 2) * Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) := by
  have hxi2 : xi ^ 2 ≤ K ^ 2 := by
    have hK : 0 ≤ K := by
      exact le_trans (abs_nonneg xi) hxi
    have h' : |xi| ≤ |K| := by
      simpa [abs_of_nonneg hK] using hxi
    exact (sq_le_sq).2 h'
  have hneg' : xi ^ 2 - 2 * K ^ 2 ≤ 0 := by nlinarith [hxi2]
  have hpos : 0 ≤ (xi - tau) ^ 2 := by nlinarith
  have hneg : xi ^ 2 - 2 * K ^ 2 ≤ (xi - tau) ^ 2 := by
    exact le_trans hneg' hpos
  have hcoef : -4 * Real.pi ^ 2 * t ≤ 0 := by
    have hpi : 0 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith [ht, hpi]
  have hmul :
      -4 * Real.pi ^ 2 * t * (xi - tau) ^ 2 ≤
        -4 * Real.pi ^ 2 * t * (xi ^ 2 - 2 * K ^ 2) := by
    exact mul_le_mul_of_nonpos_left hneg hcoef
  have hmul' :
      -4 * Real.pi ^ 2 * t * (xi - tau) ^ 2 ≤
        8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2 := by
    calc
      -4 * Real.pi ^ 2 * t * (xi - tau) ^ 2
          ≤ -4 * Real.pi ^ 2 * t * (xi ^ 2 - 2 * K ^ 2) := hmul
      _ = 8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2 := by ring
  have hexp :
      Real.exp (-4 * Real.pi ^ 2 * t * (xi - tau) ^ 2) ≤
        Real.exp (8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2) := by
    exact (Real.exp_le_exp).2 hmul'
  calc
    Real.exp (-4 * Real.pi ^ 2 * t * (xi - tau) ^ 2)
        ≤ Real.exp (8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2) := hexp
    _ = Real.exp (8 * Real.pi ^ 2 * t * K ^ 2) *
        Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) := by
      simp [sub_eq_add_neg, Real.exp_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]

def rho_oneK (K : ℝ) : ℝ :=
  Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) * rho_one

lemma weight_term_le_pow_inv (K B : ℝ) (hB : 0 < B) (n : Q3.Nodes K) :
    ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
      ≤ (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
  have hn : (n : ℕ) ≥ 2 := n.property.2
  have hwindow_nonneg :
      0 ≤ Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) :=
    Q3.fejer_heat_window_nonneg _ _ _
  have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
  have hprod_nonneg :
      0 ≤ Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) :=
    mul_nonneg hw_nonneg hwindow_nonneg
  have hnorm :
      ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) := by
    have hnorm' :
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ =
          |Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)| := by
      simp
    simpa [abs_of_nonneg hprod_nonneg] using hnorm'
  have hfej :
      Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)
        ≤ Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
    exact fejer_heat_window_le_exp B t_rkhs_cap (Q3.xi_n n) hB
  have hexp :
      Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)
        ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
    have hexp0 := exp_log_sq_le_inv_pow (n:=(n : ℕ)) hn
    have hexp1 :
        Real.exp (-(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2))
          ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
      simpa [exp_xi_log_eq (n:=(n : ℕ))] using hexp0
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hexp1
  have hw : Q3.w_Q n ≤ 4 / Real.exp 1 := w_Q_le_const (n:=(n : ℕ)) hn
  calc
    ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) := hnorm
    _ ≤ (4 / Real.exp 1) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
          exact mul_le_mul hw hfej hwindow_nonneg (by positivity)
    _ ≤ (4 / Real.exp 1) * (1 / (n : ℝ) ^ (10 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
          have hn2 : 2 ≤ (n : ℕ) := hn
          have hbase : (↑↑n : ℝ) - ((2 : ℕ) : ℝ) + 2 = (↑↑n : ℝ) := by
            ring
          rw [pow_inv_shift, Nat.cast_sub hn2, hbase]

lemma weight_term_shift_le_pow_inv (K B tau : ℝ) (hB : 0 < B) (n : Q3.Nodes K) :
    ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
      ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
        (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
  have hn : (n : ℕ) ≥ 2 := n.property.2
  have hwindow_nonneg :
      0 ≤ Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    simpa [Q3.phi_shift] using
      Q3.fejer_heat_window_nonneg B t_rkhs_cap (Q3.xi_n n - tau)
  have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
  have hprod_nonneg :
      0 ≤ Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) :=
    mul_nonneg hw_nonneg hwindow_nonneg
  have hnorm :
      ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    have hnorm' :
        ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ =
          |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
      simp
    simpa [abs_of_nonneg hprod_nonneg] using hnorm'
  have hfej :
      Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)
        ≤ Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n - tau) ^ 2) := by
    simpa [Q3.phi_shift] using
      (fejer_heat_window_le_exp B t_rkhs_cap (Q3.xi_n n - tau) hB)
  have hshift :
      Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n - tau) ^ 2)
        ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
    have hxi : |Q3.xi_n n| ≤ K := n.property.1
    have ht : 0 ≤ t_rkhs_cap := by nlinarith [one_le_t_rkhs_cap]
    exact exp_shift_le_exp_mul (K:=K) (t:=t_rkhs_cap) (xi:=Q3.xi_n n) (tau:=tau) hxi ht
  have hphi :
      Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤
        Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
    exact le_trans hfej hshift
  have hexp :
      Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)
        ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
    have hexp0 := exp_log_sq_le_inv_pow (n:=(n : ℕ)) hn
    have hexp1 :
        Real.exp (-(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2))
          ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
      simpa [exp_xi_log_eq (n:=(n : ℕ))] using hexp0
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hexp1
  have hw : Q3.w_Q n ≤ 4 / Real.exp 1 := w_Q_le_const (n:=(n : ℕ)) hn
  have hconst : 0 ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) := by
    exact Real.exp_nonneg _
  calc
    ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := hnorm
    _ ≤ (4 / Real.exp 1) *
          (Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)) := by
          exact mul_le_mul hw hphi hwindow_nonneg (by positivity)
    _ = Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          ((4 / Real.exp 1) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)) := by
          ring
    _ ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          ((4 / Real.exp 1) * (1 / (n : ℝ) ^ (10 : ℕ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hconst
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
          have hn2 : 2 ≤ (n : ℕ) := hn
          have hbase : (↑↑n : ℝ) - ((2 : ℕ) : ℝ) + 2 = (↑↑n : ℝ) := by
            ring
          simp [pow_inv_shift, Nat.cast_sub hn2, hbase, mul_assoc, mul_left_comm, mul_comm]

lemma weight_sum_le_rho_one (K B : ℝ) (hB : 0 < B) [Fintype (Q3.Nodes K)] :
    ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
      ≤ rho_one := by
  classical
  let idx : Q3.Nodes K → ℕ := fun n => (n : ℕ) - 2
  have hidx_inj : Set.InjOn idx (Set.univ : Set (Q3.Nodes K)) := by
    intro a ha b hb h
    have ha2 : 2 ≤ (a : ℕ) := a.property.2
    have hb2 : 2 ≤ (b : ℕ) := b.property.2
    have h' := congrArg (fun x => x + 2) h
    have hab : (a : ℕ) = (b : ℕ) := by
      simpa [idx, Nat.sub_add_cancel ha2, Nat.sub_add_cancel hb2] using h'
    exact Subtype.ext hab
  have hterm :
      ∀ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    intro n
    simpa [idx] using weight_term_le_pow_inv (K:=K) (B:=B) hB n
  have hsum_le :
      ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        ≤ ∑ n : Q3.Nodes K, (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact hterm n
  have hsum_image :
      ∑ n : Q3.Nodes K, (4 / Real.exp 1) * pow_inv_shift (idx n) =
        Finset.sum (Finset.univ.image idx)
          (fun m => (4 / Real.exp 1) * pow_inv_shift m) := by
    have hidx_inj' :
        Set.InjOn idx (↑(Finset.univ : Finset (Q3.Nodes K)) : Set (Q3.Nodes K)) := by
      intro a ha b hb h
      exact hidx_inj (by trivial) (by trivial) h
    simpa using (Finset.sum_image (s:=Finset.univ)
      (f:=fun m => (4 / Real.exp 1) * pow_inv_shift m) (g:=idx) hidx_inj').symm
  have hsum_le_tsum :
      Finset.sum (Finset.univ.image idx)
          (fun m => (4 / Real.exp 1) * pow_inv_shift m) ≤
        ∑' m : ℕ, (4 / Real.exp 1) * pow_inv_shift m := by
    have hsum : Summable (fun m : ℕ => (4 / Real.exp 1) * pow_inv_shift m) := by
      exact Summable.mul_left (4 / Real.exp 1) summable_pow_inv_shift
    have hnonneg : ∀ m, 0 ≤ (4 / Real.exp 1) * pow_inv_shift m := by
      intro m
      exact mul_nonneg (by positivity) (pow_inv_shift_nonneg m)
    exact Summable.sum_le_tsum (s:=Finset.univ.image idx)
      (f:=fun m : ℕ => (4 / Real.exp 1) * pow_inv_shift m)
      (hs:=by intro m hm; exact hnonneg m) (hf:=hsum)
  have htsum_bound :
      ∑' m : ℕ, (4 / Real.exp 1) * pow_inv_shift m ≤
        (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
    have hnonneg : 0 ≤ (4 / Real.exp 1 : ℝ) := by positivity
    calc
      ∑' m : ℕ, (4 / Real.exp 1) * pow_inv_shift m
          = (4 / Real.exp 1) * ∑' m : ℕ, pow_inv_shift m := by
              simpa using (tsum_mul_left (a:=4 / Real.exp 1) (f:=pow_inv_shift))
      _ ≤ (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left tsum_pow_inv_shift_le hnonneg
  have hconst : (4 / Real.exp 1 : ℝ) ≤ 2 := by
    have h : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hpos : 0 < Real.exp 1 := by exact Real.exp_pos 1
    have h' : 4 ≤ 2 * Real.exp 1 := by nlinarith [h]
    exact (div_le_iff₀ hpos).2 h'
  have hS :
      (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 100 : ℝ) := by
    norm_num [pow_inv_shift]
  have hfinal :
      (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
        ≤ rho_one := by
    have hnonneg :
        0 ≤ (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      nlinarith [pow_inv_shift_nonneg 0, pow_inv_shift_nonneg 1]
    have hmul : (4 / Real.exp 1) *
        (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
          ≤ 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hconst hnonneg
    have hS' : 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 25 : ℝ) := by
      nlinarith [hS]
    simpa [rho_one] using (le_trans hmul hS')
  exact le_trans hsum_le (by
    simpa [hsum_image] using le_trans hsum_le_tsum (le_trans htsum_bound hfinal))

lemma weight_sum_le_rho_oneK (K B tau : ℝ) (hB : 0 < B) [Fintype (Q3.Nodes K)] :
    ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
      ≤ rho_oneK K := by
  classical
  let idx : Q3.Nodes K → ℕ := fun n => (n : ℕ) - 2
  let C : ℝ := Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2)
  have hC_nonneg : 0 ≤ C := by exact Real.exp_nonneg _
  have hidx_inj : Set.InjOn idx (Set.univ : Set (Q3.Nodes K)) := by
    intro a ha b hb h
    have ha2 : 2 ≤ (a : ℕ) := a.property.2
    have hb2 : 2 ≤ (b : ℕ) := b.property.2
    have h' := congrArg (fun x => x + 2) h
    have hab : (a : ℕ) = (b : ℕ) := by
      simpa [idx, Nat.sub_add_cancel ha2, Nat.sub_add_cancel hb2] using h'
    exact Subtype.ext hab
  have hterm :
      ∀ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
          ≤ C * (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    intro n
    simpa [idx, C, mul_assoc, mul_left_comm, mul_comm] using
      weight_term_shift_le_pow_inv (K:=K) (B:=B) (tau:=tau) hB n
  have hsum_le :
      ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
        ≤ ∑ n : Q3.Nodes K, C * (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact hterm n
  have hsum_image :
      ∑ n : Q3.Nodes K, C * (4 / Real.exp 1) * pow_inv_shift (idx n) =
        Finset.sum (Finset.univ.image idx)
          (fun m => C * (4 / Real.exp 1) * pow_inv_shift m) := by
    have hidx_inj' :
        Set.InjOn idx (↑(Finset.univ : Finset (Q3.Nodes K)) : Set (Q3.Nodes K)) := by
      intro a ha b hb h
      exact hidx_inj (by trivial) (by trivial) h
    simpa using (Finset.sum_image (s:=Finset.univ)
      (f:=fun m => C * (4 / Real.exp 1) * pow_inv_shift m) (g:=idx) hidx_inj').symm
  have hsum_le_tsum :
      Finset.sum (Finset.univ.image idx)
          (fun m => C * (4 / Real.exp 1) * pow_inv_shift m) ≤
        ∑' m : ℕ, C * (4 / Real.exp 1) * pow_inv_shift m := by
    have hsum : Summable (fun m : ℕ => C * (4 / Real.exp 1) * pow_inv_shift m) := by
      exact Summable.mul_left (C * (4 / Real.exp 1)) summable_pow_inv_shift
    have hnonneg : ∀ m, 0 ≤ C * (4 / Real.exp 1) * pow_inv_shift m := by
      intro m
      exact mul_nonneg (mul_nonneg hC_nonneg (by positivity)) (pow_inv_shift_nonneg m)
    exact Summable.sum_le_tsum (s:=Finset.univ.image idx)
      (f:=fun m : ℕ => C * (4 / Real.exp 1) * pow_inv_shift m)
      (hs:=by intro m hm; exact hnonneg m) (hf:=hsum)
  have htsum_bound :
      ∑' m : ℕ, C * (4 / Real.exp 1) * pow_inv_shift m ≤
        C * (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
    have hnonneg : 0 ≤ (C * (4 / Real.exp 1 : ℝ)) := by
      exact mul_nonneg hC_nonneg (by positivity)
    calc
      ∑' m : ℕ, C * (4 / Real.exp 1) * pow_inv_shift m
          = (C * (4 / Real.exp 1)) * ∑' m : ℕ, pow_inv_shift m := by
              simpa [mul_assoc] using
                (tsum_mul_left (a:=C * (4 / Real.exp 1)) (f:=pow_inv_shift))
      _ ≤ (C * (4 / Real.exp 1)) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left tsum_pow_inv_shift_le hnonneg
  have hconst : (4 / Real.exp 1 : ℝ) ≤ 2 := by
    have h : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hpos : 0 < Real.exp 1 := by exact Real.exp_pos 1
    have h' : 4 ≤ 2 * Real.exp 1 := by nlinarith [h]
    exact (div_le_iff₀ hpos).2 h'
  have hS :
      (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 100 : ℝ) := by
    norm_num [pow_inv_shift]
  have hfinal_base :
      (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
        ≤ rho_one := by
    have hnonneg :
        0 ≤ (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      nlinarith [pow_inv_shift_nonneg 0, pow_inv_shift_nonneg 1]
    have hmul : (4 / Real.exp 1) *
        (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
          ≤ 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hconst hnonneg
    have hS' : 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 25 : ℝ) := by
      nlinarith [hS]
    simpa [rho_one] using (le_trans hmul hS')
  have hfinal :
      C * (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
        ≤ rho_oneK K := by
    have hmul := mul_le_mul_of_nonneg_left hfinal_base hC_nonneg
    simpa [rho_oneK, C, mul_assoc] using hmul
  exact le_trans hsum_le (by
    simpa [hsum_image] using le_trans hsum_le_tsum (le_trans htsum_bound hfinal))

lemma prime_rayleigh_shift_le_rho_oneK (K B tau : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hM : 0 < 2 * M + 1) :
    (2 * M + 1 : ℝ) *
        Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t_rkhs_cap tau M)
          (Q3.Proofs.RayleighQId.basis0 M) ≤ rho_oneK K := by
  have hsum_norm :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
        ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hwindow_nonneg :
        0 ≤ Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
      simpa [Q3.phi_shift] using
        Q3.fejer_heat_window_nonneg B t_rkhs_cap (Q3.xi_n n - tau)
    have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
    have hprod_nonneg :
        0 ≤ Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) :=
      mul_nonneg hw_nonneg hwindow_nonneg
    have hnorm' :
        |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| =
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
      have hnorm_real :
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ =
            |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        simpa [Real.norm_eq_abs] using
          (norm_real (Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)))
      exact hnorm_real.symm
    calc
      Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
          |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        exact (abs_of_nonneg hprod_nonneg).symm
      _ = ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := hnorm'
  have h_weight_sum :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ rho_oneK K := by
    simpa [hsum_norm] using weight_sum_le_rho_oneK (K:=K) (B:=B) (tau:=tau) hB
  have hprime :
      (2 * M + 1 : ℝ) *
          Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t_rkhs_cap tau M)
            (Q3.Proofs.RayleighQId.basis0 M) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    exact Q3.Proofs.RayleighQId.prime_rayleigh_eq_shift (K:=K) (B:=B) (t:=t_rkhs_cap)
      (tau:=tau) (M:=M) hM
  calc
    (2 * M + 1 : ℝ) *
        Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t_rkhs_cap tau M)
          (Q3.Proofs.RayleighQId.basis0 M)
        = ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := hprime
    _ ≤ rho_oneK K := h_weight_sum

lemma prime_term_phi_shift_le_rho_oneK (K B tau : ℝ) (hB : 0 < B) (hK : |tau| + B ≤ K)
    [Fintype (Q3.Nodes K)] :
    Q3.prime_term (fun ξ => Q3.phi_shift B t_rkhs_cap tau ξ) ≤ rho_oneK K := by
  have hsum :
      Q3.prime_term (fun ξ => Q3.phi_shift B t_rkhs_cap tau ξ) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    simpa using
      (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift
        (B:=B) (t:=t_rkhs_cap) (tau:=tau) (K:=K) hB hK)
  have hsum_norm :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
        ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hwindow_nonneg :
        0 ≤ Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
      simpa [Q3.phi_shift] using
        Q3.fejer_heat_window_nonneg B t_rkhs_cap (Q3.xi_n n - tau)
    have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
    have hprod_nonneg :
        0 ≤ Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) :=
      mul_nonneg hw_nonneg hwindow_nonneg
    have hnorm' :
        |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| =
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
      have hnorm_real :
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ =
            |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        simpa [Real.norm_eq_abs] using
          (norm_real (Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)))
      exact hnorm_real.symm
    calc
      Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
          |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        exact (abs_of_nonneg hprod_nonneg).symm
      _ = ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := hnorm'
  have hweight :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ rho_oneK K := by
    simpa [hsum_norm] using (weight_sum_le_rho_oneK (K:=K) (B:=B) (tau:=tau) hB)
  simpa [hsum] using hweight

lemma T_P_comp_real_opNorm_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    ‖Q3.T_P_comp_real K B t M‖ ≤
      ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
  classical
  have hsymm := T_P_comp_real_isSymm (K:=K) (B:=B) (t:=t) (M:=M)
  have hC_nonneg :
      0 ≤ ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
    refine Finset.sum_nonneg ?_
    intro n hn
    exact norm_nonneg _
  have hrow :
      ∀ i, ∑ j, |Q3.T_P_comp_real K B t M i j| ≤
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
    intro i
    exact T_P_comp_real_row_sum_le_weight_sum (K:=K) (B:=B) (t:=t) (M:=M) i
  exact Q3.Schur_test (A:=Q3.T_P_comp_real K B t M) hsymm
    (C:=∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖)
    hC_nonneg hrow

lemma T_P_comp_real_opNorm_le_via_C1_dictEmbedding
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1)
    (T : H →L[ℝ] H)
    (hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap =
        Q3.Proofs.C1Embedding.compression
          (Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim) T) :
    ‖Q3.T_P_comp_real K B t M‖ ≤ ‖T‖ := by
  have hC1 :
      ‖(Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap‖ ≤ ‖T‖ :=
    T_P_comp_real_opNorm_le_of_dictEmbedding (K := K) (B := B) (t := t) (M := M)
      (d := d) (hdim := hdim) (T := T) hA
  simpa [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using hC1

lemma rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding
    (K B : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1)
    (T : H →L[ℝ] H)
    (hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t_rkhs_cap M)).toContinuousLinearMap =
        Q3.Proofs.C1Embedding.compression
          (Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim) T)
    (hT : ‖T‖ ≤ rho_one) :
    ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  intro v hv
  have hnorm' :
      ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤ ‖T‖ :=
    T_P_comp_real_opNorm_le_via_C1_dictEmbedding (K := K) (B := B) (t := t_rkhs_cap)
      (M := M) (d := d) (hdim := hdim) (T := T) hA
  have hnorm :
      ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤ rho_one := by
    exact le_trans hnorm' hT
  have hRayleigh :
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤
        ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ :=
    RayleighQuotient_le_opNorm (A:=Q3.T_P_comp_real K B t_rkhs_cap M) (v:=v) hv
  exact le_trans hRayleigh hnorm

lemma rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding_lift
    (K B : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1)
    (h_weight_sum :
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ ≤ rho_one) :
    ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  classical
  let ι :=
    Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim
  let A : (EuclideanSpace ℝ (Fin (2 * M + 1))) →L[ℝ] (EuclideanSpace ℝ (Fin (2 * M + 1))) :=
    (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t_rkhs_cap M)).toContinuousLinearMap
  let T : H →L[ℝ] H := ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)
  have hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t_rkhs_cap M)).toContinuousLinearMap =
        Q3.Proofs.C1Embedding.compression ι T := by
    simpa [ι, A, T] using
      (T_P_comp_real_eq_compression_lift_of_dictEmbedding (K := K) (B := B) (t := t_rkhs_cap)
        (M := M) (d := d) (hdim := hdim))
  have hAop :
      ‖A‖ ≤ rho_one := by
    have hnorm :
        ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤
          ∑ n : Q3.Nodes K,
            ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ :=
      T_P_comp_real_opNorm_le_weight_sum (K:=K) (B:=B) (t:=t_rkhs_cap) (M:=M)
    have hnorm' : ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤ rho_one :=
      le_trans hnorm h_weight_sum
    simpa [A, Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using hnorm'
  have hT : ‖T‖ ≤ rho_one := by
    have hTle : ‖T‖ ≤ ‖A‖ :=
      Q3.Proofs.C1Embedding.opNorm_lift_le (ι := ι) (A := A)
    exact le_trans hTle hAop
  exact rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding (K := K) (B := B) (M := M)
    (d := d) (hdim := hdim) (T := T) (hA := hA) (hT := hT)

/-! ### Kernel-section dictionary (finite-dimensional model) -/

private noncomputable def kernel_basis (M : ℕ) :
    OrthonormalBasis (Fin (2 * M + 1)) ℝ (EuclideanSpace ℝ (Fin (2 * M + 1))) := by
  classical
  let E := EuclideanSpace ℝ (Fin (2 * M + 1))
  have hfinrank : Module.finrank ℝ E = 2 * M + 1 :=
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 * M + 1))
  exact (stdOrthonormalBasis ℝ E).reindex (finCongr hfinrank)

private noncomputable def kernel_dict (M : ℕ) :
    Fin (2 * M + 1) → EuclideanSpace ℝ (Fin (2 * M + 1)) :=
  kernel_basis M

private lemma kernel_dict_finrank (M : ℕ) :
    Module.finrank ℝ
        (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) (kernel_dict M)) = 2 * M + 1 := by
  classical
  let E := EuclideanSpace ℝ (Fin (2 * M + 1))
  have hspan :
      Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) (kernel_dict M) = ⊤ := by
    simpa [Q3.Proofs.C1Embedding.dictSubmodule, kernel_dict, kernel_basis] using
      (kernel_basis M).toBasis.span_eq
  have htop :
      Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) (kernel_dict M)) =
        Module.finrank ℝ E := by
    rw [hspan]
    exact (finrank_top (R := ℝ) (M := E))
  exact htop.trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 * M + 1))

lemma rkhs_cap_rayleigh_tcap_via_C1_kernel_dict
    (K B : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (h_weight_sum :
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ ≤ rho_one) :
    ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  classical
  let d := kernel_dict M
  have hdim :
      Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1 := by
    simpa [d] using kernel_dict_finrank (M := M)
  simpa [d] using
    (rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding_lift (K := K) (B := B) (M := M)
      (H := EuclideanSpace ℝ (Fin (2 * M + 1))) (d := d) (hdim := hdim)
      (h_weight_sum := h_weight_sum))

lemma rkhs_cap_rayleigh_tcap (K B : ℝ) [Fintype (Q3.Nodes K)]
    (h_weight_sum :
      ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        ≤ rho_one) :
    ∀ (M : ℕ) (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  intro M v hv
  exact rkhs_cap_rayleigh_tcap_via_C1_kernel_dict (K := K) (B := B) (M := M)
    (h_weight_sum := h_weight_sum) v hv

/-- DEPRECATED: This lemma uses sampling Toeplitz with a_star.
    Use A3_bridge_rayleigh_from_weight_sum_P_A from P_A_Toeplitz_bridge.lean instead,
    which uses Fourier Toeplitz with P_A (the mathematically correct formulation).
    See docs/PROSHKA_ANALYSIS_a_star_crisis.md for details. -/
lemma A3_bridge_rayleigh_from_weight_sum (K : ℝ)
    (h_rayleigh_lower_bound :
      ∀ {M : ℕ} {v : Fin (2 * M + 1) → ℝ}, v ≠ 0 →
        Q3.RayleighQuotient (ToeplitzMatrix (2 * M + 1) Q3.a_star) v ≥ Q3.c_star)
    (h_weight_sum :
      ∀ [Fintype (Q3.Nodes K)],
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one) :
    Q3.A3_bridge_data_rayleigh K := by
  intro hK _inst
  have h_cap :
      ∀ {M : ℕ} {v : Fin (2 * M + 1) → ℝ} [Fintype (Q3.Nodes K)], v ≠ 0 →
        Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v ≤ rho_one := by
    intro M v
    intro _inst' hv
    have h_weight_sum' :
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one := h_weight_sum
    exact rkhs_cap_rayleigh_tcap (K:=K) (B:=K) (h_weight_sum:=h_weight_sum') M v hv
  exact (A3_bridge_rayleigh_first (K:=K)
    (h_rayleigh_lower_bound:=h_rayleigh_lower_bound) (h_cap:=h_cap)) hK

end Q3.Proofs
