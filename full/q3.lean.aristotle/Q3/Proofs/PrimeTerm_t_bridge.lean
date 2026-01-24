import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.A3_bridge_rayleigh_first
import Q3.Proofs.Rayleigh_Q_identification

set_option linter.mathlibStandardSet false

/-! Prime-term t-bridge for shifted Fejer-heat windows. -/

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.PrimeTermBridge

open Q3

noncomputable def exp_tsym_to_rkhs (K : ℝ) : ℝ :=
  Real.exp (16 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * K ^ 2)

noncomputable def exp_tcrit_to_rkhs (K : ℝ) : ℝ :=
  Real.exp (16 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * K ^ 2)

lemma phi_shift_le_phi_shift_t_rkhs_cap (K B tau xi : ℝ)
    (hxi : |xi| ≤ K) (hB : 0 < B) (hK : |tau| + B ≤ K) :
    Q3.phi_shift B t_sym tau xi ≤
      exp_tsym_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau xi := by
  have htau : |tau| ≤ K := by
    have hpos : 0 ≤ B := by linarith [hB]
    have hle : |tau| ≤ |tau| + B := by nlinarith [hpos]
    exact le_trans hle hK
  have hsum : |xi| + |tau| ≤ 2 * K := by nlinarith [hxi, htau]
  have htri : |xi - tau| ≤ |xi| + |tau| := by
    simpa [sub_eq_add_neg, abs_neg] using (abs_add_le xi (-tau))
  have hztwo : |xi - tau| ≤ 2 * K := le_trans htri hsum
  have hz2 : (xi - tau) ^ 2 ≤ (2 * K) ^ 2 := by
    have hKnonneg : 0 ≤ K := by
      exact le_trans (abs_nonneg xi) hxi
    have hKnonneg' : 0 ≤ 2 * K := by nlinarith [hKnonneg]
    have h' : |xi - tau| ≤ |2 * K| := by
      simpa [abs_of_nonneg hKnonneg'] using hztwo
    exact (sq_le_sq).2 h'
  have hcoef_nonneg : 0 ≤ 4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) := by
    have ht : 0 ≤ t_rkhs_cap - t_sym := by
      norm_num [t_rkhs_cap, t_sym]
    have hpi2 : 0 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith [ht, hpi2]
  have hterm :
      4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (xi - tau) ^ 2 ≤
        4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hz2 hcoef_nonneg
  have hdiff :
      -4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2 ≤
        4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2 -
          4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2 := by
    have hdecomp :
        -4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2 =
          4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (xi - tau) ^ 2 -
            4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2 := by
      ring
    nlinarith [hterm, hdecomp]
  have hexp' :
      Real.exp (-4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2) ≤
        Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2 -
          4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
    exact (Real.exp_le_exp).2 hdiff
  have hexp'' :
      Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2 -
          4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) =
        Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
    simp [sub_eq_add_neg, Real.exp_add, mul_comm, mul_left_comm]
  have hfej_nonneg : 0 ≤ max (0 : ℝ) (1 - |xi - tau| / B) := by
    exact le_max_left _ _
  unfold Q3.phi_shift Q3.fejer_heat_window
  have hmul' :
      max (0 : ℝ) (1 - |xi - tau| / B) *
          Real.exp (-4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2) ≤
        max (0 : ℝ) (1 - |xi - tau| / B) *
          (Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2)) := by
    have hexp_final :
        Real.exp (-4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2) ≤
          Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
      calc
        Real.exp (-4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2)
            ≤ Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2 -
                4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := hexp'
        _ = Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2) *
              Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
              simp [hexp'']
    exact mul_le_mul_of_nonneg_left hexp_final hfej_nonneg
  have hconst :
      Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_sym) * (2 * K) ^ 2) =
        exp_tsym_to_rkhs K := by
    unfold exp_tsym_to_rkhs
    ring_nf
  have hmul_final :
      max (0 : ℝ) (1 - |xi - tau| / B) *
          Real.exp (-4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2) ≤
        max (0 : ℝ) (1 - |xi - tau| / B) *
          (exp_tsym_to_rkhs K *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2)) := by
    simpa [hconst] using hmul'
  have hmul_final' :
      max (0 : ℝ) (1 - |xi - tau| / B) *
          Real.exp (-4 * Real.pi ^ 2 * t_sym * (xi - tau) ^ 2) ≤
        exp_tsym_to_rkhs K *
          (max (0 : ℝ) (1 - |xi - tau| / B) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_final
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_final'

lemma phi_shift_le_phi_shift_t_rkhs_cap_tcrit (K B tau xi : ℝ)
    (hxi : |xi| ≤ K) (hB : 0 < B) (hK : |tau| + B ≤ K) :
    Q3.phi_shift B t_critical tau xi ≤
      exp_tcrit_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau xi := by
  have htau : |tau| ≤ K := by
    have hpos : 0 ≤ B := by linarith [hB]
    have hle : |tau| ≤ |tau| + B := by nlinarith [hpos]
    exact le_trans hle hK
  have hsum : |xi| + |tau| ≤ 2 * K := by nlinarith [hxi, htau]
  have htri : |xi - tau| ≤ |xi| + |tau| := by
    simpa [sub_eq_add_neg, abs_neg] using (abs_add_le xi (-tau))
  have hztwo : |xi - tau| ≤ 2 * K := le_trans htri hsum
  have hz2 : (xi - tau) ^ 2 ≤ (2 * K) ^ 2 := by
    have hKnonneg : 0 ≤ K := by
      exact le_trans (abs_nonneg xi) hxi
    have hKnonneg' : 0 ≤ 2 * K := by nlinarith [hKnonneg]
    have h' : |xi - tau| ≤ |2 * K| := by
      simpa [abs_of_nonneg hKnonneg'] using hztwo
    exact (sq_le_sq).2 h'
  have hcoef_nonneg : 0 ≤ 4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) := by
    have ht : 0 ≤ t_rkhs_cap - t_critical := by
      norm_num [t_rkhs_cap, t_critical]
    have hpi2 : 0 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith [ht, hpi2]
  have hterm :
      4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (xi - tau) ^ 2 ≤
        4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hz2 hcoef_nonneg
  have hdiff :
      -4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2 ≤
        4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2 -
          4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2 := by
    have hdecomp :
        -4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2 =
          4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (xi - tau) ^ 2 -
            4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2 := by
      ring
    nlinarith [hterm, hdecomp]
  have hexp' :
      Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2) ≤
        Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2 -
          4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
    exact (Real.exp_le_exp).2 hdiff
  have hexp'' :
      Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2 -
          4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) =
        Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
    simp [sub_eq_add_neg, Real.exp_add, mul_comm, mul_left_comm]
  have hfej_nonneg : 0 ≤ max (0 : ℝ) (1 - |xi - tau| / B) := by
    exact le_max_left _ _
  unfold Q3.phi_shift Q3.fejer_heat_window
  have hmul' :
      max (0 : ℝ) (1 - |xi - tau| / B) *
          Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2) ≤
        max (0 : ℝ) (1 - |xi - tau| / B) *
          (Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2)) := by
    have hexp_final :
        Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2) ≤
          Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
      calc
        Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2)
            ≤ Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2 -
                4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := hexp'
        _ = Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2) *
              Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2) := by
              simp [hexp'']
    exact mul_le_mul_of_nonneg_left hexp_final hfej_nonneg
  have hconst :
      Real.exp (4 * Real.pi ^ 2 * (t_rkhs_cap - t_critical) * (2 * K) ^ 2) =
        exp_tcrit_to_rkhs K := by
    unfold exp_tcrit_to_rkhs
    ring_nf
  have hmul_final :
      max (0 : ℝ) (1 - |xi - tau| / B) *
          Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2) ≤
        max (0 : ℝ) (1 - |xi - tau| / B) *
          (exp_tcrit_to_rkhs K *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2)) := by
    simpa [hconst] using hmul'
  have hmul_final' :
      max (0 : ℝ) (1 - |xi - tau| / B) *
          Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi - tau) ^ 2) ≤
        exp_tcrit_to_rkhs K *
          (max (0 : ℝ) (1 - |xi - tau| / B) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (xi - tau) ^ 2)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_final
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_final'

lemma prime_term_phi_shift_tsym_le (K B tau : ℝ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : |tau| + B ≤ K) :
    Q3.prime_term (fun xi => Q3.phi_shift B t_sym tau xi) ≤
      exp_tsym_to_rkhs K *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
  have hprime :
      Q3.prime_term (fun xi => Q3.phi_shift B t_sym tau xi) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_sym tau (Q3.xi_n n) := by
    simpa using
      (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift (B:=B) (t:=t_sym)
        (tau:=tau) (K:=K) hB hK)
  have hsum_le :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_sym tau (Q3.xi_n n) ≤
        ∑ n : Q3.Nodes K,
          Q3.w_Q n * (exp_tsym_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) := by
    classical
    refine Finset.sum_le_sum ?_
    intro n _
    have hxi : |Q3.xi_n n| ≤ K := n.property.1
    have hphi := phi_shift_le_phi_shift_t_rkhs_cap K B tau (Q3.xi_n n) hxi hB hK
    have hw : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
    exact mul_le_mul_of_nonneg_left hphi hw
  have hfactor : ∑ n : Q3.Nodes K,
      Q3.w_Q n * (exp_tsym_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) =
      exp_tsym_to_rkhs K *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    classical
    calc
      ∑ n : Q3.Nodes K,
          Q3.w_Q n * (exp_tsym_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n))
          = ∑ n : Q3.Nodes K,
              exp_tsym_to_rkhs K * (Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) := by
                congr 1
                ext n
                ring
      _ = exp_tsym_to_rkhs K *
            ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
                simp [Finset.mul_sum]
  calc
    Q3.prime_term (fun xi => Q3.phi_shift B t_sym tau xi)
        = ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_sym tau (Q3.xi_n n) := hprime
    _ ≤ ∑ n : Q3.Nodes K,
          Q3.w_Q n * (exp_tsym_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) := hsum_le
    _ = exp_tsym_to_rkhs K *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := hfactor

lemma prime_term_phi_shift_tcritical_le (K B tau : ℝ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : |tau| + B ≤ K) :
    Q3.prime_term (fun xi => Q3.phi_shift B t_critical tau xi) ≤
      exp_tcrit_to_rkhs K *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
  have hprime :
      Q3.prime_term (fun xi => Q3.phi_shift B t_critical tau xi) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_critical tau (Q3.xi_n n) := by
    simpa using
      (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift (B:=B) (t:=t_critical)
        (tau:=tau) (K:=K) hB hK)
  have hsum_le :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_critical tau (Q3.xi_n n) ≤
        ∑ n : Q3.Nodes K,
          Q3.w_Q n * (exp_tcrit_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) := by
    classical
    refine Finset.sum_le_sum ?_
    intro n _
    have hxi : |Q3.xi_n n| ≤ K := n.property.1
    have hphi := phi_shift_le_phi_shift_t_rkhs_cap_tcrit K B tau (Q3.xi_n n) hxi hB hK
    have hw : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
    exact mul_le_mul_of_nonneg_left hphi hw
  have hfactor : ∑ n : Q3.Nodes K,
      Q3.w_Q n * (exp_tcrit_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) =
      exp_tcrit_to_rkhs K *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    classical
    calc
      ∑ n : Q3.Nodes K,
          Q3.w_Q n * (exp_tcrit_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n))
          = ∑ n : Q3.Nodes K,
              exp_tcrit_to_rkhs K * (Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) := by
                congr 1
                ext n
                ring
      _ = exp_tcrit_to_rkhs K *
            ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
                simp [Finset.mul_sum]
  calc
    Q3.prime_term (fun xi => Q3.phi_shift B t_critical tau xi)
        = ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_critical tau (Q3.xi_n n) := hprime
    _ ≤ ∑ n : Q3.Nodes K,
          Q3.w_Q n * (exp_tcrit_to_rkhs K * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) := hsum_le
    _ = exp_tcrit_to_rkhs K *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := hfactor

lemma prime_term_phi_shift_tsym_le_cap (K B tau R : ℝ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : |tau| + B ≤ K)
    (hcap :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ R) :
    Q3.prime_term (fun ξ => Q3.phi_shift B t_sym tau ξ) ≤
      exp_tsym_to_rkhs K * R := by
  have hprime :=
    prime_term_phi_shift_tsym_le (K:=K) (B:=B) (tau:=tau) hB hK
  have hexp_nonneg : 0 ≤ exp_tsym_to_rkhs K := by
    unfold exp_tsym_to_rkhs
    exact (Real.exp_pos _).le
  have hcap' :
      exp_tsym_to_rkhs K *
          ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤
        exp_tsym_to_rkhs K * R := by
    exact mul_le_mul_of_nonneg_left hcap hexp_nonneg
  exact le_trans hprime hcap'

end Q3.Proofs.PrimeTermBridge
