import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.A3_Floor_Bounds
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.Q_Lipschitz
import Q3.Proofs.PrimeCert.Defs

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3
open Q3.Proofs

lemma prime_cert_B_max_pos : 0 < prime_cert_B_max := by
  norm_num [prime_cert_B_max]

lemma B_min_pos : 0 < B_min := by
  norm_num [B_min]

lemma abs_max0_sub_max0_le (u v : ℝ) : |max 0 u - max 0 v| ≤ |u - v| := by
  by_cases hu : u ≤ 0
  · have hmaxu : max 0 u = 0 := max_eq_left hu
    by_cases hv : v ≤ 0
    · have hmaxv : max 0 v = 0 := max_eq_left hv
      simp [hmaxu, hmaxv]
    · have hv' : 0 < v := lt_of_not_ge hv
      have hmaxv : max 0 v = v := max_eq_right (le_of_lt hv')
      have hneg : u - v ≤ 0 := by linarith [hu, hv']
      have hpos : v - u ≥ 0 := by linarith [hu, hv']
      calc
        |max 0 u - max 0 v| = |0 - v| := by simp [hmaxu, hmaxv]
        _ = v := by simp [abs_of_pos hv']
        _ ≤ v - u := by linarith [hu]
        _ = |u - v| := by
          have : |u - v| = -(u - v) := by simpa [abs_of_nonpos hneg]
          simp [this]
  · have hu' : 0 < u := lt_of_not_ge hu
    have hmaxu : max 0 u = u := max_eq_right (le_of_lt hu')
    by_cases hv : v ≤ 0
    · have hmaxv : max 0 v = 0 := max_eq_left hv
      have hneg : v - u ≤ 0 := by linarith [hv, hu']
      have hpos : u - v ≥ 0 := by linarith [hv, hu']
      calc
        |max 0 u - max 0 v| = |u - 0| := by simp [hmaxu, hmaxv]
        _ = u := by simp [abs_of_pos hu']
        _ ≤ u - v := by linarith [hv]
        _ = |u - v| := by
          have : |u - v| = u - v := by simpa [abs_of_nonneg hpos]
          simp [this]
    · have hv' : 0 < v := lt_of_not_ge hv
      have hmaxv : max 0 v = v := max_eq_right (le_of_lt hv')
      simp [hmaxu, hmaxv]

lemma abs_inv_sub_inv_le (B1 B2 : ℝ) (hB1 : B_min ≤ B1) (hB2 : B_min ≤ B2) :
    |1 / B1 - 1 / B2| ≤ |B1 - B2| / (B_min ^ 2) := by
  have hBmin : 0 < B_min := B_min_pos
  have hB1pos : 0 < B1 := lt_of_lt_of_le hBmin hB1
  have hB2pos : 0 < B2 := lt_of_lt_of_le hBmin hB2
  have hprod_pos : 0 < B1 * B2 := mul_pos hB1pos hB2pos
  have hprod_ne : B1 * B2 ≠ 0 := ne_of_gt hprod_pos
  have hmin_pos : 0 < (B_min ^ 2) := by nlinarith [hBmin]
  have hmin_ne : (B_min ^ 2) ≠ 0 := ne_of_gt hmin_pos
  have hmin_le_prod : B_min ^ 2 ≤ B1 * B2 := by
    have hBmin_nonneg : 0 ≤ B_min := le_of_lt hBmin
    have hB1_nonneg : 0 ≤ B1 := le_of_lt hB1pos
    have hB2_nonneg : 0 ≤ B2 := le_of_lt hB2pos
    have hmul : B_min * B_min ≤ B1 * B2 := by
      exact mul_le_mul hB1 hB2 hBmin_nonneg hB1_nonneg
    simpa [pow_two] using hmul
  calc
    |1 / B1 - 1 / B2| = |(B2 - B1) / (B1 * B2)| := by
      field_simp [hB1pos.ne', hB2pos.ne']
    _ = |B1 - B2| / (B1 * B2) := by
      have hdiv : |(B2 - B1) / (B1 * B2)| = |B2 - B1| / |B1 * B2| := by
        exact (abs_div (B2 - B1) (B1 * B2))
      have habs : |B2 - B1| = |B1 - B2| := by
        simpa [abs_sub_comm]
      calc
        |(B2 - B1) / (B1 * B2)| = |B2 - B1| / |B1 * B2| := hdiv
        _ = |B1 - B2| / |B1 * B2| := by simpa [habs]
        _ = |B1 - B2| / (B1 * B2) := by simp [abs_of_pos hprod_pos]
    _ ≤ |B1 - B2| / (B_min ^ 2) := by
      have hnum_nonneg : 0 ≤ |B1 - B2| := abs_nonneg _
      have h_inv : (1 / (B1 * B2)) ≤ 1 / (B_min ^ 2) := by
        have hmin_pos' : 0 < (B_min ^ 2) := by nlinarith [hBmin]
        exact one_div_le_one_div_of_le hmin_pos' hmin_le_prod
      have : |B1 - B2| / (B1 * B2) = |B1 - B2| * (1 / (B1 * B2)) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      have : |B1 - B2| / (B_min ^ 2) = |B1 - B2| * (1 / (B_min ^ 2)) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      nlinarith [hnum_nonneg, h_inv]

lemma fejer_heat_window_lipschitz_B (B1 B2 t xi : ℝ)
    (hB1 : B_min ≤ B1) (hB2 : B_min ≤ B2) (ht : 0 ≤ t) :
    |fejer_heat_window B1 t xi - fejer_heat_window B2 t xi| ≤
      |xi| * |B1 - B2| / (B_min ^ 2) := by
  have hmax :
      |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| ≤
        |(1 - |xi| / B1) - (1 - |xi| / B2)| := by
    simpa using (abs_max0_sub_max0_le (1 - |xi| / B1) (1 - |xi| / B2))
  have hdiff :
      |(1 - |xi| / B1) - (1 - |xi| / B2)| = |xi| * |1 / B1 - 1 / B2| := by
    have h :
        (1 - |xi| / B1) - (1 - |xi| / B2) = |xi| * (1 / B2 - 1 / B1) := by
      ring
    calc
      |(1 - |xi| / B1) - (1 - |xi| / B2)|
          = |(|xi| * (1 / B2 - 1 / B1))| := by simpa [h]
      _ = |xi| * |1 / B2 - 1 / B1| := by simp [abs_mul]
      _ = |xi| * |1 / B1 - 1 / B2| := by simpa [abs_sub_comm]
  have hbound_inv : |1 / B1 - 1 / B2| ≤ |B1 - B2| / (B_min ^ 2) :=
    abs_inv_sub_inv_le B1 B2 hB1 hB2
  have hmax_le :
      |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| ≤
        |xi| * |B1 - B2| / (B_min ^ 2) := by
    calc
      |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)|
          ≤ |(1 - |xi| / B1) - (1 - |xi| / B2)| := hmax
      _ = |xi| * |1 / B1 - 1 / B2| := hdiff
      _ ≤ |xi| * (|B1 - B2| / (B_min ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hbound_inv (abs_nonneg xi)
      _ = |xi| * |B1 - B2| / (B_min ^ 2) := by ring
  -- apply exp factor (≤ 1)
  have hexp_le : Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) ≤ 1 := by
    have hpi : 0 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    have hxi : 0 ≤ xi ^ 2 := by nlinarith
    have hprod : 0 ≤ Real.pi ^ 2 * t * xi ^ 2 := by
      exact mul_nonneg (mul_nonneg hpi ht) hxi
    have hnonpos : -4 * Real.pi ^ 2 * t * xi ^ 2 ≤ 0 := by
      nlinarith [hprod]
    simpa using (Real.exp_le_one_iff.mpr hnonpos)
  have hexp_nonneg : 0 ≤ Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) := by
    exact Real.exp_nonneg _
  set E : ℝ := Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2)
  have hE : E = Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) := rfl
  have hfej1 : fejer_heat_window B1 t xi = max 0 (1 - |xi| / B1) * E := by
    simp [fejer_heat_window, E, mul_comm, mul_left_comm, mul_assoc]
  have hfej2 : fejer_heat_window B2 t xi = max 0 (1 - |xi| / B2) * E := by
    simp [fejer_heat_window, E, mul_comm, mul_left_comm, mul_assoc]
  calc
    |fejer_heat_window B1 t xi - fejer_heat_window B2 t xi|
        = |(max 0 (1 - |xi| / B1) * E) - (max 0 (1 - |xi| / B2) * E)| := by
          simp [hfej1, hfej2]
    _ = |(max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)) * E| := by
          ring
    _ = E * |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| := by
          simp [abs_mul, abs_of_nonneg hexp_nonneg, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| := by
          have hle : Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) ≤ 1 := hexp_le
          have hnonneg : 0 ≤ |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| := by
            exact abs_nonneg _
          nlinarith
    _ ≤ |xi| * |B1 - B2| / (B_min ^ 2) := hmax_le

lemma phi_shift_lipschitz_B (B1 B2 xi : ℝ)
    (hB1 : B_min ≤ B1) (hB2 : B_min ≤ B2) :
    |phi_shift B1 t_critical 0 xi - phi_shift B2 t_critical 0 xi| ≤
      |xi| * |B1 - B2| / (B_min ^ 2) := by
  simpa [phi_shift] using
    (fejer_heat_window_lipschitz_B (B1:=B1) (B2:=B2) (t:=t_critical) (xi:=xi) hB1 hB2
      (le_of_lt Q3.t_critical_pos))

lemma phi_shift_support_subset_Icc (B : ℝ) (hB : 0 < B) :
    Function.support (fun xi => phi_shift B t_critical 0 xi) ⊆ Set.Icc (-B) B := by
  intro xi hxi
  have hne : phi_shift B t_critical 0 xi ≠ 0 := by
    simpa using hxi
  have hnot : ¬ B < |xi| := by
    intro hlt
    have hzero := Q3.Proofs.ShiftedWindows.phi_shift_support B t_critical 0 xi hB (by simpa using hlt)
    exact hne hzero
  have habs : |xi| ≤ B := le_of_not_gt hnot
  exact (abs_le.mp habs)

def phi_shift_B_Lipschitz_const : ℝ := prime_cert_B_max / (B_min ^ 2)

lemma phi_shift_sup_norm_le (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max) :
    sSup { |phi_shift B1 t_critical 0 x - phi_shift B2 t_critical 0 x| |
      x ∈ Set.Icc (-prime_cert_B_max) prime_cert_B_max } ≤
      phi_shift_B_Lipschitz_const * |B1 - B2| := by
  have hB1' : B_min ≤ B1 := hB1.1
  have hB2' : B_min ≤ B2 := hB2.1
  have hbound :
      ∀ x ∈ Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |phi_shift B1 t_critical 0 x - phi_shift B2 t_critical 0 x| ≤
          phi_shift_B_Lipschitz_const * |B1 - B2| := by
    intro x hx
    have hx' : |x| ≤ prime_cert_B_max := by
      exact abs_le.mpr hx
    have hphi := phi_shift_lipschitz_B (B1:=B1) (B2:=B2) (xi:=x) hB1' hB2'
    calc
      |phi_shift B1 t_critical 0 x - phi_shift B2 t_critical 0 x|
          ≤ |x| * |B1 - B2| / (B_min ^ 2) := hphi
      _ = |x| * (|B1 - B2| / (B_min ^ 2)) := by
        ring
      _ ≤ prime_cert_B_max * (|B1 - B2| / (B_min ^ 2)) := by
        have hcoef_nonneg : 0 ≤ |B1 - B2| / (B_min ^ 2) := by
          exact div_nonneg (abs_nonneg _) (by nlinarith [B_min_pos])
        exact mul_le_mul_of_nonneg_right hx' hcoef_nonneg
      _ = prime_cert_B_max * |B1 - B2| / (B_min ^ 2) := by
        ring
      _ = phi_shift_B_Lipschitz_const * |B1 - B2| := by
        simp [phi_shift_B_Lipschitz_const, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  have h_nonempty :
      { |phi_shift B1 t_critical 0 x - phi_shift B2 t_critical 0 x| |
        x ∈ Set.Icc (-prime_cert_B_max) prime_cert_B_max }.Nonempty := by
    refine ⟨|phi_shift B1 t_critical 0 0 - phi_shift B2 t_critical 0 0|, ?_⟩
    refine ⟨0, ?_, rfl⟩
    constructor <;> linarith [prime_cert_B_max_pos]
  have h_bdd :
      BddAbove { |phi_shift B1 t_critical 0 x - phi_shift B2 t_critical 0 x| |
        x ∈ Set.Icc (-prime_cert_B_max) prime_cert_B_max } := by
    classical
    refine (Q3.Proofs.QLipschitzArchBridge.D_bddAbove _ ?_ _ _ ?_ ?_)
    · exact prime_cert_B_max_pos
    ·
      simpa using
        (Q3.Proofs.ShiftedWindows.continuous_phi_shift B1 t_critical 0).continuousOn
    ·
      simpa using
        (Q3.Proofs.ShiftedWindows.continuous_phi_shift B2 t_critical 0).continuousOn
  have h_le :
      ∀ y ∈ { |phi_shift B1 t_critical 0 x - phi_shift B2 t_critical 0 x| |
        x ∈ Set.Icc (-prime_cert_B_max) prime_cert_B_max },
        y ≤ phi_shift_B_Lipschitz_const * |B1 - B2| := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hbound x hx
  exact csSup_le h_nonempty h_le

def margin (B : ℝ) : ℝ :=
  arch_term (fun ξ => phi_shift B t_critical 0 ξ) -
    prime_term (fun ξ => phi_shift B t_critical 0 ξ)

def margin_Lipschitz_const : ℝ :=
  (2 * prime_cert_B_max * M_a_local prime_cert_B_max +
    W_sum_local prime_cert_B_max) * phi_shift_B_Lipschitz_const

lemma margin_Lipschitz_symbolic (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max) :
    |margin B1 - margin B2| ≤ margin_Lipschitz_const * |B1 - B2| := by
  have hB1pos : 0 < B1 := lt_of_lt_of_le B_min_pos hB1.1
  have hB2pos : 0 < B2 := lt_of_lt_of_le B_min_pos hB2.1
  have hcont1 :
      ContinuousOn (fun ξ => phi_shift B1 t_critical 0 ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max) := by
    simpa using
      (Q3.Proofs.ShiftedWindows.continuous_phi_shift B1 t_critical 0).continuousOn
  have hcont2 :
      ContinuousOn (fun ξ => phi_shift B2 t_critical 0 ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max) := by
    simpa using
      (Q3.Proofs.ShiftedWindows.continuous_phi_shift B2 t_critical 0).continuousOn
  have hsupp1 :
      Function.support (fun ξ => phi_shift B1 t_critical 0 ξ) ⊆
        Set.Icc (-prime_cert_B_max) prime_cert_B_max := by
    have h := phi_shift_support_subset_Icc (B:=B1) hB1pos
    refine Set.Subset.trans h ?_
    intro x hx
    have hx' : |x| ≤ B1 := abs_le.mpr hx
    have hB1le : B1 ≤ prime_cert_B_max := hB1.2
    have : |x| ≤ prime_cert_B_max := le_trans hx' hB1le
    exact abs_le.mp this
  have hsupp2 :
      Function.support (fun ξ => phi_shift B2 t_critical 0 ξ) ⊆
        Set.Icc (-prime_cert_B_max) prime_cert_B_max := by
    have h := phi_shift_support_subset_Icc (B:=B2) hB2pos
    refine Set.Subset.trans h ?_
    intro x hx
    have hx' : |x| ≤ B2 := abs_le.mpr hx
    have hB2le : B2 ≤ prime_cert_B_max := hB2.2
    have : |x| ≤ prime_cert_B_max := le_trans hx' hB2le
    exact abs_le.mp this
  have hsup :=
    phi_shift_sup_norm_le (B1:=B1) (B2:=B2) hB1 hB2
  have h_arch :=
    Q3.Proofs.arch_term_Lipschitz_bridge (K:=prime_cert_B_max) (hK:=prime_cert_B_max_pos)
      (Φ₁:=fun ξ => phi_shift B1 t_critical 0 ξ)
      (Φ₂:=fun ξ => phi_shift B2 t_critical 0 ξ)
      hcont1 hcont2 hsupp1 hsupp2
  have h_prime :=
    Q3.Proofs.prime_term_Lipschitz_bridge (K:=prime_cert_B_max) (hK:=prime_cert_B_max_pos)
      (Φ₁:=fun ξ => phi_shift B1 t_critical 0 ξ)
      (Φ₂:=fun ξ => phi_shift B2 t_critical 0 ξ)
      hcont1 hcont2 hsupp1 hsupp2
  have h_triangle :
      |margin B1 - margin B2| ≤
        |arch_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
           arch_term (fun ξ => phi_shift B2 t_critical 0 ξ)| +
        |prime_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
           prime_term (fun ξ => phi_shift B2 t_critical 0 ξ)| := by
    unfold margin
    have h :
        |(arch_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
            prime_term (fun ξ => phi_shift B1 t_critical 0 ξ)) -
          (arch_term (fun ξ => phi_shift B2 t_critical 0 ξ) -
            prime_term (fun ξ => phi_shift B2 t_critical 0 ξ))|
          ≤
          |arch_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
             arch_term (fun ξ => phi_shift B2 t_critical 0 ξ)| +
          |prime_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
             prime_term (fun ξ => phi_shift B2 t_critical 0 ξ)| := by
      have h1 :
          |(arch_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
              arch_term (fun ξ => phi_shift B2 t_critical 0 ξ)) +
            (-(prime_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
                prime_term (fun ξ => phi_shift B2 t_critical 0 ξ)))|
            ≤
            |arch_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
               arch_term (fun ξ => phi_shift B2 t_critical 0 ξ)| +
            |prime_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
               prime_term (fun ξ => phi_shift B2 t_critical 0 ξ)| := by
        simpa [Real.norm_eq_abs, abs_neg, abs_sub_comm, add_comm, add_left_comm, add_assoc] using
          (norm_add_le
            (arch_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
              arch_term (fun ξ => phi_shift B2 t_critical 0 ξ))
            (-(prime_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
                prime_term (fun ξ => phi_shift B2 t_critical 0 ξ))))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
    simpa [margin, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have h_arch' :
      |arch_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
         arch_term (fun ξ => phi_shift B2 t_critical 0 ξ)| ≤
        2 * prime_cert_B_max * M_a_local prime_cert_B_max *
          (phi_shift_B_Lipschitz_const * |B1 - B2|) := by
    exact le_trans h_arch (by
      simpa using (mul_le_mul_of_nonneg_left hsup (by nlinarith [prime_cert_B_max_pos, M_a_local_pos prime_cert_B_max prime_cert_B_max_pos])))
  have h_prime' :
      |prime_term (fun ξ => phi_shift B1 t_critical 0 ξ) -
         prime_term (fun ξ => phi_shift B2 t_critical 0 ξ)| ≤
        W_sum_local prime_cert_B_max *
          (phi_shift_B_Lipschitz_const * |B1 - B2|) := by
    exact le_trans h_prime (by
      simpa using (mul_le_mul_of_nonneg_left hsup (by
        have : 0 ≤ W_sum_local prime_cert_B_max := by
          unfold W_sum_local
          apply tsum_nonneg
          intro n
          by_cases h : n ∈ ActiveNodes_local prime_cert_B_max
          · simp [h, Q3.Proofs.QLipschitzPrimeBridge.w_Q_nonneg n]
          · simp [h]
        exact this)))
  have hsum :
      |margin B1 - margin B2| ≤
        (2 * prime_cert_B_max * M_a_local prime_cert_B_max +
          W_sum_local prime_cert_B_max) *
          (phi_shift_B_Lipschitz_const * |B1 - B2|) := by
    have := add_le_add h_arch' h_prime'
    have htriangle := le_trans h_triangle this
    have hrewrite :
        2 * prime_cert_B_max * M_a_local prime_cert_B_max * (phi_shift_B_Lipschitz_const * |B1 - B2|) +
          W_sum_local prime_cert_B_max * (phi_shift_B_Lipschitz_const * |B1 - B2|) =
        (2 * prime_cert_B_max * M_a_local prime_cert_B_max + W_sum_local prime_cert_B_max) *
          (phi_shift_B_Lipschitz_const * |B1 - B2|) := by
      ring
    simpa [hrewrite] using htriangle
  have hfinal :
      |margin B1 - margin B2| ≤ margin_Lipschitz_const * |B1 - B2| := by
    simpa [margin_Lipschitz_const, mul_comm, mul_left_comm, mul_assoc] using hsum
  exact hfinal

end Q3.Proofs.PrimeCert
