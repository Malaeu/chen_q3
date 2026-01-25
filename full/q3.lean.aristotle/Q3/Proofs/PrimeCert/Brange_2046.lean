import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeGrid_2046
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

/-!
Prime-term B-range certificate at t_critical, tau = 0.
Source: output/prime_cert_brange_tcritical_2026-01-25_2046.txt
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

/-- B-grid on [B_min, B_max] with step prime_cert_B_h. -/
def prime_b_grid (i : Fin prime_b_grid_vals_q.size) : ℝ :=
  B_min + (i.1 : ℝ) * prime_cert_B_h

/-- Link table grid values to the true margin at grid points. -/
axiom prime_b_grid_val_le_margin :
    ∀ i : Fin prime_b_grid_vals_q.size,
      prime_b_grid_val i ≤
        arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ)

/-- Lipschitz certificate in B on the B-range. -/
axiom prime_margin_Lipschitz_on_Brange :
    ∀ x y,
      x ∈ Set.Icc B_min prime_cert_B_max →
      y ∈ Set.Icc B_min prime_cert_B_max →
      |(arch_term (fun ξ => phi_shift x t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift x t_critical 0 ξ)) -
       (arch_term (fun ξ => phi_shift y t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift y t_critical 0 ξ))| ≤
        prime_cert_L_ub * |x - y|

/-- Grid cover certificate on [B_min, B_max]. -/
lemma prime_b_grid_cover_cert :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      ∃ i : Fin prime_b_grid_vals_q.size,
        |B - prime_b_grid i| ≤ prime_cert_B_h / 2
  := by
  intro B hB
  rcases hB with ⟨hBmin, hBmax⟩
  -- rescale to [0, N]
  set t : ℝ := (B - B_min) / prime_cert_B_h
  have hB_h_pos : (0 : ℝ) < prime_cert_B_h := by
    norm_num [prime_cert_B_h]
  have ht0 : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hBmin) (le_of_lt hB_h_pos)
  have htN : t ≤ (19 : ℝ) := by
    have hmul : B - B_min ≤ prime_cert_B_max - B_min := by
      exact sub_le_sub_right hBmax _
    have hdiv : (B - B_min) / prime_cert_B_h ≤
        (prime_cert_B_max - B_min) / prime_cert_B_h := by
      exact (div_le_div_of_nonneg_right hmul (le_of_lt hB_h_pos))
    -- compute RHS: (4.9-3)/0.1 = 19
    simpa [prime_cert_B_max, prime_cert_B_h, B_min] using hdiv
  -- choose nearest grid index via floor(t+1/2)
  set n : ℕ := Nat.floor (t + 1/2)
  have hn_le : (n : ℝ) ≤ t + 1/2 := Nat.floor_le (by nlinarith [ht0])
  have ht_lt : t + 1/2 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t + 1/2)
  have hsize : prime_b_grid_vals_q.size = 20 := by
    native_decide
  have hn_lt : n < prime_b_grid_vals_q.size := by
    have hnonneg : 0 ≤ t + 1/2 := by nlinarith [ht0]
    have h1 : t + 1/2 ≤ (19 : ℝ) + 1/2 := by
      linarith [htN]
    have h2 : (19 : ℝ) + 1/2 < (19 : ℝ) + 1 := by
      nlinarith
    have htop' : t + 1/2 < (19 : ℝ) + 1 := lt_of_le_of_lt h1 h2
    have htop : t + 1/2 < ((20 : ℕ) : ℝ) := by
      simpa using htop'
    have hnlt : n < 20 := (Nat.floor_lt hnonneg).2 htop
    simpa [hsize] using hnlt
  refine ⟨⟨n, hn_lt⟩, ?_⟩
  -- distance ≤ h/2
  have h_repr : t * prime_cert_B_h = B - B_min := by
    unfold t
    field_simp [prime_cert_B_h]
  have hdiff :
      B - prime_b_grid ⟨n, hn_lt⟩ = prime_cert_B_h * (t - n) := by
    simp [prime_b_grid]
    nlinarith [h_repr]
  have habs_t : |t - n| ≤ (1/2 : ℝ) := by
    have h1 : (n : ℝ) - 1/2 ≤ t := by nlinarith [hn_le]
    have h2 : t ≤ (n : ℝ) + 1/2 := by nlinarith [ht_lt]
    exact (abs_le.mpr ⟨by nlinarith [h1], by nlinarith [h2]⟩)
  have hmul : |B - prime_b_grid ⟨n, hn_lt⟩| = prime_cert_B_h * |t - n| := by
    simp [hdiff, abs_mul, abs_of_pos hB_h_pos]
  have hmul' : prime_cert_B_h * |t - n| ≤ prime_cert_B_h * (1/2 : ℝ) := by
    exact mul_le_mul_of_nonneg_left habs_t (le_of_lt hB_h_pos)
  have hfinal : |B - prime_b_grid ⟨n, hn_lt⟩| ≤ prime_cert_B_h / 2 := by
    simpa [hmul, mul_div_assoc] using hmul'
  simpa using hfinal

/-- Margin certificate on B-range at t_critical (tau = 0). -/
axiom prime_cert_margin_on_Brange_axiom :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      prime_cert_margin_lb ≤
        arch_term (fun ξ => phi_shift B t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift B t_critical 0 ξ)

end Q3.Proofs.PrimeCert
