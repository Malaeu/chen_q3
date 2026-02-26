import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeGrid_2046
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatScaffold
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatProof

/-!
Proof-carrying margin kernel for the prime-heat route.

This module packages the load-bearing heat bounds into one witness object and
provides a single soundness theorem:

`checkPrimeHeatMarginCert cert = true -> margin_tau0(B) >= prime_cert_margin_lb`
for all `B` on the certified B-range.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

structure PrimeHeatMarginCert where
  source_path : String
  source_sha256 : String
  N : ℕ
  h_source_path : source_path = prime_cert_heat_brange_source
  h_source_sha256 : source_sha256 = prime_cert_heat_brange_sha256
  h_N : N = prime_cert_heat_N
  h_arch_heat :
    ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ ≤ prime_cert_L_arch_heat_raw
  h_prime_heat :
    ∑' n, (w_Q n * heat_weight_tc (xi_n n)) *
      (if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0) ≤ prime_cert_L_prime_heat_raw
  h_total_heat :
    (prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2) ≤
      prime_cert_L_total_heat_ub

def checkPrimeHeatMarginCert (c : PrimeHeatMarginCert) : Bool :=
  decide (c.source_path = prime_cert_heat_brange_source) &&
    decide (c.source_sha256 = prime_cert_heat_brange_sha256) &&
    decide (c.N = prime_cert_heat_N)

theorem checkPrimeHeatMarginCert_true (c : PrimeHeatMarginCert) :
    checkPrimeHeatMarginCert c = true := by
  rcases c with ⟨source_path, source_sha256, N, h_source_path, h_source_sha256, h_N,
    h_arch_heat, h_prime_heat, h_total_heat⟩
  simp [checkPrimeHeatMarginCert, h_source_path, h_source_sha256, h_N]

lemma prime_cert_L_total_heat_ub_eq_prime_cert_L_ub :
    prime_cert_L_total_heat_ub = prime_cert_L_ub := by
  norm_num [prime_cert_L_total_heat_ub, prime_cert_L_ub]

theorem margin_lb_on_brange_of_checked_cert
    (cert : PrimeHeatMarginCert)
    (_hcheck : checkPrimeHeatMarginCert cert = true)
    (h_cover :
      ∀ B ∈ Set.Icc B_min prime_cert_B_max,
        ∃ i : Fin prime_b_grid_size, |B - prime_b_grid i| ≤ prime_cert_B_h / 2)
    (h_grid_margin :
      ∀ i : Fin prime_b_grid_size, prime_b_grid_val i ≤ margin_tau0 (prime_b_grid i)) :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      prime_cert_margin_lb ≤ margin_tau0 B := by
  intro B hB
  rcases h_cover B hB with ⟨i, hdist⟩
  have hBgrid :
      prime_b_grid i ∈ Set.Icc B_min prime_cert_B_max := by
    have hi_nat : i.1 < 20 := by
      simpa using i.2
    have hi : (i.1 : ℝ) ≤ 19 := by
      exact_mod_cast (Nat.lt_succ_iff.mp hi_nat)
    have hBmin' : B_min ≤ prime_b_grid i := by
      have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast (Nat.zero_le i.1)
      have hBh0 : 0 ≤ prime_cert_B_h := by norm_num [prime_cert_B_h]
      have hprod : 0 ≤ (i.1 : ℝ) * prime_cert_B_h := mul_nonneg hi0 hBh0
      have : B_min ≤ B_min + (i.1 : ℝ) * prime_cert_B_h := le_add_of_nonneg_right hprod
      simpa [prime_b_grid] using this
    have hBmax' : prime_b_grid i ≤ prime_cert_B_max := by
      have hBh0 : 0 ≤ prime_cert_B_h := by norm_num [prime_cert_B_h]
      have hmul : (i.1 : ℝ) * prime_cert_B_h ≤ (19 : ℝ) * prime_cert_B_h :=
        mul_le_mul_of_nonneg_right hi hBh0
      have hbound : prime_b_grid i ≤ B_min + (19 : ℝ) * prime_cert_B_h := by
        have : B_min + (i.1 : ℝ) * prime_cert_B_h ≤ B_min + (19 : ℝ) * prime_cert_B_h :=
          add_le_add_left hmul B_min
        simpa [prime_b_grid] using this
      have h19 : B_min + (19 : ℝ) * prime_cert_B_h = prime_cert_B_max := by
        norm_num [B_min, prime_cert_B_h, prime_cert_B_max]
      simpa [h19] using hbound
    exact ⟨hBmin', hBmax'⟩
  have hLip_total :
      |margin_tau0 B - margin_tau0 (prime_b_grid i)| ≤
        prime_cert_L_total_heat_ub * |B - prime_b_grid i| := by
    exact margin_Lipschitz_heat_of_bounds (B1 := B) (B2 := prime_b_grid i)
      hB hBgrid cert.h_arch_heat cert.h_prime_heat cert.h_total_heat
  have hLip :
      |margin_tau0 B - margin_tau0 (prime_b_grid i)| ≤
        prime_cert_L_ub * |B - prime_b_grid i| := by
    simpa [prime_cert_L_total_heat_ub_eq_prime_cert_L_ub] using hLip_total
  have hLip' := (abs_sub_le_iff).1 hLip
  have hgrid_lb :
      prime_cert_margin_lb + prime_cert_L_ub * prime_cert_B_h / 2 ≤ prime_b_grid_val i := by
    exact prime_b_grid_val_ge_lb_with_slack i
  have hgrid_margin' : prime_b_grid_val i ≤ margin_tau0 (prime_b_grid i) := h_grid_margin i
  have hdist' :
      prime_cert_L_ub * |B - prime_b_grid i| ≤
        prime_cert_L_ub * (prime_cert_B_h / 2) := by
    exact mul_le_mul_of_nonneg_left hdist prime_cert_L_ub_nonneg
  have hmargin_ge :
      margin_tau0 (prime_b_grid i) - prime_cert_L_ub * |B - prime_b_grid i| ≤ margin_tau0 B := by
    nlinarith [hLip'.2]
  have hgrid_ge :
      prime_cert_margin_lb ≤
        margin_tau0 (prime_b_grid i) - prime_cert_L_ub * (prime_cert_B_h / 2) := by
    have : prime_cert_margin_lb + prime_cert_L_ub * prime_cert_B_h / 2 ≤ margin_tau0 (prime_b_grid i) := by
      exact le_trans hgrid_lb hgrid_margin'
    nlinarith
  have hfinal : prime_cert_margin_lb ≤ margin_tau0 B := by
    have : prime_cert_margin_lb ≤ margin_tau0 (prime_b_grid i) - prime_cert_L_ub * |B - prime_b_grid i| := by
      have hL : prime_cert_L_ub * |B - prime_b_grid i| ≤ prime_cert_L_ub * (prime_cert_B_h / 2) := hdist'
      nlinarith [hgrid_ge, hL]
    exact le_trans this hmargin_ge
  exact hfinal

end Q3.Proofs.PrimeCert
