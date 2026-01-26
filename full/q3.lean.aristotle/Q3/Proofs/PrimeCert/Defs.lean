import Mathlib

/-!
Prime-term certificate constants (t_critical, tau = 0).
Isolated here to avoid circular imports.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_cert_N : ℕ := 1000000
def prime_cert_prime_ub : ℝ := (8714 / 1000) -- 8.714 (upper bound from sum+tail)
def prime_cert_arch_lb : ℝ := (957 / 100)    -- 9.57 (numeric arch_term lower bound)

/-- B-range certificate parameters at t_critical (tau = 0).
    See output/prime_cert_brange_tcritical_2026-01-26_0050.txt. -/
def prime_cert_B_max : ℝ := (49 / 10) -- 4.9
def prime_cert_B_h : ℝ := (1 / 10)    -- 0.1
def prime_cert_margin_lb : ℝ := (499 / 1000) -- conservative margin
def prime_cert_L_ub : ℝ := (3 / 10)      -- Lipschitz over B (finite-diff upper bound)

lemma prime_cert_margin_pos : 0 < prime_cert_margin_lb := by
  norm_num [prime_cert_margin_lb]

lemma prime_cert_L_ub_nonneg : 0 ≤ prime_cert_L_ub := by
  norm_num [prime_cert_L_ub]

lemma prime_cert_ub_le_arch_lb : prime_cert_prime_ub ≤ prime_cert_arch_lb := by
  norm_num [prime_cert_prime_ub, prime_cert_arch_lb]

end Q3.Proofs.PrimeCert
