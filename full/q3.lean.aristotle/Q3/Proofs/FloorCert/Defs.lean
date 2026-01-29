import Mathlib
import Q3.Axioms

/-!
Floor certificate constants and grid definition (t_critical).
This file isolates numeric constants to avoid circular imports.
-/

noncomputable section

namespace Q3.Proofs.FloorCert

def floor_cert_N : ℕ := 4000
def floor_cert_min_lb : ℝ := (831 / 500)   -- 1.662
def floor_cert_L_ub : ℝ := (2493 / 10)    -- 249.3
def floor_cert_h : ℝ := (1 / 4000 : ℝ)

def floor_grid (i : Fin (floor_cert_N + 1)) : ℝ :=
  (-1/2 : ℝ) + (i.1 : ℝ) * floor_cert_h

lemma floor_cert_L_ub_nonneg : 0 ≤ floor_cert_L_ub := by
  norm_num [floor_cert_L_ub]

lemma floor_cert_h_pos : 0 < floor_cert_h := by
  norm_num [floor_cert_h]

lemma floor_cert_h_ne_zero : (floor_cert_h : ℝ) ≠ 0 := by
  nlinarith [floor_cert_h_pos]

lemma floor_cert_N_mul_h : (floor_cert_N : ℝ) * floor_cert_h = 1 := by
  norm_num [floor_cert_N, floor_cert_h]

lemma floor_cert_margin_ge_c_star :
    Q3.c_star ≤ floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 := by
  norm_num [Q3.c_star, floor_cert_min_lb, floor_cert_L_ub, floor_cert_h]

end Q3.Proofs.FloorCert
