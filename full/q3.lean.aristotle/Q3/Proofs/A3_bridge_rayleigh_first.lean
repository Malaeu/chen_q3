/-
Rayleigh-first A3 bridge proof (compression form).
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_utils

open scoped BigOperators

noncomputable section

namespace Q3.Proofs

/-- RKHS cap constant for the Rayleigh-first bridge. -/
def rho_one : ℝ := 1 / 25

def t_rkhs_cap : ℝ := 40

lemma one_le_t_rkhs_cap : (1 : ℝ) ≤ t_rkhs_cap := by
  norm_num [t_rkhs_cap]

lemma c_star_div_four_le_sub_rho_one : Q3.c_star / 4 ≤ Q3.c_star - rho_one := by
  norm_num [Q3.c_star, rho_one]

/-- Rayleigh-first A3 bridge (compression).
    Assumes Toeplitz Rayleigh lower bound and an RKHS cap at t_rkhs_cap. -/
lemma A3_bridge_rayleigh_first (K : ℝ)
    (h_rayleigh_lower_bound :
      ∀ {M : ℕ} {v : Fin (2 * M + 1) → ℝ}, v ≠ 0 →
        Q3.RayleighQuotient (ToeplitzMatrix (2 * M + 1) Q3.a_star) v ≥ Q3.c_star)
    (h_cap :
      ∀ {M : ℕ} {v : Fin (2 * M + 1) → ℝ} [Fintype (Q3.Nodes K)], v ≠ 0 →
        Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v ≤ rho_one) :
    Q3.A3_bridge_data_rayleigh K := by
  intro hK _inst
  refine ⟨t_rkhs_cap, by linarith [one_le_t_rkhs_cap], ?_⟩
  intro M v hv
  have hT :
      Q3.RayleighQuotient (ToeplitzMatrix (2 * M + 1) Q3.a_star) v ≥ Q3.c_star :=
    h_rayleigh_lower_bound (M:=M) (v:=v) hv
  have hP :
      Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v ≤ rho_one :=
    h_cap (M:=M) (v:=v) hv
  have hsub :
      Q3.RayleighQuotient
          (ToeplitzMatrix (2 * M + 1) Q3.a_star - Q3.T_P_comp_real K K t_rkhs_cap M) v
        ≥ Q3.c_star - rho_one := by
    exact Q3.Proofs.RayleighQuotient_sub_ge
      (A:=ToeplitzMatrix (2 * M + 1) Q3.a_star)
      (B:=Q3.T_P_comp_real K K t_rkhs_cap M) (v:=v)
      (a:=Q3.c_star) (b:=rho_one) hT hP
  exact le_trans c_star_div_four_le_sub_rho_one hsub

end Q3.Proofs
