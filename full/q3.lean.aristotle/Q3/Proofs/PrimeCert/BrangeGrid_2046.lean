import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.A3_Floor_Bounds

/-! Prime B-range margin grid values for t_critical.
Source: output/prime_cert_brange_tcritical_2026-01-26_0050.txt
Generated: 2026-01-29 10:55
Values are rounded to 12 decimal places.
- margin and arch_term: rounded down (lower bounds)
- prime_ub: rounded up (upper bounds)
-/-

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Size of the B-grid certificate table. -/
abbrev prime_b_grid_size : Nat := 20

def prime_b_grid (i : Fin prime_b_grid_size) : ℝ :=
  B_min + (i.1 : ℝ) * prime_cert_B_h

/-- Grid margins for B in [B_min, prime_cert_B_max] with step prime_cert_B_h. -/
def prime_b_grid_vals_q : Array ℚ := #[0.856457311774, 0.828016971090, 0.801354151698, 0.776307260754, 0.752733716336, 0.730507231598, 0.709515551568, 0.689658556946, 0.670846667303, 0.652999489949, 0.636044671464, 0.619916917295, 0.604557151420, 0.589911793260, 0.575932133198, 0.562573791361, 0.549796246996, 0.537562427922, 0.525838351309, 0.514592808436]

/-- Grid prime upper bounds (same B grid). -/
def prime_b_grid_prime_ub_q : Array ℚ := #[8.713579081616, 8.756642707771, 8.797014857293, 8.834940209873, 8.870634659362, 8.904289426022, 8.936074483423, 8.966141429614, 8.994625904952, 9.021649637966, 9.047322184328, 9.071742411356, 9.094999770429, 9.117175391872, 9.138343030522, 9.158569885232, 9.177917311476, 9.196441442986, 9.214193735684, 9.231221445006]

/-- Grid arch term lower bounds (same B grid). -/
def prime_b_grid_arch_term_q : Array ℚ := #[9.570036393390, 9.584659678861, 9.598369008991, 9.611247470627, 9.623368375697, 9.634796657620, 9.645590034992, 9.655799986559, 9.665472572255, 9.674649127915, 9.683366855792, 9.691659328651, 9.699556921850, 9.707087185132, 9.714275163720, 9.721143676593, 9.727713558471, 9.734003870908, 9.740032086993, 9.745814253443]

def prime_b_grid_val_q (i : Fin (prime_b_grid_vals_q.size)) : ℚ :=
  prime_b_grid_vals_q.get! i.1

def prime_b_grid_val (i : Fin (prime_b_grid_vals_q.size)) : ℝ :=
  (prime_b_grid_val_q i : ℝ)

def prime_b_grid_prime_ub_q_get (i : Fin (prime_b_grid_prime_ub_q.size)) : ℚ :=
  prime_b_grid_prime_ub_q.get! i.1

def prime_b_grid_prime_ub (i : Fin (prime_b_grid_prime_ub_q.size)) : ℝ :=
  (prime_b_grid_prime_ub_q_get i : ℝ)

def prime_b_grid_arch_term_q_get (i : Fin (prime_b_grid_arch_term_q.size)) : ℚ :=
  prime_b_grid_arch_term_q.get! i.1

def prime_b_grid_arch_term (i : Fin (prime_b_grid_arch_term_q.size)) : ℝ :=
  (prime_b_grid_arch_term_q_get i : ℝ)

def prime_cert_margin_lb_q : ℚ := (499 / 1000)

lemma prime_cert_margin_lb_eq_q : (prime_cert_margin_lb : ℝ) = prime_cert_margin_lb_q := by
  norm_num [prime_cert_margin_lb, prime_cert_margin_lb_q]

/-- Table min bound: every grid margin is ≥ prime_cert_margin_lb. -/
lemma prime_b_grid_val_ge_lb :
    ∀ i : Fin (prime_b_grid_vals_q.size),
      prime_cert_margin_lb ≤ prime_b_grid_val i := by
  intro i
  have hq : prime_cert_margin_lb_q ≤ prime_b_grid_val_q i := by
    decide
  have hq' : (prime_cert_margin_lb_q : ℝ) ≤ (prime_b_grid_val_q i : ℝ) := by
    exact_mod_cast hq
  simpa [prime_cert_margin_lb_eq_q, prime_b_grid_val] using hq'

/-- Table min bound with Lipschitz slack: every grid margin is ≥ margin_lb + L*h/2. -/
lemma prime_b_grid_val_ge_lb_with_slack :
    ∀ i : Fin (prime_b_grid_vals_q.size),
      prime_cert_margin_lb + prime_cert_L_ub * prime_cert_B_h / 2 ≤ prime_b_grid_val i := by
  intro i
  -- reduce to ℚ and decide
  have hq : (prime_cert_margin_lb_q + (3/10) * (1/10) / (2:ℚ)) ≤ prime_b_grid_val_q i := by
    decide
  have hq' : ((prime_cert_margin_lb_q + (3/10) * (1/10) / (2:ℚ)) : ℝ) ≤ (prime_b_grid_val_q i : ℝ) := by
    exact_mod_cast hq
  -- rewrite constants
  have hL : (prime_cert_L_ub : ℝ) = (3/10 : ℝ) := by
    norm_num [prime_cert_L_ub]
  have hH : (prime_cert_B_h : ℝ) = (1/10 : ℝ) := by
    norm_num [prime_cert_B_h]
  -- assemble
  simpa [prime_cert_margin_lb_eq_q, prime_b_grid_val, hL, hH] using hq'

end Q3.Proofs.PrimeCert
