import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.A3_Floor_Bounds

/-! Prime B-range margin grid values for t_critical.
Source: output/prime_cert_brange_tcritical_2026-01-25_2046.txt
Generated: 2026-01-29 12:01
Values are rounded to 12 decimal places.
- margin and arch_term: rounded down (lower bounds)
- prime_ub: rounded up (upper bounds)
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Size of the B-grid certificate table. -/
abbrev prime_b_grid_size : Nat := 20

def prime_b_grid (i : Fin prime_b_grid_size) : ℝ :=
  B_min + (i.1 : ℝ) * prime_cert_B_h

/-- Grid margins for B in [B_min, prime_cert_B_max] with step prime_cert_B_h. -/
def prime_b_grid_val_q : Fin prime_b_grid_size -> ℚ
| ⟨0, _⟩ => 0.856457311774
| ⟨1, _⟩ => 0.828016971090
| ⟨2, _⟩ => 0.801354151698
| ⟨3, _⟩ => 0.776307260754
| ⟨4, _⟩ => 0.752733716335
| ⟨5, _⟩ => 0.730507231598
| ⟨6, _⟩ => 0.709515551569
| ⟨7, _⟩ => 0.689658556945
| ⟨8, _⟩ => 0.670846667303
| ⟨9, _⟩ => 0.652999489949
| ⟨10, _⟩ => 0.636044671464
| ⟨11, _⟩ => 0.619916917295
| ⟨12, _⟩ => 0.604557151421
| ⟨13, _⟩ => 0.589911793260
| ⟨14, _⟩ => 0.575932133198
| ⟨15, _⟩ => 0.562573791361
| ⟨16, _⟩ => 0.549796246995
| ⟨17, _⟩ => 0.537562427922
| ⟨18, _⟩ => 0.525838351309
| ⟨19, _⟩ => 0.514592808437
| _ => 0.514592808437

/-- Grid prime upper bounds (same B grid). -/
def prime_b_grid_prime_ub_q_get : Fin prime_b_grid_size -> ℚ
| ⟨0, _⟩ => 8.713579081616
| ⟨1, _⟩ => 8.756642707771
| ⟨2, _⟩ => 8.797014857293
| ⟨3, _⟩ => 8.834940209873
| ⟨4, _⟩ => 8.870634659362
| ⟨5, _⟩ => 8.904289426022
| ⟨6, _⟩ => 8.936074483423
| ⟨7, _⟩ => 8.966141429614
| ⟨8, _⟩ => 8.994625904952
| ⟨9, _⟩ => 9.021649637966
| ⟨10, _⟩ => 9.047322184328
| ⟨11, _⟩ => 9.071742411356
| ⟨12, _⟩ => 9.094999770429
| ⟨13, _⟩ => 9.117175391872
| ⟨14, _⟩ => 9.138343030522
| ⟨15, _⟩ => 9.158569885232
| ⟨16, _⟩ => 9.177917311476
| ⟨17, _⟩ => 9.196441442986
| ⟨18, _⟩ => 9.214193735684
| ⟨19, _⟩ => 9.231221445006
| _ => 9.231221445006

/-- Grid arch term lower bounds (same B grid). -/
def prime_b_grid_arch_term_q_get : Fin prime_b_grid_size -> ℚ
| ⟨0, _⟩ => 9.570036393390
| ⟨1, _⟩ => 9.584659678861
| ⟨2, _⟩ => 9.598369008991
| ⟨3, _⟩ => 9.611247470627
| ⟨4, _⟩ => 9.623368375697
| ⟨5, _⟩ => 9.634796657620
| ⟨6, _⟩ => 9.645590034992
| ⟨7, _⟩ => 9.655799986559
| ⟨8, _⟩ => 9.665472572255
| ⟨9, _⟩ => 9.674649127915
| ⟨10, _⟩ => 9.683366855792
| ⟨11, _⟩ => 9.691659328651
| ⟨12, _⟩ => 9.699556921850
| ⟨13, _⟩ => 9.707087185132
| ⟨14, _⟩ => 9.714275163720
| ⟨15, _⟩ => 9.721143676593
| ⟨16, _⟩ => 9.727713558471
| ⟨17, _⟩ => 9.734003870908
| ⟨18, _⟩ => 9.740032086993
| ⟨19, _⟩ => 9.745814253443
| _ => 9.745814253443

def prime_b_grid_val (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_val_q i : ℝ)

def prime_b_grid_prime_ub (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_prime_ub_q_get i : ℝ)

def prime_b_grid_arch_term (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_arch_term_q_get i : ℝ)

def prime_cert_margin_lb_q : ℚ := (12 / 25)

lemma prime_cert_margin_lb_eq_q : (prime_cert_margin_lb : ℝ) = prime_cert_margin_lb_q := by
  norm_num [prime_cert_margin_lb, prime_cert_margin_lb_q]

/-- Table min bound in ℚ: every grid margin is ≥ prime_cert_margin_lb_q. -/
lemma prime_b_grid_val_ge_lb_q :
    ∀ i : Fin prime_b_grid_size,
      prime_cert_margin_lb_q ≤ prime_b_grid_val_q i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val_q, prime_cert_margin_lb_q] <;> norm_num

/-- Table min bound: every grid margin is ≥ prime_cert_margin_lb. -/
lemma prime_b_grid_val_ge_lb :
    ∀ i : Fin prime_b_grid_size,
      prime_cert_margin_lb ≤ prime_b_grid_val i := by
  intro i
  have hq : prime_cert_margin_lb_q ≤ prime_b_grid_val_q i := prime_b_grid_val_ge_lb_q i
  have hq' : (prime_cert_margin_lb_q : ℝ) ≤ (prime_b_grid_val_q i : ℝ) := by
    exact_mod_cast hq
  simpa [prime_cert_margin_lb_eq_q, prime_b_grid_val] using hq'

/-- Table min bound with Lipschitz slack in ℚ: every grid margin is ≥ lb + L*h/2. -/
lemma prime_b_grid_val_ge_lb_with_slack_q :
    ∀ i : Fin prime_b_grid_size,
      (prime_cert_margin_lb_q + (3/5) * (1/10) / (2:ℚ)) ≤ prime_b_grid_val_q i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val_q, prime_cert_margin_lb_q] <;> norm_num

/-- Table min bound with Lipschitz slack: every grid margin is ≥ margin_lb + L*h/2. -/
lemma prime_b_grid_val_ge_lb_with_slack :
    ∀ i : Fin prime_b_grid_size,
      prime_cert_margin_lb + prime_cert_L_ub * prime_cert_B_h / 2 ≤ prime_b_grid_val i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val, prime_b_grid_val_q, prime_cert_margin_lb,
          prime_cert_L_ub, prime_cert_B_h] <;> norm_num

/-! Table arithmetic: margin lower bound from arch/prime bounds. -/

lemma prime_b_grid_val_le_arch_sub_prime_ub_q :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_val_q i ≤
        prime_b_grid_arch_term_q_get i - prime_b_grid_prime_ub_q_get i := by
  intro i
  fin_cases i <;>
    simp [prime_b_grid_val_q,
          prime_b_grid_arch_term_q_get,
          prime_b_grid_prime_ub_q_get] <;> norm_num

lemma prime_b_grid_val_le_arch_sub_prime_ub :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_val i ≤
        prime_b_grid_arch_term i - prime_b_grid_prime_ub i := by
  intro i
  have hq :
      prime_b_grid_val_q i ≤
        prime_b_grid_arch_term_q_get i - prime_b_grid_prime_ub_q_get i :=
    prime_b_grid_val_le_arch_sub_prime_ub_q i
  have hq' :
      (prime_b_grid_val_q i : ℝ) ≤
        (prime_b_grid_arch_term_q_get i - prime_b_grid_prime_ub_q_get i : ℝ) := by
    exact_mod_cast hq
  simpa [prime_b_grid_val, prime_b_grid_arch_term, prime_b_grid_prime_ub] using hq'

end Q3.Proofs.PrimeCert
