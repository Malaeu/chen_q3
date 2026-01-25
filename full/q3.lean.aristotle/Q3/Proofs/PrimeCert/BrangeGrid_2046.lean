import Mathlib
import Q3.Proofs.PrimeCert.Defs

/-! Prime B-range margin grid values for t_critical.
Source: output/prime_cert_brange_tcritical_2026-01-25_2046.txt
Generated: 2026-01-25 23:46
Values are rounded *down* to 12 decimal places.
-/-

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Grid margins for B in [B_min, prime_cert_B_max] with step prime_cert_B_h. -/
def prime_b_grid_vals : Array ℝ := #[0.856457311774, 0.828016971090, 0.801354151698, 0.776307260754, 0.752733716336, 0.730507231598, 0.709515551568, 0.689658556946, 0.670846667303, 0.652999489949, 0.636044671464, 0.619916917295, 0.604557151420, 0.589911793260, 0.575932133198, 0.562573791361, 0.549796246996, 0.537562427922, 0.525838351309, 0.514592808436]

def prime_b_grid_val (i : Fin (prime_b_grid_vals.size)) : ℝ :=
  prime_b_grid_vals.get! i.1

/-- Table min bound: every grid margin is ≥ prime_cert_margin_lb. -/
axiom prime_b_grid_val_ge_lb :
    ∀ i : Fin (prime_b_grid_vals.size),
      prime_cert_margin_lb ≤ prime_b_grid_val i

end Q3.Proofs.PrimeCert
