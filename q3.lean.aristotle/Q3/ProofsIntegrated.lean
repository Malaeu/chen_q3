/-
Q3 Proofs Integrated
====================

This file imports historical integrated modules and inventories their exported
theorem-shaped declarations. Some are independent proofs; others are direct
compatibility wrappers around project assumptions.

After importing this file, run:
  #print axioms Q3.Main.RH_of_Weil_and_Q3
to inspect the actual dependency profile. This inventory does not itself prove
closure or classify dependencies.
-/

-- Import all integrated proofs
import Q3.Proofs.A1_density_integrated
import Q3.Proofs.A3_bridge_integrated
import Q3.Proofs.Q_Lipschitz_integrated
import Q3.Proofs.Q_nonneg_on_atoms_integrated
import Q3.Proofs.RKHS_contraction_integrated
import Q3.Proofs.S_K_small_integrated
import Q3.Proofs.W_sum_finite_integrated
import Q3.Proofs.node_spacing_integrated
import Q3.Proofs.off_diag_exp_sum_integrated

namespace Q3.ProofsIntegrated

/-! ## Compatibility declaration inventory

Matching a source declaration's type is not evidence of independent closure.
Use `#print axioms` on each declaration to distinguish proofs from wrappers.
-/

-- A1 Density compatibility declaration
#check Q3.Proofs.A1_Density.closes_A1_density_axiom

-- A3 Bridge compatibility declaration
#check Q3.Proofs.A3_Bridge.closes_A3_bridge_axiom

-- Q Lipschitz compatibility declaration
#check Q3.Proofs.Q_Lipschitz.closes_Q_Lipschitz_axiom

-- Q Nonneg on Atoms direct compatibility wrapper
#check Q3.Proofs.Q_Nonneg.Q_nonneg_on_atoms_legacyCompatibility

-- RKHS Contraction compatibility declaration
#check Q3.Proofs.RKHS_Contraction.closes_RKHS_axiom

-- S_K Small compatibility declaration
#check Q3.Proofs.S_K_Small.closes_S_K_small_axiom

-- W Sum Finite compatibility declaration
#check Q3.Proofs.W_sum.closes_W_sum_axiom

-- Node Spacing compatibility declaration
#check Q3.Proofs.NodeSpacing.node_spacing

-- Off Diagonal Sum compatibility declaration
#check Q3.Proofs.OffDiagExpSum.closes_off_diag_axiom

end Q3.ProofsIntegrated
