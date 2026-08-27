/-
Q3 Formalization - Riemann Hypothesis via Weil Positivity
=========================================================

Default entry point for the Q3 formalization and documentation surface.

There is no unconditional RH export.  The corrected square-class interfaces
state their mathematical inputs explicitly.  The compiled broad-cone
compatibility route requires an explicit `import Q3.Main` and is not re-exported
from this default module.
-/

-- Core modules (for doc-gen4 to include in documentation)
import Q3.Basic.Defs
import Q3.Basic.WeilSquareClass
import Q3.Basic.WeilDirectRoute
import Q3.Axioms
import Q3.AxiomsTheorems

-- Supporting theorems
import Q3.A1_Density
import Q3.A2_Lipschitz
import Q3.A3_Bridge
import Q3.Atoms_Positive
import Q3.T5_Transfer
import Q3.RKHS_Contraction
import Q3.DigammaSeries
import Q3.DigammaRemainder

-- Proof modules (key bridges and theorems)
import Q3.Proofs.Q_Lipschitz
import Q3.Proofs.A1_density
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.RKHS_contraction
import Q3.Proofs.Rayleigh_Fourier
