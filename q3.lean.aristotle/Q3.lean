/-
Q3 Formalization - Riemann Hypothesis via Weil Positivity
=========================================================

Entry point for the Q3 proof chain. This file re-exports the main theorem
and all supporting modules for documentation generation.

Main result: `Q3.Main.RH_of_Weil_and_Q3 : RH`
-/

-- Core modules (for doc-gen4 to include in documentation)
import Q3.Basic.Defs
import Q3.Axioms
import Q3.AxiomsTheorems
import Q3.Main

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
