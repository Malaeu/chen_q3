/-
Minimal Aristotle sandbox file for integrability of the heat-weighted arch term.
No Q3.Axioms imports. Do not integrate directly; copy proof bodies only.
-/

import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatIntegrable

set_option linter.mathlibStandardSet false

open scoped Real Classical
open MeasureTheory
open Q3

noncomputable section

/-- Integrability of the heat-weighted arch integrand. -/
lemma arch_heat_weight_integrable :
    MeasureTheory.Integrable (fun ξ => |Q3.a_star ξ| *
      Q3.Proofs.PrimeCert.heat_weight Q3.t_critical ξ) := by
  -- Use the global growth bound + Gaussian integrability.
  simpa using
    (Q3.Proofs.PrimeCert.integrable_abs_a_star_mul_heat_weight
      (t := Q3.t_critical) Q3.t_critical_pos)
