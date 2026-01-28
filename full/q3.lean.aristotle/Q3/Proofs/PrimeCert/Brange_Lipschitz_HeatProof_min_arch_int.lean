/-
Minimal Aristotle sandbox file for integrability of the heat-weighted arch term.
No Q3.Axioms imports. Do not integrate directly; copy proof bodies only.
-/

import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical

set_option linter.mathlibStandardSet false

open scoped Real Classical
open MeasureTheory
open Q3

noncomputable section

/-- Heat-weighted factor used in the Lipschitz bound. -/
def heat_weight (xi : ℝ) : ℝ :=
  Real.exp (-4 * Real.pi ^ 2 * Q3.t_critical * xi ^ 2) * |xi|

/-- Integrability of the heat-weighted arch integrand. -/
lemma arch_heat_weight_integrable :
    MeasureTheory.Integrable (fun ξ => |Q3.a_star ξ| * heat_weight ξ) := by
  -- PROVIDED SOLUTION
  -- 1) Use that `a_star` is continuous and has mild growth (logarithmic) if available.
  -- 2) Use integrability of functions dominated by exp(-c*ξ^2) * |ξ|.
  -- 3) Conclude by comparison.
  sorry
