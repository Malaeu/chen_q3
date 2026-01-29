/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 262f9575-6f98-4b86-a68a-4febe3366720

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error while processing imports for this file.
You are importing a file that is unknown to Aristotle, Aristotle supports importing user projects, but files must be uploaded as project context, please see the aristotlelib docs or help menu, and ensure your version of `aristotlelib` is up to date.
Details:
unknown module prefix 'Q3'

No directory 'Q3' or file 'Q3.olean' in the search path entries:
/code/harmonic-lean/.lake/packages/batteries/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Qq/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/aesop/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/proofwidgets/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/importGraph/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/plausible/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/MD4Lean/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/BibtexQuery/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/UnicodeBasic/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Cli/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/doc-gen4/.lake/build/lib/lean
/code/harmonic-lean/.lake/build/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean
-/

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
