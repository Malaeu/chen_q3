/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d4c59ac9-dcf8-468e-b85b-3c3ac7603da9

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

import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_PPCover

noncomputable section

namespace Q3.Proofs.PrimeCert

/--
Pointwise prime-power term bound needed to close the i=19 pp-cover chain.
Targeted Aristotle request: no extra goals, no unrelated sorries.
-/
theorem prime_b_grid_weight_term_le_pp_i19_all_ub_target :
    ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
      prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n := by
  sorry

end Q3.Proofs.PrimeCert
