/-
Minimal “heat RKHS” interface (no analysis)
==========================================

This file introduces a tiny RKHS-style interface sufficient to *state* the intended
`hA` matching lemma without committing to a full RKHS construction.

Key idea: if `eval x` is represented by a reproducing vector `k x`, then the matching
hypothesis needed by `RKHS_Interface_C1` becomes a pure evaluation statement:

  `inner ℂ (ψ i) (k (xi_n n)) = prime_vec ... i`
  ⇐ (reproducing) `inner ℂ (ψ i) (k (xi_n n)) = eval (xi_n n) (ψ i)`.
-/

import Q3.Basic.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

namespace Q3.Proofs

namespace HeatRKHSInterface

/-- Minimal RKHS package: a Hilbert space `H`, evaluation functionals `eval x`,
and reproducing vectors `k x` representing `eval x` by inner product. -/
structure HeatRKHS (t0 : ℝ) where
  H : Type
  instNormed : NormedAddCommGroup H
  instInner : InnerProductSpace ℂ H
  instComplete : CompleteSpace H
  eval : ℝ → (H →L[ℂ] ℂ)
  k : ℝ → H
  reproducing : ∀ (f : H) (x : ℝ), eval x f = inner ℂ f (k x)

attribute [instance] HeatRKHS.instNormed HeatRKHS.instInner HeatRKHS.instComplete

variable {t0 : ℝ} (R : HeatRKHS t0)

lemma inner_k_eq_eval (f : R.H) (x : ℝ) : inner ℂ f (R.k x) = R.eval x f := by
  simpa [R.reproducing f x] using (R.reproducing f x).symm

variable (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]

local notation "mDim" => Fin (2 * M + 1)

/-- If `ψ : mDim → H` are feature vectors in the RKHS, the `hA` matching condition
for `RKHS_Interface_C1` follows from a purely evaluational identity. -/
lemma h_eval_of_eval_eq_prime_vec
    {ψ : mDim → R.H}
    (h_evalFun :
      ∀ (n : Q3.Nodes K) (i : mDim),
        (R.eval (Q3.xi_n n)) (ψ i) = Q3.prime_vec M (Q3.xi_n n) i) :
    ∀ (n : Q3.Nodes K) (i : mDim),
      inner ℂ (ψ i) (R.k (Q3.xi_n n)) = Q3.prime_vec M (Q3.xi_n n) i := by
  intro n i
  simpa [inner_k_eq_eval (R := R) (f := ψ i) (x := Q3.xi_n n)] using (h_evalFun n i)

end HeatRKHSInterface

end Q3.Proofs
