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

open scoped ComplexConjugate

/-!
`HeatRKHS` is a minimal RKHS-style interface compatible with Mathlib's convention:
the inner product is sesquilinear, conjugate-linear in the first argument and linear in the second.

So the “reproducing identity” is written using `⟪k x, f⟫` (linear in `f`) rather than `⟪f, k x⟫`.
-/

/-- Minimal RKHS package: a Hilbert space `H`, evaluation functionals `eval x`,
and reproducing vectors `k x` representing `eval x` by inner product. -/
structure HeatRKHS (t0 : ℝ) where
  H : Type
  instNormed : NormedAddCommGroup H
  instInner : InnerProductSpace ℂ H
  instComplete : CompleteSpace H
  eval : ℝ → (H →L[ℂ] ℂ)
  k : ℝ → H
  reproducing : ∀ (f : H) (x : ℝ), eval x f = inner ℂ (k x) f

attribute [instance] HeatRKHS.instNormed HeatRKHS.instInner HeatRKHS.instComplete

variable {t0 : ℝ} (R : HeatRKHS t0)

lemma eval_eq_inner_k (f : R.H) (x : ℝ) : R.eval x f = inner ℂ (R.k x) f :=
  R.reproducing f x

lemma inner_k_eq_eval (f : R.H) (x : ℝ) : inner ℂ (R.k x) f = R.eval x f := by
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
      inner ℂ (R.k (Q3.xi_n n)) (ψ i) = Q3.prime_vec M (Q3.xi_n n) i := by
  intro n i
  simpa [eval_eq_inner_k (R := R) (f := ψ i) (x := Q3.xi_n n)] using (h_evalFun n i)

/-- Variant tailored for `RKHS_Interface_C1`: if the *linear* evaluation map matches
`conj (prime_vec ...)`, then the needed `inner (ψ i) (k x)` identity holds. -/
lemma h_eval_of_eval_eq_conj_prime_vec
    {ψ : mDim → R.H}
    (h_evalFun :
      ∀ (n : Q3.Nodes K) (i : mDim),
        (R.eval (Q3.xi_n n)) (ψ i) = conj (Q3.prime_vec M (Q3.xi_n n) i)) :
    ∀ (n : Q3.Nodes K) (i : mDim),
      inner ℂ (ψ i) (R.k (Q3.xi_n n)) = Q3.prime_vec M (Q3.xi_n n) i := by
  intro n i
  -- `eval = ⟪k,ψ⟫ = conj ⟪ψ,k⟫`
  have h1 :
      inner ℂ (R.k (Q3.xi_n n)) (ψ i) = conj (Q3.prime_vec M (Q3.xi_n n) i) := by
    simpa [eval_eq_inner_k (R := R) (f := ψ i) (x := Q3.xi_n n)] using (h_evalFun n i)
  have h2 :
      conj (inner ℂ (R.k (Q3.xi_n n)) (ψ i)) = inner ℂ (ψ i) (R.k (Q3.xi_n n)) := by
    simpa using (inner_conj_symm (𝕜 := ℂ) (x := R.k (Q3.xi_n n)) (y := ψ i))
  -- apply conjugation to `h1` and simplify
  have := congrArg (fun z : ℂ => conj z) h1
  simpa [h2] using this

end HeatRKHSInterface

end Q3.Proofs
