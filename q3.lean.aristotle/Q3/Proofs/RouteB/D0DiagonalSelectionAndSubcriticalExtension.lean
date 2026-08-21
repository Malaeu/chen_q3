import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Filter

namespace Q3.RouteB.D0Pstar

/-!
# Two abstract steps of the registered G5 route

The judge's primary G5 representation (verdict `2794daa0`) ends with

```text
fixed-m Galerkin weighted convergence
  -> one precommitted diagonal PairCofinal path
  -> CenteredTrialCriticalMomentRatio
```

and notes that a uniform rate of the projection index against the window index
is **not** logically required, because one is free to choose a single
precommitted diagonal: enumerate the rational weights below one half, and at
stage `k` satisfy the first `k` requirements. Monotonicity in the weight then
extends the conclusion from rational to every real weight below one half.

Both of those steps are pure order theory. They are separated here so that the
analytic work — the uniform source envelope and the fixed-window projection
convergence — is the only thing left that can fail.

⚠️ Nothing here is about the prolate source, the moment, or any estimate. These
lemmas mention no analysis and prove none. In particular they do not assert that
the requirements they diagonalize are satisfiable; that is exactly the open
obligation.

LEDGER:
  CLOSES: []
  OPENS:  []
-/

/-- **Diagonal selection.**  If every requirement is eventually met, one
strictly increasing choice meets the first `k` requirements at stage `k`.

Strict monotonicity is what later makes the selected index tend to infinity,
which is half of `PairCofinal`. -/
theorem exists_strictMono_diagonal_of_eventually
    {req : ℕ → ℕ → Prop}
    (h : ∀ j : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → req j N) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ k : ℕ, ∀ j : ℕ, j ≤ k → req j (N k) := by
  choose f hf using h
  refine ⟨fun k => k + (Finset.range (k + 1)).sup f, ?_, ?_⟩
  · intro a b hab
    have hsup : (Finset.range (a + 1)).sup f ≤ (Finset.range (b + 1)).sup f :=
      Finset.sup_mono (by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega)
    dsimp only
    omega
  · intro k j hjk
    refine hf j _ ?_
    have hmem : j ∈ Finset.range (k + 1) := by
      simp only [Finset.mem_range]
      omega
    have hle : f j ≤ (Finset.range (k + 1)).sup f := Finset.le_sup hmem
    dsimp only
    omega

/-- The selected diagonal index tends to infinity.  Stated separately because
that, and not the construction, is what a cofinality field consumes. -/
theorem tendsto_atTop_of_strictMono_nat {N : ℕ → ℕ} (hN : StrictMono N) :
    Tendsto N atTop atTop :=
  hN.tendsto_atTop

/-- **Subcritical extension.**  A downward-monotone property holding at every
rational weight in `[0, 1/2)` holds at every real weight there.

Downward monotone is the correct direction for a weighted bound: a smaller
weight is dominated by a larger one, so a bound at the larger weight is
inherited. -/
theorem forall_subcritical_of_forall_rat
    {Q : ℝ → Prop}
    (hmono : ∀ a b : ℝ, a ≤ b → Q b → Q a)
    (hrat : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < 1 / 2 → Q (q : ℝ)) :
    ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 → Q σ := by
  intro σ hσ0 hσ2
  obtain ⟨q, hσq, hq2⟩ := exists_rat_btwn hσ2
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans hσ0 hσq.le
  exact hmono σ (q : ℝ) hσq.le (hrat q hq0 hq2)

/-- The two steps composed in the shape the route uses: a diagonal that meets
the first `k` rational requirements, together with the extension of the
conclusion off the rationals. -/
theorem exists_diagonal_and_subcritical_extension
    {req : ℕ → ℕ → Prop} {Q : ℝ → Prop}
    (hreq : ∀ j : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → req j N)
    (hmono : ∀ a b : ℝ, a ≤ b → Q b → Q a)
    (hrat : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < 1 / 2 → Q (q : ℝ)) :
    (∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto N atTop atTop ∧
        ∀ k : ℕ, ∀ j : ℕ, j ≤ k → req j (N k)) ∧
      ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 → Q σ := by
  obtain ⟨N, hmonoN, hN⟩ := exists_strictMono_diagonal_of_eventually hreq
  exact ⟨⟨N, hmonoN, tendsto_atTop_of_strictMono_nat hmonoN, hN⟩,
    forall_subcritical_of_forall_rat hmono hrat⟩

#print axioms exists_strictMono_diagonal_of_eventually
#print axioms tendsto_atTop_of_strictMono_nat
#print axioms forall_subcritical_of_forall_rat
#print axioms exists_diagonal_and_subcritical_extension

end Q3.RouteB.D0Pstar
