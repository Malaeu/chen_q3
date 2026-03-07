# Sub-agent request: isolate the honest `W_K` membership brick

## Goal

Do **not** try to prove the old strong theorems

- `A1_density_WK`,
- `A1_density_WK_thm`,
- `A1_density_WK_fixed_t0`,
- `atom_sum_mem_atomcone_fixed_of_margin`.

The next honest target is smaller and more precise:

- isolate only the local proof that a finite nonnegative atom sum, under the margin
  condition `|τ_i| + δ ≤ K`, lies in the real admissible set `Q3.W_K K`.

This is the first clean reusable brick after the failed `G1.4` attempt.

## Exact target

Please add the following helper lemma in
`Q3/Proofs/A1prime/A1_density_fixed_t0.lean`
or in the nearest honest helper file if that is materially cleaner:

```lean
lemma atom_sum_mem_W_K_of_margin
    (K t0 δ : ℝ) (hK : K > 0) (ht0 : 0 < t0) (hδ : 0 < δ)
    (n : ℕ) (c : Fin n → ℝ) (τ : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hmargin : ∀ i, |τ i| + δ ≤ K) :
    let g : ℝ → ℝ := fun x => ∑ i, c i * Atom δ t0 (τ i) x
    g ∈ Q3.W_K K := by
  -- prove without sorry/admit; exact? is acceptable if it compiles
```

If this exact target is still too large, return only the **first blocked local sublemma**
below it, with an explicit Lean statement, and do not widen the claim.

## Real local context

`Q3.W_K` is the real project definition from `Q3/Basic/Defs.lean`:

```lean
def Q3.W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | Continuous Φ ∧
       Function.support Φ ⊆ Set.Ioo (-K) K ∧
       IsEven Φ ∧
       IsNonneg Φ}
```

The exact proof shape already exists inline inside the `hg_mem` block of
`Q3/Proofs/A1prime/A1_density_fixed_t0.lean`, around the subgoal

```lean
-- g ∈ W_K K
```

Your task is to extract only that brick as a standalone theorem.

## Available lemmas: use these, do not reprove them

From `Q3/Proofs/A1_density.lean`:

- `Atom_eq_zero_outside_open`
- `Atom_eq_q3`

From Mathlib / project context:

- `continuous_finset_sum`
- `Finset.sum_nonneg`
- kernel symmetries already used inline in the `hg_mem` block

Relevant downstream file:

- `Q3/T5_Transfer.lean`
  - once this theorem exists, the stronger cone-level wrapper can be built later
  - but do **not** prove that wrapper now

## Suggested proof structure

1. Define
   `g x := ∑ i, c i * Atom δ t0 (τ i) x`.
2. Refine membership in `Q3.W_K K` as a 4-field witness:
   continuity, support, evenness, nonnegativity.
3. Continuity:
   use `continuous_finset_sum`, then continuity of each atom term exactly as in the
   inline `hg_mem` proof.
4. Support:
   use `Function.support_subset_iff'` or the existing pointwise contradiction style,
   together with `Atom_eq_zero_outside_open hK hδ (hmargin i)`.
5. Evenness:
   reuse the current symmetry argument for `FejerKernel` and `HeatKernel`.
6. Nonnegativity:
   use `Finset.sum_nonneg`, `hc_nonneg`, and nonnegativity of the kernel factors.

## Constraints

- No `sorry` or `admit`.
- `exact?` is allowed if it helps close local subgoals and the resulting file
  compiles in the real Q3 project context.
- Do not define dummy local replacements for `Q3.W_K`, `Atom`, `IsEven`, or `IsNonneg`.
- Do not import `Q3/Archive`, `Q3/Clean`, or heavy `PrimeCert` files.
- Do not restate or prove any global density theorem on `W_K`.
- Do not claim closure of `G1`, `G2`, or `G3`.
- Keep the patch small and local.

## Deliverable

Return a Lean patch that compiles in the active project and does one of:

1. proves `atom_sum_mem_W_K_of_margin`, or
2. returns the first blocked local sublemma below it, with an explicit Lean statement.

Do **not** manufacture a stronger closure theorem.
