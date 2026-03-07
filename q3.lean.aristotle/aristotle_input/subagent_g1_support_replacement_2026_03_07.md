# Sub-agent request: extract the honest G1 support-replacement brick

## Goal

Do **not** try to prove the old strong theorems

- `A1_density_WK`,
- `A1_density_WK_thm`,
- `A1_density_WK_fixed_t0`,

and do **not** restate “Fejér-heat atoms are dense in `W_K`” as if that were the
active honest mainline theorem.

The March 2026 reset changed the target. The active `G1` route now needs one
smaller support-preserving brick:

- an explicit finite shifted-evenized atom sum, under the margin condition
  `|τ_i| + δ ≤ K`, should be shown to lie in `Q3.AtomCone_K_fixed K t0`
  and hence in admissible `Q3.W_K K`.

This is the correct reusable local theorem for the current paper/Lean reset.

## Preferred exact target

Please add the following helper lemma in
`Q3/Proofs/A1prime/A1_density_fixed_t0.lean`
or in the nearest honest helper file if that is materially cleaner:

```lean
lemma atom_sum_mem_atomcone_fixed_of_margin
    (K t0 δ : ℝ) (hK : K > 0) (ht0 : 0 < t0) (hδ : 0 < δ)
    (n : ℕ) (c : Fin n → ℝ) (τ : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hmargin : ∀ i, |τ i| + δ ≤ K) :
    let g : ℝ → ℝ := fun x => ∑ i, c i * Atom δ t0 (τ i) x
    g ∈ Q3.AtomCone_K_fixed K t0 := by
  -- prove without sorry/exact?/admit
```

This is the preferred theorem because it isolates exactly the `hg_mem` brick
currently buried inside the old `A1_density_WK_fixed_t0` proof.

## Honest fallback target

If the preferred target is too large in one shot, the acceptable fallback is:

```lean
lemma atom_sum_mem_W_K_of_margin
    (K t0 δ : ℝ) (hK : K > 0) (ht0 : 0 < t0) (hδ : 0 < δ)
    (n : ℕ) (c : Fin n → ℝ) (τ : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hmargin : ∀ i, |τ i| + δ ≤ K) :
    let g : ℝ → ℝ := fun x => ∑ i, c i * Atom δ t0 (τ i) x
    g ∈ Q3.W_K K := by
  -- prove without sorry/exact?/admit
```

If you use the fallback, do **not** invent a fake closure theorem around it.
Return only the honest local support/membership brick.

## Available local lemmas: use these, do not reprove them

From `Q3/Proofs/A1_density.lean`:

- `Atom_eq_q3`
- `Atom_eq_zero_outside_open`
- `HeatKernel_LipschitzOn`

From `Q3/Proofs/A1prime/HatInterpBounded.lean`:

- `hat_interpolation_approx_bounded`

From `Q3/Proofs/A1prime/HeatError.lean`:

- `FejerKernel_support_bound`
- `heat_error_bound`
- `total_atom_error`
- `total_atom_error_even`

From `Q3/Proofs/Q_Lipschitz.lean`:

- `Q_Lipschitz_on_W_K_thm`

The main local definition is:

```lean
def Q3.W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | Continuous Φ ∧
       Function.support Φ ⊆ Set.Ioo (-K) K ∧
       IsEven Φ ∧
       IsNonneg Φ}
```

## Proof strategy

Please follow the structure already present inside the `hg_mem` block of
`Q3/Proofs/A1prime/A1_density_fixed_t0.lean`, but extract it as a standalone
helper theorem.

Suggested structure:

1. Define
   `g x := ∑ i, c i * Atom δ t0 (τ i) x`.
2. Refine the witness for `Q3.AtomCone_K_fixed K t0` directly.
3. Coefficients:
   use `hc_nonneg`.
4. Positive bandwidth:
   all atom widths are the same `δ`, so positivity is just `hδ`.
5. Margin control:
   use `hmargin`.
6. Function identity:
   use `Atom_eq_q3` to convert `Atom` to `Q3.Fejer_heat_atom`.
7. For the embedded `g ∈ Q3.W_K K` subgoal:
   - continuity: `continuous_finset_sum`,
   - support: `Atom_eq_zero_outside_open`,
   - evenness: rewrite by symmetry of `FejerKernel` and `HeatKernel`,
   - nonnegativity: `Finset.sum_nonneg`, kernel factors nonnegative.

## Constraints

- No `sorry`, no `exact?`, no `admit`.
- Do not import `Q3/Archive` or `Q3/Clean`.
- Do not change the active gate-state narrative.
- Do not state or prove any global density theorem on `W_K`.
- Do not reintroduce the old overclaim “A1_density_WK is the honest mainline theorem”.
- Keep the deliverable small and local.

## Deliverable

Return a Lean patch that compiles in the active project and does one of:

1. proves `atom_sum_mem_atomcone_fixed_of_margin`, or
2. proves the fallback `atom_sum_mem_W_K_of_margin`.

If neither is achievable, return the **first blocked local sublemma** only,
with an explicit statement, and do not manufacture a fake closure theorem.
