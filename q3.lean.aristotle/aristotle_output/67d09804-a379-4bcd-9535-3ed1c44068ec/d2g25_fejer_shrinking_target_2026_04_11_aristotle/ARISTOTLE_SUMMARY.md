# Summary of changes for run 37ae106c-0f73-4bbc-a6ed-f021a9513200
## Fejér Shrinking-Target Bridge — Formalization Complete

I formalized the finite Fourier-analytic lemma described in `d2g25_fejer_shrinking_target_2026_04_11.md` in the file `RequestProject/FejerBridge.lean`. The formalization is fully verified with no `sorry`, no `admit`, and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Main Result

**`fejer_shrinking_target_bridge`**: For any finite set `Γ : Finset ℝ`, real `α`, and `0 < ε ≤ 1/4`:

```
#{γ ∈ Γ : distToInt(αγ) ≤ ε} ≤ 2π²ε · |Γ| + 2π²ε · ∑_{j=1}^{H-1} ‖S_α(j)‖
```

where `H = ⌊1/(2ε)⌋`, `distToInt(x) = |x - round(x)|` is the distance to the nearest integer, and `S_α(j) = ∑_{γ ∈ Γ} e(jαγ)` is the exponential sum with `e(x) = exp(2πix)`.

The absolute constant is `C = 2π²`.

### Proof Structure

The proof follows the preferred route outlined in the specification:

1. **Definitions** (`distToInt`, `eC`, `dirichletSum`, `expSum`, `shrinkCount`, `fejerH`): Clean definitions of all required objects.

2. **Basic eC properties** (`eC_zero`, `eC_add`, `norm_eC`, `eC_conj`, `eC_int`, `eC_pow`): Properties of the complex exponential `e(x) = exp(2πix)`.

3. **Dirichlet sum properties** (`norm_eC_sub_one`, `dirichletSum_geom`, `dirichletSum_at_periodic`, `norm_dirichletSum`): Key identity `|D_H(x)| = |sin(πHx)|/|sin(πx)|` via geometric series.

4. **Fejér lower bound** (`dirichletSum_norm_lower`, `dirichletSum_normSq_lower`): If `distToInt(x) ≤ 1/(2H)`, then `‖D_H(x)‖ ≥ 2H/π`, using Jordan's inequality and `sin(x) ≤ x`.

5. **Double sum expansion** (`sum_dirichletSum_normSq_bound`): `∑_γ ‖D_H(αγ)‖² ≤ H|Γ| + 2H ∑_{j=1}^{H-1} ‖S(j)‖`, proved by expanding the norm squared, swapping summation, and bounding off-diagonal terms.

6. **Floor function bounds** (`fejerH_ge_two`, `eps_le_half_inv_fejerH`, `inv_fejerH_le`): `H ≥ 2`, `ε ≤ 1/(2H)`, and `1/H ≤ 4ε`.

7. **Main theorem**: Combines all ingredients: pointwise majorization by the Fejér kernel → sum over Γ → expand and bound → use `1/H ≤ 4ε`.

### Notes

- No zeta-specific or number-theoretic facts are used — the result is purely finite and Fourier-analytic.
- The proof uses elementary inequalities (`nlinarith`, `ring`, `field_simp`) and basic Finset sum lemmas, as requested.
- The optional corollary about eventual vanishing was not included, as the main target (the finite bridge inequality) was the priority.