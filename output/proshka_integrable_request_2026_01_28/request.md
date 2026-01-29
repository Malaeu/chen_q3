# Proshka request: integrability of a_star * heat_weight

**Problem (short):**
We need a lemma proving integrability of
`fun ξ => |a_star ξ| * heat_weight ξ`,
where `heat_weight ξ = exp(-4π^2 * t_critical * ξ^2) * |ξ|`.
This is required to close the arch-term Lipschitz bound in
`Brange_Lipschitz_HeatProof.lean`.

**Context:**
- We already closed the main Lipschitz step *assuming* this integrability.
- We already can close `h_int1`/`h_int2` for `a_star * phi_shift` via
  `phi_shift_integrable_with_a_star`.
- We do **not** yet have a general growth bound on `a_star` in the code.

**What we need from you:**
A concrete, minimal path to prove integrability in the current codebase.
Either:
- point to existing lemmas/estimates on `a_star`, or
- propose a new lemma (with a proof outline) and where to place it, or
- suggest a refactor that avoids requiring this integrability.

**Files included:**
- `Brange_Lipschitz_HeatProof_min_arch_int.lean` (target lemma)
- `Defs.lean` (a_star, heat kernel, base defs)
- `A_Star_Properties.lean` (continuity, bounded on compacts)
- `Q_nonneg_lemmas.lean` (fejer_heat_atom integrability, continuity)
- `Q_nonneg_atoms_helpers.lean` (phi_shift integrability)
- `Q_nonneg_base_atoms_proof.lean` (exp/heat kernel relation)
- `Brange_Lipschitz_HeatProof.lean` (main goal context)

**Goal statement (from Brange_Lipschitz_HeatProof_min_arch_int.lean):**
```
lemma arch_heat_weight_integrable :
    MeasureTheory.Integrable (fun ξ => |Q3.a_star ξ| * heat_weight ξ) := by
  -- need proof
```
