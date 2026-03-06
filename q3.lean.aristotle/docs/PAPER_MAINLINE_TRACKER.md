# Paper Mainline Tracker

Updated: 2026-03-06

## Goal

Держать активную формализацию в соответствии с реальной бумажной mainline из
`full/RH_Q3.tex`, а не с legacy `τ=0`-маршрутом и не с compute-heavy PrimeHeat
сертификатами.

Актуальная бумажная цепочка теперь выглядит так:

`T0 -> A1' (shifted evenized density) -> A2 (Lipschitz continuity) -> compatibility reduction -> Weil positivity on W_K -> RH`

Содержательный нерешённый узел один:

`compatibility reduction` = доказать `Q ≥ 0` на shifted evenized Fejer-heat atoms
при критическом масштабе.

## Frozen Contract

| Role | Paper value | Lean object | Status |
| --- | --- | --- | --- |
| Fixed A1 scale | `t0 = t0_critical` | `Q3.t0_critical` | aligned |
| Equivalent Q-scale | `t = t_critical = 3/20` | `Q3.t_critical` | aligned |
| Generator family | shifted evenized atoms `\Phi_{B,t,\tau}^{even}` | `Q3.Fejer_heat_atom B t0_critical τ` | aligned |
| Support condition | `|\tau| + B ≤ K` | `AtomCone_K_fixed K t0` membership condition | aligned |
| Closure mechanism | A1' + A2 + positivity on generators | `Q3.T5.T5_transfer_of_atoms` | aligned |

## Mainline Nodes

| Paper node | TeX source | Lean target | Current state | Next action |
| --- | --- | --- | --- | --- |
| T0 normalization | `full/sections/T0.tex` | `Q3/AxiomsTheorems.lean`, `Q3/Main.lean` | stable | keep stable |
| A1' shifted density | `full/sections/A1prime.tex` | `Q3/Proofs/A1prime/A1_density_fixed_t0.lean` | theorem exists | reuse directly |
| A2 continuity | `full/sections/A2.tex` | `Q3/Proofs/Q_Lipschitz.lean` | theorem exists | reuse directly |
| Compatibility reduction | `full/sections/Main_closure.tex` | `Q3/Proofs/CompatibilityReduction.lean` | theoremized on 2026-03-06 | keep as canonical reduction node |
| Scalar generator positivity | `full/sections/Main_closure.tex`, new Prop. `compatibility-reduction-shifted-atoms` | `Q3.Q_Fejer_heat_atom_nonneg_t_critical` | theorem name exists, but still inherits scalar placeholder | replace the placeholder by an honest weaker theorem |
| Weil linkage | `full/sections/Weil_linkage.tex` | `Q3/Main.lean` | stable | wire only after scalar node is closed |

## What We No Longer Pretend

- `τ=0` centered atoms are **not** dense in the full even Weil class.
- `Path B` is **not** the mathematical closure route for the active paper.
- `prime_heat_bounds_arch_data` is **not** the right first blocker for paper mainline.
- Positivity of a single shifted window `phi_shift` is stronger than needed; the paper only needs positivity of the evenized shifted atom `Fejer_heat_atom`.

## Scalar Node Exported But Not Closed

For each compact `K ≥ 1`, the paper-facing scalar theorem name is now exported in Lean:

```lean
theorem Q_Fejer_heat_atom_nonneg_t_critical
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    0 ≤ Q (Fejer_heat_atom B t0_critical τ)
```

The weaker symmetric pair node is also present:

```lean
theorem Q_phi_shift_pair_nonneg_t_critical
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    0 ≤ Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))
```

But this is not yet a mathematical closure of the scalar node.
Right now the dependency chain is:

1. `Q_phi_shift_nonneg_t_critical`
2. `Q_phi_shift_pair_nonneg_t_critical`
3. `Q_Fejer_heat_atom_nonneg_t_critical`

and step 1 is still just a wrapper around
`prime_term_le_at_t_critical_axiom`.

So the compact closure machinery below is theoremized and reusable, but it is
not yet fed by an honest scalar theorem:

1. `Q_nonneg_on_atomcone_fixed_tcritical_of_shifted_evenized_atoms`
2. `Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms`
3. `Q_nonneg_on_WK_tcritical_of_phi_pair_nonneg`
4. Weil linkage

## Lean Realization Already Present

File:

- `Q3/Proofs/CompatibilityReduction.lean`
- `Q3/Proofs/Q_nonneg_t_critical.lean`
- `Q3/Proofs/PaperMainlineAtomRoute.lean`

Theorems:

- `Q_nonneg_on_atomcone_fixed_tcritical_of_shifted_evenized_atoms`
- `Q_fejer_heat_atom_nonneg_of_phi_pair_nonneg_tcritical`
- `Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms`
- `Q_nonneg_on_WK_tcritical_of_phi_pair_nonneg`
- `Q_nonneg_on_WK_tcritical_of_phi_nonneg`
- `Q_nonneg_on_WK_tcritical_current_shift_route`
- `Q_nonneg_on_WK_tcritical_current_atom_route`
- `Q_phi_shift_pair_nonneg_t_critical`
- `Q_Fejer_heat_atom_nonneg_t_critical`
- `exists_WK_of_mem_Weil_cone`
- `Q_nonneg_on_Weil_cone_current_atom_route`
- `RH_of_shifted_atom_route`

These theorems split cleanly into:
- scalar positivity at `t_critical` in `Q_nonneg_t_critical.lean`;
- closure transfer in `CompatibilityReduction.lean`.

That separation is the right paper architecture. The remaining problem is that
the scalar file still closes through the old placeholder, so the architecture is
ready but the last mathematical gate is not yet honest.

## New Mainline Vertex

The new module `Q3/Proofs/PaperMainlineAtomRoute.lean` now packages the full
paper-style route:

1. extract `K ≥ 1` and `Φ ∈ W_K K` from `Φ ∈ Weil_cone`,
2. apply `Q_nonneg_on_WK_tcritical_current_atom_route`,
3. conclude `Q ≥ 0` on all of `Weil_cone`,
4. apply the full `Weil_criterion`.

Current axiom profile of the new top theorem:

```lean
#print axioms Q3.RH_of_shifted_atom_route
-- [propext, Classical.choice, Quot.sound,
--  Q3.Weil_criterion, Q3.prime_term_le_at_t_critical_axiom]
```

This is the first top-level RH theorem in the tree that no longer mentions
`Weil_criterion_tau0` or `prime_cert_margin_from_pathB` in its own axiom list.
But it still depends on `prime_term_le_at_t_critical_axiom`, so this must be
read as a structural source-of-truth win, not as the final closure of the paper.

## Recommended Refactor Order

1. Keep `Q3/Proofs/CompatibilityReduction.lean` as the canonical closure hub.
2. Treat `Q3/Proofs/Q_nonneg_t_critical.lean` as the scalar source of truth for the active `t_critical` route, but do not confuse theorem wrappers with closure.
3. Keep `phi_shift` positivity explicitly auxiliary; the paper-facing node is `Q_Fejer_heat_atom_nonneg_t_critical`.
4. `Q3/Main.lean` is already rewired through the atom route; the remaining job is to replace its scalar placeholder, not to rewire the top theorem again.
5. Continue deleting stale comments and docs that still describe `τ=0` centered closure as if it were the active main paper path.

## Progress Labels

Each node should be tracked with:

- `paper-read`
- `lean-target-frozen`
- `reduction-theoremized`
- `scalar-bound-missing`
- `compiles`
- `mainline-wired`

## Immediate Priority

1. Propagate the new axiom profile into every remaining status/dashboard file that still claims the active chain uses `Weil_criterion_tau0` or `prime_cert_margin_from_pathB`.
2. Avoid reintroducing the false detour “prove positivity of each `phi_shift`” as the main theorem target.
3. Replace `prime_term_le_at_t_critical_axiom` by an honest weaker scalar contract on the paper generator before any full paper rewrite.
4. Reuse `A1' + A2 + T5_transfer_of_atoms` exactly as packaged now.
