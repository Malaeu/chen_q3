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
| Scalar generator positivity | `full/sections/Main_closure.tex`, new Prop. `compatibility-reduction-shifted-atoms` | currently no dedicated Lean theorem | missing | prove `Q (Fejer_heat_atom B t0_critical τ) ≥ 0` |
| Weil linkage | `full/sections/Weil_linkage.tex` | `Q3/Main.lean` | stable | wire only after scalar node is closed |

## What We No Longer Pretend

- `τ=0` centered atoms are **not** dense in the full even Weil class.
- `Path B` is **not** the mathematical closure route for the active paper.
- `prime_heat_bounds_arch_data` is **not** the right first blocker for paper mainline.
- Positivity of a single shifted window `phi_shift` is stronger than needed; the paper only needs positivity of the evenized shifted atom `Fejer_heat_atom`.

## Exact Missing Theorem

For each compact `K ≥ 1`, prove:

```lean
theorem Q_fejer_heat_atom_nonneg_tcritical
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    Q (Fejer_heat_atom B t0_critical τ) ≥ 0
```

Once this theorem exists, the rest of the compact closure is already formalized:

1. `Q_nonneg_on_atomcone_fixed_tcritical_of_shifted_evenized_atoms`
2. `Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms`
3. Weil linkage

## Lean Realization Already Present

File:

- `Q3/Proofs/CompatibilityReduction.lean`

Theorems:

- `Q_nonneg_on_atomcone_fixed_tcritical_of_shifted_evenized_atoms`
- `Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms`

These two theorems are the formal version of the paper compatibility proposition.
They deliberately isolate the remaining scalar inequality instead of smearing it
across `Main.lean` or legacy prime certificates.

## Recommended Refactor Order

1. Keep `Q3/Proofs/CompatibilityReduction.lean` as the canonical closure hub.
2. Introduce a new dedicated scalar module for shifted evenized atoms, not for `τ=0` only.
3. Refactor `Q3/Proofs/Q_nonneg_t_critical.lean` so that:
   - it stops advertising the false `τ=0` density story;
   - it targets `Fejer_heat_atom` directly;
   - any `phi_shift` lemmas are treated only as auxiliary decomposition tools.
4. Only after the scalar theorem is real, rewire `Main.lean` onto this route.

## Progress Labels

Each node should be tracked with:

- `paper-read`
- `lean-target-frozen`
- `reduction-theoremized`
- `scalar-bound-missing`
- `compiles`
- `mainline-wired`

## Immediate Priority

1. Design the scalar proof for `Q (Fejer_heat_atom B t0_critical τ) ≥ 0`.
2. Avoid the false detour “prove positivity of each `phi_shift`”.
3. Reuse `A1' + A2 + T5_transfer_of_atoms` exactly as packaged now.
