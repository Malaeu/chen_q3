# Chain Status (compiled broad-cone route vs corrected public target)

**Status:** support snapshot only; read this only after the 4 canonical control-docs.
Gate-state now lives in `PROJECT_ORCHESTRATOR.md`, not here.

**Purpose:** Supporting chain summary for the compiled Lean route after the
target-cone audit.
**Current status:** Use `Q3/CheckAxioms.lean` as the authoritative dependency
list for the compiled Lean export, but use `PROJECT_ORCHESTRATOR.md` for the
public RH contract.
**Bridge note (2026-03-07):** active `Q3.Main` still compiles through the
shifted-atom broad-cone route and inherits a single scalar placeholder
`Q3.prime_term_le_at_t_critical_axiom`, but the public manuscript target has
already pivoted to the corrected positive-definite cone.
**Next action:** freeze `A1-pd`, not the old broad-cone closure slogans.
**Decision (2026-03-07):** source of truth for RH mainline is now the corrected
positive-definite route; compiled `Q3.Main` is a background export until Lean
contract renames are performed.
**Links:** `ACTIVE/MAIN_CHAIN_DEPS.md` · `Q3/CheckAxioms.lean` · `ACTIVE/orchestrator.md`

---

This file is the canonical, minimal chain summary for the compiled Lean route.
It is intended to stay aligned with the code after each refactor, without
overriding the control-plane verdict.

## Public vs compiled target

- Public paper target: positivity on the corrected positive-definite cone
  `\mathcal W^{pd}`.
- Compiled Lean export: positivity on the broad `Weil_cone`.
- Relationship: compiled broad-cone route is background-only after `T0.1`.

## Mainline parameters (compiled route only)

- Use single-scale t_critical = 3/20.
- Use shifted evenized atoms `Fejer_heat_atom B t0_critical τ`.
- Compiled route still uses the full `Weil_cone` / `W_K` route, not `Weil_cone_tau0`.
- Avoid the old two-scale chain and the old `τ=0` certificate route in the mainline.

## Statement Sheet (compiled route)

- Formal compiled export (Lean): `Q3.Main.RH_of_Weil_and_Q3`.
- Public mathematical target: positivity on `\mathcal W^{pd}`.
- Logical compiled gate: `Q3.Weil_criterion` (broad `Weil_cone` export ↔ RH).
- Normalization: `t_critical = 3/20`, `t0_critical = 1/(16π² t_critical)`,
  generator `Fejer_heat_atom B t0_critical τ`, support condition `|τ| + B ≤ K`.

## Assumption Stack (mainline)

- Standard/kernel: `propext`, `Classical.choice`, `Quot.sound`.
- External math: `Q3.Weil_criterion`.
- Scalar placeholder: `Q3.prime_term_le_at_t_critical_axiom`.
- Everything else in the chain is a theorem.

## Notation Glossary (frozen, minimal)

- `Q*(t; Phi) = arch_term - prime_term` (see `Q_STAR_DEFINITIONS.md`).
- `w_Q(n) = 2*Λ(n)/√n`, `xi_n = log n / (2π)`.
- `phi_shift_critical B τ` = shifted Fejér×heat window at `t_critical`.
- `Fejer_heat_atom B t0_critical τ` = evenized shifted atom used by A1'.
- `P_A` = symbol (period 1).

## Revision Log (local)

- 2026-02-03: added statement sheet, assumption stack, notation glossary.
- 2026-02-04: align PrimeHeat axioms (`prime_heat_bounds_arch_data`, `prime_heat_bucket_data`).
- 2026-03-06: source-of-truth reset to active shifted-atom route.
- 2026-03-07: `T0.1` audit verdict `pivot required`; public mainline moved to
  corrected positive-definite cone, compiled route kept as background export.

## Current chain (code-level)

1) Scalar positivity node
- File: `Q3/Proofs/Q_nonneg_t_critical.lean`.
- Exported theorem names:
  `Q_phi_shift_pair_nonneg_t_critical`,
  `Q_Fejer_heat_atom_nonneg_t_critical`.
- Reality: both still inherit
  `prime_term_le_at_t_critical_axiom` through
  `Q_phi_shift_nonneg_t_critical`.

2) Compact closure node
- File: `Q3/Proofs/CompatibilityReduction.lean`.
- Status: theoremized.
- Content: A1' density + A2 continuity + scalar positivity on shifted evenized atoms
  imply positivity on every `W_K K`.

3) Global Weil node
- File: `Q3/Proofs/PaperMainlineAtomRoute.lean`.
- Status: theoremized.
- Content: extract `K ≥ 1` from `Φ ∈ Weil_cone`, apply compact closure, then `Weil_criterion`.

## Main-chain blockers (authoritative)

These are the only nonstandard axioms blocking the **current** main chain:

- `Q3.Weil_criterion`
- `Q3.prime_term_le_at_t_critical_axiom`

Authoritative check:
```bash
lake env lean Q3/CheckAxioms.lean
```

Important note:
- `Q3.prime_term_le_at_t_critical_axiom` is in the active chain, but local repo notes
  already mark the full `τ`-uniform scalar claim as false-for-now.
- So the current mainline is structurally informative, but not yet the final honest proof object.

## Note on Tier-1 axioms

The authoritative `#print axioms Q3.Main.RH_of_Weil_and_Q3` output currently includes
`Q3.Weil_criterion`. It does **not** include `Q3.Weil_criterion_tau0`,
`Q3.prime_cert_margin_from_pathB`, or `Q3.Schur_test`,
even though those names still exist elsewhere in the tree.

## Legacy (not in the current main chain)

The older `τ=0` / PathB / PrimeCert mainline descriptions are **legacy** and no
longer load-bearing in `Q3/Main.lean`. Keep them only for reference/archival.

See `ACTIVE/refs/legacy_two_scale_index.md` for legacy context.

## Related entry points

- `ACTIVE/orchestrator.md` (status, next steps)
- `ACTIVE/MAIN_CHAIN_DEPS.md` (authoritative deps)
- `ACTIVE/insights.md` (running synthesis notes)
