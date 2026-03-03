# Proshka request: prime_heat arch kernel closure (checker-free)

## Read first (mandatory)

Load this context before analysis:
- `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_context_pack_2026_03_03.md`

Role reminder:
- You are Proshka, elite mathematician + Lean engineer.
- Work deterministically: no speculation, no ambiguous output.

## Goal (single)

Remove the data axiom dependency from the arch heat bound:

- file:
  `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
- current theorem:
  `prime_heat_bounds_arch_data`
- current legacy axiom it uses:
  `prime_heat_bounds_arch_data_from_data_legacy_axiom`

Target theorem shape (must remain exactly this inequality):

```lean
∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
    |a_star ξ| * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * |ξ|)
  ≤ prime_cert_L_arch_heat_raw
```

with fixed constants:
- `prime_cert_B_max = 4.9`
- `t_critical = 3/20`
- `prime_cert_L_arch_heat_raw = 1.360378581976`

## Hard constraints

1. No `native_decide`, no `admit`, no `sorry`, no `exact?`.
2. No new axioms.
3. Keep existing numeric constants unchanged (15 digits policy).
4. Kernel-safe load-bearing proof route.
5. Do not route through `BrangeHeatCert_2026_01_28_Checker.lean`.

## Ground truth already validated

- Normalization in code:
  `a_star ξ = 2 * Real.pi * a ξ`.
- Sanity-check for exact target integrand (same formula):
  - `a(0) ≈ 5.3721834192`
  - `a_star(0) ≈ 33.7544239272`
  - target integral over `[-4.9, 4.9]` is numerically near
    `1.36037830996`, consistent with
    `prime_cert_L_arch_heat_raw = 1.360378581976`.
- Known blocker:
  naive global majorant `|a_star ξ| ≤ C0 + C1|ξ|` with whole-line erf-free
  replacement is too crude (`C0/α` alone overshoots badly), so we need
  sharp piecewise/core-offcore majorant.

## Existing modules you should reuse

1) Majorant/integral bridge (compiled):
- `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/ArchHeatMajorant.lean`
- `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatArchPiecewiseKernel.lean`

2) Digamma shift-series identities (compiled):
- `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatDigammaShift.lean`
- available lemmas:
  - `re_digamma_quarter_shift`
  - `a_eq_a0_sub_shift_series`
  - `a_star_eq_a_star0_sub_shift_series`
  - `a_star_le_a_star_zero`

## What is missing (please fill exactly)

Provide either:

1) complete checker-free proof replacing legacy axiom, or
2) minimal decomposition with exact Lean statements + proof skeletons.

If decomposition:

- **A. Pointwise majorant theorem** on `Icc (-Bmax) Bmax`:
  explicit `core/offcore` majorant for `|a_star|` sharp enough for the tight
  constant `1.360378581976`.
- **B. Integral bound theorem** for that majorant, compatible with
  `ArchHeatMajorant` bridge lemmas.
- **C. Final assembly theorem** that can directly replace
  `prime_heat_bounds_arch_data_from_data_legacy_axiom` in
  `BrangeHeatCert_2026_01_28.lean`.

## Concrete questions for deep analysis

1. Which explicit core bound for `|a_star ξ|` (formula + interval partition)
   is sharp enough to pass the fixed constant?
2. Which off-core bound should be used in Lean (erf-free vs erf-based), and why?
3. Confirm normalization and exponent factor in target integrand:
   `a_star` and `exp(-4*pi^2*t_critical*ξ^2)` (no factor mismatch).
4. If one-shot closure is too large:
   what is the smallest intermediate theorem that should be merged first?

## Acceptance criteria (must pass)

After integration, the result must satisfy all:

1. `lake env lean /mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
2. `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28`
3. `#print axioms Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`
   must NOT include `prime_heat_bounds_arch_data_from_data_legacy_axiom`
   and must NOT introduce any new project-specific axioms.

## Non-goals in this request

- Do not work on bucket checker closure here.
- Do not edit prime-sum/bucket certificate constants.
- Do not change `prime_cert_L_arch_heat_raw`.
