# Proshka Request: PrimeCert analytic Lipschitz closure (t_critical, tau = 0)
Timestamp: 2026-01-26 15:47

## Context
- Single-scale mainline: `t_critical = 3/20`, `tau = 0`, `B ∈ [B_min, B_max]` with `B_min = 3`, `B_max = 4.9`.
- Current axioms live in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`:
  `prime_b_grid_val_le_margin`, `prime_margin_Lipschitz_on_Brange`.
- Numeric evidence: `output/prime_cert_brange_tcritical_2026-01-26_0050.txt`
  (sha256 pinned + checked in `scripts/check_axioms.sh`).
- Goal: replace those two axioms by **analytic proofs** (Option A).

## Targets (Lean statements)
Let `φ_B(ξ) := phi_shift B t_critical 0 ξ` and
`margin(B) := arch_term φ_B - prime_term φ_B`.

1) **Lipschitz in B** on the certified range:
```
∀ x y, x ∈ Icc B_min B_max → y ∈ Icc B_min B_max →
  |margin x - margin y| ≤ L * |x - y|
```
with **explicit** `L ≤ 3/10` (`prime_cert_L_ub` in `PrimeCert/Defs.lean`).

2) **Grid lower bounds**:
```
∀ i : Fin prime_b_grid_size, prime_b_grid_val i ≤ margin (prime_b_grid i)
```
or propose a *replacement strategy* (e.g. monotonicity in `B`) that reduces
this to checking only endpoints.

## Hints / existing tools
- `phi_shift` definition + support lemmas: `Q3/Proofs/ShiftedWindows.lean`.
- Arch/prime Lipschitz bounds (sup-norm input):
  `Q3/Proofs/Q_Lipschitz_arch_bridge.lean`,
  `Q3/Proofs/Q_Lipschitz_prime_bridge.lean`.
- Mathlib: `abs_max_sub_max_le_max` (or `lipschitzWith_max`) for
  `max(0, ·)` being 1‑Lipschitz.
- For `f_B(x) = max(0, 1 - |x|/B)`:
  `|f_B1(x) - f_B2(x)| ≤ |x| * |B1-B2| / (B_min^2)` on `|x| ≤ B_max`
  (or a better bound).

## Constraints (important)
- **Single-scale only**: use `t_critical`, `tau = 0`.
- **No two-scale** (`t_sym`, `t_rkhs_cap`) and **no RKHS**.
- **No new axioms**.
- Use `a_star` only inside `arch_term` integrals; do not use it as A3 floor.
- Provide Lean‑ready statements or minimal lemma decomposition (no `sorry`/`exact?`).

## Deliverable
- A minimal lemma chain (Lean statements + proof outline) to close
  `prime_margin_Lipschitz_on_Brange` and `prime_b_grid_val_le_margin`.
- If full analytic closure is too heavy, propose the **smallest** subproblem
  that advances us (e.g., monotonicity in `B`, endpoint reduction, or a clean
  bound on `sup |φ_B1 - φ_B2|` with explicit constants).
