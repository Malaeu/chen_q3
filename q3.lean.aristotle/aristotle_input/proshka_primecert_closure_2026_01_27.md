# Proshka Request: PrimeCert closure architecture (t_critical, tau = 0)
Timestamp: 2026-01-27

## Context (where we are stuck)
- Main chain axiom deps (besides standard + `Weil_criterion_tau0`) are exactly two PrimeCert axioms in:
  - `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`:
    - `prime_b_grid_val_le_margin` (L19)
    - `prime_margin_Lipschitz_on_Brange` (L25)
- Single-scale only: `t_critical = 3/20`, `tau = 0`, and `B ∈ [B_min, B_max]`.
- Constants:
  - `B_min = 3` in `Q3/Proofs/A3_Floor_Bounds.lean`
  - `B_max = prime_cert_B_max = 4.9`, `h = prime_cert_B_h = 0.1`,
    `margin_lb = prime_cert_margin_lb = 0.499`, `L_ub = prime_cert_L_ub = 0.3`
    in `Q3/Proofs/PrimeCert/Defs.lean`
  - Grid values table (20 points, rounded down to 12 decimals) in
    `Q3/Proofs/PrimeCert/BrangeGrid_2046.lean`
    together with the already-proved slack lemma
    `prime_b_grid_val_ge_lb_with_slack`.
- Evidence file pinned (source + sha256) in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`:
  `output/prime_cert_brange_tcritical_2026-01-26_0050.txt`.

## Exact targets (Lean statements)
Let `φ_B(ξ) := phi_shift B t_critical 0 ξ` and `margin(B) := arch_term φ_B - prime_term φ_B`.

1) **Grid-point lower bounds (axiom #1)**:
```lean
∀ i : Fin prime_b_grid_size,
  prime_b_grid_val i ≤
    arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) -
      prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ)
```

2) **Lipschitz in B (axiom #2)**:
```lean
∀ x y,
  x ∈ Set.Icc B_min prime_cert_B_max →
  y ∈ Set.Icc B_min prime_cert_B_max →
  |margin x - margin y| ≤ prime_cert_L_ub * |x - y|
```

## What we already have (important)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean` proves a *symbolic* Lipschitz bound:
  ```lean
  |margin B1 - margin B2| ≤ margin_Lipschitz_const * |B1 - B2|
  ```
  with
  ```lean
  margin_Lipschitz_const :=
    (2 * B_max * M_a_local B_max + W_sum_local B_max) * (B_max / B_min^2)
  ```
  (`M_a_local`, `W_sum_local` come from `Q3/Proofs/Q_Lipschitz.lean`).
- We do **not** have a certified numeric bound showing
  `margin_Lipschitz_const ≤ 0.3` (this is the current concrete bottleneck for axiom #2).

## The real question (architecture decision)
PrimeCert is a *numerical certificate* problem: `arch_term` is an integral, `prime_term` is an infinite `tsum`
(`Q3/Basic/Defs.lean`), so “just prove it with tactics” won’t work without a checker/bridge.

We need your recommendation for the **minimal audit-resistant architecture** to eliminate both axioms:

### Option A (preferred): build a Lean-side verifier
What is the smallest set of analytic lemmas that lets us reduce both axioms to checking a finite list of rational/interval inequalities?
- For axiom #2: how do we best bound `M_a_local(4.9)` and `W_sum_local(4.9)` (or avoid them entirely)?
- For axiom #1: what exact decomposition do we certify at each grid point
  (arch integral truncation + tail bound, prime sum truncation + tail bound, etc.)?
Please propose the *exact lemma chain* (Lean statements) and where they should live.

### Option B (fallback): keep certificate-backed axioms longer
If full verifier is too heavy: what’s the cleanest way to keep them as assumptions while staying honest/auditable
(e.g. “axiom gated by sha256 + external checker”) without polluting the main chain?

## Constraints (must follow)
- Single-scale only: use `t_critical`, `tau = 0`.
- No two-scale bridges, no RKHS, no changing the overall Q3 strategy.
- No new axioms in the “Option A” closure plan.
- Prefer a *small targeted* lemma list (2–6 key lemmas), no “big rewrite”.

## Deliverable
- A short decision tree (Option A vs B) and, for Option A, a Lean-ready lemma decomposition
  that would let us actually implement the checker and delete the two axioms.
