# Sub-agent request: close `prime_cert_margin_from_pathB` in active Path A/B gate

## Goal
Replace the axiom in:

- `Q3/Proofs/PrimeCert/PrimeCert_Margin_PathB.lean`

```lean
axiom prime_cert_margin_from_pathB : PrimeCertMarginOnBrange
```

with a theorem, while preserving the same exported name/signature.

## Exact target statement

```lean
theorem prime_cert_margin_from_pathB : PrimeCertMarginOnBrange := by
  -- no sorry/exact?/admit
```

## Context

- `Q3/Proofs/PrimeCert/PrimeCert_Margin_Spec.lean`
  - `PrimeCertMarginOnBrange` definition
- `Q3/Proofs/PrimeCert/PrimeCert_Margin_Gate.lean`
  - `prime_cert_margin_from_gate := prime_cert_margin_from_pathB`
  - this gate is now in active `Q3.Main` axiom chain
- `Q3/Proofs/Q_nonneg_t_critical.lean`
  - active `tau=0 Brange` path uses this gate
- `Q3/Proofs/RKHS_PrimeCap_Analytic.lean`
  - intended analytic Path B source

## Preferred strategy

1. Prove `PrimeCertMarginOnBrange` from existing analytic lemmas (Path B), not via heavy table imports.
2. Keep imports thin (no `Q3/Archive`, no `Q3/Clean`).
3. If a complete theorem is not derivable from current lemmas, return:
   - strongest theorem derivable now,
   - minimal additional lemma list needed to finish closure.

## Constraints

- No `sorry`, no `exact?`, no `admit`.
- Keep existing public API names unchanged.
- Do not introduce new axioms.

## Deliverable

A Lean patch that changes `prime_cert_margin_from_pathB` from `axiom` to `theorem` and compiles in active Q3 chain.
