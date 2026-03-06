# Sub-agent request: close `Weil_criterion_tau0` (Tier-1 axiom)

## Goal
Replace the axiom in:

- `Q3/Axioms.lean`

```lean
axiom Weil_criterion_tau0 (t0 B_min B_max : ℝ) :
  (∀ Φ ∈ Weil_cone_tau0 t0 B_min B_max, Q Φ ≥ 0) ↔ RH
```

with a theorem, preferably derived from existing structures and already-defined `Weil_cone`/`W_K` framework.

## Exact target statement

```lean
theorem Weil_criterion_tau0 (t0 B_min B_max : ℝ) :
  (∀ Φ ∈ Weil_cone_tau0 t0 B_min B_max, Q Φ ≥ 0) ↔ RH := by
  -- no sorry/exact?/admit
```

## Available context (already in repo)

- `Q3/Axioms.lean`
  - definitions: `W_K`, `W_K_tau0`, `Weil_cone`, `Weil_cone_tau0`
  - axiom: `Weil_criterion : (∀ Φ ∈ Weil_cone, Q Φ ≥ 0) ↔ RH`
- `Q3/Main.lean`
  - uses `Weil_criterion_tau0 t0_critical B_min prime_cert_B_max`

## Preferred strategy

1. Prove structural relation between `Weil_cone_tau0 t0 B_min B_max` and `Weil_cone`.
2. Use that relation with `Weil_criterion` only if logically sufficient.
3. If full equivalence is not derivable from current definitions, return:
   - the strongest theorem derivable now (explicit statement),
   - a minimal list of additional lemmas needed for the full iff closure.

## Constraints

- No `sorry`, no `exact?`, no `admit`.
- No changes to public theorem names used by `Q3/Main.lean`.
- Keep imports in active Q3 only (exclude `Q3/Archive`, `Q3/Clean`).
- Prefer explicit, auditable proof steps.

## Deliverable

Lean patch for active files plus a short note on whether full `↔` was achieved or which missing lemma blocks it.
