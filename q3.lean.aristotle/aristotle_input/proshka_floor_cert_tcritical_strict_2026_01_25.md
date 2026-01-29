# Proshka STRICT: P_A floor certificate at t_critical

You already have the bundle context. Do NOT restate background, do NOT search externally, do NOT discuss RH status.

## Task
Close the `sorry` in:

```lean
-- file: Q3/Proofs/Q_nonneg_t_critical.lean
lemma P_A_ge_c_star_at_t_critical (θ : ℝ) :
    P_A_critical B_min θ ≥ c_star := by
  -- TODO
```

Either:

**Option A (preferred)**
Produce a lemma on `Icc (-1/2) (1/2)` and show how it implies the global statement by periodicity:

```lean
lemma P_A_ge_c_star_on_Icc_tcritical :
  ∀ θ ∈ Set.Icc (-1/2) (1/2), c_star ≤ P_A B_min t_critical θ := by
  -- certificate proof
```

**Option B (direct)**
Provide a direct Lean proof for `P_A_ge_c_star_at_t_critical`.

## Constraints
- Single-scale only: `t_critical`, `B_min`, τ = 0.
- No two-scale bridges, no `t_sym`.
- No `sorry`, no `exact?`.
- If numerical certificate is used, specify exactly the cert step (grid + modulus / interval arithmetic).
- Output: Lean-ready proof(s) + minimal helper lemmas (<= 3).

## Deliverable
Lean code (or patch-ready lemma list) that compiles against the current bundle.
