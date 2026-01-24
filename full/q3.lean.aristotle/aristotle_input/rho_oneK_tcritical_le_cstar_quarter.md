# Aristotle request: single‑scale prime cap at t_critical

Goal: prove the single‑scale axiom
`rho_oneK_tcritical_le_cstar_quarter` in
`Q3/Proofs/SingleScale_Assumptions.lean`.

Target statement (exact):
```
axiom rho_oneK_tcritical_le_cstar_quarter (K : ℝ) :
    Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K ≤ Q3.c_star / 4
```

Please produce a Lean theorem (no `sorry`, no `exact?`) that can replace it.

---

## Definitions

- `Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs` is defined in
  `Q3/Proofs/PrimeTerm_t_bridge.lean`:
```
exp_tcrit_to_rkhs K := Real.exp (16 * Real.pi^2 * (t_rkhs_cap - t_critical) * K^2)
```

- `Q3.Proofs.rho_oneK` is defined in
  `Q3/Proofs/RKHS_cap_rayleigh.lean`:
```
rho_oneK K := Real.exp (8 * Real.pi^2 * t_rkhs_cap * K^2) * rho_one
```

- `rho_one` is defined as `1/25` in
  `Q3/Proofs/A3_bridge_rayleigh_first.lean`.

---

## Hints / context

- `Q3.c_star = 11/10` (from `Q3.Axioms`).
- You may need a numerical bound on the product
  `exp_tcrit_to_rkhs K * rho_oneK K` at the allowed `K` range.
- If a supporting lemma already exists in the project, use it.

---

## Desired output

A Lean lemma of the form:
```
theorem rho_oneK_tcritical_le_cstar_quarter (K : ℝ) :
  Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K ≤ Q3.c_star / 4 := by
  -- proof
```

Please output Lean code that compiles under Mathlib and uses existing project lemmas.
