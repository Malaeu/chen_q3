# Aristotle request: Rayleigh basis0 lower bound at t_critical

Goal: prove the single‑scale axiom
`rayleigh_basis0_shift_ge_cstar_quarter` in
`Q3/Proofs/SingleScale_Assumptions.lean`.

Target statement (exact):
```
axiom rayleigh_basis0_shift_ge_cstar_quarter
    (K B tau : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical tau))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4
```

Please produce a Lean theorem (no `sorry`, no `exact?`) that can replace it.

---

## Hints / context (existing lemmas)

1) Rayleigh basis0 identity (already in project):
```
Q3.Proofs.RayleighQId.rayleigh_basis0
```

2) Toeplitz diagonal lemma:
```
Q3.Proofs.RayleighQId.ToeplitzMatrix_Fourier_real_diag
```

3) Rayleigh identification for P_A_shift:
```
Q3.Proofs.RayleighQId.rayleigh_basis0_eq_arch_term
```
(see `Q3/Proofs/Rayleigh_Q_identification.lean`, uses continuity of `P_A_shift`)

4) Periodization identity:
```
Q3.Proofs.ShiftedWindows.integral_P_A_shift_eq_arch_term
```

5) Continuity for `P_A_shift` at t_critical:
```
Q3.Proofs.SingleScale.continuous_P_A_shift
```
(or reprove it locally)

6) A3 floor at t_critical should give the lower bound on the arch term.
If needed, you may use the lemma skeletons in
`Q3/Proofs/Q_nonneg_t_critical.lean` (e.g. `arch_term_ge_at_t_critical`).

---

## Suggested proof outline

- Reduce Rayleigh quotient to the diagonal term using `rayleigh_basis0`.
- Use Toeplitz diagonal lemma to rewrite to integral/arch term.
- Apply the lower bound on arch term at `t_critical`.
- Conclude `≥ c_star/4`.

Please output Lean code that compiles under Mathlib and uses existing project lemmas.
