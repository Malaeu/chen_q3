# Proshka Request: prime-term cap at t_critical (single-scale)
Timestamp: 2026-01-25 15:22

## Context
- We are in the **single-scale** branch: `t_critical = 3/20`, `t0_critical = 1/(16π² t_critical)`.
- File: `Q3/Proofs/Q_nonneg_t_critical.lean`
- Lemma with `sorry`:

```lean
lemma prime_term_le_at_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) := by
  -- TODO
```

This lemma feeds:
```lean
Q_phi_shift_nonneg_t_critical
```
which uses `prime_term_le_at_t_critical` to conclude `Q ≥ 0`.

## Task
Provide a **Lean-ready proof** (or minimal lemma decomposition) to replace the `sorry` in
`prime_term_le_at_t_critical`.

## Constraints
- **Single-scale only**: use `t_critical`, not `t_sym` or `t_rkhs_cap` bridges.
- Allow general `K, B, τ` with `|τ| + B ≤ K`.
- No `sorry` / no `exact?`.
- If a helper lemma is required, keep it minimal (1–2 helpers).

## Hints / existing tools
- `phi_shift_critical B τ ξ := phi_shift B t_critical τ ξ`.
- `prime_term` and `arch_term` are in `Q3/Basic/Defs.lean`.
- You can reduce `prime_term` to a finite node sum using:
  `Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift` (if needed),
  but keep single-scale.
- There are weight-sum bounds in `Q3/Proofs/RKHS_cap_rayleigh.lean` for `t_rkhs_cap`.
  If you need a `rho_oneK`-style bound for `t_critical`, say explicitly and propose
  the smallest new lemma/definition to add.
- Existing nonnegativity facts:
  `fejer_heat_window_nonneg` and `phi_shift` nonnegativity.

## Deliverable
A Lean proof (or minimal lemma set + patch plan) that closes
`prime_term_le_at_t_critical` in `Q3/Proofs/Q_nonneg_t_critical.lean`.
