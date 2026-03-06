# Sub-agent request: close `prime_term_le_at_t_critical_axiom` (active Q3 chain)

## Goal
Replace the axiom in:

- `Q3/Proofs/Q_nonneg_t_critical.lean`

```lean
axiom prime_term_le_at_t_critical_axiom (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ)
```

with a theorem (same signature) or a theorem that is strictly stronger and can be used to define this statement without axioms.

## Exact target statement

```lean
theorem prime_term_le_at_t_critical_axiom (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) := by
  -- prove without sorry/exact?/admit
```

## Available context (already in repo)

- `Q3/Proofs/Q_nonneg_t_critical.lean`
  - `prime_term_le_arch_term_on_Brange_tau0_of_margin`
  - `prime_term_le_arch_term_on_Brange_tau0`
  - constants: `B_min`, `prime_cert_B_max`, `prime_cert_margin_lb`
- `Q3/Proofs/PrimeCert/PrimeCert_Margin_Gate.lean`
  - gate theorem for certified Brange margin
- `Q3/Proofs/RKHS_PrimeCap_Analytic.lean`
  - analytic RKHS cap route used in Path B

## Preferred strategy

1. Use existing Brange/tau=0 margin theorem if possible.
2. If full `(K,B,τ)` is too strong with current assumptions, provide:
   - a theorem with minimal additional assumptions that is provable now,
   - plus a wrapper showing how to replace active mainline dependencies.
3. Keep proof architecture Path B compatible (analytic cap), no table/autogen imports.

## Constraints

- No `sorry`, no `exact?`, no `admit`.
- Keep public API stable where possible.
- Do not import `Q3/Archive` or `Q3/Clean`.
- Keep proof small and explicit (`simpa`, `linarith`, `nlinarith`, `calc`, `refine`).

## Deliverable

Return Lean code patch that compiles in the active project and removes dependence on this axiom from active Q3 chain.
