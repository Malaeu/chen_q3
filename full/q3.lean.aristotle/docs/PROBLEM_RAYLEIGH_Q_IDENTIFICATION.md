# Resolved: Rayleigh-Q identification normalization + periodization

## What was broken

- With normalized prime_vec, evaluation satisfies
  <p, v_n> = p(xi_n) / sqrt(2M+1) (up to sign/conjugation).
  So the prime contribution in the quadratic form is
  (1/(2M+1)) * sum w(n) * |p(xi_n)|^2.
- The statement
  (2M+1) * RQ(Toeplitz - T_P_comp, basis0) = Q(Phi)
  multiplies the arch part, so it is false under the current normalization.

## What we proved

- Correct Rayleigh identification with uniform-in-M architecture:
  - arch term stays unscaled,
  - prime term carries the correct coefficient,
  - no operator scaling by (2M+1),
  - no shift to Q_M.
- Periodization identity:
  integral_{-1/2}^{1/2} P_A(B,t,theta) dtheta
    = arch_term(fejer_heat_window B t).

## Lean touchpoints (verified)

- File: `Q3/Proofs/Rayleigh_Q_identification.lean`
- `integral_P_A_eq_arch_term` is proven (no sorry).
- `rayleigh_Q_eq_Q` is proven and ready for wiring into the atoms chain.

## Constraints / invariants (still in force)

- Keep uniform-in-M architecture (no (2M+1) scaling in the operator).
- Keep prime_vec normalized (otherwise RKHS cap becomes M-dependent).
- Avoid introducing Q_M into the main chain.

## Next action

- Wire `rayleigh_Q_eq_Q` into the atoms-positivity chain to replace
  `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`.
