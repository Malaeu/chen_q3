# Problem: Rayleigh-Q identification normalization + periodization

## What is broken

- With normalized prime_vec, evaluation satisfies
  <p, v_n> = p(xi_n) / sqrt(2M+1) (up to sign/conjugation).
  So the prime contribution in the quadratic form is
  (1/(2M+1)) * sum w(n) * |p(xi_n)|^2.
- The statement
  (2M+1) * RQ(Toeplitz - T_P_comp, basis0) = Q(Phi)
  multiplies the arch part, so it is false under the current normalization.
- Therefore the bridge "Rayleigh pairing => Q(Phi)" breaks.
  If we keep the factor, we land in Q_M (M-dependent), not in T0's Q.

## What we must prove

- A correct Rayleigh identification that yields Q(Phi) with uniform-in-M
  architecture:
  - arch term stays unscaled,
  - prime term carries the correct coefficient,
  - no operator scaling by (2M+1),
  - no shift to Q_M.
- A fast periodization identity:
  integral_{-1/2}^{1/2} P_A(B,t,theta) dtheta
    = arch_term(fejer_heat_window B t).

## Lean touchpoints

- File: Q3/Proofs/Rayleigh_Q_identification.lean
- Blocker: integral_P_A_eq_arch_term currently times out (dominated-convergence
  proof). Need a lighter proof (periodize lemmas or finite-sum on a fundamental
  domain).

## Constraints / invariants

- Keep uniform-in-M architecture (no (2M+1) scaling in the operator).
- Keep prime_vec normalized (otherwise RKHS cap becomes M-dependent).
- Avoid introducing Q_M into the main chain.

## Reported status (unverified; from sandbox log)

- Sandbox summary says the carleson TASK.md was expanded to cover the
  Rayleigh-Q identification framework.
- "Fixed" formula by moving (2M+1) to the prime piece:
  Q(Phi) = RQ(Toeplitz[P_A], basis0) - (2M+1) * RQ(T_P_comp, basis0).
- Claimed lemmas: prime_vec_i0_norm_sq, T_P_comp_real_diag,
  arch_rayleigh_eq, prime_rayleigh_eq, rayleigh_Q_identification.
- Added a periodization axiom for integral_P_A_eq_arch_term to bypass timeout.
- Claimed build passes and axiom count +1.
