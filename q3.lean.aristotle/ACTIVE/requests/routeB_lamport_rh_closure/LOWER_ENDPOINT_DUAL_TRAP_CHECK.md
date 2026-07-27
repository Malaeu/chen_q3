# LOWER ENDPOINT DUAL/TRAPEZOID CHECK

`MU_INDEX_OR_SIGN_MISMATCH`

Diagnostic only; not a theorem and not RH.

The mandatory K1 Fourier-backend guard is evaluated before the lower-endpoint judge. A failed guard forbids using backend B in the residual, so no dual/trapezoid difference is manufactured.

## m = 13

- `lambda = 3.605551275463989`
- K1 guard: `FAIL`
- Dual Fejer at `lambda^-1`: `SKIPPED_BY_K1_GUARD`
- Comparison with `sqrt(lambda)*TrapError`: `NOT_FORMED`
- Backend B used in lower-endpoint residual: `false`

## m = 53

- `lambda = 7.280109889280518`
- K1 guard: `FAIL`
- Dual Fejer at `lambda^-1`: `SKIPPED_BY_K1_GUARD`
- Comparison with `sqrt(lambda)*TrapError`: `NOT_FORMED`
- Backend B used in lower-endpoint residual: `false`

## m = 257

- `lambda = 16.0312195418814`
- K1 guard: `FAIL`
- Dual Fejer at `lambda^-1`: `SKIPPED_BY_K1_GUARD`
- Comparison with `sqrt(lambda)*TrapError`: `NOT_FORMED`
- Backend B used in lower-endpoint residual: `false`

## Plants

- P1: executed at the zero-mass check; flipping `mu4` produces a material nonzero canonical transform.
- P2: the counterterm-removal shift identity is checked algebraically at `u=lambda^-1,1,lambda`.
- P3: the erroneous dual half-weight shift is evaluated from backend-A `hat_htrial(lambda)` at the affected endpoint teeth; no backend-B residual is formed.
- P4: the zero-extended replacement is compared with backend-A values at all three outside rows.

STATE was not changed. Bus 010 remains void.
