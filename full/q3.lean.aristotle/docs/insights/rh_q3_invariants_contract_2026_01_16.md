# RH_Q3 invariants contract and drift checks (2026-01-16)

Source: RH_Q3.pdf (2026-01-01), "Operator Methods for the Weil Criterion: Q3".

## What drifts in Lean (symptoms)
- A3 bridge mentions `a_star` or `ToeplitzMatrix ... a_star`.
- Toeplitz in the A3 chain is defined by sampling `P (π(i-j)/M)`.
- `a_star_pos` is used as a proxy for a Rayleigh floor.
- `t_sym` is reused as `t_rkhs` or vice versa.
- `w_Q` and `w_RKHS` are treated as the same weight.
- Direct-indexed Gaussian `T_P` is used as the uniform A3 object.

## Contract A-E (minimal)
A) Torus/Fourier basis: period-1, `e^{2πikθ}`.
B) A3 symbol: `P_A` is the periodized, windowed `a(ξ)Φ_{B,t}`; floor is `P_A ≥ c_*`.
C) Toeplitz: use Fourier/Rayleigh definition; sampling Toeplitz is not allowed in A3 chain.
D) Prime operator: compression/rank-one sum `T_P^{(M)}` with `w_Q`, not direct-indexed Gaussian.
E) Parameters: keep `t_sym` (symbol) and `t_rkhs` (cap) distinct; `w_Q` and `w_RKHS` are not interchangeable.

## Implications
- Rayleigh route yields `λ_min(T_M[P_A]) ≥ min P_A` for any M; SB is optional.
- `a_star_pos` is not required for A3 and can mislead.

## Quick test
- If a file contains `ToeplitzMatrix ... a_star` or `P (π(i-j)/M)` in the A3 chain, it is off the RH_Q3 contract.
