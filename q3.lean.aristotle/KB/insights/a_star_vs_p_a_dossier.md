---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# a_star vs P_A dossier (Rayleigh/A3)

Short: a_star has no global floor; A3 floor lives on P_A; Toeplitz in Rayleigh must be the Fourier-coefficient Toeplitz, not the sampling matrix.

## Claim check (asymptotic)

- a_star(xi) = 2*pi*(log pi - Re psi(1/4 + i*pi*xi)).
- Re psi(z) ~ log|z| as |z| -> inf in a fixed sector.
- So a_star(xi) ~ -2*pi*log|xi| -> -inf.
- Conclusion: any global axiom like a_star_pos (a_star >= c_star for all xi) is false.

## Symbol mismatch

- P_A(B,t,theta) = 2*pi * sum_{m in Z} a(theta+m) * w_{B,t}(theta+m).
- A3_FLOOR gives P_A(theta) >= c_star on T = [-1/2, 1/2].
- That floor does not transfer to a_star samples without extra theory.

## Toeplitz mismatch

Two different objects:

1) Fourier Toeplitz
   (T_M[P])_{ij} = P_hat(i-j),
   P_hat(k) = integral_{-1/2}^{1/2} P(theta) * e^{-2*pi*i*k*theta} d theta.
   Rayleigh lower bound applies here.

2) Sampling Toeplitz
   (T_sample)_{ij} = P(pi*(i-j)/M).
   No direct floor transfer from P_A without a sampling-to-Fourier bridge.

## Consequence for A3

- A3 Rayleigh piece should be stated for T_M[P_A], not ToeplitzMatrix(a_star).
- Keep a_star only for analytic lemmas (continuity, bounds on compact sets), not for floors.

## Wiring checklist

- Replace any use of a_star_pos in the Rayleigh chain with P_A_ge_c_star.
- Use the Fourier Toeplitz Rayleigh lemma (rayleigh_v1.lean).
- Subtract RKHS cap bound (weight_sum_le_rho_one / RKHS_cap_rayleigh.lean).
- Recheck parameter split: t_sym vs t_rkhs.

## File pointers

- full/q3.lean.aristotle/Q3/Axioms.lean (a_star_pos, A3_bridge_axiom)
- full/q3.lean.aristotle/Q3/Proofs/Rayleigh_utils.lean (Rayleigh helper)
- full/q3.lean.aristotle/aristotle_output/rayleigh_v1.lean (Fourier Toeplitz Rayleigh)
- full/q3.lean.aristotle/Q3/Proofs/RKHS_cap_rayleigh.lean (cap bound)
- full/q3.lean.aristotle/Q3/Basic/Defs.lean (P_A, T_P_comp)
