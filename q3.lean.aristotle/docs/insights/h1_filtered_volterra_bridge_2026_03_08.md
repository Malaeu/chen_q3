# H1 Filtered Volterra Bridge (2026-03-08)

Status: preferred first-pass H1 candidate.

## Core idea

Do not force the Suzuki bridge into the too-rigid shape

`S_{a,M}^* J_a S_{a,M} = I`.

Instead use the natural Volterra metric already suggested by Suzuki:

`(I_0^{(a)}\phi)(t) := \int_{-a}^t \phi(u)\,du`,

`J_a := (I_0^{(a)})^* I_0^{(a)}`.

Then define the filtered synthesis by

`I_0^{(a)} S_{a,M} = U_a M_{1+z}|_{P_M}`,

where `U_a` is the scaled Fourier unitary and `M_{1+z}` is multiplication by
`1+z` on `L^2(\mathbb T)`.

## Exact pullback metric

With this choice the pullback metric is explicit:

`B_M := S_{a,M}^* J_a S_{a,M} = T_M[|1+z|^2] = T_M[2+z+z^{-1}]`.

Hence

`0 <= B_M <= 4 I`.

So any existing Q3 bulk bound

`Q_M := T_M[P_A] - T_P^{(M)} >= c(a) I`

automatically yields

`Q_M >= (c(a)/4) B_M`.

## Real remaining target

The right next theorem is therefore not raw `H3`, but exact or almost-exact
matrix comparison on the filtered basis:

`S_{a,M}^* G_g[a] S_{a,M} = \kappa(a) Q_M + F_{a,M}`,

where `F_{a,M}` should ideally be zero or at worst an explicit finite-rank cap
correction on low modes.

## Verdict

- best use: preferred first-pass H1 realization;
- semilocal packets remain useful as a secondary basis/Gram refinement;
- next honest subproblem: compute
  `[<G_g[a]\chi_{n,n+1}[a], \chi_{m,m+1}[a]>]`
  and isolate exact bulk plus finite-rank cap.
