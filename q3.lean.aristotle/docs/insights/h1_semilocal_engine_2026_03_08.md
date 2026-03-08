# H1 Semilocal Engine (2026-03-08)

Status: in progress engineering layer, not a new RH endgame.

## Role

Use the finite-prime semilocal Connes--Consani--Moscovici machinery only as a
canonical basis / Gram engine for the Suzuki/Yoshida bridge `H1`.

This note does **not** replace the public mainline. The live public route
remains

`T0-pd -> H-bridge -> H4 -> RH`

with

`H-bridge = H1 -> H2 -> H3 -> H4`.

## Engineering target

Fix a finite prime window

`S(B) = { p : p <= exp(2π B) }`

matching the active prime scale of the Q3 finite block.

Let

`\eta_m^{(S,a)} ⊂ L^2(-a,a)`

be the packet states supplied by the semilocal cyclic/Jacobi machinery at that
finite level. Define

`E_{a,M}^{(S)} = span{ \eta_m^{(S,a)} : 0 <= m <= M }`.

Use raw synthesis

`S_{a,M}^{(S)} e_m := \eta_m^{(S,a)}`

and semilocal Gram matrix

`\Gamma_{a,M}^{(S)} = [ <\eta_i^{(S,a)}, \eta_j^{(S,a)}> ]_{0<=i,j<=M}`.

There are then two equivalent normalizations:

- raw metric:
  `J_a^{(S,M)} := \Gamma_{a,M}^{(S),-1}`;
- normalized synthesis:
  `\widetilde S_{a,M}^{(S)} := S_{a,M}^{(S)} \Gamma_{a,M}^{(S),-1/2}`.

## Reduced H1 statement

The semilocal-assisted bridge should target the matrix comparison

`(\widetilde S_{a,M}^{(S)})^* G_g[a] \widetilde S_{a,M}^{(S)}
 = \kappa_{S,a}(T_M[P_A] - T_P^{(M)}) + R_{S,a,M}`.

So the real next theorem task is still `H1`, now reduced to exact or asymptotic
matching of matrix elements on a canonical finite-prime packet basis.

## Verdict

- good use: finite-prime packet basis, Gram metric, matrix comparison;
- bad use: promoting the semilocal layer itself to the final RH endgame;
- recommended next step: compute the first Archimedean Toeplitz coefficients and
  prime Gram vectors in the semilocal packet basis and compare them directly to
  `T_M[P_A] - T_P^{(M)}`.
