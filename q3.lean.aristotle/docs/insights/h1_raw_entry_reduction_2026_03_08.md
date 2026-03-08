# H1 raw-entry reduction (2026-03-08)

## Status

Active refinement of the symmetric two-sided filtered Suzuki bridge.

This note does not change the public theorem stack
`H1^f -> H2^f -> H3^f -> H4^f`.
It now records the raw diagnostic layer and the reason the raw theorem target
fails.

## Frozen notation

- Proshka-facing exact raw finite operator:
  `Q_M^{raw}:=T_M[P_A]-\Pi_M`,
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`
- exact raw Section 8 entries:
  `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle=
   A_{r-s}-\sum_{|\xi_n|\le B}\lambda_n e^{2\pi i(s-r)\xi_n}`
  with
  `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`
- raw Suzuki/Weil entries:
  `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})`
- filtered finite section:
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`
- filtered Suzuki blocks:
  `M_{mn}^{\sigma\tau}(a)=\langle G_g[a]\phi_n^\sigma[a],\phi_m^\tau[a]\rangle`

## Raw diagnostic layer

The raw-compressed Section 8 layer is still worth freezing explicitly:

- `Q_M^{raw}=T_M[P_A]-\Pi_M`,
- `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
- `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle=
   A_{r-s}-\sum_{|\xi_n|\le B}\lambda_n e^{2\pi i(s-r)\xi_n}`,
- `\kappa_{A3}=1`.

But the exact raw identity
`w_{rs}(a)=\kappa(a)q_{rs}`
is no longer the active theorem target.

## Normalization caveat now frozen

The old A3 files do not directly hand us one already-named raw matrix object.
They give the normalized block `T_P^{Ray}(t,M)` together with the compression
identity
`\iota_M^*T_P^{Ray}(t)\iota_M=(2M+1)T_P^{Ray}(t,M)`.

So the good hack is to stop asking the bridge to work with the normalized prime
compression and instead freeze the raw operator
`Q_M^{raw}=T_M[P_A]-\Pi_M`, where
`\Pi_M=(2M+1)T_P^{Ray}(t,M)`.

With that choice the exact entries become stable in `M` as soon as
`|r|,|s|\le M`, and the A3 calibration fixes `\kappa_{A3}=1`. That is the
package Proshka actually wants.

## Why the raw theorem target fails

The raw Q3 matrix is Toeplitz:

- `q_{rs}=q(r-s)`,
- in particular the diagonal `q_{rr}` is constant.

The raw Suzuki/Weil matrix in the basis `\chi_n[a]` is not Toeplitz and has
logarithmically growing diagonal:

- `w_{nn}(a)\sim \log|n|`.

So no scalar `\kappa(a)` can make
`w_{rs}(a)=\kappa(a)q_{rs}`
hold on the bulk. This is a structural mismatch, not a sign or scaling bug.

## Active bulk target

The narrowest active theorem target is now:

- prove the direct filtered bulk identities
  `M_{mn}^{++}(a)=\kappa(a)\widetilde q_{mn}^{++}`
  and
  `M_{mn}^{+-}(a)=\kappa(a)\widetilde q_{mn}^{+-}`;
- then recover the remaining filtered blocks
  `(-+), (--)`
  formally by Hermitian symmetry.

## Symmetry reduction

Because
`\phi_n^-=\overline{\phi_n^+}`
and `G_g[a]` is self-adjoint with Hermitian kernel,

- `M_{mn}^{--}(a)=\overline{M_{nm}^{++}(a)}`
- `M_{mn}^{-+}(a)=\overline{M_{nm}^{+-}(a)}`

Assuming the same Hermitian normalization on the Q3 side,

- `\widetilde q_{mn}^{--}=\overline{\widetilde q_{nm}^{++}}`
- `\widetilde q_{mn}^{-+}=\overline{\widetilde q_{nm}^{+-}}`

So only the `(+,+)` and `(+,-)` filtered families must be matched independently.

## Remaining brick after bulk

After the filtered bulk identities are matched, the only other live H-bridge problem is
the finite-dimensional Suzuki cap:

- define `A_a^{cap}`
- write its finite Hermitian matrix `H_a^{cap}`
- prove cap positivity separately

## Non-goals

- no return to the one-sided `\Delta_+` bridge
- no return to the coarse `1/4`-loss transfer as the preferred argument
- no promotion of semilocal machinery beyond engineering support for `H1^f`
