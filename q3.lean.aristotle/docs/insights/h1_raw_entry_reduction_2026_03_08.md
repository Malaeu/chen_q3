# H1 raw-entry reduction (2026-03-08)

## Status

Active refinement of the symmetric two-sided filtered Suzuki bridge.

This note does not change the public theorem stack
`H1^f -> H2^f -> H3^f -> H4^f`.
It narrows the live bulk blocker inside `H1^f`.

## Frozen notation

- raw Section 8 entries:
  `q_{rs}=\langle Q e_s,e_r\rangle`
- raw Suzuki/Weil entries:
  `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})`
- filtered finite section:
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`
- filtered Suzuki blocks:
  `M_{mn}^{\sigma\tau}(a)=\langle G_g[a]\phi_n^\sigma[a],\phi_m^\tau[a]\rangle`

## Active bulk target

The narrowest active theorem target is now:

- prove the raw identity
  `w_{rs}(a)=\kappa(a)q_{rs}`
  on the two raw bulk families `(+,+)` and `(+,-)`;
- then recover the filtered four-block equalities
  `(++), (+-), (-+), (--)`
  formally by applying the two-sided filter `\Delta_{M,N}` and the Hermitian
  symmetry on both sides.

## Symmetry reduction

Because
`\phi_n^-=\overline{\phi_n^+}`
and `G_g[a]` is self-adjoint with Hermitian kernel,

- `M_{mn}^{--}(a)=\overline{M_{nm}^{++}(a)}`
- `M_{mn}^{-+}(a)=\overline{M_{nm}^{+-}(a)}`

Assuming the same Hermitian normalization on the Q3 side,

- `\widetilde q_{mn}^{--}=\overline{\widetilde q_{nm}^{++}}`
- `\widetilde q_{mn}^{-+}=\overline{\widetilde q_{nm}^{+-}}`

So only the `(+,+)` and `(+,-)` raw families must be matched independently.

## Remaining brick after bulk

After the raw bulk identity is matched, the only other live H-bridge problem is
the finite-dimensional Suzuki cap:

- define `A_a^{cap}`
- write its finite Hermitian matrix `H_a^{cap}`
- prove cap positivity separately

## Non-goals

- no return to the one-sided `\Delta_+` bridge
- no return to the coarse `1/4`-loss transfer as the preferred argument
- no promotion of semilocal machinery beyond engineering support for `H1^f`
