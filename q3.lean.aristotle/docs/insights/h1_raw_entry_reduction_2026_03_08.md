# H1 raw-entry reduction (2026-03-08)

## Status

Active refinement of the symmetric two-sided filtered Suzuki bridge.

This note does not change the public theorem stack
`H1^f -> H2^f -> H3^f -> H4^f`.
It narrows the live bulk blocker inside `H1^f`.

## Frozen notation

- exact normalized raw Section 8 entries:
  `q_{rs}^{(L)}=\langle Q_L e_s,e_r\rangle=a_{r-s}-p_{r-s}^{(L)}`
  with
  `p_k^{(L)}=(2L+1)^{-1}\sum w(n)\Phi_{B,t}(\xi_n)e^{-2\pi i k\xi_n}`
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
  on the two raw bulk families `(+,+)` and `(+,-)`,
  with the ambient shorthand `q_{rs}=q_{rs}^{(M+1)}` in the filtered bridge;
- then recover the filtered four-block equalities
  `(++), (+-), (-+), (--)`
  formally by applying the two-sided filter `\Delta_{M,N}` and the Hermitian
  symmetry on both sides.

## Normalization caveat now frozen

The old A3 files do not give a single `L`-independent global raw matrix whose
finite sections are the normalized Section 8 blocks. The factor
`(2L+1)^{-1}` on the prime side is forced by
`\iota_L^*T_P^{Ray}(t)\iota_L=(2L+1)T_P^{Ray}(t,L)`.

So the honest raw notation in the bridge is `L`-local:
- `Q_L=T_L[P_A]-T_P^{(L)}`
- `q_{rs}^{(L)}=\langle Q_L e_s,e_r\rangle`

This resolves the previous ambiguity in the shorthand `q_{rs}` used by the H1
layer.

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
