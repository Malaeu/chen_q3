# H1 four-block bulk stack (2026-03-08)

## Status

Active refinement of the symmetric two-sided filtered Suzuki bridge.

This note does not change the public theorem stack
`H1^f -> H2^f -> H3^f -> H4^f`.
It freezes the filtered consequence layer inside `H1^f`.
The narrower live theorem target is now recorded separately in
`h1_raw_entry_reduction_2026_03_08.md`.
This note stays valid only as the filtered consequence layer after the direct
filtered bulk match on `(++),(+-)`.

## Frozen notation

- Suzuki-side entries:
  `M_{mn}^{\sigma\tau}(a)=\langle G_g[a]\phi_n^\sigma[a],\phi_m^\tau[a]\rangle`
- Q3-side entries:
  `(\widetilde Q_{M,N}^{\sigma\tau})_{mn}`
- tail packets:
  `\phi_n^+[a]=\chi_{n,n+1}[a]`,
  `\phi_n^-[a]=\chi_{-n,-(n+1)}[a]`
- antiderivative packets:
  `\psi_n^+[a]=\chi_n[a]+\chi_{n+1}[a]`,
  `\psi_n^-[a]=\chi_{-n}[a]+\chi_{-(n+1)}[a]`

## Exact bulk formulas

For every `\sigma,\tau\in\{+,-\}` and `N<n,m\le M`,

`M_{mn}^{\sigma\tau}(a)=W(\psi_n^\sigma[a]*\widetilde{\psi_m^\tau[a]})`.

The four blocks are therefore exact filtered bulk objects, not heuristic matrix
patterns. In Fourier variables they are expressed through

- `\widehat{\psi_n^+}(z)=(-1)^n\sqrt{2/a}\sin(az)\left((z+\pi n/a)^{-1}-(z+\pi(n+1)/a)^{-1}\right)`
- `\widehat{\psi_n^-}(z)=(-1)^n\sqrt{2/a}\sin(az)\left((z-\pi n/a)^{-1}-(z-\pi(n+1)/a)^{-1}\right)`

and

`M_{mn}^{\sigma\tau}(a)=\sum_\gamma \widehat{\psi_n^\sigma}(-\gamma)\widehat{\psi_m^\tau}(\gamma)`.

## Matching target

The filtered consequence layer is now:

- `M^{++}(a)` vs `\kappa(a)\widetilde Q_{M,N}^{++}`
- `M^{+-}(a)` vs `\kappa(a)\widetilde Q_{M,N}^{+-}`
- `M^{-+}(a)` vs `\kappa(a)\widetilde Q_{M,N}^{-+}`
- `M^{--}(a)` vs `\kappa(a)\widetilde Q_{M,N}^{--}`

The only acceptable normalization freedom is the common scalar `\kappa(a)`.
No extra section-boundary bookkeeping should remain inside the filtered bulk,
because the active Q3-side object is already
`\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`.
However, these four filtered equalities are no longer the narrowest active
frontier once the raw layer is demoted to a diagnostic mismatch lemma and the
direct filtered bulk match on `(++),(+-)` becomes the live target.

## Remaining brick after bulk

After the four blocks are matched, the only other live H-bridge problem is the
finite-dimensional Suzuki cap:

- define `A_a^{cap}`
- write its finite Hermitian matrix `H_a^{cap}`
- prove cap positivity separately

## Non-goals

- no return to the one-sided `\Delta_+` bridge
- no return to the coarse `1/4`-loss transfer as the preferred argument
- no promotion of semilocal machinery beyond engineering support for `H1^f`
