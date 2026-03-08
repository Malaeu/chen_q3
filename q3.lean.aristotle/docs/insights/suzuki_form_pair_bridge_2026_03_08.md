# Suzuki generalized form-pair bridge (2026-03-08)

## Claim

The fastest new operator-theoretic pivot is not a fresh cone theorem and not a
new compact symbol route. It is a bridge from the already-proved finite Q3
Hermitian energy

`T_M[P_A] - T_P^{(M)}`

to Suzuki's RH-equivalent operator criterion

`0 \notin \sigma_p(G_g[a])` for every `a > 0`.

## Main correction

The naive package

- finite sections converge in raw operator norm,
- a uniform plain-`L^2` gap survives,
- therefore `0` stays away from the spectrum of `G_g[a]`

is structurally wrong for a compact / trace-class target operator.

The honest bridge must instead use a generalized form pair

`(G_g[a], J_a)`

with

- finite-dimensional subspaces `E_{a,M} \subset L^2(-a,a)`,
- synthesis/intertwining maps `S_{a,M}: P_M -> E_{a,M}`,
- a positive injective Gram / metric operator `J_a`,
- and a scalar `\kappa(a) > 0`.

## Frozen theorem package

The audited theorem stack is:

- `H1`: exact or asymptotic pair-intertwining
  `S_{a,M}^* G_g[a] S_{a,M} = \kappa(a)(T_M[P_A]-T_P^{(M)}) + R_{a,M}`
  together with
  `S_{a,M}^* J_a S_{a,M} = I`;
- `H2`: Galerkin / recovery theorem on the generalized pair;
- `H3`: gap transfer from the finite Q3 block to `\ker G_g[a] = {0}`;
- `H4`: RH from Suzuki Theorem 1.4.

## Why this route is attractive

- It reuses the strongest existing Q3 asset directly:
  the finite Hermitian block `T_M[P_A]-T_P^{(M)}`.
- It bypasses A1'/A2/T5 as primary architectural load-bearing steps.
- It lands on an external RH-equivalent criterion already in the literature.

## Honest blocker

The missing brick is `H1`, not `H3`.

Until `S_{a,M}` and `J_a` are concretely constructed, the Suzuki route remains
an audited alternative operator pivot, not the public mainline.

## Recommendation

Keep the scalar compact route `S1/S2/S3/S4` as the public mainline, but freeze
the Suzuki generalized form-pair bridge as the leading alternative operator
pivot under audit.
