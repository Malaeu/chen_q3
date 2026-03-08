# H1 candidate construction in RKHS/Gram language (2026-03-08)

## Claim

The cleanest first construction of the Suzuki/Yoshida bridge data is not raw
orthonormal Fourier restriction on `L^2(-a,a)`, but a nonorthogonal packet
synthesis extracted from the same centered Fejér×heat / RKHS geometry that
already produces the finite Q3 Hermitian block

`T_M[P_A] - T_P^{(M)}`.

## Candidate data

For fixed `a > 0`, choose packet states

`\varphi_{a,j} \in L^2(-a,a)`, `j in Z`,

and set

`E_{a,M} = span { \varphi_{a,j} : |j| <= M }`.

For

`p(\theta) = \sum_{|j|<=M} c_j e^{ij\theta} in P_M`

define the raw synthesis map

`S_{a,M} p := \sum_{|j|<=M} c_j \varphi_{a,j}`.

Let the packet Gram matrix be

`\Gamma_{a,M} = [ <\varphi_{a,i}, \varphi_{a,j}> ]_{|i|,|j|<=M}`.

Define `J_a` on the packet span by Gram pullback:

`< J_a S_{a,M} p, S_{a,M} q > := < p, q >_{L^2(T) }`.

Equivalently, in the packet basis `{ \varphi_{a,j} }` the matrix of
`J_a|_{E_{a,M}}` is `\Gamma_{a,M}^{-1}`.

Then

`S_{a,M}^* J_a S_{a,M} = I`

holds by construction.

## Reduced H1 target

With this choice, `H1` is reduced to one exact or asymptotic matrix-comparison
problem:

`[ < G_g[a]\varphi_{a,j}, \varphi_{a,k} > ]`
`= \kappa(a) ( T_M[P_A] - T_P^{(M)} ) + R_{a,M}`.

So the next blocker is no longer abstract operator language. It is the explicit
comparison between:

- the Suzuki kernel matrix on the packet basis,
- the Archimedean Toeplitz coefficients already encoded by `P_A`,
- the prime Gram vectors already encoded by `T_P^{(M)}`.

## Why this candidate is preferable

- It reuses the strongest existing Q3 object directly.
- It makes `J_a` unavoidable but natural: `J_a` is just the packet Gram metric.
- It avoids forcing a fake plain-`L^2` gap theorem onto a compact / trace-class
  operator.
- It turns `H1` into a concrete matrix-element comparison task.

## Honest status

This is not yet a theorem. It is the current best candidate construction for
the bridge data.

The next theorem-level task is:

1. define the packet basis `\varphi_{a,j}` concretely;
2. compute or estimate
   `[ < G_g[a]\varphi_{a,j}, \varphi_{a,k} > ]`;
3. identify the exact Archimedean Toeplitz and prime Gram terms that should
   appear on the Q3 side;
4. isolate the acceptable remainder `R_{a,M}`.
