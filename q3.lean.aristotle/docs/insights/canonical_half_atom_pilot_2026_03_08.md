# Canonical Centered Half-Atom Pilot (2026-03-08)

## Claim

The canonical centered half-atom

\[
g_{\delta,t_0,0}(\xi)=\Lambda_\delta(\xi)\rho_{t_0}(\xi)
=\Bigl(1-\frac{|\xi|}{\delta}\Bigr)_+ e^{-4\pi^2 t_0\xi^2}
\]

is now the first explicit pilot packet for the corrected finite-dictionary
route.

## Why it matters

- It gives exact packet geometry:
  `R_g=\delta`, `R_h=2\delta`.
- It gives exact norms:
  `\|h\|_1=\|g\|_1^2`,
  `\|h\|_\infty=h(0)=\|g\|_2^2`.
- It gives a usable core-mass lower bound:
  `H_r\ge M_g(r/2)^2`.
- It gives the first nonvacuous sparse compact regime where the finite symbol
  criterion actually closes.

## Pilot compact

Take

- `K=0.2`,
- `J={0,1}`,
- `\Delta=0.15`.

Then the active positive nodes are only `\xi_2` and `\xi_3`, and

\[
\operatorname{dist}(0.15,\Xi_K)\approx 0.02485.
\]

Hence for `\delta<0.0124` one gets

\[
\beta_0=\beta_1=0.
\]

So the finite symbol reduces to

\[
S_J(\theta)\ge \alpha_0-2|\alpha_1|.
\]

Using the live Archimedean density,

\[
a^*(0)\approx 33.75,
\qquad
a^*(0.15)\approx 13.31,
\qquad
a^*(0)-2a^*(0.15)\approx 7.13>0.
\]

Therefore, for sufficiently small `\delta`, the modulus error in the
approximate-identity bound is dominated by this positive gap, so the sparse
dictionary closes.

## Verdict

- The corrected packet criterion is mathematically alive.
- The canonical half-atom gives the first concrete success case.
- This still does not prove dense closure; it only shows that the sparse
  finite-dictionary route is nonempty and worth pursuing.
