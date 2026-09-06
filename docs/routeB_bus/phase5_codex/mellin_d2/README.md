# Source-exact evaluator of the angle density d_S(xi)

Verdict: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06.md`,
sections 1-2, equations (1)-(18), 2.4, and (16)-(17).  Cutoff lambda = 1, physical half-line u in (0,1),
S = {inf} and S = {inf, 2}.

## Files

| file | what |
|---|---|
| `core.py` | `I(beta,xi)`, `J(beta,xi)` (closed form + exact power series), GL nodes, Nystrom kernel/matrix |
| `dens.py` | `gamma_S`, `q_S`, graded v-quadrature `fine_grid`, `build_G`, `t_S` closed form |
| `galerkin.py` | Legendre-Galerkin compression: `Smat(beta,M)`, `A_galerkin`, `mellin_moments` |
| `evald.py`, `model.py` | the two independent d_S assemblers (Nystrom / Galerkin) |
| `prod_t.py` | t_S on the production grid xi = 0(0.25)600, J_u = 55, parallel -> `t_tables.npz` |
| `prod_op.py` | operator part of (6) by Nystrom, no rescaling and no clipping -> `op_*.npz` |
| `D2_REPORT.md` | the report |

## The dictionary (derived and checked here, verdict 2.2)

Log-to-physical unitary `(Vg)(u) = u^{-1/2} g(log u)`; `U_c g(x) = g(x-c)` becomes
`U_c f(u) = e^{-c/2} f(u e^{-c})`, hence `U_a f(u) = p^{-1/2} f(u/p)` and
`U_{-ja} f(u) = p^{j/2} f(p^j u)`.  Applying these to the kernel `2cos(2 pi u v)`:
`U_{-ja}F_inf` has kernel `p^{j/2} 2cos(2 pi p^j u v)` and coefficient `(1-r^2) r^j * r^{-j} = 1 - 1/p`;
`U_a F_inf` has kernel `r * 2cos(2 pi u v / p)` and coefficient `-r*r = -1/p`.  So the compressed
kernel is `2 sum_{j>=-1} c_j cos(beta_j u v)` with `beta_{-1}=2pi/p, c_{-1}=-1/p` and
`beta_j = 2 pi p^j, c_j = 1-1/p (j>=0)` — the Jacobian cancels the `r^j`, as the verdict says.

## Two closed forms used throughout (both derived here)

1. **Mellin moments of the Legendre basis.**  With `phi_m(u) = sqrt(2m+1) P_m(2u-1)` orthonormal on
   `(0,1)`, `f_xi(v) = (2pi)^{-1/2} v^{-1/2+i xi}` and `s = 1/2 + i xi`:

   ```
   <phi_m, f_xi>  =  (2 pi)^{-1/2} sqrt(2m+1) * prod_{k=1}^{m}(s-k) / prod_{k=0}^{m}(s+k)
   ```

   (equivalently `Gamma(s)^2 / (Gamma(s-m) Gamma(s+m+1))`).  Exact, pole-free on Re s = 1/2, and
   evaluated by one product recursion — no quadrature.  Note `|<phi_m,f_xi>| ~ m^{-1/2}`, i.e.
   `f_xi` is not in `L^2(0,1)`; this is why the eigen-expansion of `t_S` converges only
   logarithmically in the basis size, and why (6) is written in terms of `u_S = A_S f_xi`.

2. **Galerkin matrix of a compressed cosine transform.**

   ```
   S_mn(beta) = int_0^1 int_0^1 phi_m(u) 2cos(beta u t) phi_n(t) du dt
              = 2 sqrt((2m+1)(2n+1)) Re[ i^n int_0^1 P_m(2u-1) e^{i beta u/2} j_n(beta u/2) du ]
   ```

   (`j_n` spherical Bessel), from `int_0^1 P_n(2t-1) e^{izt} dt = e^{iz/2} i^n j_n(z/2)`.  One
   composite-GL 1-D integral per beta, all (m,n) at once by a matrix product; the result is
   symmetric to 2e-15, which is the built-in check.  Large-beta behaviour
   `S_mn(beta) -> phi_m(0) phi_n(0) pi / beta`, valid only while `beta >> 2 pi M^4`.

## Scalars

`I(beta,xi) = int_0^1 v^{-1/2+i xi} cos(beta v) dv = (1/2)[(-i beta)^{-s} gamma(s,-i beta) + (i beta)^{-s} gamma(s, i beta)]`
with `gamma = mpmath.gammainc(s,0,z)`, principal branch; `J = -dI/ds`.  Cross-checked against the
exact power series `I = sum_m (-1)^m beta^{2m} / ((2m)! (2m+s))` (`J`: denominator squared) at
dps = 0.435 beta + 60: agreement 1e-42 at (beta,xi) = (0,1000), (3,2), (25,10), (200,30), (1000,50),
(100,100), (2 pi 2^8, 60).  Naive `mp.quad` on the same integral is WRONG for xi >= 100 and is not used.
