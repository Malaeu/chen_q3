# m16 direct-X interval certificate: bounded gap

Historical gap, resolved at finite scope by
[M16_DIRECT_X_INTERVAL_AUDIT_2026-10-30.md](M16_DIRECT_X_INTERVAL_AUDIT_2026-10-30.md):
independent direct |X|/B<0.000336<1/4. The derivation below is preserved as
the pre-certificate state. This was a physical-source diagnostic and certificate plan,
not an independent interval-X result, an identity check, or an RH claim.
`CHALLENGER_NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.

## Required independent bound

For the retained interval-normalized even vector, use only

\[
 X=k(h_{\rm out},v)-k(W,v)+\lambda\langle W,v\rangle,
 \qquad W(x)=\sum_{\ell\ne0}h(x+\ell L),\quad L=\log16,\quad b=L/2.
\]

The last projection term is valid because `A_m v=lambda v` and `v` is in
`V_m`. It is about `-5.67159218446e-63` at the retained midpoint. Do not
obtain X by solving `F+X+lambda<h,v>=0`.

The direct midpoint is `X=+4.00560883249e-37`, while the certified Arb
denominator from the earlier run has midpoint `B=4.22699336601e-33`, so
`B/4=1.05674834150e-33`. To certify `|X|<B/4` by the direct route, the
**sum of all independent direct-source absolute errors** must be below

\[
 B/4-|X_{\rm midpoint}|\approx 1.05634778062\cdot10^{-33}.
\]

The earlier coarse exterior arch-tail expression at `S=L+0.3` is
`4.73325141020e-34`. If this expression is accepted as an actual absolute
bound, the unspent budget for *every other* error is
`5.83022639601e-34`. This is room for a certificate, not one: the previous
`k(h_out,v)` and `k(W,v)` integrations are high-precision midpoints without
rigorous quadrature enclosures. Their signed terms are around `1e-19`, so
ordinary floating-point agreement does not pay this budget.

## Exact reduction of the truncated W convolution

Let `omega_r=2*pi*r/L`, and write the normalized finite vector as
`v(x)=sum_{r=-16}^{16} c_r exp(i*omega_r*(x+b))/sqrt(L)`.
In this section only, set `W_2(x)=h_2(L-x)+h_2(L+x)`: this retains
images ell=+/-1 and theta indices n=1,2. The exact W above has further
images and theta terms, whose errors remain unpaid. Every q_W, <W,v>
and A_W in this section refers to this truncated W_2.
For the theta truncation `h_2` with `n=1,2`, define

\[
 J(a,z;\kappa)=\int_a^z h_2(y)e^{\kappa y}\,dy.
\]

With `lambda_n=pi*n^2` and `G_t(a,z)=Gamma(t,lambda_n e^{2a})-
Gamma(t,lambda_n e^{2z})`, each theta term is explicitly

\[
 J_n(a,z;\kappa)=
 8\pi^2 n^4\lambda_n^{-(9/2+\kappa)/2}G_{(9/2+\kappa)/2}(a,z)
 -12\pi n^2\lambda_n^{-(5/2+\kappa)/2}G_{(5/2+\kappa)/2}(a,z).
\]

Substitution `u=lambda_n exp(2y)` proves this formula. Since
`exp(i*omega_r*L)=1`, the physical overlap convolution is exactly

\[
 q_W(s)=\frac{2}{\sqrt L}\sum_{r=-16}^{16}
 c_r e^{i\omega_r(s+b)}
 \{J(b+s,3b;-i\omega_r)+J(b,3b-s;i\omega_r)\}.
\]

This removes the inner numerical quadrature. It gives
`q_W(0)=2<W,v>`, and the remaining paired arch term is

\[
 A_W=\int_0^L j(s)[q_W(0)-q_W(s)]\,ds
       +q_W(0)J_L,
 \quad j(s)=e^{-s/2}/(1-e^{-2s}),
 \quad J_L=\tfrac12\log(5/3)+\arctan(1/4).
\]

The paired difference has a removable zero at `s=0`; direct interval
evaluation of `q_W(0)-q_W(s)` loses dependency information there. In
python-flint, `acb(u).gamma_upper(shape)` is the correct argument order.
An Arb evaluation of this closed form at `s=log 2` gave
`q_W(s)=-5.65675424335788456e-20` and the independent direct Arb
integration gave half that for its unscaled overlap integral, as required.
The exact `q_W(0)` enclosure was centered at `-2.39640429540773477e-31`,
twice the earlier `<W,v>` midpoint.

## Bounded computation and remaining estimate

An outer `acb.integral` call using nested Arb inner integrals was stopped at
30 seconds. Replacing the inner integral with the exact gamma formula still
did not finish within a separate 25-second cap, including when started at
`s=0.01`. These are feasibility observations, not quadrature bounds.
The earlier 64/96 fixed Gauss-Legendre difference `4.38e-55` is also only a
convergence diagnostic.

The first unpaid estimate is a **rigorous enclosure of the paired (A_W)**
with absolute radius small enough to fit the `5.83022639601e-34` residual
budget together with all other errors. A practical next method is to factor
`q_W(0)-q_W(s)=s R(s)` analytically (or use a Taylor model near zero), then
perform Arb integration on bounded subintervals; `s*j(s)` is analytic at
zero. The direct exterior arch, pole tail, prime cutoff, theta truncations,
image tail, and interval-vector propagation must then be included in the
same budget. The first omitted W theta term at its smallest argument `b`
is `h_3(b)=2.21073842438e-190` versus `h_1(b)=1.16014079209e-17`; this
is a truncation diagnostic until an analytic tail majorant is propagated.

No source-physical interval-X bound is certified here. The existing
identity-derived bound remains a separate result and was not used above.

Root integration check: distinguished exact periodization W from W_2;
substitution y=L-x and y=L+x verifies the two displayed J limits.
This records a useful reduction, not a new certified status.
