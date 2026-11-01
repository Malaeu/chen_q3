# Independent heat-projection review

DIAGNOSTIC_NEVER_A_PROOF

The normalization in `heat_fit.py` is correct. This computes full-line forward heat followed by the literal finite-window projection. It does not replace that operation by periodic modal damping.

Let `g_s=exp(s partial_x^2)h`, `H=hat h=4xi(1/2-it)`, and use the Fourier convention `hat f(t)=int f(x)exp(-itx)dx`. The zero-extended real even basis has

\[
 B_n(t)=\frac{d_n(-1)^n b}{\sqrt L}
 [\operatorname{sinc}((t-\Omega_n)b)+\operatorname{sinc}((t+\Omega_n)b)],
 \quad b=L/2,\quad\Omega_n=2\pi n/L.
\]

Consequently

\[
 \langle g_s,e_n\rangle=\frac1\pi\int_0^\infty
 H(t)e^{-st^2}B_n(t)\,dt.
\]

Away from removable values, `B_n=2 d_n t sin(bt)/(sqrt(L)(t^2-Omega_n^2))`, exactly as implemented. The two factors `(-1)^n` cancel, so their absence in this rational expression is correct. The sinc fallback preserves the removable value. The derivative vector inserts `-t^2`; hence at zero it is the projection of the full `h''`.

For `p=P_m g_s`, `a=<f,p>`, `b0=||p||^2`, the derivative of normalized squared overlap is

\[
 W'(s)=\frac{2a}{b_0^2}
 [b_0\langle f,p'\rangle-a\langle p,p'\rangle].
\]

Thus the implemented stationary equation is correct for the fitted nonzero-overlap branch. Roots with `a=0` would also be stationary for W, but are zero-overlap minima and do not affect these maximizers. The quadratic comparison is exactly `P(h+s h''+s^2 h''''/2)`; it is a finite jet, not an assertion that the infinite heat Taylor series converges.

## Explicit exclusion of large heat times

The actual theta profile is positive. For x>=0, each theta summand is proportional to `16y^2-24y>0`, where `y=pi n^2 exp(2x)>=pi`; use evenness on the other half-line. Set

\[
 M_0=\int h=H(0),\qquad M_2=\int x^2h=-H''(0),\qquad \mu_2=M_2/M_0.
\]

Numerical values at 100 dps are

\[
 M_0=1.98848311275325643965\ldots,\quad
 M_2=0.0918877772605817501410\ldots,\quad
 \mu_2=0.0462099862308379415779\ldots.
\]

Positivity gives `|H(t)|<=M0`. Since `|cos(tx)-1|<=t^2 x^2/2`,

\[
 |g_s(x)-g_s(0)|\le\frac{M_0x^2}{8\sqrt\pi s^{3/2}}.
\]

The physical heat kernel and `exp(-u)>=1-u` give

\[
 g_s(0)\ge\frac{M_0}{2\sqrt{\pi s}}
 \left(1-\frac{\mu_2}{4s}\right),\qquad4s>\mu_2.
\]

Let `e0=1/sqrt(L)` on the window and `p_s=P_m g_s`. Orthogonal projection is a contraction, and integrating the squared x^2 bound yields

\[
 \frac{\|p_s-g_s(0)\sqrt L e_0\|}{g_s(0)\sqrt L}
 \le\eta(s):=\frac{b^2}{\sqrt5(4s-\mu_2)}.
\]

For eta<1, the normalized direction `p_s/||p_s||` has sine angle at most eta from e0. This follows from the distance of a ray to the center of the radius-eta ball around e0; its constant-mode component is positive. If `a0=|<f,e0>|`, `c0=sqrt(1-a0^2)`, then for every s>=S,

\[
 W(s)\le
 \begin{cases}
 (a_0\sqrt{1-\eta(S)^2}+c_0\eta(S))^2,&\eta(S)<c_0,\\
 1,&\text{otherwise}.
 \end{cases}
\]

This is an explicit bound for the entire infinite tail of heat times, not an extrapolation of the numerical scan.

|m|W(0)|Upper bound for all s>=1|Upper bound for all s>=100|lim W(s), s→infinity|
|---:|---:|---:|---:|---:|
|8|0.999688978|0.502353250|0.382101854|0.380927527|
|12|0.998761975|0.499006322|0.328763255|0.327142562|
|16|0.998437511|0.508038196|0.297089654|0.295127540|
|20|0.998285622|0.521988543|0.276167828|0.273927356|
|24|0.998291252|0.537232093|0.260685402|0.258210261|

Thus the source-dependent upper bound already excludes every s>=1 from improving even the zero-time baseline in these five finite cases. Constants and source vectors are evaluated with high-precision floating arithmetic, not outward-rounded intervals. This remains a numerical diagnostic rather than a formal certificate.

The bound does not prove uniqueness of a stationary point inside [0,1]. The finite grid, float optimizer and high-precision stationary refinement identify the best candidate found; they are not an exhaustive interval proof of global optimality on that compact interval. The infinite-s end is separately controlled by the bound above.

As an independent zero-time check, W'(0) from the physically projected h and h'' is positive: approximately 0.4928497295, 0.9830098497, 1.1038142839, 1.1559288338, and 1.1539632115 for m=8,12,16,20,24. These signs agree with a small positive fitted heat time.

## Stable alternatives and scope

For many small heat times, reuse spectral nodes and precompute `H(t) B_n(t)/pi`, as implemented. For very large s, scale `u=sqrt(s)t` before quadrature; the common `1/sqrt(s)` cancels from normalized overlap. This avoids trying to resolve a progressively narrower peak with a fixed t grid.

An independent physical evaluation, if needed, is

\[
 g_s(x)=\pi^{-1/2}\int_{\mathbb R}e^{-z^2}
 h(x-2\sqrt{s}\,z)\,dz,
\]

followed by the actual window projection. Gauss-Hermite inside and window quadrature outside provide a different implementation. No additional run is needed for this review, given the zero-time projection controls and the independent precision/quadrature replay already performed by the root agent.

The forward domain is s>=0. No negative-time Fourier integral is evaluated or treated as a permissible extension. No finite fit, small L2 residual, or large-time exclusion supplies the missing cofinal or energy-norm bounds.

`heat_review.py` reproduces the moments, zero-time derivatives and all large-s bounds without performing a fit or changing any output file.
