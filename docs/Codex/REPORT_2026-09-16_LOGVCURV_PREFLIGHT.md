# Full-theta `C_V = partial_x partial_y log V` preflight

STATUS: NO ACTUAL-SOURCE KILL; LIMITING TWO-END BLOCK IS PSD, WITH A
QUANTITATIVE CORRECTION GAP.

This is a bounded check of the exact full source
\[
 V(x,y)=\int_0^\infty (2t+x+y)f(t+x)f(t+y)\,dt,
 \qquad C_V=(\log V)_{xy},
\]
using source base `15c6ef56` (the four pinned reports are unchanged at `72e98b84`).  It keeps `C_V` separate from the already
refuted `C_q` tangent kernel and tests the origin jets and the two large-end
asymptotics.  It does not assert all-row positivity of `C_V` or of `V`.

Pinned inputs read:

- `REPORT_2026-09-14_SCHUR_REPEATABILITY.md`, SHA256
  `fe737941236b24c67bee7803a38014660698e852b2e61bc54f58672efb494190`,
  §§3, 5, 6, 8;
- `REPORT_2026-09-15_LAYER_GRAM_TEST.md`, SHA256
  `a402aa67f81824945d3324881e2a822a8e897a07316b3dc780e671228715e1eb`;
- `REPORT_2026-09-13_TWOCHANNEL_LAPLACE_BRIDGE.md`, SHA256
  `e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908`,
  §§T1--T3;
- `REPORT_2026-09-13_TWOCHANNEL_INTAKE.md`, SHA256
  `f8d5bd91e2c55692944af8508f272653d2dd4792dfdfba57da6366c8a5843dce`,
  origin-jet calibration.

## Origin check

Write
\[
 d_0=V(0,0)=2\int_0^\infty t f(t)^2dt,\quad q_0=f(0)^2,
 \quad I_k=2\int_0^\infty t(f^{(k)}(t))^2dt.
\]
Evenness and integration by parts give
\[
 V_x(0,0)=V_y(0,0)=0,
 \quad V_{xx}(0,0)=V_{yy}(0,0)=-I_1,
 \quad V_{xy}(0,0)=I_1-q_0,
 \quad V_{xxyy}(0,0)=I_2.
\]
The last identity follows directly by differentiating the integrand:
`V_xxyy = integral (2t(f'')^2+4f'f'')dt = I_2`, since `f'(0)=0` and
`integral f'f'' = [f'^2]/2 = 0`.

Therefore
\[
 C_V(0,0)=\frac{I_1-q_0}{d_0}=:\kappa>0,
\]
which agrees with the already paid diagonal curvature limit from the two-node
source proof.  The first derivative block test beyond the diagonal is
\[
 (C_V)_{xy}(0,0)
 =\frac{I_2}{d_0}
  -\frac{I_1^2+2(I_1-q_0)^2}{d_0^2}
 =\bigl(\sigma-\kappa^2\bigr)-2\kappa^2,
\]
where
\[
 \sigma=\frac{I_2}{d_0}+\frac{q_0^2-2q_0I_1}{d_0^2},
 \qquad
 \sigma-\kappa^2=\frac{d_0I_2-I_1^2}{d_0^2}.
\]
Weighted Cauchy--Schwarz gives only
`d_0 I_2 >= (I_1-q_0)^2`, since
`2 integral t f f'' = q_0-I_1`; it does not determine the sign of
`d_0 I_2-I_1^2`.  In particular the extra `2 kappa^2` required for
`(C_V)_{xy}(0,0)>=0` remains unpaid.  Thus the origin gives an exact
necessary jet expression but no source-specific obstruction from the
available estimates.  Higher derivative blocks remain unpaid.

## Same-end asymptotic, retaining the full theta source

The exact source factorization used in the pinned two-channel report is
\[
 f(z)=K e^{9z/2-a_z}h(a_z),\qquad a_z=\pi e^{2z},
\]
with the full convolution factor `h`, not a first-mode truncation.  For
`x=R+a`, `y=R+b`, bounded `a,b`, put
\[
 S=\pi(e^{2x}+e^{2y}),\qquad L=x+y.
\]
Endpoint Laplace scaling `z=2St` in the defining integral, with the full
`h` factors retained, gives uniformly on bounded offset sets
\[
 V(R+a,R+b)
 =K^2 e^{\frac92(2R+a+b)}e^{-S}
   \frac{L}{2S}\,(1+o(1)).
\]
More explicitly, with `a_x=pi*e^(2x)`, `a_y=pi*e^(2y)`,
`S=a_x+a_y`, `L=x+y`, and `z=S(e^(2t)-1)`, the exact normalized integral is
\[
 \frac{2S V(x,y)}{L f(x)f(y)}
 =\int_0^\infty e^{-z}\left(1+\frac zS\right)^{7/2}
   \left[1+\frac{\log(1+z/S)}L\right]
   \frac{h(a_x(1+z/S))h(a_y(1+z/S))}{h(a_x)h(a_y)}\,dz.       \tag{S1}
\]
For bounded offsets, the full Euler derivative bounds for `h` give, on
`z<=sqrt(S)`, a two-offset-derivative remainder bounded by
`C(1+z)^C/S`; on `z>sqrt(S)` the same derivatives have a polynomial bound
and the `e^-z` tail is `O(exp(-sqrt(S)/2))`.  Thus (S1) has relative `C^2`
error `O(S^-1)=O(e^-2R)`, with all theta modes retained.  Since `S` is a
sum of an `a` term and a `b` term,
\[
 \partial_a\partial_b[-\log S]
 =\frac{4e^{2a}e^{2b}}{(e^{2a}+e^{2b})^2}
 =\operatorname{sech}^2(a-b),
 \qquad
 \partial_a\partial_b\log L=-L^{-2}\to0.
\]
Consequently the raw curvature has the fixed-offset limit
\[
 C_V(R+a,R+b)
 =\operatorname{sech}^2(a-b)-\frac1{(2R+a+b)^2}+O_{C^0}(e^{-2R}),
 \tag{S}
\]
and hence tends to `A(a-b)=sech^2(a-b)`.  The displayed curvature `C^0` remainder is
uniform for bounded offsets; the full theta tail bounds retain all modes.

## Opposite-end asymptotic and the raw-derivative sign

Set `x=R+a`, `y=-R-b`, `delta=a-b`, and
`d=R+(a+b)/2`.  The folded exact identity with
`m=delta/2`, followed by `s=u^2-m^2`, gives a uniform endpoint estimate
through `delta=0`:
\[
 V(R+a,-R-b)
 =\frac{f(R+a)f(R+b)}{4\pi e^{2d}}
   \frac{\delta}{\sinh\delta}
   \bigl(1+O_{C^2}(e^{-2R})\bigr).
 \tag{O1}
\]
Here `delta/sinh(delta)` has its positive removable value `1` at zero.  To
see the scale directly, the full factorization gives, for
`A=pi*e^(2d)` and `r=sqrt(s+m^2)`,
\[
 f(d+r)f(d-r)
 =K^2e^{9d-2A\cosh(2r)}h(Ae^{2r})h(Ae^{-2r}),
\]
and the exponent increment in `s` is
\[
 H_m(s)=2\{\cosh(2\sqrt{s+m^2})-\cosh(2m)\},
 \qquad m=\delta/2.
\]
Its endpoint slope is
\[
 H'_m(0)=\frac{4\sinh(2m)}{2m},
 \qquad H'_0(0)=4,
\]
with the quotient understood by its analytic even continuation.  Thus the
apparent `sqrt(s+m^2)` singularity at `m=0` is removable.

For completeness, the uniform `C^2` endpoint check is as follows.  The full
theta factor has the exact expansion and inversion
\[
 h(u)=\sum_{n\ge1}\left(n^4-\frac{3n^2}{2u}\right)e^{-(n^2-1)u},
 \qquad
 h(u)=\left(\frac{\pi}{u}\right)^{9/2}e^{u-\pi^2/u}h(\pi^2/u).
\]
Termwise differentiation and the inverted formula give bounded Euler
derivatives `D_u^j h`, `D_u=u\partial_u`, for each fixed `j`; we use
`j<=6`, and also have `D_u^j(h-1)=O(1/u)` as `u->infinity`.  Hence the even
pair `h(Ae^{2r})h(Ae^{-2r})` and its needed `r`-derivatives have polynomial
majorants uniformly for `A>=A_0`; its even Taylor expansion removes the
`r=sqrt(s+m^2)` quotient at `m=0`.  The denominator pair at `r=m` is bounded
away from zero for large `A`, uniformly on every compact `|m|<=M`.

Make the exact change of variable `z=A H_m(s)`.  Relative to the endpoint
value `f(d+m)f(d-m)`, this gives
\[
 A H'_m(0)\frac{V(R+a,-R-b)}{f(d+m)f(d-m)}
 =\int_0^\infty e^{-z}
   \frac{h(Ae^{2r})h(Ae^{-2r})}
        {h(Ae^{2m})h(Ae^{-2m})}
   \frac{H'_m(0)}{H'_m(H_m^{-1}(z/A))}\,dz,                 \tag{O3}
\]
where `r=sqrt(H_m^{-1}(z/A)+m^2)`.  On `0<=z<=sqrt(A)`, the inverse
expansion at the endpoint and the Euler derivative bounds give, uniformly for
`|m|<=M` and for every offset derivative `|alpha|<=2`,
\[
 \left|\partial_{a,b}^{\alpha}\bigl(Q_A(z,m)-1\bigr)\right|
 \le C_M A^{-1}(1+z)^C,\qquad |\alpha|\le2,                 \tag{O4}
\]
where `Q_A` is the non-exponential factor in (O3).  The inverse is uniform
through `m=0`: differentiating `H_m(H_m^{-1}(z/A))=z/A` uses
`H'_m(s)>=4` and hence `H'_m(0)>=c_M>0`; equivalently, for
`v=H_m^{-1}(z/A)`,
`partial_m v=-2m+4 sinh(2m)/H'_m(v)`, and convexity gives the same
bounded quotient.  In particular `v<=z/(4A)` on the endpoint piece.  On
`z>sqrt(A)`, convexity and the same formula give
`r<=C_M(1+log(1+z))`; the full-source derivative bounds and the inverted
formula for small arguments then give
`|partial_{a,b}^alpha Q_A(z,m)|<=C_M(1+z)^C`.  The factor `e^-z`
then makes this tail `O(exp(-sqrt(A)/2))`, with the same conclusion after two
derivatives.  Splitting at `sqrt(A)` in (O3) proves the claimed uniform
relative `C^2` error `O(A^-1)=O(e^-2R)` in (O1), including `a=b`; the region
`u>d/2` is superexponentially smaller by the same complete-source bounds.

All factors in (O1) except
\[
 k(\delta)=\frac{\delta}{\sinh\delta}
\]
are separated in the raw variables `x,y`.  Thus, for `delta != 0`,
\[
 C_V(R+a,-R-b)\longrightarrow
 B(a-b):=(\log k)''(a-b)
 =\operatorname{csch}^2(a-b)-\frac1{(a-b)^2}.
 \tag{O2}
\]
The continuous value is `B(0)=-1/3`.

There is one sign convention to retain.  If
`\widetilde V_R(a,b)=V(R+a,-R-b)`, then
`partial_a partial_b log \widetilde V_R=-C_V(R+a,-R-b)` because
`y=-R-b`.  Equation (O2) is the **raw** `C_V` value; the offset-coordinate
curvature is `-B`.  Losing this reflected derivative reverses the channel
test.

The folded estimate pays the `C^2` transition through `a-b=0`; the pointwise
correlation asymptotic alone would not have been enough, but (O1) retains the
full source factors and the analytic slope at zero.

## Limiting two-channel curvature is positive

Ignoring that still-unpaid finite-`R` correction, the raw limiting block on
the two offset rays is
\[
 \mathcal C((+,a),(+,a'))=A(a-a'),\quad
 \mathcal C((- ,b),(-,b'))=A(b-b'),\quad
 \mathcal C((+,a),(-,b))=B(a-b).
\]
The elementary Fourier transforms (with the same convention in both
channels) are
\[
 \widehat A(\omega)=\frac{\pi|\omega|}{\sinh(\pi|\omega|/2)},
 \qquad
 \widehat B(\omega)=-\frac{2\pi|\omega|}{e^{\pi|\omega|}-1}
 =-e^{-\pi|\omega|/2}\widehat A(\omega).
\]
Here is an elementary derivation that avoids an untracked principal-value
cancellation.  The partial fractions ([DLMF 4.36.E4](https://dlmf.nist.gov/4.36.E4), paired at integer and shifted half-integer poles) are
\[
 B(t)=2\sum_{n\ge1}\frac{t^2-\pi^2n^2}{(t^2+\pi^2n^2)^2},
 \qquad
 A(t)=-2\sum_{n\ge0}
 \frac{t^2-\pi^2(n+\tfrac12)^2}{(t^2+\pi^2(n+\tfrac12)^2)^2}.
\]
For `g_a(t)=(t^2-a^2)/(t^2+a^2)^2` and the convention
`hat g(omega)=integral exp(-i omega t)g(t)dt`,
`g_a=-partial_t[t/(t^2+a^2)]` and the standard Cauchy transform give
\[
 \widehat{g_a}(\omega)=-\pi|\omega|e^{-a|\omega|}.
\]
Summing the resulting geometric series yields exactly the displayed
`hat A` and `hat B`.  The exchange is in the tempered sense against a
Schwartz test function; the paired summands are bounded by `C/a^2` for every real argument, so no absolute `L^1` summability of the
individual partial fractions is being claimed.

Hence the two-channel Fourier symbol is
\[
 \widehat A(\omega)
 \begin{pmatrix}1&-e^{-\pi|\omega|/2}\\
                 -e^{-\pi|\omega|/2}&1\end{pmatrix},
\]
whose eigenvalues are
\[
 \widehat A(\omega)(1-e^{-\pi|\omega|/2}),\qquad
 \widehat A(\omega)(1+e^{-\pi|\omega|/2})\ge0.
\]
For a finite complex family, put
`P_sigma(omega)=sum_j c_sigma,j exp(i omega a_sigma,j)` and
`r(omega)=exp(-pi|omega|/2)`.  Its limiting quadratic form is explicitly
\[
 \frac1{2\pi}\int_{\mathbb R}\widehat A(\omega)\left[
 \frac{1-r(\omega)}2|P_+(\omega)+P_-(\omega)|^2
 +\frac{1+r(\omega)}2|P_+(\omega)-P_-(\omega)|^2\right]d\omega\ge0.
\]
After combining duplicate nodes within each channel, exponential independence makes this form
strictly positive for every nonzero fixed finite coefficient family: both
weights are positive for `omega != 0`.  Nevertheless both eigenvalues lose
coercivity (the lower one at `omega=0`, and both as `|omega|->infinity`).
It is therefore a positive limiting brother, not a proof that the finite-`R`
full-theta `C_V` is PSD.  Entrywise convergence, even with fixed finite rows,
cannot control finite-`R` corrections uniformly over arbitrary finite rows;
for each fixed finite node family the exact curvature matrix is positive definite for all sufficiently large R, but its threshold and lower bound may depend on that family.

## Verdict and exact remaining test

The origin jets pass the diagonal test and do not currently give a strict
theta-source obstruction.  The two-end calculation produces a coherent
positive limiting block `(A,B)`, rather than a negative witness.  Exact
involution `V(-x,-y)=V(x,y)` is consistent with the two channel formulas and
does not remove the cross channel.

The `C^2` transition through `a=b` is paid by (O3)--(O4).  The remaining
possible stronger exterior test is a uniform finite-`R` quadratic-form
correction estimate (or a direct finite-`R` Gram construction) relative to
this limiting block.  It cannot be phrased as comparing a finite-`R` Fourier
symbol, because that block is not translation invariant.  The lower limiting
branch vanishes at `omega=0`, and both branches decay at high frequency, so
entrywise limits do not supply the required correction domination.  This is a
possible stronger `C_V` route outside the original production interval, not a
necessary step for the original `V` sign on `I`.  No such estimate is paid in
the pinned reports; the current result is a positive limiting mechanism, not
an all-row PSD theorem or a negative `C_V` witness.

The limiting kernels use reciprocity and the leading full-source tail; this argument does not extract an additional consequence from the detailed square-rate arithmetic.

No numerical scan, Lean run, or RH claim is used in this derivation.

## Independent acceptance and scope

STATUS: ACCEPTED_LIMITED_PAPER. No Lean certification or canonical admission.
Candidate SHA256: `45c67d8709722291b263df49ac7f1c8eedc23e2de75bc323ffe7575b98406638`. Independent review by
`/root/sibling5_check`, SHA256 `4a618d351f383e967bd1e158a8cfaa859bce078d993984b68a5a3ca776cf3ecf`.
Verdict: `ACCEPT_LIMITING_TWO_END_CURVATURE_MECHANISM_ONLY`.

The parent independently checked the origin derivatives, exact full-source
rescalings, uniform differentiated remainder, reflected sign and Fourier
quadratic form. The discarded stronger Cauchy--Schwarz reading is not used.
This closes a differentiated asymptotic preflight, not the all-row sign of
the exact curvature on I, the full V, or RH. This local result is separate
from the subsequently received Proshka response.

SUBSEQUENT DISPOSITION: the separately accepted LOGVCURV response at
`6f4da4917734c92fba9459316494dd70ebbe77b5` excludes all-row C positivity on
every real open interval. See `REPORT_2026-09-16_LOGVCURV_INTAKE.md`. Thus
the optional uniform exterior positivity proposal above is now excluded,
while the asymptotic formulas and fixed-family eventual positivity remain
valid. The finite family in the obstruction can depend on R; there is no
conflict of quantifiers and no further C-positivity request.
