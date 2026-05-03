# Step 32F — B-spline matrix identification instance

## Goal

Close the Step 32 Lean-side matrix-identification chain.

The output is the final object required by Step 31:

\[
\texttt{CertifiedFiniteWeilModel}.
\]

## Lean file

`Q3/Proofs/PSD_BSplineMatrixIdentificationInstance.lean`

## Main object

`CertifiedBSplineConcreteBlock`

It packages:

- concrete B-spline translated-packet identity data;
- the interval-backed finite penalty certificate;
- the split

\[
C = D + \theta R
\]

at quadratic-form level.

## Main conversion

\[
\texttt{CertifiedBSplineConcreteBlock}
\to
\texttt{CertifiedFiniteWeilModel}.
\]

Lean name:

`bspline_packet_certifiedFiniteWeilModel`

## Main consumer theorems

- `CertifiedBSplineConcreteBlock.weil_nonneg_on_analyticBoundary`
- `CertifiedBSplineConcreteBlock.weil_ge_theta_R_on_analyticBoundary`

These expose:

\[
0\le \mathcal W(h_v)
\]

and the strengthened lower bound

\[
\theta\,v^T Rv \le \mathcal W(h_v)
\]

for analytic boundary-null packet vectors.

## What this closes

Steps 31--32F now give the full formal bridge:

\[
\texttt{FinitePenaltyCert}
+
\texttt{B-spline matrix identities}
\Longrightarrow
\texttt{CertifiedFiniteWeilModel}.
\]

Equivalently, the interval-backed matrix certificate can now be consumed as a
finite analytic Weil positivity theorem for the B-spline packet block.

## Honesty note

The current Lean codebase still does not define the centered cardinal B-spline
bump, its Laplace transform integral, or its autocorrelation integral as
analytic objects.  Therefore Step 32F does not pretend to prove those
special-function facts from first principles.

Instead, it makes them the final concrete identity input through
`BSplineTranslatedAnalyticContract` and immediately converts them into the
certified finite analytic model.

The external sanity-check matches the recorded Step 12 formulas: centered
cardinal B-splines have sinc/sinh-power transforms and compactly supported
piecewise-polynomial autocorrelations.  Useful references:

- de Boor, cardinal B-splines:
  `https://pages.cs.wisc.edu/~deboor/toast/pages005.html`
- Boost cardinal B-spline documentation:
  `https://www.boost.org/doc/libs/latest/libs/math/doc/html/math_toolkit/sf_poly/cardinal_b_splines.html`

## Remaining work after Step 32

This is no longer another matrix-identification receiver.  The remaining work
is to instantiate the analytic identity input for the actual B-spline bump:

1. centered/scaled B-spline transform;
2. nonzero boundary scales;
3. B-spline autocorrelation profile \(r_k\);
4. Arch and Prime profiles.

That should be treated as the analytic B-spline model input feeding the already
closed Step 32 matrix-identification bridge.

## Verdict

Step 32 is closed on the Lean matrix-identification side.  The next architectural
move is Step 33: consume certified finite B-spline blocks inside the directed
family / exhaustion route.
