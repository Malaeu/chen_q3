# Step 32F — B-spline matrix identification instance and concrete-identity gap

## Goal

Provide the final Lean-side matrix-identification consumer for Step 32, and
record the remaining concrete B-spline identity gap without pretending it is
closed.

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

Steps 31--32F now give the final Lean consumer shape:

\[
\texttt{FinitePenaltyCert}
+
\texttt{B-spline matrix identities}
\Longrightarrow
\texttt{CertifiedFiniteWeilModel}.
\]

Equivalently, the interval-backed matrix certificate can now be consumed as a
finite analytic Weil positivity theorem for the B-spline packet block.

This is a real closure of the matrix-identification plumbing, but it is not yet
the proof of the concrete centered B-spline transform/correlation formulas.

## Concrete identity gap

The current Lean codebase still does not define the centered cardinal B-spline
bump, its Laplace transform integral, or its autocorrelation integral as
analytic objects.  Therefore Step 32F does not pretend to prove those
special-function facts from first principles.

Instead, the current file makes them the final concrete identity input through
`BSplineTranslatedAnalyticContract` and immediately converts that input into the
certified finite analytic model.

Under the stricter Step 32F requirement, Step 32 is not mathematically closed
until the following Lean objects exist and compile:

1. a centered/scaled B-spline bump definition;
2. its translated/scaled transform identity;
3. its nonzero boundary-scale proof at \(z=\pm1/2\);
4. its autocorrelation identity \(r_k(x)=b_{2k+1}(s_kx)/c_k\);
5. the Arch and Prime entry identities built from those formulas.

The external sanity-check matches the recorded Step 12 formulas: centered
cardinal B-splines have sinc/sinh-power transforms and compactly supported
piecewise-polynomial autocorrelations.  Useful references:

- de Boor, cardinal B-splines:
  `https://pages.cs.wisc.edu/~deboor/toast/pages005.html`
- Boost cardinal B-spline documentation:
  `https://www.boost.org/doc/libs/latest/libs/math/doc/html/math_toolkit/sf_poly/cardinal_b_splines.html`

## Remaining work inside Step 32F

This should not become another receiver layer.  The remaining work is the
actual analytic B-spline model input:

1. centered/scaled B-spline transform;
2. nonzero boundary scales;
3. B-spline autocorrelation profile \(r_k\);
4. Arch and Prime profiles.

That input should feed the already-built matrix-identification consumer in this
file.  Only after that can Step 32 be marked closed in the strict sense.

## Verdict

Step 32 is closed on the Lean matrix-identification-plumbing side, but not yet
closed as concrete B-spline mathematics.  Do not advance to Step 33 as if the
actual centered B-spline transform/correlation identities had already been
proved in Lean.
