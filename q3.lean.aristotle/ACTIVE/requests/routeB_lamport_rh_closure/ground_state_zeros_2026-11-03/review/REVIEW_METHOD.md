# Independent diagnostic review protocol

Registered before the new m=16..300 payload is available, 2026-11-03.
Scope: finite literal CCM matrices, N=m, three worlds, no D0/status update,
publication, literature search, or continuum conclusion. All results remain
DIAGNOSTIC_NEVER_A_PROOF. The reviewer writes only in review/.

## Predictions and discriminators

1. From prior Q2 finite diagnostics, the zeta lowest even eigenvalue, its
   even gap, and parity gap become far smaller than double precision. A
   double-precision vector in that cluster will generally be arbitrary.
   Prediction: meaningful Fourier zeros require precision increasing with
   m; a tiny residual measured only in doubles will not establish vector
   convergence. Discriminator: paired precision/source-order replay, relative
   gap versus observed matrix/eigenpair discrepancy, sign-aligned vector
   distance or projector distance, and stability of each claimed root.
2. The plant and DH may have odd-below-even ground ordering. Prediction:
   a simple even Ritz vector need not be the actual full finite ground.
   Discriminator: independently assembled odd0 and even1, with signed
   odd0-even0 and even1-even0 gaps. Mark uncertainty where the gap is not
   resolved. A lowest-even calculation must retain that name if odd wins.
3. Every finite cosine transform has structural exterior harmonic zeros.
   Prediction: such zeros can produce coincidental proximity to source
   ordinates without recovering source roots. Discriminator: separate
   numerator roots, removable harmonic poles, and exterior harmonic zeros;
   repeat source matching both with and without structural roots.
4. A real-coefficient numerator can have nonreal roots even in the zeta
   finite problem. Prediction: raw nonreal numerator counts do not equal
   off-critical source quartets. Discriminator: map y to physical t and then
   s=1/2+i*t, test the actual critical strip, keep root symmetries and
   multiplicities, and demand paired-precision/source vector stability.
5. Nearest-neighbor matching will overstate recovery if multiple finite
   roots reuse one source root. Discriminator: one-to-one assignments,
   unmatched counts on both sides, and explicit distance thresholds in
   physical t coordinates. Count positive-height roots separately from
   quartets. No post-hoc change of the fixed cutoff c=1/4.

## Definitions to audit

Let L=log(m), omega=2*pi/L, b=L/2. In the phased orthonormal even basis,
e0=1/sqrt(L), en=sqrt(2/L)*(-1)^n*cos(n*omega*x). For normalized coordinates
v, put c0=v0, cn=sqrt(2)*vn. The physical transform is

F(t)=sum_n cn*(-1)^n*b/sqrt(L)
       *[sinc((t-n*omega)*b)+sinc((t+n*omega)*b)].

Away from harmonics this equals
2*t*sin(t*b)/sqrt(L) * sum_n cn/[t^2-(n*omega)^2].
The rational numerator P(y)=sum_n cn*product_{k!=n}(y-k^2),
y=(t/omega)^2, has degree at most m. P(0) is generically nonzero.
The origin and t=n*omega, 0<=n<=m, require the sinc continuation rather
than interpreting zeros of factors separately. In particular F(0)=sqrt(L)*v0
and F(n*omega)=(-1)^n*sqrt(L/2)*vn for n>0. Exterior n>m harmonics are
structural zeros of F. An exact root of P at a denominator node requires
the removable continuation to recover its physical multiplicity; do not
count every internal sine zero as a root when its denominator cancels it.

For s=sigma+i*gamma the transform coordinate is
t=gamma+i*(1/2-sigma). An off-line source quartet contributes two roots
at positive Re(t)=gamma, related by complex conjugation, and four total
t-roots. Negative real y gives imaginary t and Re(t)=0; it is not a
positive-height critical-strip source root. Complex y gives a quartet,
but only roots with |Im(t)|<1/2 map into the open critical strip.
Boundary conventions must be identical for finite/source counts.

## Bounded independent checks

- Read source and saved protocol; no new expensive eigensolve.
- Audit file hashes, grid coverage, dimensions, normalization, source
  provenance, fixed cutoff formula, and numeric status labels.
- On selected saved vectors at low/intermediate/high m and any failure
  transition, replay the direct sinc transform, pole continuations, and
  the rational identity with independent evaluation code.
- Check symmetry, norm, saved residual and gaps from payload, and verify
  replay precision/vector/selected-root convergence when available.
- Recount roots from stored rows, distinguish root-orbit kinds, validate
  one-to-one source assignments and threshold accounting. A sign scan
  alone does not establish completeness or detect even multiplicities.
- Audit actual coordinate strip membership and distinguish numerical
  zero/polynomial completeness from interval certification.
- Review exact final files read-only, preserve unresolved rows, report
  concrete discrepancies rather than promote mathematical status.

## Source census baseline

The copied DH 200dps census has 746 critical-line roots and 26 off-line
quartets (52 positive-height off-line roots), totaling 798 positive-height
roots below 900. All 26 listed pairs numerically lie inside 0<sigma<1.
Its argument-count rectangles use -1<=sigma<=2 and are numerical;
COMPLETENESS_STATUS is NUMERICAL_COUNT_MATCH_NOT_INTERVAL_CERTIFIED.
This is an input census, not a new certificate. Source quartet counts
and raw roots must never share an unlabeled denominator.
