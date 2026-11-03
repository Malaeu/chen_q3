# Final bounded pipeline review

Reviewed scan_extended.py, native_frame.py and frame.c, plus the completed
540 scan receipts. No blocking mathematical/convention defect found for
the stated finite numerical diagnostic and guarded best-gap bracket.

The polynomial nullspace is correct. In normalized squared-frequency
coordinates x=j^2, the rational evaluation denominator is D(z)=prod(z-j^2).
Its derivatives are D'(0)=(-1)^m(m!)^2 and
D'(j^2)=(-1)^(m-j)(m-j)!(m+j)!/2 for j>0. Coefficients proportional to
P(j^2)/(d_j D'(j^2)) therefore satisfy the included rational evaluation
constraints. Real-line nodes add one factor; a quartet adds a conjugate
factor pair through |j^2-z|^2 and advances q by two. Multiplying by
(j^2/m^2)^k spans the remaining numerator degrees. Included complex
Fourier prefactors are invertible real row mixing, hence do not alter the
kernel; exceptional exact carrier/node collisions are not asserted.

Independent Python-GMP twice-reorthogonalized row MGS against the native
polynomial method at zeta40, plant55 and DH60 gives projector differences
7.87e-16,9.48e-16,1.33e-15, respectively. Row-frame/nullspace residuals
are <=1.29e-16. Details and reproducible bounded test are saved in
NULL_VALIDATION.json and validate_null.py. These are float-converted
projector comparisons, not interval root/rank certificates.

Cutoff intervals have the correct open-left/closed-right convention for
gamma<T. r=d-q indexes the zero-based sorted spectrum. Only nontrivial
0<r<d sectors are scanned. The full residual is ||AQ||. Ordered MPFR MGS
then full QR preserves the event prefixes. Native MGS performs two
reorthogonalization passes with nearest rounding and checks zero pivots;
it does not provide an interval rank bound. In the actually built bulk
frames the smallest reported relative pivot is0.00373152, and the largest
float-frame orthogonality discrepancy is1.78e-15.

For a negative-world sector, lambda_r<-lambda_0 excludes a strict separator
by the r-th absolute-singular-value minmax principle. Gap upper bound0 is
valid for such a rejected sector. It need not exclude that sector from
improving a negative incumbent; the code correctly retains it in the final
upper bracket instead of claiming the evaluated candidate is the exact
argmax. Positive-world pruning by lambda_r<incumbent uses delta>=0 and is
valid for all later smaller r. Both comparisons include numerical slack.
The DH seeding of attainable r around the lower negative-count estimate
avoids mistaking an r=1 negative lambda_1 for the appropriate tiny-positive
candidate. It is a candidate search, not an assumption that the seeding
identifies the true argmax.

All540 receipts are present (180 per world). In every receipt:

- evaluated + bounded counts equal sector_count;
- metadata evaluated/bounded counts match actual list lengths;
- best_gap_resolved is true;
- global best-gap bracket width is at most2.000024 times numeric_guard.

This validates the advertised narrow numerical bracket, not an exact
maximizing kappa or a continuum statement. Rejected sectors' zero upper
bound intentionally leaves uncertainty at the guard scale when the best
candidate is near zero. Threshold-zero negative-count ranges come from
shifted numerical LDL and remain heuristic absent a certified source norm
error enclosure. More arithmetic precision does not certify source or zero
census accuracy. No status promotion is warranted by this review.

DIAGNOSTIC_NEVER_A_PROOF. No RH or route-state conclusion.
