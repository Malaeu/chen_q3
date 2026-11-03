# Bounded final independent read-only review

DIAGNOSTIC_NEVER_A_PROOF. Reviewed inputs and hashes are recorded in
FINAL_REVIEW_INPUTS.json. This reviewer did not author the certificate
implementations or the spectral experiment. No new installation or large
numerical replay was performed during this review.

**Verdict:** no unresolved scientific blocker found in the reviewed finite
interval certificates or the stated spectral-model conclusions. One
between-node scope qualifier was requested and then corrected: perturbed
coordinates must remain in[0,logW] when the modulus is evaluated for that
window. Neither the finite certificates nor the spectral models establish
all-node positivity, an arithmetic margin law, RH or route promotion.

## Directed interval source evaluation

The executed fallback is mpmath.iv, not native Arb. The reports state this
explicitly; the optional python-flint path is not described as executed.
Its correctness relies on mpmath's directed interval primitives and the
explicit series/identity implementation, not on nearest-rounded mpmath
values being promoted to certified endpoints.

The Li2 series remainder after k terms uses
r^(k+1)/((k+1)^2(1-r)), with r an upper bound for |z|<0.71. Adding the
symmetric remainder interval separately to real and imaginary components
encloses the complex remainder conservatively. The remaining transformations
are valid in the asserted domains:

- For0<x<1, reflection through1-x uses
  Li2(x)=pi²/6-log(x)log(1-x)-Li2(1-x).
- For-1<x<0, Li2(x)=Li2(x²)/2-Li2(-x).
- For z on the positive imaginary axis, the principal-branch identity
  Li2(z)=-Li2(z/(z-1))-log²(1-z)/2 applies. Its transformed modulus is
  at most1/sqrt2 in the source domain, below the series limit0.71.

The source normalization is consistent: the archimedean constant is
(pi²+8Catalan)/4, and Li2(x)-Li2(-x)+2Im Li2(ix) selects the powers
4x^(4k+1)/(4k+1)². The pole contribution is-16sinh²(t/4). All von
Mangoldt powers within the window are included. Symbolic exact hinge
equalities contribute zero; other branches require strictly resolved
interval signs. The exact zero argument is handled before logarithms.

Approximate sorting of node labels is followed by strict directed checks
of every adjacent order. Source labels use rational k/M and logarithms
of integer ratios. No floating merge tolerance chooses an equality.

The endpoint serializer reconstructs each finite binary endpoint exactly
as a Decimal and then rounds lower values downward and upper values upward.
The reviewed acceptance paths involve finite intervals; nonfinite source
values are rejected. The printed decimal intervals are not nearest-rounded
substitutes for the internal intervals.

## Matrix acceptance and endpoint comparisons

In the direct LDL path, every accepted pivot has a strictly positive lower
endpoint. The inverse unit-lower factor is enclosed recursively. The
eigenvalue lower bound uses the product of valid induced1/infinity norm
upper bounds, not the smallest LDL pivot by itself.

The uses of Python min/max relevant to acceptance operate on lower or upper
**point endpoints** obtained from interval objects. They do not choose the
maximum of overlapping interval values using an inconclusive interval
ordering. Likewise, the residual's maximum entry bound compares upper
point endpoints. This addresses a potentially unsafe pattern without
finding it in these code paths.

In the residual method, construction of L and B is explicitly untrusted.
The saved floating matrices are converted to exact common-denominator
dyadic integers. Verification computes BL-I exactly, checks both induced
residual norms below one, and bounds

    lambda_min(LL^T) >=
      (1-epsilon1)(1-epsilonInf)/(norm1(B)*normInf(B)).

This follows from L^-1=(BL)^-1 B and the two Neumann norm bounds. The
matrix LL^T is then computed by exact integer sums. Directed source
intervals enclose A-LL^T; symmetry makes the maximum absolute row sum a
valid spectral norm upper bound. Acceptance requires a positive lower
endpoint after subtracting that residual norm. No approximate eigenvalue,
factorization sign or numerical inverse approximation decides acceptance.

A read-only hash check found no mismatches in all nine saved successful
finite-certificate receipts: verifier, source-verifier, fallback-backend
and applicable dyadic-witness hashes agree with the reviewed files. This
check does not substitute for recomputation. The retained failed direct
LDL records are correctly described as uncertified intervals, not negative
source witnesses. The separate residual certificates cover those cases.

## Finite scope and between-node statements

The certificates apply to their exact listed finite alphabets and hence
their subsets and repeated-node PSD pullbacks. The outward continuity
budget only covers corresponding finite configurations of the same
cardinality, displaced within the stated window. The corrected report
states that restriction.

At nearest-grid scale the recorded continuity budget exceeds the available
eigenvalue lower bounds. Its negative lower estimate is an insufficient
certificate, not a negative kernel. Arbitrary close nodes and arbitrary
cardinality remain outside the finite Weyl argument. The report does not
claim to have supplied the missing all-node relative coercivity estimate.

## Spectral normalization and model limitations

The spectral implementation uses the correct positive-pair normalization
g(t)=2 sum(cos(gamma*t)-1)/gamma². The FFT factor N/2 converts the real
inverse FFT with zero endpoint bins into the desired cosine sum. The
remaining positive mass contributes the stated independent-point-noise
model on the finite grid; it is not an exact continuous high-zero tail.
The report exposes its discontinuity at finer scales.

The GUE tridiagonal scaling in the corrected code has diagonal variance1
and off-diagonal mean square n-i; its semicircle radius is2sqrt(n).
This agrees with the corrected unfolding and the measured density checks.
The old sqrt(2n) comparison is explicitly invalidated and excluded from
the conclusions. The fixed-first-zero anchoring and equal-count rescaling
controls are also disclosed, rather than presented as untouched stationary
or unconditioned ensembles.

All41 retained synthetic spectra extend beyond the largest tested cutoff1600;
the smallest final height is1723.5653913846618. Thus the high-cutoff controls
do not silently run out of generated discrete frequencies. The code's
finite time lookup has spacing1/8192, which contains all the requested
dyadic q32/mesh256 samples exactly.

The arithmetic calibration reference uses one extra endpoint so its
one-step predictor at old time a has the same index as the spectral
models. The corrected pipeline runs controls.py before the final analysis.
The .02 calibration gate fails on both fine grids, and the report correctly
blocks interpretation of the surrogate ordering as an actual-zeta law.

The no-tail control's rank bound2*202=404 is retained, and earlier numerical
failures are labelled conditioning/rank uncertainty rather than negative
worlds. Frequency-bin and FFT convergence are distinguished from the
material discrete-cutoff model dependence. All-real positive-spectrum
models are PSD by construction; the text does not count their positive
innovations as independent arithmetic evidence.

The reported partial ensemble ordering depends on the registered statistic
and overlaps across realizations. It is not promoted to stochastic
dominance, a history-uniform ordering, universality for actual zeta or an
infinite-spectrum result. No unsupported success claim remains in the
reviewed conclusions.
