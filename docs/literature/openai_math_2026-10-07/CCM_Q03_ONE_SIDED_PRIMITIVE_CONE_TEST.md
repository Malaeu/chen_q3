# Own Q03-cycle attempt 1: scalar upper primitives do not order the CCM cone

2026-10-20. Q02 processed; Q03 not sent. This is a test of a proposed
one-sided summation-by-parts supplier, not a bound for actual Mobius sums.
Independent bounded PAPER review by ccm_q01_return_review: PASS; exact original Fourier normalization, three constraints and signs checked. Native goal ACTIVE; full exponent unchanged.

## Actual admissible vector

Keep original L=log m, w=2pi/L, M>=2 and all three constraints. On [0,L] set

    f(t)=(1/4+w^2) sin(wt) - (1/4+4w^2)/2 sin(2wt).

This uses only original modes ±1,±2, padded by zero. f(0)=f(L)=0.
For a=±1/2 the elementary antiderivative gives

    integral_0^L exp(a t) sin(jwt)dt
       = jw(1-exp(a L))/(a^2+j^2 w^2).

Therefore both exponential moments of f vanish exactly. Its Fourier vector c
belongs to the original ran(P); no new constraints or changed frequencies.
Also f'(0)=f'(L)=-3w^3 is nonzero. Normalizing c only multiplies the
quadratic forms below by a positive constant at each fixed cell; this factor
may depend on L and is not asserted uniform in m.

For the original normalized Fourier basis, the literal Q02(1) matrix gives

    q(s)=c*Q_M(s)c=2 Re integral_0^(L-s) f(t+s) conjugate(f(t))dt.

Here c denotes coefficients in that normalized basis (so the displayed f is
literal). Direct integration of the exponentials recovers Q02(1), including
the off-diagonal entries; mixed terms have not been discarded.

## Derivative sign changes inside the original projected cone

q(0)=2||f||_2^2>0 and q'(0)=f(L)^2-f(0)^2=0.
By periodicity and Taylor expansion at the common endpoint, with d=f'(0),

    q(L-h)=2 d^2 integral_0^h t(t-h)dt + O_L(h^4)
          =-d^2 h^3/3+O_L(h^4),
    q'(L-h)=d^2 h^2+O_L(h^3).

The derivative expansion follows directly by differentiating the smooth
integral, not by differentiating an unspecified big-O term.
For a_c(x)=x^(-1/2)q(log x), 1<=x<=m,

    a_c'(x)=x^(-3/2)[q'(log x)-q(log x)/2].

Thus a_c'(1)=-q(0)/2<0, while a_c'(x)>0 for x<m sufficiently close to m.
The positive interval may depend on L; no uniform-width claim is made.
This proves that -a_c' is not a positive comparison kernel even on an actual
rank-one weight W=cc*/||c||^2 in the original projected space.

## Exact scope of the obstruction

For a cumulative signed source H with H(1)=0, summation by parts and a_c(m)=0
read

    integral_(1,m] a_c dH = -integral_1^m H(x) a_c'(x)dx.

An upper bound H<=B alone is insufficient for a general positive-kernel
comparison. Choose a nonnegative smooth bump phi supported in an interval
where a_c'>0 and H=-K phi. Then H<=0 (and both endpoints vanish), but the
pairing equals K integral phi a_c'>0 and is unbounded as K grows.

This synthetic H is NOT the prime or Mobius cumulative source, and is NOT a
counterexample to the desired CCM estimate. It rules out only the inference
from a scalar upper bound alone, with no additional arithmetic or total-
variation input. A proof may still exploit actual coefficients, joint
frequency cancellation, two-sided control on selected regions, or an
integrated signed condition. No such supplier is proved here.

## Relation to the existing shelf and next action

CCM_LONG_MOBIUS_PRIMITIVE_TEST.md already audits the stronger absolute,
all-prefix scalar primitive: it retains prime discrepancy with coefficient
one. This attempt does not rerun that equivalence. It tests whether merely
weakening absolute control to an upper bound becomes usable after the three
projection constraints. The explicit admissible vector says that a direct
monotone-kernel argument still lacks an input.

Do not spend the next attempt on a universal scalar upper primitive unless
its return accounts for the sign changes above. Continue with the full signed
matrix pairing V=C+E_slow. No new full bound, cofinal result, SP or RH claim.

A standalone Fraction sanity check tested both moment cancellation and the
cubic coefficient at 30 rational w values (90 assertions); these finite checks
are not the proof. The proof is the displayed elementary identities for every
w>0. A SymPy import was unavailable; no dependency installed, no Lean/Arb run.

Bounded duplication check: CCM_PROJECTED_PATH_WINDOW_TEST.md uses cubic
endpoint overlaps for a different flat-projection leakage test; it does not
supply the present original three-constraint scalar-comparison obstruction.
No repository-wide novelty claim is made.
