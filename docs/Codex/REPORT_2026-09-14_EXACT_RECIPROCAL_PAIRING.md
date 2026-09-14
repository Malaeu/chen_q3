# Exact reciprocal pairing: what the finite geometric approximation lost

STATUS: INDEPENDENTLY_REVIEWED_ANALYTIC_SOURCE_STRUCTURE_ONLY.
SCOPE: complex source structure only. No sign theorem for V or zero-location
claim for xi. The concurrent GAMMABRANCH audit completed independently:
5189493584c0f56074eb42fd7b064f4b4346830a accepts B1-B8 in their stated scope.

Inputs, pinned in the gamma bridge receipt:
- Gamma bridge, 65c4a563ce4319a595a17e7c264dbbd77f1672e1,
  docs/Codex/REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md,
  SHA256 7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621.
- Full theta source, docs/routeB_bus/proshka/
  PROSHKA_THETA_TOTAL_POSITIVITY_SOURCE_TEST_2026-09-12.md,
  SHA256 654c1a3bfe0a4eb570adce71c6d62d7b97deca110765de79a7776dd6878b5bd7.
- B1-B8 obstruction, 15fe3eb8ee19c85c51f3ad2984583dc95a0af2a1,
  docs/Codex/REPORT_2026-09-14_GAMMA_COFINAL_BRANCH_OBSTRUCTION.md,
  SHA256 862011bd19d73961d2270c8b7da61f63d30e68e2d195c4846497d9f1c2c39f63.

## R1. Return point in plain language

The finite approximation combines a density at t and 1/t by taking a square
root. This restores evenness on the real axis. But a simple complex zero of
one factor, without a zero of the other factor, becomes a branch point.
The true source has an exact reciprocal identity pairing those zeros with
identical multiplicities. Thus the operation is algebraically a square for
the true source, not just a positive product on the real line.

This explains a lost property. It does not establish that the property is
sufficient to control zeros of the Fourier transform.

## R2. Complex convergence of the finite densities

Let H={t in C: Re(t)>0}, lambda_n=pi n^2. Extend r_N to an entire function
using the exact partial fractions

    r_N(t)=sum_(n=1)^N (d_(n,N)t+e_(n,N))exp(-pi n^2 t),
    d_(n,N)=4pi^2 n^4 (N!)^4/[(N-n)!(N+n)!]^2,
    e_(n,N)=-(2/pi)d_(n,N) sum_(m<=N,m!=n)1/(m^2-n^2). (R1)

The formula for e follows by differentiating the product of the other pole
factors at -lambda_n: the coefficient of (z+lambda_n)^(-1) equals
-2d_(n,N) sum_(m!=n)(lambda_m-lambda_n)^(-1).

For fixed n as N->infinity,

    d_(n,N) -> 4pi^2 n^4,
    sum_(m>=1,m!=n)1/(m^2-n^2)=3/(4n^2),
    e_(n,N) -> -6pi n^2.                               (R2)

To check the middle identity without interchanging a conditional series,
its absolutely convergent partial sum through M>=n is

    [H_(M-n)-H_(n-1)-H_(M+n)+H_n+1/(2n)]/(2n),

where H_0=0; taking M->infinity gives 3/(4n^2).

For all N>=n, the factorial ratio in d is at most one, and

    sum_(m<=N,m!=n)1/|m^2-n^2|
      <=2 sum_(k>=1)1/k^2 <=4.

Here m+n>=|m-n| and there are at most two terms for each |m-n|=k;
sum k^(-2)<=1+integral_1^infinity u^(-2)du=2. Hence

    0<d_(n,N)<=4pi^2n^4,   |e_(n,N)|<=32pi n^4.         (R3)

On a compact subset K of H, take eta=min Re(K)>0 and R=max |K|.
The absolute value of each term of (R1) is at most

    (4pi^2 R+32pi)n^4 exp(-pi eta n^2),

a summable bound independent of N (set coefficients zero when n>N).
Equations R2-R3 and dominated convergence for series therefore prove

    r_N(t) -> r(t)=sum_(n>=1)(4pi^2n^4t-6pi n^2)exp(-pi n^2t)

uniformly on K. In particular r is holomorphic on H, and all complex
derivatives converge locally uniformly there. This is an extension of the
real convergence statement, not an assumption about the zeros of r or xi.

## R3. Reciprocity pairs the entire complex divisor in H

The accepted theta identity r(1/t)=t^(5/2)r(t) holds for positive real t.
Both sides are holomorphic on H, with the principal branch of t^(5/2):
1/t maps H biholomorphically to H. The identity theorem gives

    r(1/t)=t^(5/2)r(t),  t in H.                        (R4)

Since t^(5/2) is nonzero, a zero t_0 of r in H has the same multiplicity
as the zero 1/t_0. This follows from the nonzero derivative of t->1/t.
It is a statement about the full complex divisor, not merely real symmetry.

Let S={x in C: |Im(x)|<pi/4}. Both exp(2x) and exp(-2x) lie in H, and
Log(exp(2x))=2x on S. Therefore

    Phi(x)=exp(5x/2)r(exp(2x)),
    F(x)=r(exp(2x))r(exp(-2x))=exp(5x)r(exp(2x))^2
        =Phi(x)^2,  x in S.                            (R5)

Phi is holomorphic and even on S. Every zero of F there has even order.
The square root continued from positive real values is exactly Phi; no
interior square-root branch point exists. This does not assert that Phi is
entire: the previously proved boundary obstruction at i*pi/4 is retained.

## R4. What convergence does and does not preserve

By R2 and composition on compact subsets,

    F_N(x)=r_N(exp(2x))r_N(exp(-2x)) -> Phi(x)^2

locally uniformly in S. If Phi has a zero of multiplicity m at x_0, take a
small disk with no other zeros and a zero-free boundary. Rouche's theorem
shows that F_N has exactly 2m zeros, counting multiplicities, in that disk
for sufficiently large N. It does not require those zeros to have even
individual multiplicities, or their square-root branch points to cancel
at finite N. Finite unpaired zeros can merge into an even zero of the limit.

On a compact neighborhood in S where Phi has no zeros, F_N/Phi^2->1
uniformly. For large N its values lie in the disk |w-1|<1/2, so

    Phi(x) sqrt(F_N(x)/Phi(x)^2) -> Phi(x)

is a holomorphic branch with locally uniform convergence. If the connected
neighborhood contains a real point, this branch agrees there with the
positive real G_N and hence with its analytic continuation. No square root
across an unpaired zero is asserted.

Thus complex convergence of the product is compatible with nonremovable
branches in every finite approximant. Likewise the proved entire-transform
convergence M_N->xi(1/2-iz)/xi(1/2) is compatible with infinitely many nonreal
zeros in each approximant. Nothing here determines whether those transform
zeros approach the real axis, escape to infinity, or approach a nonreal
zero of the limit. The last alternative cannot be excluded by assuming RH.

## R5. Exact next-mechanism filter

PROVED: the full additive density is TN-infinity; the actual source has R4;
R5 makes the reciprocal product an exact holomorphic square. The finite
geometric approximation retains additive TN-infinity but loses that exact
pairing and, by the separately reviewed B1-B8, fails the proposed cofinal
real-zero route for N>=13.

OPEN: a theorem converting the joint additive TN-infinity and reciprocal
structure into the required Mellin/Fourier zero location. No such theorem
is supplied by this report. Evenness, smoothness, complex analyticity, or a
formal Gram/Schur identity alone remain insufficient.

UNVERIFIED semantic descriptions for a future bounded source hunt:
- A reciprocal involution acting on a holomorphic divisor; symmetry-compatible
  approximation before a nonlinear square root. Map back: R4-R5, not evenness
  alone. Missing output: an independent real-zero or full-energy theorem.
- Additive variation diminution plus inversion/weighted Mellin transformation.
  Map back: the actual density r and exact weight exp(5x/2). Missing output:
  preservation under that specific change of variables and weight.

The next search must supply that missing output with checked hypotheses or
identify a precise restricted bridge. Another scalar Bessel lift or a renamed
geometric gamma preserver would repeat an established obstruction. Analytic
branch cancellation itself is not a positive energy and does not close RH.
