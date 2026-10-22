# Post-Q12 own attempt 2: the prime Volterra output is not automatically H1

2026-10-22. Bounded source-preserving test before a derivative-based Fourier
estimate of the xi-dependent multiplier. Original CCM and all three P constraints
are retained. This is a finite-band domain obstruction, not an asymptotic CCM
lower bound or an exclusion of joint cancellation.

## Candidate and its necessary domain check

Q12(3.5) retains the complementary square involving Fourier(B psi). One possible
way of estimating a nonconstant multiplier is to control frequency tails by
derivative norms. Before spending such a bound on its prime component, check
whether B_pr psi belongs to H1 at all. The input psi does, but multiplication by
the sign function in Q12(4.9) cannot silently preserve this property.

For the original centered test on [-T,T], T=log(m)/2, Q12 gives exactly

    B_pr psi(r) = sign(r) sum_(n<=sqrt(m)) a_n psi(r+sign(r) log n),
    a_n=Lambda(n)/sqrt(n).

All prime powers are retained. Its jump at the center is

    J_pr = B_pr psi(0+) - B_pr psi(0-)
         = sum_(n<=sqrt(m)) a_n [psi(log n)+psi(-log n)].

This is an evaluation functional of the same test, not one of its two
exponential-integral contacts. No mixed Fourier coefficient is deleted in this
calculation. If J_pr is nonzero, the distributional derivative contains
J_pr delta_0 and is not L2. Consequently the second Fourier moment
integral x² |Fourier(B_pr psi)(x)|² dx is infinite.

## Exact original-P finite cell, without numerical labels

Take m=16, M=2, L=log16, w=2pi/L and the already-used admissible profile

    f(t)=-3/4+(1+4w²)cos(wt)-(1/4+4w²)cos(2wt),  0<=t<=L.

It is a nonzero polynomial in the ORIGINAL five modes and f(0)=f(L)=0.
For a=±1/2, integrating each cosine gives

    integral exp(at)f(t)dt
      =(exp(aL)-1)[(-3/4)/a+(1+4w²)a/(a²+w²)
                                      -(1/4+4w²)a/(a²+4w²)] = 0.

Thus its coefficient vector lies in the original ran(P). Normalize it if
desired; the jump's nonvanishing is unaffected. Its centered psi(r)=f(r+L/2)
is even. The only nonzero prime-power weights through sqrt(m)=4 are n=2,3,4;
n=4 samples the zero endpoint and is retained with that zero value.

The exact factorization, already present in the Q03 source, is

    f(t)=(1-cos wt)[12w²-(1/2+8w²)(1-cos wt)].

For n=2, t=T+log2=3L/4. For n=3, 3L/4<t<L. On that interval
0<=cos(wt)<1, and the second bracket is at least 4w²-1/2>0.
Indeed log16<4 and pi>2 imply w>1. Hence psi(log2)>0 and psi(log3)>0,
and the complete jump is strictly positive:

    J_pr=2[(log2)/sqrt2 psi(log2)+(log3)/sqrt3 psi(log3)] > 0.

There is no interval-arithmetic approximation or desired-sign training table
in this argument. This small cell tests the universal finite-band domain
claim only; it is not evidence about the eventual small-epsilon schedule.

## Decision and scope

Do not use ||(B_pr psi)'||_2 or a finite second Fourier moment merely because
psi is in H01 and band-limited before zero extension. A method using them
must first retain and pay the central jump, or use a weaker regularity norm.
This does not exclude estimates on the full B: pole/arch/prime pieces could
interact, and any such cancellation must be established before separating them.
It also does not exclude a direct estimate after the actual xi multiplier.

September OPENSGN already records the unpaid Poisson reconstruction and its
possible meromorphic terms; no identity from that archive is claimed anew.
This test supplies no improved exponent for Delta, Q, S_m or T_>R.
Next viable attempt must preserve this seam and both temporal halves as well as
the actual xi/prime coupling. No automatic Q13 or new full-spectrum run.

Independent read-only q12_complement_shelf bounded PAPER PASS: contacts,
positive complete jump, all endpoint traces and H1/Fourier consequence checked.
No files changed or numerical tests run by the reviewer. This is not a renewed
audit of the inherited September analytic identities.
RH and eta(epsilon)->0 remain OPEN.
