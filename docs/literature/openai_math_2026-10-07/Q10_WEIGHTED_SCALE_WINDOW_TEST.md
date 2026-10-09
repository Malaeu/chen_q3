# Q10 own attempt — weighted Euler contraction and its window return

2026-10-09. Independent read-only q05_moment_audit PASS for W1–W5. Same source family and
Q10(18) consumer; originals/pins in SOURCE_Q10_CONCLUSION.md. RH/SP OPEN.

## Exact obstruction and proposed repair

Q10.21–24 excluded power contraction in the full UNWEIGHTED log-scale
norm. That does not cover a growing scale weight. We test the identical
Euler quadratic form with weight N^delta, and retain its full return to
N<=D0. No arithmetic coefficients in the target are changed; the weighted
Hilbert space is an auxiliary candidate only.

Fix actual u,R, finite good primes P_K outside R, and the same zero-
extended psi_u as Q10. Let Q[v](N) be the full paired Euler expression
Q10.21, with all powers, common radicals, coefficients e(d1,d2) and
normalization(qd1 qd2)^(-1/2). Fix delta=1/10 and

 ||v||_delta^2 = integral_0^infinity |v(N)|^2 N^delta dN/N,
 J_delta v(N)=N^(delta/2)v(N).

## W1. Exact weighted multiplier

Conjugating a causal dilation by this isometry gives

 J_delta[v(N/qp^j)] = qp^(j delta/2)(J_delta v)(N/qp^j).

Thus Q10's proof, with finite prime products and absolutely summable
geometric operator series, yields

 integral Q[v](N) N^delta dN/N
  = (2pi)^(-1) integral |Mellin(J_delta v)(tau)|^2 m_delta(tau) d tau,
 m_delta(tau)=product_(p in P_K,p not dividing Ru)
   [1-|z_p/(1-z_p)|^2],
 z_p=psi_u(p) qp^(-(1-delta)/2-i tau).                 W1

Characters zero at p contribute1; no prime of R or original S is added.
All active values of psi_u have modulus1. As qp>=7,
|z_p|<=7^(-9/20)<1/2 (equivalently7^9>2^20). Hence every multiplier
factor is positive. The fixed-delta geometric series has operator norm
at most qp^(-9/20)/(1-qp^(-9/20)); finite prime products justify termwise
Plancherel without requiring v to be smooth.

## W2. A genuinely stronger full-scale upper multiplier

For a=|z_p|<1/2,

 1-|z_p/(1-z_p)|^2 <= exp(-a^2/(1+a)^2)
                         <= exp(-(4/9) qp^(delta-1)).

Therefore, writing S_delta(u,R,K)=sum_active qp^(delta-1),

 0 <= integral Q[v](N) N^delta dN/N
       <= theta_delta ||v||_delta^2,
 theta_delta=exp(-(4/9) S_delta(u,R,K)) <=1.           W2

This improves the formal multiplier when the finite prime sum is large.
No asymptotic for that sum or uniform U-power saving is asserted here.
Even granting an arbitrarily strong theta_delta, W2 is not a bound on
the required finite window, as the next exact control shows.

## W3. Window negative control, with the SAME operator

Choose ANY nonzero smooth v supported strictly in(D0/2,D0). This is an
explicit test vector for a proposed generic norm-to-window implication,
NOT a substitute for the actual Mobius polynomial. If N<=D0 and d is
any nonunit good ideal, qd>=7 gives N/qd<=D0/7<D0/2. Consequently every
nonunit shift vanishes. Shared-radical coefficients have either BOTH
d_i nonunit or BOTH1. Thus exactly

 Q[v](N)=|v(N)|^2 for every N<=D0,
 integral_0^D0 Q[v](N)N^delta dN/N=||v||_delta^2.       W3

If there are no active primes, theta_delta=1 and Q[v]=|v|^2 globally;
the outside tail is zero. Otherwise theta_delta<1.
The outside tail is integrable by W1's absolute operator-series bound,
and must satisfy

 -||v||_delta^2 <= I_out[v]
  :=integral_D0^infinity Q[v](N)N^delta dN/N
  <=-(1-theta_delta)||v||_delta^2.                    W4

Thus any full-scale gain is canceled by the retained negative outside
contribution. One cannot delete this tail or suppose it is nonnegative.
For any theta_delta<1, a claimed window contraction with that factor
already fails on W3. In particular no coefficient-blind theorem giving
an o(1) multiple of ||v||_delta^2 on this window follows from W2.
The control is generic only; it does not refute Q10(18) on actual M.

## W4. Exact return for the actual arithmetic input

For fixed actual u,R set v(N)=1_(N<=D0) M_u^[R](N;W). It lies in the
weighted Hilbert space: its lower scales are empty and its upper support
is bounded. For N<=D0, causal shifts see the original polynomial, so

 integral_0^D0 Q[M_u^[R]](N)N^delta dN/N
  = integral_0^infinity Q[v](N)N^delta dN/N - I_out[v]
  <=theta_delta||v||_delta^2 - I_out[v].              W5

For a smaller target window, the lower complementary interval must also
be retained; it cannot be dropped merely from this signed identity.
All g,a,u weights can be placed outside W5 with their original masks and
scale D0=Lmax/qg; their signs/normalizations are not redefined. To obtain
an actual source gain this route needs a source-specific LOWER bound on
its combined I_out (and any lower-window complement). W3–W4 show why no
generic positivity claim supplies that input. The pointwise/common-
derivative Sobolev return also remains an obligation; W5 alone is not
Q10(18).

## Scope and next test

The weighted full-scale identity W1 and upper bound W2 are usable exact
facts, but this candidate has no full moment gain. The window return is
not a small technicality: the exact same dilation operator transports a
norm-sized negative contribution outside the window for valid generic
inputs. The arithmetic question remains whether the actual coefficients
force a sufficiently favorable combined boundary, not whether a different
weight makes the full-space multiplier small.

Independent review: q05_moment_audit checked the weight conjugation/sign,
absolute series and Plancherel, positive multiplier and finite theta,
exact generic support control including empty active-prime case, and
actual causal truncation/boundary identity. Root checked7^9>2^20 exactly.
This is pure operator algebra for the stipulated Q10 operator, not
independent certification of the source inverse moment or an actual
arithmetic lower bound. No new Pro question or rollover sent.
AUTOPSY: dropped=THEOREM_SHAPE; note=weighted full-scale Euler contraction does not imply a finite-window upper bound; an exact outside boundary can carry the whole apparent gain.

## Bounded alias return

long_positive_alias queried the shelf in three dictionaries: causal
Wiener-Hopf/finite-section Hankel boundaries; signed bilinear sieve
correlations; scale-localized Mobius second moments. All ask.sh queries
returned INCOMPLETE (freshness failure, with one unset local-candidate
variable), not evidence of literature absence.

One reused partial analogue: Connes–Consani, arXiv:2006.13771v1,
https://arxiv.org/abs/2006.13771 , Theorem1, printedp3 Eq4. Local source
is docs/routeB_bus/litreview/pdfs/2006.13771.pdf, SHA256
b8e0b54ade8535cf3ca633d1ef325bfc5c793b407da577a83d111726935b58e0.
Root rechecked hash and extractedp3; the earlier rendered-page check of
the transform vanishings is recorded in MOBIUS_PROJECTION_AUDIT_2026-10-06.md.
Short literal quote: “have support in the interval”. The stipulated
interval is[2^(-1/2),2^(1/2)]; there are also prescribed transform zeros
and an infinite Sonin projection. Logarithms map multiplicative scaling
to translation, but their archimedean positive trace is not our signed
finite-window arithmetic boundary. Its short-support hypothesis does
not allow adding all actual prime translations. No source-sensitive
lower bound for W5 is supplied; this is PARTIAL ANALOGUE only.

Next discriminator: derive the actual combined outside/lower-window
boundary from the SAME Mobius coefficients before estimating it; a
universal Hilbert-space shortcut is insufficient by W3. Any supplier
must distinguish those coefficients from the generic support control,
and return all common derivative and g/a/u costs. No new Pro chat or
request has been sent, and no claim of global literature absence is made.
