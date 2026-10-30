# Sharp entropy: cubic obstruction candidate

Root derivation after ENTROPY was sent; do not append to or resend the running
request. Status: independently checked bounded PAPER obstruction, using inherited
MARKOV (6.8) and CONFINE radicality on S_exp. This concerns the proposed
Ent_mu(F²)<=E_h(F)/4, not RH and not the even Poincare inequality.

## Exact perturbation

Let dmu=cosh(x/2)h(x)dx/2, q=h''/h, g=q−1/4. h is positive and even.
Two integrations by parts give E_mu q=1/4, hence E_mu g=0. Set Mj=E_mu g^j.
Subject to the domain passage below, k[h'']=0 and MARKOV (6.8) give
E_h(g)=8M2. All prime powers and pole terms stay present; the tau moment is
zero by parity. Constants have zero jump energy.

For centered g in L3(mu), with entropy defined as
Ent_mu(s)=int s log s−(int s)log(int s),

    Ent_mu((1+epsilon g)^2)
      =2 epsilon² M2+(2/3)epsilon³ M3+o(|epsilon|³).

Indeed phi(u)=(1+u)² log((1+u)²), with 0 log0=0, has Taylor coefficients
2,3,2/3 through degree3. Its remainder divided by |u|³ is bounded on R
and tends to zero at zero (also finite at u=−1 and infinity). Dominated
convergence applies. The normalization term is
(1+epsilon²M2)log(1+epsilon²M2)=epsilon²M2+O(epsilon⁴).
The proposed LSI right side is exactly 2epsilon²M2. M3>0 would therefore
contradict it for sufficiently small positive epsilon.

## Domain passage (root proof candidate)

For x>=0 put t_n=pi n²exp(2x). The first positive theta summand bounds h
from below, since t_n>=pi>3/2. Differentiating any fixed number of times
multiplies its Gaussian by a polynomial in t_n. Ratios of n>=2 terms to
the first are bounded by polynomial sums times exp[-pi(n²−1)exp(2x)].
Thus q=O(exp(4|x|)), q'=O(exp(6|x|)); h and h q² decay faster than every
exponential. In particular q belongs to Lp(mu) for every finite p.

Choose one smooth even cutoff chi and set chi_R(x)=chi(x/R), equal1 on [−R,R], zero outside [−2R,2R],
bounded by1, with all fixed derivative orders uniformly bounded for R>=1. Put q_R=chi_R q.
For a shift s, the differences of q_R are dominated by

    |q(x+s)−q(x)| + |q(x)| min(C|s|,2).

For 0<s<=1, the derivative bound on q makes the square of this expression
at most C s² exp(C|x|), integrable against h(x)h(x+s)dx. Multiplication
by j(s)=O(1/s) is integrable at zero. For s>=1, use
|a−b|²<=2|a|²+2|b|². Both resulting convolutions of hq² and h are
O_A(exp(−As)) for every A>0: bound each factor by C exp(−2A|x|), use
|x|+|x+s|>=s, and absorb the remaining polynomial in s.
The arch tail is integrable and the complete prime series is dominated by
C_A sum_{n>=2}(log n)n^(−A−1/2), choosing A>1/2.

These bounds also dominate differences of q_R−q. Dominated convergence
therefore gives E_h(q_R−q)->0, as well as L2/L3(mu) convergence. The source
tests hq_R=chi_R h'' converge to h'' in the weighted derivative topology
used in CONFINE (1.3)-(1.6); hence their k forms tend to k[h'']=0.
Passing MARKOV (6.8) to the limit proves E_h(q)=8Var_mu(q).
The same argument applies to F=1+epsilon g and its cutoffs: hF is a fixed
linear combination of h and h'', and the entropy passage is dominated by
C_epsilon(1+|q|³). Consequently a compact-test LSI would also apply to F.
No positive global realization of the original signed k form is assumed.

## Explicit cubic sign: interval lower bound

Write a=h''−h/4, so M3=int_0^infinity cosh(x/2)a(x)³/h(x)² dx.
Differentiation gives exactly

    h_n=8t_n(2t_n−3)exp(x/2−t_n),
    a_n=16t_n(4t_n³−28t_n²+41t_n−9)exp(x/2−t_n).

For t>=7, the cubic bracket is positive, because
4t³−28t²=t²(4t−28)>=0 and 41t−9>0. Therefore omitted n>=5 numerator
terms are positive for x>=0; and the whole spatial integrand is nonnegative
for x>=1, where even t_1>=pi exp(2)>7.

For 0<=x<=1, t²exp(−t) decreases for t>=pi*25, giving

    0<=h−sum_{n=1}^4 h_n
      <=2 exp(1/2)16pi²5^4 exp(−25pi)=:eta.

The geometric factor2 is valid because successive n^4exp(−pi n²) terms
have ratio <=(6/5)^4exp(−11pi)<1/2. eta is about2.53e−29.
The function a↦a³ is increasing also for negative a. Thus replacing a
by its first four terms and enclosing the actual positive h between its
four-term sum and that sum+eta produces a valid LOWER bound, regardless
of the sign changes in a. The omitted spatial tail is nonnegative.

`../thetagrade_2026-10-28/entropy_cubic_lower.py` uses Arb boxes on 2000
equal cells in [0,1], dps50; it bounds the integral by interval ranges,
not floating quadrature or precision agreement. Its lower endpoint is
greater than178767, in particular M3>100000 if the above reduction is valid.
JSON records the precise enclosure. The printed [2e5 +/-2.13e4] is a
coarse enclosing display; the lower endpoint is separately serialized.

This would rule out the proposed sharp LSI, while leaving the possibly sharp
Poincare bound E_h>=8Var and the NOESCAPE target open. A weaker LSI constant
is not excluded. No cofinal source gain or RH proof is claimed.

## Independent numerical/analytic sign review

A read-only reviewer independently reran the script and reproduced JSON bytes,
checked derivative coefficients, both positive tails, the geometric bound,
interval coverage and signed cubic monotonicity. No material finding. This
pass supports the displayed literal integral >100000; normalization/domain
passage are reviewed separately. SHA256 script:
df1c071994a0e927f3221a501d37eede7b11a3ef591f1c63bfbb472236d12cf3; JSON:
54b76228826c21ee402d7876b705c5659de29ae8e49faf6f79c39465650bdae8.

## Independent domain review and conclusion

The same read-only reviewer checked probability normalization and the full
cutoff argument separately. No mathematical defect was found; the requested
clarification that chi_R is a standard scaled smooth cutoff was incorporated
above, so every fixed derivative is controlled. The energy argument retains
all prime powers and the archimedean singularity; entropy converges by L3
domination. No positivity of the signed source form is assumed.

Conclusion (bounded PAPER, conditional only on the cited inherited identities):
the global LSI Ent_mu(F²)<=E_h(F)/4 is FALSE already on even smooth compact
tests. Strict violation for the noncompact perturbation survives sufficiently
large cutoffs. This is KILLED(shape) for that particular entropy supplier.
It is not a finite-carrier/cofinal counterexample, not a rejection of even
Poincare E_h>=8Var, and not a result proving or refuting RH.
No new message was sent to the thinking Proshka; compare this independent
result against his forthcoming ENTROPY verdict before the next question.
