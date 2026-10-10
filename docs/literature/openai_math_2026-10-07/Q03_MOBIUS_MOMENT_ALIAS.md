# Alias return: actual Mobius joint moment

2026-10-10. No new theorem admitted; RH/SP/MB34 OPEN, CF22 unchanged.
The paid replacement in Q03_SMOOTH_GCD_PAIR_TEST.md removes r_Y at
admissible cost but leaves the long Mobius moment. We need cancellation
across original character rows, uniformly in every common profile and mask.

Target: E_M=sum_(qa<=P,u sixthfree) rho(qu/U)|L^(-1/2)
sum_n mu(n)nu(n)chi_n(u)^eps 1_((n,a)=1)W(qn/L)|² <= H U^(-1/200+epsilon)
with the original height factor, L in [U^(r-.01),U^r], r in [1.12,1.13],
H=UP^6 and p=log_U(P)=(r(1+1/10000)-1)/6. Source: Q2 §2.2,
Q3 SI.5/SI.35 and the paid replacement note. P/M inputs remain conditional.
Negative control: a bound for an L-weighted polynomial does not bound the
bare polynomial on rows with small or zero L-values. Dividing loses control.
UNVERIFIED search rewrites: reciprocal-L mean square; mollifier Gram bound.

Three shelf dictionaries (Gram/reciprocal L; mollifier/sparse power-free
family; multiplicative chaos/arithmetic covariance) returned INCOMPLETE
because semantic freshness failed. Exact corrected runs are in the adjacent
Q03_MOBIUS_ALIAS_SEARCH.json. An initial misplaced option became query text;
those exploratory runs are not the corrected search evidence. No absence claim.

## Primary candidate A — conditional analogue, not an import

Gao–Zhao, arXiv:2212.09241v1, Theorem 1.1: quote “assuming the truth of GRH”.
https://arxiv.org/html/2212.09241v1 ; fetched HTML341881bytes,
SHA2561018ea2373677751af391002445938b717a186e69cb14dcf4954a63201388ca0.
The quadratic integer Mobius mean square has main size XY and errors
X^(1/2+epsilon)Y^(3/2)+XY^(1/2+epsilon). Lemma2.6 supplies a GRH-dependent
reciprocal-L bound at 1/2+epsilon; §3.2 and §3.4 Eq3.19 spend it after
Mellin/Poisson transformations. This is the decisive unproved input for us.
Hypothetical mapping X=U,Y=L, dividing by L and paying P, gives
P[U+sqrt(UL)+U/sqrt(L)] times losses. Its worst target margin is329/9375,
so size alone would suffice. This is NOT a transfer: quadratic integer
characters differ from sixth-free Eisenstein sextic rows, masks and twists.
Also the source asymptotic dominance range Y<X is not our L>U, though its
displayed error can still be tested as an upper-bound budget. GRH cannot be
imported into an RH proof. Replacing pointwise inverse bounds by averages
would still require justified contour shifts and all crossed poles.

## Primary candidate B — weighted short analogue

David–de Faveri–Dunn–Stucky, arXiv:2410.03048v2, Remark1.9:
quote “The mollifier length”. https://arxiv.org/html/2410.03048v2 ;
fetched HTML3416063bytes,
SHA256b79f46cd94f4a6de3f18babd3140b4e761735a378756be42ba76558876a361ae.
Equations1.25–1.26 permit asymptotic mollified second moments at length
X^(1/6-delta). The family is cubic over Eisenstein integers with squarefree
conductors and the moment includes |L(1/2,chi)|². Setting X=U would require
our length L>U in place of that short mollifier; the character order and row
support also differ. Removing the L-weight requires a lower/inverse estimate,
which is not supplied by positive-proportion central nonvanishing. This
candidate is a partial mechanism, not an upper bound for our bare moment.

## Local OpenAI candidate — same coefficients, insufficient range budget

Pinned adc7f1241, The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex,
lines665–685, Proposition thm:ms; source SHA256
 d9a8f15aa770cf883d0eabd2b775fad694ce20b44cba7928f5c0c9a6d8750d4d.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex
Quote: “For every fixed”. It states sum_(Nu<=D^(1+theta))|A_u(D)|²
<< D^(2+theta+epsilon), with 0<theta<=1/10, fixed nu,S and finitely many
profile derivatives. A_u uses the actual mu(n)nu(n)chi_n(u) coefficients.
Putting D=L, dominating the U annulus by that ball, and dividing by L
gives L^(1+theta), before amplifier counting. Even granting uniform masks,
P L^(1+theta) misses H U^(-1/200) by at least559/37500 in exponent,
already at theta approaching0. Fixed-S constants do not supply growing
amplifier masks. This is verified statement content, not certification of
the manuscript's proof; no stronger consumer bound follows by restriction.

Next discriminator: locate a source-faithful averaged reciprocal mechanism
with justified poles, or a direct long-polynomial joint estimate. Stop if it
merely assumes moving-family nonvanishing or divides by uncontrolled L-values.
No Q4 sent; completed Q3 is not polled. No full consumer gain claimed.
