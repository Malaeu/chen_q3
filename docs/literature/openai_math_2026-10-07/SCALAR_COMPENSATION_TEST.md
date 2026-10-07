# Exact scalar prime-slot transplantation — 2026-10-07

Status: own finite identity independently checked by growth_symbol_attempt; boundary, prime-power and Laplace checks PASS. No global Q3 gate changes. This tests a deliberately simple scalar analogue, not the original cubic-theta compensation theorem. Source operation: OpenAI qrh78 paper.tex 6890–6920; precise local replacement 8670–8740, pinned URL and hash in sources.json.

## Object and normalization

Set F(t)=sum_{n>=2} Lambda(n)/sqrt(n) (t-log n)_+, with all prime powers retained; F(t)=0 for t<=0. For an arithmetic coefficient sequence a, define

M_p a(n)=1_{p|n} a(n),  T_p a(n)=1_{p|n} a(n/p).

After weighted ramp summation, T_p acts as p^(-1/2)F(t-log p). M_p selects the powers of p when acting on Lambda. For distinct primes p,q, M_p commutes with T_q, and both sets of operators commute internally. No claim that M_p and T_p commute at the same prime is needed.

The proposed scalar compensation is C_S=product_{p in S}(M_p-T_p), for a finite set S of distinct primes. This is NOT a transcription of the metaplectic coefficients: the original paper has three scales, target characters, c*n^3 coefficients, exact Euler numerators, and a surviving sextic-character factor. Here the operation's entire output can be computed.

## Exact finite calculation

Let K=|S|, P=product S, and let F_outsideS retain only q^j with q not in S. Then, for every real t,

C_S F(t)=(-1)^K P^(-1/2) [F_outsideS(t-log P) - (log P)(t-log P)_+].       (1)

Proof: expand the product into marked and shifted slots. A term with at least two different marks annihilates Lambda, since an integer divisible by two distinct primes is not a prime power. The empty-mark term is (-1)^K T_P Lambda. The singleton-p term is (-1)^(K-1) T_{P/p} M_p Lambda. For n=P q^j, q outside S, only the empty-mark term remains with coefficient (-1)^K log q. For n=P p^j, p in S, the empty-mark and corresponding singleton cancel. At n=P the singleton terms sum to (-1)^(K-1) sum_{p in S} log p, since Lambda(1)=0. These are all supports. Weighting by n^(-1/2) and the ramp gives (1), including t=log P where both sides vanish. For S empty, (1) is F=F.

In particular, one prime gives

(M_p-T_p)F(t)=p^(-1/2)[(log p)(t-log p)_+ - F_outside{p}(t-log p)].          (2)

Mixed prime products enter with the opposite sign; they are not a free positive reserve. The operation removes the selected local powers but leaves the whole unselected prime-power source, translated and scaled.

## Mellin/Laplace discriminator

For Re s>1/2, absolute convergence gives L F(s)=(-zeta'/zeta)(s+1/2)/s^2. Writing r_p=p^(-(s+1/2)), equation (1) becomes

L(C_S F)(s)=(-1)^K P^(-(s+1/2))/s^2
  * [(-zeta'/zeta)(s+1/2) - sum_{p in S} (log p)/(1-r_p)].              (3)

Indeed the removed local prime powers contribute log p*r_p/(1-r_p), and the boundary ramp contributes log p, totaling log p/(1-r_p). This boundary term is essential.

For fixed finite S and Re s>0, the finite correction is holomorphic because |r_p|<1; P^(-(s+1/2)) is nonzero. A hypothetical nontrivial zero rho with Re rho>1/2 produces a pole at s=rho-1/2. Neither the finite correction nor the nonzero multiplier cancels it. This does not assert such a zero exists. It says the tested algebra preserves the offending singularity unless a new analytic estimate is proved.

For moving S=S(t), (1) remains pointwise exact but there is no fixed Laplace multiplier (3). Selecting many primes can make F_outside small while losing the original source in the inverse operation. No uniform inverse estimate, target preservation or scalar-reserve improvement follows from that pointwise fact.

## Decision

The naive scalar marking-minus-dilation transplant supplies no new source bound. It is STALLED as a standalone route: the output is exactly the old unselected source plus an explicit boundary. It does not refute the original metaplectic method or other compensators. The necessary extra ingredient is a genuine character-bearing auxiliary family with both low and high estimates and a nonvanishing detector of the original source, as in the original common-signal proposition. This is more structure than prime-power support alone.

Next source question: can the paper's detector/low-high estimates be retuned from sigma0=7/8 toward 1/2? First inspect the endpoint exponent constraints and identify an explicit inequality that fails, rather than sending Proshka a generic request to improve the exponent. Preserve the full Q3 route as OPEN; no import or proof claim follows from this test.

## Fixed-geometry endpoint obstruction (source-level calculation)

The paper explicitly identifies C_II(s)=s-11/16 and C_II(7/8)=3/16 (paper.tex 8637–8647). Its available low estimate is Z^(3/16+epsilon). The common-signal contract requires a low bound Z^(C(sigma0)+omega) with 0<omega<beta_*-sigma0 (400–430).

To obtain that contract from the AVAILABLE estimate alone one needs

3/16+epsilon <= sigma0-11/16+omega, hence sigma0+omega >= 7/8+epsilon.

But the contract also requires sigma0+omega<beta_*. Consequently this particular use of the existing low estimate cannot address beta_*<=7/8, regardless of a formal substitution of a smaller sigma0. This is a limitation of the available upper estimate, not a lower bound on the true probe and not an impossibility theorem for new estimates.

At unchanged C(s), reaching sigma0=1/2 with arbitrary small margins would require low exponent approaching -3/16 rather than +3/16: a 3/8 power improvement. New geometry changes C as well, so the invariant quantity to improve is low exponent minus the affine constant in C, currently 7/8. High-side approximation and nonvanishing Euler correction must remain valid simultaneously. Optimizing only the endpoint high-side polynomial cannot by itself overcome this low-side constraint.
