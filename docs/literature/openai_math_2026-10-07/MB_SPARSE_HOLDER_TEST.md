# Sparse-image Holder test for MB.34

2026-10-09. Independent read-only q05_moment_audit PASS for H1–H4. RH/SP OPEN.
Consumer: MB.29–34 in PROSHKA_VERDICT_MIXED_BOUNDARY_ROLLOVER_Q01.md.
The mixed boundary returns the original positive sparse energy; this test
asks if a stronger RAW-row moment would exploit its small support.
It does not assume rows are independent or replace arithmetic coefficients.

Use exactly Omega(v), V_H and E(L) from MB.24–28. Injection gives
0<=Omega<=||rho||_infty and sum Omega<=C PU. Put
H=U^h, h=r(1+c0), p=(h-1)/6, P=U^p, c0=1/10000.
All rows, units, S restrictions and the common W are unchanged.

For fixed k>1, Holder on the finite raw row set gives

 E(L)<=C_(rho,k)(PU)^(1-1/k)
                  (sum_(v in V_H)|M_v(L;W)|^(2k))^(1/k). H1

Suppose, as an UNPROVED supplier, that the last raw moment is
 <=H U^(kappa+epsilon)(1+T1)^A,
uniformly for upper scales and every common derivative profile.
Then using H/(PU)=P^5 exactly,

 E(L)<=H U^([kappa-5p(k-1)]/k+epsilon)(1+T1)^(A/k). H2

For a target HU^(-eta+epsilon), a strict sufficient budget is
 kappa<5p(k-1)-k eta.                                  H3
A strict margin leaves room for the downstream losses. This bounds the
positive E first, so the existing common-profile Sobolev return applies;
it is not a Sobolev argument on an arbitrary signed D_off.

For k=2 and eta=1/200 the allowable raw fourth-moment excess is
 kappa<5p-1/100.
Across r in[28/25,113/100] its minimum is6757/75000 (~.0900933).
At r=5617/5000 the threshold is1858539/20000000 (~.09292695).
A hypothetical fourth moment <=H U^epsilon would more than suffice:
its gain relative H is5p/2, at least7507/150000 (~.0500467).
No such moment estimate has been proved here.

## What the available inputs actually imply

The separate source raw SECOND moment gives sum|M|²<=H U^epsilon.
Direct annular counting gives |M|²<=C_W L: there are O(L) terms,
each bounded, with normalization L^(-1/2). Consequently

 sum|M|^(2k)<=C L^(k-1) H U^epsilon.                   H4

For L=U^ell this has kappa=(k-1)ell. On the upper scale interval
ell>=r-1/100, ell>5p. Thus substituting H4 into H1 is worse
than the original raw second moment; it produces no power saving.
Large k does not repair the comparison: the excess is
(k-1)(ell-5p)+k eta>0.

Even a general nonnegative energy array can put all its raw L1 mass
on the sparse support while respecting a sufficiently large pointwise
cap. This is a negative control for density-plus-second-moment reasoning,
not a counterexample for the actual Mobius polynomial. Any successful
supplier must exploit its arithmetic or bound a stronger actual moment.

## Nearby source theorem is not the required supplier

Pinned paper.tex S707–713 defines plain S_psi without mu and inverse
M_psi with mu. The fourth-moment lemma at S12526–12583 estimates
|S_psi(n1;W1)S_psi(n2;W2)Q|², with no length restriction when Q=1.
Its no-slot rows are R0, whose inducing characters are nonprincipal.
H1 instead needs all raw rows, including the complementary principal
family. It is not the raw fourth moment of M in H1. An inverse or coefficient
transfer is an additional unproved step; its cost cannot be omitted.

## Bounded alias return (long_positive_alias, root source reread)

Three shelf dictionaries were queried: sparse polynomial-image restriction
large sieve; sixth-power-free core twisted moments; centered arithmetic
covariance/relative large sieve. All returned ASK_STATUS: INCOMPLETE due
to q3_docs freshness, not literature absence. No exact supplier admitted.

Both local candidates below use pinned paper.tex, SHA256
42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3:
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex

Candidate1, lemma plain S12526ff: "There is no restriction on the bounded
nonnegative lengths" in the no-slot case. Map Z=U,m=h,n1=n2=ell would
have kappa=0 if the coefficients and rows mapped. They do not: S lacks
mu, and R0 omits principal rows. Classification: conditional interface
shape only, two missing hypotheses, NOT an imported fourth moment.

Candidate2, sextic large sieve S4707ff: "The sequence is fixed independently
of the row"; sum_sf k |sum_sf n c_n chi_n(k)|² is bounded by
(KD)^eps [K+D+(KD)^(2/3)] sum|c_n|².
The coefficient c_n=L^(-1/2)mu(n)nu(n)W(qn/L) is admissible on
squarefree good rows, but this theorem alone does not cover every
sixthfree element row or center against lambda. Even the favorable
squarefree-row diagnostic K~U,D~L has cross exponent2(1+ell)/3,
well above target h-eta near1.12. This is a weak available upper budget,
not a lower bound on the actual sum and not a route impossibility.
Squaring M for a fourth moment additionally creates nonsquarefree
product coefficients; no coefficient-preserving reduction is supplied.
Classification: conditional partial mechanism, not a supplier for H3.

Root reread S699–719, S4690–4765 and S12477–12585. Source claims remain
conditional on their unverified analytic proofs; only mapping is checked.
The generic concentration control above explains why support density alone
cannot bridge either missing coefficient/row hypothesis.

Decision: H3 is an exact candidate interface,
not evidence of an available theorem. Do not treat the new fourth moment
as easier merely because it would imply MB.34. No new Pro question sent.
