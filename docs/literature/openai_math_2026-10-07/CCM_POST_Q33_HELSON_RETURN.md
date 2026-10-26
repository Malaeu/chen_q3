# Post-Q33: product-index Helson entrance and complete norm return

2026-10-26. Root derivation; bounded independent audit PASS for H1/H2 and the auxiliary PSD obstruction. Original full
CCM, N=m,L=log m,M=floor(m^epsilon), original three-contact P unchanged.
No RH, C5 or new full exponent claim. One bounded product-space attempt.

## Shelf and exact target

The read-only shelf comparison located existing ratio/Gram, reflection,
Selberg-product and counting-lattice attempts: CCM_FIXED_PRIME_COMPRESSION_TEST.md,
CCM_COMPOSITE_REFLECTION_TEST.md, CCM_Q20_SELBERG_PAIR_ATTEMPT.md, and Q08 §6
(PROSHKA_VERDICT_FULL_CCM_RAMANUJAN_Q08.md). Their repeats are not counted as
fresh failures. Historical semantic searches are INCOMPLETE, not global absence.
The new narrow external dictionary is multiplicative Hankel/Helson forms.

Let Z>=2, Z<m, b_Z(n)=log(n)lambda_Z(n)^2/C_Z^2 be the actual finite model.
Keep the old exact target C_comp=sum_{Z<n<=m, composite} b_Z(n)h(n),
h(n)=n^(-1/2)P Q_M(log n)P. Q08 and the20.10 weighted-LCM improvement already
pay A+C_comp; the signed lower bound of C_comp remains OPEN.

## Primary source and failed positivity entrance

Perfekt--Pushnitski, On Helson matrices: moment problems, non-negativity,
boundedness, and finite rank, arXiv1611.03772v2, Theorem3.3(i), printed p7.
URL https://arxiv.org/pdf/1611.03772v2 . Local source
sources/perfekt_pushnitski_1611.03772v2.pdf, SHA256
8ee9b9d91e9010ff823853e05b38295d8c7f1764290a3e559ede10fee08e0f47.
Short quote: "if and only if there exists a measure".
Under polynomial coefficient growth, the theorem characterizes positivity of
H(alpha)=(alpha(uv)) by a positive multivariate moment measure. Its positivity
hypothesis/conclusion is substantive; nonnegative entries alone do not imply it.
This statement was read from the primary PDF; its full proof is not re-audited.

Test alpha(n)=1_{Z<n<=m, composite} b_Z(n)/sqrt(n). For distinct primes Z<p<q,
q²<=m, all p²,pq,q² are rough and lambda_Z/C_Z=1. The principal p,q block is

    [ 2log(p)/p,          log(pq)/sqrt(pq) ]
    [ log(pq)/sqrt(pq),   2log(q)/q        ].

Its determinant is exactly -(log(p)-log(q))²/(pq)<0. Explicit finite case:
Z=2,p=3,q=5,m=26. No top-cutoff discrepancy or omitted prime power explains it.
Therefore direct positive-moment import for this auxiliary product matrix fails.
The integer-index test vector is NOT an original-P vector: this is no C5/CCM
counterexample and does not exclude a bounded signed Helson method.
Existing SymPy checked the determinant algebra and actual lambda/C=1 at9,15,25.

## Exact source-preserving product-index return

For c=Pc, f=F_Mc zero-extended from [0,L], define the REAL correlation

    rho_f(n)=2 Re integral_0^(L-log n) conjugate(f(t)) f(t+log n) dt.

It retains both times and every complex mixed Fourier coefficient; |rho|<=2||c||².
The source is c*C_comp c=sum alpha(n)rho_f(n), including all proper powers.
Let d_*(n)=tau(n)-2 count ordered factor pairs u,v>=2; it is positive precisely
on composite integers. Use indices2<=u,v<=floor(m/2), and define

    H_uv=alpha(uv),
    B_uv=1_{Z<uv<=m, composite} rho_f(uv)/d_*(uv).

Both are real symmetric. Every supported n occurs exactly d_*(n) times, so

    Tr(H B)=sum alpha(n)rho_f(n)=c*C_comp c.             (H1)

No prime is inserted, no factor pair deleted, and the hyperbolic boundary uv<=m
is literal. At n=m, rho_f(m)=0, hence the boundary atom remains zero.
B depends quadratically on the actual original-P vector; it is not an arbitrary
independent coefficient vector or an unproved isometry.

## Full price of the norm completion

Since |c_q(n)|<=phi(q), |lambda_Z(n)|<=Z; C_Z>=1. Therefore
0<=alpha(n)<=Z²log(n)/sqrt(n). The finite product matrix obeys

    ||H||_HS²<=Z^4 L² sum_{uv<=m}1/(uv)
               <=Z^4 L²(1+L)²,
    ||B||_HS²=sum_{Z<n<=m composite}rho_f(n)²/d_*(n)
               <=4m||c||^4.

Hilbert--Schmidt Cauchy on the EXACT H1 consequently gives

    |c*C_comp c|<=2Z²sqrt(m)L(1+L)||c||².              (H2)

The matrix also has a Schur norm cap Z²L(1+L), using weights u^(-1/2),
but spending it requires a trace-norm estimate for B, not a free unit norm.
No such favorable additional estimate is supplied here.

At Z=floor(m^(epsilon/4)), H2 has exponent1/2+epsilon/2 with logarithms.
The inherited full A+C_comp return costs O_epsilon(m^(5epsilon/4)L²),
including small integers, proper powers, smooth model and every mixed divisor term.
Thus this completion yields A<=sP with

    s=2Z²sqrt(m)L(1+L)+O_epsilon(m^(5epsilon/4)L²),
    T_>R<=(s+b_div)P,
    PK_mP>=-(s+50L+8)P.

Keep the stronger old12sqrt(m) prime cap; H2 is not an improvement.
The divisor-short fee occurs once in T, not again in the direct K return.

## Decision and limits

The first decisive loss is separate HS payment of H and B in H2. H1 is a
faithful representation but not a new arithmetic estimate. The small auxiliary
operator norm does not survive as a small source bound without paying B.
The determinant excludes only direct PSD/moment representation of alpha(uv).
It does not exclude another source-dependent joint estimate or another lift.
Independent read-only q32_annulus_audit checked H1/H2, exact determinant, all
normalizations, original source return and primary Theorem3.3 statement. The
full external proof and inherited source facts were not re-audited. H2 even
loses a logarithm against direct triangle payment: no gain is claimed.
No Q34 sent. Next question, if needed, must name additional information about
the actual correlation matrix B and H jointly; simply asking that their pairing
be small would restate C5. This is one bounded attempt, not three alias repeats.

AUTOPSY: dropped=SIGN; note=product-space norm completion separates actual arithmetic and correlation matrices and retains half power; positive moment entrance also fails in a concrete auxiliary principal block.

## Follow-up: actual-P lower price of the separated HS certificate

Status: bounded independent PAPER PASS, conditional on inherited projection and model-mass inputs.
This checks whether H2 merely used an avoidably poor estimate for B.
It is part of the same attempt, not a second independent arithmetic attempt.

Fix a>0 and a nonzero real symmetric chi in C_c^infinity(0,a),
chi(a-t)=chi(t). Put u=chi''-chi/4, also symmetric and nonzero. Integration
by parts gives integral u(t)exp(±t/2)dt=0. For L>2a define

    f_L(t)=[u(t)+u(L-t)]/(sqrt(2)||u||_2), 0<=t<=L.

Its norm is1, every fixed derivative norm is bounded independently of L,
both exponential moments vanish, and it vanishes near both physical endpoints.
Direct substitution gives rho_f(L-a)=1. By translation continuity there is a
fixed0<h<a for which rho_f(s)>=1/2 whenever |s-(L-a)|<=h, for all sufficiently
large L (so same-side support cannot contribute in this range).

Use the original M=floor(m^epsilon) Fourier truncation and its three-contact P.
The existing sparse receiver projection/correction argument applies directly:
for fixed q>=2 the Fourier coefficients are O_q(L^(q-1/2)|j|^(-q)); the L2
tail and three normalized contact residuals are
O_q(L^(q-1/2)M^(1/2-q)). The exponential coefficient norm ratios are bounded,
and the original normalized constraint Gram matrix is >=I/2 eventually.
Thus normalized g_m in the original ran(F_M P) satisfies ||g_m-f_L||_2=o(1).
No whole-line/source change or auxiliary integer vector is substituted.
Unitary translations and Cauchy give uniformly in s

    |rho_g(s)-rho_f(s)|<=2(||g||+||f||)||g-f||=o(1).

Consequently rho_g(n)>=1/4 for integers n in
I_m=[m exp(-a-h), m exp(-a+h)]. The upper endpoint is strictly below m.
For fixed kappa=epsilon/4 and Z=floor(m^kappa), all such n exceed Z eventually.
There are N_m>=c_a,h m even composites in I_m. Since d_*(n)=tau(n)-2>=1,
Cauchy and the elementary sum_{n<=m}tau(n)<=m(1+log m) imply

    sum_{n in I_m, even}1/d_*(n)
       >=N_m²/sum_{n in I_m, even}d_*(n)
       >=c m/(1+L),
    ||B(g_m)||_HS >= c sqrt(m/(1+L)).                  (H3)

Thus the true norm of B, not just its prior bound, can retain half power on
actual original-P tests. This is a norm lower bound, not a negative CCM value.

To check the other factor does not vanish, use Q33's elementary mass estimate
mathfrak_b_Z=(2/kappa+o(1))sqrt(m) for kappa=epsilon/4. Removing all primes
costs at most W<=6sqrt(m), since b_Z(p)=log p for p>Z. Removing all n<=Z
costs at most2 Z^(5/2)log Z=o(sqrt(m)), by b_Z<=Z²log n.
Therefore the retained composite mass satisfies

    sum_n alpha(n)>=(2/kappa-6+o(1))sqrt(m).

Here kappa<1/128, so the coefficient is positive. The HS norm counts each
composite with multiplicity d_*(n)>=1. Cauchy over at most m integers gives

    ||H||_HS>=sum_n alpha(n)/sqrt(m)>=c_kappa>0.

Combining with H3 yields a lower PRICE for this separated certificate:

    ||H||_HS ||B(g_m)||_HS >= c_epsilon sqrt(m/(1+L)). (H4)

H4 rules out a vanishing-exponent all-P certificate obtained solely by
separately bounding these two HS norms. It does not lower-bound Tr(HB),
C_comp's spectrum or the source prime operator. The favorable cancellations
may still occur in their signed trace. No PNT error or RH assumption is used;
the elementary model-mass asymptotic is the inherited Q33 calculation.

### Support-aware refinement (same follow-up; independent bounded PASS)

H3 refers to the specified canonical B, whose entries can include alpha(n)=0.
It alone must not be used to exclude support pruning or other lifts.
A stronger support-aware test uses actual rough semiprimes and ordinary PNT.
Put a_-=exp(-a-h), a_+=exp(-a+h). Take primes

    m^(1/3)<=p<=2m^(1/3),
    a_-m/p<=q<=a_+m/p.

For all sufficiently large m, q>p>Z. Qualitative PNT gives at least
c m^(1/3)/L choices of p and uniformly at least c m^(2/3)/L choices of q
for each p: the q endpoints have fixed ratio a_+/a_->1 and their minimum
tends to infinity. Distinct pairs produce distinct integers because p is
the smaller prime. Thus I_m contains at least c m/L² such semiprimes.
They satisfy alpha(pq)=log(pq)/sqrt(pq)>0 and d_*(pq)=2 exactly.
The original-P rho_g remains >=1/4 there. Consequently even deleting all
zero-alpha entries leaves

    ||B||_HS>=c sqrt(m)/L.                            (H5)

More generally, any factor-pair matrix B' satisfying the coefficientwise
return sum_{uv=n}B'_{vu}=rho_g(n) for each supported n has
sum_{uv=n}|B'_{vu}|²>=|rho_g(n)|²/d_*(n). H5 therefore survives redistribution
among ordered factor pairs and addition of canceling entries. With the earlier
lower bound for ||H||_HS its separately paid certificate is >=c_epsilon sqrt(m)/L.
This excludes only that coefficientwise HS-return family; a different global
source-dependent factorization or the exact signed trace is not excluded.
PNT is used only for this support-aware certificate obstruction, not as a
favorable signed arithmetic estimate. H1/H2 do not require PNT.

The operator/trace-norm completion has the same obstruction: choose prime
indices p,q in [m^(1/6),2m^(1/6)]. All their products are rough and below m
for late cells. Each H_pq>=c L/m^(1/6), and PNT gives at least
c m^(1/6)/L such indices. The normalized constant vector on that principal
block proves ||H||_op>=c. Since ||B'||_1>=||B'||_HS, the global product
||H||_op||B'||_1 is also >=c sqrt(m)/L.

Independent read-only q32_annulus_audit checked the complete follow-up:
original-P test and uniform correlation, elementary canonical count, support-
aware actual semiprimes, coefficientwise redistribution and both global norm
products. Bounded PASS; ordinary PNT and accepted sparse projection/mass
inputs remain inherited, not re-proved. The scope correction is incorporated:
the even-composite argument alone does not survive zero-alpha pruning; the
semiprime argument does. No trace/spectral lower bound is inferred.

Decision: stop GLOBAL separate HS and operator/trace norm completion for this
coefficientwise product-index carrier. Localized joint estimates and other
factorizations remain open. One attempt with a strengthened obstruction,
not several new failures; no Q34 sent, no full CCM arithmetic gain.
