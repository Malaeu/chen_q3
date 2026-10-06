# Growth answer8: small-divisor cancellation and surviving Type-II sign

Source: PROSHKA_SMALL_DIVISOR_INLINE_2026-10-06.md; exact question8 in
SIGNED_PACKETS_AUDIT_2026-10-06.md. Same phase, full original complex carrier.

## Accepted PAPER result

U=ceil L. The exact Vaughan split uses lambdaI, lambdaII and kappa_U
as in (1)–(2), retaining every prime power and both continuous pole terms.
The new quadrature input is a centered integer sum-minus-integral bound:
for Y>=4U², q<=U², Y<=Z<=min(2Y,m), |t|<=Omega=2pi m/L,
error <=100(1+sqrt Omega)/sqrt Y, and the log-weighted version costs 300L.
Joint d,h from this single signed primitive give
 ||C_I,[Y,Z)||<=400 M_(U,L)(1+sqrt Omega)/sqrt Y,
 M_(U,L)=3UL+U²log(2U).
On X=floor(m/L^8), this is <=40000 L^(11/2)log(2L), in the ORIGINAL norm,
including all actual Schur-corrected vectors J_r v.

For Y0=ceil sqrt m the exact whole-carrier decomposition is
 H_m(r)=rI-C_II,[Y0,m]+F_m,
 ||F_m||<=Delta_m<=10^6 m^(1/4)L^(3/2)log(2L) eventually.
This is a REMAINDER budget, NOT a quarter-power negative-bottom bound:
C_II is not estimated and remains signed. Retaining D_arch gives (13),
including the positive-sign 2(R+R*) term (not asserted positive as a form).

With the ACTUAL regular block A_r and cross block B_r,
 f=J_r v=i_E v-i_R A_r^{-1} B_r v, r>epsilon_m,
 ||P_R C_II f-r(f-v)||<=Delta_m ||f||.
The exact Schur value differs from
 r||v||²-Re<v,C_II J_r v>
by <=Delta_m ||v|| ||J_r v||. No contraction of J_r is assumed.
C_II is the endpoint Hankel pairing (16)–(19), all cutoff atoms retained.
Alpha_U has an exact bounded sawtooth primitive rho_U, |rho_U|<=U.
The prime-weighted flux (21) and compensating density (22) remain OPEN
TOGETHER. Free differentiation incurs Omega and loses the desired bound.
Same-frequency multiplicative Cauchy differencing has zero curvature in a;
this stalls that particular use of the quadrature lemma, not Type II itself.

## Independent check and source readback

growth_symbol_attempt checked §§1–3 once: Vaughan, kappa, Euler–sawtooth
low-frequency IBP, high-frequency constants, partial summation and exact
joint matrix transfer. Pass conditional on the primary second-derivative
lemma. Root then read Arias Lemma5 and proof and Kedlaya Eq18.2.1 directly;
the cited hypotheses and constants match. Source map in
../../literature/small_divisor_2026-10-06/README.md.
causal_algebra_audit checked §§4–7 once, conditional on §§1–3. Pass with one
necessary endpoint clarification: in (21), an INCLUDED lower cutoff ell
uses rho_U(ell^-); an excluded lower cutoff uses rho_U(ell). The upper
cumulative is right-continuous and its W_b value is zero at bu=m.
This preserves any atom ab=Y0. Formula (22) is asserted only for
x>=Y0>=4U², not below U². Exact capture left unchanged.

SP/G1/G3/RH OPEN; no new whole-matrix floor or common good-cell sequence.
No Lean run. The next attempt retains the same signed arithmetic mechanism.

## Own attempt before question9: additive shifts and exact CRT correlation

For integer U>=1, k>=1, and [A,B) with A>U, expand
 alpha_U(n) alpha_U(n+k)
 =sum_{d,e<=U} mu_M(d)mu_M(e) 1_(d|n,e|n+k).
A pair contributes iff gcd(d,e)|k; then it is one residue class modulo
q=lcm(d,e). Therefore, with
 R_U(k)=sum_{d,e<=U,gcd(d,e)|k} mu_M(d)mu_M(e)/lcm(d,e),
 |sum_{A<=n<B} alpha_U(n)alpha_U(n+k)-(B-A)R_U(k)|<=U².
Each progression has discrepancy at most1 on every intermediate half-open
interval. Consequently for complex C¹ F,
 |sum alpha_U(n)alpha_U(n+k)F(n)-R_U(k) int_A^B F(x)dx|
 <=U² (|F(B)|+int_A^B |F'(x)|dx).
The looser bound with 2sup|F| plus variation is also valid.
This is an elementary exact source fact, not a prime-correlation conjecture.
It does not say that R_U(k) is small or has a useful sign.

Unlike multiplicative differencing, additive differencing produces
 theta(a)=t log((a+k)/a),
 theta'(a)=-tk/[a(a+k)],
 theta''(a)=tk(2a+k)/[a²(a+k)²]>0 for t,k>0.
On each compatible progression a=r+qu its curvature is multiplied by q².
Negative t is handled by conjugation. This removes precisely the zero-
curvature obstacle in answer8(23), but does not estimate the full Type-II
form: the exact product cutoffs, cross-frequency terms, prime-power weights,
continuous compensator and J_r v must still be paid jointly.
Using only the weighted-discrepancy variation bound would again incur a
frequency factor. The intended test keeps the CRT progression sums and
estimates their oscillation BEFORE summing them, retaining the main density.

growth_symbol_attempt independently checked this one bounded root lemma:
CRT compatibility/counting, partial summation, curvature sign and q² scaling.
No error found. No Type-II signed bound, improved floor or RH claim follows.

## Exact question9 sent in the same living chat

Continuation 9/10, SAME full CCM negative-bottom-growth phase. Answer8 audited once in disjoint blocks; root verified Arias de Reyna arXiv2407.02094v1 Lemma5 p4 A=2.79368380731<3 and Kedlaya chap-bombieri2 Eq18.2.1. Accepted: coherent Type-I quadrature, polylog40000L^(11/2)log(2L) on X=m/L8 strip; exact all-range H=rI-C_II+F with ||F||<=Delta=O(m^(1/4)L^(3/2)log(2L)). This is only a remainder, NOT a quarterpower floor. Actual J_r and its norm retained, Type-II flux+compensator OPEN. Endpoint clarification: in (21) an included lower ell uses rho_U(ell^-), excluded lower uses rho_U(ell); upper cumulative right-continuous, W_b(m/b)=0. Density(22) only on x>=Y0>=4U².

Own attempt, independently checked, attacks the PRECISE zero-curvature obstruction (23), not a new route.
For integers U,k>=1 and [A,B) with A>U, alpha_U(n)=-sum_{d<=U,d|n}mu_M(d).
Expanding alpha_U(n)alpha_U(n+k), CRT gives one residue class modulo q=lcm(d,e) iff gcd(d,e)|k. Thus
sum_{A<=n<B}alpha_U(n)alpha_U(n+k)=(B-A)R_U(k)+E, |E|<=U²,
R_U(k)=sum_{d,e<=U,gcd(d,e)|k}mu_M(d)mu_M(e)/lcm(d,e).
For complex C1 F the weighted discrepancy from R_U(k)int_A^B F is <=U²(|F(B)|+int|F'|); all intermediate half-open cutoffs exact. No smallness/sign of R_U(k) asserted.
ADDITIVE differencing at fixed b gives the same-frequency phase theta(a)=t log((a+k)/a),
theta''=tk(2a+k)/(a²(a+k)²)>0 for t,k>0.
On a compatible progression a=r+q u, curvature is q² theta''; negative t by conjugation.
So additive shifting avoids the exact zero curvature of multiplicative b/b' differencing. Naively bounding weighted discrepancy by variation would again lose Omega; retain progression sums and estimate oscillation first. This source lemma is proved, NOT a global Type-II or Schur estimate.

Please EXECUTE this additive-shift/CRT test on the surviving signed Type-II endpoint pairing (19), keeping the continuous compensator (22) and prime-weighted flux together. Use the actual regular constraint (14) on (v,J_r v); pay all cross-frequency terms, product cutoffs, prime powers, trace terms and ||J_r v||. Do not replace the two endpoint restrictions by independent profiles. Optimise a concrete shift range and bound its full error. The result should be a new proved source-specific estimate that advances the signed pairing, or a precise failure of THIS attempted additive mechanism with its irreducible surviving term. Merely writing a positive-curvature identity, an averaged scalar bound with no full carrier transfer, or restating the open sign does not meet the target.

Keep the existing Type-I budget; improving only its remainder exponent while leaving the large signed complement untouched is secondary. No blind packet norm envelopes, no fixed-positive-space transfers, no RH assumption, no independently intersected good-cell sequences. Same full K_m and original m=N,L=log m schedule. SP/G1/G3/RH remain OPEN. Return proof with exact consumer and original-norm errors; no plan-only response.
