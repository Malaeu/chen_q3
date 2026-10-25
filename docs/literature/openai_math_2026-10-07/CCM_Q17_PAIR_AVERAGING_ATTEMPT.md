# Q17 own attempt: average the actual pair before absolute values

2026-10-25. Original N=m,L=log m,M=floor(m^epsilon), fixed
0<epsilon<1/32, SAME three-contact sparse P. Source: Q16 section7 and
CCM_RESTRICTED_PRIME_RECEIVER / CCM_SPARSE_BAND_RECEIVER. No new premise.
This is a bounded failed completion, not a new arithmetic exponent or no-go.

## Exact signed object

Fix a hypothetical zero w=delta+i gamma, 0<delta<1/2, multiplicity r.
Let g=g_w,k=g_wdagger be the separately normalized derivative-filtered
separators in the receiver. Write C(v)=integral conjugate(g(t))k(t+v)dt.
For a>=0 set f_a=exp(-i gamma a)tau_a g-exp(i gamma a)tau_(-a)k.
Define J(a;m)=sum_(n<=m) Lambda(n)n^(-1/2)[C(2a-log n)+C(2a+log n)].
Both signs, all prime powers, and the full complex phase are retained:

 S_m[f_a]=S_m[g]+S_m[k]-2 Re(exp(2i gamma a)J(a;m)).             (1)

The two self terms are O_w(1), uniformly in m. No absolute values have
been put on the mixed term in (1). The profiles are actual separators,
not the compact synthetic tests from Q16 section5.

## Positive translation averaging on one original cell

Put h=L/2-log L, choose 1<=T<=h/2, and average (1) over a in [h-T,h].
This is an average of quadratic forms, NOT the form of an averaged vector.
Define B_T=T^(-1)integral Re(exp(2i gamma a)J(a;m))da and
E_T=T^(-1)integral exp(2delta a)da. Exactly,

 E_T=exp(2delta h)(1-exp(-2delta T))/(2delta T).               (2)
 average S_m[f_a]=O_w(1)-2B_T.                              (3)

The phase stays INSIDE the integral. In particular this is not an
oscillatory integral with constant amplitude J. The conditional adverse
identity averages to -2r E_T, with no loss of its sign.

## Full original-P return, uniform throughout this average

Apply the original centered cutoff and Fourier truncation then P to each
f_a as a whole; denote the resulting padded vector z_(m,a). All translations
in the averaging interval are at least log L from the outer boundary.
Their fixed derivative L1 norms are uniform. Thus the receiver's estimates
are uniform in a, for one fixed integer q>1/epsilon+2. With Omega=2pi M/L:

 E_q=C_q[sqrt(m)Omega^(1/2-q)+Omega^(3/2-q)+Omega^(1-q)],
 rho_K=C_wq[m exp(-c_w L^2)+m Omega^(1/2-q)
       +sqrt(m)Omega^(3/2-q)+sqrt(m)Omega^(1-q)+E_q^2
       +sqrt(m)L^(q+1/2)M^(1/2-q)]=o(1).                  (4)

The last term pays all three contact corrections, including endpoint
and both exponential residuals. The prime form has the separate direct
return rho_S<=C_wq[sqrt(m)L^(q-1/2)M^(1/2-q)
                       +m^C exp(-c_w L^2)]=o(1),          (5)
using ||A_m||<=12sqrt(m). These bounds apply to the WHOLE pair, so include
all mixed terms; no individually reprojected-packet support is assumed.
Norms ||z_(m,a)||^2<=D_w remain bounded. The archimedean return is at most
D_w(50L+8), once. Since T<=h/2, E_T>=c_delta exp(2delta h)/h,
and hence (L+rho_K+rho_S)/E_T tends to zero. No small-divisor/Vaughan fee
is charged to this direct source. The exact full average satisfies,
conditionally on w,

 average z* K_m z=-2r E_T+o(1),
 average z* A_m z=2r E_T+O_w(L)+o(1),
 B_T=-r E_T+O_w(L)+o(1).                                  (6)

An INDEPENDENT arithmetic lower bound B_T>=-o_w(E_T) would therefore
suffice. Equation (6) is the adverse implication under a hypothetical
zero, not an independent supplier for that lower bound.

## Where this completion fails

Fixed double-exponential decay of C and its derivatives, together with
the inherited Chebyshev bound for the actual Lambda weights, gives
|J(a;m)|<=C_w exp(a) for a>=1. For example, partition log n-2a into unit
intervals; each interval has Lambda/sqrt(n) mass O(exp(a+v/2)), while
the weighted sum of sup |C(-v)| converges. The reverse-time term is
also included and bounded by the same estimate. Consequently

 B_T>=-C_w exp(h)(1-exp(-T))/T.                             (7)

Relative to the required signal (2), the displayed upper PRICE is

 C_w 2delta exp((1-2delta)h)
          (1-exp(-T))/(1-exp(-2delta T)).                   (8)

For every 1<=T<=h/2, the final fraction lies between 1-exp(-1) and
1/(1-exp(-2delta)). Thus this completed averaging budget retains the
exponential deficit uniformly in T. At T comparable to h it buys a
logarithm in both budget and signal, not a net power. It supplies only
average S<=O_w(exp(h)/T+1)+rho_S and
average K>=-O_w(exp(h)/T+L+1)-rho_S, still half-power in m.
This is NOT a lower bound on actual |J| or the spectrum, and does not
exclude a genuinely signed arithmetic estimate of B_T.

The older absolute PNT transfer exp(h-o(h)) is already rejected in Q16;
rewriting it by Stieltjes summation is not a second new attempt. The new
test here is positive translation averaging with its full signal returned.
No unproved pointwise prime error, ZF78, RH, or Mertens bound is imported.

## Concrete impasse and rollback for Q17

The first unpaid line is B_T>=-o(E_T), BEFORE (7), for the actual
zero-selective cross correlation. The profile phase is locked to gamma;
oscillation alone cannot be spent independently of J. Contact constraints
cancel the continuous pole terms but do not control this signed prime
discrepancy. Positive averaging alone does not supply a net gain.
Ask Proshka for one source-specific signed mechanism beyond those contacts,
with a full budget, or a substantive earlier rollback. Merely inserting
the explicit zero formula yields (6), the adverse sign already known.
No new numerical source data, Lean/Arb run, or RH claim. Goal remains open.

## Source-specific next mechanism, not yet an estimate

The original audit gives H_w=J_w^r G/d_w,
J_w v(t)=exp(-wt) integral_(-infinity)^t exp(wu)v(u)du,
d_w=(-1)^r M_G^(r)(w)/r!, G=-4 Phi. Thus, for B=partial²-1/4,
(partial+w)^r g_w=B G/[d_w(w²-1/4)]. The partner has its OWN constants.
This is information beyond the two pole moments. A concrete Q17 candidate
is to transfer these two differential resolvents through the complete
signed prime pairing, exploiting the known radical identity W(G,v)=0.
Commutation/zero of a forcing term alone is not a positivity estimate.
All boundary/homogeneous contributions must be retained: the same equations
already support the conditional adverse signal in (6). No inverse-resolvent
positivity or favorable sign of its boundary data has been established.
This is a proposed next test for Proshka, not a second completed mechanism.

## Independent bounded disposition

Read-only q17_pair_source audit: PASS on (1)-(8), original-P uniformity,
separate partner normalization, both time signs, all prime powers and exact
price/signal ratio. No material correction requested. Shelf search found no
earlier copy of this positive translation averaging attempt. Differential
resolvent identity checked algebraically; its favorable inequality remains
unpaid. No new status for CCM, RH or actual signed B_T.
