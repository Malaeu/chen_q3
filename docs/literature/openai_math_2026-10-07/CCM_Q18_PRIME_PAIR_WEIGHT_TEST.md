# Actual finite-divisor theta weight: one prime-pair cancellation test

2026-10-25. Own bounded attempt while Q18 is pending. Proshka not accessed.
Source: CCM_Q18_THETA_FILTER_TRANSFER.md, especially (1)-(6). Original
m=N, L=log m, same three-contact sparse P and actual source pair unchanged.
RESULT: exact coefficient cancellation, NONZERO weighted defect; no new power.

## Proven rule, with finite cutoff intact

For every integer k>=1,
 d_m(k)=sum_{s prime} min(v_s(k),floor(log_s m)) log s,
where the min is interpreted as the number of j>=1 with s^j|k and s^j<=m.
Thus d_m(ab)=d_m(a)+d_m(b) if gcd(a,b)=1, for every finite m>=1.
This follows directly by listing prime-power divisors, not from an infinite
prime sum or an assumption about prime distribution.
For distinct primes p,q with gcd(a,pq)=1 set
 alpha=1_{p<=m}log p, beta=1_{q<=m}log q.
Then
 d_m(apq)-d_m(ap)-d_m(aq)+d_m(a)=0.                    (1)
This remains true when apq>m, a>m, or one/both primes exceed m. Proper prime
powers in a remain in d_m(a). No replacement d_m(k)=log k for k>m is made.
For a=1,p=2,q=3,m=3, d_3(6)=log2+log3 although 6>3: this is the actual
finite DIVISOR cutoff, not a cutoff on the outer theta index.

## Actual weighted defect, not a surrogate

Keep the literal source
 phi_k(t)=(4pi^2 k^4 exp(9t/2)-6pi k^2 exp(5t/2))exp(-pi k^2 exp(2t)).
Let A_k(t)=d_m(k)phi_k(t). With D=d_m(a), the exact mixed difference is
 A_apq-A_ap-A_aq+A_a
 =D[phi_apq-phi_ap-phi_aq+phi_a]
  +alpha[phi_apq-phi_ap]+beta[phi_apq-phi_aq].           (2)
All four weights survive. The cancellation in (1) would eliminate a COMMON
weight; our weights are not common. This is a mixed finite difference, not
a free grouping of the full theta series.

A literal negative test uses a=1,p=2,q=3,m>=3:
 D(t)=log6 phi_6(t)-log2 phi_2(t)-log3 phi_3(t).
For t>=0 all these phi are positive. For j>2,
 phi_j(t)/phi_2(t) -> 0 as t->+infinity,
because the polynomial/exponential prefactor ratio tends to j^4/16, whereas
exp[-pi(j^2-4)exp(2t)] tends to zero. Hence
 D(t)/phi_2(t) -> -log2 < 0.                            (3)
So the weighted pair does NOT vanish identically; it is negative eventually.
This is an analytic statement about actual theta summands, not numerical
assignment of a hypothetical zero. It is NOT a sign theorem for full CCM:
G_m^+ includes -4, both time orientations remain, other theta indices remain,
and the resolvent kernel and complex normalization can change real sign.

## What can actually be bounded

Directly from (2), for every real t,
 |defect| <= D(|phi_apq|+|phi_ap|+|phi_aq|+|phi_a|)
             +alpha(|phi_apq|+|phi_ap|)+beta(|phi_apq|+|phi_aq|).
For t>=0 absolute bars on individual phi may be omitted. For t<0 they may NOT.
No factor tending to zero with m has been extracted by this argument.
In particular p=2,q=3 have fixed logarithmic spacings: a derivative formula
for their finite difference does not introduce a shrinking step as m grows.

(2) does not partition sum_k A_k into disjoint such blocks. Overlap counts and
unpaired terms would need an additional exact reconstruction. We do NOT sum
these local absolute bounds over k under the global t-integral: that exchange
was not proved by the local-normal-convergence statement in the source.
Instead complete the budget using the original finite n-sum, which is valid.

## Full returned budget; all mixed terms preserved

Retain exactly
 H_G,m(y)=integral [G(t)G_m^+(t+y)+G_m^+(t)G(t+y)]dt,
 J=kappa[E_r+integral_0^infinity exp(-bu)q_r(u)H_G,m(y+u)du].
No replacement by the local four-term defect is performed. Thus the full
original object and every unpaired term, both time signs, prime powers,
complex kappa, and E1/E2 endpoints remain present. The already proved finite
n-sum completion (source equation5) still gives
 |J| <=12|kappa|[C_r+G_0 I_r(b)]sqrt(m).
Return the WHOLE pair through the original P; no commutation with dilation
or differentiation is assumed. The inherited full-form rho_K,rho_S are o(1)
for fixed q>1/epsilon+2 and contain all projection cross terms. Finite upper
endpoint plus tail is O_w(sqrt(m)(1+L)^C exp(-cL^2))=o(1).
Archimedean price D_w(50L+8) is added ONCE. The completed direct lower budget
is therefore -C_w sqrt(m)-D_w(50L+8)-o(1), not an improved exponent.
The inherited averaged bound sqrt(m)/(LT)+L+1 remains stronger by logs;
T comparable L yields sqrt(m)/L^2 versus m^delta/L^(2delta+1). The power
1/2-delta deficit remains. Neither bound is a lower bound on the true cost.
No new eta(epsilon)->0, no assertion that signed cancellation is impossible.

## Exact controls and decision

experiments/ccm_prime_pair_2026_10_25/check.py stores integer coefficient
vectors of log primes rather than rounded logarithms. 12864 assertions PASS
for m=1..64,a=1..32, four prime pairs, gcd guard. Tests include outer indices
above m and prime-power divisors. This verifies finite examples of (1) and
its additive inputs; the general proof is the prime-power listing above.
No complete CCM numerical evaluation, Lean, Arb or hypothetical zero values.

Rollback: before treating additive divisor coefficients as if the theta
weights were common. Useful surviving question is a signed comparison of
(2) together with a valid reconstruction and the real resolvent weight;
this attempt has not supplied it. Do not send another question while Q18
is pending. This is not a second proof of the Q18 weighted-Jacobi conjecture.
Independent bounded read-only PAPER audit q18_prime_pair_check: PASS on prime-power additivity, actual weighted defect and its asymptotic sign, absence of global reconstruction, and full inherited original-P budget. This is a bounded audit of this note, not a full CCM proof.
