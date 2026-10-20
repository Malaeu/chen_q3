# Weighted LCM bound: a lower-cost full Ramanujan return

2026-10-20. Status: PAPER proof reviewed independently; no material defect found. This is a
quantitative improvement of a previously paid quadrature fee. It is NOT a
supplier for C5, the signed q-block upper bound, full SP, or the full-matrix
quarter-power floor. Same original CCM source and all endpoints retained.

## One arithmetic lemma

For integer R>=2 retain exactly the Q08 coefficients

    C_R = sum_(q<=R) mu(q)^2/phi(q),
    u_R(d) = mu(d)d/(phi(d)C_R)
             sum_(k<=R/d,(k,d)=1) mu(k)^2/phi(k),
    g_R(l) = sum_(d,e<=R,[d,e]=l) u_R(d)u_R(e).

Here d,e,k,q are positive integers, phi(1)=1, and [d,e]=lcm(d,e).
The Q08 exact expansion is b_R(n)=log(n) sum_(l|n)g_R(l), with
sum_l g_R(l)/l=1/C_R and g_R(l)=0 for l>R². Claim:

    sum_l |g_R(l)|/sqrt(l) <= 324 R (1+log R)^2.          (W1)

This is an inequality for the actual coefficients, not a fitted law.

Proof. The inner sum in u_R is a subset of the nonnegative terms of C_R,
so |u_R(d)|<=d/phi(d)<=2^omega(d)<=tau(d). For real X>=1, divisor expansion gives

    sum_(a<=X) tau(a)/sqrt(a)
      =sum_(bc<=X)1/sqrt(bc)
      <=2sqrt(X) sum_(b<=X)1/b
      <=2sqrt(X)(1+log X).                              (W2)

The estimate sum_(c<=Y)c^(-1/2)<=2sqrt(Y) follows by an integral comparison.
Using sqrt([d,e])=sqrt(de)/sqrt(gcd(d,e)), and writing d=ha,e=hb with
h=gcd(d,e), drop only the nonnegative coprimality restriction (a,b)=1:

    sum_l |g_R(l)|/sqrt(l)
    <=sum_(d,e<=R) tau(d)tau(e)/sqrt([d,e])
    <=sum_(h<=R) tau(h)^2/sqrt(h)
           (sum_(a<=R/h)tau(a)/sqrt(a))^2
    <=4R(1+log R)^2 sum_(h<=R) tau(h)^2/h^(3/2).

We used tau(ha)<=tau(h)tau(a), verified prime by prime by
r+s+1<=(r+1)(s+1). For every prime exponent a>=0,
(a+1)^2<=binomial(a+3,3), since the difference is a(a-1)(a+1)/6>=0.
Thus tau(h)^2<=d_4(h), the ordered four-factor divisor count. Nonnegative
summation and the integral comparison sum_n n^(-3/2)<=3 give

    sum_h tau(h)^2/h^(3/2)
    <=sum_(a,b,c,d>=1)(abcd)^(-3/2)<=3^4=81.

This proves W1 for every R. No prime-distribution hypothesis is used.

## Source-preserving Abel return

Use the existing Q08 full-return setup: m>=4, 1<=M<=m, 2<=R<m,
L=log m, original source Fourier band, and fixed-in-t orthogonal projection P.
Put f(t)=log(t)P Q_M(log t)P/sqrt(t). Both f(1)=f(m)=0, and the already
proved source bounds give

    ||f'(t)|| <= [2+(1+D_M)log t]t^(-3/2),
    D_M=(2+8pi M)/L.

For every positive integer l, the literal discrepancy is

    B_l(t)=floor(t/l)-(t-1)/l,
    |B_l(t)|<=min(1,t/l), t>=1.                         (W3)

For t<l this follows from floor(t/l)=0; for t>=l use
B_l(t)=1/l-{t/l}. In particular the jump at t=l is retained.
The same Stieltjes/Abel identity used by Q08 gives

    E_R=-sum_l g_R(l) integral_1^m B_l(t)f'(t)dt.

There are no removed atoms: f(1)=0 and the original Q(L)=0 pays the upper
endpoint. This formula also holds when l>m; those divisors are not discarded.

Split the nonnegative scalar majorant at l (or extend it beyond m):

    integral_1^infinity min(1,t/l)[2+(1+D)log t]t^(-3/2)dt
    <=[8+4(1+D)(1+log l)]/sqrt(l)
    <=12(1+D)(1+log l)/sqrt(l), D>=0.                   (W4)

For l=1 the first piece is empty and the integral is 8+4D. For l>1 the
first piece is at most [4+2(1+D)log l]/sqrt(l); the second is
[4+(1+D)(2log l+4)]/sqrt(l). Therefore W1 and l<=R² prove

    ||E_R|| <= 3888 R(1+D_M)(1+log R)^2(1+2log R).      (W5)

Keep the minimum of W5 and the old Q08 bound
64 R²/C_R² (8+4D_M); W5 is not asserted to be numerically better at every R.

## Exact benefit and exact remaining gap

For fixed alpha,beta>0 with alpha<1,beta<1, M=floor(m^alpha),R=floor(m^beta),
W5 is O_(alpha,beta)(m^(alpha+beta)(log m)^2). Thus the quadrature exponent
changes from alpha+2beta to alpha+beta, with explicitly retained logarithms.
The existing Q08 small-argument price O(sqrt(R)(log R)^9), proper-power
price O((log m)^2), and smooth term ||J||<=8 are unchanged. Consequently the
complete JOINT return A+C_comp has the same improved upper norm budget.
For W=PWP>=0, the fee is multiplied by Tr(W); no replacement of W is made.
All mixed matrix entries remain in E_R, A and C_comp.

However A+C_comp small does NOT bound A or C_comp separately. C5 remains
unpaid. In particular, on the full carrier M=m, W5 only gives
O(m^(1+beta)(log m)^2). It does not prove the requested m^(1/4) floor.
Using a sparse band to display the improved exponent is explicitly the
separate sparse receiver, NOT a proof of full SP. We tried the direct return
to the full quarter-floor and it fails this budget check.

What has been achieved is a genuine uniform arithmetic inequality and a
smaller fee in an existing source-exact decomposition. What has NOT been
achieved is the central signed arithmetic estimate. This limitation is part
of the result, rather than a reason to rename the auxiliary fee as closure.

Sources read locally: CCM_MOMENT_Q08_CONCLUSION.md (accepted Q08-D),
PROSHKA_VERDICT_FULL_CCM_RAMANUJAN_Q08.md (coefficient expansion),
CCM_FULL_RAMANUJAN_RETURN.md (full Abel endpoints), CCM_COMPOSITE_SIGN_TARGET.md.
No external theorem, Lean proof, RH assumption or new Proshka send is used.

## Validation record

Independent read-only ccm_lcm_review checked W1–W5, constants, jumps,
normalization and exact consumer limits against Q08 §§3.3–3.5. No material
mathematical defect found. Q08 source identities/derivative inputs remain the
previously accepted PAPER inputs, not a fresh formalization of CCM.

CCM_WEIGHTED_LCM_CHECK.py ran for R=2,4,8,16,32,64,128. It checks the exact
rational mean sum(g_l/l)=1/C_R and 515 finite divisor-square identities.
Deleting mixed d,e contributions fails the exact mean identity in all seven
cases. Weighted numerical values use floating point and are diagnostics only;
the proof of W1 for all R is the argument above. No Lean certification claimed.

AUTOPSY: dropped=THEOREM_SHAPE; note=improved auxiliary full-return budget does not control separate signed composite spectrum or full-carrier quarter floor; central arithmetic supplier remains open.
