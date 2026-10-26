# Post-Q30: surviving double shifts and full normalization

2026-10-26. Bounded own attempt; independent q30_square_budget_check bounded PAPER PASS. Original goal OPEN.
Source: CCM_Q30_CONCLUSION.md and Q30 original §§4–7. No numerical
spectral claim, new hypothesis, intermediate compression, or discarded prime powers.

## Actual ordered products

Retain R=floor(m^epsilon), W=sum_{R<n<m} Lambda(n)/sqrt(n),
a_n=Lambda(n)/sqrt(n), T=sum a_n V_log(n)/W on physical L2[0,log m]. If W=0 use the short
operator directly. For W>0, before projection,

T² = W^-2 sum_{u,v>R, uv<m} Lambda(u)Lambda(v)/sqrt(uv) V_log(uv).

The uv=m boundary is zero because V_log(m)=0; both ordered orientations,
self pairs and all prime powers are included. The coefficient is a convolution,
not Lambda(uv). No P occurs between shifts.

Write W0(x)=sum_{n<=x} Lambda(n)/sqrt(n). With the inherited bound W0(x)<=6sqrt(x),

B := sum_{u,v>R,uv<m} Lambda(u)Lambda(v)/sqrt(uv)
 <= 6sqrt(m) sum_{u<m} Lambda(u)/u
 <= 36sqrt(m)+18sqrt(m)log m.

The last line follows by partial summation of W0(x):
sum_{u<=m} Lambda(u)/u <= W0(m)/sqrt(m)
 + (1/2) integral_1^m W0(t)t^(-3/2)dt <=6+3log m. Thus ||T²||<=B/W².
Ordinary PNT gives W=(2+o(1))sqrt(m), hence ||T²||=O(log(m)/sqrt(m)).
This is a genuine small normalized product bound, not yet a small real part.

## Elementary full return

Let H=T+T*. Since ||T||<=1,
H²=T²+(T*)²+TT*+T*T <= (2+2||T²||)I.
Consequently the whole prime operator satisfies

A_prime <= s2 I,
s2=2Wshort+sqrt(2W²+2B).

Here Wshort=sum_{n<=R} Lambda(n)/sqrt(n). This pays the complete short
operator and retains mixed terms until the displayed norm bound. Asymptotically
s2=(2sqrt(2)+o(1))sqrt(m)+O(m^(epsilon/2)). The square-product increment
over sqrt(2)W is at most B/(sqrt(2)W)=O(log m).
The leading sqrt(m) remains. This price is not a lower bound on A_prime.

## Stronger existing-shape control

Compare against a free prime-index split X=floor(sqrt(m)); this changes
neither the original divisor R nor the original P. Every n>X exceeds sqrt(m),
so the normalized long operator U has U²=0 exactly. Q30's q=2 isometry
and path inequality give U+U*<=I. Thus

A_prime <= sX I,  sX=W_<(m)+W(X).

The n=m atom remains exactly zero, including perfect prime powers. For
m>=4, X<m. If the long mass vanishes the same formula reduces to 2W(X).
The explicit inherited bound is sX<=6sqrt(m)+6m^(1/4); ordinary PNT gives
sX=(2+o(1))sqrt(m)+O(m^(1/4)). It is asymptotically stronger than the
above surviving-product completion, while still retaining half power.

For either cap s, compress only at the end onto the SAME P_{m,epsilon}:

T_>R <= (s+b_div)P,
P K_m P >= -(s+50log(m)+8)P,
b_div=(56+32Omega_M)sqrt(R)+12(1+log R)^2.

The divisor fee is not charged twice; no extra decay-kernel 4 is added to K.
For fixed epsilon<1/32, b_div has power3epsilon/2 up to logarithms and
cannot remove the leading half-power term. Both times enter T+T*, and all
source mixed terms are present before the explicit upper-bound step.

## Decision

NO_NEW_ARITHMETIC_EXPONENT. Small T² alone is insufficient: even the
2-by-2 shift [[0,1],[0,0]] has square zero and largest eigenvalue1 of U+U*.
This is only a general implication counterexample, not a model of CCM or
an impossibility theorem for the actual source image. Do not optimize this
constant-only completion further. Roll back before discarding the actual-image
deficit; a next supplier must estimate that deficit jointly with the complete
short operator, or use a different signed source mechanism. Q31 not sent.
