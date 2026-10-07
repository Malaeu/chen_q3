# Own attempt: actual-source three-moment target and exact residual gaps

PAPER; one independent algebraic pass by answer10_pair_audit completed. No moment sign estimate asserted.
Input: Q5 final variational test, original H_m(r)=H_m(0)+rI, fixed
R=ker L0 and E=R-perp. The accepted regular floor is A_r>=(r-epsilon_m)I.
The spaces and epsilon_m depend on the original cell, not the shift r.

## Remove the scalar shift without changing the source

Write H0=H_m(0), A0=(P_R H0 P_R)|R, B=P_R H0|E,
D0=(P_E H0 P_E)|E. Here A0 is a BLOCK, not the older cutoff ceil(sqrt m).
For this note use T=A0+epsilon_m I>=0 to avoid that naming collision below.
For v in E set b=Bv, q0=<v,D0v>, N=||v||²,

    M=||b||², c=<b,Tb>>=0, e=||Tb||²>=0, g=r-epsilon_m>0.

All five source quantities N,q0,M,c,e are independent of r. The shifted
regular block is A_r=gI+T and its cross block is exactly B, since
P_R I P_E=0. Thus q=q0+rN,

    M0=M, M1=gM+c, M2=g²M+2gc+e,
    M1-gM0=c, M2-gM1=gc+e.

The Q5 lower envelope is therefore

    L3(v;r)=q-M/g+c²/[g(gc+e)]

when gc+e>0, and its sign is exactly the sign of the explicit quartic
source expression

    F_r(v)=(gq-M)(gc+e)+c².

The upper envelope is U1=q-M²/(gM+c), with positive denominator for b!=0.
If b=0, the actual Schur value is q. If gc+e=0 and b!=0, positivity
of T implies Tb=0 and the exact value is q-M/g. These cases cannot be
handled by dividing a zero denominator. A negative L3 is inconclusive.

## Exact gaps explain what the moments do and do not control

Let mu_{b,r} be the finite spectral measure of the ACTUAL A_r at b, supported
on [g,infty), with total mass M. For any real alpha,

    upper_alpha=q-2alpha M+alpha²M1,
    lower_alpha=upper_alpha-(M-2alpha M1+alpha²M2)/g.

Direct scalar expansion at each eigenvalue lambda gives

    upper_alpha-S(v)=int (1-alpha lambda)²/lambda dmu_{b,r}(lambda),
    S(v)-lower_alpha=int (lambda-g)/(g lambda)
                               *(1-alpha lambda)² dmu_{b,r}(lambda).

These identities are nonnegative because lambda>=g>0. Optimizing gives
alpha_upper=M/M1 and alpha_lower=c/(gc+e), yielding Q5's two envelopes.
Equivalently, completion of the square uses residual
e_alpha=b-alpha A_r b and the EXACT A_r inverse. No estimate of J_r
or of a surrogate block enters. The residual gap is a weighted spectral
spread of the same source b, not a freely chosen spectral measure.

## Remaining mathematical test

Compute/estimate q0,M,c,e from the complete source H0, including the full
signed F10 and cross terms, on actual E. Proving F_r(v)>=0 for every v,
together with the two degenerate cases, at r=C_eta*m^eta on unbounded
original cells for each eta would certify this sufficient lower envelope.
An actual v with U1<0 certifies a negative Schur direction only on its
stated cells. Neither conclusion is obtained here. Generic moment
positivity or Cauchy-Schwarz does not supply the missing source inequality.
The selected next question must execute this source estimate, not merely
rederive the abstract variational identity or optimize a new surrogate.
