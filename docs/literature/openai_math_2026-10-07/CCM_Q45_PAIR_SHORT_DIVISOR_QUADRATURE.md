# While Q45 runs: actual-pair short divisor quadrature

2026-10-26. Root derivation; S1–S4 through D=sqrt(m)/L^(2+tau) independently checked
by q45_primitive_screen. Higher-order extension S5–S7 also independently checked by the same
read-only agent; source/receiver facts remain inherited. This is a
pair-cross-term estimate, NOT an all-P upper and not a new full exponent.
No additional message sent to the live Q45 chat. Sources: Q17 actual C and
all-fixed-derivative tails; Q19 exact M_C; original sparse-band receiver.

Fix the same hypothetical w, actual separately normalized g,k and complex
C(v)=int conjugate(g(t))k(t+v)dt. Put L=log m, y=2h=L-2log L.
The production R=floor(m^epsilon), fixed0<epsilon<1/32, is unchanged.
Introduce an AUXILIARY divisor cutoff 1<=D<=sqrt(m). Then

 J_short=sum_(d<=D)mu(d)/sqrt(d) sum_(k<=m/d)log(k)/sqrt(k)
                       [C(y-log(dk))+C(y+log(dk))].            (S1)

This is the exact short-d part of mu*log=Lambda. All k are retained and the
upper floor is literal. It is NOT a short-prime restriction. Define J_long
by D<d<=m in the same double sum, so J=J_short+J_long exactly.

## Quadrature with the complete floor

For each d define F_d(t)=log(t)/sqrt(dt)[C(y-log(dt))+C(y+log(dt))].
The ordinary sum-minus-integral bound, including a noninteger upper endpoint,
is bounded by a fixed multiple of sup|F_d|+int_1^(m/d)|F'_d(t)|dt.
For the first orientation change variable v=log(dt), then z=v-y. Differentiating
exp(-v/2)(v-log d)C(y-v) under the v integral gives

 sup|F_d|+int|F'_d| <= C_w(1+y+log d)exp(-y/2)
                    <= C_w L^2/sqrt(m).                      (S2)

Indeed the full weighted integrals of (1+|z|)(|C(-z)|+|C'(-z)|)exp(-z/2)
are finite by the actual double-exponential tails. The reverse orientation
has y+v>=y and costs only a polynomial times exp(-c_w exp(y)); it obeys
(S2) too. Summing |mu(d)|<=1 over d<=D gives C_w D L²/sqrt(m).
This estimate includes the fractional last k-cell; no floor is smoothed away.

The integrals are exactly
 1/d int_d^m log(t/d)t^(-1/2)[C(y-log t)+C(y+log t)]dt.
Extending their lower limits to1 costs at most
 C_w sqrt(D)(1+log D)^2 exp[-c_w m/(D L²)],                   (S3)
because log t<=log D and y-log t>=log(m/(D L²)). Then their signed sum is

 a_D I_1-b_D I_0,
 a_D=sum_(d<=D)mu(d)/d, b_D=sum_(d<=D)mu(d)log(d)/d,
 I_j=int_1^m (log t)^j t^(-1/2)[C(y-log t)+C(y+log t)]dt.

No Mertens estimate is used: |a_D|<=1+log D and
|b_D|<=(log D)(1+log D) suffice.

## Why the two continuous terms are small

The ACTUAL transform M_C(z)=kappa A(z)^2/(z+conj(w))^(2r) has double
zeros at z=+-1/2, since A(z)=(z²-1/4)M_G(z) and the denominator is
nonzero there. Thus M_C(-1/2)=M'_C(-1/2)=0, including the complex kappa.
For the first orientation,
 I_j^-=exp(y/2) int_(y-L)^y (y-v)^j exp(-v/2) C(v)dv.
For j=0,1 the full-line integral is zero by these two contacts. The omitted
lower tail starts at y-L=-2log L, the upper at y. Double-exponential bounds
pay both. The second orientation I_j^+ is small directly because y+log t>=y.
After weakening constants, for j=0,1 and large m,
 |I_j|<=C_w sqrt(m)L^3 exp(-c_w L²).
The more strongly decaying exp(-c_w m/L²) tail is absorbed here. Consequently

 |J_short|<=C_w [D L²/sqrt(m)
       +sqrt(m)L^5 exp(-c_w L²)
       +sqrt(D)(1+log D)^2 exp(-c_w m/(D L²))] = E_D.          (S4)

For D=R this is o(1). More strongly, choose any fixed tau>0 and
 D=floor(sqrt(m)/L^(2+tau)).
Then E_D=O_w(L^(-tau))+o(1)=o(1). Eventually D>=R; the extra middle
range R<d<=D is paid by the difference of two such prefix bounds. The
remaining hyperbola d>D has k<=m/D=O(sqrt(m)L^(2+tau)). This is an
auxiliary arithmetic split, not a changed production R or projector.

This is an absolute bound on the actual short CROSS term, proved from the
true source contacts and smooth inner sum; finite data are not used.

## Full return and unchanged unpaid line

Keep both self terms of the original full prime operator together, O_w(1).
Replace J by J_long only in its full mixed contribution; the fee is at most
2E_D=o(1) for the selected auxiliary D. Then apply the ORIGINAL m/P whole-pair
receiver once: rho_K+rho_S=o(1), and the original arch price O_w(L) once.
No short-divisor operator is separately projected or claimed o(1) on all P.
Thus the sufficient independent pair margin reduces to the SAME margin on
Re(exp(i gamma y)J_long), with o(1) error. This does not supply that margin.

The inherited full endpoint fallback O_w(sqrt(m)/L+L) is unchanged. The
all-P short-sector m^(O(epsilon)) estimates are not improved by a statement
on this special cross-correlation. A zero-selective source presupposes a
hypothetical w only for its construction; no actual off-line zero is asserted.
This estimate identifies the remaining long-d source; it does not close CCM.


## Higher-order extension (bounded independent derivation check PASS)

Fix 0<alpha<1 and auxiliary D=floor(m^(1-alpha)). Choose a FIXED even
integer q>1/(2alpha). The all-fixed-derivative source bounds are inherited.
With v=log(dt), write f_d(v)=exp(-v/2)(v-log d)C(y-v). Exactly

 (d/dt)^q F_d^-(t)=t^(-q) product_(j=0)^(q-1)(partial_v-j) f_d(v).

After dt=exp(v)/d dv, the weighted L1 derivative estimate is

 int_1^(m/d)|F_d^(q)(t)|dt
 <=C_(w,q) L d^(q-1) exp(-(q-1/2)y).                       (S5)

It follows by z=v-y and integrability of exp(-(q-1/2)z) times polynomial
weights and the fixed derivatives of C(-z). The other time orientation is
smaller by its y+v tail, and satisfies the same estimate.

Euler–Maclaurin with bounded periodic Bernoulli functions, INCLUDING its
fractional upper endpoint, bounds the sum-integral difference by C_q times
int|F_d^(q)| plus the derivatives of orders0,...,q-1 at1 and m/d. At m/d,
these are <=C_(w,q)(d/m)^j L/sqrt(m) exp(-c_(w,q)L²); at1 they are bounded
by C_(w,q)d^(-1/2)exp[-c_(w,q)m/(d L²)]. The log(t) factor and all derivatives
are kept; the endpoint at1 is not silently discarded after differentiation.
Sum these bounds over d<=D and use the SAME continuous contact cancellation
and lower integral-edge return as above. This gives

 |J_short(D)|<=C_(w,q)[D^q m^(1/2-q)L^(2q)
   +sqrt(m)L^5 exp(-c_(w,q)L²)
   +sqrt(D)(1+log D)^2 exp(-c_(w,q)m/(D L²))].              (S6)

The first term is <=m^(1/2-alpha q)L^(2q)=o(1); the two other terms are
o(1). No Mertens estimate, mean value of mu, or change of source is used.
The order q is fixed BEFORE m grows; constants may depend on w,q,alpha.

For the auxiliary D to cover the production R, take alpha<1-epsilon.
In particular alpha=epsilon is allowed. Then D=floor(m^(1-epsilon)) and
the EXACT complement dk<=m,d>D implies k<m^epsilon, hence k<=R. Thus

 J(h;m)=sum_(k<=R)log(k)/sqrt(k)
         sum_(D<d<=m/k)mu(d)/sqrt(d)
          [C(y-log(dk))+C(y+log(dk))] + o(1).               (S7)

Both time orientations and the full complex correlation are retained.
All original d<=D have been estimated together with their signed integrals,
not erased from the arithmetic definition. The original R/P is unchanged;
D is auxiliary, and S7 is only on the actual conditional pair. Its full
mixed-return fee is2 times S6 plus rho_K+rho_S=o(1); self terms O_w(1) and
archimedean O_w(L) remain once. An independent signed bound for the long-mu
sum in S7 is STILL MISSING. No claim that its absolute size is small follows
from its short k-index. No all-P exponent improvement is claimed.

No Lean, Arb or production-spectrum run. The audit checks the analytic
quadrature, endpoint jets, contacts and scope, not the whole inherited chain.

## Hypothetical Mertens supplier: exact required rate, not a supplied theorem

Bounded independent derivation check PASS (q45_primitive_screen).
Assume, ONLY for this test, |M(t)|<=K t^beta for t>=1, fixed1/2<=beta<=1,
M(t)=sum_(d<=t)mu(d). For each k in S7 set B_D(t)=M(t)-M(D), so
B_D(D)=0 and |B_D(t)|<=2K t^beta for t>=D. Stieltjes summation on
f_k(t)=t^(-1/2)[C(y-log(kt))+C(y+log(kt))] retains B_D(m/k)f_k(m/k)
and the integral against f'_k. The upper endpoint, including its floor,
has C(y-L)=C(-2log L) and is negligible after summing k. The lower M(D)
is included through B_D; it is not assumed small or omitted.

Changing variable v=log(kt)-y in the derivative integral gives
 |sum_(D<d<=m/k)mu(d)f_k(d)|
 <=C_(w,beta)K(exp(y)/k)^(beta-1/2)+upper-tail.
Hence
 |J_long|<=C_(w,beta)K exp((beta-1/2)y)
                     sum_(k<=R)log(k)/k^beta + o(1).          (S8)
For fixed beta<1 this is
 O_(w,beta)(K m^(beta-1/2+epsilon(1-beta)) L^(2-2beta))+o(1).
The strict sufficient condition to make S8=o(X), X=m^delta/L^(2delta), is
 beta-1/2+epsilon(1-beta)<delta.                              (S9)
For beta=1 the sum is O(log²R), so the available trivial |M(t)|<=t gives
only O_w(sqrt(m)L). This is weaker than the inherited pair fallback, kept.

No beta<1 Mertens theorem is supplied or assumed in production. The displayed
conditional transfer does not authorize replacing the required one-sided
source pairing by an all-prefix absolute estimate. In particular a uniform
power beta close to1/2 cannot be quietly inserted to close the target.
The reduction S7 pays the smooth sector; it does not itself establish the
additional arithmetic cancellation measured by S9. This is the completion
of the same auxiliary attempt, not a new independent failed mechanism.
