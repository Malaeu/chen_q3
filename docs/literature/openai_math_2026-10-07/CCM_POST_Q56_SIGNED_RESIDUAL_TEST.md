# Post-Q56: signed residuals do not repair singleton2 Cauchy loss

2026-10-27. One own bounded follow-up to Q56 §7.2, not a new source upper.
Original fixed epsilon, original P, full inner sums and all prime powers retained.
Only auxiliary prime set {2}, weight1 is tested. Q56 §7.2 was explicitly OPEN.

## Exact source and candidate

Take normalized five-mode f_L from Q56 §3, M>=2, L>=4pi. Write q=q_f,
b(d)=sum_(k<=m/d)log(k)/sqrt(dk) q(log(dk)), D=floor(m/2), H=1/2.
Let S=sum_(r<=floor(D/2))mu(r)b(2r), Q=sum mu(r)^2,
G(r)=b(2r), V=sqrt(Q sum G(r)^2). Preserve signed E,R of Q56.
Exact H A=-S+E+R gives the weaker sufficient price
J=(V+E+R)/H=A+2(V+S).                                  (1)
This identity alone is not progress. We test whether J has small power.

Finite mu*log convolution, without omitting any prime powers, gives
S=sum_(n<=m/2) Lambda(n)/sqrt(2n) q(log(2n)).             (2)
The apparent larger r range adds only k=1 (log1=0), hence contributes zero.

## Paid moving-profile scalar estimate

Use only already checked scalar Q55:
E(x)=sum_(n<=x)Lambda(n)/sqrt(n)-2(sqrt(x)-1)
=O(sqrt(x) exp[-c(log x/log(e+log x))^(1/3)]) eventually.
Real x uses floor(x) and an O(x^-1/2) correction, absorbed in constants.
The finite initial range is absorbed by an additive constant. This estimate
is stronger than o(sqrt(x)/log^K x) for every fixed K; no new supplier.

The SAME normalized f_L has support modes|j|<=2, so
|q|<=2, |q'|<=2||f'_L||_2<=8pi/L on[0,L]. Zero endpoint contacts justify
the derivative for the physical zero extension. Thus each weight
w_a(x)=q(log(ax)), a=1 or2, 1<=x<=m/a,
has total variation<=8pi, w_a(m/a)=0, and E(1)=0.
Stieltjes integration by parts bounds the error in
sum_(n<=m/a)Lambda(n)/sqrt(n) w_a(n) - int_1^(m/a)x^-1/2 w_a(x)dx
by int_1^(m/a)|E(x)| |w'_a(x)|dx.
Split at sqrt(m). On the lower piece, elementary |E(x)|<=C sqrt(x)(1+log x)
and the variation bound give O(m^1/4 L). On the upper piece Q55 uniformly
gives O(sqrt(m) exp[-c'(L/log(e+L))^(1/3)]), times variation<=8pi.
Hence the entire error is o(sqrt(m)/L^K) for each fixed K, uniformly for a=1,2.
No derivative of a real-axis big-O, spectral scan, or unpriced moving-family onset.

Original exponential contacts give exactly
int_0^L e^(s/2)q(s)ds=-int_0^L e^(-s/2)q(s)ds, whose modulus<=4.
The continuous part of A is therefore O(1). The continuous part of S is
(1/2)int_(log2)^L e^(s/2)q(s)ds, also O(1), since the omitted fixed interval
has modulus<=4(sqrt(2)-1). Both lower endpoints and the zero top atom retained.
Consequently |A(f_L)|+|S(f_L)|=o(sqrt(m)/L^K), every fixed K.       (3)

## Actual certificate lower and rollback

Q56(4.3)–(4.4), valid in particular for {2}, gives
V>=c_g sqrt(m)/(448 L^9).
Combining (1) and (3) with K=10 yields eventually
J(f_L)>=c_g sqrt(m)/(448 L^9).                              (4)
Thus even exact SIGNED E+R cannot repair the singleton2 Cauchy completion.
This is a stronger scoped negative result than absolute residual payment:
the Cauchy slack itself retains half-power although its actual signed
Möbius pairing and the original source on this witness are superlog smaller.
No lower for A/T/K follows. No conclusion for arbitrary weights, other
prime sets, or a method retaining the actual signed main pairing.

No new full upper: retain Q55/fallback and the same single short/arch fees.
Full eta(epsilon)->0 OPEN, RH unclaimed. Do not optimize singleton2 residual
payment; rollback before Cauchy. Count ONE post-Q56 no-gain attempt.
AUTOPSY: dropped=NO_DERIVATION; note=Signed residual repair still pays singleton2 Cauchy slack; original source remains open.

Independent bounded read-only q55_audit PAPER PASS, no material finding.
Reviewed pre-receipt SHA256bb8f518b7bd96bf6beda583083bf126319fed9a638bfa1444f51fc5f4333a8f4.
Exact shifted collapse, physical BV, both Stieltjes endpoints, uniform split,
continuous1/2 normalization and lower direction independently checked.
Q55/Q56 inherited, not reaudited. Acceptance limited to singleton2 completion.
