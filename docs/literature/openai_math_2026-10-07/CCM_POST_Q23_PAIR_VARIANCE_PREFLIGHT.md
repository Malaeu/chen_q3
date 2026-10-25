# Q23 follow-up: actual-pair cumulative variance preflight

2026-10-25. Supplier-strength calculation, not a new arithmetic bound or a third failed mechanism. Original full P and full prime-power source retained. Q23 cycle committed as 1541e092. The previous goal turn completed authoritative cycle state; this turn checks a possible supplier before requesting Q24.

## Exact target and inherited input

Q23 (3.7) uses E(x)=psi(x)-(x-1) and the complete two-time weight
F_a(x)=exp(2 i gamma a) x^(-1/2)[C(2a-log x)+C(2a+log x)].
(The harmless unit eta is absorbed here.) The signed centered term is
E(m) F_a(m) - integral_1^m E(x) F_a'(x) dx.
C and C' have the inherited double-exponential tails. This is the actual source-dependent pair, not arbitrary independently selected weights. Mixed terms stay in C.

Hypothetical supplier, NOT proved: for every dyadic X>=2,
integral_X^(2X) |E(x)|² dx <= K_theta X^(2theta+1), with fixed 1/2<theta<=1 and constant independent of m,a.
The finite initial range is absorbed in a constant. This is cumulative variance, not short-interval variance.

## Weighted calculation

Put H(y)=|C'(y)|+|C(y)|/2. On X<=x<=2X, full differentiation gives
|F_a'(x)| <= x^(-3/2)[H(2a-log x)+H(2a+log x)].
Cauchy bounds a block by
sqrt(K_theta) X^(theta-1/2) sup_{log X<=t<=log(2X)} [H(2a-t)+H(2a+t)]
up to an absolute constant. No boundary is introduced at a dyadic cut: partition the already integrated expression.
With b=theta-1/2>0, the forward block sum is at most
C_(w,theta) exp(2b a), because the sum of exp(-b y) times local suprema of H(y) converges uniformly under translations. The reverse block sum is bounded by C_(w,theta) for a>=0, using the double-exponential positive tail. All blocks up to m remain present. The original upper endpoint is bounded by Chebyshev and the actual tail, O_w(sqrt(m) exp(-c_w log(m)^2)), uniformly for h-T<=a<=h, h=L/2-log L, T=alpha L, 0<alpha<1/4. It is not discarded by a variance assumption.

Averaging the completed absolute budget therefore gives
U_theta <= C_(w,theta) [exp(2b h)(1-exp(-2b T))/(2b T)+1]+o(1).
The adverse signal is E_T=exp(2delta h)(1-exp(-2delta T))/(2delta T).
For fixed theta,delta and growing T, the leading price/signal power is
exp(2(theta-1/2-delta)h).
Thus theta<1/2+delta is a sufficient exponent threshold for this absolute completion. At equality, constants must be compared with r and the desired positive coefficient margin; no margin follows from exponent equality. For theta>1/2+delta the displayed price does not give the required margin. This is not a lower bound on the actual signed form.

## Full return and interpretation

Q23 original-P return rho_S=o(1), self terms O_w(1), continuous return o(1) and archimedean O_w(L) are retained once. Proper powers can either remain inside E (as above), or be removed using Q23 O_w(1) pair return, but cannot be counted as an additional gain. No short-divisor price is added to this direct full-pair comparison; the scalar T_{>R} consumer requires its existing return separately.

The old all-vector calculation in CCM_Q10_MEAN_SQUARE_RETURN.md has an extra bandwidth derivative factor. Removing that factor on a fixed actual pair is valid here, but does not supply the missing arithmetic variance. To cover an arbitrary hypothetical delta>0 by this generic supplier one still needs theta arbitrarily close to 1/2. Q10 already proves that family is RH-strength. An RH-equivalent estimate is not forbidden as a research target, but cannot be consumed as a known easier theorem.

Negative control: E(x)=x^sigma-1 has cumulative mean square of order X^(2sigma+1); for sigma>1/2+delta its displayed budget fails. This synthetic control is not actual prime data. A short-interval variance theorem cannot replace the hypothetical cumulative input without the smoothing/reconstruction fee already studied in Q10.

Decision: this source-specific mapping is bookkeeping, not a new successful mechanism. Do not send Q24 asking merely for generic variance or count this duplicate toward three fresh attempts. Remaining useful target is the signed actual C/E coupling, or a quantitatively justified earlier source rollback. No new Lean, Arb, finite-CCM run, degree, or RH claim.
