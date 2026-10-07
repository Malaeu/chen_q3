# Scalar drift alias return after Q8

## Exact obstruction and search dictionaries

The complete convexity loss is paid, but the actual signed drift S_Q(q) has no adequate lower barrier. Positive event weights and an absolute count estimate do not themselves decide the integrated sign. The consumer remains every sufficiently late prime-power cell, not a positive prefix or a sparse subsequence.
Required test from SCALAR_RESERVE_AUDIT: S_Q(q)>=-E_Q+L_Q(q)+d_q for all late q; L_Q(q)<=(18logQ+24)/sqrtQ is proved. Exact definitions and all source terms remain in Q8 and SCALAR_RESERVE_OWN.
Dictionaries: integrated Chebyshev one-sided discrepancy; convex-order/stop-loss domination; renewal cumulative logarithmic drift. UNVERIFIED search hints: endpoint-conditioned positive timing cost; terminal-load clipping of a weighted Mangoldt prefix envelope.
Three ask.sh queries using those dictionaries returned INCOMPLETE (semantic-index freshness); no absence claim. Temporary logs /tmp/q3_scalar_alias_0.log through _2.log. Existing shelf candidates did not supply the missing arithmetic inequality.

## Own negative control: strong counting asymptotics still do not force sign

This is outside the actual von Mangoldt class. Fix 0<delta<1/2, gamma>0, 0<eps<1, w=delta+i gamma. At every integer n>=2 put
a_n=n^(-1/2)+eps*n^(delta-1)*cos(gamma logn)>0.
Keep precisely the smooth B(t)=4exp(t/2)+ct+b-R(t), but replace the arithmetic event measure by these weights. Let Psi_a=B-sum_(n<=exp t) a_n(t-logn).
For f_t(x)=x^(-1/2)(t-logx), integral_1^(exp t) f_t=4exp(t/2)-2t-4. For the oscillatory perturbation,
integral_1^(exp t) x^(delta-1)cos(gamma logx)(t-logx) dx
=Re[(exp(wt)-1-wt)/w²].
Sum-integral errors are O(t): for the baseline use its O(t) total variation, and for the perturbation bound endpoint terms plus the integral of the absolute derivative by C_(delta,gamma)*t, since delta<1. Excluding n=1 changes only O(t).
Therefore Psi_a(t)=-eps Re[exp(wt)/w²]+O(t).
Choosing gamma*t-2arg(w) equal to successive even or odd multiples of pi proves both positive and negative values arbitrarily late. The exponential oscillation dominates O(t).
Nevertheless the weighted count obeys
sum_(n<=x) sqrt(n)*a_n=x+O(x^(delta+1/2)+1),
which is a smaller error than x*exp(-alpha*sqrt(logx)) eventually for every fixed alpha>0. Also A_a(x)=2sqrtx+O(x^delta+1), y_(n-)=A_a(n-)-c asymptotic to 2sqrtn, and a_n=O(n^-1/2). Hence the convexity losses are O(n^-3/2), summable.
All derivative jumps are negative, so Psi_a''<=exp(t/2)dt still holds. For every fixed alpha>0 its magnitude eventually satisfies |Psi_a(t)|<=C exp(t/2-alpha*sqrtt).
Thus positive weights, this strong counting asymptotic, one-sided curvature and summable losses together do NOT force eventual positivity. The missing discriminator must use additional properties of the actual von Mangoldt source. This is not a counterexample to its reserve or to RH.
Root construction independently checked by causal_algebra_audit: PASS for positivity, integrals, O(t) error, both late signs, counts and loss summability.
AUTOPSY: dropped=SIGN; note=abstract positive arrivals with stronger count error than the available envelope still have exponentially oscillating integrated reserve.

## Checked partial primary source; missing signed margin

Mittermeier, The Remaining Riemann-Hypothesis Tail, Part3 v3, https://zenodo.org/records/22076071 . Fetched PDF /tmp/q3_scalar_tail_candidate.pdf, SHA256 74ee615e634490f8431bd6731411ef2e177025d1a00bcf2f35008506d77c6e26. Root read Theorems4.3,4.6,5.6 and their proofs (printed pp9-10,15-16).
Theorem4.6 replaces local nonnegative timing cost by elapsed time times exact preterminal load. Theorem5.6 clips that load cap with an endpoint-pinned weighted Mangoldt envelope. These are partial upper estimates; the all-event comparison against exact capacity remains explicitly open.
Quoted abstract (p1): “That all-event inequality remains open. RH is not proved.”
Mapping: paper smooth A is our B; its weighted prefix W is our A_q; its active-event frozen minimum V is NOT our clipped V_q notation. Prefix envelope must keep its surviving coefficient delta_T=c_T+e_T-2>0 and additive d_T after pinning. Exact scope and upstream finite-height hypothesis checked by growth_symbol_attempt and reread by root: Chirre-Helfgott arXiv2512.15709 Prop9.1, printed p34. Finite zero verification is an input, not full RH.
Do not import this preprint's finite certificate as independently verified here. No Q9 selected or sent. Source check completed; exact source card and retained PDFs are in docs/literature/scalar_drift_2026-10-07/. Next action: seek a genuinely source-dependent lower estimate, not another absolute count envelope. A new representation alone is not progress.

## Own bounded test of the finite-height constructor (independently checked)

Fix a finite H and let T range over [10^7,H]. In the candidate's notation
c_T=(pi/T)coth(pi/(2T)), e_T=pi/(T-1), delta_T=c_T+e_T-2.
Since z*coth(z/2)>2 for z>0, delta_T>=kappa:=pi/(H-1)>0 uniformly.
The candidate prefix envelope is U_T(x)=(2+delta_T)sqrtx-alpha+d_T.
Q8 proves A(x)=2sqrtx+o(sqrtx); alpha is fixed and d_T is bounded on the compact T interval. Thus U_T(x)-A(x)>=kappa*sqrtx/2 uniformly eventually.
Now take any actual reference/event sequence x->infinity with q/x->1. Its preterminal weighted load Ppre=A(q-)-A(x)=o(sqrtx), by the same asymptotic (the omitted jump is also o(sqrtx)). Consequently U_T(x)-A(x)>Ppre for all admissible T eventually.
The pinned envelope R_T,a(u)=U_T(u)-A(x) increases in u. Therefore
min{Ppre,R_T,a(u)}=Ppre throughout [x,q], and its integrated upper cost is exactly Ppre*log(q/x): the front-loading cap itself.
With the source hypotheses and definitions confirmed, this proves that fixed finite-height spectral pinning gives NO additional asymptotic gain on shrinking relative windows. It does not kill front-loading, rule out larger windows, or refute any actual reserve. Allowing H to grow requires new zero verification evidence or a different unconditional input; it cannot be silently assumed.
growth_symbol_attempt independently checked the uniform-T argument: PASS; root reread Proposition9.1. This is our proved limitation of the conditional constructor, not a claim stated in that primary theorem. Equation75 of the secondary candidate also omits R'(logu); see the source card for the exact correction.
