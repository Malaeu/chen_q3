# Full CCM negative growth phase

Chat: [Proof of CCM Growth](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ac54396-d878-83eb-ae29-35d2bdd2262b).
Question1 sent 2026-10-06 18:53:10 UTC; user item 029a2e6f-548c-4259-a1a7-b763124fad95.
Pro selected; saved user message and active response verified. Answer1 complete and checked: PROSHKA_CAUSAL_DRESSING_INLINE_2026-10-06.md and CAUSAL_DRESSING_AUDIT_2026-10-06.md. Do not resend.
Previous phase complete10/10. Decision and own attempt: NEGATIVE_BOTTOM_GROWTH_AUDIT_2026-10-06.md.

## Exact question1

Full CCM negative-bottom growth — new mathematical phase, question 1/10. Work on a proof, not a plan. Take the full reasoning time; do not use Answer now. RH is not proved.

Phase: ROUTE_B / FULL_CCM_NEGATIVE_BOTTOM_GROWTH / CCM_FULL_N_EQ_M_ORIGINAL_COFINAL / FULL_WEIL_CRITERION_VIA_SUBPOLYNOMIAL_NEGATIVE_BOTTOM / CHALLENGER_NOT_RH / W02_MINUS_WR_MINUS_ALL_PRIME_POWERS_PHASED_LOG_WINDOW.
The previous Missing T7 Lemma chat is closed at 10/10, fully processed. Its direct source overlap attempt stalled without a lower overlap estimate. This is an explicit terminal-consumer change on the SAME full matrix, not closure of the old G1/G3 ground-transform constructors.

Exact source. m=N, L=log m, I=[-L/2,L/2], psi_n(t)=(-1)^n L^(-1/2)exp(2 pi i n t/L)1_I(t), |n|<=m. P_m is their L2 orthogonal projection, K_m the restriction of the FULL complex Weil form W, no pole deletion, no even restriction. Original eventual schedule m_j=preAnchorTailStart(P)+j+2, fixed P. For zero-extended f set Q_f(s)=2 Re integral conj(f(t))f(t+s)dt. The diagonal form is
W(f)=D_arch(f)-cA||f||2^2+integral_0^L 2cosh(s/2)Q_f(s)ds-sum_(n<=m) Lambda(n)/sqrt(n) Q_f(log n),
D_arch=integral_0^infinity J(s)||tau_s f-f||2^2 ds, J(s)=exp(-s/2)/(1-exp(-2s)), cA=EulerGamma+log(8pi)+pi/2. Lambda includes ALL prime powers. Polarization defines the complex form and K. Norm E^2=||exp(|t|)f||2^2+D_arch(f), |W(f,h)|<=22||f||E||h||E.

Checked input and consumer. G(t)=exp(t/2)sum_(n>=1)(24pi (n exp t)^2-16pi^2(n exp t)^4)exp(-pi(n exp t)^2), real even, fixed derivatives double-exponential tails, M_G(z)=integral G(t)exp(zt)dt=-4 xi(1/2+z). All translates and derivatives of G are full radical vectors. g_m=P_mG/||P_mG|| has ||K_m g_m||=O_R(m^-R) for every fixed R, with endpoint jets paid. This is an UPPER residual and supplies NO lower bottom overlap. The resolvent scalar tends to -1/z automatically; cyclicity and positive Gauss weights do not give quantitative norming.

An off-critical zero w=delta+i gamma, delta>0, multiplicity r, has partner wdagger=-conj(w). Define J_w v(t)=exp(-wt)integral_(-infinity)^t exp(wu)v(u)du and d_w=(-1)^r M_G^(r)(w)/r!, H_w=J_w^rG/d_w. Then M_Hw(w)=1 and vanishes at all other distinct zeros. The full zero formula gives for u_b=exp(-ib gamma)tau_b H_w-exp(ib gamma)tau_(-b)H_wdagger:
W(u_b)=-2r exp(2delta b), ||u_b||2^2<=D=2(||H_w||2^2+||H_wdagger||2^2).
H_w and every fixed derivative have fixed double-exponential tails. Constants may depend on w,r. The old September9 separator is reused; not claimed new.

New checked original-carrier projection: choose a=L/2, h=log L, b=a-h; smooth chi_a is 1 on |t|<=a-1 and zero outside I, fixed transition derivatives. The E cutoff error <=C exp(b)exp(-c L^2), ||u_b||E<=C exp(b). All fixed L1 derivative norms of chi_a u_b are uniform in b. With Omega=2pi m/L and C3>=||(chi_a u_b)'''||1 the Fourier E error is bounded by
E3=C3[(m+16)/(5pi)Omega^-5+2/(3pi)Omega^-3+2/pi^2 Omega^-4]^(1/2)=O(m^-3/2 L^3/2).
Both zero-extension jumps are paid. Full form error is O(m exp(-c L^2))+O(m^-1 L^3/2). Hence on EVERY sufficiently late original cell
lambda_min(K_m)<=-c m^delta/(log m)^(2delta).
Independent source-pair and projection audits accepted this conditional implication; no off-critical zero is asserted.
Thus it SUFFICES to prove the currently OPEN assertion (SP): for every eta>0, lambda_min(K_m)>=-C_eta m^eta eventually. RH would make SP trivial, so SP is not advertised as logically weaker than RH; its quantitative form is the proposed attack. This bypasses old ground tracking without proving G1/G3.

Own attempt already done. Separate absolute values yield only lambda_min>=-cA-(1+4L)sqrt(m): W02=2(|integral cosh(t/2)f|^2-|integral sinh(t/2)f|^2), ||sinh(t/2)||I^2=(sqrt(m)-m^-1/2-L)/2; primes bounded by 2 sum Lambda(n)/sqrt(n). The shelf's fixed-window lower semiboundedness has the SAME cutoff dependence, not SP.
Retaining exact cancellation, E(x)=psi(x)-x+1 and A(x)=x^-1/2 Q_f(log x), E(1)=A(m)=0, gives
W(f)=D_arch(f)-cA||f||2^2+integral_0^L exp(-s/2)Q_f(s)ds+integral_1^m E(x)A'(x)dx.
The continuous correlation term is nonnegative (multiplier 1/(1/4+omega^2)). No subpolynomial lower bound on the final signed arithmetic correction is known here. This is the OLD Chebyshev-primitive representation; renaming it is not a new estimate. PNT absolute errors alone do not pay SP. Finite-stencil CSS certificates and independent pole-gauge profile domination failed previously; radical translates constrain any positive domination. Full-carrier leakage-smallness for multiplication by G was explicitly false, and the bottom-restricted estimate remains unproved.

TASK: Attack SP directly through the JOINT pole/prime operator before taking separate norms, on the above actual complex carrier. Look for a source-specific cancellation or a factorization/semiboundedness mechanism whose constants grow subpolynomially with m. Use relevant primary literature only with exact hypotheses and a checked source map. Do not assume RH, positivity of W, a zero-free half strip, RH-strength psi error, a polynomial spectral gap, or the missing overlap. No abstract replacement matrix or numerical extrapolation as supplier. Produce an actual estimate with all m dependence and endpoints paid, or a precise proved obstruction to a concrete attempted mechanism, leaving the first unsupplied inequality explicit. Another restatement of SP=>RH or the old separator is not progress. End with one concrete next mathematical step justified by your calculations.
