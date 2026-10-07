# Direct long-divisor cofactor bound

Root derivation and independent mobius_source_audit bounded PASS, 2026-10-07. This improves the cofactor estimate and pays its N~T boundary. It does not close the full physical sum. Input: the pinned source sextic large-sieve lemma, paper.tex4707–4725, already subjected to a bounded source audit; no certification of the whole OpenAI manuscript is implied.

## Object and bound

Use the exact B_H,m(N) of FREE_COFACTOR_COMPLETION_ATTEMPT.md. Fix eta,S,m before the H sum, Q,T>=1,N>=T, and a fixed smooth annular F. Sum over every primary good H with Q<q_H<=2Q, without squarefree or coprimality restrictions on H. Then

sum_H |B_H,m(N)|² <<epsilon,F,eta,S (QN)^epsilon
 [Q/T + sqrt(Q)log²(2N/T) + Q^(2/3)T^(-1/3)].                 (1)

The puncture m only removes coefficients, so the constant is uniform in m. The previously checked balanced H-dependent profile is allowed using its Fourier separation in log(q_H/Q), with the other balanced-box parameters fixed before the H sum and uniformly controlled.

## Proof retaining the actual convolution

Use beta_T=mu_gt*1 directly, rather than delta−mu_le*1:

B_H,m(N)=sum_(k,m)=1 eta(k)bar chi_k(H)/q_k
 sum_qd>T,(d,m)=1 mu(d)eta(d)bar chi_d(H)/q_d F(q_d q_k/N).

Only q_k<=C_F N/T contributes. There is no (d,k)=1 condition; mu(d) restricts d to squarefree ideals. For each fixed k the outside row multiplier has absolute value at most1. Including 1/q_k in the coefficient, the squared column mass is O_F(1/(N q_k)). All coefficients are independent of H.

The square decomposition H=s u², with s squarefree and no (s,u) restriction, extends the source sieve to all good rows:

sum_H |sum_d c_d bar chi_d(H)|²
 <<epsilon (QD)^epsilon [Q+D sqrt(Q)+(QD)^(2/3)] sum_d|c_d|².

Indeed K=2Q/q_u²>=1 for every contributing u; summing the source terms gives Q sum_u q_u^-2, D sqrt(Q), and (QD)^(2/3)sum_u q_u^(-4/3). For the fixed k polynomial use D=C_F N/q_k; if D<T the polynomial is empty, otherwise D>=1.

Consequently its l2 norm is at most, up to a common epsilon factor,

sqrt(Q/N)q_k^-1/2 + Q^1/4 q_k^-1 + Q^1/3 N^-1/6 q_k^-5/6.

Minkowski over k and ideal counting give respectively sqrt(N/T), log(2N/T), and (N/T)^1/6 for these three harmonic sums. Thus

||B||_2 <<epsilon (QN)^epsilon
 [sqrt(Q/T)+Q^1/4 log(2N/T)+Q^1/3 T^-1/6].

Squaring and renaming epsilon proves(1). Sixth-power/principal rows are included in the sieve from the outset; none is removed or declared zero. Sharp q_d>T and all original zero-extended symbols are retained. The H-dependent profile extension follows by Minkowski in the Fourier parameter with its rapid seminorm decay.

## Scales, boundary, and remaining consumer

At Q=Z^(13/16),T=Z^(1/4), the energy powers are9/16,13/32,11/24. The RMS divided by sqrt(Q) is O_epsilon(Z^(-1/8+epsilon)), uniformly for N>=T in the stated profile class. Exact rational arithmetic checked. This strengthens the previous convexity-based Z^-3/64 cofactor bound.

For the shell T<q_nu<2T, beta_T(nu)=mu(nu) exactly: every proper divisor omits a good nonunit factor of norm at least7, so its norm is belowT. Formula(1) handles the wider range without relying on this special simplification. The earlier statement that the critical-line estimate did not pay N~T remains true for that method; (1) supplies a different estimate that does pay this cofactor boundary.

## Actual selected/shared-prime weights

Independent squarefree_conductor_check bounded PASS for the following transfer. Fix the tuple, its selected states and g before H summation. Put G=g P22, J=P11, R=q_G q_J, where Pii contains precisely the selected primes in state(i,i). These ideals are squarefree and G,J disjoint. From the exact Q2 table,

|D10|²=|D12|²=|D21|²=1_(p,H)=1,
|D11|²=1_p notdivides H + q_p² 1_p² divides H,
|D22|²=|L_p|²=1_v=1+(q_p−1)²1_v>=2
 <=1_p divides H+q_p²1_p² divides H.

Consequently, dropping only nonnegative coprimality restrictions,

|Delta_P(H)L_g(H)|²
 <=sum_a|G,b|J q_a² q_b² 1_(G a b²)|H.                       (2)

For any fixed good ideal E, the row substitution H=E h is a bijection on multiples of E. Original zero-extended multiplicativity gives chi_n(Eh)=chi_n(E)chi_n(h). Thus a polynomial with squarefree columns has the all-row sieve at row length Q/q_E, after absorbing chi_n(E) into its column coefficients without increasing their squared mass. Terms q_E>2Q are empty; for Q/q_E in[1/2,1] changing to max(1,Q/q_E) costs only a fixed constant.

Apply this with E=G a b² and sum(2). The three divisor sums give, up to (QDR)^epsilon,

sum_H |Delta_P L_g sum_n c_n bar chi_n(H)|²
 <<epsilon (QDR)^epsilon
 [Q+D sqrt(Q)R+(QDR)^(2/3)] sum_n|c_n|².                    (3)

Explicitly their factors are Q/q_G *sum_a q_a *sum_b1;
D sqrt(Q)/sqrt(q_G)*sum_a q_a^(3/2)*sum_b q_b;
and (QD)^(2/3)/q_G^(2/3)*sum_a q_a^(4/3)*sum_b q_b^(2/3).
The first is Q times a divisor-epsilon factor, the second at most D sqrt(Q)R times that factor, and the third at most (QDR)^(2/3) times that factor. This uses the density of the large local weights, rather than their supremum.

Repeat the fixed-k argument of(1) with(3). Minkowski, including every cross-k term, proves

sum_H |Delta_P(H)L_g(H) B_H,m(N)|²
 <<epsilon (QNR)^epsilon
 [Q/T+sqrt(Q)R log²(2N/T)+(QR)^(2/3)T^(-1/3)].               (4)

The fixed-k l2 contributions before summation are sqrt(Q/N)q_k^-1/2,
Q^1/4 R^1/2 q_k^-1, and Q^1/3 R^1/3 N^-1/6 q_k^-5/6.
Summing their squares separately would falsely delete cross-k terms and is not used. All principal/sixth-power rows remain in(3)-(4).

At the balanced scales the energy exponents are9/16,13/32+r,11/24+2r/3 where R=Z^r. The new unweighted exponent9/16 survives for r<=5/32 (both inequalities agree at this endpoint). The previous exponent23/32 survives for r<=5/16. Uniform positive RMS gain relative to ambient sqrt(Q) follows from(4) for r<13/32. All statements absorb logarithms in epsilon and need a fixed positive margin when a strict saving is claimed. The broad original ranges permit R<=q_g q_P<<Z31/48, so this does not guarantee a saving on every fixed tuple. Failure of the upper bound to save is not a lower bound or a no-go result.

Outer d,v,tuples, Type I, physical complement and high continuation still require their full joint bounds. No RH or full-low-exponent claim follows from(1) or(4). Q4 has now arrived and is under independent audit; no extra message sent.
