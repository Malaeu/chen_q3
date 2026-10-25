# Reciprocal real-axis smoothing: universal inverse fee

2026-10-25. Own bounded preflight after Q23. Independent q24_reciprocal_inverse_audit bounded PAPER PASS; root checked the same dimension and asymptotic calculation. This tests one explicit transfer, not the full reciprocal-Xi research family. No new CCM exponent.

## Transform and source correspondence

Sra v1 Corollary2.5, equations(2.9)–(2.10), p.6, gives the Fourier multiplier 1/xi(1/2+t) of the positive reciprocal density. The Laplace transform 1/Xi(z) holds only in |Re z|<gamma_1. These are not 1/xi(1/2+i t) on the full real frequency axis. The actual Q23 cross transform remains eta p(s)q_r(s). No equality of the two kernels is established.

We test an optimistic discrete diagonal realization on the exact original modes, without claiming that periodizing/compressing physical convolution equals this realization. Write L=log m, M=floor(m^epsilon), omega_j=2pi j/L, c0=xi(1/2)>0 and
D_m=diag(c0/xi(1/2+omega_j)), -M<=j<=M.
Real-axis xi is positive (the inherited positive theta representation), even about1/2. Let K_m^rec=(P D_m P)|ranP. This notation is auxiliary and must not replace the production CCM K_m. The auxiliary operator is positive definite in finite dimension.

## Exact original-P lower bound for the inverse fee

Let V_hi be supported on ceil(M/2)<=j<=M. For M sufficiently large dim V_hi>=4. Since P imposes at most three linear contacts, V_hi intersects ranP nontrivially. For a unit vector v in that intersection,
<v,K_m^rec v>=sum_hi d_j |v_j|² <= max_hi d_j.
Thus
||(K_m^rec)^(-1)|| >= min_hi xi(1/2+omega_j)/c0.
No commutation of P and D is assumed. Complex coefficients and all contact constraints remain intact.

From the definition xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2 and real Stirling,
log xi(1/2+t)=(t/2)log(t/(2pi))-t/2+O(log t), t->+infinity.
Uniformly for Omega/2<=t<=Omega, Omega=2pi M/L, this is >=c Omega log Omega for large m. For each fixed epsilon>0, Omega log Omega is asymptotic to 2pi epsilon m^epsilon. Consequently the universal inverse fee is at least exp(c_epsilon m^epsilon), exceeding every fixed power of m. Floor effects do not alter this conclusion.

## Complete scope of the failed completion

If an approximate signed comparison supplies K_m^rec A K_m^rec <= B_m I on ranP, its generic scalar return is A<=B_m ||(K_m^rec)^(-1)||² I when B_m>=0. Thus this standard norm-based return requires correspondingly tiny B_m to yield a subpower budget. Polynomially small residual bounds do not suffice for this displayed certificate. All mixed terms of A are preserved by the congruence; there is no diagonal replacement of A. Existing short-divisor and archimedean fees cannot improve this positive inverse price.

This is a lower bound for the universal inverse norm, NOT a lower bound for actual A or CCM. It does not prove the particular source pair suffers the worst conditioning. In particular an EXACT nonpositive congruence would transfer sign with no positive error fee: the inverse-norm obstruction does not refute that possibility. A source-specific range theorem, an exact sign theorem, or another transform could avoid this completion. Nor has a physical-convolution/original-P intertwining been supplied; paying that extra commutator is a separate obligation, not silently zero.

Decision after bounded audit: do not propose mere positive smoothing followed by universal norm inversion as a cheap return. The unresolved substantive question is whether the new reciprocal density supplies an actual source-specific signed comparison without that loss. This is one concrete transfer preflight, not three failed attempts. Q24 not sent.

Audit refinement: dim V_hi=floor(M/2)+1, so M>=6 suffices. The quantitative lower bound is log ||(K_m^rec)^(-1)|| >= (pi epsilon/2+o(1)) m^epsilon. This review covers the proposed inverse fee, not the Sra paper or a missing physical intertwining.
