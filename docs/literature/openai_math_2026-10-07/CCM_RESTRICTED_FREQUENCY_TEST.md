# High frequencies survive the exact continuous-kernel restriction

2026-10-08. Root calculation and independent read-only prime_frequency_supplier check PASS for (1)–(4) and the exact primary-source map. Same N=m CCM carrier and P from CCM_RESTRICTED_PRIME_RECEIVER.md. This is a legal projected test-vector construction, not identification of the actual adaptive spectral density. No prime spectral bound, SP or RH is proved.

## The source-map question

The prime-only receiver removes span{b,v_+,v_-}. Could this automatically remove the short wavelengths that obstruct using coarse prime-counting intervals? The following literal source calculation answers no for the whole restricted space.

Let e_m be the highest original Fourier coordinate and let E=I-P. The accepted normalized Gram matrix of b,vhat_+,vhat_- has least eigenvalue at least1/2 eventually. At omega_m=2pi m/L the explicit exponential coefficients and the already proved norms ||v_+||²=m+O(L), ||v_-||²=1+O(L/m) give

    |(vhat_+)_m|²<=L/(2pi²m²),
    |(vhat_-)_m|²<=L/(2pi²m²),
    |b*e_m|²=1/(2m+1).                                    (1)

For example, ||v_+||²>=m/2 and (sqrt(m)-1)²<=m give the first bound directly from denominator L(1/4+omega_m²); the minus case uses ||v_-||²>=1/2 and numerator<=1. Thus

    epsilon_m²=||E e_m||²
       <=2[1/(2m+1)+L/(pi²m²)]<=2/m                      (2)

eventually. These bounds use the actual three-vector Gram inverse, not an assumption that the finite vectors are exactly orthogonal.

Set z_m=P e_m/||P e_m||. It is defined eventually and belongs to ran P. Because <e_m,z_m>=||P e_m|| is real nonnegative,

    ||z_m-e_m||²=2(1-sqrt(1-epsilon_m²))
                <=2epsilon_m²<=4/m.                       (3)

The original ||Q(s)||<=2 now gives uniformly for 0<=s<=L,

    |z_m*Q(s)z_m-e_m*Q(s)e_m|<=8/sqrt(m),
    z_m*Q(s)z_m
       =2(1-s/L)cos(2pi m s/L)+O(8/sqrt(m)).                (4)

This is an explicit legal rank-one PSD probe z_m z_m*. It is not claimed to equal S_-^(p-1) or an eigenprojector of the prime operator.

On any fixed interior upper block am<=u<=bm with 1/2<a<b<1, put s=log u. The cosine envelope 2log(m/u)/L is bounded above and below by positive constants times1/L, while m^(-1/2)=o(1/L). Successive equal-phase locations have ratio exp(L/m), so their spacing is u(exp(L/m)-1), asymptotic to uL/m, uniformly on that block. It is of order log m. Thus the exact restriction retains oscillatory probes at the original shortest arithmetic scale. A projection onto three constraints cannot be treated as a low-frequency filter.

## Implication for density suppliers

A theorem controlling only prime mass in intervals of power length cannot by itself control these legal oscillatory probes merely through P. This is a missing hypothesis in that source map, not a counterexample to the theorem or proof that its full methods cannot help. One must prove cancellation inside the coarse intervals, or establish additional regularity for the actual adaptive spectral density. The latter cannot be inferred from membership in ran P alone.

The signed baseline quadrature in CCM_TRANSPORT_QUADRATURE_CONTROL.md remains compatible with (4): collective arithmetic structure can compensate oscillations. Its weight-one result cannot be transferred to Lambda without an estimate of the actual Lambda-1 block.

## Primary large-value theorem: exact quantified map

Verified primary source: Larry Guth and James Maynard, New large value estimates for Dirichlet polynomials, arXiv:2405.20552v2, 7 April2026. Existing shelf PDF docs/routeB_bus/litreview/pdfs/2405.20552.pdf; SHA256915392cf7d0ecd108479814a9a1481e23423ef63415776471cec3975ae482cae. Root read Theorem1.1 on p1 and Corollary1.4 on p3; URL https://arxiv.org/pdf/2405.20552v2. Quote from Theorem1.1: “1-separated points”. This is source-verified discovery evidence, not a new arithmetic premise.

For coefficients |b_n|<=1 on a dyadic interval of length N, the theorem bounds the number R of such points in [0,T] where |sum b_n n^(it)|>=V by

    R <= T^o(1)[N² V^(-2)+N^(18/5)V^(-4)
                                  +T N^(12/5)V^(-4)].       (5)

For the actual upper-block D_m(t)=sum (Lambda(n)-1)chi(n/m)n^(-1/2+it), choose a fixed C_chi large enough that b_n=sqrt(m)(Lambda(n)-1)chi(n/m)/(C_chi L sqrt(n)) has magnitude<=1. Choose N comparable to m, padding by zero as needed. T is comparable to m/L; shifting the t interval only multiplies b_n by a unit phase. The original frequency grid has spacing2pi/L, so applying a 1-separated-point theorem to all grid points needs O(L) residue classes of that grid.

At a normalized threshold |D_m|>=m^eta, the theorem's V is m^(1/2+eta)/(C_chi L). Its FIRST upper-bound term alone is of order m^(1-2eta)L². For small fixed eta>0, this upper certificate grows; it cannot imply R=0 or exclude even one large frequency. This is not a lower bound on the actual number R. The theorem's generic coefficient class can indeed contain coherent spikes, unlike an as-yet-proved source-specific cancellation hypothesis. Its advertised improvement regime N<=T^(5/6-epsilon) does not include N comparable to T log T. No improved full spectral moment follows here merely by restating this large-value bound.

Corollary1.4 controls prime counts for lengths X^(2/15+epsilon)<=y<=X^0.99 outside a quantified exceptional set of starts. At X comparable to m these cells are much longer than the legal projected wavelengths in (4). The exceptional starts and oscillatory weights are unpaid; neither density information nor the projection automatically pays them. A future argument using deeper parts of the method is not excluded.

Remaining target: an actual source-dependent collective estimate retaining all intermediate CCM projections and signs. The bounded source comparison above rejects importing this theorem as an already complete supplier; it does not declare the mathematical target false.
