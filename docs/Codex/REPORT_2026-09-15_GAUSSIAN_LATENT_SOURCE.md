# Exact Gaussian latent source and radial-angular preflight

STATUS: ANALYTIC_PAPER_CANDIDATE. Scope: exact arithmetic-source representation and explicit regularity/scaling filters; no zero-free theorem, C6, V sign, or RH.
Source base: a4063fed4a087c6374ec324778a9dcbbd66c6eca.
Inputs: AR1-AR4 in REPORT_2026-09-15_ARITHMETIC_RECIPROCITY.md (SHA256 b128c925d794693fdbc5b1e8257e5587060c92d60770a650f2f8d26ee6838f53), and the reviewed Barvinok hypotheses/affine filters in REPORT_2026-09-15_OSCILLATORY_MARGINAL_HUNT.md (SHA256 4d7b06b1a7e17eeb2822f282358772a929f362527209c5b98306cb8fe6840565). The new work below is elementary source algebra, not a new literature claim. The existing gamma representation and Mellin formula are reused rather than counted as newly discovered facts.

## 1. Exact finite Gaussian representation

Let Y_(n,j), 1<=n<=N,1<=j<=4, be independent standard real normal variables. Define

T_N(Y)=sum_(n=1)^N sum_(j=1)^4 Y_(n,j)^2/(2 pi n^2).

Each half-block sum is Gamma(2,1): polar integration of the standard Gaussian in four dimensions gives density s exp(-s), s>0. Independence therefore gives exactly the r_N density used in the source, with no changed rates.

For p complex with Re p>-2N, define m_N(p)=E T_N^p, using the real log of T_N>0. AR4 gives the exact normalized arithmetic transform

A_N(z)=[m_N(1/4-iz/2)+m_N(1/4+iz/2)]/[2m_N(1/4)]
      =E[T_N^(1/4) cos((z/2)log T_N)] / E T_N^(1/4).          (L1)

The domain is |Im z|<4N+1/2, exactly the previously established Fourier strip. The denominator is finite and positive. This is a Gaussian integral in dimension 4N, with all source rates retained, not a Gaussian approximation to the source.

## 2. Why the direct latent integrand does not meet Barvinok's hypotheses

For z=u+iv with |v|<1/2 and 0<T<=1,

|T^(1/4)cos((z/2)log T)|<=T^(1/4-|v|/2).

Thus the numerator integrand in (L1) has a continuous extension equal to zero at Y=0. A function exp(sum_(j=1)^m phi_j(Y)) with finitely many globally Lipschitz complex phi_j is continuous and never zero, including at Y=0. It cannot equal this integrand even Gaussian-almost everywhere: continuity and the Gaussian measure's full support would force equality everywhere. A nonzero normalization factor cannot repair the mismatch. The same vanishing obstruction applies to each separate power T_N^(1/4±iz/2).

Moving T_N^(1/4) into the reference measure is an exact alternative, but gives a different positive measure, with log weight (1/4)log T_N singular at the origin. It is not the standard product Gaussian with globally Lipschitz logarithmic interactions required by the cited theorem. No assertion about the boundary |v|=1/2 is needed for this obstruction; every interior critical-strip compact is already relevant.

This only rejects the pointwise direct latent-integrand route and its finite globally Lipschitz exponential splittings. It does not reject all equal-integral representations or nonlinear constructions.

## 3. Integrate the radial part exactly

Write Y=sqrt(2S_N) U_N, where S_N=||Y||^2/2 is Gamma(2N,1) and U_N is independent and uniform on the unit sphere S^(4N-1). This follows directly from the Gaussian polar Jacobian: the radial density is s^(2N-1)exp(-s)/Gamma(2N), independent of direction.

Put

Q_N(U)=sum_(n=1)^N (1/(pi n^2)) sum_(j=1)^4 U_(n,j)^2.

Then T_N=S_N Q_N, and 1/(pi N^2)<=Q_N<=1/pi. Define the entire function of p

D_N(p)=E_(sphere) exp(p log Q_N).

Radial integration is now explicit:

m_N(p)=Gamma(2N+p)/Gamma(2N) D_N(p), Re p>-2N.               (L2)

Consequently (L1) becomes

A_N(z)=[Gamma(2N+1/4-iz/2)D_N(1/4-iz/2)
       +Gamma(2N+1/4+iz/2)D_N(1/4+iz/2)]
       /[2Gamma(2N+1/4)D_N(1/4)].                           (L3)

The origin singularity has been integrated exactly, without an omitted remainder. The angular integral remains. It can equivalently be written over the simplex of W_n=sum_j U_(n,j)^2, with Dirichlet(2,...,2) density Gamma(2N) product W_n on sum W_n=1 (N=1 means a point mass). This follows by the substitution from independent Gamma(2,1) blocks to their sum and proportions, whose Jacobian is s^(N-1).

For N=1, Q_1=1/pi is constant, recovering the earlier explicit gamma-pair formula. Formula (L3) retains the sum of both complex contributions. It does not infer nonvanishing of that sum from properties of separate factors.

## 4. The angular phase does not become globally flat with N

Let A be diagonal on R^(4N) with eigenvalues 1/(pi n^2), each repeated four times. On the unit sphere Q=U^T A U and

||grad_S log Q||=2 sqrt(U^T A^2 U-Q^2)/Q.                   (L4)

Set M=1/pi, m=1/(pi N^2). The scalar inequality lambda^2<=(M+m)lambda-Mm for m<=lambda<=M gives

U^T A^2 U-Q^2 <= (M-Q)(Q-m).

Maximizing (M-Q)(Q-m)/Q^2 over [m,M] gives (M-m)^2/(4Mm), at Q=2Mm/(M+m). This is attained by a direction using only the endpoint eigenspaces with the required proportions. Hence, for the sphere's intrinsic geodesic metric,

Lip(log Q_N)=sup ||grad_S log Q_N||=(M-m)/sqrt(Mm)=N-1/N.    (L5)

For N=1 the value is zero. Equality between global Lipschitz constant and the maximum gradient follows by integrating along minimizing geodesics and by taking local directional quotients. Thus p log Q_N has Lipschitz constant |p|(N-1/N). Scaling Q_N by 2N only adds a constant to log Q_N and does not reduce this value.

This is a proved scale diagnosis for the exact angular representation. The Gaussian/exponential Barvinok theorems are not theorems about uniform sphere measure, so (L5) is not advertised as their direct application or as a necessary condition for zero-freeness. It specifically disproves the hope that adding the exact Gaussian dimensions makes this angular phase uniformly small in the ordinary sphere metric.

## 5. The scaled angular variable converges back to the full source

Couple all Y_(n,j) in one infinite independent array. The nonnegative series T=sum_(n>=1,j) Y_(n,j)^2/(2pi n^2) has finite expectation, since sum n^(-2)<infinity. Hence T_N->T almost surely and T is finite. The original source construction identifies T's density as r.

Also E S_N=2N and Var(S_N)=2N, so S_N/(2N)->1 in probability by Chebyshev. Since 2N Q_N=T_N/(S_N/(2N)), it follows that

2N Q_N -> T in probability.                                (L6)

The limit is nondegenerate: its independent first gamma term has positive variance and the remaining terms have finite total variance. Thus the angular part, after the natural radial scaling, retains the full random source. Its fluctuations do not collapse to a constant merely because the dimension grows. Formula (L6) is an audit of what this representation preserves, not an implication about Fourier zeros.

## 6. A broader, precise Gaussian-transport obstruction for H_N

Fix N. The normalized source probability density H_N(x)/Z_N^A has exponential tails c_N exp(-(4N+1/2)|x|), with c_N>0. Therefore

integral exp(epsilon x^2) H_N(x)/Z_N^A dx=infinity
for every epsilon>0.                                      (L7)

Suppose this probability law were the pushforward of a standard Gaussian in any finite dimension d by a globally L-Lipschitz real map F. Then
|F(y)|<=|F(0)|+L||y||, so for sufficiently small epsilon>0,
E exp(epsilon F(Y)^2)<=exp(2epsilon|F(0)|^2) E exp(2epsilon L^2||Y||^2)<infinity,
contradicting (L7). If L=0 the pushforward is a point mass and is already impossible.

The same proof allows a positive reference reweighting w with globally Lipschitz log w, followed by such an F. Indeed w(y)<=w(0)exp(K||y||), and a small enough quadratic exponential remains Gaussian-integrable; normalize by the finite positive E w. Thus neither an unweighted nor a globally log-Lipschitz positively weighted finite Gaussian followed by a globally Lipschitz observable reproduces this arithmetic-source probability law.

This is broader than an affine-coordinate obstruction, but narrower than a prohibition of arbitrary Gaussian representations. The exact representation (L1) is consistent with it because its weight/observable are singular. General complex interactions depending on z, different reference measures, non-Lipschitz maps, and other zero-free mechanisms remain outside this exclusion. The lemma makes no claim about the geometric G_N family, whose tails are different.

## 7. Route decision

The exact latent source exists, and radial integration yields a compact angular formulation with no artificial residual. It does not supply the missing sign mechanism: its direct Gaussian integrand is outside the required global Lipschitz class; the angular phase has growing global sensitivity; and its scaled random variable converges to the original full source.

This is the second bounded preflight of the Barvinok small-global-interaction route, after the affine test. Park these direct Gaussian/Lipschitz implementations; do not commission a third renamed version of the same unpaid budget. Preserve the exact formulas as possible tools for a different, source-specific mechanism. There is no enlargement of the geometric |Re z|<=5 zero-free slab and no positive or negative verdict on full V or RH.
