# Arithmetic reciprocal assembly of the exact finite gamma source

STATUS: ANALYTIC_PAPER; exact-payload independent review is recorded in the adjacent SPACE_SIBLING_HUNT_20260915 certificate.
This is one bounded source reconstruction test in response to the user's suggestion, not a claimed real-zero theorem or a replacement of the CRITICALSTRIP request.

## Pinned source facts

Use r_N and r of REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md G1-G4, SHA256 7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621.
T_N=sum_(n<=N) Gamma(2,1)/(pi n^2), r_N=density(T_N), lambda_n=pi n^2.
We have uniform real convergence r_N -> r, r(1/t)=t^(5/2)r(t), Phi(x)=e^(5x/2)r(e^(2x)), and r_N(t)<=C exp(-pi t/2), C=2pi exp(1/7), all N,t>0. The complete-source Fourier transform is xi(1/2-iz).

## AR1: explicit reconstruction and exact limiting source

Set a_N(x)=e^(5x/2)r_N(e^(2x)) and

H_N(x)=(a_N(x)+a_N(-x))/2.

Every H_N is real, strictly positive and even on the real axis. Pointwise, a_N(x)->Phi(x) and a_N(-x)->Phi(-x)=Phi(x), hence H_N->Phi. This is a different approximating family from G_N=sqrt(r_N(e^(2x))r_N(e^(-2x))), with the SAME exact limiting source. It changes the finite assembly, not the limiting xi function.

## AR2: every fixed spectral strip has a common integrable bound eventually

For fixed M>=1, the convolution-simplex formula for the M shape-two gamma densities implies

r_M(t)<=C_M t^(2M-1), t>0,
C_M=product_(n<=M) lambda_n^2 / Gamma(2M).

Indeed the density integrand is product lambda_n^2 u_n times exp(-sum lambda_n u_n)<=product lambda_n^2 u_n, and its convolution integral equals t^(2M-1)/Gamma(2M). Extend r_M by zero to negative arguments. For N>=M the positive independent remainder gives
r_N(t)=E r_M(t-(T_N-T_M))<=C_M t^(2M-1), t>0.

For x>=0 and N>=M it follows that

0<H_N(x)<=1/2 [C e^(5x/2) exp(-pi e^(2x)/2)+C_M e^(-(4M+1/2)x)].    (AR2)

Evenness supplies the same bound in |x|. Given B>=0 choose M with B<4M+1/2. Then e^(B|x|) times the right side is integrable, independent of N>=M. Pointwise convergence, the same bound for Phi, and dominated convergence prove

integral_R e^(B|x|)|H_N(x)-Phi(x)|dx ->0.                           (AR3)

Put Z_N^A=integral_R H_N>0 and Z=integral_R Phi>0. Then Z_N^A->Z and the normalized transforms

A_N(z)=(Z_N^A)^(-1) integral_R H_N(x)e^(-izx)dx

are holomorphic on |Im z|<4N+1/2 and converge uniformly on every fixed closed horizontal strip |Im z|<=B once N is large enough. The limit is xi(1/2-iz)/xi(1/2). Derivatives under the integral follow on smaller substrips using polynomial-weight domination. The finite transforms are not claimed entire.

## AR3: the old source branch mechanism is absent, with an explicit price

For every fixed N the partial-fraction formula expresses r_N(t) as a finite sum (d_n t+e_n)e^(-lambda_n t). This gives an entire continuation in t and hence a_N and H_N are entire in x. There is no complex square root in this definition and therefore no square-root branch divisor of the kind used in GAMMA_COFINAL_BRANCH_OBSTRUCTION B1-B8.

The price is a finite Fourier strip for each fixed N. The simplex formula also gives r_N(t)~C_N t^(2N-1) as t decreases to zero, so

H_N(x)~(C_N/2)e^(-(4N+1/2)|x|) as |x|->infinity.

Therefore the ordinary defining Fourier integral is absolutely convergent exactly for |Im z|<4N+1/2 and diverges on its boundary. This is an integral-domain claim, not a claim that meromorphic continuation outside the strip is impossible. The strips expand with N, which is sufficient for the usual fixed-compact analytic limit and Rouché arguments. No claim about the zeros inside those strips has been obtained.

## AR4: transform identified without an unknown correction

Define L_N(s)=integral_0^infinity t^(s-1)r_N(t)dt, initially Re s>1-2N. Then substitution t=e^(2x) gives exactly

A_N(z)=[L_N(5/4-iz/2)+L_N(5/4+iz/2)]/[2 L_N(5/4)].                 (AR4)

For N=1 this specializes to
L_1(s)=pi^(1-s)Gamma(s+1),
A_1(z)=[pi^(iz/2)Gamma(9/4-iz/2)+pi^(-iz/2)Gamma(9/4+iz/2)]/[2Gamma(9/4)].
This is an exact formula, not a real-zero claim. Positive evenness of H_N, and the cancellation of source branch defects, do not prove real zeros or V_(H_N)>=0.

## Decision

This family is a source-faithful rebuilt approximation with a proved eventual-strip limit, not a solved sign mechanism. It removes one specifically identified obstruction (finite source square-root branches) and exposes its exact analytic cost (finite but expanding Fourier strips). Any continuation must prove a sufficient zero-exclusion property inside the critical strip from these explicit Mellin transforms; that step remains open. Do not apply the former geometric-family no-go to this different family, and do not treat its absence as a positive theorem. Publication-time update: CRITICALSTRIP has now been answered and independently reviewed; REPORT_2026-09-15_CRITICALSTRIP_INTAKE.md compares its geometric-family curvature mechanism with this arithmetic family. No duplicate request was sent.
