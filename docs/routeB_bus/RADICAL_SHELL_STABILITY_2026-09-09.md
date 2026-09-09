# Radical-shell stability: K36 versus K48, 2026-09-09

Authority: DIAGNOSTIC_NEVER_A_PROOF. All ratios below are raw finite-matrix diagnostics, not certified source eigenvalues.

## Frozen prediction and method

Before any numerical launch: q/lambda1 = 1.5 at a=0.75, K=48, span of g0,g2,...,g12. Frozen manifest SHA256: 92592e8037f57aff9cd71aa1dd3441cdc59ed906510dfebde03d356ecf6af3a0. Six sequential background jobs, each with three windows, all completed EXIT=0. Builder settings: base h=0.02, XI=20000; h refinement 0.01/20000; cutoff refinement 0.02/40000. Saved Q, G, eigenpairs and projected theta coefficients are retained for all jobs.

g0-g4/g8/g12 means 3/5/7 even members. Physical Gram orthogonality is used. q_cancel=(r-b*C^-1*b)/(1+||z||^2); q_direct is the Rayleigh quotient of the reconstructed trial. The absolute diagnostic rounding scale is max(eps*max(1,||L^-1 Q L^-T||2),abs(q_direct-q_cancel)), G=LL^T. It is NOT a rigorous floating-point error bound.

## Baseline comparison

| a | even shell | q/lambda1 K36 | q/lambda1 K48 | absolute scale K36 | absolute scale K48 | final status |
|---|---|---:|---:|---:|---:|---|
| 0.70 | span_g0-4 | 161.71238 | 165.25329 | 1.044991e-15 | 1.172725e-15 | UNRESOLVED / UNRESOLVED |
| 0.70 | span_g0-8 | 8.721609 | 8.9125695 | 1.044991e-15 | 1.172725e-15 | UNRESOLVED / UNRESOLVED |
| 0.70 | span_g0-12 | 1.6006434 | 1.6358137 | 1.044991e-15 | 1.172725e-15 | UNRESOLVED / UNRESOLVED |
| 0.75 | span_g0-4 | 907.60883 | 1204.2256 | 1.026565e-15 | 1.151714e-15 | UNRESOLVED / UNRESOLVED |
| 0.75 | span_g0-8 | 21.442116 | 28.452567 | 1.026565e-15 | 1.151714e-15 | UNRESOLVED / UNRESOLVED |
| 0.75 | span_g0-12 | 2.6154958 | 3.4516623 | 1.026565e-15 | 1.151714e-15 | UNRESOLVED / UNRESOLVED |
| 0.80 | span_g0-4 | -220.35027 | -98.226977 | 1.010191e-15 | 1.135609e-15 | UNRESOLVED / UNRESOLVED |
| 0.80 | span_g0-8 | -1.4166724 | -0.61947426 | 1.010191e-15 | 1.135609e-15 | UNRESOLVED / UNRESOLVED |
| 0.80 | span_g0-12 | 1.9307688 | 0.86902792 | 1.010191e-15 | 1.135609e-15 | UNRESOLVED / UNRESOLVED |

## Builder sensitivity, absolute normalized matrix scales

E_Q,h and E_Q,XI are norms of the individual Q differences in the BASE Gram-whitened coordinates, compared only at the same K and a. E_G is the corresponding normalized Gram difference. max(E_Q,h,E_Q,XI) is an empirical sensitivity gauge, NOT a joint or certified error bound. It does not justify any enclosure of the continuum eigenvalue.

| K | a | E_Q,h | E_Q,XI | max E_G | lambda base | lambda h | lambda XI |
|---:|---|---:|---:|---:|---:|---:|---:|
| 36 | 0.70 | 1.162834e-14 | 1.223270e-05 | 0.000000e+00 | 4.36748254e-13 | 4.38379498e-13 | 4.38098377e-13 |
| 36 | 0.75 | 1.333561e-14 | 9.065381e-06 | 0.000000e+00 | 3.88553744e-15 | 3.80026854e-15 | 3.82566974e-15 |
| 36 | 0.80 | 3.826671e-15 | 5.085529e-06 | 0.000000e+00 | -4.10338878e-16 | -9.93971781e-16 | -6.86825786e-16 |
| 48 | 0.70 | 2.008022e-14 | 5.136048e-05 | 0.000000e+00 | 4.27389897e-13 | 4.27586385e-13 | 4.27859770e-13 |
| 48 | 0.75 | 2.398850e-14 | 3.800391e-05 | 0.000000e+00 | 2.92847654e-15 | 4.03070945e-15 | 3.65501312e-15 |
| 48 | 0.80 | 6.132922e-15 | 2.928281e-05 | 0.000000e+00 | -9.20426786e-16 | -1.58658938e-15 | -1.61714847e-15 |

## Acceptance limits and uncovered errors

A row is UNRESOLVED if any build variant fails the local floating/solve screen, lambda1 is not above the empirical matrix gauge, or normalized Gram variation >=1e-3. Local solve screens: cond(C)*eps <=1e-3 and relative solve residual <=1e-10. This conservative diagnostic classification does not assert that the entire matrix difference acts on the ground direction. Full raw direct/cancellation values and each refinement are in the companion JSON.

The requested rigorous builder budget remains OPEN: sc_build uses binary64 special functions and quadrature and a leading asymptotic Fourier-tail correction without a total remainder enclosure. Theta derivatives/projection and infinite-tail errors are also not enclosed. Mesh/cutoff differences cannot replace these bounds. No larger K or extrapolated degree law can repair this missing certificate.

The numerical prediction is UNRESOLVED under the frozen error-based scoring rule. It is neither confirmed nor refuted by a raw ratio with unresolved denominator. Three windows do not determine cofinal m(a). At a=0.80 negative rounded eigenvalues are below the floating scale and are not evidence of a negative source form.

## Independent checks

A separate recomputation at K48,a=0.70 used polynomial derivative recursion and Gram-orthonormal coordinates: even shell ranks 3/5/7; direct ratios 165.2533199462,8.9125893409,1.6358376201. Differences from saved direct q were at most 1.54e-17, below floating scale 1.172725288e-15. The main observer separately recomputed the stored g0-g12 cancellation ratio as 1.6358136659398185.

A 70-digit eigensolve of the exact rounded K48,a=0.75 Q/G gave lambda1=0.000000000000002996589111827079995959768340279588884465245592216055227868731082252975; difference from binary64 eigensolver 0.00000000000000006811257063744142228090661288762153181280127164231165317047553935442473. This verifies only the saved rounded matrix, not source assembly.

## Decision

Retain SCHUR as an analytical proof-construction batch: fixed degree schedule, full-tail determinant, coupled signed arithmetic remainder. Do not use this table to claim the stronger unnormalized recovered-energy inequality or a lower sign. My next numerical choice is a projected/source error enclosure at a=0.75 before extending a or K. If that enclosure resolves lambda and q, test the degree law; otherwise retain the analytic tail-determinant task and classify the numerical ratio as unresolved.

## Artifacts

- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/radical_shell_stability_20260909.json
- /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/radical_shell_stability_20260909_manifest.json
- Matrix, eigenpair and margin outputs: /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/window_derivative_K{36,48}_codex_radical_20260909_{base,h,xi}*
- Reproduction scripts are embedded byte-for-byte with hashes in the companion JSON; the original frozen manifest is retained unchanged.


## Exact frozen-polynomial follow-up

This follow-up encloses the full form of one explicitly frozen polynomial; it does not certify the theta-source trial, its projection error, a window eigenvalue, the numerical ratio forecast, or RH. The polynomial has exact dyadic Legendre coefficients and is zero outside the exact interval (-7/10,7/10). The earlier builder used binary64 a=0.70; this parameter distinction is explicit and no source-transfer equality is asserted.

The K36 span_g0-12 coefficient vector is reconstructed with the literal vectorized orthogonalization and einsum normalization from one_direction_margin.py. Its raw little-endian binary64 SHA256 is `0da2212a2cf7c9ac5cd627571d3e2adba14806b75cb9644028cde56bee385e7b`. This identity is an enforced precondition, not inferred from a nearby Rayleigh value. A previous per-column reconstruction was a different vector and is excluded from this follow-up. The companion data preserves its historical diagnostic separately.

For p of degree 35, rational arithmetic constructs R_+(t)=integral from t-a to a of p(x)p(x-t), N=integral p^2, and h_+=N-R_+. The exact degree of h_+ is 71. The identities h_+(0)=0, R_+(2a)=0, h_+(2a)=N and the vanishing derivative of order 72 are checked exactly. The full form uses one-sided endpoint derivatives, Hurwitz zeta sums and an explicit geometric outer-mode remainder, all evaluated with Arb. The only prime-power atoms are 2,3,4, with Lambda(4)=log(2); both pole moments are retained. The strict inequalities log(4)<2a<log(5) are checked with intervals.

| precision bits | outer modes | full Q, midpoint (rounded for display) | rigorous absolute radius below | result |
|---:|---:|---:|---:|---|
| 256 | 24 | unresolved | 1.19e37 | too wide |
| 384 | 48 | unresolved | 0.0590 | too wide |
| 640 | 96 | 7.046297034495313407e-13 | 4.59e-78 | controlled polynomial enclosure |
| 768 | 128 | 7.046297034495313407e-13 | 3.67e-117 | controlled polynomial enclosure |

Displayed shortened midpoints are not the endpoints of these narrow balls; exact ball strings and outward endpoints are in the companion data. Both high-precision enclosures overlap, and their radii are below 1e-20. The exact rational norm has decimal approximation 1.0067727374858177. Q/N is approximately 6.998895353574841299e-13; its full enclosure is retained in the companion data.

Constant and linear polynomial controls were checked against independent high-precision direct quadrature of the full form. The linear endpoint derivative is h_+'(2a-)=-49/100. The quadrature comparisons are diagnostics; the rigorous radius comes from Arb operations and the explicit outer-mode remainder. Increasing arithmetic precision fixes cancellation in this polynomial calculation; it does not pay theta normalization, derivative-series or projection errors.

The next decisive source margin remains OPEN. In particular, no conclusion about T(0.70)^2-Q[f_source] follows until both T and the source-to-polynomial transfer are enclosed. No finite-candidate failure, cofinal degree law, or lower-sign claim is scored here. The lambda denominator and frozen 1.5 forecast remain UNRESOLVED.


## True theta normalization and source-profile discriminator

At the same exact a=7/10, the true theta tail fraction and physical cut norm are now enclosed independently of the window builder. With I(a)=2 integral_a^infinity Phi(x)^2 dx, the quantities are T=I(a)/I(0) and N_a=sqrt(I(0)-I(a)). No projected Gram norm is substituted for N_a.

| quantity | value, rounded for display | interpretation |
|---|---:|---|
| true T(a)^2 | 6.589865655707739776e-13 | interval-certified theta mass ratio |
| true N_a | 0.2827328917872553244 | interval-certified physical cut norm |
| T(a)^2-Q[f_poly] | -4.564313787875736310e-14 | polynomial scalar difference only; NOT the source margin S40 |

Full outward intervals, not shortened decimal centers, are retained in the companion data. The T-squared enclosure has radius below 6e-117 at 384 bits; the N_a enclosure has radius below 1.4e-107. Independent 256-bit balls overlap these enclosures and pass their absolute-width checks. The separately computed 100-digit truncated-source physical norm agrees in its displayed digits; that quadrature agreement is diagnostic only.

For reproducibility, set z=pi*n^2*exp(2x) and P_0(z)=2z^2-3z. Then Phi_n^(r)(x)=exp(x/2-z)P_r(z), with P_(r+1)=(1/2-2z)P_r+2z P'_r. For r<=15, deg(P_r)=r+2<=17. If P_r=sum_k c_(r,k)z^k and rho=(10/9)^34 exp(-19pi), then

B_r = exp(-81pi)/(1-rho) * sum_k |c_(r,k)|(81pi)^k

bounds the absolute derivative tail n>=9 uniformly on x>=0. Indeed z^(k+1/4)exp(-z) decreases for z>=81pi>17+1/4, and successive n terms have ratio at most rho<1. This also gives uniform termwise differentiation on compact subintervals of the positive half-line. The estimate concerns right derivatives at zero; full-source evenness is a separate theta identity. In particular B_0<3.985e-106, B_14<4.954e-68 and B_15<2.678e-65.

The mass calculation uses the finite n,m<=8 expansion. With c=pi(n^2+m^2) and v=exp(2a), each ordered pair contributes

4*pi^4*n^4*m^4*c^(-9/2)*Gamma(9/2,c*v)
-6*pi^3*(n^4*m^2+n^2*m^4)*c^(-7/2)*Gamma(7/2,c*v)
+9*pi^2*n^2*m^2*c^(-5/2)*Gamma(5/2,c*v).

Here Gamma(s,z) is the unregularized upper incomplete gamma function. The factor 2 for the two physical tails cancels dx=dv/(2v). Let H_0=sum_(n=1)^8 exp(-pi*n^2)[2(pi*n^2)^2+3pi*n^2], alpha=2pi-9/2 and beta=162pi-9/2. The bounds |Phi_8(x)|<=H_0 exp(-alpha*x), |Phi-Phi_8|<=B_0 exp(-beta*x) yield the explicit mass remainder

E(a)=4 H_0 B_0 exp(-(alpha+beta)a)/(alpha+beta) + B_0^2 exp(-2 beta a)/beta.

The finite mass balls are enlarged by this bound before division or square roots. The implementation checks positivity of total, tail and inside masses and 0<T<1. Thus this follow-up pays the theta normalization and T-squared threshold errors, but does not pay the source-trial projection error.

The intended next source candidate is fixed by the seven numerical response coefficients y_j, each stored as exact binary64 bytes and float.hex in the companion data. These coefficients are never recomputed from source integrals. For the full Phi, define p=1_I Phi/N_a, h_j=1_I g_(2j)-<p,1_I g_(2j)>p, d_j=h_j/||h_j||_2 and f_src=p-sum_(j=0)^6 y_j d_j. This is a fixed admissible choice, not a claim of exact source stationarity or a positive Schur optimizer. The old frozen polynomial remains a separate object. Any refined polynomial used for transfer must approximate this same f_src, preserving y_j and exact physical normalizations.

A deterministic 33-point diagnostic compared the old polynomial with the n<=8 source surrogate using physical quadrature normalizations at 80 decimal digits. Both observed maxima occurred at the interior endpoint a-minus:

| observed quantity | magnitude | status |
|---|---:|---|
| profile discrepancy | 1.05507027975187e-8 | observed at x=a, not a supremum upper bound |
| interior derivative discrepancy | 9.75035263627430e-6 | observed at x=a-minus, not an E-norm estimate |

The selected maxima were recomputed at 100 digits, agreeing in the shown digits. Values at the support boundary mean limits of the interior profiles, not the arbitrary point value of a zero-extended L2 function. The exact-source derivative at zero uses full-source evenness. The diagnostic does not enclose quadrature or the seven direction normalizers; the separately proved theta-tail estimate does not turn this grid into a source certificate.

A useful rigorous transfer inequality is available. For e=1_(-a,a)v, L=2a, |v|<=u and |v'|<=b throughout the closed interval, including one-sided endpoint limits,

||e||_E^2 <= [L exp(L)+L^2+L+4L exp(-L/2)/(1-exp(-2L))]u^2 + (L^4+L^3)b^2/12.

For 0<t<L, the translation difference is bounded by 2t*u^2+(L-t)t^2*b^2; for t>=L it is bounded by 2L*u^2. Integration against A_0(t), using A_0(t)<=1+1/(2t) inside and A_0(t)<=exp(-t/2)/(1-exp(-2L)) outside, proves the displayed bound, including the endpoint jumps. At a=7/10 the coefficients are less than 11.998213 and exactly 0.5488, respectively.

Conditional method test: if a certified full-source endpoint derivative discrepancy is at least 9e-6, every valid b is at least 9e-6. This sufficient estimator then has B>=0.5488*(9e-6)^2=4.44528e-11; using e=sqrt(B) and ||f_poly||_E>=||f_poly||_2>1 in S41 returns an uncertainty budget greater than 2.9e-4, far larger than the polynomial scalar gap. The grid has NOT established that certified premise. This is a statement about the output of the sufficient estimator, NOT a lower bound on the actual E error, and does not reject the source trial or its T-squared budget. The next numerical choice is to obtain a sharper certified approximation of the same frozen source candidate, not increase precision of the already enclosed old polynomial. S40 remains UNRESOLVED until source energy/transfer is enclosed. Cofinal rates, the lambda denominator, the 1.5 forecast and the lower sign remain OPEN.
